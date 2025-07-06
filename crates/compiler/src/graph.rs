//! Graph based Continuation-Passing Style Intermediate Representation.
//!
//! Based on [Compiling with Continuations, Continued]
//!
//! [Compiling with Continuations, Continued]: https://www.microsoft.com/en-us/research/wp-content/uploads/2007/10/compilingwithcontinuationscontinued.pdf

use std::fmt;

use lasso::Spur;
use petgraph::{dot::Dot, graph::EdgeIndex, stable_graph::StableGraph};

use crate::{
    ast::{Datum, INTERNER, P, Symbol},
    source::Span,
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Edge {
    /// Edge to a node which defines this node.
    Def,
    Root,
    /// Variable use edge.
    Use,
    /// Edge which connects one node to another in the graph.
    ///
    /// One node can have only one `Next` edge, which is used to
    /// represent the next node in the control flow.
    Next,

    /// Edge to a function or continuation that is recursive.
    ///
    /// It is formed by `fix` form. If you have functions `f`, `g`, and `h` that
    /// are mutually recursive, the `fix` in graph form would look like:
    /// ```text
    ///  <parent>
    ///     |
    ///     v
    ///     f
    ///     ^
    ///     |
    ///     v   
    ///     g
    ///     ^
    ///     |   
    ///     v
    ///     h
    ///     |
    ///     v
    ///   <next>
    /// ```
    ///
    Rec,
}

/// A CPS node in the graph.
#[derive(Clone, Debug)]
pub enum Node {
    Global(P<Symbol>, Span),
    Constant(P<Datum>),

    /// Reference to a primitive function.
    PrimRef {
        name: Spur,
        span: Span,
    },

    Call {
        callee: id::Edge,
        k: id::Edge,
        h: id::Edge,
        args: Vec<id::Edge>,
        span: Span,
    },

    Continue {
        k: id::Edge,
        args: Vec<id::Edge>,
        span: Span,
    },

    Raise {
        k: id::Edge,
        args: Vec<id::Edge>,
        span: Span,
    },

    Continuation {
        name: Option<Spur>,
        nargs: usize,
        rest: bool,
        /// Edge linking this continuation to the body of the continuation.
        body: id::Edge,
        span: Span,
    },

    Func(Func),

    /// Case is equivalent to a `if` expression. It
    /// matches on a `test` and then jumps to one of the branches.
    Case {
        test: id::Edge,
        /// Continuations to jump to based on value of `test`.
        if_true: id::Edge,
        if_false: id::Edge,
    },

    /// Call to a primitive function.
    PrimCall {
        name: Spur,
        k: id::Edge,
        h: id::Edge,
        args: Vec<id::Edge>,
        span: Span,
    },

    Param(u32),
    Rest(u32),

    ReturnContinuation,
    RaiseContinuation,

    Unfinalized,
    Removed,
}

impl Node {
    pub fn is_variable_like(&self) -> bool {
        matches!(
            self,
            Node::Global(_, _) | Node::Constant(_) | Node::Param(_) | Node::Rest(_)
        )
    }

    pub fn is_continuation(&self) -> bool {
        matches!(
            self,
            Node::Continuation { .. } | Node::ReturnContinuation | Node::RaiseContinuation
        )
    }

    pub fn is_func(&self) -> bool {
        matches!(self, Node::Func(_))
    }

    pub fn is_call(&self) -> bool {
        matches!(self, Node::Call { .. } | Node::PrimCall { .. })
    }

    pub fn is_continue(&self) -> bool {
        matches!(self, Node::Continue { .. })
    }

    pub fn is_raise(&self) -> bool {
        matches!(self, Node::Raise { .. })
    }

    pub fn is_case(&self) -> bool {
        matches!(self, Node::Case { .. })
    }

    pub fn is_constant(&self) -> bool {
        matches!(self, Node::Constant(_))
    }

    pub fn is_primitive(&self) -> bool {
        matches!(self, Node::PrimRef { .. } | Node::PrimCall { .. })
    }
}

#[derive(Clone, PartialEq, Eq, Copy)]
pub struct Func {
    pub name: Option<Spur>,
    pub nargs: usize,
    pub rest: bool,
    pub body: id::Edge,
    pub span: Span,
}

pub mod id {
    pub type Edge = petgraph::stable_graph::EdgeIndex;
    pub type Node = petgraph::stable_graph::NodeIndex;
}

pub struct CPS {
    pub graph: StableGraph<Node, Edge>,
    pub root: id::Node,
}

type BuildCont = Box<dyn for<'a> FnOnce(&'a mut CPS, id::Node) -> id::Node>;

impl CPS {
    pub fn new() -> Self {
        CPS {
            graph: StableGraph::new(),
            root: id::Node::end(),
        }
    }

    /// Returns the number of nodes in the graph.
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Returns the number of edges in the graph.
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    pub fn letk(
        &mut self,
        nargs: usize,
        rest: bool,
    ) -> (
        id::Node,
        Box<dyn for<'a> FnOnce(&'a mut CPS, id::Node) -> BuildCont>,
    ) {
        let k = self.graph.add_node(Node::Continuation {
            name: None,
            nargs,
            rest,
            body: EdgeIndex::end(),
            span: Default::default(),
        });
        let build_cont = Box::new(move |cps: &mut CPS, body: id::Node| -> BuildCont {
            let def = cps.graph.add_edge(k, body, Edge::Root);
            *cps.graph.node_weight_mut(k).unwrap() = Node::Continuation {
                name: None,
                nargs,
                rest,
                body: def,
                span: Default::default(),
            };
            Box::new(move |cps: &mut CPS, next| {
                cps.graph.add_edge(k, next, Edge::Next);
                k
            })
        });

        (k, build_cont)
    }

    pub fn letf(
        &mut self,
        name: Option<Spur>,
        nargs: usize,
        rest: bool,
    ) -> (
        id::Node,
        Box<dyn for<'a> FnOnce(&'a mut CPS, id::Node) -> BuildCont>,
    ) {
        let f = self.graph.add_node(Node::Func(Func {
            name,
            nargs,
            rest,
            body: EdgeIndex::end(),
            span: Default::default(),
        }));
        let build_cont = Box::new(move |cps: &mut CPS, body: id::Node| -> BuildCont {
            let body = cps.graph.add_edge(f, body, Edge::Root);
            let Node::Func(func) = cps.graph.node_weight_mut(f).unwrap() else {
                panic!("Expected a function node");
            };

            func.body = body;

            Box::new(move |cps: &mut CPS, next| {
                cps.graph.add_edge(f, next, Edge::Next);
                f
            })
        });

        (f, build_cont)
    }

    pub fn fix(&mut self, funcs: impl Iterator<Item = Func>) -> (id::Node, BuildCont) {
        let mut prev = None;
        for func in funcs {
            let f = self.graph.add_node(Node::Func(func));

            if let Some(prev) = prev {
                self.graph.add_edge(prev, f, Edge::Rec);
            }
            prev = Some(f);
        }

        let build_cont = Box::new(move |cps: &mut CPS, next: id::Node| {
            if let Some(prev) = prev {
                cps.graph.add_edge(prev, next, Edge::Next);
            }
            prev.unwrap()
        });

        (prev.unwrap(), build_cont)
    }

    pub fn continue_(
        &mut self,
        k: id::Node,
        args: impl IntoIterator<Item = id::Node>,
        span: Span,
    ) -> id::Node {
        let call = self.graph.add_node(Node::Continue {
            k: EdgeIndex::end(),
            args: Vec::new(),
            span,
        });

        let args = args
            .into_iter()
            .map(|node| self.graph.add_edge(node, call, Edge::Use))
            .collect::<Vec<_>>();

        let k = self.graph.add_edge(k, call, Edge::Use);

        *self.graph.node_weight_mut(call).unwrap() = Node::Continue { k, args, span };

        call
    }

    pub fn funcall(
        &mut self,
        callee: id::Node,
        k: id::Node,
        h: id::Node,
        args: impl IntoIterator<Item = id::Node>,
        span: Span,
    ) -> id::Node {
        let call = self.graph.add_node(Node::Call {
            callee: EdgeIndex::end(),
            k: EdgeIndex::end(),
            h: EdgeIndex::end(),
            args: Vec::new(),
            span,
        });
        let args = args
            .into_iter()
            .map(|node| self.graph.add_edge(node, call, Edge::Use))
            .collect::<Vec<_>>();
        let k = self.graph.add_edge(k, call, Edge::Use);
        let h = self.graph.add_edge(h, call, Edge::Use);
        let callee = self.graph.add_edge(callee, call, Edge::Use);

        *self.graph.node_weight_mut(call).unwrap() = Node::Call {
            callee,
            k,
            h,
            args,
            span,
        };

        call
    }

    pub fn letv(&mut self, datum: P<Datum>) -> (id::Node, BuildCont) {
        let node = self.graph.add_node(Node::Constant(datum));

        let build_cont = Box::new(move |cps: &mut CPS, next: id::Node| {
            cps.graph.add_edge(node, next, Edge::Next);
            node
        });

        (node, build_cont)
    }

    pub fn letg(&mut self, name: P<Symbol>, span: Span) -> (id::Node, BuildCont) {
        let node = self.graph.add_node(Node::Global(name, span));

        let build_cont = Box::new(move |cps: &mut CPS, next: id::Node| {
            cps.graph.add_edge(node, next, Edge::Next);
            node
        });

        (node, build_cont)
    }

    pub fn dot(&self) -> Dot<'_, &StableGraph<Node, Edge>> {
        Dot::with_attr_getters(
            &self.graph,
            &[petgraph::dot::Config::NodeNoLabel],
            &|_, _| String::new(),
            &|g, node| format!("label = \"{}\"", NodeDisplay(g, node.0)),
        )
    }
}

#[macro_export]
macro_rules! with_cps {
    ($cps: ident; $binder : ident <- $expr: expr; $($rest:tt)+) => {
        let ($binder, cont) = $expr;

        let inner = with_cps!($cps; $($rest)+);

        cont(&mut $cps, inner)
    };

    ($cps: ident; letk $binder : ident ($($arg: ident),*) = $expr: expr; $($rest:tt)+) => {{
        let argc = {
            let mut count = 0;
            $(
                let _ = stringify!($arg);
                count += 1;
            )*
            count
        };
        let ($binder, cont) = $cps.letk(
            argc,
            false,
        );
        let body = $expr;
        let cont = cont(&mut $cps, body);

        let inner = with_cps!($cps; $($rest)+);

        cont(&mut $cps, inner)
    }};

    ($cps: ident; letf $binder : ident ($k: ident, $h: ident $(,)? $($arg: ident),*) = $expr: expr; $($rest:tt)+) => {{
        let argc = {
            let mut count = 0;
            $(
                let _ = stringify!($arg);
                count += 1;
            )*
            count
        };
        let ($binder, cont) = $cps.letf(
            None,
            argc,
            false,
        );
        let $k = $cps.graph.add_node($crate::graph::Node::ReturnContinuation);
        $cps.graph.add_edge($binder, $k, $crate::graph::Edge::Def);
        let $h = $cps.graph.add_node($crate::graph::Node::RaiseContinuation);
        $cps.graph.add_edge($binder, $h, $crate::graph::Edge::Def);
        let mut apos = 0;
        $(
            let $arg = $cps.graph.add_node($crate::graph::Node::Param(apos));
            $cps.graph.add_edge($binder, $arg, $crate::graph::Edge::Def);
            apos += 1;
        )*

        let body = $expr;
        let cont = cont(&mut $cps, body);

        let inner = with_cps!($cps; $($rest)+);

        cont(&mut $cps, inner)
    }};

    ($cps: ident; letv $binder: ident = $expr: expr; $($rest:tt)+) => {{
        let ($binder, cont) = $cps.letv($expr);
        let inner = with_cps!($cps; $($rest)+);
        cont(&mut $cps, inner)
    }};

    ($cps: ident; letg $binder: ident = $expr: expr; $($rest:tt)+) => {{
        let ($binder, cont) = $cps.letg($expr, Default::default());
        let inner = with_cps!($cps; $($rest)+);
        cont(&mut $cps, inner)
    }};

    ($cps: ident; funcall $callee: expr, $k: expr, $h: expr, args = [$($args: expr),*]; $($rest:tt)+) => {{
        let args = vec![$(with_cps!($cps; $args)),*];
        let call = $cps.funcall(
            $callee,
            $k,
            $h,
            args.into_iter(),
            Default::default(),
        );
        with_cps!($cps; call; $($rest)+)
    }};

    ($cps: ident; continue $k: ident ($($arg: ident), *)) => {{
        $cps.continue_($k, [$($arg),*], Default::default())
    }};

    ($cps: ident; case $test: ident => $k1: ident | $k2: ident) => {{
        let case = $cps.graph.add_node($crate::graph::Node::Unfinalized);

        let $test = $cps.graph.add_edge($test, case, $crate::graph::Edge::Use);
        let $k1 = $cps.graph.add_edge($k1, case, $crate::graph::Edge::Use);
        let $k2 = $cps.graph.add_edge($k2, case, $crate::graph::Edge::Use);

        *$cps.graph.node_weight_mut(case).unwrap() = $crate::graph::Node::Case {
            test: $test,
            if_true: $k1,
            if_false: $k2,
        };

        case
    }};

    ($cps: ident; # $expr: expr; $($rest:tt)+) => {{
        let _ = $expr;
        with_cps!($cps; $($rest)+)
    }};

    ($cps: ident; # $expr: expr) => {{
        $expr
    }};
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name {
            write!(
                f,
                "fn {} (req: {}, opt: {})",
                INTERNER.resolve(&name),
                self.nargs,
                self.rest
            )
        } else {
            write!(f, "fn (req: {}, opt: {})", self.nargs, self.rest)
        }
    }
}

pub struct NodeDisplay<'a>(&'a StableGraph<Node, Edge>, id::Node);

#[allow(unused_variables)]
impl fmt::Display for NodeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let node = self.0.node_weight(self.1).unwrap();

        if node.is_variable_like() {
            write!(f, "v{} = ", self.1.index())?;
        } else if node.is_continuation() {
            write!(f, "k{} = ", self.1.index())?;
        }

        match node {
            Node::Call {
                callee,
                k,
                h,
                args,
                span: _,
            } => {
                let callee = EdgeDisplay(self.0, *callee);
                let k = EdgeDisplay(self.0, *k);
                let h = EdgeDisplay(self.0, *h);
                let args = args
                    .iter()
                    .map(|arg| EdgeDisplay(self.0, *arg).to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{callee}({k}, {h}, {args})",)
            }

            Node::Case {
                test,
                if_true,
                if_false,
            } => {
                let test = EdgeDisplay(self.0, *test);
                let if_true = EdgeDisplay(self.0, *if_true);
                let if_false = EdgeDisplay(self.0, *if_false);

                write!(f, "case {test} -> {if_true} | {if_false}")
            }

            Node::Constant(datum) => {
                write!(f, "const({})", datum)
            }

            Node::Continue { k, args, span: _ } => {
                let k = EdgeDisplay(self.0, *k);
                write!(
                    f,
                    "continue {k}({})",
                    args.iter()
                        .map(|arg| EdgeDisplay(self.0, *arg).to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }

            Node::Func(func) => {
                if let Some(name) = func.name {
                    write!(
                        f,
                        "fn {} (req: {}, opt: {})",
                        INTERNER.resolve(&name),
                        func.nargs,
                        func.rest
                    )
                } else {
                    write!(f, "fn (req: {}, opt: {})", func.nargs, func.rest)
                }
            }

            Node::Continuation {
                name,
                nargs,
                rest,
                body,
                span,
            } => {
                let name = if let Some(name) = name {
                    INTERNER.resolve(&name)
                } else {
                    ""
                };
                write!(f, "cont {name}(req: {nargs}, opt: {rest})",)
            }

            Node::Global(name, _) => {
                write!(f, "global {}", name)
            }

            Node::Param(index) => {
                write!(f, "param {index}")
            }

            Node::Rest(index) => {
                write!(f, "rest {index}")
            }

            Node::PrimRef { name, span } => {
                write!(f, "#%{}", INTERNER.resolve(&name))
            }

            Node::Unfinalized => {
                write!(f, "unfinalized")
            }

            Node::PrimCall {
                name,
                k,
                h,
                args,
                span,
            } => {
                let k = EdgeDisplay(self.0, *k);
                let h = EdgeDisplay(self.0, *h);
                write!(
                    f,
                    "#%{}({}) -> {k} | {h}",
                    INTERNER.resolve(&name),
                    args.iter()
                        .map(|arg| EdgeDisplay(self.0, *arg).to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }

            Node::Raise { k, args, span } => {
                let k = EdgeDisplay(self.0, *k);
                write!(
                    f,
                    "raise {k}({})",
                    args.iter()
                        .map(|arg| EdgeDisplay(self.0, *arg).to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }

            Node::RaiseContinuation => {
                write!(f, "raise_cont")
            }

            Node::ReturnContinuation => {
                write!(f, "return_cont")
            }

            Node::Removed => {
                write!(f, "removed")
            }
        }
    }
}

pub struct EdgeDisplay<'a>(&'a StableGraph<Node, Edge>, id::Edge);

impl fmt::Display for EdgeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let w = self.0.edge_weight(self.1).copied().unwrap();
        let (a_id, b_id) = self.0.edge_endpoints(self.1).unwrap();
        let v_id = if w == Edge::Use {
            a_id 
        } else {
            b_id 
        };
        let v = self.0.node_weight(v_id).unwrap();
        
        if v.is_variable_like() || v.is_func() || v.is_primitive() {
            write!(f, "v{}", v_id.index())
        } else if v.is_continuation() {
            write!(f, "k{}", v_id.index())
        } else {
            write!(f, "<node {}>", v_id.index())
        }
    }
}
