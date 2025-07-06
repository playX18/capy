//! CPS Intermediate Representation
//!
//! Based on [Compiling with Continuations, Continued]
//!
//!
//! [Compiling with Continuations, Continued]: https://www.cs.indiana.edu/~dyb/papers/continuations-continued.pdf

use crate::{
    ast::{Datum, INTERNER, Symbol},
    expand::{IForm, ITerm, LVar, Proc, ProcCase},
    source::Span,
};
use cranelift_entity::{
    EntityList, ListPool, PrimaryMap, SecondaryMap, entity_impl, packed_option::ReservedValue,
};
use lasso::Spur;
use std::{
    borrow::Borrow,
    cell::Cell,
    collections::HashMap,
    fmt,
    ops::{Deref, DerefMut, Index, IndexMut},
};

pub mod analysis;
pub mod opt;
pub mod pretty;

/// A graph representing the CPS program.
pub struct Graph {
    /* main storage arenas */
    pub variables: PrimaryMap<Var, Variable>,
    pub continuations: PrimaryMap<ContVar, Continuation>,
    pub terms: PrimaryMap<TermId, Term>,
    pub functions: PrimaryMap<FuncId, Function>,
    pub values: PrimaryMap<ValueId, Value>,
    pub var_pool: ListPool<Var>,
    pub cont_pool: ListPool<ContVar>,
    pub func_pool: ListPool<FuncId>,

    pub var_occurences: VarOccurences,
    pub cont_occurences: ContOccurences,

    pub entrypoint: Option<FuncId>,
    defining: Result<FuncId, ContVar>,
}

#[derive(Default)]
pub struct VarOccurences {
    pub storage: PrimaryMap<VarOccurenceId, VarOccurence>,
    pub var_to_occurences: SecondaryMap<Var, (Option<VarOccurenceId>, Option<VarOccurenceId>)>,
    pub occurences_in_terms: HashMap<TermId, Vec<VarOccurenceId>>,
}

impl VarOccurences {
    pub fn clear(&mut self) {
        self.storage.clear();
        self.var_to_occurences.clear();
        self.occurences_in_terms.clear();
    }
}

impl ContOccurences {
    pub fn clear(&mut self) {
        self.storage.clear();
        self.var_to_occurences.clear();
        self.occurences_in_terms.clear();
    }
}

impl Index<Var> for VarOccurences {
    type Output = (Option<VarOccurenceId>, Option<VarOccurenceId>);

    fn index(&self, index: Var) -> &Self::Output {
        &self.var_to_occurences[index]
    }
}

impl IndexMut<Var> for VarOccurences {
    fn index_mut(&mut self, index: Var) -> &mut Self::Output {
        &mut self.var_to_occurences[index]
    }
}

impl Index<VarOccurenceId> for VarOccurences {
    type Output = VarOccurence;

    fn index(&self, index: VarOccurenceId) -> &Self::Output {
        &self.storage.get(index).unwrap()
    }
}

impl IndexMut<VarOccurenceId> for VarOccurences {
    fn index_mut(&mut self, index: VarOccurenceId) -> &mut Self::Output {
        self.storage.get_mut(index).unwrap()
    }
}

#[derive(Clone)]
pub struct VarOccurence {
    pub is_recursive: Cell<Option<bool>>,
    pub var: Var,
    pub site: TermId,
    pub prev: Option<VarOccurenceId>,
    pub next: Option<VarOccurenceId>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarOccurenceId(u32);

entity_impl!(VarOccurenceId, "var_occurence");

#[derive(Clone)]
pub struct ContOccurence {
    pub is_recursive: Cell<Option<bool>>,
    pub cont: ContVar,
    pub site: TermId,
    pub prev: Option<ContOccurenceId>,
    pub next: Option<ContOccurenceId>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContOccurenceId(u32);

entity_impl!(ContOccurenceId, "cont_occurence");
#[derive(Default)]
pub struct ContOccurences {
    pub storage: PrimaryMap<ContOccurenceId, ContOccurence>,
    pub var_to_occurences:
        SecondaryMap<ContVar, (Option<ContOccurenceId>, Option<ContOccurenceId>)>,
    pub occurences_in_terms: HashMap<TermId, Vec<ContOccurenceId>>,
}

impl Index<ContVar> for ContOccurences {
    type Output = (Option<ContOccurenceId>, Option<ContOccurenceId>);

    fn index(&self, index: ContVar) -> &Self::Output {
        &self.var_to_occurences[index]
    }
}

impl IndexMut<ContVar> for ContOccurences {
    fn index_mut(&mut self, index: ContVar) -> &mut Self::Output {
        &mut self.var_to_occurences[index]
    }
}

impl Index<ContOccurenceId> for ContOccurences {
    type Output = ContOccurence;

    fn index(&self, index: ContOccurenceId) -> &Self::Output {
        &self.storage.get(index).unwrap()
    }
}

impl IndexMut<ContOccurenceId> for ContOccurences {
    fn index_mut(&mut self, index: ContOccurenceId) -> &mut Self::Output {
        self.storage.get_mut(index).unwrap()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueId(u32);
entity_impl!(ValueId, "value");

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExprId(u32);

entity_impl!(ExprId, "expr");

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncId(u32);

entity_impl!(FuncId, "func");

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContVar(u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(u32);

entity_impl!(ContVar, "k");
entity_impl!(Var, "v");

/// Represents a single CPS term in a graph.
///
/// Each term holds a reference to its parent term, a variant that describes the type of term it is, and optionally a reference to the next term in the sequence.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Term {
    pub parent: Option<TermId>,
    pub next: Option<TermId>,
    pub definition: TermDef,
    /// A function or continuation body where this term
    /// is defined in.
    pub defined_in: Result<FuncId, ContVar>,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TermDef {
    Letv(Var, ValueId),
    /// `letk` defines a continuation `k` in scope `K`.
    Letk1(ContVar),
    /// `letkrec` defines recursive continuations `k1...kn` in scope `K`.
    LetkRec(EntityList<ContVar>),

    /// `fix` is a special term that represents
    /// mutually recursive functions.
    Fix(EntityList<FuncId>),

    /// `funcall` is a function call to a function `f` with arguments `args` and continuation `k`.
    Funcall(
        Var,
        ContVar, /* continuation */
        ContVar, /* error handler */
        EntityList<Var>,
    ),

    PrimCall(Spur, ContVar, ContVar, EntityList<Var>),

    /// `continue k args ...`: invoke continuation k with args.
    Continue(ContVar, EntityList<Var>),

    /// Throw error with `k`, `tag` and `args` into continuation `h`.
    Throw(ContVar, ContVar, Var, EntityList<Var>),

    /// `case v k1 | k2` if `v` is true jumps to `k1`, otherwise jumps to `k2`.
    Case(Var, ContVar, ContVar),

    /// Similar to `case` but checks arity of the arguments
    /// passed to function.
    ///
    /// If arity matches execution continues with continuation `k`,
    /// otherwise continuation `h` is invoked.
    ///
    /// If `h` is None this term would check `k` arity
    /// and if it does not match will throw runtime error.
    Arity(ContVar, Option<ContVar>),

    Halt,

    /// Indicates that the term has been removed from the graph.
    ///
    /// We use arena allocation so terms cannot be freed from memory, but we can mark them as removed.
    Removed,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermId(u32);

entity_impl!(TermId, "term");

#[derive(Clone)]
pub enum Continuation {
    /// A return continuation.
    ///
    /// This continuation is used to return a value from a function.
    ///
    /// NOTE: This continuation type is a little tricky: we don't really reify
    /// it as we treat all `Return` continuations as closures in backend. But
    /// there might be a contification pass and then this continuation might be un-reified
    /// by conversion to `Local`.
    Return(FuncId /* function that defines this continuation */),

    /// Continuation that is defined inside some lexical scope.
    ///
    /// We can think of it as a function that takes some arguments and returns a value.
    Local {
        args: EntityList<Var>,
        variadic: Option<Var>,
        body: TermId,
        /// Term that defines this continuation.
        definition: TermId,
    },

    /// Continuation has not been built yet. This variant is usually only
    /// constructed during construction of graph.
    Unfinalized,

    Removed,
}
#[derive(Clone)]
pub struct Function {
    pub name: Option<Spur>,
    /// The continuation that this function returns to.
    pub return_continuation: ContVar,
    /// The continuation that this function returns to
    /// if error has occured.
    pub error_continuation: ContVar,
    pub body: TermId,
    pub bound_to: Var,
}

#[derive(Clone)]
pub struct Variable {
    /// Definition of this variable.
    pub definition: VarDef,
}

#[derive(Clone, Copy)]
pub enum VarDef {
    InTerm(TermId),
    Func(FuncId, Option<TermId>),
    /// Indicates that variable is bound to argument N
    /// in function F and entrypoint K.
    Argument(usize, FuncId, ContVar),

    /// Indicates that variable is bound to rest argument starting
    /// from N in function F and entrypoint K.
    Rest(usize, FuncId, ContVar),
    /// Indicates that variable is bound to continuation argument
    /// N in continuation K.
    ContArgument(usize, ContVar),
    /// Indicates that variable is bound to rest argument starting
    /// from N in continuation K.
    ContRest(usize, ContVar),
    /// Variable is unbound.
    Unbound,

    Removed,
}

use crate::ast::P;
#[derive(Clone)]
pub enum Value {
    Const(P<Datum>),
    Global(P<Symbol>),
    PrimRef(Spur),
    /// A non recursive function.
    Func(FuncId),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Const(c) => write!(f, "'{c}"),
            Value::Global(g) => write!(f, "{g}"),
            Value::PrimRef(p) => write!(f, "#%{}", INTERNER.resolve(p)),
            Value::Func(_f) => write!(f, "&{_f:?}"),
        }
    }
}

impl From<P<Datum>> for Value {
    fn from(value: P<Datum>) -> Self {
        Self::Const(value)
    }
}

impl From<P<Symbol>> for Value {
    fn from(value: P<Symbol>) -> Self {
        Self::Global(value)
    }
}

impl Graph {
    pub fn new() -> Self {
        Self {
            variables: Default::default(),
            continuations: Default::default(),
            terms: Default::default(),
            functions: Default::default(),
            values: Default::default(),
            var_pool: Default::default(),
            func_pool: Default::default(),
            cont_pool: Default::default(),
            var_occurences: Default::default(),
            cont_occurences: Default::default(),
            entrypoint: None,
            defining: Ok(FuncId::reserved_value()),
        }
    }

    pub fn remove_occurence(&mut self, occurence: VarOccurenceId) {
        let var_occurence = &self.var_occurences[occurence];

        let var = var_occurence.var;
        let next = var_occurence.next;
        let prev = var_occurence.prev;

        let (head, tail) = self.var_occurences[var_occurence.var];
        if Some(occurence) == head {
            self.var_occurences[var].0 = next;
        }

        if Some(occurence) == tail {
            self.var_occurences[var].1 = prev;
        }

        if let Some(prev) = prev {
            self.var_occurences[prev].next = next;
        }

        if let Some(next) = next {
            self.var_occurences[next].prev = prev;
        }
    }

    pub fn remove_occurence_of_cont(&mut self, occurence: ContOccurenceId) {
        let var_occurence = &self.cont_occurences[occurence];

        let var = var_occurence.cont;
        let next = var_occurence.next;
        let prev = var_occurence.prev;

        let (head, tail) = self.cont_occurences[var];
        if Some(occurence) == head {
            self.cont_occurences[var].0 = next;
        }

        if Some(occurence) == tail {
            self.cont_occurences[var].1 = prev;
        }

        if let Some(prev) = prev {
            self.cont_occurences[prev].next = next;
        }

        if let Some(next) = next {
            self.cont_occurences[next].prev = prev;
        }
    }

    pub fn number_of_occurences_of_var(&self, var: Var) -> usize {
        let (head, _tail) = self.occurences_of_var(var);
        if head.is_none() {
            return 0;
        }

        let mut count = 0;
        let mut current = head;
        while let Some(id) = current {
            count += 1;
            current = self.var_occurences[id].next;
        }
        count
    }

    pub fn number_of_occurences_of_cont(&self, var: ContVar) -> usize {
        let (head, _tail) = self.occurences_of_cont(var);
        if head.is_none() {
            return 0;
        }

        let mut count = 0;
        let mut current = head;
        while let Some(id) = current {
            count += 1;
            current = self.cont_occurences[id].next;
        }
        count
    }

    pub fn occurences_of_var(&self, var: Var) -> (Option<VarOccurenceId>, Option<VarOccurenceId>) {
        self.var_occurences
            .var_to_occurences
            .get(var)
            .copied()
            .unwrap_or((None, None))
    }

    pub fn occurences_of_cont(
        &self,
        var: ContVar,
    ) -> (Option<ContOccurenceId>, Option<ContOccurenceId>) {
        self.cont_occurences
            .var_to_occurences
            .get(var)
            .copied()
            .unwrap_or((None, None))
    }

    pub fn add_occurence_of_var(
        &mut self,
        var: Var,
        site: TermId,
        _recursive: bool,
    ) -> VarOccurenceId {
        let (head, tail) = self.occurences_of_var(var);

        let new_tail = self.var_occurences.storage.push(VarOccurence {
            is_recursive: Cell::new(None),
            var,
            site,
            prev: tail,
            next: None,
        });

        let head = match tail {
            Some(old_tail) => {
                self.var_occurences[old_tail].next = Some(new_tail);
                head
            }

            None => Some(new_tail),
        };

        self.var_occurences.var_to_occurences[var] = (head, Some(new_tail));
        new_tail
    }
    pub fn add_occurence_of_cont(
        &mut self,
        var: ContVar,
        site: TermId,
        _recursive: bool,
    ) -> ContOccurenceId {
        let (head, tail) = self.occurences_of_cont(var);

        let new_tail = self.cont_occurences.storage.push(ContOccurence {
            is_recursive: Cell::new(None),
            cont: var,
            site,
            prev: tail,
            next: None,
        });

        let head = match tail {
            Some(old_tail) => {
                self.cont_occurences[old_tail].next = Some(new_tail);
                head
            }

            None => Some(new_tail),
        };

        self.cont_occurences.var_to_occurences[var] = (head, Some(new_tail));
        new_tail
    }

    pub fn letkrec<'b>(
        &mut self,
        conts: impl IntoIterator<Item = (&'b [Var], Option<Var>, TermId)> + 'b,
    ) -> (
        Vec<ContVar>,
        Box<dyn FnOnce(&mut Graph, TermId) -> TermId + 'b>,
    ) {
        let conts = conts.into_iter().collect::<Vec<_>>();
        let vars = conts
            .iter()
            .map(|_| self.continuations.push(Continuation::Unfinalized))
            .collect::<Vec<ContVar>>();
        let v = vars.clone();

        let build = move |cps: &mut Graph, next| {
            let cvars = EntityList::from_slice(&vars, &mut cps.cont_pool);
            let term = cps.terms.push(Term {
                parent: None,
                next: Some(next),
                definition: TermDef::LetkRec(cvars),
                span: Span::default(),
                defined_in: cps.defining,
            });

            for (var, (args, variadic, body)) in vars.iter().zip(conts.into_iter()) {
                let args = EntityList::from_slice(&args, &mut cps.var_pool);
                cps.continuations[*var] = Continuation::Local {
                    args,
                    variadic,
                    body,
                    definition: term,
                };
            }

            cps.terms[next].parent = Some(term);

            term
        };

        (v, Box::new(build))
    }

    pub fn fresh_continuation(&mut self) -> ContVar {
        self.continuations.push(Continuation::Unfinalized)
    }

    pub fn unbound(&mut self) -> Var {
        self.variables.push(Variable {
            definition: VarDef::Unbound,
        })
    }

    pub fn fix(
        &mut self,
        vars: impl AsRef<[Var]>,
        funcs: impl AsRef<[FuncId]>,
    ) -> ((), Box<dyn FnOnce(&mut Graph, TermId) -> TermId>) {
        let vars = vars.as_ref().to_vec();
        let funcs = funcs.as_ref();

        let funcs = EntityList::from_slice(funcs, &mut self.func_pool);

        let build = move |cps: &mut Graph, next| {
            let term = cps.terms.push(Term {
                defined_in: cps.defining,
                parent: None,
                next: Some(next),
                definition: TermDef::Fix(funcs),
                span: Span::default(),
            });

            cps.terms[next].parent = Some(term);

            for (i, &var) in vars.iter().enumerate() {
                let func = funcs.get(i, &cps.func_pool).unwrap();

                cps.variables[var].definition = VarDef::Func(func, Some(term));
                cps.terms[cps.functions[func].body].defined_in = cps.defining
            }

            term
        };

        ((), Box::new(build))
    }

    /// Construct `letk` term. Returns a continuation variable and closure to finalize
    /// construction. Closure accepts next term in the graph
    /// to continue execution to and returns a newly constructed definition of continuation.
    pub fn letk(
        &mut self,
        args: impl AsRef<[Var]>,
        variadic: Option<Var>,
        body: TermId,
    ) -> (ContVar, Box<dyn FnOnce(&mut Graph, TermId) -> TermId>) {
        let args = args.as_ref();
        let cont = self.continuations.push(Continuation::Unfinalized);

        for (i, arg) in args.iter().enumerate() {
            self.variables[*arg].definition = VarDef::ContArgument(i, cont);
        }

        if let Some(variadic) = variadic {
            self.variables[variadic].definition = VarDef::ContRest(args.len(), cont);
        }

        let args = EntityList::from_slice(args.as_ref(), &mut self.var_pool);
        let build = move |graph: &mut Graph, next| {
            let term = graph.terms.push(Term {
                defined_in: graph.defining,
                parent: None,
                span: Span::default(),
                definition: TermDef::Letk1(cont),
                next: Some(next),
            });

            graph.continuations[cont] = Continuation::Local {
                args,
                variadic,
                body,
                definition: term,
            };
            graph.terms[next].parent = Some(term);
            graph.terms[body].defined_in = Err(cont);

            term
        };

        (cont, Box::new(build))
    }

    pub fn letv(
        &mut self,
        value: impl Into<Value>,
    ) -> (Var, Box<dyn FnOnce(&mut Graph, TermId) -> TermId>) {
        let val = self.values.push(value.into());
        let var = self.variables.push(Variable {
            definition: VarDef::Unbound,
        });
        let build = move |graph: &mut Graph, next| {
            let term = graph.terms.push(Term {
                defined_in: graph.defining,
                parent: None,
                definition: TermDef::Letv(var, val),
                next: Some(next),
                span: Span::default(),
            });

            graph.variables[var].definition = VarDef::InTerm(term);
            graph.terms[next].parent = Some(term);
            term
        };

        (var, Box::new(build))
    }

    pub fn primcall(
        &mut self,
        name: &str,
        k: ContVar,
        h: ContVar,
        args: impl AsRef<[Var]>,
    ) -> TermId {
        let name = INTERNER.get_or_intern(name);
        self.primcall_(name, k, h, args)
    }

    pub fn primcall_(
        &mut self,
        name: impl Borrow<Spur>,
        k: ContVar,
        h: ContVar,
        args: impl AsRef<[Var]>,
    ) -> TermId {
        let args = EntityList::from_slice(args.as_ref(), &mut self.var_pool);

        let term = self.terms.push(Term {
            defined_in: self.defining,
            parent: None,
            next: None,
            span: Span::default(),
            definition: TermDef::PrimCall(*name.borrow(), k, h, args),
        });

        term
    }
    pub fn continue_(
        &mut self,
        k: ContVar,
        args: impl IntoIterator<Item = impl Borrow<Var>>,
    ) -> TermId {
        let args = EntityList::from_iter(
            args.into_iter().map(|var| *var.borrow()),
            &mut self.var_pool,
        );

        self.terms.push(Term {
            defined_in: self.defining,
            parent: None,
            next: None,
            span: Span::default(),
            definition: TermDef::Continue(k, args),
        })
    }

    pub fn funcall(&mut self, f: Var, k: ContVar, h: ContVar, args: impl AsRef<[Var]>) -> TermId {
        let args = EntityList::from_slice(args.as_ref(), &mut self.var_pool);
        self.terms.push(Term {
            defined_in: self.defining,
            parent: None,
            next: None,
            definition: TermDef::Funcall(f, k, h, args),
            span: Span::default(),
        })
    }

    pub fn halt(&mut self, parent: Option<TermId>) -> TermId {
        self.terms.push(Term {
            defined_in: self.defining,
            parent,
            next: None,
            definition: TermDef::Halt,
            span: Span::default(),
        })
    }

    /// Splices a new node `new` in place of an existing node `old`.
    pub fn splice(&mut self, old: TermId, new: TermId) {
        let old_term = self.terms[old];
        let old_parent = old_term.parent;
        let old_next = old_term.next;

        // Update the new term's parent and next
        self.terms[new].parent = old_parent;
        if old_next != Some(new) && old_next.is_some() {
            self.terms[new].next = old_next;
        }

        // Update parent's next pointer if it exists
        if let Some(parent) = old_parent {
            if self.terms[parent].next == Some(old) {
                self.terms[parent].next = Some(new);
            }
        } else if let Ok(func) = old_term.defined_in {
            self.functions[func].body = new;
            self.terms[new].defined_in = Ok(func);
        } else if let Err(cont) = old_term.defined_in {
            if let Continuation::Local { body, .. } = &mut self.continuations[cont] {
                *body = new;
            }
            self.terms[new].defined_in = Err(cont);
        }

        // Update next term's parent pointer if it exists and isn't already pointing to new
        if let Some(next) = old_next {
            if next != new && self.terms[next].parent == Some(old) {
                self.terms[next].parent = Some(new);
            }
        }

        // Mark the old term as removed
        self.terms[old].definition = TermDef::Removed;
    }
}

/// A helper macro to construct CPS form without any boilerplate code.
///
/// Syntax:
///
///
/// ```text
/// letk k (rv0 rv1 ...) = $expr;
/// letv v = $expr;
/// binder <- $expr;
/// #$expr;
/// @tk (h) var;
/// @tk* (h) vars;
///
/// /* tail expressions */
/// f(k, h, arg0, arg1, ...)
/// f(k, h, args...)
/// % prim (k, h, arg0, arg1, ...)
/// % prim (k, h, args...)
/// continue k (arg0, arg1, ....)
/// continue k (args...)
/// case test => k1 | k2
/// #expr
/// @tk (h) var
/// @tk* (h) vars
/// ```
///
/// Language consists of two kinds of expressions: binders and
/// tail expressions. Binders never can be final expressions in the macro invocation.
///
/// `letk` is used to create a new continuation `k` which accepts arguments specified inside
/// parenthesis and continuation body is produced by `$expr`.
///
/// `letv` is used to create a new variable with some value produced by `$expr`.
///
/// `binder <- $expr` expects `$expr` to produce pair of (`var`, `cont`) where `var`
/// is a variable that is bound to a term produced by `cont`. `cont` must be a closure
/// which accepts CPS graph and `next` term and produce a term.
///
/// `#expr` executes expression in the lexical scope of terms coming before the expression.
///
/// `@tk* var` and `@tk* (h) vars` is used to recursively perform higher order conversion to CPS
/// on a Tree IL form stored in `var` and then bind it to `var`.
///
/// Tail expressions always appear at the end of `with_cps` invocation.
///
/// `f(k, h, arg0, arg1, ...)` builds a function call to variable `f` with continuations `k` and `h` and
/// arguments `arg0`, `arg1` etc. There is a second form of this expression
/// which accepts `args...` as valid input, in that case variable you pass to the
/// constructor must be a slice of arguments.
///
/// `continue k (...)` calls continuation `k` with provided arguments. Also provides
/// two forms like function call.
///
/// `% prim (k, h, ...)` calls primitive function `prim` with continuations and arguments.
///
/// `#expr` executes expression as is in the lexical scope of terms coming before the expression.
#[macro_export]
macro_rules! with_cps {
    ($graph: ident;
        $binder: ident <- $expr: expr; $($rest:tt)+
    ) => {
        {
        let ($binder, cont) = $expr;

        let inner = { with_cps!($graph; $($rest)+) };

        cont($graph, inner)
    }};

    ($graph: ident;
        letk $k: ident ($($rv: ident),*) = $term: expr; $($rest:tt)+
    ) => {{
        $(
            let $rv = $graph.unbound();
        )*
        let term = $term;
        with_cps!($graph;
            $k <- $graph.letk(&[$($rv),*], None, term);
            $($rest)+
        )
    }};

    ($graph: ident;
        letv $v: ident = $value: expr; $($rest:tt)+
    ) => {{
        let value = $value;
        with_cps!(
            $graph;
            $v <- $graph.letv(value);
            $($rest)+
        )
    }};

    ($graph: ident; # $expr: expr; $($rest:tt)+) => {
        {
            $expr;
            with_cps!($graph; $($rest)+)
        }
    };


    ($graph: ident; # $expr: expr) => {
        $expr
    };

    ($graph: ident; case $test: ident => $k1: ident | $k2: ident) => {
        {let defining = $graph.defining;
        $graph.terms.push($crate::cps::Term {
            defined_in: defining,
            next: None,
            parent: None,
            span: Span::default(),
            definition: TermDef::Case($test, $k1, $k2)
        })}
    };

    ($graph: ident; continue $k: ident ($($arg: ident),*)) => {
        $graph.continue_($k, &[$($arg),*])
    };

    ($graph: ident; $f: ident ($k: ident, $h: ident $(,)? $($arg: ident),*)) => {
        $graph.funcall($f, $k, $h, [$($arg),*])
    };

    ($graph: ident; $f: ident ($k: ident, $h: ident, $args: ident ...)) => {
        $graph.funcall($f, $k, $h, $args)
    };

    ($graph: ident; % $f: literal ($k: ident, $h: ident $(,)? $($arg: ident),*)) => {
        $graph.primcall($f, $k, $h, &[$($arg),*])
    };

    ($graph: ident; % $f: literal ($k: ident, $h: ident, $args: ident ...)) => {
        $graph.primcall($f, $k, $h, $args)
    };

    ($graph: ident; % $f: ident ($k: ident, $h: ident, $args: ident ...)) => {
        $graph.primcall_($f, $k, $h, $args)
    };

    ($graph: ident; @tk ($h: ident) $var: ident; $($rest:tt)+) => {
        $graph.t_k($var, Box::new(move |$graph, $var| {
            with_cps!($graph; $($rest)+)
        }), $h)
    };

    ($graph: ident; @tk* ($h: ident) $vars: ident; $($rest:tt)+) => {

        $graph.t_k_many($vars, Box::new(move |$graph, $vars| {
            with_cps!($graph; $($rest)+)
        }), $h)
    };

    ($graph: ident; @tc ($k: ident, $h: ident) $var: ident) => {
        $graph.t_c($var, $k, $h)
    };


    ($graph: ident; @tc ($k: ident, $h: ident) $var: ident; $($rest:tt)+) => {{
        let $var = $graph.t_c($var, $k, $h);
        with_cps!($graph; $($rest)+)
    }};


}

pub struct CpsConverter<'a> {
    pub graph: &'a mut Graph,
    pub lvar_to_var: HashMap<P<LVar>, Var>,
}

impl<'a> Deref for CpsConverter<'a> {
    type Target = Graph;

    fn deref(&self) -> &Self::Target {
        &self.graph
    }
}

impl<'a> DerefMut for CpsConverter<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.graph
    }
}

impl<'a> CpsConverter<'a> {
    pub fn new(graph: &'a mut Graph) -> Self {
        Self {
            graph,
            lvar_to_var: HashMap::new(),
        }
    }

    pub fn t_c(&mut self, form: &IForm, k: ContVar, h: ContVar) -> TermId {
        let cps = self;
        match &form.term {
            ITerm::LRef(lvar) => {
                let var = cps.lvar_to_var[lvar];

                with_cps!(cps;
                    continue k (var)
                )
            }

            ITerm::Const(c) => {
                with_cps!(cps;
                    letv v = c.clone();
                    continue k (v)
                )
            }

            ITerm::LSet(_, _) => {
                unreachable!("must be removed at Tree IL level")
            }

            ITerm::GRef(var) => {
                with_cps!(cps;
                    letv v = var.clone();
                    continue k (v)
                )
            }

            ITerm::GSet(var, val) => {
                with_cps!(cps;
                    @tk (h) val;
                    letv sym = var.clone();
                    % "gset" (k, h, sym, val)
                )
            }

            ITerm::PrimRef(name) => with_cps!(cps;
                letv v = Value::PrimRef(*name);
                continue k(v)
            ),

            ITerm::Seq(seq) => with_cps!(cps;
                @tk* (h) seq;
                # {
                  cps.continue_(k, &[*seq.last().unwrap()])
                }
            ),

            ITerm::Define(var, val) => with_cps!(cps;
                @tk (h) val;
                letv sym = var.clone();
                % "define" (k, h, sym, val)
            ),

            ITerm::Let(l) => {
                let inits = &l.initializers;
                let body = &l.body;

                with_cps!(cps;
                   @tk* (h) inits;
                   #
                       for (lvar, ivar) in l.variables.iter().zip(inits.iter()) {
                           cps.lvar_to_var.insert(lvar.clone(), *ivar);
                       };
                   @tk (h) body;
                   continue k(body)
                )
            }

            ITerm::Fix(_) => with_cps!(cps;
                @tk (h) form;
                continue k(form)
            ),

            ITerm::Proc(_) => with_cps!(cps;
                @tk (h) form;
                continue k(form)
            ),
            ITerm::If(test, cons, alt) => with_cps!(cps;
                @tk (h) test;
                letk kcons () = with_cps!(cps;
                    @tc (k, h) cons
                );
                letk kalt () = with_cps!(cps;
                    @tc (k, h) alt
                );

                case test => kcons | kalt
            ),

            ITerm::App(proc, args) => {
                with_cps!(cps;
                    @tk* (h) args;
                    @tk (h) proc;
                    proc(k, h, args...)
                )
            }

            ITerm::PrimApp(name, args) => {
                with_cps!(cps;
                    @tk* (h) args;
                    % name (k, h, args...)
                )
            }
        }
    }

    pub fn t_k<'b>(
        &mut self,
        form: &'b IForm,
        fk: Box<dyn FnOnce(&mut Self, Var) -> TermId + 'b>,
        h: ContVar,
    ) -> TermId {
        let cps = self;
        match &form.term {
            ITerm::LRef(lvar) => {
                let var = cps.lvar_to_var[lvar];

                fk(cps, var)
            }

            ITerm::Const(c) => {
                with_cps!(cps;
                    letv v = c.clone();
                    # fk(cps, v)
                )
            }

            ITerm::GRef(sym) => {
                with_cps!(cps;
                    letv v = sym.clone();
                    # fk(cps, v)
                )
            }

            ITerm::GSet(sym, val) => {
                with_cps!(cps;
                    @tk (h) val;
                    letv sym = sym.clone();
                    letk k (rv) = fk(cps,rv);
                    % "gset" (k, h, sym, val)
                )
            }

            ITerm::LSet(_, _) => panic!("must be removed in Tree IL"),

            ITerm::PrimRef(name) => with_cps!(cps;
                letv v = Value::PrimRef(*name);
                # fk(cps, v)
            ),
            ITerm::Seq(seq) => with_cps!(cps;
                @tk* (h) seq;
                # fk(cps, *seq.last().unwrap())),

            ITerm::Define(var, val) => {
                with_cps!(cps;
                    @tk (h) val;
                    letv v = var.clone();
                    letk k(rv) = fk(cps, rv);
                    % "define" (k, h, v, val)
                )
            }

            ITerm::Let(l) => {
                let inits = &l.initializers;
                let body = &l.body;
                with_cps!(cps;
                    @tk* (h) inits;
                    #
                        for (lvar, ivar) in l.variables.iter().zip(inits.iter()) {
                            cps.lvar_to_var.insert(lvar.clone(), *ivar);
                        };

                    @tk (h) body;
                    # fk(cps, body)
                )
            }

            ITerm::Fix(fix) => {
                let vars = fix
                    .variables
                    .iter()
                    .map(|lvar| {
                        let var = cps.graph.unbound();
                        cps.lvar_to_var.insert(lvar.clone(), var);
                        var
                    })
                    .collect::<Vec<Var>>();

                let funcs = fix
                    .procedures
                    .iter()
                    .zip(vars.iter())
                    .map(|(func, &var)| cps.convert_proc(var, func))
                    .collect::<Vec<FuncId>>();

                let body = &fix.body;
                with_cps!(cps;
                    _fix <- cps.graph.fix(vars, funcs);
                    @tk (h) body;
                    # fk(cps, body)
                )
            }

            ITerm::Proc(proc) => {
                let var = cps.graph.unbound();
                let func = cps.convert_proc(var, proc);

                with_cps!(cps;
                    _fix <- cps.graph.fix(&[var], &[func]);
                    # fk(cps, var)
                )
            }

            ITerm::If(test, cons, alt) => {
                with_cps!(cps;
                    @tk (h) test;
                    letk kcontinue (rv) = fk(cps, rv);
                    letk kcons () = with_cps!(cps;
                        @tc (kcontinue, h) cons
                    );
                    letk kalt () = with_cps!(cps;
                        @tc (kcontinue, h) alt
                    );

                    case test => kcons | kalt
                )
            }

            ITerm::App(proc, args) => {
                with_cps!(cps;
                    @tk* (h) args;
                    @tk (h) proc;
                    letk k (rv) = fk(cps, rv);
                    proc(k, h, args...)
                )
            }

            ITerm::PrimApp(name, args) => {
                with_cps!(cps;
                    @tk* (h) args;
                    letk k (rv) = fk(cps, rv);
                    % name (k, h, args...)
                )
            }
        }
    }

    pub fn t_k_many<'b>(
        &mut self,
        forms: &'b [P<IForm>],
        fk: Box<dyn FnOnce(&mut Self, Vec<Var>) -> TermId + 'b>,
        h: ContVar,
    ) -> TermId {
        fn process_next<'a, 'b>(
            cps: &mut CpsConverter<'a>,
            forms: &'b [P<IForm>],
            mut results: Vec<Var>,
            fk: Box<dyn FnOnce(&mut CpsConverter<'a>, Vec<Var>) -> TermId + 'b>,
            h: ContVar,
        ) -> TermId {
            if forms.is_empty() {
                return fk(cps, results);
            }
            let (head, rest) = forms.split_at(1);

            cps.t_k(
                &head[0],
                Box::new(move |cps, head| {
                    results.push(head);
                    process_next(cps, rest, results, fk, h)
                }),
                h,
            )
        }

        process_next(self, forms.as_ref(), Vec::new(), fk, h)
    }

    /// Convert regular procedure into CPS function.
    pub fn convert_proc(&mut self, var: Var, proc: &Proc) -> FuncId {
        let k = self.graph.fresh_continuation();
        let h = self.graph.fresh_continuation();
        let cases = proc
            .cases
            .iter()
            .map(|case| {
                let args = case
                    .args
                    .iter()
                    .map(|arg| {
                        let var = self.graph.unbound();
                        self.lvar_to_var.insert(arg.clone(), var);
                        var
                    })
                    .collect::<Vec<Var>>();
                let variadic = case.variadic.clone().map(|lvar| {
                    let var = self.graph.unbound();
                    self.lvar_to_var.insert(lvar, var);
                    var
                });

                let body = self.t_c(&case.body, k, h);
                self.graph.terms[body].span = case.loc.unwrap_or(Default::default());
                let (k, cont) = self.graph.letk(&args, variadic, body);
                (k, cont)
            })
            .collect::<Vec<_>>();

        let mut t = self.graph.terms.push(Term {
            defined_in: self.defining,
            parent: None,
            next: None,
            definition: TermDef::Halt,
            span: Span::default(),
        });

        let mut next = None;
        for (k, cont) in cases.into_iter().rev() {
            t = with_cps!(self;
                k <- (k, cont);
                #{
                    let term = self.graph.terms.push(Term {
                        defined_in: self.graph.defining,
                        parent: None,
                        next: None,
                        definition: TermDef::Arity(k, next),
                        span: Span::default()
                    });
                    next = Some(k);
                    term
               }
            );
        }

        let func = self.graph.functions.push(Function {
            name: proc
                .name
                .as_ref()
                .map(|x| INTERNER.get_or_intern(&x.to_string())),
            return_continuation: k,
            error_continuation: h,
            body: t,
            bound_to: var,
        });

        self.graph.terms[t].defined_in = Ok(func);
        self.graph.variables[var].definition = VarDef::Func(func, None);

        func
    }
}

/// Given a program convert it to CPS graph IR.
pub fn program_to_graph(forms: &[P<IForm>]) -> Graph {
    let mut graph = Graph::new();

    let body = P(IForm {
        span: Default::default(),
        term: ITerm::Seq(forms.to_vec()),
    });

    let proc = Proc {
        loc: Some(Default::default()),
        name: Some(Datum::make_symbol("%entrypoint", None)),
        cases: vec![ProcCase {
            loc: Some(Default::default()),
            args: vec![],
            variadic: None,
            body,
        }],
    };

    let mut pass = CpsConverter {
        lvar_to_var: HashMap::new(),
        graph: &mut graph,
    };

    let var = pass.unbound();
    let func = pass.convert_proc(var, &proc);

    graph.entrypoint = Some(func);

    graph
}
