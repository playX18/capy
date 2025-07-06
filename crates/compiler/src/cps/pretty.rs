use ::pretty::{DocAllocator, Pretty};

use crate::cps::*;

pub struct PrettyTerm<'a>(&'a Graph, TermId);
pub struct PrettyCont<'a>(&'a Graph, ContVar);
pub struct PrettyFunc<'a>(&'a Graph, FuncId);

pub struct PrettyVal<'a>(&'a Graph, ValueId);

impl<'a, D, A> Pretty<'a, D, A> for PrettyVal<'a>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: Clone + 'a,
{
    fn pretty(self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A> {
        allocator.text(self.0.values[self.1].to_string())
    }
}

impl<'a, D, A> Pretty<'a, D, A> for PrettyCont<'a>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: Clone + 'a,
{
    fn pretty(self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A> {
        match self.0.continuations[self.1] {
            Continuation::Return(_) => allocator.text("return"),
            Continuation::Local {
                args,
                variadic,
                body,
                definition: _,
            } => {
                let args = args.as_slice(&self.0.var_pool);
                ((allocator.intersperse(args.iter().copied(), allocator.space())
                    + variadic.map(|v| allocator.text(format!(" . k{}", v.as_u32()))))
                .group()
                .parens()
                    + allocator.text(" =")
                    + allocator.line()
                    + PrettyTerm(self.0, body).pretty(allocator))
                .nest(2)
                .group()
            }

            Continuation::Unfinalized => unreachable!(),

            Continuation::Removed => {
                allocator.text("<removed>")
            }
        }
    }
}

impl<'a, D, A> Pretty<'a, D, A> for Var
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: Clone + 'a,
{
    fn pretty(self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A> {
        allocator.text(format!("v{}", self.as_u32()))
    }
}

impl<'a, D, A> Pretty<'a, D, A> for ContVar
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: Clone + 'a,
{
    fn pretty(self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A> {
        allocator.text(format!("k{}", self.as_u32()))
    }
}

impl<'a, D, A> Pretty<'a, D, A> for PrettyTerm<'a>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: Clone + 'a,
{
    fn pretty(self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A> {
        let term = &self.0.terms[self.1];

        let doc = match term.definition {
            TermDef::Arity(k1, k2) => {
                allocator.text("arity")
                    + if let Some(k2) = k2 {
                        allocator.text(format!(" k{} | k{}", k1.as_u32(), k2.as_u32()))
                    } else {
                        allocator.text(format!(" k{}", k1.as_u32()))
                    }
            }
            TermDef::Halt => allocator.text("halt"),

            TermDef::Removed => allocator.text("removed"),

            TermDef::Case(test, k1, k2) => {
                allocator.text("case ")
                    + test
                    + allocator.text(" => ")
                    + allocator.text(format!("k{} | k{}", k1.as_u32(), k2.as_u32()))
            }

            TermDef::Continue(k, args) => {
                let args_doc = allocator.intersperse(
                    args.as_slice(&self.0.var_pool).iter().copied(),
                    allocator.space(),
                );
                allocator.text("continue ")
                    + k.pretty(allocator)
                    + allocator.text(" (")
                    + args_doc
                    + allocator.text(")")
            }

            TermDef::Fix(fix) => {
                let funcs = fix.as_slice(&self.0.func_pool);
                let func_docs = allocator.intersperse(
                    funcs
                        .iter()
                        .map(|f| PrettyFunc(self.0, *f).pretty(allocator)),
                    allocator.line(),
                );
                (allocator.text("fix") + allocator.line() + func_docs.group()).nest(2)
            }

            TermDef::Letk1(k) => {
                if let Continuation::Local { .. } = self.0.continuations[k] {
                    allocator.text("letk ")
                        + k.pretty(allocator)
                        + allocator.space()
                        + PrettyCont(self.0, k).pretty(allocator).nest(2)
                        + allocator.hardline()
                } else {
                    unreachable!()
                }
            }

            TermDef::LetkRec(conts) => {
                let cont_docs = allocator.intersperse(
                    conts
                        .as_slice(&self.0.cont_pool)
                        .iter()
                        .map(|c| PrettyCont(self.0, *c).pretty(allocator)),
                    allocator.line(),
                );
                allocator.text("letk ") + allocator.line() + cont_docs.group().nest(2)
            }

            TermDef::Letv(var, val) => {
                let val_doc = PrettyVal(self.0, val).pretty(allocator);
                allocator.text("letv ") + var.pretty(allocator) + allocator.text(" = ") + val_doc
            }

            TermDef::Funcall(f, k, h, args) => {
                let args_doc = allocator.intersperse(
                    args.as_slice(&self.0.var_pool).iter().copied(),
                    allocator.space(),
                );
                f.pretty(allocator)
                    + (k.pretty(allocator) + allocator.space() + h.pretty(allocator) + if args.is_empty() {
                        allocator.nil()
                    } else {
                        allocator.space() + args_doc
                    })
                        .parens()
            }

            TermDef::PrimCall(name, k, h, args) => {
                let args_doc = allocator.intersperse(
                    args.as_slice(&self.0.var_pool).iter().copied(),
                    allocator.space(),
                );
                allocator.text("#%")
                    + INTERNER.resolve(&name).to_owned().pretty(allocator)
                    + (k.pretty(allocator)
                        + allocator.space()
                        + h.pretty(allocator)
                        + if args.is_empty() {
                            allocator.nil()
                        } else {
                            allocator.space() + args_doc
                        })
                        .parens()
            }

            TermDef::Throw(k, h, tag, args) => {
                let args_doc = allocator.intersperse(
                    args.as_slice(&self.0.var_pool).iter().copied(),
                    allocator.space(),
                );
                allocator.text("throw ")
                    + (k.pretty(allocator)
                        + allocator.space()
                        + h.pretty(allocator)
                        + allocator.space()
                        + tag.pretty(allocator)
                        + if !args.is_empty() {
                            allocator.space() + args_doc
                        } else {
                            allocator.nil()
                        })
                    .group()
                    .parens()
            }
        };
        if let Some(next) = term.next {
            doc
                + (allocator.softline() + allocator.text("in") + allocator.hardline())
                + (PrettyTerm(self.0, next).pretty(allocator).indent(2).nest(2))
        } else {
            doc
        }
    }
}

impl<'a, D, A> Pretty<'a, D, A> for PrettyFunc<'a>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: Clone + 'a,
{
    fn pretty(self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A> {
        let func = &self.0.functions[self.1];

        let name = func
            .name
            .as_ref()
            .map(|n| allocator.text(INTERNER.resolve(n)))
            .unwrap_or(allocator.nil());

        (func.bound_to.pretty(allocator)
            + allocator.text(" = ")
            + allocator.text("fn ")
            + name
            + allocator.text(format!(
                "(ret: k{}, err: k{})",
                func.return_continuation.as_u32(),
                func.error_continuation.as_u32()
            ))
            + allocator.text(" = ")
            + allocator.line()
            + PrettyTerm(self.0, func.body).pretty(allocator))
        .nest(2)
        .group()
    }
}

impl Graph {
    pub fn pretty<'a, D, A>(&'a self, allocator: &'a D) -> ::pretty::DocBuilder<'a, D, A>
    where
        D: DocAllocator<'a, A>,
        D::Doc: Clone,
        A: Clone + 'a,
    {
        let root = self.entrypoint.unwrap();

        PrettyFunc(self, root).pretty(allocator)
    }
}
