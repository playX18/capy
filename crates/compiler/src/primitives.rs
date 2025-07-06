use std::sync::LazyLock;

use lasso::Spur;
use std::collections::HashSet;

use crate::{ast::INTERNER, ast::*, expand::*};

static PRIMITIVE_NAMES: &[&str] = &["+", "-", "*", "/", "=", ">", "<", ">=", "<="];

pub static PRIMITIVE_SET: LazyLock<HashSet<Spur>> = LazyLock::new(|| {
    let mut set = HashSet::new();

    for name in PRIMITIVE_NAMES.iter() {
        set.insert(INTERNER.get_or_intern(name));
    }

    set
});

/// Given iform resolve all primitive references in it.
pub fn resolve_primitives(iform: &P<IForm>) -> P<IForm> {
    match &iform.term {
        ITerm::GRef(sym) => {
            if let Symbol::Interned(name) = &*sym.root() {
                if PRIMITIVE_SET.contains(name) {
                    return P(IForm {
                        span: iform.span,
                        term: ITerm::PrimRef(*name),
                    });
                }
            }

            return iform.clone();
        }

        ITerm::If(test, cons, alt) => P(IForm {
            span: iform.span,
            term: ITerm::If(
                resolve_primitives(test),
                resolve_primitives(cons),
                resolve_primitives(alt),
            ),
        }),

        ITerm::LSet(var, val) => P(IForm {
            span: iform.span,
            term: ITerm::LSet(var.clone(), resolve_primitives(val)),
        }),

        ITerm::GSet(var, val) => P(IForm {
            span: iform.span,
            term: ITerm::GSet(var.clone(), resolve_primitives(val)),
        }),

        ITerm::Seq(seq) => P(IForm {
            span: iform.span,
            term: ITerm::Seq(seq.iter().map(resolve_primitives).collect()),
        }),

        ITerm::Define(var, val) => P(IForm {
            span: iform.span,
            term: ITerm::Define(var.clone(), resolve_primitives(val)),
        }),

        ITerm::Proc(proc) => {
            let cases = proc
                .cases
                .iter()
                .map(|case| ProcCase {
                    loc: case.loc.clone(),
                    args: case.args.clone(),
                    variadic: case.variadic.clone(),
                    body: resolve_primitives(&case.body),
                })
                .collect::<Vec<_>>();
            P(IForm {
                span: iform.span,
                term: ITerm::Proc(P(Proc {
                    loc: proc.loc,
                    name: proc.name.clone(),
                    cases,
                })),
            })
        }

        ITerm::App(proc, args) => {
            let proc = resolve_primitives(proc);

            let args = args.iter().map(resolve_primitives).collect();

            if let ITerm::PrimRef(name) = &proc.term {
                return P(IForm {
                    span: iform.span,
                    term: ITerm::PrimApp(*name, args),
                });
            }
            P(IForm {
                span: iform.span,
                term: ITerm::App(proc, args),
            })
        }

        ITerm::Let(l) => {
            let initializers = l.initializers.iter().map(resolve_primitives).collect();
            let body = resolve_primitives(&l.body);

            P(IForm {
                span: iform.span,
                term: ITerm::Let(Let {
                    variables: l.variables.clone(),
                    initializers,
                    body,
                    style: l.style,
                }),
            })
        }

        ITerm::Fix(fix) => {
            let procs = fix
                .procedures
                .iter()
                .map(|proc| {
                    let cases = proc
                        .cases
                        .iter()
                        .map(|case| ProcCase {
                            loc: case.loc.clone(),
                            args: case.args.clone(),
                            variadic: case.variadic.clone(),
                            body: resolve_primitives(&case.body),
                        })
                        .collect::<Vec<_>>();
                    P(Proc {
                        loc: proc.loc,
                        name: proc.name.clone(),
                        cases,
                    })
                })
                .collect();

            P(IForm {
                span: iform.span,
                term: ITerm::Fix(Fix {
                    procedures: procs,
                    variables: fix.variables.clone(),
                    body: resolve_primitives(&fix.body),
                }),
            })
        }

        _ => iform.clone(),
    }
}
