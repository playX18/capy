use hashlink::LinkedHashMap as HashMap;
use lasso::Spur;
use once_cell::unsync::OnceCell;
use std::cell::Cell;
use std::cell::RefCell;
use std::hash::Hash;

use crate::ast::*;
use crate::source::Span;
use crate::{Error, SyntaxError};

#[derive(Clone)]
pub struct Cenv {
    pub syntax_env: P<SyntaxEnv>,
    pub frames: Option<P<Frame>>,
    pub expr_name: Option<P<Datum>>,
}

impl Cenv {
    pub fn new() -> Self {
        Self {
            syntax_env: define_syntax(),
            frames: None,
            expr_name: None,
        }
    }

    pub fn is_toplevel(&self) -> bool {
        self.frames.is_none()
    }

    pub fn append(&mut self, mut frame: Frame) -> Option<P<Frame>> {
        let prev = self.frames.clone();
        frame.prev = prev.clone();
        self.frames = Some(P(frame));
        prev
    }

    pub fn pop(&mut self) {
        self.frames = self.frames.take().unwrap().prev.clone();
    }

    pub fn lookup(&self, name: &P<Datum>) -> Option<Denotation> {
        let mut y = name.clone();
        let mut frames = self.frames.clone();
        loop {
            if let Some(denotation) = frames.as_ref().and_then(|frame| frame.resolve(&y)) {
                return Some(denotation);
            }

            let DatumValue::Identifier(inner_id) = y.value() else {
                break;
            };
            let inner = inner_id.name.clone();
            if !matches!(inner.value, DatumValue::Identifier(_)) {
                frames = inner_id.binding_frame().clone();
            }
            y = inner;
        }

        None
    }
}

#[derive(Debug, Clone)]
pub enum Denotation {
    SyntaxRules(P<SyntaxRules>),
    Special(fn(&P<Datum>, &mut Cenv) -> Result<P<IForm>, Box<Error>>),
    LVar(P<LVar>),
    Primitive(Spur),

    /// Internal definition.
    ///
    /// Only occurs when expanding lambda definitions.
    Rec(P<Datum>, P<Datum>),
}

#[derive(Debug, Clone)]
pub struct SyntaxEnv {
    pub env: RefCell<HashMap<P<Symbol>, Denotation>>,
    pub denotation_of_define: fn(&P<Datum>, &mut Cenv) -> Result<P<IForm>, Box<Error>>,
    pub denotation_of_begin: fn(&P<Datum>, &mut Cenv) -> Result<P<IForm>, Box<Error>>,
}

impl SyntaxEnv {
    pub fn get(&self, id: &P<Symbol>) -> Option<Denotation> {
        self.env.borrow().get(id).cloned()
    }
}

/// Immediate form.
///
/// We expand R5RS Scheme into IForms on which we can perform optimizations. IForms
/// are way easier to work and reason about since they don't have cons-lists, internal defines,
/// unresolved variables and other aambiguity that can exist in Scheme code.
///
/// IForms on their own are used for a short period of time only for a few passes:
/// - Fixing letrec: getting rid of letrec by replacing it with `fix`, `set!` and `let` forms.
/// - Primitive resolution: resolve `GRef` forms into `PrimRef` forms if they reference primitive
/// procedures or constants.
/// - Lambda lifting: removing captured variables if closure does not escape scope it was created in.
/// - Primitive beta-reduction: cases like ((lambda (x) x) 42) are by default handled and replaced with just `42`.
/// - Single Assignment Elimination: When variable is assigned to only once (using `set!`) we can skip boxing
/// the variable and instead just create a new variable.
#[derive(Debug, Clone)]
pub struct IForm {
    pub span: Span,
    pub term: ITerm,
}

impl IForm {
    pub fn constant(span: Span, val: DatumValue) -> P<Self> {
        P(Self {
            span,
            term: ITerm::Const(Datum::new(val)),
        })
    }
}

#[derive(Debug, Clone)]
pub enum ITerm {
    Const(P<Datum>),
    LSet(P<LVar>, P<IForm>),
    LRef(P<LVar>),
    GRef(P<Symbol>),
    GSet(P<Symbol>, P<IForm>),
    PrimRef(Spur),
    Seq(Vec<P<IForm>>),
    Define(P<Symbol>, P<IForm>),

    Let(Let),
    Fix(Fix),
    Proc(P<Proc>),
    If(P<IForm>, P<IForm>, P<IForm>),
    App(P<IForm>, Vec<P<IForm>>),
    PrimApp(Spur, Vec<P<IForm>>),
}

impl IForm {
    pub fn is_transparent(&self) -> bool {
        match &self.term {
            ITerm::Const(_) | ITerm::PrimRef(_) | ITerm::Proc(_) => true,
            ITerm::LRef(var) => !var.is_mutated(),
            ITerm::If(test, cons, alt) => {
                test.is_transparent() && cons.is_transparent() && alt.is_transparent()
            }
            ITerm::Let(l) => {
                l.body.is_transparent() && l.initializers.iter().all(|x| x.is_transparent())
            }

            ITerm::Seq(seq) => seq.iter().all(|x| x.is_transparent()),

            ITerm::App(proc, args) => {
                if !args.iter().all(|x| x.is_transparent()) {
                    return false;
                }

                if let ITerm::Proc(ref proc) = proc.term {
                    proc.cases.iter().all(|case| case.body.is_transparent())
                } else {
                    false
                }
            }

            _ => false,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LetStyle {
    Let,
    LetStar,
    LetRec,
    LetRecStar,
}

#[derive(Debug, Clone)]
pub struct Let {
    pub style: LetStyle,
    pub variables: Vec<P<LVar>>,
    pub initializers: Vec<P<IForm>>,
    pub body: P<IForm>,
}

#[derive(Debug, Clone)]
pub struct Fix {
    pub variables: Vec<P<LVar>>,
    pub procedures: Vec<P<Proc>>,
    pub body: P<IForm>,
}

#[derive(Debug, Clone)]
pub struct Proc {
    pub loc: Option<Span>,
    pub name: Option<P<Datum>>,
    pub cases: Vec<ProcCase>,
}

#[derive(Debug, Clone)]
pub struct ProcCase {
    pub loc: Option<Span>,
    pub args: Vec<P<LVar>>,
    pub variadic: Option<P<LVar>>,
    pub body: P<IForm>,
}

#[derive(Debug)]
pub struct LVar {
    pub name: P<Datum>,
    pub loc: Option<Span>,
    ref_count: Cell<u32>,
    set_count: Cell<u32>,
}

impl LVar {
    pub fn new(name: P<Datum>, loc: Option<Span>) -> P<LVar> {
        P(LVar {
            name,
            loc,

            ref_count: Cell::new(0),
            set_count: Cell::new(0),
        })
    }

    pub fn set(&self) {
        self.set_count.set(self.set_count.get() + 1);
    }

    pub fn ref_(&self) {
        self.ref_count.set(self.ref_count.get() + 1);
    }

    pub fn is_mutated(&self) -> bool {
        self.set_count.get() != 0
    }

    pub fn is_mutated_once(&self) -> bool {
        self.set_count.get() == 1
    }

    pub fn unref(&self) {
        self.ref_count.set(0);
    }

    pub fn ref_count(&self) -> u32 {
        self.ref_count.get()
    }
}

impl Hash for LVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self as *const Self).hash(state);
    }
}

impl PartialEq for LVar {
    fn eq(&self, other: &Self) -> bool {
        self as *const Self == other as *const Self
    }
}

impl Eq for LVar {}

impl Identifier {
    pub fn binding_frame(&self) -> &Option<P<Frame>> {
        self.frame.get_or_init(|| {
            self.frames
                .as_ref()
                .and_then(|frame| frame.get_binding_frame(&self.name).cloned())
        })
    }

    pub fn wrap(self: &P<Self>) -> P<Self> {
        P(Self {
            name: Datum::new_at(self.name.span(), DatumValue::Identifier(self.clone())),
            frame: OnceCell::new(),
            frames: self.frames.clone(),
            env: self.env.clone(),
            global_name: OnceCell::new(),
        })
    }

    pub fn outermost(mut self: &P<Self>) -> &P<Self> {
        while let DatumValue::Identifier(x) = &self.name.value {
            self = x;
        }

        self
    }

    pub fn unwrap(self: &P<Self>) -> P<Symbol> {
        let DatumValue::Symbol(sym) = self.outermost().name.value() else {
            panic!("unwrap_identifier: not a symbol")
        };

        sym.clone()
    }
}

impl Datum {
    pub fn identifier_to_symbol(&self) -> P<Symbol> {
        match self.value {
            DatumValue::Identifier(ref id) => id.unwrap(),
            DatumValue::Symbol(ref sym) => sym.clone(),
            _ => panic!("not a symbol"),
        }
    }
}

pub struct Frame {
    pub bindings: RefCell<HashMap<P<Datum>, Denotation>>,
    pub prev: Option<P<Frame>>,
}

impl Frame {
    pub fn new(prev: Option<P<Frame>>) -> Self {
        Self {
            bindings: RefCell::new(HashMap::new()),
            prev,
        }
    }

    pub fn get_binding_frame(self: &P<Frame>, var: &P<Datum>) -> Option<&P<Frame>> {
        let mut frame = Some(self);

        while let Some(fp) = frame {
            if self.bindings.borrow().contains_key(var) {
                return Some(fp);
            }

            frame = fp.prev.as_ref();
        }

        None
    }

    pub fn resolve(&self, var: &P<Datum>) -> Option<Denotation> {
        self.bindings
            .borrow()
            .get(var)
            .cloned()
            .or_else(|| self.prev.as_ref().and_then(|prev| prev.resolve(var)))
    }

    pub fn extend(&self, var: P<Datum>, denotation: Denotation) {
        self.bindings.borrow_mut().insert(var, denotation);
    }
}

/// Construct default syntax environment for R5RS Scheme.
///
/// Returned environment contains special forms in R5RS:
/// `define`, `begin`, `define-syntax` etc.
pub fn define_syntax() -> P<SyntaxEnv> {
    let mut env = HashMap::new();
    let mut denotation_of_define = None::<fn(&P<Datum>, &mut Cenv) -> Result<P<IForm>, Box<Error>>>;
    let mut denotation_of_begin = None::<fn(&P<Datum>, &mut Cenv) -> Result<P<IForm>, Box<Error>>>;
    macro_rules! def {
        ($name: literal, $form: ident, $cenv: ident, $b: block) => {{
            fn stx($form: &P<Datum>, $cenv: &mut Cenv) -> Result<P<IForm>, Box<Error>> {
                $b
            }

            let denotation = Denotation::Special(stx);

            let sym = Symbol::new($name);

            if $name == "define" {
                denotation_of_define = Some(stx);
            } else if $name == "begin" {
                denotation_of_begin = Some(stx);
            }

            env.insert(sym, denotation);
        }};
    }

    def!("lambda", form, cenv, {
        if form.list_length().filter(|x| *x >= 3).is_none() {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: form.span(),
                message: format!("invalid 'lambda' form"),
            })));
        }

        let formals = form.cadr().unwrap();
        let body = form.cddr().unwrap();

        fn parse_formals(
            xs: &P<Datum>,
            ys: P<Datum>,
        ) -> Result<(P<Datum>, Option<P<Datum>>), Box<Error>> {
            match xs.value() {
                DatumValue::Null => Ok((ys.reverse(), None)),
                DatumValue::Identifier(_) | DatumValue::Symbol(_) => {
                    Ok((ys.reverse(), Some(xs.clone())))
                }
                DatumValue::Pair(car, rest) if car.is_id() => {
                    parse_formals(rest, Datum::cons(car.clone(), ys, Some(car.span())))
                }
                _ => Err(Box::new(Error::syntax(SyntaxError::Invalid {
                    span: xs.span(),
                    message: format!("invalid lambda parameter"),
                }))),
            }
        }

        let (args, variadic) = parse_formals(formals, Datum::new(DatumValue::Null))?;

        pass1_vanilla_lambda(form, args, variadic, body.clone(), cenv)
    });
    def!("define", form, cenv, {
        pass1_define(form.clone(), form.clone(), cenv)
    });

    def!("quote", form, _cenv, {
        if form.list_length() != Some(2) {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: form.span(),
                message: format!("quote: bad syntax"),
            })));
        }

        let datum = form.cadr().unwrap();

        Ok(P(IForm {
            span: form.span(),
            term: ITerm::Const(datum.clone()),
        }))
    });

    def!("let", form, cenv, {
        if form.list_length().filter(|x| *x >= 3).is_none() {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: form.span(),
                message: format!("let: bad syntax"),
            })));
        }
        let bindings = form.cadr().unwrap();
        let body = form.cddr().unwrap();

        if bindings.is_null() {
            pass1_body_rec(body.clone(), None, None, cenv)
        } else {
            let mut lhs = Vec::new();
            let mut rhs = Vec::new();
            for vardef in bindings.iter_pairs() {
                if vardef.list_length() != Some(2) {
                    return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                        span: form.span(),
                        message: format!("let: bad syntax"),
                    })));
                }

                let var = vardef.car().unwrap();
                let val = vardef.cadr().unwrap();

                let lvar = LVar::new(var.clone(), Some(var.span()));
                let val = pass1(&val, cenv)?;

                lhs.push(lvar);
                rhs.push(val);
            }

            let frame = Frame::new(cenv.frames.clone());

            for var in lhs.iter() {
                frame.extend(var.name.clone(), Denotation::LVar(var.clone()));
            }

            let saved = cenv.frames.clone();
            cenv.append(frame);

            let body = pass1(&body.car().unwrap(), cenv)?;
            cenv.frames = saved;

            Ok(P(IForm {
                span: form.span(),
                term: ITerm::Let(Let {
                    style: LetStyle::Let,
                    variables: lhs,
                    initializers: rhs,
                    body,
                }),
            }))
        }
    });

    def!("set!", form, cenv, {
        if form.list_length() == Some(3) {
            let var = form.cadr().unwrap();
            let val = form.caddr().unwrap();

            if !var.is_id() {
                return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                    span: form.span(),
                    message: "invalid `set!` form".to_owned(),
                })));
            }

            let var_deno = cenv.lookup(var);
            let value = pass1(val, cenv)?;

            match var_deno {
                Some(Denotation::LVar(lvar)) => {
                    lvar.set();
                    Ok(P(IForm {
                        span: form.span(),
                        term: ITerm::LSet(lvar, value),
                    }))
                }

                Some(_) => {
                    return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                        span: form.span(),
                        message: format!("invalid assignment to {var}"),
                    })));
                }

                None => {
                    let sym = match var.value() {
                        DatumValue::Symbol(sym) => sym.clone(),
                        DatumValue::Identifier(id) => id.global_name(),
                        _ => unreachable!(),
                    };

                    Ok(P(IForm {
                        span: form.span(),
                        term: ITerm::GSet(sym, value),
                    }))
                }
            }
        } else {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: form.span(),
                message: "invalid `set!` form".to_owned(),
            })));
        }
    });
    def!("if", form, cenv, {
        if form.list_length() == Some(4) {
            let cond = pass1(&form.cadr().unwrap(), cenv)?;
            let consequent = pass1(&form.caddr().unwrap(), cenv)?;
            let alternative = pass1(&form.cadddr().unwrap(), cenv)?;

            Ok(P(IForm {
                span: form.span(),
                term: ITerm::If(cond, consequent, alternative),
            }))
        } else if form.list_length() == Some(3) {
            let cond = pass1(&form.cadr().unwrap(), cenv)?;
            let consequent = pass1(&form.caddr().unwrap(), cenv)?;
            let alternative = P(IForm {
                span: form.span(),
                term: ITerm::Const(Datum::new(DatumValue::Undefined)),
            });

            Ok(P(IForm {
                span: form.span(),
                term: ITerm::If(cond, consequent, alternative),
            }))
        } else {
            Err(Box::new(Error::syntax(crate::SyntaxError::Invalid {
                span: form.span(),
                message: "invalid 'if' expression".to_owned(),
            })))
        }
    });

    def!("begin", form, cenv, {
        let mut seq = Vec::new();

        // we can unwrap here just fine. `pass1` or `pass1_body_rec`
        // already verify that `form` is proper list.
        let mut ls = form.cdr().unwrap();

        while let Some((car, cdr)) = ls.try_pair() {
            seq.push(pass1(car, cenv)?);
            ls = cdr;
        }

        if seq.len() == 1 {
            Ok(seq[0].clone())
        } else if seq.is_empty() {
            Ok(P(IForm {
                span: form.span(),
                term: ITerm::Const(Datum::new(DatumValue::Undefined)),
            }))
        } else {
            Ok(P(IForm {
                span: form.span(),
                term: ITerm::Seq(seq),
            }))
        }
    });

    P(SyntaxEnv {
        env: RefCell::new(env),
        denotation_of_define: denotation_of_define.unwrap(),
        denotation_of_begin: denotation_of_begin.unwrap(),
    })
}

pub fn pass1(program: &P<Datum>, cenv: &mut Cenv) -> Result<P<IForm>, Box<Error>> {
    fn global_call(
        program: P<Datum>,
        id: P<Datum>,
        cenv: &mut Cenv,
    ) -> Result<P<IForm>, Box<Error>> {
        let name = match id.value() {
            DatumValue::Symbol(sym) => sym.clone(),
            DatumValue::Identifier(id) => id.global_name(),
            _ => unreachable!(),
        };

        let proc = match cenv.syntax_env.get(&name) {
            Some(Denotation::Special(special)) => return special(&program, cenv),
            Some(Denotation::SyntaxRules(_)) => todo!(),
            Some(Denotation::Primitive(primref)) => P(IForm {
                span: id.span(),
                term: ITerm::PrimRef(primref),
            }),

            None => P(IForm {
                span: id.span(),
                term: ITerm::GRef(name),
            }),

            Some(Denotation::LVar(_)) => unreachable!(),
            _ => unreachable!(),
        };

        expand_call(&program, proc, program.cdr().unwrap().clone(), cenv)
    }

    if let Some((head, rest)) = program.try_pair() {
        if !program.is_list() {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: program.span(),
                message: format!("proper list is required for application or macro use"),
            })));
        }

        match cenv.lookup(head) {
            Some(Denotation::LVar(lvar)) => {
                return expand_call(
                    program,
                    P(IForm {
                        span: head.span(),
                        term: ITerm::LRef(lvar),
                    }),
                    rest.clone(),
                    cenv,
                );
            }

            Some(Denotation::Special(special)) => return special(program, cenv),

            Some(Denotation::SyntaxRules(_)) => todo!(),

            Some(Denotation::Primitive(primref)) => {
                return expand_call(
                    program,
                    P(IForm {
                        span: head.span(),
                        term: ITerm::PrimRef(primref),
                    }),
                    rest.clone(),
                    cenv,
                );
            }

            None => {
                let proc = match head.value() {
                    DatumValue::Symbol(_) => Datum::new(DatumValue::Identifier(Identifier::new(
                        head.clone(),
                        cenv.syntax_env.clone(),
                    ))),

                    _ => head.clone(),
                };

                if matches!(
                    proc.value(),
                    DatumValue::Identifier(_) | DatumValue::Symbol(_)
                ) {
                    return global_call(program.clone(), proc, cenv);
                }

                let proc = pass1(&proc, cenv)?;

                return expand_call(&program, proc, rest.clone(), cenv);
            }

            _ => unreachable!(),
        }
    } else if matches!(
        program.value(),
        DatumValue::Identifier(_) | DatumValue::Symbol(_)
    ) {
        match cenv.lookup(program) {
            Some(Denotation::LVar(lvar)) => Ok(P(IForm {
                span: program.span(),
                term: ITerm::LRef(lvar),
            })),
            Some(_) => Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: program.span(),
                message: "Invalid usage of syntax form".to_string(),
            }))),

            None => {
                let id = match program.value() {
                    DatumValue::Symbol(sym) => sym.clone(),
                    DatumValue::Identifier(id) => id.global_name(),
                    _ => unreachable!(),
                };

                Ok(P(IForm {
                    span: program.span(),
                    term: ITerm::GRef(id),
                }))
            }
        }
    } else {
        Ok(P(IForm {
            span: program.span(),
            term: ITerm::Const(program.clone()),
        }))
    }
}

fn expand_call(
    form: &P<Datum>,
    proc: P<IForm>,
    mut args: P<Datum>,
    cenv: &mut Cenv,
) -> Result<P<IForm>, Box<Error>> {
    if args.is_null() {
        return Ok(P(IForm {
            span: form.span(),
            term: ITerm::App(proc, vec![]),
        }));
    }

    let mut iargs = Vec::new();

    while let Some((car, cdr)) = args.try_pair() {
        iargs.push(pass1(car, cenv)?);
        args = cdr.clone();
    }

    if !args.is_null() {
        return Err(Box::new(Error::syntax(SyntaxError::Invalid {
            span: form.span(),
            message: format!("application must be a proper list"),
        })));
    }

    Ok(P(IForm {
        span: form.span(),
        term: ITerm::App(proc, iargs),
    }))
}

fn pass1_body_rec(
    exprs: P<Datum>,
    mframe: Option<P<Frame>>,
    vframe: Option<P<Frame>>,
    cenv: &mut Cenv,
) -> Result<P<IForm>, Box<Error>> {
    fn dupe_check(
        var: &P<Datum>,
        mframe: &Option<P<Frame>>,
        vframe: &Option<P<Frame>>,
    ) -> Result<(), Box<Error>> {
        if matches!(
            mframe
                .as_ref()
                .map(|f| f.resolve(var).is_some())
                .or_else(|| vframe.as_ref().map(|f| f.resolve(var).is_some())),
            Some(true)
        ) {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: var.span(),
                message: format!("Duplicate definition found"),
            })));
        }

        Ok(())
    }

    match exprs.value() {
        DatumValue::Pair(car, cdr) if car.is_pair() => {
            let rest = cdr;
            let op = exprs.caar().unwrap();
            let args = exprs.cdar().unwrap();

            if matches!(vframe.as_ref().and_then(|f| f.resolve(op)), None) && op.is_id() {
                if !args.is_list() {
                    return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                        span: exprs.span(),
                        message: format!("proper list is required for application or macro use"),
                    })));
                }

                match cenv.lookup(op) {
                    Some(Denotation::LVar(_))
                    | Some(Denotation::Special(_))
                    | Some(Denotation::Primitive(_))
                    | Some(Denotation::Rec(_, _)) => {
                        return pass1_body_finish(exprs, mframe, vframe, cenv);
                    }
                    Some(Denotation::SyntaxRules(_)) => todo!(),

                    None => {
                        let name = match op.value() {
                            DatumValue::Symbol(sym) => sym.clone(),
                            DatumValue::Identifier(id) => id.global_name(),
                            _ => unreachable!(),
                        };
                        let deno = cenv.syntax_env.get(&name);

                        match deno {
                            None | Some(Denotation::Primitive(_)) => {
                                return pass1_body_finish(exprs, mframe, vframe, cenv);
                            }
                            Some(Denotation::SyntaxRules(_)) => todo!(),
                            Some(Denotation::Special(special)) => {
                                /* somebody save me from this mess ... */
                                if special as usize == cenv.syntax_env.denotation_of_begin as usize
                                {
                                    let x = args.append(&rest);
                                    return pass1_body_rec(x, mframe, vframe, cenv);
                                }
                                if special as usize == cenv.syntax_env.denotation_of_define as usize
                                {
                                    println!("define {args}");
                                    let (name, def) = match args {
                                        args if args.is_pair() && args.car().unwrap().is_pair() => {
                                            let name = args.caar().unwrap();
                                            let formals = args.cdar().unwrap();
                                            let body = args.cdr().unwrap();
                                            dupe_check(&name, &mframe, &vframe)?;
                                            let lam = Datum::make_list_with(
                                                &[
                                                    Datum::make_symbol("lambda", Some(args.span())),
                                                    formals.clone(),
                                                ],
                                                body.clone(),
                                                Some(exprs.span()),
                                            );

                                            (name.clone(), Denotation::Rec(name.clone(), lam))
                                        }
                                        args if args.is_pair()
                                            && args.cdr().unwrap().is_pair()
                                            && args.cddr().unwrap().is_null() =>
                                        {
                                            let var = args.car().unwrap().clone();
                                            dupe_check(&var, &mframe, &vframe)?;
                                            let init = args.cadr().unwrap().clone();

                                            (var.clone(), Denotation::Rec(var, init))
                                        }

                                        _ => {
                                            return Err(Box::new(Error::syntax(
                                                SyntaxError::Invalid {
                                                    span: exprs.span(),
                                                    message: format!("invalid define form"),
                                                },
                                            )));
                                        }
                                    };

                                    if !name.is_id() {
                                        return Err(Box::new(Error::syntax(
                                            SyntaxError::Invalid {
                                                span: exprs.span(),
                                                message: format!("invalid define form"),
                                            },
                                        )));
                                    }
                                    if mframe.is_none() {
                                        let mframe = Frame::new(cenv.frames.clone());
                                        cenv.append(mframe);
                                        let mframe = cenv.frames.clone();
                                        let vframe = Frame::new(mframe.clone());
                                        cenv.append(vframe);
                                        let vframe = cenv.frames.clone();
                                        vframe.as_ref().unwrap().extend(name, def);
                                        return pass1_body_rec(rest.clone(), mframe, vframe, cenv);
                                    } else {
                                        vframe.as_ref().unwrap().extend(name, def);
                                        return pass1_body_rec(rest.clone(), mframe, vframe, cenv);
                                    }
                                }

                                return pass1_body_finish(exprs, mframe, vframe, cenv);
                            }

                            _ => unreachable!(),
                        }
                    }
                }
            }

            return pass1_body_finish(exprs, mframe, vframe, cenv);
        }

        _ => return pass1_body_finish(exprs, mframe, vframe, cenv),
    }
}

fn pass1_body_finish(
    exprs: P<Datum>,
    mframe: Option<P<Frame>>,
    vframe: Option<P<Frame>>,
    cenv: &mut Cenv,
) -> Result<P<IForm>, Box<Error>> {
    if let (Some(_mframe), Some(vframe)) = (mframe, vframe) {
        let mut lvars = Vec::new();
        let mut inits = Vec::new();

        for (var, deno) in vframe.bindings.borrow_mut().iter_mut() {
            let Denotation::Rec(_, expr) = deno else {
                unreachable!()
            };

            inits.push(expr.clone());

            let lvar = LVar::new(var.clone(), Some(var.span()));
            lvars.push(lvar.clone());

            *deno = Denotation::LVar(lvar);
        }

        let inits = inits
            .into_iter()
            .zip(lvars.iter())
            .map(|(init, lvar)| {
                let saved = cenv.expr_name.clone();
                cenv.expr_name = Some(lvar.name.clone());
                let r = pass1(&init, cenv);
                cenv.expr_name = saved;
                r
            })
            .collect::<Result<Vec<_>, Box<Error>>>()?;

        let body = pass1_body_rest(exprs.clone(), cenv)?;

        Ok(P(IForm {
            span: exprs.span(),
            term: ITerm::Let(Let {
                style: LetStyle::LetRec,
                variables: lvars,
                initializers: inits,
                body,
            }),
        }))
    } else {
        pass1_body_rest(exprs, cenv)
    }
}

fn pass1_body_rest(exprs: P<Datum>, cenv: &mut Cenv) -> Result<P<IForm>, Box<Error>> {
    if exprs.is_null() {
        return Ok(P(IForm {
            span: exprs.span(),
            term: ITerm::Const(Datum::new(DatumValue::Undefined)),
        }));
    } else if let DatumValue::Pair(car, cdr) = &exprs.value
        && cdr.is_null()
    {
        return pass1(&car, cenv);
    }

    let mut seq = Vec::new();

    let mut ls = exprs.clone();

    while let Some((car, cdr)) = ls.try_pair() {
        seq.push(pass1(&car, cenv)?);
        ls = cdr.clone();
    }

    Ok(P(IForm {
        span: exprs.span(),
        term: ITerm::Seq(seq),
    }))
}

fn pass1_vanilla_lambda(
    form: &P<Datum>,
    formals: P<Datum>,
    variadic: Option<P<Datum>>,
    body: P<Datum>,
    cenv: &mut Cenv,
) -> Result<P<IForm>, Box<Error>> {
    let lvars = formals
        .iter_pairs()
        .map(|var| {
            if var.is_id() {
                Ok(LVar::new(var.clone(), Some(var.span())))
            } else {
                Err(Box::new(Error::syntax(SyntaxError::Invalid {
                    span: var.span(),
                    message: format!("expected variable name"),
                })))
            }
        })
        .collect::<Result<Vec<_>, Box<Error>>>()?;

    let variadic = variadic.map(|var| LVar::new(var.clone(), Some(var.span())));

    let frame = Frame::new(cenv.frames.clone());

    for lvar in lvars.iter() {
        frame.extend(lvar.name.clone(), Denotation::LVar(lvar.clone()));
    }

    if let Some(variadic) = variadic.as_ref() {
        frame.extend(variadic.name.clone(), Denotation::LVar(variadic.clone()));
    }

    let saved = cenv.append(frame);

    let body = pass1_body_rec(body, None, None, cenv)?;

    cenv.frames = saved;

    let proc = Proc {
        loc: Some(form.span()),
        name: cenv.expr_name.clone(),
        cases: vec![ProcCase {
            loc: Some(form.span()),
            args: lvars[..].to_vec(),
            variadic,
            body,
        }],
    };

    Ok(P(IForm {
        span: form.span(),
        term: ITerm::Proc(P(proc)),
    }))
}

fn pass1_define(form: P<Datum>, oform: P<Datum>, cenv: &mut Cenv) -> Result<P<IForm>, Box<Error>> {
    let name = form.cadr().unwrap();
    let orig = name.clone();
    match name.value() {
        DatumValue::Pair(name, args) => {
            let body = form.cddr().unwrap();

            let lambda = Datum::make_list_with(
                [
                    Datum::make_symbol("lambda", Some(form.span())),
                    args.clone(),
                ],
                body.clone(),
                Some(oform.span()),
            );

            let define = Datum::make_list(
                [
                    Datum::make_symbol("define", Some(oform.span())),
                    name.clone(),
                    lambda,
                ],
                Some(oform.span()),
            );

            pass1_define(define, orig, cenv)
        }

        DatumValue::Symbol(_) | DatumValue::Identifier(_) => {
            let value = match form.cddr().map(|x| x.value()) {
                Some(DatumValue::Null) => {
                    // R6RS style (define <name>)
                    P(IForm {
                        span: oform.span(),
                        term: ITerm::Const(Datum::new(DatumValue::Undefined)),
                    })
                }

                Some(DatumValue::Pair(value, cdr)) if cdr.is_null() => {
                    let saved = cenv.expr_name.replace(name.clone());
                    let value = pass1(value, cenv)?;
                    cenv.expr_name = saved;
                    value
                }

                _ => {
                    return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                        span: oform.span(),
                        message: "invalid definition".to_owned(),
                    })));
                }
            };

            let id = match name.value() {
                DatumValue::Identifier(id) => {
                    id.gensym();
                    id.global_name()
                }

                DatumValue::Symbol(sym) => sym.clone(),
                _ => unreachable!(),
            };

            Ok(P(IForm {
                span: oform.span(),
                term: ITerm::Define(id, value),
            }))
        }

        _ => {
            return Err(Box::new(Error::syntax(SyntaxError::Invalid {
                span: oform.span(),
                message: format!("invalid name for 'define'"),
            })));
        }
    }
}

use pretty::{DocAllocator, DocBuilder};

impl IForm {
    pub fn pretty<'b, D, A>(&'b self, allocator: &'b D) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.p(allocator)
    }

    fn p<'b, D, A>(&'b self, allocator: &'b D) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match &self.term {
            ITerm::Const(datum) => allocator
                .text("quote")
                .append(allocator.space())
                .append(allocator.text(format!("{datum}")))
                .group()
                .parens(),

            ITerm::LRef(lref) => allocator.text(lref.name.to_string()),
            ITerm::GRef(gref) => allocator
                .text("gref")
                .append(allocator.space())
                .append(allocator.text(format!("{gref}")))
                .group()
                .parens(),

            ITerm::LSet(lset, val) => allocator
                .text("set!")
                .append(allocator.space())
                .append(allocator.text(format!("{}", lset.name)))
                .append(allocator.space())
                .append(val.p(allocator))
                .group()
                .parens(),

            ITerm::GSet(gset, val) => allocator
                .text("gset!")
                .append(allocator.space())
                .append(allocator.text(format!("{gset}")))
                .append(allocator.space())
                .append(val.p(allocator))
                .group()
                .parens(),

            ITerm::PrimRef(primref) => allocator
                .text("prim")
                .append(allocator.space())
                .append(allocator.text(format!("{}", INTERNER.resolve(primref))))
                .group()
                .parens(),

            ITerm::If(test, cons, alt) => allocator
                .text("if")
                .append(allocator.space())
                .append(test.p(allocator))
                .nest(2)
                .append(allocator.softline())
                .append(cons.p(allocator))
                .append(allocator.line())
                .append(alt.p(allocator)),

            ITerm::Seq(seq) => {
                let builder = allocator.text("seq").nest(2);

                builder
                    .append(allocator.line())
                    .append(
                        allocator.intersperse(seq.iter().map(|x| x.p(allocator)), allocator.line()),
                    )
                    .nest(2)
                    .group()
                    .parens()
            }

            ITerm::App(proc, args) => {
                let mut builder = allocator
                    .text("call")
                    .append(allocator.space())
                    .append(proc.p(allocator))
                    .nest(2);
                if !args.is_empty() {
                    builder = builder.append(allocator.softline());
                }
                builder = builder
                    .append(
                        allocator
                            .intersperse(args.iter().map(|x| x.p(allocator)), allocator.softline()),
                    )
                    .nest(2);
                builder.group().parens()
            }

            ITerm::Define(sym, val) => allocator
                .text("define")
                .append(allocator.space())
                .append(allocator.text(format!("{sym}")))
                .append(allocator.softline())
                .append(val.p(allocator).nest(2))
                .group()
                .parens(),

            ITerm::Proc(proc) => {
                let builder = allocator.text("proc");

                builder
                    .append(allocator.hardline())
                    .nest(2)
                    .append(allocator.intersperse(
                        proc.cases.iter().map(|case| {
                            let mut args = vec![];

                            for arg in case.args.iter() {
                                args.push(allocator.text(format!("{}", arg.name)));
                            }

                            if let Some(v) = &case.variadic {
                                args.push(allocator.text(format!("&{}", v.name)));
                            }

                            allocator
                                .text("case")
                                .append(allocator.space())
                                .append(
                                    allocator
                                        .intersperse(args.into_iter(), allocator.space())
                                        .group()
                                        .parens(),
                                )
                                .append(allocator.hardline())
                                .append(case.body.p(allocator))
                                .nest(2)
                                .group()
                                .parens()
                        }),
                        allocator.hardline(),
                    ))
                    .nest(2)
                    .group()
                    .parens()
            }

            ITerm::Let(l) => {
                let text = match l.style {
                    LetStyle::Let => allocator.text("let"),
                    LetStyle::LetRec => allocator.text("letrec"),
                    LetStyle::LetStar => allocator.text("let*"),
                    LetStyle::LetRecStar => allocator.text("letrec*"),
                };

                let vars = l
                    .variables
                    .iter()
                    .zip(l.initializers.iter())
                    .map(|(var, init)| {
                        allocator
                            .text(format!("{}", var.name))
                            .append(allocator.softline())
                            .nest(2)
                            .append(init.p(allocator))
                            .group()
                            .brackets()
                    });
                text.append(allocator.softline())
                    .append(
                        allocator
                            .intersperse(vars, allocator.softline())
                            .group()
                            .parens()
                            .nest(2),
                    )
                    .append(allocator.hardline())
                    .append(l.body.p(allocator))
                    .nest(2)
                    .group()
                    .parens()
            }
            _ => todo!(),
        }
    }
}

impl PartialEq for IForm {
    fn eq(&self, other: &Self) -> bool {
        self as *const Self == other as *const Self
    }
}

impl Eq for IForm {}

impl Hash for IForm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self as *const Self).hash(state);
    }
}
