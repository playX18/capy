use crate::cps::*;
use hashlink::LinkedHashSet as HashSet;

impl Graph {
    /// Substitute all occurences of `a` with `w` in the term.
    pub fn substitute_uses(&mut self, term: TermId, a: Var, w: Var) {
        let term_def = &mut self.terms[term];

        match &mut term_def.definition {
            TermDef::Case(test, _, _) => {
                if *test == a {
                    *test = w;
                }
            }

            TermDef::Continue(_, args) => {
                for arg in args.as_mut_slice(&mut self.var_pool) {
                    if *arg == a {
                        *arg = w;
                    }
                }
            }

            TermDef::Funcall(f, _, _, args) => {
                if *f == a {
                    *f = w;
                }
                for arg in args.as_mut_slice(&mut self.var_pool) {
                    if *arg == a {
                        *arg = w;
                    }
                }
            }

            TermDef::PrimCall(_, _, _, args) => {
                for arg in args.as_mut_slice(&mut self.var_pool) {
                    if *arg == a {
                        *arg = w;
                    }
                }
            }

            TermDef::Throw(_, _, tag, args) => {
                if *tag == a {
                    *tag = w;
                }
                for arg in args.as_mut_slice(&mut self.var_pool) {
                    if *arg == a {
                        *arg = w;
                    }
                }
            }

            TermDef::Letv(var, _) => {
                if *var == a {
                    *var = w;
                }
            }

            TermDef::Fix(fix) => {
                let sfix = fix.as_mut_slice(&mut self.func_pool);
                for func in sfix.iter_mut() {
                    if self.functions[*func].bound_to == a {
                        self.functions[*func].bound_to = w;
                    }
                }
            }

            _ => (),
        }

        self.remove_occurence_in_term(a, term);
        self.add_occurence_of_var(w, term, false);
    }

    pub fn substitute_var(&mut self, a: Var, w: Var) {
        let mut head = self.var_occurences.var_to_occurences[a].0;

        while let Some(occ) = head {
            let next = self.var_occurences.storage[occ].next;
            let site = self.var_occurences.storage[occ].site;

            self.substitute_uses(site, a, w);
            head = next;
        }

        match self.variables[a].definition {
            VarDef::InTerm(term) => {
                self.substitute_uses(term, a, w);
            }

            VarDef::Func(func, _) => {
                self.functions[func].bound_to = w;
            }

            _ => (),
        }
    }

    pub fn substitute_cont(&mut self, a: ContVar, w: ContVar) {
        let mut head = self.cont_occurences.var_to_occurences[a].0;

        while let Some(occ) = head {
            let next = self.cont_occurences.storage[occ].next;
            let site = self.cont_occurences.storage[occ].site;

            self.substitute_cont_uses(site, a, w);
            head = next;
        }
    }

    pub fn remove_occurence_in_term(&mut self, var: Var, term: TermId) {
        let (mut head, _tail) = self.var_occurences.var_to_occurences[var];

        while let Some(occ) = head {
            if self.var_occurences.storage[occ].site == term {
                self.remove_occurence(occ);
                return;
            }
            head = self.var_occurences.storage[occ].next;
        }
    }

    pub fn remove_occurence_of_cont_in_term(&mut self, cont: ContVar, term: TermId) {
        let (mut head, _tail) = self.cont_occurences.var_to_occurences[cont];

        while let Some(occ) = head {
            if self.cont_occurences.storage[occ].site == term {
                self.remove_occurence_of_cont(occ);
                return;
            }
            head = self.cont_occurences.storage[occ].next;
        }
    }

    pub fn substitute_cont_uses(&mut self, term: TermId, a: ContVar, w: ContVar) {
        let term_def = &mut self.terms[term];

        match &mut term_def.definition {
            TermDef::Arity(k1, k2) => {
                if *k1 == a {
                    *k1 = w;
                }
                if let Some(k2) = k2 {
                    if *k2 == a {
                        *k2 = w;
                    }
                }
            }

            TermDef::Case(_, k1, k2) => {
                if *k1 == a {
                    *k1 = w;
                }
                if *k2 == a {
                    *k2 = w;
                }
            }

            TermDef::Continue(k, _) => {
                if *k == a {
                    *k = w;
                }
            }

            TermDef::Funcall(_, k, h, _) => {
                if *k == a {
                    *k = w;
                }
                if *h == a {
                    *h = w;
                }
            }

            _ => (),
        }

        self.remove_occurence_of_cont_in_term(a, term);
        self.add_occurence_of_cont(w, term, false);
    }

    pub fn compute_var_redex(&self, var: Var, workstack: &mut HashSet<Redex>) {
        let n = self.number_of_occurences_of_var(var);

        if n == 0 {
            if matches!(
                self.variables[var].definition,
                VarDef::InTerm(_) | VarDef::Func(_, _)
            ) {
                workstack.insert(Redex::Dead(var));
            }
        } else if n == 1 {
            let occ = self
                .occurences_of_var(var)
                .0
                .expect("Variable should have at least one occurence");

            if self.is_recursive(occ) {
                workstack.insert(Redex::Dead(var));
            } else {
                let site = self.var_occurences[occ].site;
                let VarDef::Func(func, _) = &self.variables[var].definition else {
                    return;
                };

                let TermDef::Funcall(f, _k, _h, args) = self.terms[site].definition else {
                    return;
                };

                if f != var {
                    return; // Not a function call
                }
                if let Some(k) = self
                    .find_matching_clause(args.as_slice(&self.var_pool), self.functions[*func].body)
                {
                    workstack.insert(Redex::InlineFunc(var, k));
                }
            }
        }
    }

    /// Given `term` which is `Arity` attempt to find a
    /// matching clause `k`.
    pub fn find_matching_clause(&self, expect_args: &[Var], mut term: TermId) -> Option<ContVar> {
        /* functions are defined as follows:

        ---
        fn foo =
            letk k0 (a b) = ... in
                arity k0
        ---
        or for multiple clauses:
        ---
        fn bar
            letk k0 (a b) = ... in
                letk k1 () =
                    letk k2 (a b c) = ... in
                    arity k2
                in
            arity k0 k1
        --

        */

        while let TermDef::Arity(k1, k2) = self.terms[self.terms[term].next.unwrap()].definition {
            let Continuation::Local { args, variadic, .. } = &self.continuations[k1] else {
                return None;
            };

            if args.len(&self.var_pool) == expect_args.len() && variadic.is_none() {
                return Some(k1);
            }

            if let Some(k2) = k2 {
                if let Continuation::Local { body, .. } = self.continuations[k2] {
                    term = body;
                    continue;
                } else {
                    return None; // k2 is not a local continuation
                }
            }

            return None;
        }

        None
    }

    pub fn compute_redexes(&self) -> HashSet<Redex> {
        let mut redexes = HashSet::new();
        for (id, _) in self.variables.iter().skip(1) {
            self.compute_var_redex(id, &mut redexes);
        }

        for (id, cont) in self.continuations.iter() {
            let Continuation::Local { args, variadic, .. } = &cont else {
                continue;
            };
            let n = self.number_of_occurences_of_cont(id);
            println!("Checking cont {}: {} occurences", id, n);
            if n == 0 {
                redexes.insert(Redex::DeadCont(id));
            } else if n == 1 {
                let occ = self
                    .occurences_of_cont(id)
                    .0
                    .expect("Continuation should have at least one occurence");

                if self.is_cont_recursive(occ) {
                    redexes.insert(Redex::DeadCont(id));
                } else {
                    let site = self.cont_occurences[occ].site;  
                   
                    if let TermDef::Continue(_, cargs) = &self.terms[site].definition {
                        if args.len(&self.var_pool) == cargs.len(&self.var_pool)
                            && cargs.as_slice(&self.var_pool) == args.as_slice(&self.var_pool)
                            && variadic.is_none()
                        {
                            redexes.insert(Redex::InlineCont(id, occ));
                        }
                    }
                }
            }
        }

        redexes
    }

    pub fn dead(&mut self, var: Var) {
        match self.variables[var].definition {
            VarDef::Func(_, Some(def)) => {
                if let TermDef::Fix(mut funcs) = self.terms[def].definition {
                    let sfuncs = funcs.as_mut_slice(&mut self.func_pool);
                    let idx = sfuncs
                        .iter()
                        .position(|f| self.functions[*f].bound_to == var)
                        .expect("Var should be in fix");
                    funcs.remove(idx, &mut self.func_pool);
                    if funcs.is_empty() {
                        self.splice(def, self.terms[def].next.unwrap());
                    } else {
                        self.terms[def].definition = TermDef::Fix(funcs.into());
                    }

                    self.variables[var].definition = VarDef::Removed;
                }
            }

            VarDef::InTerm(def) => {
                if let TermDef::Letv(_, _) = self.terms[def].definition {
                    let d = self.terms[def].next.expect("Letv should have a next term");
                    self.splice(def, d);

                    self.variables[var].definition = VarDef::Removed;
                }
            }
            _ => (),
        }
    }

    pub fn inline_func(&mut self, var: Var, cont: ContVar) {
        /*
        inline function call:
        ---
        fix f () = 42 in
            f ()
        ---
        becomes
        ---
        fix f () = 42 in
            letk k0 () = 42 in
                continue k0()
        ---
        so `f` is now a dead variable which is detected later on.

        abstract code:

        inline(v):
            def(v) is D is fix v(ret, err, w1,...,wk) = E in F
            occ(v) is {a}
            site(a) is G is a(k, h, b1.,...bk)

            splice F in place of D
            splice E in place of G

            subst(ret, k)
            subst(err, h)
            for i in 1..k {
                subst(wi, bi)
                delete(bi)
            }
        */

        let VarDef::Func(func, Some(d)) = self.variables[var].definition else {
            return; // not a function definition 
        };

        let ret = self.functions[func].return_continuation;
        let err = self.functions[func].error_continuation;
        let f = self.terms[d]
            .next
            .expect("Function definition should have a next term");
        let Some(occ) = self.occurences_of_var(var).0 else {
            return; // no occurences of the variable: it is dead
        };

        let g = self.var_occurences[occ].site;

        let TermDef::Funcall(_f, k, h, args) = self.terms[g].definition else {
            return; // not a function call
        };
        assert_eq!(_f, var, "Function call should match the variable");

        let Continuation::Local { definition, .. } = self.continuations[cont] else {
            return;
        };

        self.splice(d, definition);

        let fk = self.continue_(cont, args.as_slice(&self.var_pool).to_vec());
        self.splice(g, fk);

        self.substitute_cont(ret, k);
        self.substitute_cont(err, h);

        /*for i in 0..args.len(&self.var_pool) {
            let w = cont_args.as_slice(&self.var_pool)[i];
            let b = args.as_slice(&self.var_pool)[i];

            self.substitute_var(b, w);
        }*/
    }

    pub fn inline_cont(&mut self, var: ContVar) {
        let Some(occ) = self.occurences_of_cont(var).0 else {
            return; // no occurences of the continuation: it is dead
        };

        let site = self.cont_occurences[occ].site;

        let Continuation::Local {
            args: cont_args,
            body: e,
            ..
        } = self.continuations[var]
        else {
            return; // not a local continuation
        };

        let TermDef::Continue(_, args) = self.terms[site].definition else {
            return; // not a continuation call
        };

        assert_eq!(
            args.len(&self.var_pool),
            cont_args.len(&self.var_pool),
            "Continuation args should match"
        );
        self.splice(site, e);
        self.remove_occurence_of_cont(occ);
        for i in 0..args.len(&self.var_pool) {
            let w = cont_args.as_slice(&self.var_pool)[i];
            let b = args.as_slice(&self.var_pool)[i];

            self.substitute_var(b, w);
        }
        self.continuations[var] = Continuation::Removed;
    }

    pub fn reduce(&mut self, mut workstack: HashSet<Redex>) {
        while let Some(redex) = workstack.pop_back() {
            match redex {
                Redex::Dead(var) => self.dead(var),

                Redex::DeadCont(cont) => {
                    let Continuation::Local { definition, .. } = self.continuations[cont] else {
                        continue;
                    };

                    if let TermDef::Letk1(_) = self.terms[definition].definition {
                        let d = self.terms[definition]
                            .next
                            .expect("Letk1 should have a next term");
                        self.splice(definition, d);
                        self.continuations[cont] = Continuation::Removed;
                    } else if let TermDef::LetkRec(mut conts) = self.terms[definition].definition {
                        let sconts = conts.as_mut_slice(&mut self.cont_pool);
                        let idx = sconts
                            .iter()
                            .position(|c| *c == cont)
                            .expect("Cont should be in letkrec");
                        conts.remove(idx, &mut self.cont_pool);
                        if conts.is_empty() {
                            self.splice(definition, self.terms[definition].next.unwrap());
                        } else {
                            self.terms[definition].definition = TermDef::LetkRec(conts.into());
                        }

                        self.continuations[cont] = Continuation::Removed;
                    }
                }

                Redex::InlineCont(cont, _occ) => {
                    self.inline_cont(cont);
                }
                Redex::InlineFunc(var, cont) => {
                    self.inline_func(var, cont);
                }
            }
        }
    }

    pub fn optimize(&mut self, iters: usize) {
        self.analyze_occurences();
        let mut workstack = self.compute_redexes();

        for _ in 0..iters {
            if workstack.is_empty() {
                break;
            }
            self.analyze_occurences();
            println!("Reducing: {:?}", workstack);
            self.reduce(workstack.clone());
            workstack = self.compute_redexes();
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Redex {
    Dead(Var),
    DeadCont(ContVar),

    InlineCont(ContVar, ContOccurenceId),
    InlineFunc(Var, ContVar),
}
