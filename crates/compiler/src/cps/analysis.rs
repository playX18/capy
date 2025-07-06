use super::*;

impl Graph {
    /// Find all occurences of variables and continuations in the graph.
    pub fn analyze_occurences(&mut self) {
        self.var_occurences.clear();
        self.cont_occurences.clear();

        let root = self.entrypoint.unwrap();
        let entry = self.functions[root].body;
        self.occurence_rec(entry);
    }

    fn occurence_rec(&mut self, id: TermId) {
        match self.terms[id].definition {
            TermDef::Arity(k1, k2) => {
                self.add_occurence_of_cont(k1, id, false);
                if let Some(k2) = k2 {
                    self.add_occurence_of_cont(k2, id, false);
                }
            }

            TermDef::Case(test, k1, k2) => {
                self.add_occurence_of_var(test, id, false);
                self.add_occurence_of_cont(k1, id, false);
                self.add_occurence_of_cont(k2, id, false);
            }

            TermDef::Continue(k, args) => {
                self.add_occurence_of_cont(k, id, false);
                let len = args.len(&self.var_pool);
                for i in 0..len {
                    let arg = args.get(i, &self.var_pool).unwrap();
                    self.add_occurence_of_var(arg, id, false);
                }
            }

            TermDef::Fix(funcs) => {
                let flen = funcs.len(&self.func_pool);
                for i in 0..flen {
                    let func = funcs.get(i, &self.func_pool).unwrap();
                    let term = self.functions[func].body;
                    self.occurence_rec(term);
                }
            }

            TermDef::Funcall(f, k, h, args) => {
                self.add_occurence_of_var(f, id, false);
                self.add_occurence_of_cont(k, id, false);
                self.add_occurence_of_cont(h, id, false);

                let len = args.len(&self.var_pool);
                for i in 0..len {
                    let arg = args.get(i, &self.var_pool).unwrap();
                    self.add_occurence_of_var(arg, id, false);
                }
            }

            TermDef::Letk1(k) => {
                if let Continuation::Local { body, .. } = self.continuations[k] {
                    self.occurence_rec(body);
                }
            }

            TermDef::LetkRec(conts) => {
                let clen = conts.len(&self.cont_pool);

                for i in 0..clen {
                    let cont = conts.get(i, &self.cont_pool).unwrap();
                    if let Continuation::Local { body, .. } = self.continuations[cont] {
                        self.occurence_rec(body);
                    }
                }
            }

            TermDef::Letv(_, _) => (),
            TermDef::PrimCall(_, k, h, args) => {
                self.add_occurence_of_cont(k, id, false);
                self.add_occurence_of_cont(h, id, false);

                let len = args.len(&self.var_pool);
                for i in 0..len {
                    let arg = args.get(i, &self.var_pool).unwrap();
                    self.add_occurence_of_var(arg, id, false);
                }
            }

            TermDef::Throw(k, h, tag, args) => {
                self.add_occurence_of_cont(k, id, false);
                self.add_occurence_of_cont(h, id, false);
                self.add_occurence_of_var(tag, id, false);

                let len = args.len(&self.var_pool);
                for i in 0..len {
                    let arg = args.get(i, &self.var_pool).unwrap();
                    self.add_occurence_of_var(arg, id, false);
                }
            }

            TermDef::Halt | TermDef::Removed => (),
        }

        if let Some(next) = self.terms[id].next {
            self.occurence_rec(next);
        }
    }

    pub fn is_recursive(&self, occ: VarOccurenceId) -> bool {
        if let Some(val) = self.var_occurences[occ].is_recursive.get() {
            return val;
        }
        let var = self.var_occurences[occ].var;
        let site = self.var_occurences[occ].site;

        let VarDef::InTerm(def) = self.variables[var].definition else {
            return false;
        };

        let is_recursive = match self.terms[def].definition {
            TermDef::Letk1(k) => {
                if let Continuation::Local { body, .. } = self.continuations[k] {
                    self.site_occurs_in(body, site)
                } else {
                    false
                }
            }

            TermDef::LetkRec(conts) => {
                let clen = conts.len(&self.cont_pool);
                for i in 0..clen {
                    let cont = conts.get(i, &self.cont_pool).unwrap();
                    if let Continuation::Local { body, .. } = self.continuations[cont] {
                        if self.site_occurs_in(body, site) {
                            return true;
                        }
                    }
                }
                false
            }

            TermDef::Fix(funcs) => 'exit: {
                let flen = funcs.len(&self.func_pool);
                for i in 0..flen {
                    let func = funcs.get(i, &self.func_pool).unwrap();
                    let term = self.functions[func].body;
                    if self.site_occurs_in(term, site) {
                        break 'exit true;
                    }
                }
                false
            }

            _ => false,
        };

        self.var_occurences[occ].is_recursive.set(Some(is_recursive));
        is_recursive
    }

    pub fn is_cont_recursive(&self, occ: ContOccurenceId) -> bool {
        if let Some(val) = self.cont_occurences[occ].is_recursive.get() {
            return val;
        }
        let cont = self.cont_occurences[occ].cont;
        let site = self.cont_occurences[occ].site;

        let Continuation::Local { definition, .. } = self.continuations[cont] else {
            return false;
        };

       

        let is_recursive = match self.terms[definition].definition {
            TermDef::Letk1(k) => 'exit: {
                if let Continuation::Local { body, .. } = self.continuations[k] {
                    if self.site_occurs_in(body, site) {
                        
                        break 'exit true;
                    }
                }
                false
            }

            TermDef::LetkRec(conts) => 'exit: {
                let clen = conts.len(&self.cont_pool);
                for i in 0..clen {
                    let cont = conts.get(i, &self.cont_pool).unwrap();
                    if let Continuation::Local { body, .. } = self.continuations[cont] {
                        if self.site_occurs_in(body, site) {
                           
                            break 'exit true;
                        }
                    }
                }

                false
            }

            TermDef::Fix(funcs) => 'exit: {
                let flen = funcs.len(&self.func_pool);
                for i in 0..flen {
                    let func = funcs.get(i, &self.func_pool).unwrap();
                    let term = self.functions[func].body;
                    if self.site_occurs_in(term, site) {
                        break 'exit true;
                    }
                }

                false
            }

            _ => false,
        };

        self.cont_occurences[occ].is_recursive.set(Some(is_recursive));
        is_recursive
    }

    pub fn site_occurs_in(&self, term: TermId, site: TermId) -> bool {
        let in_def = match self.terms[term].definition {
            TermDef::Letk1(k) => {
                if let Continuation::Local { body, .. } = self.continuations[k] {
                    return self.site_occurs_in(body, site);
                }
                false
            }

            TermDef::LetkRec(conts) => {
                let clen = conts.len(&self.cont_pool);
                for i in 0..clen {
                    let cont = conts.get(i, &self.cont_pool).unwrap();
                    if let Continuation::Local { body, .. } = self.continuations[cont] {
                        if self.site_occurs_in(body, site) {
                            return true;
                        }
                    }
                }
                false
            }

            TermDef::Fix(funcs) => {
                let flen = funcs.len(&self.func_pool);
                for i in 0..flen {
                    let func = funcs.get(i, &self.func_pool).unwrap();
                    let term = self.functions[func].body;
                    if self.site_occurs_in(term, site) {
                        return true;
                    }
                }
                false
            }

            _ => false,
        };

        if in_def {
            return true;
        }

        if let Some(next) = self.terms[term].next {
            return self.site_occurs_in(next, site);
        }

        false
    }
}
