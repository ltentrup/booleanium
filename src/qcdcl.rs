use self::propagation::{assignment::Assignment, trail::Trail, watch::WatchList};
use crate::{
    clause::{Clause, Clauses},
    literal::{db::VariableDatabase, Lit, Var},
    qdimacs::FromQdimacs,
    quantifier::{ScopeDatabase, ScopeId},
    QuantTy, SolverResult,
};

pub(crate) mod propagation;

#[derive(Debug, Clone, Default)]
pub struct Context {
    clauses: Clauses,
    vars: VariableDatabase,
    quants: ScopeDatabase,
    assignment: Assignment,
    watchlist: WatchList,
    trail: Trail,
}

/// Public interface
impl Context {
    pub fn new_variables(&mut self, num_variables: u32) -> impl Iterator<Item = Var> {
        let iter = self.vars.new_variables(num_variables);
        self.assignment.set_var_count(self.vars.var_count());
        self.clauses.binary.set_var_count(self.vars.var_count());
        self.watchlist.set_var_count(self.vars.var_count());
        iter
    }

    pub fn set_num_clauses(&mut self, num_clauses: u32) {
        self.clauses.alloc.reserve(num_clauses);
    }

    pub fn num_clauses(&mut self) -> u32 {
        self.clauses.num_clauses()
    }

    /// Adds a clause consisting of the provided literals.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        // make sure every literal is bound to some scope
        lits.iter().for_each(|&l| {
            let var_info = &mut self.vars[l];
            if var_info.scope.is_none() {
                // unbound variable
                self.quants.bind_variable(&mut self.vars, ScopeDatabase::UNBOUND, l.var());
            }
            debug_assert!(self.vars[l].scope.is_some());
        });

        let mut clause = Clause::new(lits);
        clause.reduce_universal(&self.vars);
        println!("{clause}");

        match clause.lits() {
            &[] => {
                // empty clause, the matrix is unsatisfiable
                todo!("empty clause in input");
            }
            &[l] => {
                // unit clause, immediately propagate assignment
                assert!(
                    self.vars[l].existential_or_unbound(),
                    "universal variables cannot appear in unit clauses due to universal reduction"
                );
                self.enqueue_assignment(l);
                self.clauses.add_unit_clause(l);
            }
            &[l1, l2] => {
                self.clauses.add_binary_clause([l1, l2]);
            }
            _ => {
                self.clauses.add_long_clause(clause.lits());
            }
        }
    }

    pub fn new_quantified_scope(&mut self, quant: QuantTy) -> ScopeId {
        self.quants.new_quantifier(quant)
    }

    pub fn bind_variable(&mut self, scope: ScopeId, variable: Var) {
        self.quants.bind_variable(&mut self.vars, scope, variable)
    }

    pub fn solve(&mut self) -> SolverResult {
        self.init();
        self.propagate();

        todo!();
    }
}

impl Context {
    fn init(&mut self) {
        self.watchlist.enable(&self.clauses);
    }
}

impl FromQdimacs for Context {
    fn set_num_variables(&mut self, variables: u32) {
        assert_eq!(self.vars.var_count(), 0);
        let _vars = self.new_variables(variables);
    }

    fn set_num_clauses(&mut self, clauses: u32) {
        self.set_num_clauses(clauses);
    }

    fn quantify(&mut self, quant: QuantTy, vars: &[Var]) {
        let scope = self.new_quantified_scope(quant);
        for &var in vars {
            self.bind_variable(scope, var);
        }
    }

    fn add_clause(&mut self, lits: &[Lit]) {
        self.add_clause(lits);
    }
}
