//! Unit clause propagation

use super::Context;
use crate::literal::Lit;
use std::mem;

pub(crate) mod assignment;
pub(crate) mod trail;
pub(crate) mod watch;

impl Context {
    pub(crate) fn propagate(&mut self) {
        assert!(self.watchlist.is_enabled());
        self.watchlist.enable(&self.clauses);

        while let Some(lit) = self.trail.next_lit_to_propagate() {
            self.propagate_long(lit);
        }
    }

    fn propagate_long(&mut self, lit: Lit) {
        println!("{lit}");
        let mut watches = mem::take(&mut self.watchlist[lit]);
        println!("{watches:?}");
        watches.retain(|watch| {
            let clause = &mut self.clauses.alloc[watch.clause];
            println!(">> {clause}");
            let lits = clause.lits_mut();
            debug_assert!(lits[0] == !lit || lits[1] == !lit);

            // move lit to second position in clause
            if lits[0] == !lit {
                lits.swap(0, 1);
                debug_assert_eq!(lits[1], lit);
            }

            // check if the other watched literal satisfies the clause
            let first = lits[0];
            if self.assignment.lit_is_true(first) {
                return true;
            }

            // check whether the clause is satisfied
            let (initial, remaining) = lits.split_at_mut(2);
            for remaining_lit in remaining {
                if !self.assignment.lit_is_false(*remaining_lit) {
                    // we found a non-false literal which we make a watched literal for this clause
                    mem::swap(&mut initial[1], remaining_lit);
                    self.watchlist.add_watch(initial[1], *watch);
                    return false;
                }
            }

            if self.assignment.lit_is_false(first) {
                // conflict
                todo!();
            }

            // unit clause => propagate
            self.enqueue_assignment(first);

            true
        });
        self.watchlist[lit] = watches;
    }

    pub(crate) fn enqueue_assignment(&mut self, assignment: Lit) {
        self.assignment.assign_function(assignment);
        self.trail.push(assignment);
    }
}
