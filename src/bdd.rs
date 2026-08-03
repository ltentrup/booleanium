//! A minimal reduced ordered binary decision diagram package.
//!
//! Exists to answer a measurement question rather than to be a serious
//! BDD library: *how large are the objects this solver represents as
//! circuits and cube sets when they are represented as BDDs instead?*
//! Skolem functions and winning regions are the two candidates, and
//! their BDD size is the whole argument for or against a BDD-backed
//! conflict check — the check itself becomes a pointer comparison, so
//! the only question left is whether the representation stays small.
//!
//! Deliberately absent: complement edges, dynamic variable reordering,
//! garbage collection. Reordering in particular is what a real BDD
//! implementation lives or dies by, so sizes measured here are an
//! **upper bound** on what a tuned package would produce with the
//! natural (input-order) variable order.

use std::collections::HashMap;

/// A node handle. `0` is the false terminal and `1` the true terminal.
pub type NodeId = u32;

pub const FALSE: NodeId = 0;
pub const TRUE: NodeId = 1;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Node {
    /// index in the variable order; terminals use `u32::MAX` so that
    /// every decision node is ordered above them
    var: u32,
    low: NodeId,
    high: NodeId,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Op {
    And,
    Or,
}

#[derive(Default)]
pub struct Bdd {
    nodes: Vec<Node>,
    unique: HashMap<Node, NodeId>,
    apply_memo: HashMap<(Op, NodeId, NodeId), NodeId>,
    not_memo: HashMap<NodeId, NodeId>,
    /// nodes after which construction gives up; see [`Bdd::exceeded`]
    limit: usize,
    exceeded: bool,
}

impl Bdd {
    #[must_use]
    pub fn new() -> Self {
        Self::with_limit(usize::MAX)
    }

    /// A package that stops allocating past `limit` nodes.
    ///
    /// Not a nicety: BDD size is the one thing that can sink a
    /// BDD-backed conflict check, and the failure mode is exponential
    /// memory rather than slowness, so a measurement of "how big does
    /// it get" has to be able to answer "bigger than you can afford"
    /// without taking the machine down. A hybrid design — BDD while it
    /// stays cheap, SAT once it does not — needs exactly this signal.
    #[must_use]
    pub fn with_limit(limit: usize) -> Self {
        let terminal = Node { var: u32::MAX, low: FALSE, high: TRUE };
        Self { nodes: vec![terminal, terminal], limit, ..Self::default() }
    }

    /// Whether the node limit was hit. Every result computed after
    /// that is meaningless and must be discarded.
    #[must_use]
    pub fn exceeded(&self) -> bool {
        self.exceeded
    }

    /// Total nodes ever created, terminals included — the package's
    /// peak footprint, since nothing is collected.
    #[must_use]
    pub fn allocated(&self) -> usize {
        self.nodes.len()
    }

    fn is_terminal(id: NodeId) -> bool {
        id <= TRUE
    }

    fn var_of(&self, id: NodeId) -> u32 {
        self.nodes[id as usize].var
    }

    /// The reduced node for `(var, low, high)`: an unnecessary test is
    /// dropped and structurally equal nodes are shared, which together
    /// are what make the representation canonical.
    fn mk(&mut self, var: u32, low: NodeId, high: NodeId) -> NodeId {
        if low == high {
            return low;
        }
        let node = Node { var, low, high };
        if let Some(&id) = self.unique.get(&node) {
            return id;
        }
        if self.nodes.len() >= self.limit {
            self.exceeded = true;
            return FALSE;
        }
        let id = u32::try_from(self.nodes.len()).expect("node count fits u32");
        self.nodes.push(node);
        self.unique.insert(node, id);
        id
    }

    /// The projection function of the variable at order index `var`.
    pub fn variable(&mut self, var: u32) -> NodeId {
        self.mk(var, FALSE, TRUE)
    }

    pub fn not(&mut self, id: NodeId) -> NodeId {
        if Self::is_terminal(id) {
            return 1 - id;
        }
        if let Some(&cached) = self.not_memo.get(&id) {
            return cached;
        }
        let Node { var, low, high } = self.nodes[id as usize];
        let (low, high) = (self.not(low), self.not(high));
        let result = self.mk(var, low, high);
        self.not_memo.insert(id, result);
        result
    }

    pub fn and(&mut self, a: NodeId, b: NodeId) -> NodeId {
        self.apply(Op::And, a, b)
    }

    pub fn or(&mut self, a: NodeId, b: NodeId) -> NodeId {
        self.apply(Op::Or, a, b)
    }

    fn apply(&mut self, op: Op, a: NodeId, b: NodeId) -> NodeId {
        match op {
            Op::And => {
                if a == FALSE || b == FALSE {
                    return FALSE;
                }
                if a == TRUE {
                    return b;
                }
                if b == TRUE || a == b {
                    return a;
                }
            }
            Op::Or => {
                if a == TRUE || b == TRUE {
                    return TRUE;
                }
                if a == FALSE {
                    return b;
                }
                if b == FALSE || a == b {
                    return a;
                }
            }
        }
        // commutative, so order the operands to halve the memo
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        if let Some(&cached) = self.apply_memo.get(&(op, a, b)) {
            return cached;
        }
        // recurse on the topmost variable of the two, taking the
        // cofactors of whichever operand tests it
        let var = self.var_of(a).min(self.var_of(b));
        let cofactor = |bdd: &Self, id: NodeId, high: bool| {
            if bdd.var_of(id) == var {
                let node = bdd.nodes[id as usize];
                if high {
                    node.high
                } else {
                    node.low
                }
            } else {
                id
            }
        };
        let (a_low, b_low) = (cofactor(self, a, false), cofactor(self, b, false));
        let (a_high, b_high) = (cofactor(self, a, true), cofactor(self, b, true));
        let low = self.apply(op, a_low, b_low);
        let high = self.apply(op, a_high, b_high);
        let result = self.mk(var, low, high);
        self.apply_memo.insert((op, a, b), result);
        result
    }

    /// The nodes reachable from `root`, terminals included — the size
    /// of *this* function rather than of the whole package.
    #[must_use]
    pub fn size(&self, root: NodeId) -> usize {
        let mut seen = vec![false; self.nodes.len()];
        let mut stack = vec![root];
        let mut count = 0;
        while let Some(id) = stack.pop() {
            if std::mem::replace(&mut seen[id as usize], true) {
                continue;
            }
            count += 1;
            if !Self::is_terminal(id) {
                let node = self.nodes[id as usize];
                stack.push(node.low);
                stack.push(node.high);
            }
        }
        count
    }

    /// Builds the function given by an explicit truth table over `vars`
    /// variables, where the entry at index `i` is the value under the
    /// assignment whose variable `v` is bit `v` of `i`.
    ///
    /// The table is `2^vars` long, so this is for measuring regions the
    /// explicit fixpoint already enumerated, not for building anything
    /// large.
    pub fn from_truth_table(&mut self, table: &[bool], vars: u32) -> NodeId {
        assert_eq!(table.len(), 1 << vars, "the table must cover every assignment");
        self.build_table(table, 0, 0, vars)
    }

    /// `prefix` fixes the variables below `var`; the entries it selects
    /// are those whose low bits agree with it.
    fn build_table(&mut self, table: &[bool], prefix: usize, var: u32, vars: u32) -> NodeId {
        if var == vars {
            return NodeId::from(table[prefix]);
        }
        let low = self.build_table(table, prefix, var + 1, vars);
        let high = self.build_table(table, prefix | (1 << var), var + 1, vars);
        self.mk(var, low, high)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn reduction_and_sharing_make_it_canonical() {
        let mut bdd = Bdd::new();
        let (x, y) = (bdd.variable(0), bdd.variable(1));
        // x & y and !(!x | !y) must be the same node
        let conj = bdd.and(x, y);
        let (nx, ny) = (bdd.not(x), bdd.not(y));
        let disj = bdd.or(nx, ny);
        let de_morgan = bdd.not(disj);
        assert_eq!(conj, de_morgan);
        // a tautology reduces to the terminal
        let tautology = bdd.or(x, nx);
        assert_eq!(tautology, TRUE);
        let contradiction = bdd.and(x, nx);
        assert_eq!(contradiction, FALSE);
    }

    #[test]
    fn a_truth_table_round_trips() {
        let mut bdd = Bdd::new();
        // xor of three variables, the classic linear-size / hard-to-CNF
        // function
        let table: Vec<bool> = (0..8).map(|i: usize| i.count_ones() % 2 == 1).collect();
        let root = bdd.from_truth_table(&table, 3);
        let built = {
            let vars: Vec<NodeId> = (0..3).map(|v| bdd.variable(v)).collect();
            let mut acc = FALSE;
            for v in vars {
                // acc xor v
                let (na, nv) = (bdd.not(acc), bdd.not(v));
                let left = bdd.and(acc, nv);
                let right = bdd.and(na, v);
                acc = bdd.or(left, right);
            }
            acc
        };
        assert_eq!(root, built);
        // parity is the standard small-BDD/large-CNF function: one node
        // at the top level, two at each level below it, two terminals
        assert_eq!(bdd.size(root), 2 * 3 + 1);
    }

    #[test]
    fn size_counts_the_function_not_the_package() {
        let mut bdd = Bdd::new();
        let x = bdd.variable(0);
        let y = bdd.variable(3);
        let _unrelated = bdd.and(x, y);
        assert_eq!(bdd.size(x), 3, "one decision node and both terminals");
        assert!(bdd.allocated() > 3);
    }
}
