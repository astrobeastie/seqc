use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

use crate::expr::{Expr, ExprEnumerator};
use crate::proof::{Proof, ProofStep};
use crate::substitution::{Subst, Substitution};

#[derive(Debug, Clone)]
pub enum Formula {
    Bot,
    Top,
    Pred(String, Vec<Expr>),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implication(Box<Formula>, Box<Formula>),
    All(String, Box<Formula>), // quantifiers save the bound name, bound variables use De Bruijin indices
    Exists(String, Box<Formula>),
}

// Eq must respect alpha equivalence, so we implement it manually.
impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Formula::Bot, Formula::Bot) | (Formula::Top, Formula::Top) => true,
            (Formula::Pred(x, args1), Formula::Pred(y, args2)) => x == y && args1 == args2,
            (Formula::Not(g1), Formula::Not(g2)) => g1 == g2,
            (Formula::And(a1, b1), Formula::And(a2, b2))
            | (Formula::Or(a1, b1), Formula::Or(a2, b2))
            | (Formula::Implication(a1, b1), Formula::Implication(a2, b2)) => a1 == a2 && b1 == b2,
            (Formula::All(_, g1), Formula::All(_, g2))
            | (Formula::Exists(_, g1), Formula::Exists(_, g2)) => {
                // alpha equivalence: bound names do not matter
                g1 == g2
            }
            _ => false,
        }
    }
}

impl Eq for Formula {}

impl Hash for Formula {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Formula::Bot => {
                state.write_u8(0);
            }
            Formula::Top => {
                state.write_u8(1);
            }
            Formula::Pred(name, args) => {
                state.write_u8(2);
                name.hash(state);
                for a in args {
                    a.hash(state);
                }
            }
            Formula::Not(g) => {
                state.write_u8(3);
                g.hash(state);
            }
            Formula::And(a, b) => {
                state.write_u8(4);
                a.hash(state);
                b.hash(state);
            }
            Formula::Or(a, b) => {
                state.write_u8(5);
                a.hash(state);
                b.hash(state);
            }
            Formula::Implication(a, b) => {
                state.write_u8(6);
                a.hash(state);
                b.hash(state);
            }
            Formula::All(_, g) => {
                state.write_u8(7);
                g.hash(state);
            }
            Formula::Exists(_, g) => {
                state.write_u8(8);
                g.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Sequent {
    pub assumptions: HashSet<Formula>,
    pub conclusions: HashSet<Formula>,
}

impl Hash for Sequent {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Order-independent hash via XOR of per-element finishes.
        let combine = |set: &HashSet<Formula>| -> u64 {
            set.iter()
                .map(|f| {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    f.hash(&mut h);
                    std::hash::Hasher::finish(&h)
                })
                .fold(0u64, |acc, x| acc ^ x)
        };
        state.write_u64(combine(&self.assumptions));
        state.write_u64(combine(&self.conclusions));
    }
}

impl Sequent {
    pub fn free_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    pub fn collect_free_vars(&self, vars: &mut HashSet<String>) {
        for f in self.assumptions.iter().chain(self.conclusions.iter()) {
            f.collect_free_vars(vars);
        }
    }

    pub fn proof_search(&self, max_depth: usize) -> Option<Proof> {
        let mut memo: HashMap<Sequent, usize> = HashMap::new();
        self.proof_search_memo(max_depth, &mut memo)
    }

    fn proof_search_memo(
        &self,
        max_depth: usize,
        memo: &mut HashMap<Sequent, usize>,
    ) -> Option<Proof> {
        if max_depth == 0 {
            return None;
        }
        if let Some(&d) = memo.get(self) {
            if d >= max_depth {
                return None;
            }
        }
        if self.assumptions.contains(&Formula::Bot) {
            return Some(Proof {
                claim: self.clone(),
                proof: ProofStep::BotLeft,
            });
        }
        if self
            .assumptions
            .iter()
            .any(|f| self.conclusions.contains(&f))
        {
            return Some(Proof {
                claim: self.clone(),
                proof: ProofStep::Axiom,
            });
        }
        for f in self.assumptions.iter() {
            if let Formula::Not(g) = f {
                let mut new_assms = self.assumptions.clone();
                new_assms.remove(f);
                let mut new_concs = self.conclusions.clone();
                new_concs.insert(g.as_ref().clone());

                let new_sequent = Sequent {
                    assumptions: new_assms,
                    conclusions: new_concs,
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::NegLeft(Box::new(proof)),
                    });
                }
            }
            if let Formula::And(a, b) = f {
                let mut new_assms = self.assumptions.clone();
                new_assms.remove(f);
                new_assms.insert(a.as_ref().clone());
                new_assms.insert(b.as_ref().clone());
                let new_sequent = Sequent {
                    assumptions: new_assms,
                    conclusions: self.conclusions.clone(),
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::AndLeft(Box::new(proof)),
                    });
                }
            }

            if let Formula::Or(a, b) = f {
                let mut new_assms_a = self.assumptions.clone();
                new_assms_a.remove(f);
                new_assms_a.insert(a.as_ref().clone());
                let seqa = Sequent {
                    assumptions: new_assms_a,
                    conclusions: self.conclusions.clone(),
                };
                let mut new_assms_b = self.assumptions.clone();
                new_assms_b.remove(f);
                new_assms_b.insert(b.as_ref().clone());
                let seqb = Sequent {
                    assumptions: new_assms_b,
                    conclusions: self.conclusions.clone(),
                };
                if let (Some(proofa), Some(proofb)) = (
                    seqa.proof_search_memo(max_depth - 1, memo),
                    seqb.proof_search_memo(max_depth - 1, memo),
                ) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::OrLeft(Box::new(proofa), Box::new(proofb)),
                    });
                }
            }

            if let Formula::Implication(a, b) = f {
                let mut new_assms_1 = self.assumptions.clone();
                new_assms_1.remove(f);
                let mut new_concs_1 = self.conclusions.clone();
                new_concs_1.insert(a.as_ref().clone());
                let seq1 = Sequent {
                    assumptions: new_assms_1,
                    conclusions: new_concs_1,
                };
                let mut new_assms_2 = self.assumptions.clone();
                new_assms_2.remove(f);
                new_assms_2.insert(b.as_ref().clone());
                let seq2 = Sequent {
                    assumptions: new_assms_2,
                    conclusions: self.conclusions.clone(),
                };
                if let (Some(proof1), Some(proof2)) = (
                    seq1.proof_search_memo(max_depth - 1, memo),
                    seq2.proof_search_memo(max_depth - 1, memo),
                ) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::ImplLeft(Box::new(proof1), Box::new(proof2)),
                    });
                }
            }

            if let Formula::Exists(x, body) = f {
                let mut new_assms = self.assumptions.clone();
                new_assms.remove(f);
                let free_var = self.new_free_var(vec![x]);
                new_assms.insert(body.instantiate(&Expr::Free(free_var)));
                let new_sequent = Sequent {
                    assumptions: new_assms,
                    conclusions: self.conclusions.clone(),
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::ExistsLeft(Box::new(proof)),
                    });
                }
            }

            // Forall Left and exists Right should be checked at the end
        }

        for f in self.conclusions.iter() {
            if let Formula::Not(g) = f {
                let mut new_assms = self.assumptions.clone();
                new_assms.insert(g.as_ref().clone());
                let mut new_concs = self.conclusions.clone();
                new_concs.remove(f);

                let new_sequent = Sequent {
                    assumptions: new_assms,
                    conclusions: new_concs,
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::NegRight(Box::new(proof)),
                    });
                }
            }

            if let Formula::And(a, b) = f {
                let mut new_concs_a = self.conclusions.clone();
                new_concs_a.remove(f);
                new_concs_a.insert(a.as_ref().clone());
                let seqa = Sequent {
                    assumptions: self.assumptions.clone(),
                    conclusions: new_concs_a,
                };
                let mut new_concs_b = self.conclusions.clone();
                new_concs_b.remove(f);
                new_concs_b.insert(b.as_ref().clone());
                let seqb = Sequent {
                    assumptions: self.assumptions.clone(),
                    conclusions: new_concs_b,
                };
                if let (Some(proofa), Some(proofb)) = (
                    seqa.proof_search_memo(max_depth - 1, memo),
                    seqb.proof_search_memo(max_depth - 1, memo),
                ) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::AndRight(Box::new(proofa), Box::new(proofb)),
                    });
                }
            }
            if let Formula::Or(a, b) = f {
                let mut new_concs = self.conclusions.clone();
                new_concs.remove(f);
                new_concs.insert(a.as_ref().clone());
                new_concs.insert(b.as_ref().clone());
                let new_sequent = Sequent {
                    assumptions: self.assumptions.clone(),
                    conclusions: new_concs,
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::OrRight(Box::new(proof)),
                    });
                }
            }

            if let Formula::Implication(a, b) = f {
                let mut new_assms = self.assumptions.clone();
                new_assms.insert(a.as_ref().clone());
                let mut new_concs = self.conclusions.clone();
                new_concs.remove(f);
                new_concs.insert(b.as_ref().clone());
                let new_sequent = Sequent {
                    assumptions: new_assms,
                    conclusions: new_concs,
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::ImplRight(Box::new(proof)),
                    });
                }
            }

            if let Formula::All(x, body) = f {
                let mut new_concs = self.conclusions.clone();
                new_concs.remove(f);
                let free_var = self.new_free_var(vec![x]);
                new_concs.insert(body.instantiate(&Expr::Free(free_var)));
                let new_sequent = Sequent {
                    assumptions: self.assumptions.clone(),
                    conclusions: new_concs,
                };
                if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                    return Some(Proof {
                        claim: self.clone(),
                        proof: ProofStep::ForAllRight(Box::new(proof)),
                    });
                }
            }
            // Exists Right should be checked at the end
        }
        // check easy cases of AllLeft and ExistsRight first. ie. if the other side already contains an instance
        for f in self.assumptions.iter() {
            if let Formula::All(_, body) = f {
                // Very easy case: body has no Bound(0), so the instance is
                // independent of the witness — only one instantiation exists.
                if !body.mentions_bound(0) {
                    let mut new_assms = self.assumptions.clone();
                    new_assms.remove(f);
                    new_assms.insert(body.lower(0));
                    let new_sequent = Sequent {
                        assumptions: new_assms,
                        conclusions: self.conclusions.clone(),
                    };
                    if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                        return Some(Proof {
                            claim: self.clone(),
                            proof: ProofStep::ForAllLeft(Box::new(proof)),
                        });
                    }
                }
                for instance in self.conclusions.iter() {
                    if let Some(s) = instance.is_instance_of(body, 0) {
                        let mut new_assms = self.assumptions.clone();
                        new_assms.remove(f);
                        new_assms.insert(body.instantiate(&s.lookup(0).unwrap()));
                        let new_sequent = Sequent {
                            assumptions: new_assms,
                            conclusions: self.conclusions.clone(),
                        };
                        return Some(Proof {
                            claim: self.clone(),
                            proof: ProofStep::ForAllLeft(Box::new(Proof {
                                claim: new_sequent.clone(),
                                proof: ProofStep::Axiom,
                            })),
                        });
                    }
                }
            }
        }

        for f in self.conclusions.iter() {
            if let Formula::Exists(_, body) = f {
                // Very easy case: body has no Bound(0), so the instance is
                // independent of the witness — only one instantiation exists.
                if !body.mentions_bound(0) {
                    let mut new_concs = self.conclusions.clone();
                    new_concs.remove(f);
                    new_concs.insert(body.lower(0));
                    let new_sequent = Sequent {
                        assumptions: self.assumptions.clone(),
                        conclusions: new_concs,
                    };
                    if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                        return Some(Proof {
                            claim: self.clone(),
                            proof: ProofStep::ExistsRight(Box::new(proof)),
                        });
                    }
                }
                for instance in self.assumptions.iter() {
                    if let Some(s) = instance.is_instance_of(body, 0) {
                        let mut new_concs = self.conclusions.clone();
                        new_concs.remove(f);
                        new_concs.insert(body.instantiate(&s.lookup(0).unwrap()));
                        let new_sequent = Sequent {
                            assumptions: self.assumptions.clone(),
                            conclusions: new_concs,
                        };
                        return Some(Proof {
                            claim: self.clone(),
                            proof: ProofStep::ExistsRight(Box::new(Proof {
                                claim: new_sequent.clone(),
                                proof: ProofStep::Axiom,
                            })),
                        });
                    }
                }
            }
        }

        // Witness search for ∀L / ∃R when the body mentions Bound(0).
        // First, try every closed term that already appears in the sequent;
        // then fall back to systematic enumeration over the signature, up to
        // (max subterm size + 1) × (max arity + 1) in node count.
        let symbols = self.constants_with_arity();
        let mut subterms: Vec<Expr> = self.closed_subterms().into_iter().collect();
        subterms.sort_by_key(|e| e.to_string());
        let max_subterm_size = subterms.iter().map(|e| e.size()).max().unwrap_or(0);
        let max_arity = symbols.iter().map(|(_, k)| *k).max().unwrap_or(0);
        let max_instance_size = (max_subterm_size + 1) * (max_arity + 1);
        let witnesses = subterms
            .into_iter()
            .chain(ExprEnumerator::new(symbols).take_while(|e| e.size() <= max_instance_size));

        let mut tried: HashSet<Expr> = HashSet::new();
        for witness in witnesses {
            if !tried.insert(witness.clone()) {
                continue;
            }
            for f in self.assumptions.iter() {
                if let Formula::All(_, body) = f {
                    if !body.mentions_bound(0) {
                        continue; // handled by easy case above
                    }
                    let instance = body.instantiate(&witness);
                    if self.assumptions.contains(&instance) {
                        continue;
                    }
                    // Keep `f` in the assumptions: a different witness may be
                    // needed later in the same proof branch.
                    let mut new_assms = self.assumptions.clone();
                    new_assms.insert(instance);
                    let new_sequent = Sequent {
                        assumptions: new_assms,
                        conclusions: self.conclusions.clone(),
                    };
                    if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                        return Some(Proof {
                            claim: self.clone(),
                            proof: ProofStep::ForAllLeft(Box::new(proof)),
                        });
                    }
                }
            }
            for f in self.conclusions.iter() {
                if let Formula::Exists(_, body) = f {
                    if !body.mentions_bound(0) {
                        continue;
                    }
                    let instance = body.instantiate(&witness);
                    if self.conclusions.contains(&instance) {
                        continue;
                    }
                    let mut new_concs = self.conclusions.clone();
                    new_concs.insert(instance);
                    let new_sequent = Sequent {
                        assumptions: self.assumptions.clone(),
                        conclusions: new_concs,
                    };
                    if let Some(proof) = new_sequent.proof_search_memo(max_depth - 1, memo) {
                        return Some(Proof {
                            claim: self.clone(),
                            proof: ProofStep::ExistsRight(Box::new(proof)),
                        });
                    }
                }
            }
        }

        memo.entry(self.clone())
            .and_modify(|d| *d = (*d).max(max_depth))
            .or_insert(max_depth);
        None
    }

    pub fn constants_with_arity(&self) -> HashSet<(String, usize)> {
        let mut symbols = HashSet::new();
        for f in self.assumptions.iter().chain(self.conclusions.iter()) {
            f.collect_constants(&mut symbols);
        }
        symbols
    }

    pub fn closed_subterms(&self) -> HashSet<Expr> {
        let mut terms = HashSet::new();
        for f in self.assumptions.iter().chain(self.conclusions.iter()) {
            f.collect_closed_subterms(&mut terms);
        }
        terms
    }

    pub fn size(&self) -> usize {
        self.assumptions
            .iter()
            .chain(self.conclusions.iter())
            .map(|f| f.size())
            .sum()
    }

    pub fn new_free_var(&self, preferred: Vec<&str>) -> String {
        let vars = self.free_vars();
        for p in preferred.iter() {
            if !vars.contains(*p) {
                return p.to_string();
            }
        }

        let mut i = 1;
        loop {
            for p in preferred.iter() {
                let candidate = format!("{}_{}", *p, i);
                if !vars.contains(&candidate) {
                    return candidate;
                }
            }
            i += 1;
        }
    }
}

impl Formula {
    pub fn free_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars);
        vars
    }

    pub fn collect_free_vars(&self, vars: &mut HashSet<String>) {
        match self {
            Formula::Bot | Formula::Top => {}
            Formula::Pred(_, args) => {
                for a in args {
                    a.collect_free_vars(vars);
                }
            }
            Formula::Not(g) => g.collect_free_vars(vars),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implication(a, b) => {
                a.collect_free_vars(vars);
                b.collect_free_vars(vars);
            }
            Formula::All(_, body) | Formula::Exists(_, body) => {
                body.collect_free_vars(vars);
            }
        }
    }

    pub fn all_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        self.collect_all_vars(&mut vars);
        vars
    }

    pub fn collect_all_vars(&self, vars: &mut HashSet<String>) {
        match self {
            Formula::Bot | Formula::Top => {}
            Formula::Pred(_, args) => {
                for a in args {
                    a.collect_free_vars(vars);
                }
            }
            Formula::Not(g) => g.collect_all_vars(vars),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implication(a, b) => {
                a.collect_all_vars(vars);
                b.collect_all_vars(vars);
            }
            Formula::All(x, body) | Formula::Exists(x, body) => {
                vars.insert(x.clone());
                body.collect_all_vars(vars);
            }
        }
    }

    pub fn new_free_var(&self, preferred: Vec<&str>) -> String {
        let vars = self.free_vars();
        for p in preferred.iter() {
            if !vars.contains(*p) {
                return p.to_string();
            }
        }

        let mut i = 1;
        loop {
            for p in preferred.iter() {
                let candidate = format!("{}_{}", *p, i);
                if !vars.contains(&candidate) {
                    return candidate;
                }
            }
            i += 1;
        }
    }

    pub fn lift(&self, min: usize) -> Formula {
        match self {
            Formula::Bot | Formula::Top => self.clone(),
            Formula::Pred(name, args) => {
                Formula::Pred(name.clone(), args.iter().map(|a| a.lift(min)).collect())
            }
            Formula::Not(g) => Formula::Not(Box::new(g.lift(min))),
            Formula::And(a, b) => Formula::And(Box::new(a.lift(min)), Box::new(b.lift(min))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.lift(min)), Box::new(b.lift(min))),
            Formula::Implication(a, b) => {
                Formula::Implication(Box::new(a.lift(min)), Box::new(b.lift(min)))
            }
            Formula::All(x, body) => Formula::All(x.clone(), Box::new(body.lift(min + 1))),
            Formula::Exists(x, body) => Formula::Exists(x.clone(), Box::new(body.lift(min + 1))),
        }
    }

    /// Checks whether `self` is an instance of `template` at de Bruijn depth
    /// `depth`, i.e. whether there exists a closed expression `t` (containing
    /// no `Bound` indices) such that `template.instantiate(&t) == self` (when
    /// `template` is treated as a quantifier body).
    ///
    /// On success, returns a substitution binding `0 -> witness` (or empty
    /// if `Bound(depth)` does not occur in `template`, in which case any
    /// term works). Returns `None` when there is no instance.
    pub fn is_instance_of(&self, template: &Formula, depth: usize) -> Option<Substitution> {
        match (template, self) {
            (Formula::Bot, Formula::Bot) | (Formula::Top, Formula::Top) => {
                Some(Substitution::new())
            }
            (Formula::Pred(n1, a1), Formula::Pred(n2, a2)) if n1 == n2 && a1.len() == a2.len() => {
                a1.iter()
                    .zip(a2.iter())
                    .try_fold(Substitution::new(), |acc, (x, y)| {
                        acc.merge(&y.is_instance_of(x, depth)?)
                    })
            }
            (Formula::Not(g1), Formula::Not(g2)) => g2.is_instance_of(g1, depth),
            (Formula::And(a1, b1), Formula::And(a2, b2))
            | (Formula::Or(a1, b1), Formula::Or(a2, b2))
            | (Formula::Implication(a1, b1), Formula::Implication(a2, b2)) => {
                let s1 = a2.is_instance_of(a1, depth)?;
                let s2 = b2.is_instance_of(b1, depth)?;
                s1.merge(&s2)
            }
            (Formula::All(_, b1), Formula::All(_, b2))
            | (Formula::Exists(_, b1), Formula::Exists(_, b2)) => b2.is_instance_of(b1, depth + 1),
            _ => None,
        }
    }

    /// Instantiate `self` (the body of a quantifier) with witness `t`. Equal
    /// to `self.subst(&{0 -> t.lift(0)}).lower(0)`. The caller is responsible
    /// for ensuring `self` is a body (i.e. has been extracted from an
    /// `All`/`Exists`).
    pub fn instantiate(&self, t: &Expr) -> Formula {
        let sigma = Substitution::singleton(0, t.lift(0));
        self.subst(&sigma).lower(0)
    }

    pub fn lower(&self, min: usize) -> Formula {
        match self {
            Formula::Bot | Formula::Top => self.clone(),
            Formula::Pred(name, args) => {
                Formula::Pred(name.clone(), args.iter().map(|a| a.lower(min)).collect())
            }
            Formula::Not(g) => Formula::Not(Box::new(g.lower(min))),
            Formula::And(a, b) => Formula::And(Box::new(a.lower(min)), Box::new(b.lower(min))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.lower(min)), Box::new(b.lower(min))),
            Formula::Implication(a, b) => {
                Formula::Implication(Box::new(a.lower(min)), Box::new(b.lower(min)))
            }
            Formula::All(x, body) => Formula::All(x.clone(), Box::new(body.lower(min + 1))),
            Formula::Exists(x, body) => Formula::Exists(x.clone(), Box::new(body.lower(min + 1))),
        }
    }
    pub fn collect_constants(&self, symbols: &mut HashSet<(String, usize)>) {
        match self {
            Formula::Bot | Formula::Top => {}
            Formula::Pred(_, args) => {
                for a in args {
                    a.collect_constants(symbols);
                }
            }
            Formula::Not(g) => g.collect_constants(symbols),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implication(a, b) => {
                a.collect_constants(symbols);
                b.collect_constants(symbols);
            }
            Formula::All(_, body) | Formula::Exists(_, body) => {
                body.collect_constants(symbols);
            }
        }
    }

    pub fn mentions_bound(&self, idx: usize) -> bool {
        match self {
            Formula::Bot | Formula::Top => false,
            Formula::Pred(_, args) => args.iter().any(|a| a.mentions_bound(idx)),
            Formula::Not(g) => g.mentions_bound(idx),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implication(a, b) => {
                a.mentions_bound(idx) || b.mentions_bound(idx)
            }
            Formula::All(_, body) | Formula::Exists(_, body) => body.mentions_bound(idx + 1),
        }
    }

    pub fn collect_closed_subterms(&self, terms: &mut HashSet<Expr>) {
        match self {
            Formula::Bot | Formula::Top => {}
            Formula::Pred(_, args) => {
                for a in args {
                    a.collect_closed_subterms(terms);
                }
            }
            Formula::Not(g) => g.collect_closed_subterms(terms),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implication(a, b) => {
                a.collect_closed_subterms(terms);
                b.collect_closed_subterms(terms);
            }
            Formula::All(_, body) | Formula::Exists(_, body) => {
                body.collect_closed_subterms(terms);
            }
        }
    }

    pub fn size(&self) -> usize {
        match self {
            Formula::Bot | Formula::Top => 1,
            Formula::Pred(_, args) => 1 + args.iter().map(|a| a.size()).sum::<usize>(),
            Formula::Not(g) => 1 + g.size(),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implication(a, b) => {
                1 + a.size() + b.size()
            }
            Formula::All(_, body) | Formula::Exists(_, body) => 1 + body.size(),
        }
    }
}

// Precedences for non-binary syntactic forms.
const PREC_ATOM: u8 = 100;
const PREC_NEG: u8 = 90;
// Quantifiers bind only the next atomic formula (same as negation), so they
// share negation's precedence — a quantifier as a binop child needs no parens.
const PREC_QUANT: u8 = 90;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Assoc {
    Left,
    Right,
}

impl Assoc {
    /// `(left_min, right_min)` for a binary operator at precedence `op_prec`.
    /// The "tight" side accepts equal precedence without parens; the "loose"
    /// side requires strictly higher. Used identically by the parser (as
    /// `(l_prec, r_prec)` in the Pratt loop) and by the printer (as the `min`
    /// passed to each child).
    pub fn child_mins(self, op_prec: u8) -> (u8, u8) {
        match self {
            Assoc::Left => (op_prec, op_prec + 1),
            Assoc::Right => (op_prec + 1, op_prec),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum BinOp {
    And,
    Or,
    Implication,
}

impl BinOp {
    pub fn prec(self) -> u8 {
        match self {
            BinOp::And => 30,
            BinOp::Or => 20,
            BinOp::Implication => 10,
        }
    }

    pub fn assoc(self) -> Assoc {
        match self {
            BinOp::And | BinOp::Or => Assoc::Left,
            BinOp::Implication => Assoc::Right,
        }
    }

    pub fn glyph(self) -> &'static str {
        match self {
            BinOp::And => " ∧ ",
            BinOp::Or => " ∨ ",
            BinOp::Implication => " → ",
        }
    }
}

impl Formula {
    pub fn neg(&self) -> Formula {
        Formula::Not(Box::new(self.clone()))
    }

    fn prec(&self) -> u8 {
        match self {
            Formula::Bot | Formula::Top | Formula::Pred(_, _) => PREC_ATOM,
            Formula::Not(_) => PREC_NEG,
            Formula::And(_, _) => BinOp::And.prec(),
            Formula::Or(_, _) => BinOp::Or.prec(),
            Formula::Implication(_, _) => BinOp::Implication.prec(),
            Formula::All(_, _) | Formula::Exists(_, _) => PREC_QUANT,
        }
    }

    fn fmt_at(&self, f: &mut fmt::Formatter<'_>, min: u8, bound_vars: &Vec<&str>) -> fmt::Result {
        let parens = self.prec() < min;
        if parens {
            write!(f, "(")?;
        }
        match self {
            Formula::Bot => write!(f, "⊥")?,
            Formula::Top => write!(f, "⊤")?,
            Formula::Pred(name, args) => {
                write!(f, "{}", name)?;
                if !args.is_empty() {
                    write!(f, "(")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        a.fmt_with(f, bound_vars)?;
                    }
                    write!(f, ")")?;
                }
            }
            Formula::Not(g) => {
                write!(f, "¬")?;
                g.fmt_at(f, PREC_NEG, bound_vars)?;
            }
            Formula::And(a, b) => fmt_binop(f, a, b, BinOp::And, bound_vars)?,
            Formula::Or(a, b) => fmt_binop(f, a, b, BinOp::Or, bound_vars)?,
            Formula::Implication(a, b) => fmt_binop(f, a, b, BinOp::Implication, bound_vars)?,
            Formula::All(x, body) => {
                let mut new_vars = bound_vars.clone();
                new_vars.push(x);
                write!(f, "∀{}. ", x)?;
                body.fmt_at(f, PREC_QUANT, &new_vars)?;
            }
            Formula::Exists(x, body) => {
                let mut new_vars = bound_vars.clone();
                new_vars.push(x);
                write!(f, "∃{}. ", x)?;
                body.fmt_at(f, PREC_QUANT, &new_vars)?;
            }
        }
        if parens {
            write!(f, ")")?;
        }
        Ok(())
    }
}

fn fmt_binop(
    f: &mut fmt::Formatter<'_>,
    lhs: &Formula,
    rhs: &Formula,
    op: BinOp,
    bound_vars: &Vec<&str>,
) -> fmt::Result {
    let (left_min, right_min) = op.assoc().child_mins(op.prec());
    lhs.fmt_at(f, left_min, bound_vars)?;
    write!(f, "{}", op.glyph())?;
    rhs.fmt_at(f, right_min, bound_vars)
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(f, 0, &vec![])
    }
}

impl fmt::Display for Sequent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lhs: Vec<String> = self.assumptions.iter().map(|a| a.to_string()).collect();
        write!(f, "{}", lhs.join(", "))?;
        write!(f, " ⇒ ")?;
        let rhs: Vec<String> = self.conclusions.iter().map(|c| c.to_string()).collect();
        write!(f, "{}", rhs.join(", "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn parse_formula(s: &str) -> Formula {
        let mut p = Parser::new(s.to_string()).expect("parser init");
        p.parse_formula().expect("parse_formula")
    }

    /// Parse `forall x. F` and return F (the body, which has `Bound(0)` for x).
    fn body_of_forall(s: &str) -> Formula {
        match parse_formula(s) {
            Formula::All(_, body) => *body,
            other => panic!("expected ∀, got {:?}", other),
        }
    }

    #[test]
    fn instance_with_simple_witness() {
        let template = body_of_forall("forall x. P(x)");
        let target = parse_formula("P(a)");
        assert_eq!(
            target.is_instance_of(&template, 0),
            Some(Substitution::singleton(0, Expr::Free("a".to_string())))
        );
    }

    #[test]
    fn instance_with_function_witness() {
        let template = body_of_forall("forall x. P(x)");
        let target = parse_formula("P(f(a))");
        assert_eq!(
            target.is_instance_of(&template, 0),
            Some(Substitution::singleton(
                0,
                Expr::Func("f".to_string(), vec![Expr::Free("a".to_string())])
            ))
        );
    }

    #[test]
    fn instance_with_constant_part() {
        let template = body_of_forall("forall x. P(x, b)");
        let target = parse_formula("P(a, b)");
        assert_eq!(
            target.is_instance_of(&template, 0),
            Some(Substitution::singleton(0, Expr::Free("a".to_string())))
        );
    }

    #[test]
    fn inconsistent_witness_fails() {
        // forall x. P(x, x) — target P(a, b) requires x = a AND x = b.
        let template = body_of_forall("forall x. P(x, x)");
        let target = parse_formula("P(a, b)");
        assert_eq!(target.is_instance_of(&template, 0), None);
    }

    #[test]
    fn structural_mismatch_fails() {
        let template = body_of_forall("forall x. P(x)");
        let target = parse_formula("Q(a)");
        assert_eq!(target.is_instance_of(&template, 0), None);
    }

    #[test]
    fn nested_quantifier_instance() {
        // ∀x. ∀y. P(x, y) — instance with x = a is ∀y. P(a, y).
        let template = body_of_forall("forall x. forall y. P(x, y)");
        let target = parse_formula("forall y. P(a, y)");
        assert_eq!(
            target.is_instance_of(&template, 0),
            Some(Substitution::singleton(0, Expr::Free("a".to_string())))
        );
    }

    #[test]
    fn vacuous_template_returns_empty_substitution() {
        // ∀x. P(a) — body has no Bound(0); any t works.
        let template = body_of_forall("forall x. P(a)");
        let target = parse_formula("P(a)");
        assert_eq!(
            target.is_instance_of(&template, 0),
            Some(Substitution::new())
        );
    }

    #[test]
    fn is_instance_rejects_bound_witness() {
        // ∀x. P(x) — target P(Bound(0)) would require t = Bound(0). The
        // implementation only accepts closed witnesses (no Bound).
        let template = body_of_forall("forall x. P(x)");
        let target = Formula::Pred("P".to_string(), vec![Expr::Bound(0)]);
        assert_eq!(target.is_instance_of(&template, 0), None);
    }

    #[test]
    fn is_instance_rejects_func_with_bound() {
        // Likewise, t = f(Bound(0)) is not closed and gets rejected.
        let template = body_of_forall("forall x. P(x)");
        let target = Formula::Pred(
            "P".to_string(),
            vec![Expr::Func("f".to_string(), vec![Expr::Bound(0)])],
        );
        assert_eq!(target.is_instance_of(&template, 0), None);
    }

    #[test]
    fn instantiate_simple() {
        // body of ∀x. P(x) is P(Bound(0)). Instantiate with t = Free("a").
        // Expected: P(Free("a")).
        let body = body_of_forall("forall x. P(x)");
        let expected = parse_formula("P(a)");
        assert_eq!(body.instantiate(&Expr::Free("a".to_string())), expected);
    }

    #[test]
    fn instantiate_under_quantifier() {
        // body of ∀x. ∀y. P(x, y) is ∀y. P(Bound(1), Bound(0)).
        // Instantiate with t = Free("a") gives ∀y. P(a, y).
        let body = body_of_forall("forall x. forall y. P(x, y)");
        let expected = parse_formula("forall y. P(a, y)");
        assert_eq!(body.instantiate(&Expr::Free("a".to_string())), expected);
    }
}
