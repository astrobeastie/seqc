use std::collections::{HashMap, HashSet};

use crate::expr::Expr;
use crate::formula::Formula;

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Substitution {
    pub bindings: HashMap<usize, Expr>,
}

impl Substitution {
    pub fn new() -> Self {
        Substitution {
            bindings: HashMap::new(),
        }
    }

    pub fn singleton(var: usize, term: Expr) -> Self {
        let mut bindings = HashMap::new();
        bindings.insert(var, term);
        Substitution { bindings }
    }

    pub fn lookup(&self, var: usize) -> Option<&Expr> {
        self.bindings.get(&var)
    }

    pub fn terms_contain_var(&self, var: &str) -> bool {
        self.bindings.values().any(|t| t.occurs_free(var))
    }

    pub fn lift(&self) -> Substitution {
        let bindings = self
            .bindings
            .iter()
            .map(|(&v, t)| (v + 1, t.lift(0)))
            .collect();
        Substitution { bindings }
    }

    pub fn merge(&self, other: &Substitution) -> Option<Substitution> {
        let mut bindings = self.bindings.clone();
        for (k, v) in &other.bindings {
            match bindings.get(k) {
                Some(existing) if existing != v => return None,
                Some(_) => {}
                None => {
                    bindings.insert(*k, v.clone());
                }
            }
        }
        Some(Substitution { bindings })
    }

    /// Composition: applying `self.then(other)` to a term is the same as
    /// applying `self`, then applying `other`. For each `v -> t` in `self`,
    /// the resulting binding is `v -> t.subst(other)`. Bindings from `other`
    /// for variables not in `self` are appended.
    pub fn then(&self, other: &Substitution) -> Substitution {
        let mut bindings: HashMap<usize, Expr> = self
            .bindings
            .iter()
            .map(|(&v, t)| (v, t.subst(other)))
            .collect();
        for (&v, t) in &other.bindings {
            bindings.entry(v).or_insert_with(|| t.clone());
        }
        Substitution { bindings }
    }
}

pub trait Subst: Sized {
    fn subst(&self, sigma: &Substitution) -> Self;
}

impl Subst for Expr {
    fn subst(&self, sigma: &Substitution) -> Expr {
        match self {
            Expr::Bound(idx) => match sigma.lookup(*idx) {
                Some(t) => t.clone(),
                None => self.clone(),
            },
            Expr::Func(name, args) => {
                Expr::Func(name.clone(), args.iter().map(|a| a.subst(sigma)).collect())
            }
            Expr::Free(_) => self.clone(),
        }
    }
}

fn new_free_var(vars: HashSet<String>, preferred: Vec<&str>) -> String {
    for p in preferred.iter() {
        if !vars.contains(*p) {
            return p.to_string();
        }
    }
    let mut i = 0;
    loop {
        let candidate = format!("x{}", i);
        if !vars.contains(&candidate) {
            return candidate;
        }
        i += 1;
    }
}

impl Subst for Formula {
    fn subst(&self, sigma: &Substitution) -> Formula {
        match self {
            Formula::Bot | Formula::Top => self.clone(),
            Formula::Pred(name, args) => {
                Formula::Pred(name.clone(), args.iter().map(|a| a.subst(sigma)).collect())
            }
            Formula::Not(g) => Formula::Not(Box::new(g.subst(sigma))),
            Formula::And(a, b) => Formula::And(Box::new(a.subst(sigma)), Box::new(b.subst(sigma))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.subst(sigma)), Box::new(b.subst(sigma))),
            Formula::Implication(a, b) => {
                Formula::Implication(Box::new(a.subst(sigma)), Box::new(b.subst(sigma)))
            }
            Formula::All(y, body) => {
                if sigma.terms_contain_var(y) {
                    let all_vars = body
                        .all_vars()
                        .into_iter()
                        .chain(sigma.bindings.values().flat_map(|t| t.free_vars()))
                        .collect();
                    let fresh = new_free_var(all_vars, vec![y]);
                    Formula::All(fresh, Box::new(body.subst(&sigma.lift())))
                } else {
                    Formula::All(y.clone(), Box::new(body.subst(&sigma.lift())))
                }
            }
            Formula::Exists(y, body) => {
                if sigma.terms_contain_var(y) {
                    let all_vars = body
                        .all_vars()
                        .into_iter()
                        .chain(sigma.bindings.values().flat_map(|t| t.free_vars()))
                        .collect();
                    let fresh = new_free_var(all_vars, vec![y]);
                    Formula::Exists(fresh, Box::new(body.subst(&sigma.lift())))
                } else {
                    Formula::Exists(y.clone(), Box::new(body.subst(&sigma.lift())))
                }
            }
        }
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
    fn subst_replaces_bound_zero() {
        // body of ∀x. P(x) is P(Bound(0)); subst {0 -> a} → P(a).
        let template = body_of_forall("forall x. P(x)");
        let sigma = Substitution::singleton(0, Expr::Free("a".to_string()));
        assert_eq!(template.subst(&sigma), parse_formula("P(a)"));
    }

    #[test]
    fn subst_lifts_under_quantifier() {
        // body of ∀x. ∀y. P(x, y), with x = a, gives ∀y. P(a, y).
        let template = body_of_forall("forall x. forall y. P(x, y)");
        let sigma = Substitution::singleton(0, Expr::Free("a".to_string()));
        assert_eq!(template.subst(&sigma), parse_formula("forall y. P(a, y)"));
    }

    #[test]
    fn subst_avoids_capture() {
        // body of ∀x. ∀y. P(x, y), with x = (free) y. Naive subst would put
        // Free("y") under ∀y, which (in the displayed form) collides with the
        // bound name. The impl renames the inner binder to keep them distinct.
        let template = body_of_forall("forall x. forall y. P(x, y)");
        let sigma = Substitution::singleton(0, Expr::Free("y".to_string()));
        // Alpha-equivalent expected: ∀z. P(y, z) — bound name doesn't matter
        // for `==` since Formula's PartialEq ignores it.
        assert_eq!(template.subst(&sigma), parse_formula("forall z. P(y, z)"));
    }

    #[test]
    fn subst_no_matching_key_is_noop() {
        let f = parse_formula("P(a, b)");
        let sigma = Substitution::singleton(5, Expr::Free("c".to_string()));
        assert_eq!(f.subst(&sigma), f);
    }

    #[test]
    fn empty_subst_is_identity() {
        let f = parse_formula("forall x. P(x) -> Q(x)");
        assert_eq!(f.subst(&Substitution::new()), f);
    }

    #[test]
    fn subst_bound_term_simple() {
        // body of ∀x. P(x) is P(Bound(0)).
        // σ = {0 → Bound(2)} — t references some outer binder.
        // Result: P(Bound(2)).
        let template = body_of_forall("forall x. P(x)");
        let sigma = Substitution::singleton(0, Expr::Bound(2));
        let expected = Formula::Pred("P".to_string(), vec![Expr::Bound(2)]);
        assert_eq!(template.subst(&sigma), expected);
    }

    #[test]
    fn subst_func_with_bound_arg() {
        // σ = {0 → f(Bound(3))}, applied to P(Bound(0)).
        // Result: P(f(Bound(3))).
        let template = body_of_forall("forall x. P(x)");
        let sigma = Substitution::singleton(0, Expr::Func("f".to_string(), vec![Expr::Bound(3)]));
        let expected = Formula::Pred(
            "P".to_string(),
            vec![Expr::Func("f".to_string(), vec![Expr::Bound(3)])],
        );
        assert_eq!(template.subst(&sigma), expected);
    }

    #[test]
    fn subst_bound_term_through_quantifier() {
        // body of ∀x. ∀y. P(x) is ∀y. P(Bound(1)).
        // σ = {0 → Bound(2)}. When descending into ∀y, lift to
        // {1 → Bound(3)} — both key and value shift, so the term still
        // refers to the same outer binder it did before crossing ∀y.
        // Result: ∀y. P(Bound(3)).
        let template = body_of_forall("forall x. forall y. P(x)");
        let sigma = Substitution::singleton(0, Expr::Bound(2));
        let expected = Formula::All(
            "y".to_string(),
            Box::new(Formula::Pred("P".to_string(), vec![Expr::Bound(3)])),
        );
        assert_eq!(template.subst(&sigma), expected);
    }

    #[test]
    fn then_composes_substitutions() {
        // σ₁ = {0 -> f(Bound(1))}, σ₂ = {1 -> a}.
        // σ₁.then(σ₂) applies σ₂ to σ₁'s values:
        //   0 -> f(Bound(1)).subst({1 -> a}) = f(a).
        // Then carries σ₂'s 1 -> a over (key 1 not in σ₁).
        let sigma1 = Substitution::singleton(0, Expr::Func("f".to_string(), vec![Expr::Bound(1)]));
        let sigma2 = Substitution::singleton(1, Expr::Free("a".to_string()));
        let composed = sigma1.then(&sigma2);

        assert_eq!(
            composed.lookup(0),
            Some(&Expr::Func(
                "f".to_string(),
                vec![Expr::Free("a".to_string())]
            ))
        );
        assert_eq!(composed.lookup(1), Some(&Expr::Free("a".to_string())));
    }
}
