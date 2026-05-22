use std::collections::HashSet;
use std::fmt;

use crate::expr::Expr;
use crate::formula::{Formula, Sequent};

pub enum ProofStep {
    Axiom,
    BotLeft,
    NegLeft(Box<Proof>),
    NegRight(Box<Proof>),
    AndLeft(Box<Proof>),
    AndRight(Box<Proof>, Box<Proof>),
    OrLeft(Box<Proof>, Box<Proof>),
    OrRight(Box<Proof>),
    ImplLeft(Box<Proof>, Box<Proof>),
    ImplRight(Box<Proof>),
    ForAllLeft(Box<Proof>),
    ForAllRight(Box<Proof>),
    ExistsLeft(Box<Proof>),
    ExistsRight(Box<Proof>),
}

pub struct Proof {
    pub claim: Sequent,
    pub proof: ProofStep,
}

impl ProofStep {
    pub fn keyword(&self) -> &'static str {
        match self {
            ProofStep::Axiom => "axiom",
            ProofStep::BotLeft => "botL",
            ProofStep::NegLeft(_) => "negL",
            ProofStep::NegRight(_) => "negR",
            ProofStep::AndLeft(_) => "andL",
            ProofStep::AndRight(_, _) => "andR",
            ProofStep::OrLeft(_, _) => "orL",
            ProofStep::OrRight(_) => "orR",
            ProofStep::ImplLeft(_, _) => "impL",
            ProofStep::ImplRight(_) => "impR",
            ProofStep::ForAllLeft(_) => "forallL",
            ProofStep::ForAllRight(_) => "forallR",
            ProofStep::ExistsLeft(_) => "existsL",
            ProofStep::ExistsRight(_) => "existsR",
        }
    }

    pub fn children(&self) -> Vec<&Proof> {
        match self {
            ProofStep::Axiom | ProofStep::BotLeft => vec![],
            ProofStep::NegLeft(p)
            | ProofStep::NegRight(p)
            | ProofStep::AndLeft(p)
            | ProofStep::OrRight(p)
            | ProofStep::ImplRight(p)
            | ProofStep::ForAllLeft(p)
            | ProofStep::ForAllRight(p)
            | ProofStep::ExistsLeft(p)
            | ProofStep::ExistsRight(p) => vec![p.as_ref()],
            ProofStep::AndRight(a, b) | ProofStep::OrLeft(a, b) | ProofStep::ImplLeft(a, b) => {
                vec![a.as_ref(), b.as_ref()]
            }
        }
    }
}

impl Proof {
    fn fmt_at(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        let pad = "  ".repeat(indent);
        let children = self.proof.children();
        if children.is_empty() {
            write!(f, "{}{} by {}", pad, self.claim, self.proof.keyword())
        } else {
            writeln!(f, "{}{} by {} {{", pad, self.claim, self.proof.keyword())?;
            for (i, child) in children.iter().enumerate() {
                child.fmt_at(f, indent + 1)?;
                if i + 1 < children.len() {
                    writeln!(f, ",")?;
                } else {
                    writeln!(f)?;
                }
            }
            write!(f, "{}}}", pad)
        }
    }
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(f, 0)
    }
}

pub type ProofCheckError = Vec<String>;
pub type ProofCheckResult = std::result::Result<(), ProofCheckError>;

impl Proof {
    pub fn check(&self) -> ProofCheckResult {
        match &self.proof {
            ProofStep::Axiom => {
                if self
                    .claim
                    .assumptions
                    .intersection(&self.claim.conclusions)
                    .next()
                    .is_some()
                {
                    Ok(())
                } else {
                    Err(vec![format!("Cannot apply Axiom on {}", self.claim)])
                }
            }
            ProofStep::BotLeft => {
                if self.claim.assumptions.contains(&Formula::Bot) {
                    Ok(())
                } else {
                    Err(vec![format!("Cannot apply BotLeft on {}", self.claim)])
                }
            }
            ProofStep::NegLeft(p) => {
                // check assumption are a subset
                let mut conc_diff = p.claim.conclusions.difference(&self.claim.conclusions);
                let Some(f) = conc_diff.next() else {
                    return Err(vec![
                        format!("Proof step does not add new Conclusion on {}", p.claim),
                        format!("While checking NegLeft on {}", self.claim),
                    ]);
                };
                if conc_diff.next().is_some() {
                    return Err(vec![
                        format!("Proof step adds multiple new Conclusions on {}", p.claim),
                        format!("While checking NegLeft on {}", self.claim),
                    ]);
                }
                if !self.claim.assumptions.contains(&f.neg()) {
                    return Err(vec![
                        format!(
                            "Negation of new Conclusion {} does not occur in previous assumptions on {}",
                            f, p.claim
                        ),
                        format!("While checking NegLeft on {}", self.claim),
                    ]);
                }
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Proof step adds new Assumption on {}", p.claim),
                        format!("While checking NegLeft on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking NegLeft on {}", self.claim));
                    e
                })
            }
            ProofStep::NegRight(p) => {
                let mut assum_diff = p.claim.assumptions.difference(&self.claim.assumptions);
                let Some(f) = assum_diff.next() else {
                    return Err(vec![
                        format!("Proof step does not add new Assumption on {}", p.claim),
                        format!("While checking NegRight on {}", self.claim),
                    ]);
                };
                if assum_diff.next().is_some() {
                    return Err(vec![
                        format!("Proof step adds multiple new Assumptions on {}", p.claim),
                        format!("While checking NegRight on {}", self.claim),
                    ]);
                }
                if !self.claim.conclusions.contains(&f.neg()) {
                    return Err(vec![
                        format!(
                            "Negation of new Assumption {} does not occur in previous conclusions on {}",
                            f, p.claim
                        ),
                        format!("While checking NegRight on {}", self.claim),
                    ]);
                }
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Proof step adds new Conclusion on {}", p.claim),
                        format!("While checking NegRight on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking NegRight on {}", self.claim));
                    e
                })
            }
            ProofStep::AndLeft(p) => {
                let diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if diff.len() > 2 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than two new Assumptions on {}",
                            p.claim
                        ),
                        format!("While checking AndLeft on {}", self.claim),
                    ]);
                }
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::And(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        diff.iter().all(|x| *x == a || *x == b)
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "New Assumptions do not match the conjuncts of any conjunction in previous assumptions on {}",
                            p.claim
                        ),
                        format!("While checking AndLeft on {}", self.claim),
                    ]);
                }
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Proof step adds new Conclusion on {}", p.claim),
                        format!("While checking AndLeft on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking AndLeft on {}", self.claim));
                    e
                })
            }
            ProofStep::AndRight(p_left, p_right) => {
                let left_diff: HashSet<&Formula> = p_left
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if left_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Left branch adds more than one new Conclusion on {}",
                            p_left.claim
                        ),
                        format!("While checking AndRight on {}", self.claim),
                    ]);
                }
                let right_diff: HashSet<&Formula> = p_right
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if right_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Right branch adds more than one new Conclusion on {}",
                            p_right.claim
                        ),
                        format!("While checking AndRight on {}", self.claim),
                    ]);
                }
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::And(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        left_diff.iter().all(|x| *x == a) && right_diff.iter().all(|x| *x == b)
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "Sub-proofs do not match the conjuncts of any conjunction in previous conclusions on {} and {}",
                            p_left.claim, p_right.claim
                        ),
                        format!("While checking AndRight on {}", self.claim),
                    ]);
                }
                if !p_left.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Left branch adds new Assumption on {}", p_left.claim),
                        format!("While checking AndRight on {}", self.claim),
                    ]);
                }
                if !p_right.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Right branch adds new Assumption on {}", p_right.claim),
                        format!("While checking AndRight on {}", self.claim),
                    ]);
                }
                p_left.check().map_err(|mut e| {
                    e.push(format!(
                        "While checking left branch of AndRight on {}",
                        self.claim
                    ));
                    e
                })?;
                p_right.check().map_err(|mut e| {
                    e.push(format!(
                        "While checking right branch of AndRight on {}",
                        self.claim
                    ));
                    e
                })?;
                Ok(())
            }
            ProofStep::OrLeft(p_left, p_right) => {
                let left_diff: HashSet<&Formula> = p_left
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if left_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Left branch adds more than one new Assumption on {}",
                            p_left.claim
                        ),
                        format!("While checking OrLeft on {}", self.claim),
                    ]);
                }
                let right_diff: HashSet<&Formula> = p_right
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if right_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Right branch adds more than one new Assumption on {}",
                            p_right.claim
                        ),
                        format!("While checking OrLeft on {}", self.claim),
                    ]);
                }
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::Or(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        left_diff.iter().all(|x| *x == a) && right_diff.iter().all(|x| *x == b)
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "Sub-proofs do not match the disjuncts of any disjunction in previous assumptions on {} and {}",
                            p_left.claim, p_right.claim
                        ),
                        format!("While checking OrLeft on {}", self.claim),
                    ]);
                }
                if !p_left.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Left branch adds new Conclusion on {}", p_left.claim),
                        format!("While checking OrLeft on {}", self.claim),
                    ]);
                }
                if !p_right.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Right branch adds new Conclusion on {}", p_right.claim),
                        format!("While checking OrLeft on {}", self.claim),
                    ]);
                }
                p_left.check().map_err(|mut e| {
                    e.push(format!(
                        "While checking left branch of OrLeft on {}",
                        self.claim
                    ));
                    e
                })?;
                p_right.check().map_err(|mut e| {
                    e.push(format!(
                        "While checking right branch of OrLeft on {}",
                        self.claim
                    ));
                    e
                })?;
                Ok(())
            }
            ProofStep::OrRight(p) => {
                let diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if diff.len() > 2 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than two new Conclusions on {}",
                            p.claim
                        ),
                        format!("While checking OrRight on {}", self.claim),
                    ]);
                }
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::Or(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        diff.iter().all(|x| *x == a || *x == b)
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "New Conclusions do not match the disjuncts of any disjunction in previous conclusions on {}",
                            p.claim
                        ),
                        format!("While checking OrRight on {}", self.claim),
                    ]);
                }
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Proof step adds new Assumption on {}", p.claim),
                        format!("While checking OrRight on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking OrRight on {}", self.claim));
                    e
                })
            }
            ProofStep::ImplLeft(p_left, p_right) => {
                let left_diff: HashSet<&Formula> = p_left
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if left_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Left branch adds more than one new Conclusion on {}",
                            p_left.claim
                        ),
                        format!("While checking ImplLeft on {}", self.claim),
                    ]);
                }
                let right_diff: HashSet<&Formula> = p_right
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if right_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Right branch adds more than one new Assumption on {}",
                            p_right.claim
                        ),
                        format!("While checking ImplLeft on {}", self.claim),
                    ]);
                }
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::Implication(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        left_diff.iter().all(|x| *x == a) && right_diff.iter().all(|x| *x == b)
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "Sub-proofs do not match an implication in previous assumptions on {} and {}",
                            p_left.claim, p_right.claim
                        ),
                        format!("While checking ImplLeft on {}", self.claim),
                    ]);
                }
                if !p_left.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Left branch adds new Assumption on {}", p_left.claim),
                        format!("While checking ImplLeft on {}", self.claim),
                    ]);
                }
                if !p_right.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Right branch adds new Conclusion on {}", p_right.claim),
                        format!("While checking ImplLeft on {}", self.claim),
                    ]);
                }
                p_left.check().map_err(|mut e| {
                    e.push(format!(
                        "While checking left branch of ImplLeft on {}",
                        self.claim
                    ));
                    e
                })?;
                p_right.check().map_err(|mut e| {
                    e.push(format!(
                        "While checking right branch of ImplLeft on {}",
                        self.claim
                    ));
                    e
                })?;
                Ok(())
            }
            ProofStep::ImplRight(p) => {
                let assum_diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if assum_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than one new Assumption on {}",
                            p.claim
                        ),
                        format!("While checking ImplRight on {}", self.claim),
                    ]);
                }
                let conc_diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if conc_diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than one new Conclusion on {}",
                            p.claim
                        ),
                        format!("While checking ImplRight on {}", self.claim),
                    ]);
                }
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::Implication(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        assum_diff.iter().all(|x| *x == a) && conc_diff.iter().all(|x| *x == b)
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "Sub-proof does not match an implication in previous conclusions on {}",
                            p.claim
                        ),
                        format!("While checking ImplRight on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking ImplRight on {}", self.claim));
                    e
                })
            }
            ProofStep::ForAllLeft(p) => {
                let diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than one new Assumption on {}",
                            p.claim
                        ),
                        format!("While checking ForAllLeft on {}", self.claim),
                    ]);
                }
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::All(_, body) = g {
                        diff.iter().all(|f| f.is_instance_of(body, 0).is_some())
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "No ∀ in previous assumptions matches the sub-proof on {}",
                            p.claim
                        ),
                        format!("While checking ForAllLeft on {}", self.claim),
                    ]);
                }
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Proof step adds new Conclusion on {}", p.claim),
                        format!("While checking ForAllLeft on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking ForAllLeft on {}", self.claim));
                    e
                })
            }
            ProofStep::ForAllRight(p) => {
                let diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than one new Conclusion on {}",
                            p.claim
                        ),
                        format!("While checking ForAllRight on {}", self.claim),
                    ]);
                }
                let self_free = self.claim.free_vars();
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::All(_, body) = g {
                        diff.iter().all(|f| match f.is_instance_of(body, 0) {
                            None => false,
                            Some(sub) if sub.bindings.is_empty() => true,
                            Some(sub) => match sub.lookup(0) {
                                Some(Expr::Free(y)) => !self_free.contains(y),
                                _ => false,
                            },
                        })
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "No ∀ in previous conclusions matches the sub-proof with a fresh eigenvariable on {}",
                            p.claim
                        ),
                        format!("While checking ForAllRight on {}", self.claim),
                    ]);
                }
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Proof step adds new Assumption on {}", p.claim),
                        format!("While checking ForAllRight on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking ForAllRight on {}", self.claim));
                    e
                })
            }
            ProofStep::ExistsLeft(p) => {
                let diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than one new Assumption on {}",
                            p.claim
                        ),
                        format!("While checking ExistsLeft on {}", self.claim),
                    ]);
                }
                let self_free = self.claim.free_vars();
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::Exists(_, body) = g {
                        diff.iter().all(|f| match f.is_instance_of(body, 0) {
                            None => false,
                            Some(sub) if sub.bindings.is_empty() => true,
                            Some(sub) => match sub.lookup(0) {
                                Some(Expr::Free(y)) => !self_free.contains(y),
                                _ => false,
                            },
                        })
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "No ∃ in previous assumptions matches the sub-proof with a fresh eigenvariable on {}",
                            p.claim
                        ),
                        format!("While checking ExistsLeft on {}", self.claim),
                    ]);
                }
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Proof step adds new Conclusion on {}", p.claim),
                        format!("While checking ExistsLeft on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking ExistsLeft on {}", self.claim));
                    e
                })
            }
            ProofStep::ExistsRight(p) => {
                let diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if diff.len() > 1 {
                    return Err(vec![
                        format!(
                            "Proof step adds more than one new Conclusion on {}",
                            p.claim
                        ),
                        format!("While checking ExistsRight on {}", self.claim),
                    ]);
                }
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::Exists(_, body) = g {
                        diff.iter().all(|f| f.is_instance_of(body, 0).is_some())
                    } else {
                        false
                    }
                });
                if !ok {
                    return Err(vec![
                        format!(
                            "No ∃ in previous conclusions matches the sub-proof on {}",
                            p.claim
                        ),
                        format!("While checking ExistsRight on {}", self.claim),
                    ]);
                }
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Proof step adds new Assumption on {}", p.claim),
                        format!("While checking ExistsRight on {}", self.claim),
                    ]);
                }
                p.check().map_err(|mut e| {
                    e.push(format!("While checking ExistsRight on {}", self.claim));
                    e
                })
            }
        }
    }

    /// Validate the proof and, on success, return an equivalent proof in which
    /// each sequent has been pruned to the minimum assumptions and conclusions
    /// needed at that step. Returns `None` if any rule application is invalid.
    pub fn strip(&self) -> Option<Proof> {
        match &self.proof {
            ProofStep::Axiom => {
                let f = self
                    .claim
                    .assumptions
                    .intersection(&self.claim.conclusions)
                    .next()?
                    .clone();
                Some(Proof {
                    claim: Sequent {
                        assumptions: crate::hash_set! {f.clone()},
                        conclusions: crate::hash_set! {f},
                    },
                    proof: ProofStep::Axiom,
                })
            }
            ProofStep::BotLeft => {
                if !self.claim.assumptions.contains(&Formula::Bot) {
                    return None;
                }
                Some(Proof {
                    claim: Sequent {
                        assumptions: crate::hash_set! {Formula::Bot},
                        conclusions: HashSet::new(),
                    },
                    proof: ProofStep::BotLeft,
                })
            }
            ProofStep::NegLeft(p) => {
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                let mut conc_diff = p.claim.conclusions.difference(&self.claim.conclusions);
                let g = conc_diff.next()?.clone();
                if conc_diff.next().is_some() {
                    return None;
                }
                if !self.claim.assumptions.contains(&g.neg()) {
                    return None;
                }
                let p_s = p.strip()?;
                let mut assms = p_s.claim.assumptions.clone();
                assms.insert(g.neg());
                let mut concs = p_s.claim.conclusions.clone();
                concs.remove(&g);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                    },
                    proof: ProofStep::NegLeft(Box::new(p_s)),
                })
            }
            ProofStep::NegRight(p) => {
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                let mut assum_diff = p.claim.assumptions.difference(&self.claim.assumptions);
                let g = assum_diff.next()?.clone();
                if assum_diff.next().is_some() {
                    return None;
                }
                if !self.claim.conclusions.contains(&g.neg()) {
                    return None;
                }
                let p_s = p.strip()?;
                let mut assms = p_s.claim.assumptions.clone();
                assms.remove(&g);
                let mut concs = p_s.claim.conclusions.clone();
                concs.insert(g.neg());
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                    },
                    proof: ProofStep::NegRight(Box::new(p_s)),
                })
            }
            ProofStep::AndLeft(p) => {
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                let diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if diff.len() > 2 {
                    return None;
                }
                let principal = self.claim.assumptions.iter().find_map(|g| match g {
                    Formula::And(a, b)
                        if diff.iter().all(|x| *x == a.as_ref() || *x == b.as_ref()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let (la, lb) = match &principal {
                    Formula::And(a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => unreachable!(),
                };
                let p_s = p.strip()?;
                let mut assms = p_s.claim.assumptions.clone();
                assms.remove(&la);
                assms.remove(&lb);
                assms.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: p_s.claim.conclusions.clone(),
                    },
                    proof: ProofStep::AndLeft(Box::new(p_s)),
                })
            }
            ProofStep::AndRight(p_l, p_r) => {
                if !p_l.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                if !p_r.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                let left_diff: HashSet<&Formula> = p_l
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if left_diff.len() > 1 {
                    return None;
                }
                let right_diff: HashSet<&Formula> = p_r
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if right_diff.len() > 1 {
                    return None;
                }
                let principal = self.claim.conclusions.iter().find_map(|g| match g {
                    Formula::And(a, b)
                        if left_diff.iter().all(|x| *x == a.as_ref())
                            && right_diff.iter().all(|x| *x == b.as_ref()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let (la, lb) = match &principal {
                    Formula::And(a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => unreachable!(),
                };
                let l_s = p_l.strip()?;
                let r_s = p_r.strip()?;
                let assms = &l_s.claim.assumptions | &r_s.claim.assumptions;
                let concs = &(&(&l_s.claim.conclusions - &crate::hash_set! {la})
                    | &(&r_s.claim.conclusions - &crate::hash_set! {lb}))
                    | &crate::hash_set! {principal};
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                    },
                    proof: ProofStep::AndRight(Box::new(l_s), Box::new(r_s)),
                })
            }
            ProofStep::OrLeft(p_l, p_r) => {
                if !p_l.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                if !p_r.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                let left_diff: HashSet<&Formula> = p_l
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if left_diff.len() > 1 {
                    return None;
                }
                let right_diff: HashSet<&Formula> = p_r
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if right_diff.len() > 1 {
                    return None;
                }
                let principal = self.claim.assumptions.iter().find_map(|g| match g {
                    Formula::Or(a, b)
                        if left_diff.iter().all(|x| *x == a.as_ref())
                            && right_diff.iter().all(|x| *x == b.as_ref()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let (la, lb) = match &principal {
                    Formula::Or(a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => unreachable!(),
                };
                let l_s = p_l.strip()?;
                let r_s = p_r.strip()?;
                let assms = &(&(&l_s.claim.assumptions - &crate::hash_set! {la})
                    | &(&r_s.claim.assumptions - &crate::hash_set! {lb}))
                    | &crate::hash_set! {principal};
                let concs = &l_s.claim.conclusions | &r_s.claim.conclusions;
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                    },
                    proof: ProofStep::OrLeft(Box::new(l_s), Box::new(r_s)),
                })
            }
            ProofStep::OrRight(p) => {
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                let diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if diff.len() > 2 {
                    return None;
                }
                let principal = self.claim.conclusions.iter().find_map(|g| match g {
                    Formula::Or(a, b)
                        if diff.iter().all(|x| *x == a.as_ref() || *x == b.as_ref()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let (la, lb) = match &principal {
                    Formula::Or(a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => unreachable!(),
                };
                let p_s = p.strip()?;
                let mut concs = p_s.claim.conclusions.clone();
                concs.remove(&la);
                concs.remove(&lb);
                concs.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: p_s.claim.assumptions.clone(),
                        conclusions: concs,
                    },
                    proof: ProofStep::OrRight(Box::new(p_s)),
                })
            }
            ProofStep::ImplLeft(p_l, p_r) => {
                if !p_l.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                if !p_r.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                let left_diff: HashSet<&Formula> = p_l
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if left_diff.len() > 1 {
                    return None;
                }
                let right_diff: HashSet<&Formula> = p_r
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if right_diff.len() > 1 {
                    return None;
                }
                let principal = self.claim.assumptions.iter().find_map(|g| match g {
                    Formula::Implication(a, b)
                        if left_diff.iter().all(|x| *x == a.as_ref())
                            && right_diff.iter().all(|x| *x == b.as_ref()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let (la, lb) = match &principal {
                    Formula::Implication(a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => unreachable!(),
                };
                let l_s = p_l.strip()?;
                let r_s = p_r.strip()?;
                let assms = &(&l_s.claim.assumptions
                    | &(&r_s.claim.assumptions - &crate::hash_set! {lb}))
                    | &crate::hash_set! {principal};
                let concs =
                    &(&l_s.claim.conclusions - &crate::hash_set! {la}) | &r_s.claim.conclusions;
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                    },
                    proof: ProofStep::ImplLeft(Box::new(l_s), Box::new(r_s)),
                })
            }
            ProofStep::ImplRight(p) => {
                let assum_diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if assum_diff.len() > 1 {
                    return None;
                }
                let conc_diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if conc_diff.len() > 1 {
                    return None;
                }
                let principal = self.claim.conclusions.iter().find_map(|g| match g {
                    Formula::Implication(a, b)
                        if assum_diff.iter().all(|x| *x == a.as_ref())
                            && conc_diff.iter().all(|x| *x == b.as_ref()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let (la, lb) = match &principal {
                    Formula::Implication(a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => unreachable!(),
                };
                let p_s = p.strip()?;
                let mut assms = p_s.claim.assumptions.clone();
                assms.remove(&la);
                let mut concs = p_s.claim.conclusions.clone();
                concs.remove(&lb);
                concs.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                    },
                    proof: ProofStep::ImplRight(Box::new(p_s)),
                })
            }
            ProofStep::ForAllLeft(p) => {
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                let diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if diff.len() > 1 {
                    return None;
                }
                let principal = self.claim.assumptions.iter().find_map(|g| match g {
                    Formula::All(_, body)
                        if diff.iter().all(|f| f.is_instance_of(body, 0).is_some()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let added = diff.iter().next().map(|f| (*f).clone());
                let p_s = p.strip()?;
                // If the instance wasn't actually used by the stripped subproof,
                // the ∀L application was wasteful — skip it.
                let useful = added
                    .as_ref()
                    .map_or(false, |x| p_s.claim.assumptions.contains(x));
                if !useful {
                    return Some(p_s);
                }
                let mut assms = p_s.claim.assumptions.clone();
                if let Some(x) = &added {
                    assms.remove(x);
                }
                assms.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: p_s.claim.conclusions.clone(),
                    },
                    proof: ProofStep::ForAllLeft(Box::new(p_s)),
                })
            }
            ProofStep::ForAllRight(p) => {
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                let diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if diff.len() > 1 {
                    return None;
                }
                let self_free = self.claim.free_vars();
                let principal = self.claim.conclusions.iter().find_map(|g| match g {
                    Formula::All(_, body) => {
                        let ok = diff.iter().all(|f| match f.is_instance_of(body, 0) {
                            None => false,
                            Some(sub) if sub.bindings.is_empty() => true,
                            Some(sub) => match sub.lookup(0) {
                                Some(Expr::Free(y)) => !self_free.contains(y),
                                _ => false,
                            },
                        });
                        if ok { Some(g.clone()) } else { None }
                    }
                    _ => None,
                })?;
                let added = diff.iter().next().map(|f| (*f).clone());
                let p_s = p.strip()?;
                let mut concs = p_s.claim.conclusions.clone();
                if let Some(x) = &added {
                    concs.remove(x);
                }
                concs.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: p_s.claim.assumptions.clone(),
                        conclusions: concs,
                    },
                    proof: ProofStep::ForAllRight(Box::new(p_s)),
                })
            }
            ProofStep::ExistsLeft(p) => {
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return None;
                }
                let diff: HashSet<&Formula> = p
                    .claim
                    .assumptions
                    .difference(&self.claim.assumptions)
                    .collect();
                if diff.len() > 1 {
                    return None;
                }
                let self_free = self.claim.free_vars();
                let principal = self.claim.assumptions.iter().find_map(|g| match g {
                    Formula::Exists(_, body) => {
                        let ok = diff.iter().all(|f| match f.is_instance_of(body, 0) {
                            None => false,
                            Some(sub) if sub.bindings.is_empty() => true,
                            Some(sub) => match sub.lookup(0) {
                                Some(Expr::Free(y)) => !self_free.contains(y),
                                _ => false,
                            },
                        });
                        if ok { Some(g.clone()) } else { None }
                    }
                    _ => None,
                })?;
                let added = diff.iter().next().map(|f| (*f).clone());
                let p_s = p.strip()?;
                let mut assms = p_s.claim.assumptions.clone();
                if let Some(x) = &added {
                    assms.remove(x);
                }
                assms.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: p_s.claim.conclusions.clone(),
                    },
                    proof: ProofStep::ExistsLeft(Box::new(p_s)),
                })
            }
            ProofStep::ExistsRight(p) => {
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return None;
                }
                let diff: HashSet<&Formula> = p
                    .claim
                    .conclusions
                    .difference(&self.claim.conclusions)
                    .collect();
                if diff.len() > 1 {
                    return None;
                }
                let principal = self.claim.conclusions.iter().find_map(|g| match g {
                    Formula::Exists(_, body)
                        if diff.iter().all(|f| f.is_instance_of(body, 0).is_some()) =>
                    {
                        Some(g.clone())
                    }
                    _ => None,
                })?;
                let added = diff.iter().next().map(|f| (*f).clone());
                let p_s = p.strip()?;
                // If the instance wasn't actually used by the stripped subproof,
                // the ∃R application was wasteful — skip it.
                let useful = added
                    .as_ref()
                    .map_or(false, |x| p_s.claim.conclusions.contains(x));
                if !useful {
                    return Some(p_s);
                }
                let mut concs = p_s.claim.conclusions.clone();
                if let Some(x) = &added {
                    concs.remove(x);
                }
                concs.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: p_s.claim.assumptions.clone(),
                        conclusions: concs,
                    },
                    proof: ProofStep::ExistsRight(Box::new(p_s)),
                })
            }
        }
    }
}
