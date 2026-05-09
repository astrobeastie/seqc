use std::collections::HashSet;

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
                        format!("Proof step adds more than two new Assumptions on {}", p.claim),
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
                        format!("Left branch adds more than one new Conclusion on {}", p_left.claim),
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
                        format!("Right branch adds more than one new Conclusion on {}", p_right.claim),
                        format!("While checking AndRight on {}", self.claim),
                    ]);
                }
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::And(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        left_diff.iter().all(|x| *x == a)
                            && right_diff.iter().all(|x| *x == b)
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
                    e.push(format!("While checking left branch of AndRight on {}", self.claim));
                    e
                })?;
                p_right.check().map_err(|mut e| {
                    e.push(format!("While checking right branch of AndRight on {}", self.claim));
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
                        format!("Left branch adds more than one new Assumption on {}", p_left.claim),
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
                        format!("Right branch adds more than one new Assumption on {}", p_right.claim),
                        format!("While checking OrLeft on {}", self.claim),
                    ]);
                }
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::Or(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        left_diff.iter().all(|x| *x == a)
                            && right_diff.iter().all(|x| *x == b)
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
                    e.push(format!("While checking left branch of OrLeft on {}", self.claim));
                    e
                })?;
                p_right.check().map_err(|mut e| {
                    e.push(format!("While checking right branch of OrLeft on {}", self.claim));
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
                        format!("Proof step adds more than two new Conclusions on {}", p.claim),
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
                        format!("Left branch adds more than one new Conclusion on {}", p_left.claim),
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
                        format!("Right branch adds more than one new Assumption on {}", p_right.claim),
                        format!("While checking ImplLeft on {}", self.claim),
                    ]);
                }
                let ok = self.claim.assumptions.iter().any(|g| {
                    if let Formula::Implication(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        left_diff.iter().all(|x| *x == a)
                            && right_diff.iter().all(|x| *x == b)
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
                    e.push(format!("While checking left branch of ImplLeft on {}", self.claim));
                    e
                })?;
                p_right.check().map_err(|mut e| {
                    e.push(format!("While checking right branch of ImplLeft on {}", self.claim));
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
                        format!("Proof step adds more than one new Assumption on {}", p.claim),
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
                        format!("Proof step adds more than one new Conclusion on {}", p.claim),
                        format!("While checking ImplRight on {}", self.claim),
                    ]);
                }
                let ok = self.claim.conclusions.iter().any(|g| {
                    if let Formula::Implication(a, b) = g {
                        let a = a.as_ref();
                        let b = b.as_ref();
                        assum_diff.iter().all(|x| *x == a)
                            && conc_diff.iter().all(|x| *x == b)
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
                        format!("Proof step adds more than one new Assumption on {}", p.claim),
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
                        format!("Proof step adds more than one new Conclusion on {}", p.claim),
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
                        format!("Proof step adds more than one new Assumption on {}", p.claim),
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
                        format!("Proof step adds more than one new Conclusion on {}", p.claim),
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
}
