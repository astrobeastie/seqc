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
    /// Verify that names appearing in `child.eigenvars` were either already in
    /// scope at `self.claim` (i.e. mentioned in some formula or eigenvar) or
    /// belong to `allowed` (the fresh eigenvariable introduced by the current
    /// rule, if any). This is what enforces "no new constants show up in
    /// eigenvars except through ExistsLeft / ForAllRight, or by moving an
    /// implicitly named constant into eigenvars".
    fn check_eigenvars(
        &self,
        child: &Proof,
        allowed: Option<&str>,
        rule_name: &str,
    ) -> ProofCheckResult {
        let self_free = self.claim.free_vars();
        let bad: Vec<String> = child
            .claim
            .eigenvars
            .iter()
            .filter(|v| !self_free.contains(*v) && allowed != Some(v.as_str()))
            .cloned()
            .collect();
        if !bad.is_empty() {
            return Err(vec![
                format!(
                    "Sub-proof has eigenvariable(s) {:?} not in scope on {}",
                    bad, child.claim
                ),
                format!("While checking {} on {}", rule_name, self.claim),
            ]);
        }
        Ok(())
    }

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
                self.check_eigenvars(p, None, "NegLeft")?;
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
                self.check_eigenvars(p, None, "NegRight")?;
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
                self.check_eigenvars(p, None, "AndLeft")?;
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
                self.check_eigenvars(p_left, None, "AndRight")?;
                self.check_eigenvars(p_right, None, "AndRight")?;
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
                self.check_eigenvars(p_left, None, "OrLeft")?;
                self.check_eigenvars(p_right, None, "OrLeft")?;
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
                self.check_eigenvars(p, None, "OrRight")?;
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
                self.check_eigenvars(p_left, None, "ImplLeft")?;
                self.check_eigenvars(p_right, None, "ImplLeft")?;
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
                self.check_eigenvars(p, None, "ImplRight")?;
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
                if let Some(f) = diff.iter().next() {
                    let witness = self.claim.assumptions.iter().find_map(|g| match g {
                        Formula::All(_, body) => {
                            f.is_instance_of(body, 0).map(|s| s.lookup(0).cloned())
                        }
                        _ => None,
                    });
                    let Some(witness) = witness else {
                        return Err(vec![
                            format!(
                                "No ∀ in previous assumptions matches the sub-proof on {}",
                                p.claim
                            ),
                            format!("While checking ForAllLeft on {}", self.claim),
                        ]);
                    };
                    if let Some(w) = witness {
                        if !w
                            .constants_with_arity()
                            .is_subset(&self.claim.constants_with_arity())
                        {
                            return Err(vec![
                                format!("Witness {} uses constants not in scope on {}", w, p.claim),
                                format!("While checking ForAllLeft on {}", self.claim),
                            ]);
                        }
                    }
                }
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Proof step adds new Conclusion on {}", p.claim),
                        format!("While checking ForAllLeft on {}", self.claim),
                    ]);
                }
                self.check_eigenvars(p, None, "ForAllLeft")?;
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
                let p_free = p.claim.free_vars();
                let new_vars: Vec<&String> = p_free.difference(&self_free).collect();
                if new_vars.len() > 1 {
                    return Err(vec![
                        format!(
                            "Sub-proof introduces more than one new free variable on {}",
                            p.claim
                        ),
                        format!("While checking ForAllRight on {}", self.claim),
                    ]);
                }
                let new_eigenvar: Option<&String> = new_vars.into_iter().next();
                if let Some(f) = diff.iter().next() {
                    let ok = self.claim.conclusions.iter().any(|g| {
                        let Formula::All(_, body) = g else {
                            return false;
                        };
                        match f.is_instance_of(body, 0) {
                            None => false,
                            Some(sub) if sub.bindings.is_empty() => true,
                            Some(sub) => match (sub.lookup(0), new_eigenvar) {
                                (Some(Expr::Free(y)), Some(intro)) => y == intro,
                                _ => false,
                            },
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
                }
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Proof step adds new Assumption on {}", p.claim),
                        format!("While checking ForAllRight on {}", self.claim),
                    ]);
                }
                self.check_eigenvars(p, new_eigenvar.map(|s| s.as_str()), "ForAllRight")?;
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
                let p_free = p.claim.free_vars();
                let new_vars: Vec<&String> = p_free.difference(&self_free).collect();
                if new_vars.len() > 1 {
                    return Err(vec![
                        format!(
                            "Sub-proof introduces more than one new free variable on {}",
                            p.claim
                        ),
                        format!("While checking ExistsLeft on {}", self.claim),
                    ]);
                }
                let new_eigenvar: Option<&String> = new_vars.into_iter().next();
                if let Some(f) = diff.iter().next() {
                    let ok = self.claim.assumptions.iter().any(|g| {
                        let Formula::Exists(_, body) = g else {
                            return false;
                        };
                        match f.is_instance_of(body, 0) {
                            None => false,
                            Some(sub) if sub.bindings.is_empty() => true,
                            Some(sub) => match (sub.lookup(0), new_eigenvar) {
                                (Some(Expr::Free(y)), Some(intro)) => y == intro,
                                _ => false,
                            },
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
                }
                if !p.claim.conclusions.is_subset(&self.claim.conclusions) {
                    return Err(vec![
                        format!("Proof step adds new Conclusion on {}", p.claim),
                        format!("While checking ExistsLeft on {}", self.claim),
                    ]);
                }
                self.check_eigenvars(p, new_eigenvar.map(|s| s.as_str()), "ExistsLeft")?;
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
                if let Some(f) = diff.iter().next() {
                    let witness = self.claim.conclusions.iter().find_map(|g| match g {
                        Formula::Exists(_, body) => {
                            f.is_instance_of(body, 0).map(|s| s.lookup(0).cloned())
                        }
                        _ => None,
                    });
                    let Some(witness) = witness else {
                        return Err(vec![
                            format!(
                                "No ∃ in previous conclusions matches the sub-proof on {}",
                                p.claim
                            ),
                            format!("While checking ExistsRight on {}", self.claim),
                        ]);
                    };
                    if let Some(w) = witness {
                        if !w
                            .constants_with_arity()
                            .is_subset(&self.claim.constants_with_arity())
                        {
                            return Err(vec![
                                format!("Witness {} uses constants not in scope on {}", w, p.claim),
                                format!("While checking ExistsRight on {}", self.claim),
                            ]);
                        }
                    }
                }
                if !p.claim.assumptions.is_subset(&self.claim.assumptions) {
                    return Err(vec![
                        format!("Proof step adds new Assumption on {}", p.claim),
                        format!("While checking ExistsRight on {}", self.claim),
                    ]);
                }
                self.check_eigenvars(p, None, "ExistsRight")?;
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
                        eigenvars: HashSet::new(),
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
                        eigenvars: HashSet::new(),
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
                if !p_s.claim.conclusions.contains(&g) {
                    return Some(p_s);
                }
                let mut assms = p_s.claim.assumptions.clone();
                assms.insert(g.neg());
                let mut concs = p_s.claim.conclusions.clone();
                concs.remove(&g);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                        eigenvars: p_s.claim.eigenvars.clone(),
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
                if !p_s.claim.assumptions.contains(&g) {
                    return Some(p_s);
                }
                let mut assms = p_s.claim.assumptions.clone();
                assms.remove(&g);
                let mut concs = p_s.claim.conclusions.clone();
                concs.insert(g.neg());
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                        eigenvars: p_s.claim.eigenvars.clone(),
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
                if !p_s.claim.assumptions.contains(&la) && !p_s.claim.assumptions.contains(&lb) {
                    return Some(p_s);
                }
                let mut assms = p_s.claim.assumptions.clone();
                assms.remove(&la);
                assms.remove(&lb);
                assms.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: p_s.claim.conclusions.clone(),
                        eigenvars: p_s.claim.eigenvars.clone(),
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
                if !l_s.claim.conclusions.contains(&la) && !r_s.claim.conclusions.contains(&lb) {
                    return Some(l_s);
                }
                let assms = &l_s.claim.assumptions | &r_s.claim.assumptions;
                let concs = &(&(&l_s.claim.conclusions - &crate::hash_set! {la})
                    | &(&r_s.claim.conclusions - &crate::hash_set! {lb}))
                    | &crate::hash_set! {principal};
                let eigenvars = &l_s.claim.eigenvars | &r_s.claim.eigenvars;
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                        eigenvars,
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
                if !l_s.claim.assumptions.contains(&la) && !r_s.claim.assumptions.contains(&lb) {
                    return Some(l_s);
                }
                let assms = &(&(&l_s.claim.assumptions - &crate::hash_set! {la})
                    | &(&r_s.claim.assumptions - &crate::hash_set! {lb}))
                    | &crate::hash_set! {principal};
                let concs = &l_s.claim.conclusions | &r_s.claim.conclusions;
                let eigenvars = &l_s.claim.eigenvars | &r_s.claim.eigenvars;
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                        eigenvars,
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
                if !p_s.claim.conclusions.contains(&la) && !p_s.claim.conclusions.contains(&lb) {
                    return Some(p_s);
                }
                let mut concs = p_s.claim.conclusions.clone();
                concs.remove(&la);
                concs.remove(&lb);
                concs.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: p_s.claim.assumptions.clone(),
                        conclusions: concs,
                        eigenvars: p_s.claim.eigenvars.clone(),
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
                if !l_s.claim.conclusions.contains(&la) && !r_s.claim.assumptions.contains(&lb) {
                    return Some(l_s);
                }
                let assms = &(&l_s.claim.assumptions
                    | &(&r_s.claim.assumptions - &crate::hash_set! {lb}))
                    | &crate::hash_set! {principal};
                let concs =
                    &(&l_s.claim.conclusions - &crate::hash_set! {la}) | &r_s.claim.conclusions;
                let eigenvars = &l_s.claim.eigenvars | &r_s.claim.eigenvars;
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                        eigenvars,
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
                if !p_s.claim.assumptions.contains(&la) && !p_s.claim.conclusions.contains(&lb) {
                    return Some(p_s);
                }
                let mut assms = p_s.claim.assumptions.clone();
                assms.remove(&la);
                let mut concs = p_s.claim.conclusions.clone();
                concs.remove(&lb);
                concs.insert(principal);
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: concs,
                        eigenvars: p_s.claim.eigenvars.clone(),
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
                let Formula::All(_, body) = &principal else {
                    return None;
                };
                let witness: Option<Expr> = added.as_ref().and_then(|inst| {
                    inst.is_instance_of(body, 0)
                        .and_then(|s| s.lookup(0).cloned())
                });
                if let Some(w) = &witness {
                    if !w
                        .constants_with_arity()
                        .is_subset(&self.claim.constants_with_arity())
                    {
                        return None;
                    }
                }
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
                let mut eigenvars = p_s.claim.eigenvars.clone();
                if let Some(w) = &witness {
                    let mut parent_free: HashSet<String> = HashSet::new();
                    for f in assms.iter().chain(p_s.claim.conclusions.iter()) {
                        f.collect_free_vars(&mut parent_free);
                    }
                    parent_free.extend(eigenvars.iter().cloned());
                    for v in w.free_vars() {
                        if !parent_free.contains(&v) {
                            eigenvars.insert(v);
                        }
                    }
                }
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: p_s.claim.conclusions.clone(),
                        eigenvars,
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
                let new_eigenvar = p
                    .claim
                    .eigenvars
                    .difference(&self.claim.eigenvars)
                    .next()
                    .cloned();
                let p_s = p.strip()?;
                let mut concs = p_s.claim.conclusions.clone();
                if let Some(x) = &added {
                    concs.remove(x);
                }
                concs.insert(principal);
                let mut eigenvars = p_s.claim.eigenvars.clone();
                if let Some(ev) = &new_eigenvar {
                    eigenvars.remove(ev);
                }
                Some(Proof {
                    claim: Sequent {
                        assumptions: p_s.claim.assumptions.clone(),
                        conclusions: concs,
                        eigenvars,
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
                let new_eigenvar = p
                    .claim
                    .eigenvars
                    .difference(&self.claim.eigenvars)
                    .next()
                    .cloned();
                let p_s = p.strip()?;
                let mut assms = p_s.claim.assumptions.clone();
                if let Some(x) = &added {
                    assms.remove(x);
                }
                assms.insert(principal);
                let mut eigenvars = p_s.claim.eigenvars.clone();
                if let Some(ev) = &new_eigenvar {
                    eigenvars.remove(ev);
                }
                Some(Proof {
                    claim: Sequent {
                        assumptions: assms,
                        conclusions: p_s.claim.conclusions.clone(),
                        eigenvars,
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
                let Formula::Exists(_, body) = &principal else {
                    return None;
                };
                let witness: Option<Expr> = added.as_ref().and_then(|inst| {
                    inst.is_instance_of(body, 0)
                        .and_then(|s| s.lookup(0).cloned())
                });
                if let Some(w) = &witness {
                    if !w
                        .constants_with_arity()
                        .is_subset(&self.claim.constants_with_arity())
                    {
                        return None;
                    }
                }
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
                let mut eigenvars = p_s.claim.eigenvars.clone();
                if let Some(w) = &witness {
                    let mut parent_free: HashSet<String> = HashSet::new();
                    for f in p_s.claim.assumptions.iter().chain(concs.iter()) {
                        f.collect_free_vars(&mut parent_free);
                    }
                    parent_free.extend(eigenvars.iter().cloned());
                    for v in w.free_vars() {
                        if !parent_free.contains(&v) {
                            eigenvars.insert(v);
                        }
                    }
                }
                Some(Proof {
                    claim: Sequent {
                        assumptions: p_s.claim.assumptions.clone(),
                        conclusions: concs,
                        eigenvars,
                    },
                    proof: ProofStep::ExistsRight(Box::new(p_s)),
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn parse_initial(input: &str) -> Sequent {
        if let Ok(s) = Parser::new(input.to_string()).and_then(|mut p| p.parse_sequent()) {
            return s;
        }
        let mut parser = Parser::new(input.to_string()).expect("parser init");
        let formula = parser.parse_formula().expect("parse_formula");
        let mut conclusions = HashSet::new();
        conclusions.insert(formula);
        Sequent {
            assumptions: HashSet::new(),
            conclusions,
            eigenvars: HashSet::new(),
        }
    }

    fn try_prove(input: &str) -> Option<Proof> {
        let sequent = parse_initial(input);
        let depth = (2 * sequent.size()).max(12);
        sequent.proof_search(depth)
    }

    fn parse_proof_str(input: &str) -> Result<Proof, Vec<String>> {
        Parser::new(input.to_string())?.parse_proof()
    }

    #[test]
    fn provable_round_trip() {
        let formulas = [
            "P -> P",
            "P, Q => P",
            "P & Q -> Q & P",
            "P | Q -> Q | P",
            "P -> ~~P",
            "~~P -> P",
            "P | ~P",
            "(P -> Q) -> (~Q -> ~P)",
            "P -> Q, Q -> R => P -> R",
            "P | Q, P -> R, Q -> R => R",
            "P(c) -> exists x. P(x)",
            "forall x. P(x) -> P(c)",
            "P(c), forall x. Q(x) => exists y. Q(y)",
            "exists y. forall x. p(x,y) -> forall x. exists y. p(x,y)",
            "forall x. p(x) & ~p(x) => forall x. 0",
            "~(forall x. p(x) -> exists x. p(x)) -> ~exists x. 1",
        ];
        for s in &formulas {
            let proof = try_prove(s).unwrap_or_else(|| panic!("no proof for: {}", s));
            proof
                .check()
                .unwrap_or_else(|e| panic!("raw proof failed check for {}: {:?}", s, e));
            let stripped = proof
                .strip()
                .unwrap_or_else(|| panic!("strip returned None for: {}", s));
            stripped
                .check()
                .unwrap_or_else(|e| panic!("stripped proof failed check for {}: {:?}", s, e));
        }
    }

    #[test]
    fn unprovable_formulas() {
        let formulas = [
            "=> P",
            "P => Q",
            "(P -> Q) -> (Q -> P)",
            "exists x. P(x) => forall x. P(x)",
            "(forall x. P(x) | Q(x)) -> (forall x. P(x)) | (forall x. Q(x))",
            "forall y. exists x. R(x, y) => exists x. forall y. R(x, y)",
        ];
        for s in &formulas {
            assert!(
                try_prove(s).is_none(),
                "unexpectedly found a proof for: {}",
                s
            );
        }
    }

    /// Run `check` and `strip` against every file under `proofs/valid/` and
    /// `proofs/bad/`. For each file `check` and `strip` must agree;
    /// `valid` files must additionally pass re-check after stripping.
    #[test]
    fn proofs_directory() {
        for (subdir, expect_valid) in [("valid", true), ("bad", false)] {
            let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("proofs")
                .join(subdir);
            let mut entries: Vec<_> = std::fs::read_dir(&dir)
                .unwrap_or_else(|e| panic!("read {}: {}", dir.display(), e))
                .map(|e| e.expect("dir entry").path())
                .collect();
            entries.sort();
            assert!(!entries.is_empty(), "proofs/{}/ is empty", subdir);
            for path in entries {
                let name = format!("{}/{}", subdir, path.file_name().unwrap().to_string_lossy());
                let contents = std::fs::read_to_string(&path)
                    .unwrap_or_else(|e| panic!("read {}: {}", name, e));
                let proof = parse_proof_str(&contents)
                    .unwrap_or_else(|e| panic!("parse failed for {}: {:?}", name, e));
                let check_ok = proof.check().is_ok();
                let strip_ok = proof.strip().is_some();
                assert_eq!(
                    check_ok, strip_ok,
                    "check ({}) and strip ({}) disagree on {}",
                    check_ok, strip_ok, name
                );
                if expect_valid {
                    assert!(check_ok, "expected {} to check successfully", name);
                    let stripped = proof.strip().expect("strip");
                    stripped
                        .check()
                        .unwrap_or_else(|e| panic!("stripped {} failed re-check: {:?}", name, e));
                } else {
                    assert!(!check_ok, "expected {} to fail check", name);
                }
            }
        }
    }
}
