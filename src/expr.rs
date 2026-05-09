use std::fmt;
use std::collections::HashSet;

use crate::substitution::Substitution;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Expr {
    Bound(usize),
    Free(String),
    Func(String, Vec<Expr>),
}

impl Expr {
    pub fn free_vars(&self) -> Vec<String> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars);
        vars.into_iter().collect()
    }

    pub fn collect_free_vars(&self, vars: &mut HashSet<String>) {
        match self {
            Expr::Free(name) => {
                vars.insert(name.clone());
            }
            Expr::Bound(_) => {}
            Expr::Func(_, args) => {
                for a in args {
                    a.collect_free_vars(vars);
                }
            }
        }
    }

    pub fn occurs_free(&self, var: &str) -> bool {
        match self {
            Expr::Free(name) => name == var,
            Expr::Bound(_) => false,
            Expr::Func(_, args) => args.iter().any(|a| a.occurs_free(var)),
        }
    }

    pub fn lift(&self, min: usize) -> Expr {
        match self {
            Expr::Bound(idx) => Expr::Bound(if *idx >= min { *idx + 1} else {*idx}),
            Expr::Free(name) => Expr::Free(name.clone()),
            Expr::Func(name, args) => {
                Expr::Func(name.clone(), args.iter().map(|a| a.lift(min)).collect())
            }
        }
    }

    pub fn lower(&self, min: usize) -> Expr {
        match self {
            Expr::Bound(idx) => {
                if *idx > min {
                    Expr::Bound(*idx - 1)
                } else {
                    Expr::Bound(*idx)
                }
            }
            Expr::Free(name) => Expr::Free(name.clone()),
            Expr::Func(name, args) => {
                Expr::Func(name.clone(), args.iter().map(|a| a.lower(min)).collect())
            }
        }
    }

    /// True iff this expression contains any `Bound(_)` index (i.e. is not
    /// closed with respect to outer binders).
    pub fn has_any_bound(&self) -> bool {
        match self {
            Expr::Bound(_) => true,
            Expr::Free(_) => false,
            Expr::Func(_, args) => args.iter().any(|a| a.has_any_bound()),
        }
    }

    /// Checks whether `self` is an instance of `template` at de Bruijn depth
    /// `depth`. See `Formula::is_instance_of`. The witness must be closed
    /// (no `Bound` indices). Returns the substitution `{0 -> witness}` (or
    /// the empty substitution if no occurrence of the hole was needed), or
    /// `None` if there is no instance.
    pub fn is_instance_of(
        &self,
        template: &Expr,
        depth: usize,
    ) -> Option<Substitution> {
        match (template, self) {
            // The hole at the current depth: self is the witness candidate.
            (Expr::Bound(idx), _) if *idx == depth => {
                if self.has_any_bound() {
                    None
                } else {
                    Some(Substitution::singleton(0, self.clone()))
                }
            }
            // Non-hole bound: lower-by-1 if it pointed past the hole, else unchanged.
            (Expr::Bound(a_idx), Expr::Bound(b_idx)) => {
                let expected = if *a_idx > depth { a_idx - 1 } else { *a_idx };
                (expected == *b_idx).then(Substitution::new)
            }
            (Expr::Free(n1), Expr::Free(n2)) if n1 == n2 => Some(Substitution::new()),
            (Expr::Func(n1, a1), Expr::Func(n2, a2))
                if n1 == n2 && a1.len() == a2.len() =>
            {
                a1.iter().zip(a2.iter()).try_fold(Substitution::new(), |acc, (x, y)| {
                    acc.merge(&y.is_instance_of(x, depth)?)
                })
            }
            _ => None,
        }
    }

    pub fn fmt_with(&self, f: &mut fmt::Formatter<'_>, bound_names : &Vec<&str>) -> fmt::Result {
        match self {
            Expr::Bound(idx) => {
                // return error if out of bounds
                if *idx >= bound_names.len() {
                    return Err(fmt::Error);
                }
                write!(f, "{}", bound_names[bound_names.len() - 1 - idx])
            }
            Expr::Free(name) => write!(f, "{}", name),
            Expr::Func(name, args) => {
                write!(f, "{}(", name)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    a.fmt_with(f, bound_names)?;
                }
                write!(f, ")")
            }
        }
    }

}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bound(idx) => write!(f, "${}", idx),
            Expr::Free(name) => write!(f, "{}", name),
            Expr::Func(name, args) => {
                write!(f, "{}(", name)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", a)?;
                }
                write!(f, ")")
            }
        }
    }
}
