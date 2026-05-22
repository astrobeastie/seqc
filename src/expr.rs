use std::collections::HashSet;
use std::fmt;

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
            Expr::Bound(idx) => Expr::Bound(if *idx >= min { *idx + 1 } else { *idx }),
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

    pub fn mentions_bound(&self, idx: usize) -> bool {
        match self {
            Expr::Bound(n) => *n == idx,
            Expr::Free(_) => false,
            Expr::Func(_, args) => args.iter().any(|a| a.mentions_bound(idx)),
        }
    }

    /// Checks whether `self` is an instance of `template` at de Bruijn depth
    /// `depth`. See `Formula::is_instance_of`. The witness must be closed
    /// (no `Bound` indices). Returns the substitution `{0 -> witness}` (or
    /// the empty substitution if no occurrence of the hole was needed), or
    /// `None` if there is no instance.
    pub fn is_instance_of(&self, template: &Expr, depth: usize) -> Option<Substitution> {
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
            (Expr::Func(n1, a1), Expr::Func(n2, a2)) if n1 == n2 && a1.len() == a2.len() => a1
                .iter()
                .zip(a2.iter())
                .try_fold(Substitution::new(), |acc, (x, y)| {
                    acc.merge(&y.is_instance_of(x, depth)?)
                }),
            _ => None,
        }
    }

    pub fn fmt_with(&self, f: &mut fmt::Formatter<'_>, bound_names: &Vec<&str>) -> fmt::Result {
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

    pub fn collect_constants(&self, symbols: &mut HashSet<(String, usize)>) {
        match self {
            Expr::Bound(_) => {}
            Expr::Free(x) => {
                symbols.insert((x.clone(), 0));
            }
            Expr::Func(name, args) => {
                symbols.insert((name.clone(), args.len()));
                for a in args {
                    a.collect_constants(symbols);
                }
            }
        }
    }

    pub fn collect_closed_subterms(&self, terms: &mut HashSet<Expr>) {
        match self {
            Expr::Bound(_) => {}
            Expr::Free(_) => {
                terms.insert(self.clone());
            }
            Expr::Func(_, args) => {
                if !self.has_any_bound() {
                    terms.insert(self.clone());
                }
                for a in args {
                    a.collect_closed_subterms(terms);
                }
            }
        }
    }

    pub fn size(&self) -> usize {
        match self {
            Expr::Bound(_) | Expr::Free(_) => 1,
            Expr::Func(_, args) => 1 + args.iter().map(|a| a.size()).sum::<usize>(),
        }
    }
}

/// Enumerates closed expressions over a fixed signature in order of
/// increasing size (number of nodes). Each `(name, 0)` symbol yields a
/// `Free(name)` of size 1; each `(name, k)` with k ≥ 1 yields `Func(name, args)`
/// where args are smaller expressions whose sizes sum to `size - 1`.
pub struct ExprEnumerator {
    symbols: Vec<(String, usize)>,
    by_size: Vec<Vec<Expr>>, // by_size[i] = all exprs of size i + 1
    has_compound: bool,
    cur_outer: usize,
    cur_inner: usize,
}

impl ExprEnumerator {
    pub fn new(symbols: HashSet<(String, usize)>) -> Self {
        let mut symbols: Vec<_> = symbols.into_iter().collect();
        symbols.sort();
        let has_compound = symbols.iter().any(|(_, k)| *k >= 1);
        Self {
            symbols,
            by_size: Vec::new(),
            has_compound,
            cur_outer: 0,
            cur_inner: 0,
        }
    }

    fn ensure_size(&mut self, size_idx: usize) {
        while self.by_size.len() <= size_idx {
            let next_size = self.by_size.len() + 1;
            let exprs = Self::build_size(&self.symbols, &self.by_size, next_size);
            self.by_size.push(exprs);
        }
    }

    fn build_size(symbols: &[(String, usize)], by_size: &[Vec<Expr>], size: usize) -> Vec<Expr> {
        let mut out = Vec::new();
        if size == 1 {
            for (name, arity) in symbols {
                if *arity == 0 {
                    out.push(Expr::Free(name.clone()));
                }
            }
            return out;
        }
        for (name, arity) in symbols {
            if *arity == 0 || *arity > size - 1 {
                continue;
            }
            for comp in compositions(size - 1, *arity) {
                let pools: Vec<&Vec<Expr>> = comp.iter().map(|&s| &by_size[s - 1]).collect();
                for args in cartesian(&pools) {
                    out.push(Expr::Func(name.clone(), args));
                }
            }
        }
        out
    }
}

impl Iterator for ExprEnumerator {
    type Item = Expr;
    fn next(&mut self) -> Option<Expr> {
        loop {
            self.ensure_size(self.cur_outer);
            if self.cur_inner < self.by_size[self.cur_outer].len() {
                let e = self.by_size[self.cur_outer][self.cur_inner].clone();
                self.cur_inner += 1;
                return Some(e);
            }
            // Exhausted size cur_outer + 1.
            if self.cur_outer == 0 && self.by_size[0].is_empty() {
                // No base case → no closed expressions exist at all.
                return None;
            }
            if !self.has_compound {
                // Only 0-ary symbols → nothing past size 1.
                return None;
            }
            self.cur_outer += 1;
            self.cur_inner = 0;
        }
    }
}

/// All k-tuples of positive integers summing to n.
fn compositions(n: usize, k: usize) -> Vec<Vec<usize>> {
    if k == 0 {
        return if n == 0 { vec![vec![]] } else { vec![] };
    }
    if k == 1 {
        return if n >= 1 { vec![vec![n]] } else { vec![] };
    }
    let mut out = Vec::new();
    let max_first = n.saturating_sub(k - 1);
    for first in 1..=max_first {
        for rest in compositions(n - first, k - 1) {
            let mut comp = Vec::with_capacity(k);
            comp.push(first);
            comp.extend(rest);
            out.push(comp);
        }
    }
    out
}

fn cartesian(pools: &[&Vec<Expr>]) -> Vec<Vec<Expr>> {
    let mut result = vec![vec![]];
    for pool in pools {
        let mut next = Vec::with_capacity(result.len() * pool.len());
        for r in &result {
            for item in pool.iter() {
                let mut new_r = r.clone();
                new_r.push(item.clone());
                next.push(new_r);
            }
        }
        result = next;
    }
    result
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

#[cfg(test)]
mod tests {
    use super::*;

    fn syms(items: &[(&str, usize)]) -> HashSet<(String, usize)> {
        items.iter().map(|(n, k)| (n.to_string(), *k)).collect()
    }

    #[test]
    fn enumerator_only_constants() {
        let it = ExprEnumerator::new(syms(&[("a", 0), ("b", 0)]));
        let got: Vec<String> = it.map(|e| e.to_string()).collect();
        assert_eq!(got, vec!["a", "b"]);
    }

    #[test]
    fn enumerator_no_base_case_is_empty() {
        let it = ExprEnumerator::new(syms(&[("f", 1), ("g", 2)]));
        assert_eq!(it.count(), 0);
    }

    #[test]
    fn enumerator_unary_function_grows_linearly() {
        let it = ExprEnumerator::new(syms(&[("a", 0), ("f", 1)]));
        let got: Vec<String> = it.take(4).map(|e| e.to_string()).collect();
        assert_eq!(got, vec!["a", "f(a)", "f(f(a))", "f(f(f(a)))"]);
    }

    #[test]
    fn enumerator_size_ordering() {
        let it = ExprEnumerator::new(syms(&[("a", 0), ("b", 0), ("f", 2)]));
        // size 1: a, b
        // size 3: f(a,a), f(a,b), f(b,a), f(b,b)  (size-2 is empty since f is 2-ary needing 2 size-1 args = size 3)
        let got: Vec<String> = it.take(6).map(|e| e.to_string()).collect();
        assert_eq!(got[0..2], ["a", "b"]);
        assert!(got[2..].iter().all(|s| s.starts_with("f(")));
    }
}
