//! Render `Expr`, `Formula`, `Sequent` and `Proof` as LaTeX (using the
//! `bussproofs` package) or as Typst (using the `curryst` package).
//!
//! The two backends share the formula / sequent rendering via a small
//! `Syntax` glyph table; the proof-tree structure differs (post-order for
//! bussproofs, pre-order nested calls for curryst).

use std::fmt::Write;

use crate::expr::Expr;
use crate::formula::{BinOp, Formula, PREC_NEG, PREC_QUANT, Sequent};
use crate::proof::Proof;

pub trait Latex {
    fn to_latex(&self) -> String;
}

pub trait Typst {
    fn to_typst(&self) -> String;
}

struct Syntax {
    bot: &'static str,
    top: &'static str,
    neg: &'static str,
    and: &'static str,
    or: &'static str,
    impl_: &'static str,
    forall: &'static str,
    exists: &'static str,
    sequent_arrow: &'static str,
    /// Render an identifier so that any `_`-separated tail becomes a
    /// proper subscript: `x_12` → `x_{12}` (LaTeX) / `x_(12)` (Typst);
    /// `x_1_2` → `x_{1,2}` / `x_(1,2)`.
    name: fn(&str) -> String,
}

const LATEX_SYN: Syntax = Syntax {
    bot: "\\bot",
    top: "\\top",
    neg: "\\neg ",
    and: " \\wedge ",
    or: " \\vee ",
    impl_: " \\to ",
    forall: "\\forall ",
    exists: "\\exists ",
    sequent_arrow: " \\Rightarrow ",
    name: latex_name,
};

const TYPST_SYN: Syntax = Syntax {
    bot: "bot",
    top: "top",
    neg: "not ",
    and: " and ",
    or: " or ",
    impl_: " -> ",
    forall: "forall ",
    exists: "exists ",
    sequent_arrow: " => ",
    name: typst_name,
};

fn split_subscript(name: &str) -> (&str, Vec<&str>) {
    let Some(idx) = name.find('_') else {
        return (name, Vec::new());
    };
    if idx == 0 {
        return (name, Vec::new());
    }
    let (base, rest) = name.split_at(idx);
    let parts: Vec<&str> = rest[1..].split('_').filter(|s| !s.is_empty()).collect();
    if parts.is_empty() {
        (name, Vec::new())
    } else {
        (base, parts)
    }
}

fn latex_name(name: &str) -> String {
    let (base, parts) = split_subscript(name);
    if parts.is_empty() {
        base.to_string()
    } else {
        format!("{}_{{{}}}", base, parts.join(","))
    }
}

fn typst_name(name: &str) -> String {
    let (base, parts) = split_subscript(name);
    if parts.is_empty() {
        base.to_string()
    } else {
        format!("{}_({})", base, parts.join(","))
    }
}

fn write_expr<'a>(out: &mut String, e: &'a Expr, bound: &[&'a str], syn: &Syntax) {
    match e {
        Expr::Bound(idx) => {
            let name = bound[bound.len() - 1 - idx];
            out.push_str(&(syn.name)(name));
        }
        Expr::Free(name) => out.push_str(&(syn.name)(name)),
        Expr::Func(name, args) => {
            out.push_str(&(syn.name)(name));
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_expr(out, a, bound, syn);
            }
            out.push(')');
        }
    }
}

fn write_formula<'a>(
    out: &mut String,
    f: &'a Formula,
    min: u8,
    bound: &mut Vec<&'a str>,
    syn: &Syntax,
) {
    let parens = f.prec() < min;
    if parens {
        out.push('(');
    }
    match f {
        Formula::Bot => out.push_str(syn.bot),
        Formula::Top => out.push_str(syn.top),
        Formula::Pred(name, args) => {
            out.push_str(&(syn.name)(name));
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write_expr(out, a, bound, syn);
                }
                out.push(')');
            }
        }
        Formula::Not(g) => {
            out.push_str(syn.neg);
            write_formula(out, g, PREC_NEG, bound, syn);
        }
        Formula::And(a, b) => write_binop(out, a, b, BinOp::And, syn.and, bound, syn),
        Formula::Or(a, b) => write_binop(out, a, b, BinOp::Or, syn.or, bound, syn),
        Formula::Implication(a, b) => {
            write_binop(out, a, b, BinOp::Implication, syn.impl_, bound, syn)
        }
        Formula::All(x, body) => {
            out.push_str(syn.forall);
            out.push_str(&(syn.name)(x));
            out.push_str(". ");
            bound.push(x.as_str());
            write_formula(out, body, PREC_QUANT, bound, syn);
            bound.pop();
        }
        Formula::Exists(x, body) => {
            out.push_str(syn.exists);
            out.push_str(&(syn.name)(x));
            out.push_str(". ");
            bound.push(x.as_str());
            write_formula(out, body, PREC_QUANT, bound, syn);
            bound.pop();
        }
    }
    if parens {
        out.push(')');
    }
}

fn write_binop<'a>(
    out: &mut String,
    l: &'a Formula,
    r: &'a Formula,
    op: BinOp,
    glyph: &str,
    bound: &mut Vec<&'a str>,
    syn: &Syntax,
) {
    let (lmin, rmin) = op.assoc().child_mins(op.prec());
    write_formula(out, l, lmin, bound, syn);
    out.push_str(glyph);
    write_formula(out, r, rmin, bound, syn);
}

fn write_sequent(out: &mut String, seq: &Sequent, syn: &Syntax) {
    if !seq.eigenvars.is_empty() {
        let mut vars: Vec<&str> = seq.eigenvars.iter().map(|s| s.as_str()).collect();
        vars.sort();
        let rendered: Vec<String> = vars.iter().map(|v| (syn.name)(v)).collect();
        out.push_str(&rendered.join(", "));
        out.push_str(" : ");
    }
    let mut bound: Vec<&str> = Vec::new();
    let mut parts: Vec<String> = Vec::with_capacity(seq.assumptions.len());
    for f in &seq.assumptions {
        let mut s = String::new();
        write_formula(&mut s, f, 0, &mut bound, syn);
        parts.push(s);
    }
    out.push_str(&parts.join(", "));
    out.push_str(syn.sequent_arrow);
    parts.clear();
    for f in &seq.conclusions {
        let mut s = String::new();
        write_formula(&mut s, f, 0, &mut bound, syn);
        parts.push(s);
    }
    out.push_str(&parts.join(", "));
}

impl Latex for Expr {
    fn to_latex(&self) -> String {
        let mut s = String::new();
        write_expr(&mut s, self, &[], &LATEX_SYN);
        s
    }
}

impl Typst for Expr {
    fn to_typst(&self) -> String {
        let mut s = String::new();
        write_expr(&mut s, self, &[], &TYPST_SYN);
        s
    }
}

impl Latex for Formula {
    fn to_latex(&self) -> String {
        let mut s = String::new();
        let mut bound: Vec<&str> = Vec::new();
        write_formula(&mut s, self, 0, &mut bound, &LATEX_SYN);
        s
    }
}

impl Typst for Formula {
    fn to_typst(&self) -> String {
        let mut s = String::new();
        let mut bound: Vec<&str> = Vec::new();
        write_formula(&mut s, self, 0, &mut bound, &TYPST_SYN);
        s
    }
}

impl Latex for Sequent {
    fn to_latex(&self) -> String {
        let mut s = String::new();
        write_sequent(&mut s, self, &LATEX_SYN);
        s
    }
}

impl Typst for Sequent {
    fn to_typst(&self) -> String {
        let mut s = String::new();
        write_sequent(&mut s, self, &TYPST_SYN);
        s
    }
}

impl Latex for Proof {
    fn to_latex(&self) -> String {
        let mut out = String::new();
        out.push_str("% requires \\usepackage{bussproofs}\n");
        out.push_str("\\begin{prooftree}\n");
        write_latex_node(&mut out, self, 1);
        out.push_str("\\end{prooftree}");
        out
    }
}

fn write_latex_node(out: &mut String, p: &Proof, indent: usize) {
    let pad = "  ".repeat(indent);
    let mut seq = String::new();
    write_sequent(&mut seq, &p.claim, &LATEX_SYN);
    let children = p.proof.children();
    if children.is_empty() {
        writeln!(out, "{}\\AxiomC{{}}", pad).unwrap();
    } else {
        for c in &children {
            write_latex_node(out, c, indent);
        }
    }
    writeln!(
        out,
        "{}\\RightLabel{{{}}}",
        pad,
        latex_rule_label(p.proof.keyword())
    )
    .unwrap();
    let inf = match children.len() {
        0 | 1 => "\\UnaryInfC",
        2 => "\\BinaryInfC",
        _ => unreachable!("proof step with unexpected child count"),
    };
    writeln!(out, "{}{}{{${}$}}", pad, inf, seq).unwrap();
}

fn latex_rule_label(kw: &str) -> &'static str {
    match kw {
        "axiom" => "$\\mathrm{Ax}$",
        "botL" => "$\\bot L$",
        "negL" => "$\\neg L$",
        "negR" => "$\\neg R$",
        "andL" => "$\\wedge L$",
        "andR" => "$\\wedge R$",
        "orL" => "$\\vee L$",
        "orR" => "$\\vee R$",
        "impL" => "$\\to L$",
        "impR" => "$\\to R$",
        "forallL" => "$\\forall L$",
        "forallR" => "$\\forall R$",
        "existsL" => "$\\exists L$",
        "existsR" => "$\\exists R$",
        _ => panic!("unknown rule keyword: {}", kw),
    }
}

fn typst_rule_label(kw: &str) -> &'static str {
    match kw {
        "axiom" => "$\"Ax\"$",
        "botL" => "$bot L$",
        "negL" => "$not L$",
        "negR" => "$not R$",
        "andL" => "$and L$",
        "andR" => "$and R$",
        "orL" => "$or L$",
        "orR" => "$or R$",
        "impL" => "$arrow.r L$",
        "impR" => "$arrow.r R$",
        "forallL" => "$forall L$",
        "forallR" => "$forall R$",
        "existsL" => "$exists L$",
        "existsR" => "$exists R$",
        _ => panic!("unknown rule keyword: {}", kw),
    }
}

impl Typst for Proof {
    fn to_typst(&self) -> String {
        let mut out = String::new();
        out.push_str("// requires #import \"@preview/curryst:0.5.1\": rule, prooftree\n");
        out.push_str("#prooftree(\n");
        write_typst_node(&mut out, self, 1);
        out.push_str("\n)");
        out
    }
}

fn write_typst_node(out: &mut String, p: &Proof, indent: usize) {
    let pad = "  ".repeat(indent);
    let mut seq = String::new();
    write_sequent(&mut seq, &p.claim, &TYPST_SYN);
    let label = typst_rule_label(p.proof.keyword());
    let children = p.proof.children();
    if children.is_empty() {
        write!(out, "{}rule(name: {}, ${}$)", pad, label, seq).unwrap();
    } else {
        writeln!(out, "{}rule(", pad).unwrap();
        let inner = "  ".repeat(indent + 1);
        writeln!(out, "{}name: {},", inner, label).unwrap();
        writeln!(out, "{}${}$,", inner, seq).unwrap();
        for (i, c) in children.iter().enumerate() {
            write_typst_node(out, c, indent + 1);
            if i + 1 < children.len() {
                writeln!(out, ",").unwrap();
            } else {
                writeln!(out).unwrap();
            }
        }
        write!(out, "{})", pad).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn parse(input: &str) -> Proof {
        Parser::new(input.to_string())
            .expect("parser init")
            .parse_proof()
            .expect("parse_proof")
    }

    #[test]
    fn latex_axiom() {
        let p = parse("P => P by axiom");
        let s = p.to_latex();
        assert!(s.contains("\\AxiomC{}"), "expected empty AxiomC in {}", s);
        assert!(
            s.contains("\\RightLabel{$\\mathrm{Ax}$}"),
            "expected Ax label in {}",
            s
        );
        assert!(s.contains("\\UnaryInfC"), "expected UnaryInfC in {}", s);
        assert!(
            s.contains("\\begin{prooftree}"),
            "expected begin/end in {}",
            s
        );
        assert!(s.contains("\\Rightarrow"), "expected \\Rightarrow in {}", s);
    }

    #[test]
    fn latex_unary_and_binary() {
        let p = parse("P, Q => P & Q by andR { P, Q => P by axiom, P, Q => Q by axiom }");
        let s = p.to_latex();
        assert!(s.contains("\\BinaryInfC"), "expected BinaryInfC in {}", s);
        assert!(
            s.contains("\\RightLabel{$\\wedge R$}"),
            "expected ∧R label in {}",
            s
        );
        assert!(s.contains("\\wedge"), "expected \\wedge in {}", s);
    }

    #[test]
    fn typst_axiom() {
        let p = parse("P => P by axiom");
        let s = p.to_typst();
        assert!(s.contains("#prooftree("), "expected #prooftree in {}", s);
        assert!(
            s.contains("rule(name: $\"Ax\"$"),
            "expected Ax rule in {}",
            s
        );
        assert!(s.contains("=>"), "expected => in {}", s);
    }

    #[test]
    fn typst_nested() {
        let p = parse("P, Q => P & Q by andR { P, Q => P by axiom, P, Q => Q by axiom }");
        let s = p.to_typst();
        assert!(s.contains("name: $and R$"), "expected ∧R rule in {}", s);
        assert!(
            s.matches("name: $\"Ax\"$").count() == 2,
            "expected two Ax rules in {}",
            s
        );
        assert!(s.contains(" and "), "expected ' and ' in {}", s);
    }

    #[test]
    fn subscript_names() {
        let p = parse("P(x_12), forall y_1_2. P(y_1_2) => P(x_12) by axiom");
        let l = p.to_latex();
        assert!(l.contains("x_{12}"), "expected x_{{12}} in {}", l);
        assert!(l.contains("y_{1,2}"), "expected y_{{1,2}} in {}", l);
        let t = p.to_typst();
        assert!(t.contains("x_(12)"), "expected x_(12) in {}", t);
        assert!(t.contains("y_(1,2)"), "expected y_(1,2) in {}", t);
    }

    #[test]
    fn sequent_eigenvars_prefix() {
        let p = parse(
            "c : forall x. P(x) => exists y. P(y) by forallL {
                c : forall x. P(x), P(c) => exists y. P(y) by existsR {
                    c : forall x. P(x), P(c) => exists y. P(y), P(c) by axiom
                }
            }",
        );
        assert!(p.to_latex().contains("c : "));
        assert!(p.to_typst().contains("c : "));
    }
}
