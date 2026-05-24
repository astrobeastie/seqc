use std::collections::{HashMap, HashSet};

use crate::expr::Expr;
use crate::formula::{BinOp, Formula, Sequent};
use crate::lexer::{Keyword, Lexer, Token};
use crate::proof::{Proof, ProofStep};

pub type ParseError = Vec<String>;
pub type ParseResult<T> = Result<T, ParseError>;

pub trait ParseCtx<T> {
    fn ctx(self, msg: impl FnOnce() -> String) -> ParseResult<T>;
}

impl<T> ParseCtx<T> for ParseResult<T> {
    fn ctx(self, msg: impl FnOnce() -> String) -> ParseResult<T> {
        self.map_err(|mut e| {
            e.push(msg());
            e
        })
    }
}

pub struct Parser {
    lexer: Lexer,
    current_token: Token,
    current_pos: usize,
}

impl Parser {
    pub fn new(input: String) -> ParseResult<Self> {
        let mut lexer = Lexer::new(input);
        let (first_token, first_pos) = lexer.next_token().map_err(|s| vec![s])?;
        Ok(Parser {
            lexer,
            current_token: first_token,
            current_pos: first_pos,
        })
    }

    fn advance(&mut self) -> ParseResult<()> {
        let (tok, pos) = self.lexer.next_token().map_err(|s| vec![s])?;
        self.current_token = tok;
        self.current_pos = pos;
        Ok(())
    }

    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        if self.current_token == expected {
            self.advance()
        } else {
            Err(vec![format!(
                "expected {:?} at byte {}, found {:?}",
                expected, self.current_pos, self.current_token,
            )])
        }
    }

    pub fn parse_expr(&mut self, bound_vars: &HashMap<String, usize>) -> ParseResult<Expr> {
        let start = self.current_pos;
        match &self.current_token {
            Token::Identifier(name) => {
                let identifier = name.clone();
                self.advance()?;
                if self.current_token == Token::LeftParen {
                    self.advance()?;
                    let mut args = Vec::new();
                    if self.current_token != Token::RightParen {
                        loop {
                            let arg = self.parse_expr(bound_vars).ctx(|| {
                                format!("while parsing function argument at byte {}", start)
                            })?;
                            args.push(arg);
                            if self.current_token == Token::Comma {
                                self.advance()?;
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(Token::RightParen)?;
                    Ok(Expr::Func(identifier, args))
                } else {
                    if let Some(&idx) = bound_vars.get(&identifier) {
                        let max = bound_vars.values().copied().max().unwrap();
                        Ok(Expr::Bound(max - idx))
                    } else {
                        Ok(Expr::Free(identifier))
                    }
                }
            }
            _ => Err(vec![format!(
                "expected term at byte {}, found {:?}",
                start, self.current_token,
            )]),
        }
    }

    pub fn parse_atomic_formula(
        &mut self,
        bound_vars: &HashMap<String, usize>,
    ) -> ParseResult<Formula> {
        let start = self.current_pos;
        match &self.current_token {
            Token::Bot => {
                self.advance()?;
                Ok(Formula::Bot)
            }
            Token::Top => {
                self.advance()?;
                Ok(Formula::Top)
            }
            Token::Identifier(name) => {
                let identifier = name.clone();
                self.advance()?;
                if self.current_token == Token::LeftParen {
                    self.advance()?;
                    let mut args = Vec::new();
                    if self.current_token != Token::RightParen {
                        loop {
                            let arg = self.parse_expr(bound_vars).ctx(|| {
                                format!("while parsing predicate argument at byte {}", start)
                            })?;
                            args.push(arg);
                            if self.current_token == Token::Comma {
                                self.advance()?;
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(Token::RightParen)?;
                    Ok(Formula::Pred(identifier, args))
                } else {
                    Ok(Formula::Pred(identifier, Vec::new()))
                }
            }
            Token::Not => {
                self.advance()?;
                let formula = self
                    .parse_atomic_formula(bound_vars)
                    .ctx(|| format!("while parsing operand of negation at byte {}", start))?;
                Ok(Formula::Not(Box::new(formula)))
            }
            Token::LeftParen => {
                self.advance()?;
                let formula = self
                    .parse_formula_inner(0, bound_vars)
                    .ctx(|| format!("while parsing parenthesized formula at byte {}", start))?;
                self.expect(Token::RightParen)?;
                Ok(formula)
            }
            Token::ForAll => {
                self.advance()?;
                let var = match &self.current_token {
                    Token::Identifier(v) => {
                        let v = v.clone();
                        self.advance()?;
                        v
                    }
                    _ => {
                        return Err(vec![format!(
                            "expected bound variable at byte {}, found {:?}",
                            self.current_pos, self.current_token,
                        )])
                        .ctx(|| format!("while parsing forall-quantifier at byte {}", start));
                    }
                };
                self.expect(Token::Dot)?;
                let mut new_bound_vars = bound_vars.clone();
                let next_idx = new_bound_vars
                    .values()
                    .copied()
                    .max()
                    .map(|m| m + 1)
                    .unwrap_or(0);
                new_bound_vars.insert(var.clone(), next_idx);
                let body = self
                    .parse_atomic_formula(&new_bound_vars)
                    .ctx(|| format!("while parsing body of forall-quantifier at byte {}", start))?;
                Ok(Formula::All(var, Box::new(body)))
            }
            Token::Exists => {
                self.advance()?;
                let var = match &self.current_token {
                    Token::Identifier(v) => {
                        let v = v.clone();
                        self.advance()?;
                        v
                    }
                    _ => {
                        return Err(vec![format!(
                            "expected bound variable at byte {}, found {:?}",
                            self.current_pos, self.current_token,
                        )])
                        .ctx(|| format!("while parsing exists-quantifier at byte {}", start));
                    }
                };
                self.expect(Token::Dot)?;
                let mut new_bound_vars = bound_vars.clone();
                let next_idx = new_bound_vars
                    .values()
                    .copied()
                    .max()
                    .map(|m| m + 1)
                    .unwrap_or(0);
                new_bound_vars.insert(var.clone(), next_idx);
                let body = self
                    .parse_atomic_formula(&new_bound_vars)
                    .ctx(|| format!("while parsing body of exists-quantifier at byte {}", start))?;
                Ok(Formula::Exists(var, Box::new(body)))
            }
            _ => Err(vec![format!(
                "expected formula at byte {}, found {:?}",
                start, self.current_token,
            )]),
        }
    }

    fn peek_binop(&self) -> Option<BinOp> {
        match &self.current_token {
            Token::And => Some(BinOp::And),
            Token::Or => Some(BinOp::Or),
            Token::RightArrow => Some(BinOp::Implication),
            _ => None,
        }
    }

    fn parse_formula_inner(
        &mut self,
        min_prec: u8,
        bound_vars: &HashMap<String, usize>,
    ) -> ParseResult<Formula> {
        let mut lhs = self.parse_atomic_formula(bound_vars)?;
        while let Some(op) = self.peek_binop() {
            let (l_prec, r_prec) = op.assoc().child_mins(op.prec());
            assert_ne!(min_prec, l_prec);
            if l_prec < min_prec {
                break;
            }
            let op_pos = self.current_pos;
            self.advance()?;
            let rhs = self
                .parse_formula_inner(r_prec, bound_vars)
                .ctx(|| format!("while parsing rhs of binary operator at byte {}", op_pos))?;
            lhs = match op {
                BinOp::And => Formula::And(Box::new(lhs), Box::new(rhs)),
                BinOp::Or => Formula::Or(Box::new(lhs), Box::new(rhs)),
                BinOp::Implication => Formula::Implication(Box::new(lhs), Box::new(rhs)),
            }
        }
        Ok(lhs)
    }

    pub fn parse_formula(&mut self) -> ParseResult<Formula> {
        self.parse_formula_inner(0, &HashMap::new())
    }

    pub fn parse_sequent(&mut self) -> ParseResult<Sequent> {
        // Optional eigenvars prefix: IDENT (',' IDENT)* ':'
        // Snapshot the position of the current token so we can rewind if there is no colon.
        let snap = self.current_pos;
        let mut eigenvars: HashSet<String> = HashSet::new();
        if matches!(self.current_token, Token::Identifier(_)) {
            let mut names: Vec<String> = Vec::new();
            loop {
                let Token::Identifier(name) = &self.current_token else {
                    break;
                };
                names.push(name.clone());
                self.advance()?;
                if self.current_token == Token::Comma {
                    self.advance()?;
                } else {
                    break;
                }
            }
            if self.current_token == Token::Colon && !names.is_empty() {
                self.advance()?;
                eigenvars = names.into_iter().collect();
            } else {
                self.lexer.set_position(snap);
                self.advance()?;
            }
        }
        let mut assumptions = HashSet::new();
        while !matches!(self.current_token, Token::SequentArrow | Token::EOF) {
            let f_pos = self.current_pos;
            let formula = self
                .parse_formula()
                .ctx(|| format!("while parsing assumption at byte {}", f_pos))?;
            assumptions.insert(formula);
            if self.current_token == Token::Comma {
                self.advance()?;
            } else {
                break;
            }
        }
        self.expect(Token::SequentArrow)?;
        let mut conclusions = HashSet::new();
        while !matches!(
            self.current_token,
            Token::EOF | Token::Keyword(_) | Token::RightBrace
        ) {
            let f_pos = self.current_pos;
            let formula = self
                .parse_formula()
                .ctx(|| format!("while parsing conclusion at byte {}", f_pos))?;
            conclusions.insert(formula);
            if self.current_token == Token::Comma {
                self.advance()?;
            } else {
                break;
            }
        }
        Ok(Sequent {
            assumptions,
            conclusions,
            eigenvars,
        })
    }

    pub fn parse_proof(&mut self) -> ParseResult<Proof> {
        let start = self.current_pos;
        let claim = self
            .parse_sequent()
            .ctx(|| format!("while parsing claim at byte {}", start))?;
        self.expect(Token::Keyword(Keyword::By))?;
        let kw = match &self.current_token {
            Token::Keyword(k) => *k,
            _ => {
                return Err(vec![format!(
                    "expected proof step keyword at byte {}, found {:?}",
                    self.current_pos, self.current_token,
                )]);
            }
        };
        self.advance()?;
        // Nullary rules (axiom, botL) take no body.
        let has_body = !matches!(kw, Keyword::Axiom | Keyword::BotLeft);
        if has_body {
            self.expect(Token::LeftBrace)?;
        } else if self.current_token == Token::LeftBrace {
            return Err(vec![format!(
                "axiom and botL do not take a body (at byte {})",
                self.current_pos
            )]);
        }
        let proof_step = match kw {
            Keyword::Axiom => ProofStep::Axiom,
            Keyword::BotLeft => ProofStep::BotLeft,
            Keyword::NegLeft => ProofStep::NegLeft(self.parse_sub_proof("negL", start)?),
            Keyword::NegRight => ProofStep::NegRight(self.parse_sub_proof("negR", start)?),
            Keyword::AndLeft => ProofStep::AndLeft(self.parse_sub_proof("andL", start)?),
            Keyword::AndRight => {
                let l = self.parse_sub_proof("left branch of andR", start)?;
                self.expect(Token::Comma)?;
                let r = self.parse_sub_proof("right branch of andR", start)?;
                ProofStep::AndRight(l, r)
            }
            Keyword::OrLeft => {
                let l = self.parse_sub_proof("left branch of orL", start)?;
                self.expect(Token::Comma)?;
                let r = self.parse_sub_proof("right branch of orL", start)?;
                ProofStep::OrLeft(l, r)
            }
            Keyword::OrRight => ProofStep::OrRight(self.parse_sub_proof("orR", start)?),
            Keyword::ImpLeft => {
                let l = self.parse_sub_proof("left branch of impL", start)?;
                self.expect(Token::Comma)?;
                let r = self.parse_sub_proof("right branch of impL", start)?;
                ProofStep::ImplLeft(l, r)
            }
            Keyword::ImpRight => ProofStep::ImplRight(self.parse_sub_proof("impR", start)?),
            Keyword::ForAllLeft => ProofStep::ForAllLeft(self.parse_sub_proof("forallL", start)?),
            Keyword::ForAllRight => ProofStep::ForAllRight(self.parse_sub_proof("forallR", start)?),
            Keyword::ExistsLeft => ProofStep::ExistsLeft(self.parse_sub_proof("existsL", start)?),
            Keyword::ExistsRight => ProofStep::ExistsRight(self.parse_sub_proof("existsR", start)?),
            Keyword::By => {
                return Err(vec![format!(
                    "'by' is not a valid proof step keyword (at byte {})",
                    start,
                )]);
            }
        };
        if has_body {
            self.expect(Token::RightBrace)?;
        }
        Ok(Proof {
            claim,
            proof: proof_step,
        })
    }

    fn parse_sub_proof(&mut self, label: &str, parent_start: usize) -> ParseResult<Box<Proof>> {
        let p = self.parse_proof().ctx(|| {
            format!(
                "while parsing sub-proof of {} at byte {}",
                label, parent_start
            )
        })?;
        Ok(Box::new(p))
    }
}

#[cfg(test)]
mod tests {
    use super::{ParseResult, Parser};
    use crate::proof::Proof;

    fn parse(input: &str) -> ParseResult<Proof> {
        let mut p = Parser::new(input.to_string())?;
        p.parse_proof()
    }

    #[test]
    fn axiom_parses() {
        let r = parse("A => A by axiom");
        assert!(r.is_ok(), "expected ok, got {:?}", r.err());
    }

    #[test]
    fn empty_conclusion_parses() {
        let r = parse("A, ~A => by botL");
        assert!(r.is_ok(), "expected ok, got {:?}", r.err());
    }

    #[test]
    fn forall_in_formula_parses() {
        let r = parse("=> forall x. P(x) -> P(x) by impR { P(x) => P(x) by axiom }");
        assert!(r.is_ok(), "expected ok, got {:?}", r.err());
    }

    #[test]
    fn forall_left_body_is_plain_subproof() {
        let r = parse("forall x. P(x) => P(a) by forallL { P(a) => P(a) by axiom }");
        assert!(r.is_ok(), "expected ok, got {:?}", r.err());
    }

    #[test]
    fn unknown_proof_step_yields_trace() {
        let r = parse("=> A by foo { }");
        let trace = r.err().expect("expected err");
        assert!(
            trace
                .iter()
                .any(|s| s.contains("expected proof step keyword")),
            "trace: {:?}",
            trace,
        );
        assert!(
            trace.iter().any(|s| s.contains("foo")),
            "trace: {:?}",
            trace,
        );
    }

    #[test]
    fn missing_sequent_arrow_yields_trace() {
        let r = parse("A, B by axiom");
        let trace = r.err().expect("expected err");
        assert!(
            trace.iter().any(|s| s.contains("SequentArrow")),
            "trace: {:?}",
            trace,
        );
    }

    #[test]
    fn bot_top_ascii_parse() {
        let r = parse("0 => 1 by axiom");
        assert!(r.is_ok(), "expected ok, got {:?}", r.err());
    }

    #[test]
    fn bot_top_unicode_parse() {
        let r = parse("⊥ => ⊤ by axiom");
        assert!(r.is_ok(), "expected ok, got {:?}", r.err());
    }

    #[test]
    fn nested_error_builds_trace() {
        let r = parse("=> A & by axiom");
        let trace = r.err().expect("expected err");
        assert!(
            trace.iter().any(|s| s.contains("expected formula")),
            "trace: {:?}",
            trace,
        );
        assert!(
            trace.iter().any(|s| s.contains("rhs of binary operator")),
            "trace: {:?}",
            trace,
        );
        assert!(
            trace.iter().any(|s| s.contains("conclusion")),
            "trace: {:?}",
            trace,
        );
    }
}
