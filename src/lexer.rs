#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Identifier(String),
    RightArrow,
    LeftParen,
    RightParen,
    Not,
    And,
    Or,
    ForAll,
    Exists,
    Bot,
    Top,
    Dot,
    Comma,

    LeftBrace,
    RightBrace,
    SequentArrow,
    Keyword(Keyword),

    EOF,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Keyword {
    By,
    Axiom,
    BotLeft,
    NegLeft,
    NegRight,
    AndLeft,
    AndRight,
    OrLeft,
    OrRight,
    ImpLeft,
    ImpRight,
    ForAllLeft,
    ForAllRight,
    ExistsLeft,
    ExistsRight,
}

#[derive(Debug)]
pub struct Lexer {
    input: String,
    position: usize,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        Lexer { input, position: 0 }
    }

    fn remaining(&self) -> &str {
        &self.input[self.position..]
    }

    fn skip_ws(&mut self) {
        while let Some(c) = self.remaining().chars().next() {
            if c.is_whitespace() {
                self.position += c.len_utf8();
            } else {
                break;
            }
        }
    }

    fn peek_string(&self) -> Option<String> {
        let mut chars = self.remaining().chars();
        let mut s = String::new();

        if let Some(c) = chars.next() {
            if c.is_alphabetic() || c == '_' {
                s.push(c);
            } else {
                return None;
            }
        } else {
            return None;
        }

        for c in chars {
            if c.is_alphanumeric() || c == '_' || c == '\'' {
                s.push(c);
            } else {
                break;
            }
        }
        Some(s)
    }

    fn is_word_boundary_after(&self, len: usize) -> bool {
        self.remaining()[len..]
            .chars()
            .next()
            .map(|c| !c.is_alphanumeric() && c != '_' && c != '\'')
            .unwrap_or(true)
    }

    pub fn next_token(&mut self) -> Result<(Token, usize), String> {
        self.skip_ws();
        let start = self.position;
        let s = self.remaining();
        if s.is_empty() {
            return Ok((Token::EOF, start));
        }

        // Symbol tokens. Longest match first so e.g. "->" beats a hypothetical "-".
        let symbols: &[(&str, Token)] = &[
            ("->", Token::RightArrow),
            ("=>", Token::SequentArrow),
            ("→", Token::RightArrow),
            ("⇒", Token::SequentArrow),
            ("¬", Token::Not),
            ("∧", Token::And),
            ("∨", Token::Or),
            ("∀", Token::ForAll),
            ("∃", Token::Exists),
            ("⊥", Token::Bot),
            ("⊤", Token::Top),
            ("(", Token::LeftParen),
            (")", Token::RightParen),
            ("~", Token::Not),
            ("!", Token::Not),
            ("&", Token::And),
            ("|", Token::Or),
            (".", Token::Dot),
            (",", Token::Comma),
            ("{", Token::LeftBrace),
            ("}", Token::RightBrace),
            ("0", Token::Bot),
            ("1", Token::Top),
        ];
        for (prefix, tok) in symbols {
            if s.starts_with(prefix) {
                self.position += prefix.len();
                return Ok((tok.clone(), start));
            }
        }

        // Keyword table — longest match first, word boundary required.
        let keywords: &[(&str, Token)] = &[
            ("forallL", Token::Keyword(Keyword::ForAllLeft)),
            ("forallR", Token::Keyword(Keyword::ForAllRight)),
            ("forall", Token::ForAll),
            ("existsL", Token::Keyword(Keyword::ExistsLeft)),
            ("existsR", Token::Keyword(Keyword::ExistsRight)),
            ("exists", Token::Exists),
            ("andL", Token::Keyword(Keyword::AndLeft)),
            ("andR", Token::Keyword(Keyword::AndRight)),
            ("and", Token::And),
            ("orL", Token::Keyword(Keyword::OrLeft)),
            ("orR", Token::Keyword(Keyword::OrRight)),
            ("or", Token::Or),
            ("negL", Token::Keyword(Keyword::NegLeft)),
            ("negR", Token::Keyword(Keyword::NegRight)),
            ("impL", Token::Keyword(Keyword::ImpLeft)),
            ("impR", Token::Keyword(Keyword::ImpRight)),
            ("botL", Token::Keyword(Keyword::BotLeft)),
            ("axiom", Token::Keyword(Keyword::Axiom)),
            ("all", Token::ForAll),
            ("by", Token::Keyword(Keyword::By)),
        ];
        for (prefix, tok) in keywords {
            if s.starts_with(prefix) && self.is_word_boundary_after(prefix.len()) {
                self.position += prefix.len();
                return Ok((tok.clone(), start));
            }
        }

        if let Some(ident) = self.peek_string() {
            self.position += ident.len();
            return Ok((Token::Identifier(ident), start));
        }

        let c = s.chars().next().unwrap();
        Err(format!("unexpected character {:?} at byte {}", c, start))
    }
}
