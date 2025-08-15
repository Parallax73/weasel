use miette::{Diagnostic, Result, SourceSpan};
use std::borrow::Cow;
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum LexError {
    #[error("Unexpected character: {0}")]
    #[diagnostic(
        code(lexer::unexpected_character),
        help("This character is not valid in the current context")
    )]
    UnexpectedCharacter(char, #[source_code] Cow<'static, str>, #[label("here")] SourceSpan),

    #[error("Unterminated string literal")]
    #[diagnostic(
        code(lexer::unterminated_string),
        help("String literals must be closed with a matching quote")
    )]
    UnterminatedString(#[source_code] Cow<'static, str>, #[label("started here")] SourceSpan),

    #[error("Invalid number literal")]
    #[diagnostic(
        code(lexer::invalid_number),
        help("Number literals must contain valid digits")
    )]
    InvalidNumber(#[source_code] Cow<'static, str>, #[label("here")] SourceSpan),

    #[error("Unknown symbol: {0}")]
    #[diagnostic(
        code(lexer::unknown_symbol),
        help("This symbol is not recognized by the lexer")
    )]
    UnknownSymbol(char, #[source_code] Cow<'static, str>, #[label("here")] SourceSpan),
}

#[derive(PartialEq, Debug, Clone)]
pub enum LexerState {
    Start,
    Done,
    InNumber,
    InIdentifier,
    InString,
    InComment,
    InSymbol,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenType {
    Number(i64),
    Identifier(String),
    Plus,
    Minus,
    Star,
    Slash,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Equal,
    Semicolon,
    StringLiteral(String),
    Comma,
    EqualEqual,
    NotEqual,
    Less,
    Greater,
    LessEq,
    GreaterEq,
    And,
    Or,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'de> {
    pub origin: &'de str,
    pub offset: usize,
    pub kind: TokenType,
}

pub struct Lexer<'de> {
    whole: &'de str,
    rest: &'de str,
    byte: usize,
    peeked: Option<Result<TokenType, LexError>>,
    state: LexerState,
}

impl<'de> Lexer<'de> {
    pub fn new(input: &'de str) -> Self {
        Self {
            whole: input,
            rest: input,
            byte: 0,
            peeked: None,
            state: LexerState::Start,
        }
    }

    pub fn advance(&mut self) {
        if self.rest.is_empty() {
            return;
        }

        let next_char = self.rest.chars().next().unwrap();
        let char_len = next_char.len_utf8();

        self.byte += char_len;
        self.rest = &self.rest[char_len..];
    }

    pub fn peek(&self) -> Option<char> {
        self.rest.chars().next()
    }

    pub fn peek_next(&self) -> Option<char> {
        self.rest.chars().nth(1)
    }

    pub fn is_whitespace(c: char) -> bool {
        matches!(c, ' ' | '\t' | '\n' | '\r')
    }

    pub fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if !Self::is_whitespace(c) {
                break;
            }
            self.advance();
        }
    }

    pub fn state_transition(&mut self) {
        match self.state {
            LexerState::Start => {
                if self.rest.is_empty() {
                    self.state = LexerState::Done;
                    return;
                }
                let c = self.peek().unwrap();
                if c.is_ascii_digit() {
                    self.state = LexerState::InNumber;
                } else if c.is_alphabetic() || c == '_' {
                    self.state = LexerState::InIdentifier;
                } else if c == '"' {
                    self.state = LexerState::InString;
                } else if c == '/' && (self.peek_next() == Some('/') || self.peek_next() == Some('*')) {
                    self.state = LexerState::InComment;
                } else if matches!(c, '+' | '-' | '*' | '/' | '(' | ')' | '{' | '}' | '=' | ';' | ',' | '!' | '<' | '>' | '&' | '|') {
                    self.state = LexerState::InSymbol;
                } else {
                    self.peeked = Some(Err(LexError::UnexpectedCharacter(
                        c,
                        Cow::Owned(self.whole.to_string()),
                        SourceSpan::from(self.byte..self.byte + c.len_utf8()),
                    )));
                    self.state = LexerState::Start;
                }
            }
            LexerState::InNumber => self.handle_in_number(),
            LexerState::InIdentifier => self.handle_in_identifier(),
            LexerState::InString => self.handle_in_string(),
            LexerState::InComment => self.handle_in_comment(),
            LexerState::InSymbol => self.handle_in_symbol(),
            LexerState::Done => {}
        }
    }

    pub fn handle_in_number(&mut self) {
        let start = self.byte;
        let mut acc: i64 = 0;

        while let Some(c) = self.peek() {
            if let Some(d) = c.to_digit(10) {
                match acc.checked_mul(10).and_then(|v| v.checked_add(d as i64)) {
                    Some(val) => {
                        acc = val;
                        self.advance();
                    }
                    None => {
                        self.peeked = Some(Err(LexError::InvalidNumber(
                            Cow::Owned(self.whole.to_string()),
                            SourceSpan::from(start..self.byte),
                        )));
                        self.state = LexerState::Start;
                        return;
                    }
                }
            } else {
                break;
            }
        }

        self.peeked = Some(Ok(TokenType::Number(acc)));
        self.state = LexerState::Start;
    }

    pub fn handle_in_identifier(&mut self) {
        let start = self.byte;
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }
        let slice = &self.whole[start..self.byte];
        self.peeked = Some(Ok(TokenType::Identifier(slice.to_string())));
        self.state = LexerState::Start;
    }

    pub fn handle_in_symbol(&mut self) {
        let c = self.peek();
        if c == Some('=') && self.peek_next() == Some('=') {
            self.advance();
            self.advance();
            self.peeked = Some(Ok(TokenType::EqualEqual));
        } else if c == Some('!') && self.peek_next() == Some('=') {
            self.advance();
            self.advance();
            self.peeked = Some(Ok(TokenType::NotEqual));
        } else if c == Some('<') && self.peek_next() == Some('=') {
            self.advance();
            self.advance();
            self.peeked = Some(Ok(TokenType::LessEq));
        } else if c == Some('>') && self.peek_next() == Some('=') {
            self.advance();
            self.advance();
            self.peeked = Some(Ok(TokenType::GreaterEq));
        } else if c == Some('&') && self.peek_next() == Some('&') {
            self.advance();
            self.advance();
            self.peeked = Some(Ok(TokenType::And));
        } else if c == Some('|') && self.peek_next() == Some('|') {
            self.advance();
            self.advance();
            self.peeked = Some(Ok(TokenType::Or));
        } else {
            let token = match c {
                Some('+') => TokenType::Plus,
                Some('-') => TokenType::Minus,
                Some('*') => TokenType::Star,
                Some('/') => TokenType::Slash,
                Some('(') => TokenType::LParen,
                Some(')') => TokenType::RParen,
                Some('{') => TokenType::LBrace,
                Some('}') => TokenType::RBrace,
                Some('=') => TokenType::Equal,
                Some(';') => TokenType::Semicolon,
                Some(',') => TokenType::Comma,
                Some('<') => TokenType::Less,
                Some('>') => TokenType::Greater,
                Some('!') => TokenType::Not,
                Some(c) => {
                    self.peeked = Some(Err(LexError::UnknownSymbol(
                        c,
                        Cow::Owned(self.whole.to_string()),
                        SourceSpan::from(self.byte..self.byte + c.len_utf8()),
                    )));
                    self.state = LexerState::Start;
                    return;
                }
                None => {
                    self.peeked = Some(Err(LexError::UnexpectedCharacter(
                        '\0',
                        Cow::Owned(self.whole.to_string()),
                        SourceSpan::from(self.byte..self.byte + 1),
                    )));
                    self.state = LexerState::Start;
                    return;
                }
            };
            self.advance();
            self.peeked = Some(Ok(token));
        }
        self.state = LexerState::Start;
    }

    pub fn handle_in_comment(&mut self) {
        if self.peek() == Some('/') && self.peek_next() == Some('/') {
            self.advance();
            self.advance();
            while let Some(c) = self.peek() {
                self.advance();
                if c == '\n' {
                    break;
                }
            }
        } else if self.peek() == Some('/') && self.peek_next() == Some('*') {
            self.advance();
            self.advance();
            while let Some(c) = self.peek() {
                self.advance();
                if c == '*' && self.peek() == Some('/') {
                    self.advance();
                    break;
                }
            }
        }
        self.state = LexerState::Start;
    }

    pub fn handle_in_string(&mut self) {
        let start = self.byte;
        self.advance(); // skip opening quote
        while let Some(c) = self.peek() {
            if c == '"' {
                let slice = &self.whole[start + 1..self.byte];
                self.advance(); // skip closing quote
                self.peeked = Some(Ok(TokenType::StringLiteral(slice.to_string())));
                self.state = LexerState::Start;
                return;
            }
            self.advance();
        }
        self.peeked = Some(Err(LexError::UnterminatedString(
            Cow::Owned(self.whole.to_string()),
            SourceSpan::from(start..self.byte),
        )));
        self.state = LexerState::Start;
    }

    pub fn next_token(&mut self) -> Result<Option<Token<'de>>> {
        self.skip_whitespace();

        if self.state == LexerState::Done || self.rest.is_empty() {
            return Ok(None);
        }

        if let Some(cached_result) = self.peeked.take() {
            return match cached_result {
                Ok(token_type) => Ok(Some(Token {
                    origin: self.whole,
                    offset: self.byte,
                    kind: token_type,
                })),
                Err(e) => Err(e.into()),
            };
        }

        let token_start = self.byte;
        self.state_transition();

        if let Some(Err(e)) = self.peeked.take() {
            return Err(e.into());
        }

        match self.state {
            LexerState::InNumber => self.handle_in_number(),
            LexerState::InIdentifier => self.handle_in_identifier(),
            LexerState::InString => self.handle_in_string(),
            LexerState::InSymbol => self.handle_in_symbol(),
            LexerState::InComment => {
                self.handle_in_comment();
                return self.next_token();
            }
            LexerState::Done => return Ok(None),
            LexerState::Start => return Ok(None),
        };

        match self.peeked.take() {
            Some(Ok(token_type)) => Ok(Some(Token {
                origin: self.whole,
                offset: token_start,
                kind: token_type,
            })),
            Some(Err(e)) => Err(e.into()),
            None => Ok(None),
        }
    }

    pub fn tokenize(&mut self) -> Result<Vec<Token<'de>>> {
        let mut tokens = Vec::new();

        while let Some(token) = self.next_token()? {
            tokens.push(token);
        }

        Ok(tokens)
    }
}