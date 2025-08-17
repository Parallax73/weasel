use std::borrow::Cow;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

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

    Identifier(String),

    // Start data types
    Number(i64),
    String(String),
    Boolean(bool),
    Float(f64),
    Null,

    //End data Types
    Plus,
    Minus,
    Star,
    Slash,
    Equal,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Less,
    Greater,
    Comma,
    Semicolon,
    StringLiteral(Cow<'static, str>),
    Unknown(char),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token<'a> {
    pub origin: Cow<'a, str>,
    pub offset: usize,
    pub kind: TokenType,
}

impl<'a> Token<'a> {
    pub fn span(&self) -> SourceSpan {
        let len = self.origin.len();
        (self.offset, len).into()
    }
}

#[derive(Error, Diagnostic, Debug)]
pub enum LexError {
    #[error("Unexpected character: {0}")]
    #[diagnostic(code(lexer::unexpected_character))]
    UnexpectedCharacter(char, #[label] SourceSpan),

    #[error("Unterminated string literal")]
    #[diagnostic(code(lexer::unterminated_string))]
    UnterminatedString(#[label] SourceSpan),

    #[error("Invalid number format")]
    #[diagnostic(code(lexer::invalid_number))]
    InvalidNumber(#[label] SourceSpan),

    #[error("Unknown symbol")]
    #[diagnostic(code(lexer::unknown_symbol))]
    UnknownSymbol(#[label] SourceSpan),
}

pub struct Lexer<'a> {
    input: &'a str,
    tokens: Vec<Token<'a>>,
    position: usize,
    token_start: usize,
    state: LexerState,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            tokens: Vec::new(),
            position: 0,
            token_start: 0,
            state: LexerState::Start,
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.position..].chars().next()
    }

    fn advance_char(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.position += c.len_utf8();
        Some(c)
    }

    fn add_token(&mut self, kind: TokenType) {
        let text = Cow::Borrowed(&self.input[self.token_start..self.position]);
        self.tokens.push(Token {
            origin: text,
            offset: self.token_start,
            kind,
        });
    }

    fn handle_in_number(&mut self) -> bool {
        if let Some(c) = self.peek_char() {
            if c.is_ascii_digit() {
                self.advance_char();
                return true;
            }
        }
        false
    }

    fn handle_in_string(&mut self) -> Result<(), LexError> {
        // We're at the opening quote, advance past it
        loop {
            if let Some(c) = self.advance_char() {
                if c == '"' {
                    // Extract the string content (between the quotes)
                    let text = &self.input[self.token_start + 1..self.position - 1];
                    self.add_token(TokenType::StringLiteral(Cow::Owned(text.to_string())));
                    self.state = LexerState::Start;
                    return Ok(());
                }
            } else {
                return Err(LexError::UnterminatedString(
                    (self.token_start, self.position - self.token_start).into(),
                ));
            }
        }
    }

    fn handle_in_comment(&mut self) {
        loop {
            if let Some(c) = self.advance_char() {
                if c == '\n' {
                    self.state = LexerState::Start;
                    return;
                }
            } else {
                self.state = LexerState::Start;
                return;
            }
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<Token<'a>>, LexError> {
        while self.position < self.input.len() {
            self.token_start = self.position;
            let c = self.advance_char().unwrap();

            match self.state {
                LexerState::Start => match c {
                    ' ' | '\t' | '\r' | '\n' => {}
                    '+' => self.add_token(TokenType::Plus),
                    '-' => self.add_token(TokenType::Minus),
                    '*' => self.add_token(TokenType::Star),
                    '/' => self.add_token(TokenType::Slash),
                    '=' => self.add_token(TokenType::Equal),
                    '(' => self.add_token(TokenType::LParen),
                    ')' => self.add_token(TokenType::RParen),
                    '{' => self.add_token(TokenType::LBrace),
                    '}' => self.add_token(TokenType::RBrace),
                    ',' => self.add_token(TokenType::Comma),
                    ';' => self.add_token(TokenType::Semicolon),
                    '[' => self.add_token(TokenType::LBracket),
                    ']' => self.add_token(TokenType::RBracket),
                    '<' => self.add_token(TokenType::Less),
                    '>' => self.add_token(TokenType::Greater),
                    '"' => {
                        self.state = LexerState::InString;
                        self.handle_in_string()?;
                    },
                    '0'..='9' => {
                        self.state = LexerState::InNumber;
                        while self.handle_in_number() {}
                        self.state = LexerState::Start;
                        let text = &self.input[self.token_start..self.position];
                        match text.parse::<i64>() {
                            Ok(num) => self.add_token(TokenType::Number(num)),
                            Err(_) => {
                                return Err(LexError::InvalidNumber(
                                    (self.token_start, self.position - self.token_start).into(),
                                ));
                            }
                        }
                    }
                    'a'..='z' | 'A'..='Z' | '_' => {
                        self.state = LexerState::InIdentifier;
                        loop {
                            if let Some(c) = self.peek_char() {
                                if c.is_alphanumeric() || c == '_' {
                                    self.advance_char();
                                } else {
                                    break;
                                }
                            } else {
                                break;
                            }
                        }
                        let text = &self.input[self.token_start..self.position];

                        // Handle keywords
                        let token_type = match text {
                            "true" => TokenType::Boolean(true),
                            "false" => TokenType::Boolean(false),
                            "null" => TokenType::Null,
                            _ => TokenType::Identifier(text.to_string()),
                        };

                        self.add_token(token_type);
                        self.state = LexerState::Start;
                    }
                    _ => {
                        return Err(LexError::UnexpectedCharacter(
                            c,
                            (self.token_start, c.len_utf8()).into(),
                        ));
                    }
                },
                LexerState::InString => {
                    // This case should not be reached since we handle strings immediately
                    return Err(LexError::UnexpectedCharacter(
                        c,
                        (self.token_start, c.len_utf8()).into(),
                    ));
                }
                LexerState::InComment => {
                    self.handle_in_comment();
                }
                _ => {}
            }
        }
        Ok(self.tokens)
    }
}