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
    Number(i64),
    Identifier(String),
    Plus,
    Minus,
    Star,
    Slash,
    Equal,
    LParen,
    RParen,
    LBrace,
    RBrace,
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
    state: LexerState,
    position: usize,
    token_start: usize,
    tokens: Vec<Token<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            state: LexerState::Start,
            position: 0,
            token_start: 0,
            tokens: Vec::new(),
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.position..].chars().next()
    }

    fn advance_char(&mut self) -> Option<char> {
        if let Some(ch) = self.peek_char() {
            self.position += ch.len_utf8();
            Some(ch)
        } else {
            None
        }
    }

    fn add_token(&mut self, kind: TokenType) {
        let origin = Cow::Borrowed(&self.input[self.token_start..self.position]);
        self.tokens.push(Token {
            origin,
            offset: self.token_start,
            kind,
        });
    }

    fn handle_in_comment(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch == '\n' {
                break;
            }
            self.advance_char();
        }
        self.state = LexerState::Start;
    }

    fn handle_in_string(&mut self) -> Result<(), LexError> {
        while let Some(ch) = self.advance_char() {
            if ch == '"' {
                let text = &self.input[self.token_start + 1..self.position - 1];
                self.add_token(TokenType::StringLiteral(Cow::Owned(text.to_string())));
                self.state = LexerState::Start;
                return Ok(());
            }
        }
        Err(LexError::UnterminatedString(
            (self.token_start, self.position - self.token_start).into(),
        ))
    }

    pub fn tokenize(mut self) -> Result<Vec<Token<'a>>, LexError> {
        while let Some(ch) = self.peek_char() {
            match self.state {
                LexerState::Start => {
                    self.token_start = self.position;
                    match ch {
                        '0'..='9' => {
                            self.state = LexerState::InNumber;
                            self.advance_char();
                        }
                        'a'..='z' | 'A'..='Z' | '_' => {
                            self.state = LexerState::InIdentifier;
                            self.advance_char();
                        }
                        '"' => {
                            self.state = LexerState::InString;
                            self.advance_char();
                        }
                        '/' => {
                            self.advance_char();
                            if self.peek_char() == Some('/') {
                                self.state = LexerState::InComment;
                                self.advance_char();
                            } else {
                                self.add_token(TokenType::Slash);
                                self.state = LexerState::Start;
                            }
                        }
                        '+' => {
                            self.advance_char();
                            self.add_token(TokenType::Plus);
                        }
                        '-' => {
                            self.advance_char();
                            self.add_token(TokenType::Minus);
                        }
                        '*' => {
                            self.advance_char();
                            self.add_token(TokenType::Star);
                        }
                        '=' => {
                            self.advance_char();
                            self.add_token(TokenType::Equal);
                        }
                        '(' => {
                            self.advance_char();
                            self.add_token(TokenType::LParen);
                        }
                        ')' => {
                            self.advance_char();
                            self.add_token(TokenType::RParen);
                        }
                        '{' => {
                            self.advance_char();
                            self.add_token(TokenType::LBrace);
                        }
                        '}' => {
                            self.advance_char();
                            self.add_token(TokenType::RBrace);
                        }
                        ',' => {
                            self.advance_char();
                            self.add_token(TokenType::Comma);
                        }
                        ';' => {
                            self.advance_char();
                            self.add_token(TokenType::Semicolon);
                        }
                        ' ' | '\t' | '\n' | '\r' => {
                            self.advance_char();
                        }
                        _ => {
                            return Err(LexError::UnexpectedCharacter(
                                ch,
                                (self.position, ch.len_utf8()).into(),
                            ));
                        }
                    }
                }
                LexerState::InNumber => {
                    if let Some(c) = self.peek_char() {
                        if c.is_ascii_digit() {
                            self.advance_char();
                        } else {
                            let text = &self.input[self.token_start..self.position];
                            match text.parse::<i64>() {
                                Ok(num) => self.add_token(TokenType::Number(num)),
                                Err(_) => {
                                    return Err(LexError::InvalidNumber(
                                        (self.token_start, self.position - self.token_start).into(),
                                    ));
                                }
                            }
                            self.state = LexerState::Start;
                        }
                    } else {
                        let text = &self.input[self.token_start..self.position];
                        match text.parse::<i64>() {
                            Ok(num) => self.add_token(TokenType::Number(num)),
                            Err(_) => {
                                return Err(LexError::InvalidNumber(
                                    (self.token_start, self.position - self.token_start).into(),
                                ));
                            }
                        }
                        break;
                    }
                }
                LexerState::InIdentifier => {
                    if let Some(c) = self.peek_char() {
                        if c.is_alphanumeric() || c == '_' {
                            self.advance_char();
                        } else {
                            let text = &self.input[self.token_start..self.position];
                            self.add_token(TokenType::Identifier(text.to_string()));
                            self.state = LexerState::Start;
                        }
                    } else {
                        let text = &self.input[self.token_start..self.position];
                        self.add_token(TokenType::Identifier(text.to_string()));
                        break;
                    }
                }
                LexerState::InString => {
                    self.handle_in_string()?;
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
