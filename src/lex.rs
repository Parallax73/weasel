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

    // Data types
    Number(i64),
    String(String),
    Boolean(bool),
    Float(f64),
    Null,

    // Keywords
    If,
    Else,
    While,
    Break,
    Continue,
    Fn,
    Return,
    Let,
    True,
    False,
    Str,
    Int,
    Bool,
    FloatType,
    Arr,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Equal,
    EqualEqual,    // ==
    NotEqual,      // not=
    Less,
    Greater,
    LessEqual,     // <=
    GreaterEqual,  // >=
    And,           // and
    Or,            // or
    Not,           // not
    LeftShift,     // <<
    RightShift,    // >>
    PlusEqual,     // +=
    MinusEqual,    // -=
    StarEqual,     // *=
    SlashEqual,    // /=

    // Delimiters
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semicolon,
    Colon,         // :
    Arrow,         // ->

    StringLiteral(Cow<'static, str>),
    Unknown(char),
    Eof,
    Bang,
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
    #[error("Unterminated string")]
    #[diagnostic(code(lex::unterminated_string), help("A string literal was not closed with a '\"'"))]
    UnterminatedString(#[label("This string was not closed")] SourceSpan),

    #[error("Unknown character '{0}'")]
    #[diagnostic(code(lex::unknown_character))]
    UnknownCharacter(char),

    #[error("Invalid number")]
    #[diagnostic(code(lex::invalid_number))]
    InvalidNumber,
}

pub struct Lexer<'a> {
    input: &'a str,
    position: usize,
    token_start: usize,
    tokens: Vec<Token<'a>>,
    state: LexerState,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            position: 0,
            token_start: 0,
            tokens: Vec::new(),
            state: LexerState::Start,
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<Token<'a>>, LexError> {
        while self.state != LexerState::Done {
            match self.state {
                LexerState::Start => {
                    self.token_start = self.position;
                    self.handle_start()?
                }
                LexerState::InNumber => self.handle_in_number(),
                LexerState::InIdentifier => self.handle_in_identifier(),
                LexerState::InString => self.handle_in_string()?,
                LexerState::InComment => self.handle_in_comment(),
                LexerState::InSymbol => self.handle_in_symbol(),
                LexerState::Done => {}
            }
        }
        Ok(self.tokens)
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

    fn handle_start(&mut self) -> Result<(), LexError> {
        if let Some(c) = self.advance_char() {
            match c {
                c if c.is_ascii_whitespace() => {}
                c if c.is_ascii_digit() => {
                    self.state = LexerState::InNumber;
                    self.position -= c.len_utf8();
                }
                c if c.is_alphabetic() => {
                    self.state = LexerState::InIdentifier;
                    self.position -= c.len_utf8();
                }
                '\"' => self.state = LexerState::InString,
                '/' => {
                    if let Some(next) = self.peek_char() {
                        if next == '/' {
                            self.advance_char();
                            self.state = LexerState::InComment;
                        } else {
                            self.add_token(TokenType::Slash);
                        }
                    } else {
                        self.add_token(TokenType::Slash);
                    }
                }
                _ => {
                    self.state = LexerState::InSymbol;
                    self.position -= c.len_utf8();
                }
            }
        } else {
            self.state = LexerState::Done;
            self.add_token(TokenType::Eof);
        }
        Ok(())
    }

    fn handle_in_number(&mut self) {
        while let Some(c) = self.peek_char() {
            if c.is_ascii_digit() {
                self.advance_char();
            } else if c == '.' {
                self.advance_char();
                while let Some(c) = self.peek_char() {
                    if c.is_ascii_digit() {
                        self.advance_char();
                    } else {
                        break;
                    }
                }
                let text = &self.input[self.token_start..self.position];
                let value = text.parse::<f64>().unwrap();
                self.add_token(TokenType::Float(value));
                self.state = LexerState::Start;
                return;
            } else {
                break;
            }
        }
        let text = &self.input[self.token_start..self.position];
        let value = text.parse::<i64>().unwrap();
        self.add_token(TokenType::Number(value));
        self.state = LexerState::Start;
    }

    fn handle_in_identifier(&mut self) {
        while let Some(c) = self.peek_char() {
            if c.is_ascii_alphanumeric() || c == '_' {
                self.advance_char();
            } else {
                break;
            }
        }
        let text = &self.input[self.token_start..self.position];
        let kind = match text {
            "if" => TokenType::If,
            "else" => TokenType::Else,
            "while" => TokenType::While,
            "break" => TokenType::Break,
            "continue" => TokenType::Continue,
            "fn" => TokenType::Fn,
            "let" => TokenType::Let,
            "true" => TokenType::True,
            "false" => TokenType::False,
            "str" => TokenType::Str,
            "int" => TokenType::Int,
            "bool" => TokenType::Bool,
            "float" => TokenType::FloatType,
            "arr" => TokenType::Arr,
            "not" => {
                if self.peek_char() == Some('=') {
                    self.advance_char(); 
                    TokenType::NotEqual
                } else {
                    TokenType::Not
                }
            }
            "and" => TokenType::And,
            "or" => TokenType::Or,
            _ => TokenType::Identifier(text.to_string()),
        };
        self.add_token(kind);
        self.state = LexerState::Start;
    }

    fn handle_in_string(&mut self) -> Result<(), LexError> {
        loop {
            if let Some(c) = self.advance_char() {
                if c == '\"' {
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
                self.state = LexerState::Done;
                self.add_token(TokenType::Eof);
                return;
            }
        }
    }

    fn handle_in_symbol(&mut self) {
        if let Some(c) = self.advance_char() {
            match c {
                '=' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::EqualEqual);
                        } else {
                            self.add_token(TokenType::Equal);
                        }
                    } else {
                        self.add_token(TokenType::Equal);
                    }
                }
                '<' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::LessEqual);
                        } else if next == '<' {
                            self.advance_char();
                            self.add_token(TokenType::LeftShift);
                        } else {
                            self.add_token(TokenType::Less);
                        }
                    } else {
                        self.add_token(TokenType::Less);
                    }
                }
                '>' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::GreaterEqual);
                        } else if next == '>' {
                            self.advance_char();
                            self.add_token(TokenType::RightShift);
                        } else {
                            self.add_token(TokenType::Greater);
                        }
                    } else {
                        self.add_token(TokenType::Greater);
                    }
                }
                '!' => {
                    self.add_token(TokenType::Bang);
                }
                '+' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::PlusEqual);
                        } else {
                            self.add_token(TokenType::Plus);
                        }
                    } else {
                        self.add_token(TokenType::Plus);
                    }
                }
                '-' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::MinusEqual);
                        } else if next == '>' {
                            self.advance_char();
                            self.add_token(TokenType::Arrow);
                        } else {
                            self.add_token(TokenType::Minus);
                        }
                    } else {
                        self.add_token(TokenType::Minus);
                    }
                }
                '*' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::StarEqual);
                        } else {
                            self.add_token(TokenType::Star);
                        }
                    } else {
                        self.add_token(TokenType::Star);
                    }
                }
                '/' => {
                    if let Some(next) = self.peek_char() {
                        if next == '=' {
                            self.advance_char();
                            self.add_token(TokenType::SlashEqual);
                        } else {
                            self.add_token(TokenType::Slash);
                        }
                    } else {
                        self.add_token(TokenType::Slash);
                    }
                }
                '(' => self.add_token(TokenType::LParen),
                ')' => self.add_token(TokenType::RParen),
                '{' => self.add_token(TokenType::LBrace),
                '}' => self.add_token(TokenType::RBrace),
                '[' => self.add_token(TokenType::LBracket),
                ']' => self.add_token(TokenType::RBracket),
                ',' => self.add_token(TokenType::Comma),
                ';' => self.add_token(TokenType::Semicolon),
                ':' => self.add_token(TokenType::Colon),
                _ => self.add_token(TokenType::Unknown(c)),
            }
        } else {
            self.state = LexerState::Done;
            self.add_token(TokenType::Eof);
        }
        self.state = LexerState::Start;
    }
}