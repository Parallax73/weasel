use crate::lex::{Token, TokenType};
use crate::ast::{Expr, Stmt, BinaryOp, UnaryOp};
use miette::{Diagnostic, Result, SourceSpan};
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum ParseError {
    #[error("Unexpected token: expected {expected}, found {found}")]
    #[diagnostic(
        code(parser::unexpected_token),
        help("Check if you're missing a token or have an extra one")
    )]
    UnexpectedToken {
        expected: String,
        found: String,
        #[label("unexpected token here")]
        span: SourceSpan,
    },

    #[error("Unexpected end of input")]
    #[diagnostic(
        code(parser::unexpected_eof),
        help("The input ended unexpectedly, you might be missing a closing bracket or semicolon")
    )]
    UnexpectedEof {
        #[label("input ended here")]
        span: SourceSpan,
    },

    #[error("Invalid expression")]
    #[diagnostic(
        code(parser::invalid_expr),
        help("This doesn't form a valid expression")
    )]
    InvalidExpression {
        #[label("invalid expression")]
        span: SourceSpan,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    None = 0,
    Assignment = 1,
    Or = 2,
    And = 3,
    Equality = 4,
    Comparison = 5,
    Term = 6,
    Factor = 7,
    Unary = 8,
    Call = 9,
    Primary = 10,
}

pub struct Parser<'de> {
    tokens: Vec<Token<'de>>,
    current: usize,
    source: &'de str,
}

impl<'de> Parser<'de> {
    pub fn new(tokens: Vec<Token<'de>>, source: &'de str) -> Self {
        Self {
            tokens,
            current: 0,
            source,
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::new();
        while !self.is_at_end() {
            match self.parse_statement() {
                Ok(stmt) => statements.push(stmt),
                Err(e) => {
                    self.synchronize();
                    return Err(e);
                }
            }
        }
        Ok(statements)
    }

    pub fn parse_statement(&mut self) -> Result<Stmt> {
        if self.match_token(&[TokenType::LBrace]) {
            let mut statements = Vec::new();
            while !self.check(&TokenType::RBrace) && !self.is_at_end() {
                statements.push(self.parse_statement()?);
            }
            self.consume(TokenType::RBrace)?;
            Ok(Stmt::Block(statements))
        } else if self.check_identifier("let") {
            self.advance();
            let name = self.consume_identifier()?;
            let initializer = if self.match_token(&[TokenType::Equal]) {
                Some(self.parse_expression()?)
            } else {
                None
            };
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::VarDecl { name, initializer })
        } else if self.check_identifier("fn") {
            self.advance();
            let name = self.consume_identifier()?;
            self.consume(TokenType::LParen)?;
            let mut params = Vec::new();
            if !self.check(&TokenType::RParen) {
                loop {
                    let param = self.consume_identifier()?;
                    params.push(param);
                    if !self.match_token(&[TokenType::Comma]) {
                        break;
                    }
                }
            }
            self.consume(TokenType::RParen)?;
            self.consume(TokenType::LBrace)?;
            let body = Box::new(self.parse_statement()?);
            Ok(Stmt::FnDecl { name, params, body })
        } else if self.check_identifier("return") {
            self.advance();
            let expr = if !self.check(&TokenType::Semicolon) {
                Some(self.parse_expression()?)
            } else {
                None
            };
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::Return(expr))
        } else if self.check_identifier("if") {
            self.advance();
            let condition = self.parse_expression()?;
            self.consume(TokenType::LBrace)?;
            let then_branch = Box::new(self.parse_statement()?);
            let else_branch = if self.check_identifier("else") {
                self.advance();
                self.consume(TokenType::LBrace)?;
                Some(Box::new(self.parse_statement()?))
            } else {
                None
            };
            Ok(Stmt::If { condition, then_branch, else_branch })
        } else if self.check_identifier("while") {
            self.advance();
            let condition = self.parse_expression()?;
            self.consume(TokenType::LBrace)?;
            let body = Box::new(self.parse_statement()?);
            Ok(Stmt::While { condition, body })
        } else {
            let expr = self.parse_expression()?;
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::Expression(expr))
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr> {
        self.parse_precedence(Precedence::Assignment)
    }

    pub fn parse_precedence(&mut self, precedence: Precedence) -> Result<Expr> {
        let token = self.advance_or_eof()?;

        if !self.has_prefix_rule(&token.kind) {
            return Err(ParseError::InvalidExpression {
                span: SourceSpan::from(token.offset..token.offset + 1),
            }.into());
        }

        let mut left = self.parse_prefix()?;

        loop {
            let next_token = match self.peek() {
                Some(t) => t.clone(),
                None => break,
            };

            let next_precedence = Self::get_precedence(&next_token.kind);
            if next_precedence <= precedence {
                break;
            }
            left = self.parse_infix(left)?;
        }

        Ok(left)
    }

    pub fn parse_prefix(&mut self) -> Result<Expr> {
        let token = self.previous().unwrap();

        match &token.kind {
            TokenType::Number(n) => Ok(Expr::Number(*n)),
            TokenType::StringLiteral(s) => Ok(Expr::String(s.clone())),
            TokenType::Identifier(s) => {
                let mut expr = Expr::Identifier(s.clone());
                if self.check(&TokenType::LParen) {
                    expr = self.parse_call(expr)?;
                }
                Ok(expr)
            },
            TokenType::LParen => {
                let expr = self.parse_expression()?;
                self.consume(TokenType::RParen)?;
                Ok(Expr::Grouping(Box::new(expr)))
            },
            TokenType::Minus => {
                let operand = self.parse_precedence(Precedence::Unary)?;
                Ok(Expr::Unary {
                    operator: UnaryOp::Negate,
                    operand: Box::new(operand),
                })
            }
            TokenType::Not => {
                let operand = self.parse_precedence(Precedence::Unary)?;
                Ok(Expr::Unary {
                    operator: UnaryOp::Not,
                    operand: Box::new(operand),
                })
            }
            _ => {
                Err(ParseError::InvalidExpression {
                    span: SourceSpan::from(token.offset..token.offset + 1),
                }.into())
            }
        }
    }

    pub fn parse_infix(&mut self, left: Expr) -> Result<Expr> {
        let operator_token = self.advance_or_eof()?;

        if operator_token.kind == TokenType::LParen {
            return self.parse_call(left);
        }

        let operator = Self::token_to_binary_op(&operator_token.kind);
        if let Some(op) = operator {
            let precedence = if op == BinaryOp::Assign {
                Precedence::Assignment
            } else {
                Self::get_precedence(&operator_token.kind)
            };
            let right = self.parse_precedence(precedence)?;
            Ok(Expr::Binary {
                left: Box::new(left),
                operator: op,
                right: Box::new(right),
            })
        } else {
            Err(ParseError::InvalidExpression {
                span: SourceSpan::from(operator_token.offset..operator_token.offset + 1),
            }.into())
        }
    }

    pub fn parse_call(&mut self, callee: Expr) -> Result<Expr> {
        self.consume(TokenType::LParen)?;
        let mut arguments = Vec::new();
        if !self.check(&TokenType::RParen) {
            loop {
                arguments.push(self.parse_expression()?);
                if !self.match_token(&[TokenType::Comma]) {
                    break;
                }
            }
        }
        self.consume(TokenType::RParen)?;
        Ok(Expr::Call {
            callee: Box::new(callee),
            arguments,
        })
    }

    fn advance_or_eof(&mut self) -> Result<Token<'de>> {
        match self.advance() {
            Some(t) => Ok(t.clone()),
            None => {
                let source_len = self.source.len();
                Err(ParseError::UnexpectedEof {
                    span: SourceSpan::from(source_len..source_len),
                }.into())
            }
        }
    }

    pub fn advance(&mut self) -> Option<&Token<'de>> {
        if self.is_at_end() {
            None
        } else {
            self.current += 1;
            self.previous()
        }
    }

    pub fn peek(&self) -> Option<&Token<'de>> {
        self.tokens.get(self.current)
    }

    pub fn previous(&self) -> Option<&Token<'de>> {
        if self.current > 0 {
            self.tokens.get(self.current - 1)
        } else {
            None
        }
    }

    pub fn is_at_end(&self) -> bool {
        self.current >= self.tokens.len()
    }

    pub fn check(&self, token_type: &TokenType) -> bool {
        match self.peek() {
            Some(token) => Self::tokens_match(token_type, &token.kind),
            None => false,
        }
    }

    pub fn check_identifier(&self, expected: &str) -> bool {
        match self.peek() {
            Some(token) => matches!(&token.kind, TokenType::Identifier(s) if s == expected),
            None => false,
        }
    }

    pub fn consume_identifier(&mut self) -> Result<String> {
        if let Some(token) = self.peek() {
            if let TokenType::Identifier(s) = &token.kind {
                let result = s.clone();
                self.advance();
                return Ok(result);
            }
        }

        let current_token = self.peek();
        let source_len = self.source.len();
        let span = current_token.map_or_else(
            || SourceSpan::from(source_len..source_len),
            |token| SourceSpan::from(token.offset..token.offset + 1),
        );
        Err(ParseError::UnexpectedToken {
            expected: "identifier".to_string(),
            found: current_token.map_or("EOF".to_string(), |t| format!("{:?}", t.kind)),
            span,
        }.into())
    }

    pub fn tokens_match(expected: &TokenType, actual: &TokenType) -> bool {
        match (expected, actual) {
            (TokenType::Number(_), TokenType::Number(_)) => true,
            (TokenType::Identifier(_), TokenType::Identifier(_)) => true,
            (TokenType::StringLiteral(_), TokenType::StringLiteral(_)) => true,
            _ => std::mem::discriminant(expected) == std::mem::discriminant(actual),
        }
    }

    pub fn match_token(&mut self, types: &[TokenType]) -> bool {
        for token_type in types {
            if self.check(token_type) {
                self.advance();
                return true;
            }
        }
        false
    }

    pub fn consume(&mut self, expected: TokenType) -> Result<&Token<'de>> {
        if self.check(&expected) {
            Ok(self.advance().unwrap())
        } else {
            let current_token = self.peek();
            let source_len = self.source.len();
            let span = current_token.map_or_else(
                || SourceSpan::from(source_len..source_len),
                |token| SourceSpan::from(token.offset..token.offset + 1),
            );
            Err(ParseError::UnexpectedToken {
                expected: format!("{:?}", expected),
                found: current_token.map_or("EOF".to_string(), |t| format!("{:?}", t.kind)),
                span,
            }.into())
        }
    }

    pub fn get_precedence(token_type: &TokenType) -> Precedence {
        match token_type {
            TokenType::Plus | TokenType::Minus => Precedence::Term,
            TokenType::Star | TokenType::Slash => Precedence::Factor,
            TokenType::Equal => Precedence::Assignment,
            TokenType::EqualEqual | TokenType::NotEqual => Precedence::Equality,
            TokenType::Less | TokenType::Greater | TokenType::LessEq | TokenType::GreaterEq => Precedence::Comparison,
            TokenType::And => Precedence::And,
            TokenType::Or => Precedence::Or,
            TokenType::LParen => Precedence::Call,
            TokenType::Number(_) | TokenType::Identifier(_) | TokenType::StringLiteral(_) => Precedence::Primary,
            _ => Precedence::None,
        }
    }

    pub fn has_prefix_rule(&self, token_type: &TokenType) -> bool {
        matches!(token_type,
            TokenType::Number(_) |
            TokenType::Identifier(_) |
            TokenType::Minus |
            TokenType::Not |
            TokenType::LParen |
            TokenType::StringLiteral(_)
        )
    }

    pub fn synchronize(&mut self) {
        while !self.is_at_end() {
            if let Some(prev) = self.previous() {
                if matches!(prev.kind, TokenType::Semicolon) {
                    return;
                }
            }
            if let Some(current) = self.peek() {
                if let TokenType::Identifier(s) = &current.kind {
                    if matches!(s.as_str(), "let" | "fn" | "return" | "if" | "while") {
                        return;
                    }
                }
            }
            self.advance();
        }
    }

    pub fn token_to_binary_op(token_type: &TokenType) -> Option<BinaryOp> {
        match token_type {
            TokenType::Plus => Some(BinaryOp::Add),
            TokenType::Minus => Some(BinaryOp::Subtract),
            TokenType::Star => Some(BinaryOp::Multiply),
            TokenType::Slash => Some(BinaryOp::Divide),
            TokenType::Equal => Some(BinaryOp::Assign),
            TokenType::EqualEqual => Some(BinaryOp::Equal),
            TokenType::NotEqual => Some(BinaryOp::NotEqual),
            TokenType::Less => Some(BinaryOp::Less),
            TokenType::Greater => Some(BinaryOp::Greater),
            TokenType::LessEq => Some(BinaryOp::LessEq),
            TokenType::GreaterEq => Some(BinaryOp::GreaterEq),
            TokenType::And => Some(BinaryOp::And),
            TokenType::Or => Some(BinaryOp::Or),
            _ => None,
        }
    }
}
