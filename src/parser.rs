use crate::lex::{Token, TokenType};
use crate::ast::{Expr, Stmt, BinaryOp, UnaryOp, Type};
use miette::{Diagnostic, Result, SourceSpan, Report};
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum ParseError {
    #[error("Unexpected token: expected {expected}, found {found}")]
    #[diagnostic(code(parser::unexpected_token), help("Check if you're missing a token or have an extra one"))]
    UnexpectedToken {
        expected: String,
        found: String,
        #[label("unexpected token here")]
        span: SourceSpan,
    },
    #[error("Unexpected end of input")]
    #[diagnostic(code(parser::unexpected_eof), help("The input ended unexpectedly, you might be missing a closing bracket or semicolon"))]
    UnexpectedEof {
        #[label("input ended here")]
        span: SourceSpan,
    },
    #[error("Invalid expression")]
    #[diagnostic(code(parser::invalid_expr), help("This doesn't form a valid expression"))]
    InvalidExpression {
        #[label("invalid expression")]
        span: SourceSpan,
    },
    #[error("Type mismatch: expected {expected}, found {found}")]
    #[diagnostic(code(parser::type_mismatch), help("All elements in a typed array must match the declared type"))]
    TypeMismatch {
        expected: String,
        found: String,
        #[label("type mismatch here")]
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
}

pub struct Parser<'de> {
    tokens: Vec<Token<'de>>,
    current: usize,
}

impl<'de> Parser<'de> {
    pub fn new(tokens: Vec<Token<'de>>) -> Self {
        Self { tokens, current: 0 }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::new();
        while !self.check(&TokenType::Eof) {
            match self.parse_statement() {
                Ok(stmt) => statements.push(stmt),
                Err(e) => {
                    self.synchronize();
                    return Err(e.into());
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
        } else if self.match_token(&[TokenType::Let]) {
            let name = self.consume_identifier()?;
            let initializer = if self.match_token(&[TokenType::Equal]) {
                Some(self.parse_expression()?)
            } else {
                None
            };
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::VarDecl { name, initializer })
        } else if self.match_token(&[TokenType::Fn]) {
            let name = self.consume_identifier()?;
            self.consume(TokenType::LParen)?;
            let mut params = Vec::new();
            if !self.check(&TokenType::RParen) {
                loop {
                    let param_name = self.consume_identifier()?;
                    self.consume(TokenType::Colon)?;
                    let param_type = self.parse_type()?;
                    params.push((param_name, param_type));
                    if !self.match_token(&[TokenType::Comma]) {
                        break;
                    }
                }
            }
            self.consume(TokenType::RParen)?;
            let return_type = if self.match_token(&[TokenType::Arrow]) {
                self.parse_type()?
            } else {
                Type::Null
            };
            self.consume(TokenType::LBrace)?;
            let mut body_stmts = Vec::new();
            while !self.check(&TokenType::RBrace) && !self.is_at_end() {
                body_stmts.push(self.parse_statement()?);
            }
            self.consume(TokenType::RBrace)?;
            Ok(Stmt::FnDecl {
                name,
                params,
                body: Box::new(Stmt::Block(body_stmts)),
                return_type,
            })
        } else if self.match_token(&[TokenType::Return]) {
            let expr = if !self.check(&TokenType::Semicolon) {
                Some(self.parse_expression()?)
            } else {
                None
            };
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::Return(expr))
        } else if self.match_token(&[TokenType::If]) {
            let condition = self.parse_expression()?;
            let then_branch = Box::new(self.parse_statement()?);
            let else_branch = if self.match_token(&[TokenType::Else]) {
                Some(Box::new(self.parse_statement()?))
            } else {
                None
            };
            Ok(Stmt::If {
                condition,
                then_branch,
                else_branch,
            })
        } else if self.match_token(&[TokenType::While]) {
            let condition = self.parse_expression()?;
            let body = Box::new(self.parse_statement()?);
            Ok(Stmt::While { condition, body })
        } else if self.match_token(&[TokenType::Break]) {
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::Break)
        } else if self.match_token(&[TokenType::Continue]) {
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::Continue)
        } else {
            let expr = self.parse_expression()?;
            self.consume(TokenType::Semicolon)?;
            Ok(Stmt::Expression(expr))
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr> {
        self.parse_precedence(Precedence::None)
    }

    pub fn parse_precedence(&mut self, precedence: Precedence) -> Result<Expr> {
        let token = self.advance_or_eof()?;
        let token_span = token.span();

        if !self.has_prefix_rule(&token.kind) {
            return Err(Report::new(ParseError::InvalidExpression {
                span: token_span,
            }));
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
            TokenType::String(s) => Ok(Expr::String(s.to_string())),
            TokenType::StringLiteral(s) => Ok(Expr::String(s.to_string())),
            TokenType::Boolean(b) => Ok(Expr::Boolean(*b)),
            TokenType::True => Ok(Expr::Boolean(true)),
            TokenType::False => Ok(Expr::Boolean(false)),
            TokenType::Float(f) => Ok(Expr::Float(*f)),
            TokenType::Null => Ok(Expr::Null),
            TokenType::Identifier(s) => Ok(Expr::Identifier(s.clone())),
            TokenType::LBracket => self.parse_array(),
            TokenType::Less => self.parse_typed_array(),
            TokenType::LParen => {
                let expr = self.parse_expression()?;
                self.consume(TokenType::RParen)?;
                Ok(Expr::Grouping(Box::new(expr)))
            }
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
            _ => Err(Report::new(ParseError::InvalidExpression {
                span: token.span(),
            })),
        }
    }

    pub fn parse_array(&mut self) -> Result<Expr> {
        let mut elements = Vec::new();
        if self.check(&TokenType::RBracket) {
            self.advance();
            return Ok(Expr::Array(elements));
        }
        loop {
            elements.push(self.parse_expression()?);
            if self.match_token(&[TokenType::Comma]) {
                continue;
            } else if self.check(&TokenType::RBracket) {
                self.advance();
                break;
            } else {
                return Err(Report::new(ParseError::UnexpectedToken {
                    expected: "comma or ]".to_string(),
                    found: format!("{:?}", self.peek().map(|t| &t.kind)),
                    span: self.peek().map_or((0, 0).into(), |t| t.span()),
                }));
            }
        }
        Ok(Expr::Array(elements))
    }

    fn parse_typed_array(&mut self) -> Result<Expr> {
        let type_name = self.consume_identifier()?;
        self.consume(TokenType::Greater)?;
        let element_type = match type_name.as_str() {
            "int" => Type::Int,
            "string" => Type::String,
            "bool" => Type::Bool,
            "float" => Type::Float,
            "arr" => {
                self.consume(TokenType::Less)?;
                let inner_type_name = self.consume_identifier()?;
                self.consume(TokenType::Greater)?;
                match inner_type_name.as_str() {
                    "int" => Type::Arr(Box::new(Type::Int)),
                    "string" => Type::Arr(Box::new(Type::String)),
                    "bool" => Type::Arr(Box::new(Type::Bool)),
                    "float" => Type::Arr(Box::new(Type::Float)),
                    _ => {
                        return Err(Report::new(ParseError::InvalidExpression {
                            span: self.previous().unwrap().span(),
                        }))
                    }
                }
            }
            _ => {
                return Err(Report::new(ParseError::InvalidExpression {
                    span: self.previous().unwrap().span(),
                }))
            }
        };
        self.consume(TokenType::LBracket)?;
        let mut elements = Vec::new();
        if self.check(&TokenType::RBracket) {
            self.advance();
            return Ok(Expr::TypedArray {
                element_type,
                elements,
            });
        }
        loop {
            let element = self.parse_expression()?;
            if !self.element_matches_type(&element, &element_type) {
                return Err(Report::new(ParseError::TypeMismatch {
                    expected: element_type.to_string(),
                    found: format!("{:?}", element),
                    span: self.previous().unwrap().span(),
                }));
            }
            elements.push(element);
            if self.match_token(&[TokenType::Comma]) {
                continue;
            } else if self.check(&TokenType::RBracket) {
                self.advance();
                break;
            } else {
                return Err(Report::new(ParseError::UnexpectedToken {
                    expected: "comma or ]".to_string(),
                    found: format!("{:?}", self.peek().map(|t| &t.kind)),
                    span: self.peek().map_or((0, 0).into(), |t| t.span()),
                }));
            }
        }
        Ok(Expr::TypedArray {
            element_type,
            elements,
        })
    }

    fn element_matches_type(&self, expr: &Expr, expected_type: &Type) -> bool {
        match (expr, expected_type) {
            (Expr::Number(_), Type::Int) => true,
            (Expr::String(_), Type::String) => true,
            (Expr::Boolean(_), Type::Bool) => true,
            (Expr::Float(_), Type::Float) => true,
            _ => false,
        }
    }

    pub fn parse_infix(&mut self, left: Expr) -> Result<Expr> {
        let operator_token = self.advance_or_eof()?;
        match &operator_token.kind {
            TokenType::LBracket => {
                let index = self.parse_expression()?;
                self.consume(TokenType::RBracket)?;
                Ok(Expr::Index {
                    array: Box::new(left),
                    index: Box::new(index),
                })
            }
            TokenType::LParen => self.parse_call(left),
            _ => {
                let operator = Self::token_to_binary_op(&operator_token.kind);
                if let Some(op) = operator {
                    let precedence = Self::get_precedence(&operator_token.kind);
                    let right = self.parse_precedence(precedence)?;
                    Ok(Expr::Binary {
                        left: Box::new(left),
                        operator: op,
                        right: Box::new(right),
                    })
                } else {
                    Err(Report::new(ParseError::InvalidExpression {
                        span: operator_token.span(),
                    }))
                }
            }
        }
    }

    pub fn parse_call(&mut self, callee: Expr) -> Result<Expr> {
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

    fn parse_type(&mut self) -> Result<Type> {
        let type_name = self.consume_identifier()?;
        match type_name.as_str() {
            "int" => Ok(Type::Int),
            "string" => Ok(Type::String),
            "bool" => Ok(Type::Bool),
            "float" => Ok(Type::Float),
            "arr" => {
                self.consume(TokenType::Less)?;
                let inner_type = self.parse_type()?;
                self.consume(TokenType::Greater)?;
                Ok(Type::Arr(Box::new(inner_type)))
            }
            _ => Err(Report::new(ParseError::InvalidExpression {
                span: self.previous().unwrap().span(),
            })),
        }
    }

    fn advance_or_eof(&mut self) -> Result<Token<'de>> {
        match self.advance() {
            Some(t) => Ok(t.clone()),
            None => Err(Report::new(ParseError::UnexpectedEof {
                span: (0, 0).into(),
            })),
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
        let span = current_token.map_or_else(|| (0, 0).into(), |token| token.span());
        Err(Report::new(ParseError::UnexpectedToken {
            expected: "identifier".to_string(),
            found: current_token.map_or("EOF".to_string(), |t| format!("{:?}", t.kind)),
            span,
        }))
    }

    pub fn tokens_match(expected: &TokenType, actual: &TokenType) -> bool {
        match (expected, actual) {
            (TokenType::Number(_), TokenType::Number(_)) => true,
            (TokenType::Identifier(_), TokenType::Identifier(_)) => true,
            (TokenType::String(_), TokenType::String(_)) => true,
            (TokenType::StringLiteral(_), TokenType::StringLiteral(_)) => true,
            (TokenType::Boolean(_), TokenType::Boolean(_)) => true,
            (TokenType::Float(_), TokenType::Float(_)) => true,
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

    pub fn consume(&mut self, token_type: TokenType) -> Result<()> {
        if self.check(&token_type) {
            self.advance();
            Ok(())
        } else {
            let current_token = self.peek();
            let span = current_token.map_or_else(|| (0, 0).into(), |token| token.span());
            Err(Report::new(ParseError::UnexpectedToken {
                expected: format!("{:?}", token_type),
                found: current_token.map_or("EOF".to_string(), |t| format!("{:?}", t.kind)),
                span,
            }))
        }
    }

    pub fn synchronize(&mut self) {
        self.advance();
        while !self.is_at_end() {
            if let Some(prev) = self.previous() {
                if prev.kind == TokenType::Semicolon {
                    return;
                }
            }
            match self.peek() {
                Some(token) => match token.kind {
                    TokenType::Let | TokenType::Fn | TokenType::If | TokenType::While | TokenType::Return => return,
                    _ => {}
                },
                None => return,
            }
            self.advance();
        }
    }

    pub fn get_precedence(token_type: &TokenType) -> Precedence {
        match token_type {
            TokenType::Equal => Precedence::Assignment,
            TokenType::Or => Precedence::Or,
            TokenType::And => Precedence::And,
            TokenType::EqualEqual | TokenType::NotEqual => Precedence::Equality,
            TokenType::Less | TokenType::Greater | TokenType::LessEqual | TokenType::GreaterEqual => Precedence::Comparison,
            TokenType::Plus | TokenType::Minus => Precedence::Term,
            TokenType::Star | TokenType::Slash => Precedence::Factor,
            TokenType::LParen | TokenType::LBracket => Precedence::Call,
            _ => Precedence::None,
        }
    }

    pub fn has_prefix_rule(&self, token_type: &TokenType) -> bool {
        matches!(
            token_type,
            TokenType::Number(_)
                | TokenType::Identifier(_)
                | TokenType::LParen
                | TokenType::LBracket
                | TokenType::Less
                | TokenType::Minus
                | TokenType::Not
                | TokenType::String(_)
                | TokenType::StringLiteral(_)
                | TokenType::Boolean(_)
                | TokenType::True
                | TokenType::False
                | TokenType::Float(_)
                | TokenType::Null
        )
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
            TokenType::LessEqual => Some(BinaryOp::LessEq),
            TokenType::GreaterEqual => Some(BinaryOp::GreaterEq),
            TokenType::And => Some(BinaryOp::And),
            TokenType::Or => Some(BinaryOp::Or),
            TokenType::PlusEqual => Some(BinaryOp::AddAssign),
            TokenType::MinusEqual => Some(BinaryOp::SubtractAssign),
            TokenType::StarEqual => Some(BinaryOp::MultiplyAssign),
            TokenType::SlashEqual => Some(BinaryOp::DivideAssign),
            _ => None,
        }
    }
}