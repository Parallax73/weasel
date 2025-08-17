use miette::{Diagnostic, Report, SourceSpan};
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum AstError {
    #[error("Invalid operation")]
    #[diagnostic(code(ast::invalid_operation), help("This operation is not allowed here"))]
    InvalidOperation {
        #[label("invalid operation")]
        span: SourceSpan,
    },

    #[error("Unexpected expression")]
    #[diagnostic(code(ast::unexpected_expr))]
    UnexpectedExpr {
        #[label("here")]
        span: SourceSpan,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    String,
    Bool,
    Float,
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::String => write!(f, "string"),
            Type::Bool => write!(f, "bool"),
            Type::Float => write!(f, "float"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Number(i64),
    String(String),
    Boolean(bool),
    Float(f64),
    Null,
    Identifier(String),
    Array(Vec<Expr>),
    TypedArray {
        element_type: Type,
        elements: Vec<Expr>,
    },
    Index {
        array: Box<Expr>,
        index: Box<Expr>,
    },
    Binary {
        left: Box<Expr>,
        operator: BinaryOp,
        right: Box<Expr>,
    },
    Unary {
        operator: UnaryOp,
        operand: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },
    Grouping(Box<Expr>),
}

impl Expr {
    pub fn new_binary(
        left: Expr,
        operator: BinaryOp,
        right: Expr,
        span: SourceSpan,
    ) -> Result<Self, Report> {
        if let BinaryOp::Assign = operator {
            if matches!(left, Expr::Number(_) | Expr::String(_) | Expr::Identifier(_)) {
                return Ok(Expr::Binary {
                    left: Box::new(left),
                    operator,
                    right: Box::new(right),
                });
            } else {
                return Err(Report::new(AstError::InvalidOperation { span }));
            }
        }
        Ok(Expr::Binary {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        })
    }

    pub fn new_unary(operator: UnaryOp, operand: Expr, span: SourceSpan) -> Result<Self, Report> {
        Ok(Expr::Unary {
            operator,
            operand: Box::new(operand),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Expression(Expr),
    Block(Vec<Stmt>),
    VarDecl {
        name: String,
        initializer: Option<Expr>,
    },
    FnDecl {
        name: String,
        params: Vec<String>,
        body: Box<Stmt>,
    },
    Return(Option<Expr>),
    If {
        condition: Expr,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>,
    },
    While {
        condition: Expr,
        body: Box<Stmt>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Assign,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEq,
    GreaterEq,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Negate,
    Not,
}

impl std::fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            BinaryOp::Add => write!(f, "+"),
            BinaryOp::Subtract => write!(f, "-"),
            BinaryOp::Multiply => write!(f, "*"),
            BinaryOp::Divide => write!(f, "/"),
            BinaryOp::Assign => write!(f, "="),
            BinaryOp::Equal => write!(f, "=="),
            BinaryOp::NotEqual => write!(f, "!="),
            BinaryOp::Less => write!(f, "<"),
            BinaryOp::Greater => write!(f, ">"),
            BinaryOp::LessEq => write!(f, "<="),
            BinaryOp::GreaterEq => write!(f, ">="),
            BinaryOp::And => write!(f, "&&"),
            BinaryOp::Or => write!(f, "||"),
        }
    }
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            UnaryOp::Negate => write!(f, "-"),
            UnaryOp::Not => write!(f, "!"),
        }
    }
}
