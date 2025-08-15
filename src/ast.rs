#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Literal values
    Number(i64),
    String(String),
    Identifier(String),

    // Binary operations: left op right
    Binary {
        left: Box<Expr>,
        operator: BinaryOp,
        right: Box<Expr>,
    },

    // Unary operations: op operand
    Unary {
        operator: UnaryOp,
        operand: Box<Expr>,
    },

    // Function calls: callee(args...)
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },

    // Grouping: (expression)
    Grouping(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    // Expression statement: expr;
    Expression(Expr),

    // Block statement: { statements... }
    Block(Vec<Stmt>),

    // Variable declaration: let name = value;
    VarDecl {
        name: String,
        initializer: Option<Expr>,
    },

    // Function declaration: fn name(params...) { body }
    FnDecl {
        name: String,
        params: Vec<String>,
        body: Box<Stmt>,
    },

    // Return statement: return expr?;
    Return(Option<Expr>),

    // If statement: if condition { then_branch } else { else_branch }?
    If {
        condition: Expr,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>,
    },

    // While loop: while condition { body }
    While {
        condition: Expr,
        body: Box<Stmt>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    // Arithmetic
    Add,        // +
    Subtract,   // -
    Multiply,   // *
    Divide,     // /

    // Assignment
    Assign,     // =

    // Comparison
    Equal,      // ==
    NotEqual,   // !=
    Less,       // <
    Greater,    // >
    LessEq,     // <=
    GreaterEq,  // >=

    // Logical
    And,        // &&
    Or,         // ||
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Negate,     // -
    Not,        // !
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