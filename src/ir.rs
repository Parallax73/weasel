use crate::ast::{BinaryOp, Expr, Stmt, Type, UnaryOp};
use miette::Report;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(i64),
    String(String),
    Boolean(bool),
    Float(f64),
    Null,
    Array(Vec<Value>),
    TypedArray {
        element_type: Type,
        elements: Vec<Value>,
    },
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "{}", s),
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Null => write!(f, "null"),
            Value::Array(arr) => {
                write!(f, "[")?;
                for (i, val) in arr.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", val)?;
                }
                write!(f, "]")
            }
            Value::TypedArray { element_type, elements } => {
                write!(f, "<{}>[", element_type)?;
                for (i, val) in elements.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", val)?;
                }
                write!(f, "]")
            }
        }
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum Opcode {
    PushNumber(i64),
    PushString(String),
    PushBoolean(bool),
    PushNull,
    CreateArray(usize),
    CreateTypedArray(Type, usize),
    GetIndex,
    SetIndex,
    Negate,
    Add,
    Subtract,
    Multiply,
    Divide,
    Store(String),
    Load(String),
    Sum(usize),
    Print,
    Halt,
}

pub struct CodeGen {
    instructions: Vec<Opcode>,
    variables: HashMap<String, Value>,
}

impl CodeGen {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            variables: HashMap::new(),
        }
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<(), Report> {
        match expr {
            Expr::Number(n) => self.instructions.push(Opcode::PushNumber(*n)),
            Expr::String(s) => self.instructions.push(Opcode::PushString(s.clone())),
            Expr::Boolean(b) => self.instructions.push(Opcode::PushBoolean(*b)),
            Expr::Null => self.instructions.push(Opcode::PushNull),
            Expr::Float(f) => {
                // For now, treat floats as numbers - you might want to add PushFloat opcode
                self.instructions.push(Opcode::PushNumber(*f as i64))
            },
            Expr::Identifier(name) => self.instructions.push(Opcode::Load(name.clone())),
            Expr::Array(elements) => {
                for element in elements {
                    self.compile_expr(element)?;
                }
                self.instructions.push(Opcode::CreateArray(elements.len()));
            }
            Expr::TypedArray { element_type, elements } => {
                for element in elements {
                    self.compile_expr(element)?;
                }
                self.instructions.push(Opcode::CreateTypedArray(element_type.clone(), elements.len()));
            }
            Expr::Index { array, index } => {
                self.compile_expr(array)?;
                self.compile_expr(index)?;
                self.instructions.push(Opcode::GetIndex);
            }
            Expr::Unary { operator, operand } => {
                self.compile_expr(operand)?;
                match operator {
                    UnaryOp::Negate => self.instructions.push(Opcode::Negate),
                    _ => return Err(Report::msg("Unsupported unary operator for compilation")),
                }
            }
            Expr::Binary {
                left,
                operator,
                right,
            } => {
                if matches!(operator, BinaryOp::Assign) {
                    if let Expr::Identifier(name) = left.as_ref() {
                        self.compile_expr(right)?;
                        self.instructions.push(Opcode::Store(name.clone()));
                    } else if let Expr::Index { array, index } = left.as_ref() {
                        self.compile_expr(array)?;
                        self.compile_expr(index)?;
                        self.compile_expr(right)?;
                        self.instructions.push(Opcode::SetIndex);
                    } else {
                        return Err(Report::msg("Invalid assignment target"));
                    }
                } else {
                    self.compile_expr(left)?;
                    self.compile_expr(right)?;
                    match operator {
                        BinaryOp::Add => self.instructions.push(Opcode::Add),
                        BinaryOp::Subtract => self.instructions.push(Opcode::Subtract),
                        BinaryOp::Multiply => self.instructions.push(Opcode::Multiply),
                        BinaryOp::Divide => self.instructions.push(Opcode::Divide),
                        _ => return Err(Report::msg("Unsupported binary operator for compilation")),
                    }
                }
            }
            Expr::Call { callee, arguments } => {
                if let Expr::Identifier(name) = callee.as_ref() {
                    if name == "sum" {
                        let arg_count = arguments.len();
                        for arg in arguments {
                            self.compile_expr(arg)?;
                        }
                        self.instructions.push(Opcode::Sum(arg_count));
                    } else if name == "print" {
                        if arguments.len() != 1 {
                            return Err(Report::msg("Print statement expects exactly one argument"));
                        }
                        self.compile_expr(&arguments[0])?;
                        self.instructions.push(Opcode::Print);
                    } else {
                        return Err(Report::msg(format!("Unknown function: {}", name)));
                    }
                } else {
                    return Err(Report::msg("Call callee must be an identifier"));
                }
            }
            Expr::Grouping(inner) => self.compile_expr(inner)?,
        }
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt) -> Result<(), Report> {
        match stmt {
            Stmt::Expression(expr) => self.compile_expr(expr)?,
            Stmt::VarDecl { name, initializer } => {
                if let Some(value) = initializer {
                    self.compile_expr(value)?;
                    self.instructions.push(Opcode::Store(name.clone()));
                }
            }
            _ => return Err(Report::msg("Unsupported statement type")),
        }
        Ok(())
    }

    pub fn compile_ast(&mut self, stmts: &Vec<Stmt>) -> Result<(), Report> {
        for stmt in stmts {
            self.compile_stmt(stmt)?;
        }
        self.instructions.push(Opcode::Halt);
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), Report> {
        let mut pc = 0;
        let mut stack: Vec<Value> = Vec::new();

        while pc < self.instructions.len() {
            let opcode = &self.instructions[pc];
            pc += 1;

            match opcode {
                Opcode::PushNumber(n) => stack.push(Value::Number(*n)),
                Opcode::PushString(s) => stack.push(Value::String(s.clone())),
                Opcode::PushBoolean(b) => stack.push(Value::Boolean(*b)),
                Opcode::PushNull => stack.push(Value::Null),
                Opcode::CreateArray(count) => {
                    let mut elements = Vec::new();
                    for _ in 0..*count {
                        elements.push(stack.pop().ok_or(Report::msg("Stack underflow"))?);
                    }
                    elements.reverse();
                    stack.push(Value::Array(elements));
                }
                Opcode::CreateTypedArray(element_type, count) => {
                    let mut elements = Vec::new();

                    for _ in 0..*count {
                        let element = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                        elements.push(element);
                    }
                    elements.reverse();

                    stack.push(Value::TypedArray {
                        element_type: element_type.clone(),
                        elements
                    });
                }
                Opcode::GetIndex => {
                    let index = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let array = stack.pop().ok_or(Report::msg("Stack underflow"))?;

                    match (array, index) {
                        (Value::Array(arr), Value::Number(idx)) => {
                            let i = idx as usize;
                            if i < arr.len() {
                                stack.push(arr[i].clone());
                            } else {
                                return Err(Report::msg("Array index out of bounds"));
                            }
                        }
                        (Value::TypedArray { elements, .. }, Value::Number(idx)) => {
                            let i = idx as usize;
                            if i < elements.len() {
                                stack.push(elements[i].clone());
                            } else {
                                return Err(Report::msg("Array index out of bounds"));
                            }
                        }
                        _ => return Err(Report::msg("Invalid array indexing")),
                    }
                }
                Opcode::SetIndex => {
                    let value = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let index = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let array = stack.pop().ok_or(Report::msg("Stack underflow"))?;

                    match (array, index) {
                        (Value::Array(mut arr), Value::Number(idx)) => {
                            let i = idx as usize;
                            if i < arr.len() {
                                arr[i] = value;
                                stack.push(Value::Array(arr));
                            } else {
                                return Err(Report::msg("Array index out of bounds"));
                            }
                        }
                        (Value::TypedArray { element_type, mut elements }, Value::Number(idx)) => {
                            let i = idx as usize;
                            if i < elements.len() {
                                // Type check assignment - warn but allow mismatches
                                if !self.value_matches_type(&value, &element_type) {
                                    println!("Warning: Type mismatch in assignment - expected {}, got {:?}",
                                             element_type, value);
                                }
                                elements[i] = value;
                                stack.push(Value::TypedArray { element_type, elements });
                            } else {
                                return Err(Report::msg("Array index out of bounds"));
                            }
                        }
                        _ => return Err(Report::msg("Invalid array indexing")),
                    }
                }
                Opcode::Negate => {
                    let value = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    match value {
                        Value::Number(n) => stack.push(Value::Number(-n)),
                        _ => return Err(Report::msg("Cannot negate non-number")),
                    }
                }
                Opcode::Add => {
                    let right = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Number(a + b)),
                        (Value::String(a), Value::String(b)) => stack.push(Value::String(format!("{}{}", a, b))),
                        _ => return Err(Report::msg("Cannot add incompatible types")),
                    }
                }
                Opcode::Subtract => {
                    let right = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Number(a - b)),
                        _ => return Err(Report::msg("Cannot subtract non-numbers")),
                    }
                }
                Opcode::Multiply => {
                    let right = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Number(a * b)),
                        _ => return Err(Report::msg("Cannot multiply non-numbers")),
                    }
                }
                Opcode::Divide => {
                    let right = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => {
                            if b == 0 {
                                return Err(Report::msg("Division by zero"));
                            }
                            stack.push(Value::Number(a / b))
                        },
                        _ => return Err(Report::msg("Cannot divide non-numbers")),
                    }
                }
                Opcode::Store(name) => {
                    let value = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    self.variables.insert(name.clone(), value);
                }
                Opcode::Load(name) => {
                    let value = self.variables.get(name).ok_or(Report::msg(
                        format!("Variable '{}' not found", name),
                    ))?.clone();
                    stack.push(value);
                }
                Opcode::Sum(arg_count) => {
                    let mut sum = 0;
                    for _ in 0..*arg_count {
                        match stack.pop().ok_or(Report::msg("Stack underflow"))? {
                            Value::Number(n) => sum += n,
                            _ => return Err(Report::msg("Sum can only operate on numbers")),
                        }
                    }
                    stack.push(Value::Number(sum));
                }
                Opcode::Print => {
                    let value = stack.pop().ok_or(Report::msg("Stack underflow"))?;
                    println!("{}", value);
                }
                Opcode::Halt => {
                    return Ok(());
                }
            }
        }

        Ok(())
    }

    fn value_matches_type(&self, value: &Value, expected_type: &Type) -> bool {
        match (value, expected_type) {
            (Value::Number(_), Type::Int) => true,
            (Value::String(_), Type::String) => true,
            (Value::Boolean(_), Type::Bool) => true,
            (Value::Float(_), Type::Float) => true,
            _ => false,
        }
    }
}