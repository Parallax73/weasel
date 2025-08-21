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
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", val)?;
                }
                write!(f, "]")
            }
            Value::TypedArray {
                element_type,
                elements,
            } => {
                write!(f, "<{}>[", element_type)?;
                for (i, val) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", val)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl Value {
    fn is_truthy(&self) -> bool {
        match self {
            Value::Boolean(b) => *b,
            Value::Null => false,
            Value::Number(n) => *n != 0,
            Value::String(s) => !s.is_empty(),
            Value::Array(arr) => !arr.is_empty(),
            Value::TypedArray { elements, .. } => !elements.is_empty(),
            Value::Float(f) => *f != 0.0,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Opcode {
    PushNumber(i64),
    PushString(String),
    PushBoolean(bool),
    PushFloat(f64),
    PushNull,
    CreateArray(usize),
    CreateTypedArray(Type, usize),
    GetIndex,
    SetIndex,
    Negate,
    Not,
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEq,
    GreaterEq,
    And,
    Or,
    Store(String),
    Load(String),
    Sum(usize),
    Print,
    Jump(usize),
    JumpIfFalse(usize),
    JumpIfTrue(usize),
    Pop,
    Return,
    Halt,
    Break,
    Continue,
}

pub struct CodeGen {
    instructions: Vec<Opcode>,
    variables: HashMap<String, Value>,
    loop_start_stack: Vec<usize>,
    loop_end_stack: Vec<usize>,
}

impl CodeGen {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            variables: HashMap::new(),
            loop_start_stack: Vec::new(),
            loop_end_stack: Vec::new(),
        }
    }

    fn emit(&mut self, opcode: Opcode) {
        self.instructions.push(opcode);
    }

    fn current_address(&self) -> usize {
        self.instructions.len()
    }

    fn patch_jump(&mut self, jump_addr: usize, target: usize) {
        match &mut self.instructions[jump_addr] {
            Opcode::Jump(addr) => *addr = target,
            Opcode::JumpIfFalse(addr) => *addr = target,
            Opcode::JumpIfTrue(addr) => *addr = target,
            _ => panic!("Attempted to patch non-jump instruction"),
        }
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<(), Report> {
        match expr {
            Expr::Number(n) => self.emit(Opcode::PushNumber(*n)),
            Expr::String(s) => self.emit(Opcode::PushString(s.clone())),
            Expr::Boolean(b) => self.emit(Opcode::PushBoolean(*b)),
            Expr::Null => self.emit(Opcode::PushNull),
            Expr::Float(f) => self.emit(Opcode::PushFloat(*f)),
            Expr::Identifier(name) => self.emit(Opcode::Load(name.clone())),
            Expr::TypedArray {
                element_type,
                elements,
            } => {
                for element in elements {
                    self.compile_expr(element)?;
                }
                self.emit(Opcode::CreateTypedArray(element_type.clone(), elements.len()));
            }
            Expr::Array(elements) => {
                for element in elements {
                    self.compile_expr(element)?;
                }
                self.emit(Opcode::CreateArray(elements.len()));
            }
            Expr::Index { array, index } => {
                self.compile_expr(array)?;
                self.compile_expr(index)?;
                self.emit(Opcode::GetIndex);
            }
            Expr::Unary { operator, operand } => {
                self.compile_expr(operand)?;
                match operator {
                    UnaryOp::Negate => self.emit(Opcode::Negate),
                    UnaryOp::Not => self.emit(Opcode::Not),
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
                        self.emit(Opcode::Store(name.clone()));
                    } else if let Expr::Index { array, index } = left.as_ref() {
                        self.compile_expr(array)?;
                        self.compile_expr(index)?;
                        self.compile_expr(right)?;
                        self.emit(Opcode::SetIndex);
                    } else {
                        return Err(Report::msg("Invalid assignment target"));
                    }
                } else {
                    match operator {
                        BinaryOp::And => {
                            self.compile_expr(left)?;
                            let jump_addr = self.current_address();
                            self.emit(Opcode::JumpIfFalse(0));
                            self.compile_expr(right)?;
                            let end_addr = self.current_address();
                            self.patch_jump(jump_addr, end_addr);
                        }
                        BinaryOp::Or => {
                            self.compile_expr(left)?;
                            let jump_addr = self.current_address();
                            self.emit(Opcode::JumpIfTrue(0));
                            self.compile_expr(right)?;
                            let end_addr = self.current_address();
                            self.patch_jump(jump_addr, end_addr);
                        }
                        _ => {
                            self.compile_expr(left)?;
                            self.compile_expr(right)?;
                            match operator {
                                BinaryOp::Add => self.emit(Opcode::Add),
                                BinaryOp::Subtract => self.emit(Opcode::Subtract),
                                BinaryOp::Multiply => self.emit(Opcode::Multiply),
                                BinaryOp::Divide => self.emit(Opcode::Divide),
                                BinaryOp::Equal => self.emit(Opcode::Equal),
                                BinaryOp::NotEqual => self.emit(Opcode::NotEqual),
                                BinaryOp::Less => self.emit(Opcode::Less),
                                BinaryOp::Greater => self.emit(Opcode::Greater),
                                BinaryOp::LessEq => self.emit(Opcode::LessEq),
                                BinaryOp::GreaterEq => self.emit(Opcode::GreaterEq),
                                _ => {
                                    return Err(Report::msg(
                                        "Unsupported binary operator for compilation",
                                    ))
                                }
                            }
                        }
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
                        self.emit(Opcode::Sum(arg_count));
                    } else if name == "print" {
                        if arguments.len() != 1 {
                            return Err(Report::msg(
                                "Print statement expects exactly one argument",
                            ));
                        }
                        self.compile_expr(&arguments[0])?;
                        self.emit(Opcode::Print);
                    } else if name == "str" {
                        if arguments.len() != 1 {
                            return Err(Report::msg("str() expects exactly one argument"));
                        }
                        self.compile_expr(&arguments[0])?;
                    } else if name == "int" {
                        if arguments.len() != 1 {
                            return Err(Report::msg("int() expects exactly one argument"));
                        }
                        self.compile_expr(&arguments[0])?;
                    } else if name == "float" {
                        if arguments.len() != 1 {
                            return Err(Report::msg("float() expects exactly one argument"));
                        }
                        self.compile_expr(&arguments[0])?;
                    } else if name == "bool" {
                        if arguments.len() != 1 {
                            return Err(Report::msg("bool() expects exactly one argument"));
                        }
                        self.compile_expr(&arguments[0])?;
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
            Stmt::Expression(expr) => {
                self.compile_expr(expr)?;

                let should_pop = match expr {
                    Expr::Binary { operator, .. } if *operator == BinaryOp::Assign => false,
                    Expr::Call { callee, .. } => {
                        if let Expr::Identifier(name) = &**callee {
                            name != "print"
                        } else {
                            true
                        }
                    }
                    _ => true,
                };

                if should_pop {
                    self.emit(Opcode::Pop);
                }
            }
            Stmt::Block(stmts) => {
                for stmt in stmts {
                    self.compile_stmt(stmt)?;
                }
            }
            Stmt::VarDecl { name, initializer } => {
                if let Some(init) = initializer {
                    match init {
                        Expr::TypedArray {
                            element_type,
                            elements,
                        } => {
                            for element in elements {
                                self.compile_expr(element)?;
                            }
                            self.emit(Opcode::CreateTypedArray(
                                element_type.clone(),
                                elements.len(),
                            ));
                        }
                        Expr::Array(elements) => {
                            for element in elements {
                                self.compile_expr(element)?;
                            }
                            self.emit(Opcode::CreateArray(elements.len()));
                        }
                        _ => {
                            self.compile_expr(init)?;
                        }
                    }
                    self.emit(Opcode::Store(name.clone()));
                }
            }
            Stmt::FnDecl { .. } => {}
            Stmt::Return(expr) => {
                if let Some(e) = expr {
                    self.compile_expr(e)?;
                }
                self.emit(Opcode::Return);
            }
            Stmt::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.compile_expr(condition)?;
                let else_jump = self.current_address();
                self.emit(Opcode::JumpIfFalse(0));
                self.compile_stmt(then_branch)?;
                if let Some(else_stmt) = else_branch {
                    let end_jump = self.current_address();
                    self.emit(Opcode::Jump(0));
                    let else_start = self.current_address();
                    self.patch_jump(else_jump, else_start);
                    self.compile_stmt(else_stmt)?;
                    let end_addr = self.current_address();
                    self.patch_jump(end_jump, end_addr);
                } else {
                    let end_addr = self.current_address();
                    self.patch_jump(else_jump, end_addr);
                }
            }
            Stmt::While { condition, body } => {
                let loop_start = self.current_address();
                self.loop_start_stack.push(loop_start);

                self.compile_expr(condition)?;
                let end_jump = self.current_address();
                self.emit(Opcode::JumpIfFalse(0));

                self.loop_end_stack.push(0);
                self.compile_stmt(body)?;
                self.emit(Opcode::Jump(loop_start));

                let end_addr = self.current_address();
                self.patch_jump(end_jump, end_addr);

                if let Some(end_pos) = self.loop_end_stack.pop() {
                    if end_pos != 0 {
                        self.patch_jump(end_pos, end_addr);
                    }
                }
                self.loop_start_stack
                    .pop()
                    .ok_or_else(|| Report::msg("Loop stack underflow"))?;
            }
            Stmt::Break => {
                let jump_addr = self.current_address();
                self.emit(Opcode::Jump(0));
                if let Some(end_pos) = self.loop_end_stack.last_mut() {
                    *end_pos = jump_addr;
                } else {
                    return Err(Report::msg("Break outside loop"));
                }
            }
            Stmt::Continue => {
                if let Some(start) = self.loop_start_stack.last() {
                    self.emit(Opcode::Jump(*start));
                } else {
                    return Err(Report::msg("Continue outside loop"));
                }
            }
        }
        Ok(())
    }

    pub fn compile_ast(&mut self, stmts: &[Stmt]) -> Result<(), Report> {
        for stmt in stmts {
            self.compile_stmt(stmt)?;
        }
        self.emit(Opcode::Halt);
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), Report> {
        let mut stack: Vec<Value> = Vec::new();
        let mut pc = 0;

        while pc < self.instructions.len() {
            let opcode = self.instructions[pc].clone();
            pc += 1;

            match opcode {
                Opcode::PushNumber(n) => stack.push(Value::Number(n)),
                Opcode::PushString(s) => stack.push(Value::String(s)),
                Opcode::PushBoolean(b) => stack.push(Value::Boolean(b)),
                Opcode::PushFloat(f) => stack.push(Value::Float(f)),
                Opcode::PushNull => stack.push(Value::Null),
                Opcode::CreateArray(len) => {
                    let mut arr = Vec::with_capacity(len);
                    for _ in 0..len {
                        let val = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                        arr.push(val);
                    }
                    arr.reverse();
                    stack.push(Value::Array(arr));
                }
                Opcode::CreateTypedArray(element_type, len) => {
                    let mut elements = Vec::with_capacity(len);
                    for _ in 0..len {
                        let val = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                        elements.push(val);
                    }
                    elements.reverse();
                    stack.push(Value::TypedArray {
                        element_type,
                        elements,
                    });
                }
                Opcode::GetIndex => {
                    let index = stack
                        .pop()
                        .ok_or_else(|| Report::msg("Stack underflow"))?;
                    let array = stack
                        .pop()
                        .ok_or_else(|| Report::msg("Stack underflow"))?;
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
                    let value = stack
                        .pop()
                        .ok_or_else(|| Report::msg("Stack underflow"))?;
                    let index = stack
                        .pop()
                        .ok_or_else(|| Report::msg("Stack underflow"))?;
                    let array = stack
                        .pop()
                        .ok_or_else(|| Report::msg("Stack underflow"))?;

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
                        (
                            Value::TypedArray {
                                element_type,
                                mut elements,
                            },
                            Value::Number(idx),
                        ) => {
                            let i = idx as usize;
                            if i < elements.len() {
                                if !self.value_matches_type(&value, &element_type) {
                                    println!(
                                        "Warning: Type mismatch in assignment - expected {}, got {:?}",
                                        element_type, value
                                    );
                                }
                                elements[i] = value;
                                stack.push(Value::TypedArray {
                                    element_type,
                                    elements,
                                });
                            } else {
                                return Err(Report::msg("Array index out of bounds"));
                            }
                        }
                        _ => return Err(Report::msg("Invalid array indexing")),
                    }
                }
                Opcode::Negate => {
                    let value = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match value {
                        Value::Number(n) => stack.push(Value::Number(-n)),
                        Value::Float(f) => stack.push(Value::Float(-f)),
                        _ => return Err(Report::msg("Cannot negate non-number")),
                    }
                }
                Opcode::Not => {
                    let value = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    stack.push(Value::Boolean(!value.is_truthy()));
                }
                Opcode::Add => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Number(a + b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Float(a + b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Float(a as f64 + b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Float(a + b as f64))
                        }
                        (Value::String(a), Value::String(b)) => {
                            stack.push(Value::String(format!("{}{}", a, b)))
                        }
                        _ => return Err(Report::msg("Cannot add incompatible types")),
                    }
                }
                Opcode::Subtract => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Number(a - b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Float(a - b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Float(a as f64 - b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Float(a - b as f64))
                        }
                        _ => return Err(Report::msg("Cannot subtract non-numbers")),
                    }
                }
                Opcode::Multiply => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Number(a * b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Float(a * b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Float(a as f64 * b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Float(a * b as f64))
                        }
                        _ => return Err(Report::msg("Cannot multiply non-numbers")),
                    }
                }
                Opcode::Divide => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => {
                            if b == 0 {
                                return Err(Report::msg("Division by zero"));
                            }
                            stack.push(Value::Number(a / b))
                        }
                        (Value::Float(a), Value::Float(b)) => {
                            if b == 0.0 {
                                return Err(Report::msg("Division by zero"));
                            }
                            stack.push(Value::Float(a / b))
                        }
                        (Value::Number(a), Value::Float(b)) => {
                            if b == 0.0 {
                                return Err(Report::msg("Division by zero"));
                            }
                            stack.push(Value::Float(a as f64 / b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            if b == 0 {
                                return Err(Report::msg("Division by zero"));
                            }
                            stack.push(Value::Float(a / b as f64))
                        }
                        _ => return Err(Report::msg("Cannot divide non-numbers")),
                    }
                }
                Opcode::Equal => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    stack.push(Value::Boolean(left == right));
                }
                Opcode::NotEqual => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    stack.push(Value::Boolean(left != right));
                }
                Opcode::Less => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Boolean(a < b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Boolean(a < b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Boolean((a as f64) < b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Boolean(a < (b as f64)))
                        }
                        _ => return Err(Report::msg("Cannot compare non-numbers")),
                    }
                }
                Opcode::Greater => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Boolean(a > b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Boolean(a > b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Boolean((a as f64) > b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Boolean(a > (b as f64)))
                        }
                        _ => return Err(Report::msg("Cannot compare non-numbers")),
                    }
                }
                Opcode::LessEq => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Boolean(a <= b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Boolean(a <= b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Boolean((a as f64) <= b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Boolean(a <= (b as f64)))
                        }
                        _ => return Err(Report::msg("Cannot compare non-numbers")),
                    }
                }
                Opcode::GreaterEq => {
                    let right = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    let left = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    match (left, right) {
                        (Value::Number(a), Value::Number(b)) => stack.push(Value::Boolean(a >= b)),
                        (Value::Float(a), Value::Float(b)) => stack.push(Value::Boolean(a >= b)),
                        (Value::Number(a), Value::Float(b)) => {
                            stack.push(Value::Boolean((a as f64) >= b))
                        }
                        (Value::Float(a), Value::Number(b)) => {
                            stack.push(Value::Boolean(a >= (b as f64)))
                        }
                        _ => return Err(Report::msg("Cannot compare non-numbers")),
                    }
                }
                Opcode::And | Opcode::Or => {
                    return Err(Report::msg(
                        "Logical operators should use short-circuit evaluation",
                    ));
                }
                Opcode::Store(name) => {
                    let value = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    self.variables.insert(name.clone(), value);
                }
                Opcode::Load(name) => {
                    let value = self
                        .variables
                        .get(&name)
                        .ok_or(Report::msg(format!("Variable '{}' not found", name)))?
                        .clone();
                    stack.push(value);
                }
                Opcode::Sum(arg_count) => {
                    let mut sum = 0;
                    for _ in 0..arg_count {
                        match stack.pop().ok_or_else(|| Report::msg("Stack underflow"))? {
                            Value::Number(n) => sum += n,
                            _ => return Err(Report::msg("Sum can only operate on numbers")),
                        }
                    }
                    stack.push(Value::Number(sum));
                }
                Opcode::Print => {
                    let value = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    println!("{}", value);
                }
                Opcode::Jump(addr) => {
                    pc = addr;
                }
                Opcode::JumpIfFalse(addr) => {
                    let value = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    if !value.is_truthy() {
                        pc = addr;
                    }
                }
                Opcode::JumpIfTrue(addr) => {
                    let value = stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                    if value.is_truthy() {
                        pc = addr;
                    }
                }
                Opcode::Pop => {
                    stack.pop().ok_or_else(|| Report::msg("Stack underflow"))?;
                }
                Opcode::Return => {
                    return Ok(());
                }
                Opcode::Halt => {
                    return Ok(());
                }
                Opcode::Break => {
                    return Err(Report::msg("Break encountered"));
                }
                Opcode::Continue => {
                    return Err(Report::msg("Continue encountered"));
                }
            }
        }

        Ok(())
    }

    fn element_matches_type(&self, expr: &Expr, expected_type: &Type) -> bool {
        match expr {
            Expr::Number(_) => matches!(expected_type, Type::Int),
            Expr::String(_) => matches!(expected_type, Type::String),
            Expr::Boolean(_) => matches!(expected_type, Type::Bool),
            Expr::Float(_) => matches!(expected_type, Type::Float),
            Expr::Array(elements) => {
                if let Type::Arr(inner) = expected_type {
                    elements
                        .iter()
                        .all(|e| self.element_matches_type(e, &*inner))
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn value_matches_type(&self, value: &Value, expected_type: &Type) -> bool {
        match value {
            Value::Number(_) => matches!(expected_type, Type::Int),
            Value::String(_) => matches!(expected_type, Type::String),
            Value::Boolean(_) => matches!(expected_type, Type::Bool),
            Value::Float(_) => matches!(expected_type, Type::Float),
            Value::Array(elements) => {
                if let Type::Arr(inner) = expected_type {
                    elements
                        .iter()
                        .all(|v| self.value_matches_type(v, &*inner))
                } else {
                    false
                }
            }
            Value::TypedArray {
                elements,
                element_type,
            } if element_type == expected_type => {
                elements
                    .iter()
                    .all(|v| self.value_matches_type(v, expected_type))
            }
            _ => false,
        }
    }
}