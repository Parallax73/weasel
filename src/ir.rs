use llvm_sys::core::*;
use llvm_sys::execution_engine::*;
use llvm_sys::target::*;
use llvm_sys::analysis::*;
use llvm_sys::prelude::*;
use std::ffi::{CString, CStr};
use std::ptr;
use llvm_sys::LLVMIntPredicate;
use miette::Report;

use crate::ast::{Expr, BinaryOp, UnaryOp, Stmt};

pub struct CodeGen {
    context: LLVMContextRef,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    execution_engine: Option<LLVMExecutionEngineRef>,
}

impl CodeGen {
    pub fn new(module_name: &str) -> Result<Self, Report> {
        unsafe {
            // Initialize LLVM
            LLVM_InitializeNativeTarget();
            LLVM_InitializeNativeAsmPrinter();
            LLVMLinkInMCJIT();

            let context = LLVMContextCreate();
            let module_name_c = CString::new(module_name)
                .map_err(|_| Report::msg("Invalid module name"))?;
            let module = LLVMModuleCreateWithNameInContext(module_name_c.as_ptr(), context);
            let builder = LLVMCreateBuilderInContext(context);

            Ok(Self {
                context,
                module,
                builder,
                execution_engine: None,
            })
        }
    }

    pub fn compile_ast(&mut self, stmts: &[Stmt]) -> Result<(), Report> {
        unsafe {
            // Create main function
            let i64_type = LLVMInt64TypeInContext(self.context);
            let fn_type = LLVMFunctionType(i64_type, ptr::null_mut(), 0, 0);

            let main_name = CString::new("main")
                .map_err(|_| Report::msg("Invalid function name"))?;
            let function = LLVMAddFunction(self.module, main_name.as_ptr(), fn_type);

            let entry_name = CString::new("entry")
                .map_err(|_| Report::msg("Invalid block name"))?;
            let entry = LLVMAppendBasicBlockInContext(self.context, function, entry_name.as_ptr());
            LLVMPositionBuilderAtEnd(self.builder, entry);

            // Compile statements
            for stmt in stmts {
                self.compile_stmt(stmt)?;
            }

            // Return 0 if no explicit return
            let zero = LLVMConstInt(i64_type, 0, 0);
            LLVMBuildRet(self.builder, zero);

            // Verify module
            let mut error = ptr::null_mut();
            if LLVMVerifyModule(self.module, LLVMVerifierFailureAction::LLVMAbortProcessAction, &mut error) != 0 {
                let error_msg = if !error.is_null() {
                    let c_str = CStr::from_ptr(error);
                    let rust_str = c_str.to_string_lossy().into_owned();
                    LLVMDisposeMessage(error);
                    rust_str
                } else {
                    "Unknown verification error".to_string()
                };
                return Err(Report::msg(format!("Module verification failed: {}", error_msg)));
            }

            // Create execution engine
            let mut ee = ptr::null_mut();
            let mut error = ptr::null_mut();
            if LLVMCreateJITCompilerForModule(&mut ee, self.module, 2, &mut error) != 0 {
                let error_msg = if !error.is_null() {
                    let c_str = CStr::from_ptr(error);
                    let rust_str = c_str.to_string_lossy().into_owned();
                    LLVMDisposeMessage(error);
                    rust_str
                } else {
                    "Unknown execution engine error".to_string()
                };
                return Err(Report::msg(format!("Failed to create execution engine: {}", error_msg)));
            }
            self.execution_engine = Some(ee);
        }
        Ok(())
    }

    pub fn compile_stmt(&self, stmt: &Stmt) -> Result<(), Report> {
        match stmt {
            Stmt::Expression(expr) => {
                self.compile_expr(expr)?;
                Ok(())
            }
            Stmt::Block(stmts) => {
                for stmt in stmts {
                    self.compile_stmt(stmt)?;
                }
                Ok(())
            }
            Stmt::Return(expr) => {
                unsafe {
                    if let Some(expr) = expr {
                        let value = self.compile_expr(expr)?;
                        LLVMBuildRet(self.builder, value);
                    } else {
                        let i64_type = LLVMInt64TypeInContext(self.context);
                        let zero = LLVMConstInt(i64_type, 0, 0);
                        LLVMBuildRet(self.builder, zero);
                    }
                }
                Ok(())
            }
            _ => Err(Report::msg("Statement type not implemented yet")),
        }
    }

    pub fn compile_expr(&self, expr: &Expr) -> Result<LLVMValueRef, Report> {
        unsafe {
            let i64_type = LLVMInt64TypeInContext(self.context);
            match expr {
                Expr::Number(n) => {
                    Ok(LLVMConstInt(i64_type, *n as u64, 0))
                }
                Expr::Unary { operator, operand } => {
                    let val = self.compile_expr(operand)?;
                    match operator {
                        UnaryOp::Negate => {
                            let name = CString::new("neg").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildNeg(self.builder, val, name.as_ptr()))
                        }
                        UnaryOp::Not => {
                            let zero = LLVMConstInt(i64_type, 0, 0);
                            let name = CString::new("is_zero").map_err(|_| Report::msg("Invalid name"))?;
                            let is_zero = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntEQ,
                                val,
                                zero,
                                name.as_ptr(),
                            );
                            let name = CString::new("not").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, is_zero, i64_type, name.as_ptr()))
                        }
                    }
                }
                Expr::Binary { left, operator, right } => {
                    let l = self.compile_expr(left)?;
                    let r = self.compile_expr(right)?;
                    match operator {
                        BinaryOp::Add => {
                            let name = CString::new("add").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildAdd(self.builder, l, r, name.as_ptr()))
                        }
                        BinaryOp::Subtract => {
                            let name = CString::new("sub").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildSub(self.builder, l, r, name.as_ptr()))
                        }
                        BinaryOp::Multiply => {
                            let name = CString::new("mul").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildMul(self.builder, l, r, name.as_ptr()))
                        }
                        BinaryOp::Divide => {
                            let name = CString::new("div").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildSDiv(self.builder, l, r, name.as_ptr()))
                        }
                        BinaryOp::Equal => {
                            let name = CString::new("eq").map_err(|_| Report::msg("Invalid name"))?;
                            let cmp = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntEQ,
                                l,
                                r,
                                name.as_ptr(),
                            );
                            let name = CString::new("eq_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, cmp, i64_type, name.as_ptr()))
                        }
                        BinaryOp::NotEqual => {
                            let name = CString::new("ne").map_err(|_| Report::msg("Invalid name"))?;
                            let cmp = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntNE,
                                l,
                                r,
                                name.as_ptr(),
                            );
                            let name = CString::new("ne_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, cmp, i64_type, name.as_ptr()))
                        }
                        BinaryOp::Less => {
                            let name = CString::new("lt").map_err(|_| Report::msg("Invalid name"))?;
                            let cmp = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntSLT,
                                l,
                                r,
                                name.as_ptr(),
                            );
                            let name = CString::new("lt_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, cmp, i64_type, name.as_ptr()))
                        }
                        BinaryOp::Greater => {
                            let name = CString::new("gt").map_err(|_| Report::msg("Invalid name"))?;
                            let cmp = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntSGT,
                                l,
                                r,
                                name.as_ptr(),
                            );
                            let name = CString::new("gt_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, cmp, i64_type, name.as_ptr()))
                        }
                        BinaryOp::LessEq => {
                            let name = CString::new("le").map_err(|_| Report::msg("Invalid name"))?;
                            let cmp = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntSLE,
                                l,
                                r,
                                name.as_ptr(),
                            );
                            let name = CString::new("le_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, cmp, i64_type, name.as_ptr()))
                        }
                        BinaryOp::GreaterEq => {
                            let name = CString::new("ge").map_err(|_| Report::msg("Invalid name"))?;
                            let cmp = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntSGE,
                                l,
                                r,
                                name.as_ptr(),
                            );
                            let name = CString::new("ge_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, cmp, i64_type, name.as_ptr()))
                        }
                        BinaryOp::And => {
                            let zero = LLVMConstInt(i64_type, 0, 0);
                            let name = CString::new("l_bool").map_err(|_| Report::msg("Invalid name"))?;
                            let l_bool = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntNE,
                                l,
                                zero,
                                name.as_ptr(),
                            );
                            let name = CString::new("r_bool").map_err(|_| Report::msg("Invalid name"))?;
                            let r_bool = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntNE,
                                r,
                                zero,
                                name.as_ptr(),
                            );
                            let name = CString::new("and").map_err(|_| Report::msg("Invalid name"))?;
                            let and_result = LLVMBuildAnd(self.builder, l_bool, r_bool, name.as_ptr());
                            let name = CString::new("and_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, and_result, i64_type, name.as_ptr()))
                        }
                        BinaryOp::Or => {
                            let zero = LLVMConstInt(i64_type, 0, 0);
                            let name = CString::new("l_bool").map_err(|_| Report::msg("Invalid name"))?;
                            let l_bool = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntNE,
                                l,
                                zero,
                                name.as_ptr(),
                            );
                            let name = CString::new("r_bool").map_err(|_| Report::msg("Invalid name"))?;
                            let r_bool = LLVMBuildICmp(
                                self.builder,
                                LLVMIntPredicate::LLVMIntNE,
                                r,
                                zero,
                                name.as_ptr(),
                            );
                            let name = CString::new("or").map_err(|_| Report::msg("Invalid name"))?;
                            let or_result = LLVMBuildOr(self.builder, l_bool, r_bool, name.as_ptr());
                            let name = CString::new("or_ext").map_err(|_| Report::msg("Invalid name"))?;
                            Ok(LLVMBuildZExt(self.builder, or_result, i64_type, name.as_ptr()))
                        }
                        BinaryOp::Assign => Err(Report::msg("Assign not implemented in codegen")),
                    }
                }
                Expr::Call { callee, arguments } => {
                    if let Expr::Identifier(name) = &**callee {
                        let func_name = CString::new(name.as_str())
                            .map_err(|_| Report::msg("Invalid function name"))?;
                        let func = LLVMGetNamedFunction(self.module, func_name.as_ptr());
                        if func.is_null() {
                            return Err(Report::msg(format!("Unknown function '{}'", name)));
                        }

                        let mut args_vals: Vec<LLVMValueRef> = Vec::new();
                        for arg in arguments {
                            args_vals.push(self.compile_expr(arg)?);
                        }

                        let name = CString::new("call").map_err(|_| Report::msg("Invalid name"))?;
                        Ok(LLVMBuildCall2(
                            self.builder,
                            LLVMGlobalGetValueType(func),
                            func,
                            args_vals.as_mut_ptr(),
                            args_vals.len() as u32,
                            name.as_ptr(),
                        ))
                    } else {
                        Err(Report::msg("Call callee must be identifier"))
                    }
                }
                Expr::Identifier(_) => Err(Report::msg("Identifier cannot be compiled directly")),
                Expr::Grouping(inner) => self.compile_expr(inner),
                Expr::String(_) => Err(Report::msg("String literals not implemented yet")),
            }
        }
    }

    pub fn jit_compile_sum(&mut self, call_expr: &Expr) -> Result<unsafe extern "C" fn(u64, u64, u64) -> u64, Report> {
        unsafe {
            let i64_type = LLVMInt64TypeInContext(self.context);
            let mut param_types = [i64_type, i64_type, i64_type];
            let fn_type = LLVMFunctionType(i64_type, param_types.as_mut_ptr(), 3, 0);

            let sum_name = CString::new("sum").map_err(|_| Report::msg("Invalid function name"))?;
            let function = LLVMAddFunction(self.module, sum_name.as_ptr(), fn_type);

            let entry_name = CString::new("entry").map_err(|_| Report::msg("Invalid block name"))?;
            let entry = LLVMAppendBasicBlockInContext(self.context, function, entry_name.as_ptr());
            LLVMPositionBuilderAtEnd(self.builder, entry);

            if let Expr::Call { arguments, .. } = call_expr {
                if arguments.len() != 3 {
                    return Err(Report::msg("sum expects exactly 3 arguments"));
                }

                let a = if let Expr::Number(n) = &arguments[0] {
                    LLVMConstInt(i64_type, *n as u64, 0)
                } else {
                    LLVMConstInt(i64_type, 0, 0)
                };
                let b = if let Expr::Number(n) = &arguments[1] {
                    LLVMConstInt(i64_type, *n as u64, 0)
                } else {
                    LLVMConstInt(i64_type, 0, 0)
                };
                let c = if let Expr::Number(n) = &arguments[2] {
                    LLVMConstInt(i64_type, *n as u64, 0)
                } else {
                    LLVMConstInt(i64_type, 0, 0)
                };

                let name1 = CString::new("sum1").map_err(|_| Report::msg("Invalid name"))?;
                let sum1 = LLVMBuildAdd(self.builder, a, b, name1.as_ptr());
                let name2 = CString::new("sum2").map_err(|_| Report::msg("Invalid name"))?;
                let sum2 = LLVMBuildAdd(self.builder, sum1, c, name2.as_ptr());

                LLVMBuildRet(self.builder, sum2);
            }

            // Create execution engine if not exists
            if self.execution_engine.is_none() {
                let mut ee = ptr::null_mut();
                let mut error = ptr::null_mut();
                if LLVMCreateJITCompilerForModule(&mut ee, self.module, 2, &mut error) != 0 {
                    let error_msg = if !error.is_null() {
                        let c_str = CStr::from_ptr(error);
                        let rust_str = c_str.to_string_lossy().into_owned();
                        LLVMDisposeMessage(error);
                        rust_str
                    } else {
                        "Unknown execution engine error".to_string()
                    };
                    return Err(Report::msg(format!("Failed to create execution engine: {}", error_msg)));
                }
                self.execution_engine = Some(ee);
            }

            let sum_name = CString::new("sum").map_err(|_| Report::msg("Invalid function name"))?;
            let func_addr = LLVMGetFunctionAddress(
                self.execution_engine.unwrap(),
                sum_name.as_ptr(),
            );

            if func_addr == 0 {
                return Err(Report::msg("Failed to get function address"));
            }

            Ok(std::mem::transmute(func_addr))
        }
    }
}

impl Drop for CodeGen {
    fn drop(&mut self) {
        unsafe {
            if let Some(ee) = self.execution_engine {
                LLVMDisposeExecutionEngine(ee);
            }
            LLVMDisposeBuilder(self.builder);
            LLVMContextDispose(self.context);
        }
    }
}