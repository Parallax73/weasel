use inkwell::context::Context;
use inkwell::builder::Builder;
use inkwell::values::IntValue;
use inkwell::module::Module;
use inkwell::execution_engine::JitFunction;
use inkwell::OptimizationLevel;
use crate::ast::Expr;
use miette::Result;

pub struct Codegen<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
}

impl<'ctx> Codegen<'ctx> {
    pub fn new(context: &'ctx Context, name: &str) -> Self {
        let module = context.create_module(name);
        let builder = context.create_builder();
        Self { context, builder, module }
    }

    pub fn jit_compile_sum(
        &'_ self,
        expr: &Expr,
    ) -> Result<JitFunction<'_, unsafe extern "C" fn(u64, u64, u64) -> u64>> {
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(
            &[i64_type.into(), i64_type.into(), i64_type.into()],
            false,
        );
        let function = self.module.add_function("sum", fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);

        if let Expr::Call { arguments, .. } = expr {
            let arg0 = match &arguments[0] {
                Expr::Number(n) => i64_type.const_int(*n as u64, false),
                _ => i64_type.const_int(0, false),
            };
            let arg1 = match &arguments[1] {
                Expr::Number(n) => i64_type.const_int(*n as u64, false),
                _ => i64_type.const_int(0, false),
            };
            let arg2 = match &arguments[2] {
                Expr::Number(n) => i64_type.const_int(*n as u64, false),
                _ => i64_type.const_int(0, false),
            };

            let sum1 = self.builder.build_int_add(arg0, arg1, "sum1")
                .expect("build_int_add failed for sum1");
            let sum2 = self.builder.build_int_add(sum1, arg2, "sum2")
                .expect("build_int_add failed for sum2");
            self.builder.build_return(Some(&sum2)).expect("TODO: panic message");
        }

        let execution_engine = self
            .module
            .create_jit_execution_engine(OptimizationLevel::None)
            .unwrap();
        unsafe { Ok(execution_engine.get_function("sum").unwrap()) }
    }
}
