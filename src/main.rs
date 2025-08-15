#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]

use clap::{Parser, Subcommand};
use miette::{IntoDiagnostic, Result, WrapErr, Report};
use std::fs;
use std::path::PathBuf;

mod lex;
mod ast;
mod parser;
mod ir;

use lex::{Lexer, LexError};
use parser::Parser as MyParser;
use ir::Codegen;
use ast::{Expr, Stmt};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Tokenize { filename: PathBuf },
    Parse { filename: PathBuf },
    Sum { filename: PathBuf },
}

fn main() -> Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Tokenize { filename } => {
            let file_content = fs::read_to_string(&filename)
                .into_diagnostic()
                .wrap_err(format!("Failed to read file {:?}", filename))?;

            let mut lexer = Lexer::new(&file_content);
            let tokens = lexer
                .tokenize()
                .map_err(|e: LexError| Report::new(e))
                .wrap_err("Tokenization failed")?;

            println!("Tokens:");
            for token in tokens {
                println!("{:?}", token);
            }
            Ok(())
        }
        Commands::Parse { filename } => {
            let file_content = fs::read_to_string(&filename)
                .into_diagnostic()
                .wrap_err(format!("Failed to read file {:?}", filename))?;

            let mut lexer = Lexer::new(&file_content);
            let tokens = lexer
                .tokenize()
                .map_err(|e: LexError| Report::new(e))
                .wrap_err("Tokenization failed")?;

            let mut parser = MyParser::new(tokens, &file_content);
            let ast = parser.parse().wrap_err("Parsing failed")?;

            println!("AST: {:#?}", ast);
            Ok(())
        }
        Commands::Sum { filename } => {
            let file_content = fs::read_to_string(&filename)
                .into_diagnostic()
                .wrap_err(format!("Failed to read file {:?}", filename))?;

            let mut lexer = Lexer::new(&file_content);
            let tokens = lexer
                .tokenize()
                .map_err(|e: LexError| Report::new(e))
                .wrap_err("Tokenization failed")?;

            let mut parser = MyParser::new(tokens, &file_content);
            let stmts = parser.parse().wrap_err("Parsing failed")?;

            for stmt in stmts {
                if let Stmt::Expression(expr) = stmt {
                    if let Expr::Call { callee, arguments } = expr {
                        if let Expr::Identifier(ref name) = *callee {
                            if name == "sum" {
                                if arguments.len() != 3 {
                                    println!("sum function expects exactly 3 arguments.");
                                    continue;
                                }

                                let context = inkwell::context::Context::create();
                                let codegen = Codegen::new(&context, "sum_module");
                                let sum_fn = codegen.jit_compile_sum(&Expr::Call {
                                    callee: callee.clone(),
                                    arguments: arguments.clone(),
                                })?;

                                let a = if let Expr::Number(n) = &arguments[0] { *n as u64 } else { 0 };
                                let b = if let Expr::Number(n) = &arguments[1] { *n as u64 } else { 0 };
                                let c = if let Expr::Number(n) = &arguments[2] { *n as u64 } else { 0 };

                                unsafe {
                                    let result = sum_fn.call(a, b, c);
                                    println!("sum({}, {}, {}) = {}", a, b, c, result);
                                }
                            }
                        }
                    }
                }
            }
            Ok(())
        }
    }
}
