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
use ir::CodeGen;

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
    Run { filename: PathBuf },
}

fn main() -> Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Tokenize { filename } => {
            let file_content = fs::read_to_string(&filename)
                .into_diagnostic()
                .wrap_err(format!("Failed to read file {:?}", filename))?;

            let tokens = Lexer::new(&file_content)
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

            let tokens = Lexer::new(&file_content)
                .tokenize()
                .map_err(|e: LexError| Report::new(e))
                .wrap_err("Tokenization failed")?;

            let ast = MyParser::new(tokens)
                .parse()
                .wrap_err("Parsing failed")?;

            println!("AST: {:#?}", ast);
            Ok(())
        }
        Commands::Run { filename } => {
            let file_content = fs::read_to_string(&filename)
                .into_diagnostic()
                .wrap_err(format!("Failed to read file {:?}", filename))?;

            let tokens = Lexer::new(&file_content)
                .tokenize()
                .map_err(|e: LexError| Report::new(e))
                .wrap_err("Tokenization failed")?;

            let stmts = MyParser::new(tokens)
                .parse()
                .wrap_err("Parsing failed")?;

            let mut codegen = CodeGen::new();
            codegen.compile_ast(&stmts)?;

            codegen.run()?;

            Ok(())
        }
    }
}