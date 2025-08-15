use std::fs;
use std::env;
use miette::{IntoDiagnostic, Result};

mod lex;
mod parser;
mod ast;

use crate::lex::Lexer;
use crate::parser::Parser;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        std::process::exit(1);
    }

    let filename = &args[1];
    let file_content = fs::read_to_string(filename)
        .into_diagnostic()?;

    println!("File content:\n{}\n", file_content);

    let mut lexer = Lexer::new(&file_content);
    let tokens = lexer.tokenize()?;

    println!("Tokens: {:#?}\n", tokens);

    let mut parser = Parser::new(tokens, &file_content);
    let ast = parser.parse()?;

    println!("AST:\n{:#?}", ast);

    Ok(())
}