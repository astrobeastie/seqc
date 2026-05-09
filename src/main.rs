use std::env;
use std::fs;
use std::process;

mod expr;
mod formula;
mod lexer;
mod parser;
mod proof;
mod substitution;

use parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} <proof-file>", args[0]);
        process::exit(2);
    }
    let path = &args[1];
    let contents = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error reading {}: {}", path, e);
            process::exit(2);
        }
    };
    let mut parser = match Parser::new(contents) {
        Ok(p) => p,
        Err(trace) => {
            print_trace("parse error", &trace);
            process::exit(1);
        }
    };
    let proof = match parser.parse_proof() {
        Ok(p) => p,
        Err(trace) => {
            print_trace("parse error", &trace);
            process::exit(1);
        }
    };
    match proof.check() {
        Ok(()) => {
            println!("proof checks out");
        }
        Err(trace) => {
            print_trace("proof check failed", &trace);
            process::exit(1);
        }
    }
}

fn print_trace(prefix: &str, trace: &[String]) {
    eprintln!("{}:", prefix);
    for line in trace {
        eprintln!("  {}", line);
    }
}
