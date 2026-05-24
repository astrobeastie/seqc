use std::collections::HashSet;
use std::env;
use std::fs;
use std::process;

#[macro_export]
macro_rules! hash_set {
    {$($v: expr),* $(,)?} => {
        ::std::collections::HashSet::from([$($v,)*])
    };
}

mod expr;
mod formula;
mod lexer;
mod parser;
mod proof;
mod substitution;

use formula::Sequent;
use parser::Parser;
use proof::Proof;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        usage(&args[0]);
        process::exit(2);
    }
    match args[1].as_str() {
        "verify" => verify(&args),
        "prove" => prove(&args),
        _ => {
            usage(&args[0]);
            process::exit(2);
        }
    }
}

fn usage(prog: &str) {
    eprintln!("usage:");
    eprintln!("  {} verify <proof-file>", prog);
    eprintln!("  {} prove <formula>", prog);
}

fn verify(args: &[String]) {
    if args.len() != 3 {
        eprintln!("usage: {} verify <proof-file>", args[0]);
        process::exit(2);
    }
    let path = &args[2];
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

fn prove(args: &[String]) {
    if args.len() < 3 {
        eprintln!("usage: {} prove <formula>", args[0]);
        process::exit(2);
    }
    let input = args[2..].join(" ");
    let sequent = match Parser::new(input.clone()).and_then(|mut p| p.parse_sequent()) {
        Ok(s) => s,
        Err(_) => {
            let mut parser = match Parser::new(input) {
                Ok(p) => p,
                Err(trace) => {
                    print_trace("parse error", &trace);
                    process::exit(1);
                }
            };
            let formula = match parser.parse_formula() {
                Ok(f) => f,
                Err(trace) => {
                    print_trace("parse error", &trace);
                    process::exit(1);
                }
            };
            let mut conclusions = HashSet::new();
            conclusions.insert(formula);
            Sequent {
                assumptions: HashSet::new(),
                conclusions,
                eigenvars: HashSet::new(),
            }
        }
    };
    let max_depth = 2 * sequent.size();
    // Binary search [1, max_depth] for the smallest depth that admits a proof.
    let mut best: Option<Proof> = None;
    let mut lo = 1usize;
    let mut hi = max_depth + 1;
    while lo < hi {
        let mid = (lo + hi) / 2;
        match sequent.proof_search(mid) {
            Some(p) => {
                best = Some(p);
                hi = mid;
            }
            None => {
                lo = mid + 1;
            }
        }
    }
    match best {
        Some(proof) => {
            let stripped = proof
                .strip()
                .expect("proof_search produced an invalid proof");
            println!("{}", stripped);
        }
        None => {
            eprintln!("no proof found within depth {}", max_depth);
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
