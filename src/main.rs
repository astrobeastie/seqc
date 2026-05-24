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

mod export;
mod expr;
mod formula;
mod lexer;
mod parser;
mod proof;
mod substitution;

use export::{Latex, Typst};
use formula::Sequent;
use parser::Parser;
use proof::Proof;

#[derive(Clone, Copy, Eq, PartialEq)]
enum Format {
    Plain,
    Latex,
    Typst,
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        usage(&args[0]);
        process::exit(2);
    }
    match args[1].as_str() {
        "verify" => verify(&args),
        "prove" => prove(&args),
        "latex" => export_subcommand(&args, Format::Latex),
        "typst" => export_subcommand(&args, Format::Typst),
        _ => {
            usage(&args[0]);
            process::exit(2);
        }
    }
}

fn usage(prog: &str) {
    eprintln!("usage:");
    eprintln!("  {} verify <proof-file>", prog);
    eprintln!("  {} prove [--latex|--typst] <formula>", prog);
    eprintln!("  {} latex  <proof-file>", prog);
    eprintln!("  {} typst  <proof-file>", prog);
}

fn load_proof(prog: &str, cmd: &str, path: &str) -> Proof {
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
    match parser.parse_proof() {
        Ok(p) => p,
        Err(trace) => {
            print_trace("parse error", &trace);
            let _ = (prog, cmd);
            process::exit(1);
        }
    }
}

fn export_subcommand(args: &[String], format: Format) {
    let cmd = match format {
        Format::Latex => "latex",
        Format::Typst => "typst",
        Format::Plain => unreachable!(),
    };
    if args.len() != 3 {
        eprintln!("usage: {} {} <proof-file>", args[0], cmd);
        process::exit(2);
    }
    let proof = load_proof(&args[0], cmd, &args[2]);
    println!("{}", render(&proof, format));
}

fn render(proof: &Proof, format: Format) -> String {
    match format {
        Format::Plain => proof.to_string(),
        Format::Latex => proof.to_latex(),
        Format::Typst => proof.to_typst(),
    }
}

fn verify(args: &[String]) {
    if args.len() != 3 {
        eprintln!("usage: {} verify <proof-file>", args[0]);
        process::exit(2);
    }
    let proof = load_proof(&args[0], "verify", &args[2]);
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
        eprintln!("usage: {} prove [--latex|--typst] <formula>", args[0]);
        process::exit(2);
    }
    let mut format = Format::Plain;
    let mut rest = &args[2..];
    while let Some(first) = rest.first() {
        match first.as_str() {
            "--latex" if format == Format::Plain => {
                format = Format::Latex;
                rest = &rest[1..];
            }
            "--typst" if format == Format::Plain => {
                format = Format::Typst;
                rest = &rest[1..];
            }
            "--latex" | "--typst" => {
                eprintln!("error: --latex and --typst are mutually exclusive");
                process::exit(2);
            }
            s if s.starts_with("--") => {
                eprintln!("error: unknown flag {}", s);
                process::exit(2);
            }
            _ => break,
        }
    }
    if rest.is_empty() {
        eprintln!("usage: {} prove [--latex|--typst] <formula>", args[0]);
        process::exit(2);
    }
    let input = rest.join(" ");
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
            println!("{}", render(&stripped, format));
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
