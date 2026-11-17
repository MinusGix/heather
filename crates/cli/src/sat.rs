//! `heather sat <file.cnf>` — ask the solver behind certified bit-level
//! decisions (`crates/sat`, CaDiCaL) about a DIMACS CNF.
//!
//! Unsatisfiable: prints `s UNSATISFIABLE` and the refutation as LRAT text
//! (trimmed, derived clauses numbered after the formula's), exit 20. The
//! kernel checks such a proof with `lib/std/tactic/lrat.hthr`;
//! `scripts/lrat-probes` turns one into stage theorems. Satisfiable: prints
//! `s SATISFIABLE` and a `v` line of the model, exit 10. Both are the SAT
//! competition's conventions.

use std::process::ExitCode;

use heather_sat::{Answer, lrat_text, parse_dimacs, solve};

use crate::color;

pub fn run(args: &[String]) -> ExitCode {
    let [path] = args else {
        eprintln!("usage: heather sat <file.cnf>");
        return ExitCode::from(2);
    };
    let fail = |msg: String| {
        eprintln!("{}: {msg}", color::error_label(color::stderr_enabled()));
        ExitCode::from(1)
    };
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => return fail(format!("{path}: {e}")),
    };
    let (vars, clauses) = match parse_dimacs(&text) {
        Ok(f) => f,
        Err(e) => return fail(format!("{path}: {e}")),
    };
    match solve(vars, &clauses) {
        Ok(Answer::Refuted(steps)) => {
            print!("s UNSATISFIABLE\n{}", lrat_text(&steps));
            ExitCode::from(20)
        }
        Ok(Answer::Satisfiable(model)) => {
            let lits: Vec<String> = model.iter().enumerate().map(|(i, &b)| if b { format!("{}", i + 1) } else { format!("-{}", i + 1) }).collect();
            println!("s SATISFIABLE\nv {} 0", lits.join(" "));
            ExitCode::from(10)
        }
        Err(e) => fail(format!("{path}: the solver failed: {e:?}")),
    }
}
