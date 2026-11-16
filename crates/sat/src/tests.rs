//! The solver's answers checked independently: a model against the
//! clauses, a refutation by replaying its unit propagation here (the
//! kernel's checker is the real judge; this one catches a misread proof).
use super::*;
use std::collections::HashMap;

fn rup_checks(clauses: &[Vec<i32>], steps: &[Step]) -> bool {
    let mut db: HashMap<u64, Vec<i32>> = clauses.iter().cloned().enumerate().map(|(i, c)| (i as u64 + 1, c)).collect();
    for s in steps {
        let mut a: HashMap<u32, bool> = s.clause.iter().map(|&l| (l.unsigned_abs(), l < 0)).collect();
        let mut conflict = false;
        for h in &s.hints {
            let Some(d) = db.get(h) else { return false };
            let value = |l: i32, a: &HashMap<u32, bool>| a.get(&l.unsigned_abs()).map(|&v| v == (l > 0));
            if d.iter().any(|&l| value(l, &a) == Some(true)) {
                return false;
            }
            let open: Vec<i32> = d.iter().copied().filter(|&l| value(l, &a).is_none()).collect();
            match open.as_slice() {
                [] => {
                    conflict = true;
                    break;
                }
                [u] => {
                    a.insert(u.unsigned_abs(), *u > 0);
                }
                _ => return false,
            }
        }
        if !conflict {
            return false;
        }
        db.insert(s.id, s.clause.clone());
    }
    steps.last().is_some_and(|s| s.clause.is_empty())
}

fn refuted(num_vars: u32, clauses: &[Vec<i32>]) -> Vec<Step> {
    match solve(num_vars, clauses) {
        Ok(Answer::Refuted(steps)) => {
            assert!(rup_checks(clauses, &steps), "the refutation replays: {steps:?}");
            let first = clauses.len() as u64 + 1;
            assert!(steps.iter().enumerate().all(|(i, s)| s.id == first + i as u64), "ids are dense after the formula's");
            steps
        }
        other => panic!("expected a refutation, got {other:?}"),
    }
}

/// `n + 1` pigeons in `n` holes; variable `p * n + h + 1` puts pigeon `p` in hole `h`.
fn pigeons(n: i32) -> (u32, Vec<Vec<i32>>) {
    let var = |p: i32, h: i32| p * n + h + 1;
    let mut cs: Vec<Vec<i32>> = (0..=n).map(|p| (0..n).map(|h| var(p, h)).collect()).collect();
    for h in 0..n {
        for p in 0..=n {
            for q in p + 1..=n {
                cs.push(vec![-var(p, h), -var(q, h)]);
            }
        }
    }
    (((n + 1) * n) as u32, cs)
}

#[test]
fn a_contradiction_is_refuted() {
    let steps = refuted(1, &[vec![1], vec![-1]]);
    assert_eq!(steps.last().map(|s| s.clause.is_empty()), Some(true));
}

#[test]
fn pigeons_are_refuted() {
    for n in 2..=5 {
        let (v, cs) = pigeons(n);
        refuted(v, &cs);
    }
}

#[test]
fn a_formula_with_the_empty_clause_is_refuted() {
    refuted(1, &[vec![1], vec![]]);
}

#[test]
fn a_model_satisfies_every_clause() {
    let cs = vec![vec![1, 2], vec![-1, 3], vec![-2, -3], vec![-3, 1]];
    match solve(3, &cs) {
        Ok(Answer::Satisfiable(m)) => {
            assert!(cs.iter().all(|c| c.iter().any(|&l| m[l.unsigned_abs() as usize - 1] == (l > 0))), "{m:?}");
        }
        other => panic!("expected a model, got {other:?}"),
    }
}

#[test]
fn the_empty_formula_is_satisfiable() {
    assert!(matches!(solve(2, &[]), Ok(Answer::Satisfiable(m)) if m.len() == 2));
}

#[test]
fn a_literal_outside_the_variables_is_refused() {
    assert_eq!(solve(1, &[vec![2]]), Err(SatError::BadLiteral(2)));
    assert_eq!(solve(1, &[vec![0]]), Err(SatError::BadLiteral(0)));
}

#[test]
fn dimacs_round_trips() {
    let (v, cs) = parse_dimacs("c pigeons\np cnf 2 3\n1 2 0\n-1 0 -2\n0\n").expect("parses");
    assert_eq!((v, cs), (2, vec![vec![1, 2], vec![-1], vec![-2]]));
    assert!(parse_dimacs("p cnf 1 1\n1").is_err(), "an unterminated clause is refused");
}

// Units among the clauses: the solver's ids for what follows them skip
// (seen on multiplier miters), and the refutation still names our places.
#[test]
fn units_among_the_clauses_keep_their_places() {
    let (v, mut cs) = pigeons(3);
    cs.insert(2, vec![-1]);
    cs.insert(7, vec![-5]);
    refuted(v, &cs);
    refuted(3, &[vec![1, 2], vec![-1], vec![-2, 3], vec![-3]]);
}
