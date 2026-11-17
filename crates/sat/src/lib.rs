//! SAT solving for certified bit-level decisions
//! (issues/lrat-certified-bitvector-decision.md).
//!
//! `solve` asks CaDiCaL (`vendor/cadical`) about a CNF. A satisfiable one
//! comes back with a model; an unsatisfiable one with an LRAT refutation,
//! trimmed to the steps the empty clause depends on and renumbered densely
//! after the formula's own clauses. Nothing here is trusted: the kernel
//! checks the refutation with `lib/std/tactic/lrat.hthr`, whose soundness is
//! proved, so a wrong answer costs a failed proof and never a wrong one.
//!
//! Literals are DIMACS: variable `v` is `v`, its negation `-v`, `v ≥ 1`.
//! Clauses are numbered from 1 in the order given.

mod ffi;

use std::collections::HashMap;

/// One LRAT step: `clause` follows by unit propagation along `hints`, the ids
/// of earlier clauses, in order; the last one is a conflict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub id: u64,
    pub clause: Vec<i32>,
    pub hints: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// `model[v - 1]` is variable `v`'s value.
    Satisfiable(Vec<bool>),
    /// Steps ending in the empty clause.
    Refuted(Vec<Step>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatError {
    /// A literal is 0 or names a variable above `num_vars`.
    BadLiteral(i32),
    /// The solver stopped without an answer.
    Unknown,
    /// The solver's proof does not fit what this crate reads: original
    /// clauses numbered other than 1.., no empty clause, a hint to no clause.
    Proof(String),
}

pub fn solve(num_vars: u32, clauses: &[Vec<i32>]) -> Result<Answer, SatError> {
    if let Some(&l) = clauses.iter().flatten().find(|&&l| l == 0 || l.unsigned_abs() > num_vars) {
        return Err(SatError::BadLiteral(l));
    }
    // The solver derives nothing from a clause that is already empty: the
    // refutation is that clause, hinted.
    if let Some(k) = clauses.iter().position(|c| c.is_empty()) {
        return Ok(Answer::Refuted(vec![Step { id: clauses.len() as u64 + 1, clause: Vec::new(), hints: vec![k as u64 + 1] }]));
    }
    let mut s = ffi::Session::new();
    for c in clauses {
        for &l in c {
            s.add(l);
        }
        s.add(0);
    }
    match s.solve() {
        10 => Ok(Answer::Satisfiable((1..=num_vars as i32).map(|v| s.val(v) > 0).collect())),
        20 => {
            if s.restored() {
                return Err(SatError::Proof("the solver restored a clause".into()));
            }
            let originals = original_ids(clauses, &s.originals())?;
            Ok(Answer::Refuted(trim(&originals, read_steps(&s.steps())?)?))
        }
        _ => Err(SatError::Unknown),
    }
}

/// The solver reports the clauses it was given in the order given, but its
/// ids for them can skip (it numbers a few things of its own): map each of
/// its ids to the clause's place, checking the clause is the one we gave.
fn original_ids(clauses: &[Vec<i32>], flat: &[i64]) -> Result<HashMap<u64, u64>, SatError> {
    let bad = |why: String| SatError::Proof(format!("original clauses: {why}"));
    let set = |c: &[i32]| {
        let mut c = c.to_vec();
        c.sort_unstable();
        c.dedup();
        c
    };
    let mut ids = HashMap::new();
    let mut i = 0;
    while i < flat.len() {
        let (id, n) = (flat[i] as u64, *flat.get(i + 1).ok_or_else(|| bad("truncated".into()))? as usize);
        let lits: Vec<i32> = flat.get(i + 2..i + 2 + n).ok_or_else(|| bad("truncated".into()))?.iter().map(|&l| l as i32).collect();
        i += 2 + n;
        let k = ids.len();
        let given = clauses.get(k).ok_or_else(|| bad("more than were given".into()))?;
        if set(&lits) != set(given) {
            return Err(bad(format!("the solver's clause {id} is {lits:?}, but the {}th given is {given:?}", k + 1)));
        }
        if ids.insert(id, k as u64 + 1).is_some() {
            return Err(bad(format!("id {id} twice")));
        }
    }
    if ids.len() != clauses.len() {
        return Err(bad(format!("{} reported of {} given", ids.len(), clauses.len())));
    }
    Ok(ids)
}

fn read_steps(flat: &[i64]) -> Result<Vec<Step>, SatError> {
    let bad = || SatError::Proof("a truncated step".into());
    let mut out = Vec::new();
    let mut i = 0;
    while i < flat.len() {
        let id = *flat.get(i).ok_or_else(bad)? as u64;
        let n = *flat.get(i + 1).ok_or_else(bad)? as usize;
        let clause = flat.get(i + 2..i + 2 + n).ok_or_else(bad)?.iter().map(|&l| l as i32).collect();
        i += 2 + n;
        let m = *flat.get(i).ok_or_else(bad)? as usize;
        let hints = flat.get(i + 1..i + 1 + m).ok_or_else(bad)?.iter().map(|&h| h as u64).collect();
        i += 1 + m;
        out.push(Step { id, clause, hints });
    }
    Ok(out)
}

/// The steps the first empty clause depends on, in order, in our numbering:
/// the given clauses by place, derived ones densely after them (the checker
/// looks ids up a bit at a time, so small ids are cheaper).
fn trim(originals: &HashMap<u64, u64>, steps: Vec<Step>) -> Result<Vec<Step>, SatError> {
    let end = steps.iter().position(|s| s.clause.is_empty()).ok_or_else(|| SatError::Proof("no empty clause".into()))?;
    let steps = &steps[..=end];
    let at: HashMap<u64, usize> = steps.iter().enumerate().map(|(i, s)| (s.id, i)).collect();
    let mut needed = vec![false; steps.len()];
    needed[end] = true;
    for i in (0..=end).rev() {
        if !needed[i] {
            continue;
        }
        for h in &steps[i].hints {
            match at.get(h) {
                Some(&j) if j < i => needed[j] = true,
                Some(_) => return Err(SatError::Proof(format!("step {} hints a later clause {h}", steps[i].id))),
                None if originals.contains_key(h) => {}
                None => return Err(SatError::Proof(format!("step {} hints no clause {h}", steps[i].id))),
            }
        }
    }
    let mut renamed = originals.clone();
    let mut out = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        if !needed[i] {
            continue;
        }
        let id = originals.len() as u64 + 1 + out.len() as u64;
        renamed.insert(s.id, id);
        let hints = s.hints.iter().map(|h| renamed[h]).collect();
        out.push(Step { id, clause: s.clause.clone(), hints });
    }
    Ok(out)
}

/// DIMACS CNF: `p cnf <vars> <clauses>` and zero-terminated clauses;
/// comment lines start with `c`.
pub fn parse_dimacs(text: &str) -> Result<(u32, Vec<Vec<i32>>), String> {
    let mut vars = None;
    let mut clauses = Vec::new();
    let mut cur = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("p cnf") {
            let n = rest.split_whitespace().next().ok_or("a `p cnf` line without a variable count")?;
            vars = Some(n.parse::<u32>().map_err(|e| format!("variable count: {e}"))?);
            continue;
        }
        for t in line.split_whitespace() {
            let l: i32 = t.parse().map_err(|e| format!("literal `{t}`: {e}"))?;
            if l == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                cur.push(l);
            }
        }
    }
    if !cur.is_empty() {
        return Err("the last clause has no terminating 0".into());
    }
    Ok((vars.ok_or("no `p cnf` line")?, clauses))
}

/// LRAT text, one step a line: `id lits 0 hints 0`.
pub fn lrat_text(steps: &[Step]) -> String {
    let mut out = String::new();
    for s in steps {
        out.push_str(&s.id.to_string());
        for l in &s.clause {
            out.push(' ');
            out.push_str(&l.to_string());
        }
        out.push_str(" 0");
        for h in &s.hints {
            out.push(' ');
            out.push_str(&h.to_string());
        }
        out.push_str(" 0\n");
    }
    out
}

#[cfg(test)]
mod tests;
