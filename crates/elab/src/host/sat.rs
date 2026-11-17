//! `Sat(cs, vars)`: the clauses a closed term computes, given to CaDiCaL
//! (`crates/sat`). A refutation comes back as a proof term the kernel replays
//! (`lib/std/tactic/lrat.hthr`, "A refutation as one term"); a model as the
//! values of the variables asked about.
//!
//! Nothing here is trusted. The solver's proof is laid out as stages, each
//! obligation `X = True` or `X = literal` proved by `refl` and so a
//! conversion of its own, which keeps every conversion inside the kernel's
//! per-conversion fuel:
//!
//! - the input clauses some step names are built into the formula a run of
//!   consecutive ones at a time (`reaches_build`), a literal trie every
//!   [`BUILD_EVERY`] runs and after the last; runs no step names are
//!   dropped (`reaches_drop`);
//! - the solver's steps are added a chunk at a time (`reaches_add`), every
//!   [`EVERY`]th chunk ending in a literal trie of the formula so far
//!   (`reaches_add_at`), so a stage replays at most [`EVERY`] chunks of
//!   insertions;
//! - the last chunk derives the empty clause (`reaches_done`).
//!
//! The cost shape behind these choices is in
//! `docs/tactics/bv-decide-design.md`.
//!
//! The whole is `reaches_refutes(cs, …)`, whose type mentions `cs` as the
//! tactic wrote it: the kernel converts `cs` with the chunks once.

use super::*;
use std::collections::HashMap;

/// Clauses one formula chunk inserts.
const BUILD_PER: usize = 256;

/// Hinted literals one step chunk reads: each costs a lookup of its
/// variable, which dominates a stage, and lookups deepen as the formula and
/// the variables grow. A chunk of 1100 needed about four fifths of the budget
/// on an 8-bit adder's proof; on a 64-bit adder's, chunks of 800 passed it
/// and chunks of 500 all fit.
const STEP_PER: usize = 500;

/// Stages between literal checkpoints of the formula.
const BUILD_EVERY: usize = 2;

/// Input clauses one `reaches_piece` meets against their chunks: each piece
/// computes the tactic's clause list again, so pieces are few and large.
const PIECE: usize = 1024;
const EVERY: usize = 8;

/// Literals the clauses may hold before the host declines to read them.
const MAX_LITERALS: usize = 1 << 22;

/// What one force of the clause term may spend: the term runs a whole
/// bit-blaster, more than one conversion's worth, and only bounds a runaway.
const CLAUSE_FUEL: u64 = heather_kernel::typing::DEFAULT_FUEL << 8;

/// A checker literal: variable `v` is `2v`, its negation `2v + 1`
/// (`lib/std/tactic/lrat.hthr`). DIMACS numbers variables from 1, so
/// variable `v` is DIMACS `v + 1`.
fn to_dimacs(code: u64) -> Result<i32, String> {
    let v = i32::try_from(code / 2 + 1).map_err(|_| format!("a literal past the solver's range: {code}"))?;
    Ok(if code % 2 == 1 { -v } else { v })
}

fn from_dimacs(l: i32) -> u64 {
    2 * (l.unsigned_abs() as u64 - 1) + u64::from(l < 0)
}

/// A persistent `NatMap` trie as `lib/std/data/nat_map.hthr` lays it out:
/// key 0 at the root, `Succ(k)` in child `low_bit(k)` at `k / 2`. Each node
/// keeps the kernel term it spells once built, so consecutive checkpoints
/// share every subtree the steps between them did not touch.
#[derive(Clone, Default)]
struct Trie(Option<Rc<Node>>);

struct Node {
    here: Option<Rc<Term>>,
    even: Trie,
    odd: Trie,
    term: Term,
}

/// The kernel spellings a certificate is built from: `lrat::` globals by
/// their qualified keys, which reach a `by` through its import closure
/// whether or not the user's module names them.
struct Spell {
    nat_nil: Wrap,
    nat_cons: Wrap,
    clause_nil: Wrap,
    clause_cons: Wrap,
    step: Wrap,
    step_nil: Wrap,
    step_cons: Wrap,
    map_empty: Wrap,
    map_node: Wrap,
    none: Wrap,
    some: Wrap,
    chunks_nil: Wrap,
    chunks_cons: Wrap,
}

/// A constructor's spelling, a function of `lrat`'s whose body is the
/// constructor. Spelling the constructor itself instead (its body
/// instantiated) makes a literal far slower to check: the kernel types each
/// occurrence of a constructor's encoding afresh, and a call once.
struct Wrap {
    head: Term,
}

impl Wrap {
    fn at(&self, args: &[&Term]) -> Term {
        app(&self.head, args)
    }
}

fn app(f: &Term, args: &[&Term]) -> Term {
    let mut out = f.clone();
    for a in args {
        out = Term::AppAt { fun: Rc::new(out), arg: Rc::new((*a).clone()) };
    }
    out
}



impl Spell {
    fn nats(&self, xs: &[u64]) -> Term {
        let mut out = self.nat_nil.at(&[]);
        for &x in xs.iter().rev() {
            out = self.nat_cons.at(&[&nat_term(x), &out]);
        }
        out
    }

    fn clauses(&self, cs: &[Rc<Term>]) -> Term {
        let mut out = self.clause_nil.at(&[]);
        for c in cs.iter().rev() {
            out = self.clause_cons.at(&[c, &out]);
        }
        out
    }

    fn chunks(&self, cs: &[Term]) -> Term {
        let mut out = self.chunks_nil.at(&[]);
        for c in cs.iter().rev() {
            out = self.chunks_cons.at(&[c, &out]);
        }
        out
    }

    fn steps(&self, ss: &[(u64, Rc<Term>, Term)]) -> Term {
        let mut out = self.step_nil.at(&[]);
        for (id, c, hints) in ss.iter().rev() {
            let s = self.step.at(&[&nat_term(*id), c, hints]);
            out = self.step_cons.at(&[&s, &out]);
        }
        out
    }

    fn node(&self, here: Option<Rc<Term>>, even: Trie, odd: Trie) -> Trie {
        if here.is_none() && even.0.is_none() && odd.0.is_none() {
            return Trie(None);
        }
        let h = match &here {
            Some(c) => self.some.at(&[c]),
            None => self.none.at(&[]),
        };
        let term = self.map_node.at(&[&h, &self.trie(&even), &self.trie(&odd)]);
        Trie(Some(Rc::new(Node { here, even, odd, term })))
    }

    fn trie(&self, t: &Trie) -> Term {
        match &t.0 {
            None => self.map_empty.at(&[]),
            Some(n) => n.term.clone(),
        }
    }

    /// `t` with `key ↦ c`.
    fn set(&self, t: &Trie, key: u64, c: Rc<Term>) -> Trie {
        let (here, even, odd) = match &t.0 {
            None => (None, Trie(None), Trie(None)),
            Some(n) => (n.here.clone(), n.even.clone(), n.odd.clone()),
        };
        if key == 0 {
            return self.node(Some(c), even, odd);
        }
        let j = key - 1;
        if j % 2 == 0 {
            self.node(here, self.set(&even, j / 2, c), odd)
        } else {
            self.node(here, even, self.set(&odd, j / 2, c))
        }
    }
}

fn nat_term(n: u64) -> Term {
    crate::inductive::nat_lit(n as usize)
}

/// One stage of the refutation, outermost first.
enum Stage {
    /// `reaches_build(k, f, chunk, g, rest, built, ·)`, `g` a literal at a
    /// checkpoint.
    Build { k: Term, f: Term, chunk: Term, g: Term },
    /// `reaches_piece(f, cs, n, chunks, ·, ·)`: the next `n` clauses of the
    /// list as the tactic wrote it (`cs`), met against their chunks.
    Piece { f: Term, cs: Term, n: Term, chunks: Term },
    /// `reaches_drop(f, chunk, ·, ·)`: clauses no step names.
    Drop { f: Term, chunk: Term },
    /// `reaches_add(f, steps, ·, ·, ·)`, or `reaches_keep` into `g` holding
    /// `keys`.
    Add { f: Term, steps: Term, keep: Option<(Term, Term)> },
    /// `reaches_add_at(f, steps, g, ·, ·, ·, ·)`: `g` the literal it builds.
    AddAt { f: Term, steps: Term, g: Term },
    /// `reaches_done(f, steps, ·)`.
    Done { f: Term, steps: Term },
}

impl Host<'_> {
    /// `lrat::name` as a closed global term and its type.
    fn lrat_global(&self, name: &str) -> Result<(Term, Type, Level), Fault> {
        let key = format!("lrat::{name}");
        self.names
            .global(&key)
            .and_then(|info| self.raw_global_at(info.abs as usize))
            .ok_or_else(|| Fault::Ill(format!("`{key}` is not in scope: a SAT refutation needs `lrat` in the import closure")))
    }

    fn lrat_wrap(&self, name: &str) -> Result<Wrap, Fault> {
        Ok(Wrap { head: self.lrat_term(name)? })
    }

    fn lrat_term(&self, name: &str) -> Result<Term, Fault> {
        Ok(self.lrat_global(name)?.0)
    }

    /// `Sat(cs, vars)`.
    pub(super) fn sat_request(&self, run: &mut Run, cs: &RExpr, vars: u64) -> Result<SatView, Fault> {
        let at = run.scope_of(cs)?;
        let (refutes, refutes_ty, _) = self.lrat_global("reaches_refutes")?;
        let Type::Pi { dom_level, dom, .. } = &refutes_ty else {
            return Err(Fault::Ill("`lrat::reaches_refutes` is not a function".into()));
        };
        let mark = run.trail.len();
        let r = self.reify(run, cs, at).inspect_err(|_| run.restore(mark))?;
        let expected = dom.shift_global(run.world() as u32);
        if !r.level.equiv(dom_level) || !self.same_ty(run, at, &r.ty, &expected, dom_level)? {
            run.restore(mark);
            return Err(Fault::Ill(format!("the clauses are a `{}`, not a `List<List<Nat>>`", self.shown_ty(run, at, &r.ty))));
        }
        let Some(t) = run.committed_tm(&r.term) else {
            run.restore(mark);
            return Err(Fault::Ill("the clauses mention a hole nothing has solved".into()));
        };
        if heather_kernel::subst::local_bound(&Rc::new(t.clone())) != 0 {
            return Err(Fault::Ill("the clauses mention a local, and only a closed list of clauses is solved".into()));
        }
        let clauses = self.read_clauses(&t).map_err(|why| Fault::Ill(format!("reading the clauses: {why}")))?;
        let num_vars = clauses.iter().flatten().map(|&c| c / 2 + 1).max().unwrap_or(0).max(vars);
        let num_vars = u32::try_from(num_vars).map_err(|_| Fault::Ill("more variables than the solver takes".into()))?;
        let dimacs = clauses
            .iter()
            .map(|c| c.iter().map(|&l| to_dimacs(l)).collect::<Result<Vec<_>, _>>())
            .collect::<Result<Vec<_>, _>>()
            .map_err(Fault::Ill)?;
        let answer = heather_sat::solve(num_vars, &dimacs).map_err(|e| Fault::Ill(format!("the solver failed: {e:?}")))?;
        let steps = match answer {
            heather_sat::Answer::Satisfiable(model) => {
                return Ok(SatView::Model((0..vars as usize).map(|v| model.get(v).copied().unwrap_or(false)).collect()));
            }
            heather_sat::Answer::Refuted(steps) => steps,
        };
        // `reaches_refutes(t, proof)`: its type is the theorem's, at `t`,
        // and the empty formula the proof starts from is the one `r`'s type
        // names.
        let shape = || Fault::Ill("`lrat::reaches_refutes`'s statement is not the shape the host builds".into());
        let Some(Type::Pi { dom: r_dom, cod, cod_level, .. }) = inst(&refutes_ty, &[&t]) else { return Err(shape()) };
        let f0 = reaches_args(&r_dom).ok_or_else(shape)?.0;
        let (proof, proof_ty) = self.refutation(f0, &t, &clauses, &steps)?;
        let proof = Rc::new(proof);
        if std::env::var_os("HEATHER_SAT_TRACE").is_some() {
            let start = std::time::Instant::now();
            let fits = crate::oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel)
                .convert_type(&LocalCtx::nil(), Layer::Prog, &proof_ty, &r_dom, &Level::Zero)
                .is_ok();
            eprintln!("sat: the clauses as written against their chunks: {}, {:.2?}", if fits { "fits" } else { "past the budget" }, start.elapsed());
        }
        let t = Rc::new(t);
        let ty = (*cod).clone().apply_local(&LocalSubst::id(&LocalCtx::nil()).extended(Rc::clone(&proof)));
        let term = Term::AppAt { fun: Rc::new(Term::AppAt { fun: Rc::new(refutes), arg: t }), arg: Rc::clone(&proof) };
        let n = run.cx(at)?.gamma.len() as u32;
        Ok(SatView::Refuted(run.issue(at, Held::Term(term.shift_local(n), ty.shift_local(n), cod_level))))
    }

    /// The clause list `t` computes, each literal a checker literal.
    fn read_clauses(&self, t: &Term) -> Result<Vec<Vec<u64>>, String> {
        let world = self.goal_psi();
        let arena = ValueArena::new();
        let reader = Reader::with_fuel(&world, &arena, CLAUSE_FUEL);
        let mut budget = MAX_LITERALS;
        let mut out = Vec::new();
        for c in reader.list(reader.root(t.clone()), MAX_LITERALS)? {
            let lits = reader.list(c, budget)?;
            budget = budget.checked_sub(lits.len() + 1).ok_or_else(|| format!("more than {MAX_LITERALS} literals"))?;
            out.push(lits.into_iter().map(|l| reader.nat(l)).collect::<Result<Vec<_>, _>>()?);
        }
        Ok(out)
    }

    fn spell(&self) -> Result<Spell, Fault> {
        Ok(Spell {
            nat_nil: self.lrat_wrap("cert_nat_nil")?,
            nat_cons: self.lrat_wrap("cert_nat_cons")?,
            clause_nil: self.lrat_wrap("cert_clause_nil")?,
            clause_cons: self.lrat_wrap("cert_clause_cons")?,
            step: self.lrat_wrap("cert_step")?,
            step_nil: self.lrat_wrap("cert_step_nil")?,
            step_cons: self.lrat_wrap("cert_step_cons")?,
            map_empty: self.lrat_wrap("cert_map_empty")?,
            map_node: self.lrat_wrap("cert_map_node")?,
            none: self.lrat_wrap("cert_none")?,
            some: self.lrat_wrap("cert_some")?,
            chunks_nil: self.lrat_wrap("cert_chunks_nil")?,
            chunks_cons: self.lrat_wrap("cert_chunks_cons")?,
        })
    }

    /// A proof of `Reaches(f0, cs)` from the solver's steps, `f0` the empty
    /// formula as `reaches_refutes` spells it and `cs` spelled as its chunks
    /// appended.
    ///
    /// Every formula and clause list a stage's type mentions is taken from
    /// that theorem's own statement instantiated at the stage's arguments,
    /// so the kernel finds each stage's type the same syntax its parent
    /// expects: a stage is never compared with its parent by evaluation, and
    /// the only conversions that compute are the obligations (`adds(…) =
    /// True`, `check(…) = True`, a checkpoint's `… = literal`) and `cs`
    /// against its chunks.
    fn refutation(&self, f0: Term, t: &Term, clauses: &[Vec<u64>], steps: &[heather_sat::Step]) -> Result<(Term, Type), Fault> {
        let sp = self.spell()?;
        let bad = |why: String| Fault::Ill(format!("the solver's refutation does not fit the checker: {why}"));
        let shape = || Fault::Ill("a `lrat` stage theorem's statement is not the shape the host builds".into());
        match steps.last() {
            Some(s) if s.clause.is_empty() => {}
            _ => return Err(bad("it does not end in the empty clause".into())),
        }
        let lemma = |name: &str| self.lrat_global(name).map(|(t, ty, _)| (t, ty));
        let build = lemma("reaches_build")?;
        let drop = lemma("reaches_drop")?;
        let piece = lemma("reaches_piece")?;
        let same_clauses = self.lrat_term("reaches_same_clauses")?;
        let add = lemma("reaches_add")?;
        let keep = lemma("reaches_keep")?;
        let add_at = lemma("reaches_add_at")?;
        let pruned = knob("SAT_KEEP", 0) == 1;
        let done = lemma("reaches_done")?;
        let ok = self.lrat_term("reaches_true")?;
        let same = self.lrat_term("reaches_same")?;
        let nil = sp.clause_nil.at(&[]);
        let trace = std::env::var_os("HEATHER_SAT_TRACE").is_some();

        // Every clause's spelling once, shared by the chunks, the steps and
        // every checkpoint that holds it.
        let mut spelled: HashMap<u64, Rc<Term>> = HashMap::new();
        let mut lens: HashMap<u64, usize> = HashMap::new();
        for (i, c) in clauses.iter().enumerate() {
            spelled.insert(i as u64 + 1, Rc::new(sp.nats(c)));
            lens.insert(i as u64 + 1, c.len());
        }
        // The steps, a chunk at a time by the hinted literals they read, and
        // the last chunk naming each clause.
        let mut chunks: Vec<Vec<(u64, Rc<Term>, Term)>> = vec![Vec::new()];
        let mut last_use: HashMap<u64, usize> = HashMap::new();
        let mut read = 0usize;
        for s in steps {
            for h in &s.hints {
                read += *lens.get(h).ok_or_else(|| bad(format!("step {} hints clause {h}, which no earlier step adds", s.id)))?;
                last_use.insert(*h, chunks.len() - 1);
            }
            let lits: Vec<u64> = s.clause.iter().map(|&l| from_dimacs(l)).collect();
            read += lits.len();
            let c = Rc::new(sp.nats(&lits));
            spelled.insert(s.id, Rc::clone(&c));
            lens.insert(s.id, lits.len());
            chunks.last_mut().expect("a chunk").push((s.id, c, sp.nats(&s.hints)));
            if read >= knob("SAT_PER", STEP_PER) {
                chunks.push(Vec::new());
                read = 0;
            }
        }
        if chunks.last().is_some_and(Vec::is_empty) {
            chunks.pop();
        }
        if trace {
            eprintln!(
                "sat: {} clauses, {} steps, {} hints, {} step chunks",
                clauses.len(),
                steps.len(),
                steps.iter().map(|s| s.hints.len()).sum::<usize>(),
                chunks.len()
            );
        }
        // The checkpoint after chunk `n` (`None`: before the first): the
        // clauses held so far that a later chunk names, as keys and a trie.
        let checkpoint = |held: &std::collections::BTreeSet<u64>, n: Option<usize>| {
            let mut trie = Trie(None);
            let mut keys = Vec::new();
            for id in held {
                if last_use.get(id).is_some_and(|&u| n.is_none_or(|n| u > n)) {
                    trie = sp.set(&trie, *id, Rc::clone(&spelled[id]));
                    keys.push(*id);
                }
            }
            if trace {
                eprintln!("sat: checkpoint after {n:?} keeps {} of {} clauses", keys.len(), held.len());
            }
            (sp.nats(&keys), sp.trie(&trie))
        };

        let mut stages = Vec::new();
        let mut held = std::collections::BTreeSet::new();
        let mut trie = Trie(None);
        let mut f = f0;
        // The formula: the clauses some step names, a run of consecutive
        // ones at a time (`BUILD_PER` at most), a literal of the whole of it
        // every `EVERY` runs and after the last; the runs between, which no
        // step names, dropped.
        let live = |i: usize| last_use.contains_key(&(i as u64 + 1));
        let mut runs: Vec<(usize, usize, bool)> = Vec::new();
        for i in 0..clauses.len() {
            match runs.last_mut() {
                Some((start, end, l)) if *l == live(i) && (!*l || *end - *start < BUILD_PER) => *end = i + 1,
                _ => runs.push((i, i + 1, live(i))),
            }
        }
        let built_runs = runs.iter().filter(|r| r.2).count();
        let mut nth = 0;
        // The list as the tactic wrote it, met a piece of runs at a time.
        let mut listed = t.clone();
        let mut piece_start = 0;
        for (r, &(start, end, is_live)) in runs.iter().enumerate() {
            let cs: Vec<Rc<Term>> = (start..end).map(|i| Rc::clone(&spelled[&(i as u64 + 1)])).collect();
            let chunk = sp.clauses(&cs);
            if start == piece_start {
                let mut chunks = vec![chunk.clone()];
                let mut upto = end;
                for &(s2, e2, _) in &runs[r + 1..] {
                    if e2 - start > PIECE {
                        break;
                    }
                    let cs2: Vec<Rc<Term>> = (s2..e2).map(|i| Rc::clone(&spelled[&(i as u64 + 1)])).collect();
                    chunks.push(sp.clauses(&cs2));
                    upto = e2;
                }
                let n = nat_term((upto - start) as u64);
                let chunks = sp.chunks(&chunks);
                // What is left after it, `listed.drop(n)` as `r`'s type spells it.
                let at = inst(&piece.1, &[&f, &listed, &n, &chunks, &nil]).ok_or_else(shape)?;
                let Type::Pi { dom, .. } = at else { return Err(shape()) };
                let joined = reaches_args(&dom).ok_or_else(shape)?.1;
                let left = spine_args(&joined).last().map(|d| (*d).clone()).ok_or_else(shape)?;
                stages.push(Stage::Piece { f: f.clone(), cs: listed.clone(), n, chunks });
                listed = left;
                piece_start = upto;
            }
            if !is_live {
                stages.push(Stage::Drop { f: f.clone(), chunk });
                continue;
            }
            for i in start..end {
                let id = i as u64 + 1;
                trie = sp.set(&trie, id, Rc::clone(&spelled[&id]));
                held.insert(id);
            }
            nth += 1;
            let k = nat_term(start as u64 + 1);
            let g = if nth % knob("SAT_BUILD_EVERY", BUILD_EVERY) == 0 || nth == built_runs {
                sp.trie(&trie)
            } else {
                // `formula_from(chunk, k, f)` as `built`'s statement spells it.
                let built = inst(&build.1, &[&k, &f, &chunk, &f, &nil]).ok_or_else(shape)?;
                let Type::Pi { dom, .. } = built else { return Err(shape()) };
                let Type::Id { lhs, .. } = &*dom else { return Err(shape()) };
                (**lhs).clone()
            };
            stages.push(Stage::Build { k, f: f.clone(), chunk, g: g.clone() });
            f = g;
        }
        held.retain(|id| last_use.contains_key(id));
        let last = chunks.len() - 1;
        for (n, chunk) in chunks.iter().enumerate() {
            let steps = sp.steps(chunk);
            if n == last {
                stages.push(Stage::Done { f: f.clone(), steps });
                break;
            }
            held.extend(chunk.iter().map(|(id, _, _)| *id));
            if !pruned {
                for (id, c, _) in chunk {
                    trie = sp.set(&trie, *id, Rc::clone(c));
                }
            }
            if (n + 1) % knob("SAT_EVERY", EVERY) == 0 && !pruned {
                let g = sp.trie(&trie);
                stages.push(Stage::AddAt { f: f.clone(), steps, g: g.clone() });
                f = g;
            } else if (n + 1) % knob("SAT_EVERY", EVERY) == 0 {
                let (keys, g) = checkpoint(&held, Some(n));
                held.retain(|id| last_use.get(id).is_some_and(|&u| u > n));
                stages.push(Stage::Add { f: f.clone(), steps, keep: Some((keys, g.clone())) });
                f = g;
            } else {
                // `add_all(f, steps)` as `r`'s type spells it.
                let r = inst(&add.1, &[&f, &steps, &nil, &ok]).ok_or_else(shape)?;
                let Type::Pi { dom, .. } = r else { return Err(shape()) };
                let next = reaches_args(&dom).ok_or_else(shape)?.0;
                stages.push(Stage::Add { f: f.clone(), steps, keep: None });
                f = next;
            }
        }
        // Inside out: each stage's proof takes the next one's, and the
        // clauses still to add are read off the next one's type.
        let mut proof: Option<(Term, Type)> = None;
        for stage in stages.into_iter().rev() {
            let inner = proof.take();
            let mut rest = || -> Result<(Term, Term), Fault> {
                let (r, r_ty) = inner.clone().expect("a stage inside");
                Ok((r, reaches_args(&r_ty).ok_or_else(shape)?.1))
            };
            let (args, lemma) = match stage {
                Stage::Done { f, steps } => (vec![f, steps, ok.clone()], &done),
                Stage::Add { f, steps, keep: None } => {
                    let (r, cs) = rest()?;
                    (vec![f, steps, cs, ok.clone(), r], &add)
                }
                Stage::Add { f, steps, keep: Some((keys, g)) } => {
                    let (r, cs) = rest()?;
                    let same_g = app(&same, &[&g]);
                    (vec![f, steps, keys, g, cs, ok.clone(), same_g, r], &keep)
                }
                Stage::AddAt { f, steps, g } => {
                    let (r, cs) = rest()?;
                    let same_g = app(&same, &[&g]);
                    (vec![f, steps, g, cs, ok.clone(), same_g, r], &add_at)
                }
                Stage::Piece { f, cs, n, chunks } => {
                    let (r, _) = rest()?;
                    let at = inst(&piece.1, &[&f, &cs, &n, &chunks]).ok_or_else(shape)?;
                    let Type::Pi { dom, .. } = at else { return Err(shape()) };
                    let Type::Id { rhs, .. } = &*dom else { return Err(shape()) };
                    let took = app(&same_clauses, &[rhs]);
                    (vec![f, cs, n, chunks, took, r], &piece)
                }
                Stage::Drop { f, chunk } => {
                    let (r, cs) = rest()?;
                    (vec![f, chunk, cs, r], &drop)
                }
                Stage::Build { k, f, chunk, g } => {
                    let (r, cs) = rest()?;
                    let built = app(&same, &[&g]);
                    (vec![k, f, chunk, g, cs, built, r], &build)
                }
            };
            let refs: Vec<&Term> = args.iter().collect();
            if trace {
                eprintln!("sat: stage {}", ["done", "add", "keep", "drop", "build", "add_at", "piece"][[&done, &add, &keep, &drop, &build, &add_at, &piece].iter().position(|l| std::ptr::eq(*l, lemma)).unwrap_or(0)]);
                self.trace_obligations(&lemma.1, &refs);
            }
            let stage_ty = inst(&lemma.1, &refs).ok_or_else(shape)?;
            proof = Some((app(&lemma.0, &refs), stage_ty));
        }
        Ok(proof.expect("at least the last stage"))
    }
}

impl Host<'_> {
    /// Each `X = Y` parameter of a stage, converted on its own and timed
    /// (`HEATHER_SAT_TRACE`): which obligation is past the kernel's budget,
    /// and with any other value than `fit` the fraction of it each needs.
    fn trace_obligations(&self, ty: &Type, args: &[&Term]) {
        let mut cur = ty.clone();
        for (i, a) in args.iter().enumerate() {
            let Type::Pi { dom, cod, .. } = cur else { return };
            if let Type::Id { level, ty: t, rhs, .. } = &*dom {
                let actual = Type::Id { level: level.clone(), ty: Rc::clone(t), lhs: Rc::clone(rhs), rhs: Rc::clone(rhs) };
                let start = std::time::Instant::now();
                let fits = |fuel: u64| {
                    crate::oracle::SemanticOracle::in_world(self.goal_psi(), fuel)
                        .convert_type(&LocalCtx::nil(), Layer::Prog, &actual, &dom, &Level::Zero)
                        .is_ok()
                };
                if std::env::var("HEATHER_SAT_TRACE").is_ok_and(|v| v == "fit") {
                    if !fits(self.policy.fuel) {
                        eprintln!("sat: obligation {i}: past the budget, {:.2?}", start.elapsed());
                    }
                    cur = (*cod).clone().apply_local(&LocalSubst::id(&LocalCtx::nil()).extended(Rc::new((*a).clone())));
                    continue;
                }
                let (mut lo, mut hi) = (0u64, self.policy.fuel * 64);
                if fits(hi) {
                    while hi - lo > hi / 64 {
                        let mid = lo + (hi - lo) / 2;
                        if fits(mid) { hi = mid } else { lo = mid }
                    }
                }
                eprintln!("sat: obligation {i}: needs {:.3} of the budget, {:.2?}", hi as f64 / self.policy.fuel as f64, start.elapsed());
            }
            cur = (*cod).clone().apply_local(&LocalSubst::id(&LocalCtx::nil()).extended(Rc::new((*a).clone())));
        }
    }
}

fn knob(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// `ty` instantiated at `args`, one Π at a time; closed terms only.
fn inst(ty: &Type, args: &[&Term]) -> Option<Type> {
    let mut out = ty.clone();
    for a in args {
        let Type::Pi { cod, .. } = out else { return None };
        out = (*cod).clone().apply_local(&LocalSubst::id(&LocalCtx::nil()).extended(Rc::new((*a).clone())));
    }
    Some(out)
}

/// The arguments of an application, the first first.
fn spine_args(t: &Term) -> Vec<&Term> {
    let mut out = Vec::new();
    let mut t = t;
    loop {
        match t {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
                out.push(&**arg);
                t = fun;
            }
            _ => break,
        }
    }
    out.reverse();
    out
}

/// `Reaches(f, cs)`'s formula and clauses.
fn reaches_args(ty: &Type) -> Option<(Term, Term)> {
    let Type::El { tm, .. } = ty else { return None };
    match spine_args(tm)[..] {
        [f, cs] => Some((f.clone(), cs.clone())),
        _ => None,
    }
}
