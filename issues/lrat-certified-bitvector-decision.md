---
title: Certified bitvector decisions: bit-blast, external SAT, kerneltime LRAT check
status: open
labels: [proofs,solver,bitvec,x86,design,research]
area: tactics
created: 2026-09-24
updated: 2026-11-17
---

Build (or first cost) a **kerneltime decision procedure for bitvector goals
with certificates**: bit-blast to CNF, run an external SAT solver, and have
the kernel check an LRAT certificate with a checker proved sound once. This
is Lean's `bv_decide` design: generators need no verification, outputs
carry certificates, which is Heather's own stance applied to decision
procedures.

## Why now

- x86 proofs are dominated by bitvector facts (flags, carries, width
  arithmetic). CutSat ([[cutsat-linear-integer-arithmetic]]) covers linear
  arithmetic, not bit-level identities.
- The kernel already has native bitvector values (`Val::BitRun`) and
  accelerated folds, so evaluating a bit-blasted circuit on concrete
  assignments is cheap. The open question is the **checker's** kerneltime
  cost on real certificates, which is mostly list/array manipulation over
  clause ids.
- [[reflection-through-decide-instances]] (closed) settled that a fast
  procedure behind a `Decide` instance keeps one notion at proof sites. An
  LRAT-backed instance is the same shape with an external oracle.

## Reading

- Cruz-Filipe, Heule, Hunt, Kaufmann, Schneider-Kamp, *Efficient Certified
  RAT Verification*, CADE 2017 — `docs/papers/1612.02353.pdf` (the LRAT format).
- Szeider, *Streaming LRAT Certificates into Lean Theorems* (2026) —
  `docs/papers/2607.00815.pdf` (a resumable, streaming checker in Lean core).

## Acceptance (first round, investigation)

Hand-check one small unsatisfiable CNF's LRAT proof with an in-language
checker on a probe, measure how the kernel's cost grows with certificate
size (a shape, not a number), and identify what dominates: clause lookup,
unit propagation, or list rebuilding. Decide from that whether the checker
needs a representation change (arrays/maps with good kernel behaviour)
before a generator is worth writing.

## What it assumes from elsewhere

- **[[kernel-acceleration-policy]]** owns what the kernel may accelerate.
  Assumed here: only that a checker is ordinary library code; no kernel
  case for it.
- **[[decide-class]]** owns the `Decide` interface.

## Log

- 2026-10-25: Second customer, from `docs/surveys/multi-width-bitvector-survey.md` §5 (Bhat et al., OOPSLA 2026, `docs/papers/3839511.pdf`). A multi-width claim bounded by a global width o (all widths below 65, say) reduces to one QF_BV query at width o by masks, instead of o^k queries, one per width assignment. The reduction's correctness (the paper's Lemma 4.2) is a structural induction that Heather can prove once, where the paper trusts an unverified translator. What remains is exactly this issue's decision. Rung B of [[bitvec-width-generic-decision]] (k-induction over transducers) also needs it. Benchmarks for the first round should include a wide, mask-heavy query.
- 2026-11-05: gardener: cites a file it shares with [[function-ir-narrow-arithmetic]] (`docs/surveys/multi-width-bitvector-survey.md`).
- 2026-11-16: first round done. `lib/std/tactic/lrat.hthr` is the checker
  (literals as `2v`/`2v + 1`, the clause database a `NatMap` keyed by id,
  reverse unit propagation along the hints, no deletions) with its soundness
  proof: `refuted` says that once `check(formula_of(cs), steps) = True`,
  every valuation makes some clause of `cs` false. Probes in
  `lib/_tests/std/tactic/lrat_tests.hthr`, written by `scripts/lrat-probes`
  (Tseitin miters of `a + b ≠ b + a` and `a * b ≠ b * a`, a small untrusted
  CDCL solver in Python, since a vendored solver could not be built here).
  What the measurements say:
  - **Cost is linear in the hinted literals.** Each one is a variable lookup
    in the assignment's `NatMap` (logarithmic in the variable count), each
    unit an insertion, each hint a lookup by id (logarithmic in the id).
    Walking lists and `NatMap` nodes dominates; nothing is quadratic. A
    resolution-chain format over sorted clauses was measured too and costs
    the same, so the checker stays plain LRAT: no representation change.
  - **One `refl` holds a few hundred hints** before the conversion budget, so
    a proof is cut into stage theorems: `adds(f_k, chunk) = True` per stage,
    `add_all` naming the formula a stage leaves, `check` on the last, and
    `adds_sound` chaining them. Stages are cut by hinted literals, not by
    steps (learned clauses grow), and check in parallel on the kernel's
    workers.
  - **The formula must be a literal map**, not `formula_of(list)`: building
    it costs a large fraction of a stage, and every stage would rebuild it.
    For the same reason every few stages leave their formula as a literal
    checkpoint (`f_k_is: add_all(f_{k-1}, c_k) = f_k` by `refl`), else the
    replayed insertions grow with the stage's index and late stages run out.
  - 8-bit addition commutes: 655 steps, tens of thousands of hints, 83 stages;
    the whole refutation checks in seconds of wall time on eight workers.
  Next, in order: (1) a host request that runs an untrusted solver and
  returns LRAT; (2) a bit-blaster written in Heather, from `BitVec`
  expressions to a circuit to CNF, proved once (a valuation of the words
  satisfies the clauses), so `refuted` turns into the bitvector identity;
  (3) the tactic, which must emit the stages as declarations of their own;
  (4) the UTF-8 word-to-spec bridges in `examples/utf8/utf8_check.hthr` as
  the first customer.
- 2026-11-16: the solver is CaDiCaL (Minus chose it after the evaluation in
  the levers thread: native LRAT for every technique, MIT, maintained, what
  Lean's `bv_decide` runs). Vendored unedited as `vendor/cadical` (release
  3.0.1), compiled by `crates/sat` (`heather-sat`), which collects the proof
  in memory through CaDiCaL's tracer, trims it to what the empty clause
  depends on and renumbers it into the formula's own numbering;
  `heather sat <file.cnf>` prints it, and `scripts/lrat-probes` uses it by
  default. Its proofs are far shorter than the naive solver's on adders
  (8-bit addition commuting: a few stages instead of 83) and comparable on
  multipliers, which stay hard for any SAT solver. Gotcha: the tracer's ids
  for the input clauses skip where the input has units, so `heather-sat`
  maps them by the order and contents of the clauses reported, never by id.
- 2026-11-17: the bit-blaster, `lib/std/tactic/bitblast.hthr`, proved once.
  Expressions `BVExpr` (inputs `BVar(offset, width)` read zero-extended or
  truncated at the width a predicate chooses, constants, not/and/or/xor,
  addition, shifts by a constant) under predicates `BVPred` (equality,
  unsigned less-than, Boolean connectives, iff) are built into an
  and-inverter graph whose node 0 is false and whose next `K` nodes are the
  input bits, so every occurrence of an input shares its nodes. Tseitin
  clauses over the graph, numbered as the checker numbers literals, and the
  end theorem `BVPred::unsat_sound`: if no assignment satisfies
  `p.clauses(K)`, `p.eval` is true at every input. The proof is a growth
  invariant: a literal built from circuit `c` means its value in every
  circuit grown from `c`, which composes without separate stability lemmas.
  Ands with a constant input fold away; without that, UTF-8's 64-bit masks
  on zero-extended bytes made thousands of clauses, with it tens.
  `scripts/lrat-probes blast` takes the clauses from `heather eval`, refutes
  them with CaDiCaL and writes the stages plus `<name>_holds`;
  `lib/_tests/std/tactic/bitblast_tests.hthr` has De Morgan, `x + y = y + x`
  and `x + x = x << 1` over bytes, `x < x + 1` unless `x = 255`, and the
  decoder's continuation and overlong tests at 64 bits, each in under a
  second, with `x + y = y + x` and De Morgan carried back to `BitVec` through
  `BitVec::pair_bits`. Cost shape: computing the clauses by `refl` is cheap
  (64-bit De Morgan well under a second); the limit is the formula literal
  and the stages, as before. 64-bit addition commuting (4193 clauses) runs
  out of fuel building its formula literal in one `refl`, so the generator
  must build the formula in chunks too. Next: chunked formulas; the tactic
  that reflects a `BitVec` goal into `BVPred` and lays out its words;
  subtraction, multiplication, extraction and concatenation; folding equal
  and opposite operands.
- 2026-11-17: the tactic, `by bv_decide()` (`lib/std/tactic/bv_decide.hthr`,
  design in `docs/tactics/bv-decide-design.md`). A new host request
  `Sat(cs, vars)` (tag 38, `crates/elab/src/host/sat.rs`) evaluates a closed
  clause term, runs CaDiCaL in process, and answers with a model or with the
  whole refutation as one term (`reaches_refutes`), its stages each one
  conversion: input clauses built a run at a time (`reaches_build`), runs no
  step names dropped (`reaches_drop`), steps added a chunk at a time
  (`reaches_add`) with a literal checkpoint every few chunks
  (`reaches_add_at`), the empty clause last (`reaches_done`). Each stage's
  statement is read off the lemma instantiated at its arguments; built any
  other way, parent and child types were compared by evaluation. The
  bit-blaster gained subtraction, negation, multiplication, signed
  less-than, slices, sign extension, concatenation, single bits, Boolean
  atoms and `PXor`. The tactic reads `BitVec`/`Bool` claims (unfolding
  definitions it does not know), lays the atoms into one bit stream, and
  carries `BVPred::unsat_sound` back by congruence over the sides abstracted
  at the atoms; a satisfiable predicate fails naming a counterexample. First
  customer: `examples/utf8/utf8_check.hthr`'s `cont_word` and the 2-, 3- and
  4-byte code words now prove by `bv_decide()` as word equations, replacing
  the `Fintype` enumerations, the payload lemmas and `bv_omega`, at about the
  same check time. Probes: `lib/_tests/std/tactic/bv_decide_tests.hthr`.
  Measured: a step chunk's check is linear in its hinted literals (about four
  fifths of the budget per 1100 on an 8-bit adder's proof, more as the
  formula deepens, so chunks are 800); a literal checkpoint costs about its
  new insertions, its comparison cheap; pruning a checkpoint to the live
  clauses (`reaches_keep`, `reaches_trim`) costs a lookup and an insertion
  per kept clause, several budgets at thousands of clauses, so it is off.
  Multiplication of two variables stays out of reach (8-bit `x * y = y * x`
  is over a million hints).
