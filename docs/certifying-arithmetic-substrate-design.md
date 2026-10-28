# Certifying arithmetic substrate and CutSat direction

## Decision

Keep the current Omega solver as a small, deterministic first pass. Build
complete linear integer arithmetic as a model-based CutSat solver over shared
arithmetic reflection and certificate infrastructure. Do not turn Omega's
`Problem` into a universal arithmetic solver, and do not make a full
dark/grey-shadow implementation the prerequisite for `linarith` or `grind`.

The trusted boundary stays unchanged: Rust searches and constructs an ordinary
Heather proof; the existing kernel checks that proof. A candidate model is a
diagnostic/search artifact, never a proof that a proposition is satisfiable.

## Evidence from the current Omega rail

The original generated rail searched `[-4, 4]` but did not assert those bounds,
so absence of a model was not a complete classification. The replacement puts
the box into every problem and pins two deterministic populations:

| population | satisfiable | contradicted by real shadow | integer-unsat miss |
| --- | ---: | ---: | ---: |
| 5,400 small grid systems | 4,414 | 986 | 0 |
| 20,000 seeded systems | 11,074 | 8,835 | 91 |

The first seeded miss (680) minimizes to:

```text
 2x + 3y >= -2
 2x + 5y <=  0
          y >=  1
```

The first two inequalities imply `y <= 1`; therefore `y = 1`, after which
they require both `2x >= -5` and `2x <= -5`. The real relaxation has the point
`(-5/2, 1)`, but the integer system is contradictory. Pugh's nightmare is also
pinned as a real-shadow miss.

This establishes that an integer-complete fallback is useful. It does not show
that grey-shadow enumeration should become the general arithmetic engine: only
0.455% of the broader generated sample needs more than the present fast path,
and complete grey shadows have coefficient-sensitive branching.

## What modern Lean's CutSat actually does

The pinned Lean reference is commit
`31aea96d017b53c6acf56577b20e4ef48421af9e`. Its implementation lives under
`src/Lean/Meta/Tactic/Grind/Arith/Cutsat` and is based on the model-based
procedure in *Cutting to the Chase: Solving Linear Integer Arithmetic*.

Important implementation choices:

- Four explicit constraint kinds: `p = 0`, `p <= 0`, `p != 0`, and `d | p`.
  Each constraint carries a solver-specific justification object.
- Sorted affine polynomials are indexed by their maximal variable. Equalities
  eliminate eagerly; divisibility constraints are maintained in solved form,
  with at most one per variable; lower, upper, and disequality arrays retain
  the other constraints.
- Search assigns variables in order. For each variable it computes the best
  lower and upper bound under the partial assignment, intersects those with a
  divisibility progression, and avoids forbidden disequality values.
- It first tries rational model construction. If the result is imprecise, the
  integer pass uses Cooper-Left/Right conflict rules. This makes the cheap real
  shadow a discovery tool inside a complete procedure rather than a separate
  all-or-nothing algorithm.
- Cooper and disequality splits use decision variables. Conflicts collect the
  decisions they actually depend on, permitting non-chronological backtracking.
  State snapshots are used instead of a mutation trail.
- Assertion is incremental. A newly derived constraint is normalized,
  substituted through solved equalities, checked for triviality/conflict,
  indexed by its leading variable, and may invalidate only the affected suffix
  of the candidate assignment.
- Proof construction is delayed and cached. Search justifications form a
  shared graph; final reconstruction creates local declarations for repeated
  variables/polynomials/expressions and emits a kernel-checkable term.
- The surrounding `grind` integration can expose the candidate assignment to
  model-based theory combination. Nonlinear multiplication and non-literal
  division/modulus remain opaque theory terms; equal candidate values suggest
  congruence case splits rather than becoming trusted facts.

The reference also has pragmatic incompleteness controls: a configured step
limit can stop search and return an imprecise/partial assignment. Heather
should preserve that distinction explicitly as `ResourceLimit`, not report it
as ordinary logical stuckness.

## Heather boundaries

Share representations and proof plumbing, not solver policy.

### 1. Arithmetic reflection

Extract the carrier-independent pieces currently embedded in
`omega_cert.rs`:

```text
AtomId
AtomTable<Term>              -- structural interning plus display spelling
Affine<Coeff>                -- constant + sorted/dense atom coefficients
Domain = Int | NatEmbedded
ReflectedConstraint          -- Eq, Le, Ne, Dvd with source evidence
```

Reflection owns affine normalization, literal scaling, opaque-atom sharing,
Nat-to-Int side conditions, and source evidence. It does not choose Omega,
CutSat, or linarith. The first extraction should retain checked `i128` and its
structured overflow refusal; arbitrary-precision coefficients are a later,
separable representation change.

**Which facts are reflected.** Omega reads every local, but it refutes with
the nearest ones first (`relevant_layers`, `omega_cert.rs`). The first
attempt uses only the facts over the negated goal's own atoms. Each further
layer adds the atoms of every fact touching the last one, and the facts over
those, up to `RELEVANCE_WIDENINGS` layers. The last attempt uses every fact.
A division atom brings its dividend's atoms, and a fact with no atoms is in
every layer. Each attempt collects again over only its facts, so the atom
list, and with it every row of the certificate, has only the atoms in play.
Layers are an order, not a claim, so the attempt over every fact still finds
a contradiction among facts away from the goal. Only that last attempt
records a failure report.

Connectivity alone keeps too much. In a proof about machine words, every
equation mentions the same `v`, so the whole context is one component. The
facts *over* the goal's atoms are what a side condition like `v * 2 + v * 2 <
2^60` needs. The filter also spares omega from spelling atoms of unrelated
facts, which is where a misspelled atom used to fail
(issues/omega-relevant-facts-only.md).

For future nonlinear tactics, commutative-ring normalization may intern a
canonical monomial as an `AtomId`. That lets linear solvers reason about
relations among monomials without pretending that they understand nonlinear
semantics.

### 2. Solver-local constraints and justifications

Omega keeps `Interval` rows and its existing `Derivation` enum. CutSat gets
separate `EqConstraint`, `LeConstraint`, `NeConstraint`, `DvdConstraint`, and
`CutDerivation` types. A small generic append-only arena may provide IDs,
reachability, memoized replay, and proof slicing, but the derivation node enums
must remain solver-specific and exhaustive.

This avoids a lowest-common-denominator `Constraint` interface while retaining
the part Heather already benefits from: one derived fact, one node, one shared
certificate binding.

### 3. Structured solver outcomes

The orchestration boundary should distinguish:

```text
Contradiction { root, reachable, stats }
CandidateModel { integer assignments, completeness }
Stuck { residual constraints, reason }
ResourceLimit { partial model, residual constraints, stats }
Unsupported { reflected fragment and reason }
```

Omega normally returns either `Contradiction` or `Stuck::RealShadowSurvived`.
CutSat may return a complete integer candidate for its supported fragment, but
frontends must describe it as a model only for the reflected constraint set.
Future `grind` may use that candidate heuristically for theory combination.

### 4. Certificate reconstruction

Retain the current ordinary-proof boundary, but move from solver-specific
string assembly toward a shared certificate builder that can:

- bind a reachable derivation once and refer to it many times;
- record the exact lemma set and source assumptions;
- build deterministic local proof blocks/ASTs;
- report generated-term size before elaboration;
- leave every solver rule represented by a named Heather theorem.

The builder is infrastructure, not a reflected proof checker. Omega and CutSat
remain responsible for mapping their typed derivations to theorem applications.

**Constants past a machine word.** Coefficients are checked `i128`, and word
arithmetic reaches 2^64 in bounds, carries, and search steps nobody wrote.
`nat_lit` (`omega_cert.rs`) is the one place a constant becomes source, and it
spells the numeral it is: numerals are unbounded since 2026-09-26
(`docs/wide-numerals-design.md`). Before that a constant above a `u64` token
was spelled over its top word one byte at a time. `nat_lit_value` reads the
spelling back, because a later round reflects the certificate's own facts.
For the same reason, a closed
`nat::Nat::pow(a, b)` reflects as its value when `(a + 1) * b` is within
`POWER_EVALUATION_STEPS`, and the kernel checks the value by evaluation. A
larger power stays an atom (issues/omega-constants-beyond-u64.md).

### 5. Orchestration and reuse

The initial tactic path is:

```text
reflect affine goal/context
  -> Omega fast pass
  -> if RealShadowSurvived, CutSat
  -> reconstruct contradiction or return structured state
```

Later consumers reuse narrower pieces:

- `linarith`: affine/ring reflection, atom table, certificate builder, and
  ordered-domain metadata; its Farkas-style search is not CutSat.
- nonlinear arithmetic: ring normalization and monomial atoms, then generates
  additional sound facts for a linear backend.
- `grind`: incremental assertion, candidate models, propagation, and decision
  dependency information from CutSat.
- counterexample tooling: complete candidate models when available, clearly
  separated from heuristic partial assignments.

## Implementation slices

1. Extract `Affine`, atom interning, reflected relations, and display metadata
   from `omega_cert.rs` without changing Omega reports or certificates.
2. Add a CutSat search-only core for `Eq` and `Le`, using the two pinned thin
   systems and the generated 91-gap corpus as completeness acceptance. Return
   candidate models and typed cut derivations; do not expose a tactic yet.
3. Add Heather lemmas and reconstruction for real-bound combination and
   Cooper-Left/Right, then place CutSat behind Omega on contradiction goals.
4. Add disequality and divisibility constraints, reusing the existing Omega
   frontend coverage for negated relations and literal div/mod.
5. Add incremental invalidation, decision dependency sets, resource limits,
   and a model API suitable for `grind`.
6. Only then extract ordered-ring normalization for `linarith`; share the
   substrate but keep its solver and proof rule vocabulary independent.

Each slice must keep deterministic stats, replayable generated failures,
reachable-proof slicing, and the ordinary kernel gate.

### Landed foundation

The first representation extraction landed in `crates/elab/src/arithmetic.rs`:
checked `Affine`/`Coeffs`, stable `AtomId`/`AtomTable`, `Domain`, `Relation`, and
generic `ReflectedConstraint<A, E>`. Omega re-exports its old `LinearExpr`,
`Coeffs`, `Relation`, `Failure`, and `Z` names, so this is an internal ownership
change rather than a solver API break. Its frontend now uses the shared atom
table and relation record while keeping division expansion, interval lowering,
and proof evidence Omega-specific. Existing reports pin identical opaque-atom
sharing and label order.

The search-only core now lives in `crates/elab/src/cutsat.rs`. Its public input
is deliberately the first `Eq`/`Le` slice; equality lowers to two normalized
inequalities. Search assigns variables in order, learns real projections, and
uses Cooper-Left/Right cases with internal divisibility constraints. Compatible
congruences are combined by generalized CRT. In the two-variable acceptance
slice, a combined-congruence conflict can exclude the current lower-variable
value by an explicit exhaustive split; higher-dimensional symbolic
divisibility interaction remains a structured resource refusal.

The core returns either a checked integer model, a contradiction root plus the
reachable typed derivation slice, or partial model/residual constraints with a
resource reason. Omega routes real-shadow survivors through this untrusted
search; the kernel remains the only acceptance boundary. The deterministic
20,000-system boxed rail pins 11,074 models and 8,926 contradictions, closing
all 91 real-shadow misses.

### Complete search (2026-10-28)

The search is now complete over `≤`, `=`, `≠` and `∣` with no refusal shape
left (`ResourceReason` is only step/case budgets and a repeated-conflict
guard):

- **Solved-form divisibility.** At most one divisibility constraint per
  leading variable. A second one on the same variable is combined with the
  first by the solve-div rule: `m ∣ a·x + p` and `n ∣ b·x + q` with
  `g = gcd(a·n, b·m) = u·a·n + v·b·m` become `m·n ∣ u·n·(a·x + p) + v·m·(b·x + q)`
  (still on `x`) and `g ∣ b·(a·x + p) − a·(b·x + q)`, which no longer mentions
  `x`. When the variable has no admissible value left, `d ∣ a·x + p` drops
  it: `gcd(a, d) ∣ p`.
- **Cooper with a carried divisibility.** A conflict between a lower bound, an
  upper bound and the variable's divisibility splits into
  `lcm(A, A·d / gcd(A·d, |c|))` cases (left; the right rule is the mirror). Each
  case carries the cut bound, the selected residue and the rewritten
  divisibility.
- **Disequalities.** `p ≠ 0` is checked against the model; a conflict splits
  into `p + 1 ≤ 0` and `−p + 1 ≤ 0` only then.
- Every split case is a **scope**. A derived node's scope is the deepest
  scope among its premises, so a fact learned in one case is never visible in
  a sibling, and a fact learned from the root alone is shared by every case.

### Scoped DAG certificate (2026-10-28)

`crates/elab/src/cutsat_cert.rs` writes the reachable derivation slice as one
`have` per node, in id order, inside the block of the node's scope. `have` is
opaque, so the kernel checks each node once and every later use is a variable
(`issues/arithmetic-certificate-dag-sharing.md`, 2026-09-25 note). A node's
statement is a row fact over the atom list:

- `dot(ROW, atoms) <= BOUND` for `p ≤ 0`;
- `cut_dvd(D, dot(ROW, atoms) + C)` for `D ∣ p`, where
  `cut_dvd(d, v) = Exists(w. v = d·w)`;
- `dot(ROW, atoms) + C ≠ 0` for `p ≠ 0`;
- `False` for a conflict.

Each rule is one named lemma in `lib/std/tactic/omega.hthr`: `divide_upper`
(tighten), `cut_resolve`, `cut_dvd_combo` (solve-div, both outputs),
`cut_dvd_drop`, `cut_constant_upper` / `cut_constant_dvd` /
`cut_constant_diseq`, `cut_diseq` (the split), and `cut_cooper_left` /
`cut_cooper_right`. A Cooper node's cases are a `Below(period, P)` chain
(`below_zero`, `below_succ`), each case a `λ h_cut h_sel h_car => { … }`
block. Closed arithmetic in side conditions (row splits, period divisibility
witnesses, threshold comparisons) is `refl` or a literal comparison, decided
by evaluation.

The Cooper lemmas are proved once over abstract values
(`cut_cooper_core`, `cut_cooper_{left,right}_values`) and instantiated at
`dot` rows by `dot_pivot`. Two `omega` gotchas shaped them: Omega reads a
`dot(…)` term specially, so lemmas whose context mentions symbolic `dot`
terms must state the arithmetic over plain `Int`s; and an `Exists` witness's
`.proof` has a β-redex type that Omega skips, so it is bound under an
annotated `have` first.

No certificate re-enters Omega. Pugh's nightmare and the seed-680 gap are
kernel-checked through `omega` as library probes
(`lib/_tests/std/tactic/omega_tests.hthr`); the cost of Pugh is dominated by
elaborating the certificate, then the kernel gate, with the search itself
negligible. The old nested-continuation route did not finish under the rail.

### Disequalities reach CutSat (2026-10-28)

Omega's frontend reflects a context `x ≠ y` at Int, and at Nat through
`Int::ofnat_ne`, as `Relation::Ne`, with evidence
`normalized_ne_value : dot(row) + c ≠ 0`. Omega's real shadow ignores these
rows (they sit after every bounded fact, so Omega's assumption indices are
unchanged); CutSat reads them with `assume_ne` and splits one only where its
model lands on the excluded value. Before, each disequality was split up
front and Omega re-ran on both sides, `2ⁿ` runs for `n` disequalities. The
up-front split stays as the fallback for shapes CutSat is not given:
`¬(d ∣ e)` still splits on its remainder.

## Why dark/grey shadows remain open

Dark shadows may be a useful sufficient shortcut for exactly the thin regions
the classifier now exposes. Grey shadows may also outperform general CutSat on
some small bounded coefficients. They should therefore be compared as an
Omega optimization against the generated miss corpus and CutSat fallback.

They are not the shared foundation: they do not naturally provide candidate
models, incremental theory propagation, disequality/divisibility state, or the
ordered-ring substrate wanted by future tactics.

## References

- William Pugh, [The Omega Test: a fast and practical integer programming
  algorithm for dependence analysis](https://www.cs.utexas.edu/~pingali/CS380C/2019/papers/pugh92omega.pdf).
- Dejan Jovanovic and Leonardo de Moura, [Cutting to the Chase: Solving Linear
  Integer Arithmetic](https://doi.org/10.1007/978-3-031-37703-7_13).
- Lean, [Linear Integer Arithmetic in
  `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Integer-Arithmetic/).
