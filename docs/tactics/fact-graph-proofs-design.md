# Fact-graph proofs: minimal library-free core for declarative waypoints

Status: **design notes (parked for later)**, 2026-11-23. Tracked by
`issues/fact-graph-proofs.md` (`area: tactics`, `milestone: [tac-general]`).

This note records the design of a declarative, low-entropy proof engine —
"waypoint" or "fact-graph" proofs — focused specifically on **what minimal,
library-agnostic core makes it useful on a brand-new user type with no large
library behind it**. It is not scheduled yet; scoped proof worlds
(`docs/language/proof-worlds-design.md`) are built first.

---

## 1. Motivation

Today a proof in Heather either spells out low-level term plumbing
(`same_trans`, `cong_fn`, `ofRat_*`, `j` transports, `.left`/`.right`
projections) or delegates a closed subproblem to a single decision procedure
(`omega`, `linarith`, `ring`, `simp_only`). In a real proof like
`CReal::exp_sub_lin_near` (`lib/std/analysis/real_exp.hthr`), over 80% of the
lines carry zero mathematical entropy: they move casts past operators, split
and reassemble `AbsLe` conjunctions, propagate positivity, and chain
transitivity/respects steps.

The goal is a proof style where the author writes **only the creative
mathematical waypoints** (which lemmas to cite, which nonlinear or non-obvious
intermediate bound to cross through), and a small certifying engine bridges
adjacent waypoints — emitting a kernel-checked proof term and an inspectable
explanation (`--explain-proof`, mirroring `--explain-optimizer`).

```heather
// Illustrative target shape (not built):
proof {
    cite exp_rat_sub_lin(p, 1), exp_dev(h, p);
    waypoint p * p <= (k + g) * (k + g) <= k * k + 2 * g;
}
```

---

## 2. The five library-free fundamentals

A fact-graph engine only earns its keep if it works immediately on a
brand-new user-defined structure with two axioms and one lemma, without
waiting for a large stdlib. Almost all proof plumbing falls into five generic,
domain-independent primitives:

1. **Congruence + preorder closure (e-graph + directed relation graph).**
   Generalise `grind`'s equality e-graph (`docs/tactics/grind-design.md`,
   [[egraph-setoid-path-algebra]]) to arbitrary relations tagged as equivalences
   (`Refl`/`Sym`/`Trans`) or preorders (`Refl`/`Trans`), together with
   congruence/monotonicity edges (`Respects`/`Mono`). On any new type, this
   retires manual `trans`, `sym`, `cong_fn`, `respects`, `le_trans`, and `j`
   chains at once.

2. **Type-directed structural unpacking and splitting.**
   Driven purely by the elaborator's knowledge of `record` and `inductive`,
   with no library knowledge:
   - Any hypothesis whose type is a single-constructor record or conjunction
     (`And`, `AbsLe`, user-defined invariant bundles) automatically saturates
     its field projections into the graph.
   - A goal whose type is a conjunction or single-constructor record splits
     into independent subgoals automatically.

3. **Explicit `cite`-seeded e-matching (local, not a giant global DB).**
   Rather than relying on an opaque global lemma pool, `cite l₁, …, lₙ;`
   seeds e-matching with only the cited lemmas plus the ambient local
   hypotheses, matching against terms already present in the graph and
   discharging side conditions recursively from the graph. A user-defined
   type with three lemmas works on day one, and proofs stay fast and
   refactor-resilient.

4. **Generic homomorphism / cast push (`rule`-tagged laws).**
   Pushing `ofRat`, `BitVec::toNat`, `List::len`, or a `datarepr::abs` across
   operations and relations is one uniform pattern:
   `f(op(a, b)) ≈ op'(f(a), f(b))` and `R(a, b) → R'(f(a), f(b))`. Reusing
   the `rule` / registry pattern (`docs/native/optimizer-rules-design.md`,
   [[automation-lemma-registries]]) lets the graph bridge carriers without
   hardcoding any stdlib map.

5. **Optional Nelson–Oppen theory satellites.**
   When a file imports `omega`, `linarith`, `ring`, `bv_omega`, or SAT, each
   plugs into the same graph as a certifying theory satellite exchanging
   equalities and bounds over shared atoms. When no arithmetic theory is
   imported, primitives (1)–(4) still stand on their own.

---

## 3. Interaction with scoped proof worlds

Fact-graph proofs and scoped proof worlds
(`docs/language/proof-worlds-design.md`) are orthogonal and compose cleanly:
a proof world handles **control/quantifier structure** (deferred thresholds in
`Eventually`, constructive classicality in `Dne`, truncation in `Squash`),
while a fact-graph bridges **local equational/relational/algebraic steps**
inside each branch.

---

## 4. Open questions for when this is picked up

- **Explainability and minimization:** producing a human-readable `calc`/step
  trace (`Say` notes / `--explain-proof`) and reporting only the minimal
  subset of `cite`d lemmas that contributed to the kernel proof.
- **Certificate cost:** keeping proof reconstruction linear and shared
  (emitting `have` bindings for reused intermediate facts rather than
  duplicating sub-proofs along DAG merges).
- **Relationship to `grind`:** whether this grows directly out of `grind`
  (`lib/std/tactic/grind.hthr`) by adding [[egraph-setoid-path-algebra]],
  [[grind-e-matching]], and preorder edges, rather than introducing a second
  engine. Lean: evolve `grind` as the single engine.
