---
title: --deny-axioms misses an axiom a tactic reaches by its name
status: closed
labels: [frontend,proofs,soundness,tooling]
area: language
created: 2026-11-16
updated: 2026-11-16
---

`heather check --deny-axioms` accepted a theorem of `1 = 0` that rests on an
axiom, and `heather axioms` answered "no axioms" for it:

```
fn g(n: Nat) → Nat { match n { Zero => 1, Succ(k) => g(k) } }
axiom g_bad(n: Nat): g(n) = 0;
register def my_set: SimpSet = simp_set("a::bad", [name_of(g_bad)]);
theorem t1(n: Nat): g(n) = 0 { by simp_with([my_set], defaults := False) }
theorem t2(): 1 = 0 { t1(0) }
```

The kernel is not involved: the axiom is a declared assumption and the proof
checks from it. What failed is the record of which declarations a proof
reaches (`crates/elab/src/provenance.rs`). An edge was recorded only where a
*written* name resolved (`Elaborator::resolve`) and where a derived instance
was referenced (`Resolution::derived_ref`). A tactic builds its references
from name strings through the host (`resolve("…")`, a `simp` set's laws), so
its proof term named `g_bad` and the declaration's record did not. The same
gap stood behind any reference a term gains without a written name: one left
by a reduction, or one inside a generated definition or a lifted proof, which
have no record of their own and so ended the chain (`Provenance::commit`
skips a dependency it has no record of).

## Fix

The edges are read off the term the kernel gate is handed
(`DeclarationsMut::record_reached`, called from `gate_bodied` for a
declaration and for each proof it lifts). A reference to a recorded
declaration is an edge. A reference to a global with no record follows what
it was made from: its body when it has one, and otherwise (a proof lifted
out of a declaration) the declaration it was committed just before. The
written-name edges stay, since they are a subset.

Module images written before the fix hold the old edge lists; the exact
image policy re-elaborates them after a compiler change.

## Regression test

`crates/cli/tests/check.rs`, `deny_axioms_sees_an_axiom_a_tactic_names`, over
`fixtures/axioms_by_name.hthr`: a tactic that resolves a name string and
returns it as the proof.

## Left open

- **A mention is now a dependency.** A term cannot tell a use from a
  mention, so `theorem t(): witness() = witness() { refl }` depends on the
  axiom `witness` (it sits in `refl`'s annotation), where
  `issues/axiom-provenance.md` chose that a statement-only mention does not
  taint. The written-name edges cannot give that precision back once a
  tactic's references count, and the strict reading is the safe one for
  `--deny-axioms`; the library declares no axiom, so nothing there moves.
  Minus's call if the looser reading is wanted back for some shape.
- An instance, a `register def` and the other non-`check_decl` commit paths
  were not audited one by one; the gate-side reading covers whatever goes
  through `gate_bodied`.
