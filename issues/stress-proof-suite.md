---
title: Stress-proof acceptance suite for the frontend
status: open
labels: [frontend,testing,milestone]
blocked-by: [elaborator-design, inductive-compiler]
created: 2026-07-23
updated: 2026-07-26
---

The acceptance gate for [[elaborator-design]]: the stress proofs are not an
alternative to the frontend, they are how we know it works — and they are
barely feasible without it. When this suite passes, defining the IR is just
another `inductive` and simulate another `def`, and
[[ir-simulate-design]] reopens in-language.

The three items (agreed 2026-07-23):

1. **Nat arithmetic + Id lemmas.** comm/assoc via `elim_Nat`;
   `sym`/`trans`/`cong` via J. Exercises Id and the elaborator's
   annotation synthesis. Gates elaborator stage 1 (explicit levels, no
   metas) and again stage 2 (annotations dropped).
2. **List via tier-1 fording.** The forcing function for
   [[inductive-compiler]] tier 1: exact-height encoding, derived recursor,
   constructor injectivity/disjointness (no-confusion via large elim),
   plus a real proof or two (e.g. append associativity). Hand-prototyped
   first, then reproduced by the generator.
3. **Acc via W** (tier 2, hand-built). Exercises the synthesized-ih β rule
   — the newest, least-battle-tested kernel machinery — and the
   W + Id + funext indexed-containers story from
   [[kernel-v1-extensions]].

Each item's elaborated output goes through the real kernel check (the
frontend soundness-by-construction property from [[elaborator-design]]).

## Log

- 2026-07-23: Opened; items agreed in the frontend-first route discussion.
- 2026-07-23: Item 1 PASSING at elaborator stage 1 (explicit-annotation form): add_zero/add_succ/add_comm/add_assoc via elim_Nat with explicit motives + ih patterns, sym/trans/cong_succ via J, all elaborated from surface syntax and checked by the real kernel (crates/elab/tests/nat_suite.rs). Also: 2+2==4 by bare refl (computation check), and negative tests confirming the kernel gate rejects wrong proofs/lemma uses. Item 1 re-gates at stage 2 when the annotations drop.
- 2026-07-24: Item 2 half done, 2026-07-24: List via tier-1 exact-height fording is hand-prototyped and kernel-checked (crates/elab/tests/tier1_fording.rs) -- derived recursor, append, append_nil and append_assoc by induction, disjointness and per-field injectivity incl. the recursive field, plus negative controls. Remaining for the item: reproduce it from a surface 'inductive' declaration once the tier-1 generator exists. Note the prototype adds a second type (Bits) beyond the item's text, because List's height classes hold one constructor each and so never exercise the sum spine or same-height disjointness.
- 2026-07-26: Item 2 is now reachable and half-done. 'List via tier-1 fording' is misnamed as of 2026-07-26: there is no fording — List, Bits and every branching declaration lower onto the Wf former through one path (docs/inductive-tier1-wf-lowering.md, closing [[tier1-branching-constructors]]). What the generator now produces for a tier-1 declaration: the type, constructors, the recursor via a guarded self-call, and no-confusion (disjointness by large elimination over Wf, injectivity at both payload and recursive fields) — crates/elab/tests/inductive_tier1.rs, 13 tests. What item 2 still wants on top of that is the PROOF content: a real theorem or two about a linear type, e.g. append associativity over List, written at the surface. mirror(mirror t) = t over Tree is the branching analogue and is done.
