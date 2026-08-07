---
title: Traits and instances: classes as records, disciplined resolution, programmable later
status: open
labels: [frontend,syntax,elaboration,design,metaprogramming]
created: 2026-08-07
updated: 2026-08-07
---

The general typeclass/trait feature, designed 2026-08-07 in discussion; the full record is docs/traits-design.md and this issue owns its staging (doc §13). One-paragraph contract: a class is a parameterized record; an instance is a namespace of ordinary declarations plus an assembled record value (block and literal forms, `instance Monoid<Rat>`, no `for`); `extends` is flattening plus ONE CANONICAL VALUE PER (CLASS, CARRIER) — parents filled by reference when declared, synthesized as projections when not, overrides owing kernel-checked agreement proofs; resolution is an ascending-scope, deterministic, mode-directed, structurally-terminating backchainer whose every derivation is minted as a canonical named global (memoization = canonicalization), scheduled on the withheld-obligation machinery, failures returning the search trace as data; instance implicits are the default case of solver-default arguments (`:= infer`); layer 3 re-implements the resolver as a heather function over QUOTED goals when context computation lands.

## What it assumes from elsewhere

- **[[compile-typeclass-design]]** owns the Compile certificate shape and CallCtx. Assumed here: only that an instance's semantics stays 'ordinary record value'. Its §5 class layer is superseded by this design (target indexing struck — doc §10).
- **[[elab-unifier-completeness]]** owns the withheld-slot scheduler. Assumed here: only that deferral-and-retry-to-fixpoint stays available to new obligation kinds.
- **[[generators-in-the-language]]** owns the meta-layer migration and the ch. 07 missing-features list. Assumed here: only that context computation is on that list and enumerable.
- **[[elaboration-determinism]]** (closed, spine recorded on [[parallel-checking-and-caching]]): the resolver must be a deterministic function of (goal, scope).
- **[[ai-facing-tooling]]** owns failure-state-as-data. Assumed here: only the direction.

## Staging

Doc §13: (a) layer 1 declaration forms; (b) layer 2 resolver + `:= infer`; (c) trace-as-data diagnostics; (d) layer 3, behind the meta-layer roadmap. Open questions in doc §12 (termination default's bite, post-hoc registration, mode syntax, canonical-table scope, agreement-proof form).

## Log

- 2026-08-07: Layer 1 landed (doc §13 item (a)): specification slice docs/traits-layer1-design.md; class/instance parse (crates/syntax parser+ast) and elaborate (new crates/elab/src/traits.rs) as pure surface desugaring — a class builds the record an equivalent `record` would and calls elab_inductive, an instance builds ast::Decls (members, value, synthesized parents, agreement certificates) and calls elab_decl, so no kernel change and no new lowering. Block and literal forms, dependent fields, extends with flattening+dedup, canonical parents in BOTH directions (parent-first fill-by-reference, child-first synthesis), overrides certified by a synthesized `theorem …#agrees: over = parent { refl }`, generic instances as dictionary-valued functions with `requires` as explicit params. 31 tests in crates/elab/tests/traits.rs; workspace 1177 -> 1208 fast. TWO CORRECTIONS to docs/traits-design.md, both recorded in the slice §7: (1) §12's content-addressed minting keyed on (class, carrier-syntax) is narrowed at layer 1 to (class, carrier HEAD) — the canonical name has to be spellable (`Rat::Monoid`) for an instance to be usable without a resolver, and a rendered type argument is not an identifier; two carriers sharing a head is a declaration error naming both, and layer 2's canonical-derivation table inherits the full key. (2) A member reference in the assembled value writes its type arguments explicitly (`f<A,B>(ma,mb)`) because the applicator refuses to mix partial application with implicit insertion. Also found: `extends` arguments are restricted to the child's own type parameters (instantiation is then a rename, not a substituting walk) and an instance is all-or-nothing by elaborator snapshot. DEFERRED to layer 2 (slice §8, owner = this issue's item (b)): the full canonical key; receiver dispatch through an instance (member_bases records `Monoid::op`, not `op`, so x.op(y) does not reach a member — concrete-carrier dispatch needs member_head to try T::C::op, generic-carrier dispatch needs receiver sugar to consult dictionaries); fill-by-reference and override agreement against a PARAMETERIZED canonical parent (applying its value is resolution); and making `requires` instance-implicit, which is what turns the cross-member rule from 'pass them' into 'they are found'. One lexer residue: three-segment names (`Rat::Monoid::op`) are registered and resolvable but unwritable (the lexer joins exactly one `::`) — members are reached by projection instead, definitionally the same value.
