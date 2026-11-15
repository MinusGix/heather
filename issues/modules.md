---
title: "Modules: imports, per-file namespaces, and the library as Heather files"
status: closed
labels: [frontend, syntax, elaboration, stdlib, design]
created: 2026-08-05
updated: 2026-08-05
---

Every `.hthr` file is a whole program: there is no way for one file to use
a declaration from another, so `lib/certgen/ir_v1.hthr` hand-declares a monomorphic
`OptVal` and a full Nat order kit, and every future library file pays the
same tax again ([[prelude-option-and-friends]] is the record of that cost).

## What this issue owns

The module story: how a file names another file's declarations — the import
form, the namespace/qualification scheme, resolution order, and where the
standard library lives. Acceptance for the first round: `Nat`'s order kit,
`Option`, and `List` land as actual Heather modules that `ir_v1.hthr`-style
files import, and the Rust-seeded prelude shrinks rather than grows.

Deliberately **not** owned here (v1 is module *organization*, not separate
compilation): serialization of checked kernel state, per-module check
caching, and cache invalidation. Those are their own rounds when two library
files make them matter; the design doc should leave them reachable.

## What it assumes from elsewhere

- **[[prelude-option-and-friends]]** owns the helper shopping list and the
  `?`-chaining sugar (its layers 2–3). Assumed here: only that its layer 1
  (residency) is satisfied by modules instead of `with_prelude` seeding.
- **[[indexed-families]]** owns the generators' naming discipline. Assumed
  here: only its §10.6 note — generated definitions key on declaration
  names, and an index type must survive *as a declaration* (alias-hostile).
  Qualification must not change what those keys see.
- **[[compile-typeclass-design]]** owns instance keying. Assumed here: only
  that instances key on elaborated syntax, so module-dependent *spelling* of
  a reference must not leak into elaborated terms (or the keying moves).

## Log

- 2026-08-05: Filed; design round opens (coordinator-run, not managed).
- 2026-08-05: Design doc landed (docs/language/modules-design.md). Verdict: kernel
  untouched (Ψ is nameless), modules are files, imports elaborate the DAG
  once into one Ψ; the name regime is unambiguous-or-qualified with
  ambiguity-at-use, no silent shadowing between modules (doc §4 has the
  argument). Generator keys are nominal tags, so qualification cannot
  disturb them — the §10.6 assumption holds by construction. Horizon
  recorded, not built (§8): caching keyed on content hashes, parameterized
  modules as generators (no functor mechanism needed), module-scoped
  instances for the resolver round. Four open questions to the user in the
  doc's tail; implementation phased in §10.
- 2026-08-05: v1 LANDED (managed round) and this issue closes — all four
  §10 phases: `import`/`::` (qualified names join in the lexer, one token),
  the §4 regime in `crates/elab/src/names.rs` with every table keyed
  `module::name`, the CLI import-DAG loader (`crates/cli/src/loader.rs`:
  dedup by path, cycle printed, `-L` with `lib/std` defaulted), and
  `lib/std/{nat,option,list}.hthr` with `lib/certgen/ir_v1.hthr` migrated to
  `import nat;`. Suite 936 → 971, coordinator-verified. Match arms turned
  out to already be scrutinee-directed (they position within the
  declaration), so cross-module arms were correct by construction; the
  round added only the qualified spelling. Deviations from the doc are in
  the round report, none regime-visible; notable: `OptVal` stays local to
  ir_v1 (migration would put a large diff through a 66s proof file for no
  claim), re-entering a module is additive for the two-chunk test idiom,
  and the corpus bench rows now time import closures (baseline re-saved
  under that shape). Residue, each with an owner:
  [[module-scope-of-stored-syntax]] (stored surface syntax resolves at the
  use site — the round's one invariant-adjacent seam),
  [[resolver-lookup-constant]] (per-lookup allocation + elaborator-clone
  2.5x, measured, levers recorded),
  [[ctor-resolution-by-expected-type]] (the §4 follow-up, now filed).
  Unfiled by decision: two-segment qualification (`option::Option::None`)
  has no current need and `import` covers every live case; the loader's
  double parse waits for the caching round, which wants a parsed-module
  cache anyway. `use` stays a reserved keyword per the doc's Decisions.
- 2026-08-05: All four open questions decided with the user (doc
  "Decisions" section): regime signed off, keyword `import` with `use`
  reserved as the future policy keyword, minimal migration, `lib/std/`.
  Horizon §8 gained the one-resolution-judgment direction and its two
  invariants (checking position may shrink candidates; growth may error,
  never reinterpret). Implementing round launches.
