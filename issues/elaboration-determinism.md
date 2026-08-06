---
title: Elaboration determinism as an enforced guarantee
status: closed
labels: [frontend, elaboration, testing, metaprogramming]
created: 2026-07-24
updated: 2026-08-06
---

For most compilers, deterministic output is hygiene. For Heather it is a
**semantic commitment**, and that is the reason to enforce it early rather
than assume it.

The commitment comes from sketch round 2 ([[surface-syntax]] log,
docs/sketches/surface-v2.md): `.code` on a top-level `fn` quotes the
*elaborated* term, and intensional analysis keys on that. So the elaborator's
output is observable *inside the language* — a meta-function can branch on
it. Two elaborations that differ in any way a `match code` can see are two
different programs, not two spellings of one. Anything downstream that keys
on elaborated syntax inherits this: [[certifying-generator]]'s prove-once
shape, [[compile-typeclass-design]]'s dedup by "(syntax, descriptor)"
keying, and [[setoid-auto-lifting]]'s boxed-code introspection.

## What could break it today

Nothing known to be broken — this is about not *acquiring* the bug:

- **Hash-map iteration.** `Elaborator.globals` is a `HashMap<String,
  GlobalInfo>` and `goal_spans` a `HashMap<(usize,usize), usize>`. Both are
  only ever *looked up*, which is fine; the day one is iterated, output order
  becomes hash-seed dependent. Rule: never iterate a `HashMap` in a way that
  reaches the emitted term — use `BTreeMap`, or a `Vec` in insertion order,
  or sort. (`rustc-hash` would make iteration deterministic within a build
  but is a footgun as a *fix*, since it hides the intent.)
- **Address/pointer identity.** `Rc::ptr_eq`-style shortcuts are legitimate
  optimisations but must never change *which* term is emitted, only how fast
  it is found. Hash-consing ([[dependency-policy]]) is where this will get
  tempting.
- **Ordering coming out of goal machinery.** Goals are already numbered in
  creation order and discharged in source order, both deterministic by
  construction ([[goal-holes]]) — worth a regression test rather than a
  comment, since the padding/dedup logic is the kind of thing a refactor
  reorders.
- **Anything time-, path-, or environment-derived** in a term. None today.

## Deliverable

1. A determinism test: elaborate the same source twice in one process and
   assert the emitted terms are identical (`PartialEq` is derived on the
   kernel types), plus the suite run under a different hash seed
   (re-running with a changed `RandomState` is enough to catch iteration
   order).
2. A golden hash of the elaborated Nat suite — cheap, and it turns "the
   elaborator's output changed" into a visible event rather than a silent
   one. This is a good `insta` snapshot once that lands
   ([[dependency-policy]]).
3. A line in `crates/elab`'s module docs stating the guarantee and the
   `HashMap` rule, so the next person adding a map knows it is load-bearing.

## Later, harder version

Determinism *across versions* of the elaborator is a stronger and much more
awkward property: it means an elaborator change can invalidate a proof that
pattern-matched on generated code. Worth knowing this is coming before
[[certifying-generator]] leans on syntax keying; the mitigation is probably
that certified generators prove things about the code they *see*, not about
code the elaborator promised to keep producing. Not a problem to solve now,
but a reason not to let syntax-keying spread casually.

## Log

- 2026-08-06: A second consumer filed: [[parallel-checking-and-caching]] (2026-08-06) keys its whole content-addressed cache DAG on elaborated-output hashes, so this guarantee is now the hard prerequisite for parallel checking, not only for .code instance keying.
- 2026-08-06: **Done — all three deliverables landed, and the audit found nothing to fix.**

  *Audit (every `HashMap`/`HashSet` in `crates/elab/src/`; the tokens appear in
  exactly three files, so this is the complete set — there are no local ones).*
  Every one is **lookup-only**: `get`/`insert`/`contains_key`/`clear`, never
  `iter`/`values`/`keys`/`drain`/`retain`. No iteration order reaches an
  emitted term or a diagnostic today.
  - `names.rs by_name: HashMap<String, Vec<NameEntry>>` — lookup-only. Its
    *values* are `Vec`s in declaration order, and the ambiguity diagnostic
    ("declared in m1, m2") lists from that `Vec`, so even the one place a
    collection is printed is order-stable.
  - `gendefs.rs by_key/by_abs/fam_lvl` — lookup-only (the generated-definition
    dedup index; allocation order is insertion order into Ψ, not map order).
  - `lib.rs module_scopes / globals / inductives / by_tag / forded_by_skel /
    ctors / meta_defs / meta_slots` — lookup-only.
  - `lib.rs record_fields / member_bases` (`HashSet<String>`) — membership
    tests only.
  - `lib.rs goal_spans` (`RefCell<HashMap<(usize,usize), usize>>`) —
    `get`/`insert`/`clear`. Goal *numbering* comes from `goals.len()` (a
    `Vec`), i.e. creation order; the map only re-finds an already-numbered
    hole. So the [[goal-holes]] ordering concern above is deterministic by
    construction, as suspected, and is now covered by the repeat test.

  *What landed.*
  - `crates/elab/tests/determinism.rs`:
    `same_source_elaborates_identically` runs **8 fresh `Elaborator`s** over
    the same source and compares Ψ with derived structural `PartialEq`. The
    repetition is the point: std's `RandomState` draws new keys **per map
    instance**, so each fresh elaboration in this one process already hashes
    names into a different order — no env var, subprocess, or second `cargo
    test` invocation is needed to vary the seed.
  - Golden hash: `NAT_SUITE_GOLDEN = 0x697538d142d9c471` in the same file,
    over the prelude + Nat suite Ψ (9 bindings). A failure prints the new
    value as a paste-ready `const` line, and the doc comment says plainly
    that a failure is a *notification* ("the elaborator's output changed"),
    to be confirmed deliberately, not a bug report.
  - First-party hasher, since `crates/elab` has no dev-deps and `insta` has
    not landed ([[dependency-policy]]): FNV-1a in
    `crates/elab/tests/support/mod.rs`, which also now owns `NAT_SUITE` —
    shared with `nat_suite.rs` so the hash pins the very source that suite
    checks rather than a copy that can drift.
  - The rendering hashed is **not** `{:?}`: kernel `Debug` is budget-bounded
    and elides past 512 nodes, so hashing it would make two Ψs agreeing on a
    prefix indistinguishable — a golden hash that cannot fail. Added
    `heather_kernel::fmt::write_exact` (`fmt` is now a public module): the
    same impls with both budgets disarmed, streaming into any `fmt::Write`
    (here, straight into the hasher — no `String` of the printed tree is ever
    built). A third test, `the_hash_sees_past_the_debug_budget`, pins that it
    really does, by hashing two Ψs that differ only 2000 nodes deep.
    `write_exact` is also what [[parallel-checking-and-caching]] should key
    its cache on.
  - `crates/elab/src/lib.rs` module docs gained a "Determinism is a
    guarantee, not hygiene" section: the commitment, the `HashMap` rule, the
    note that `RandomState` varies per instance, and why a fixed-seed hasher
    is the wrong fix.

  Not done, deliberately: **cross-version** determinism (the "later, harder
  version" above) stays out of scope — the golden hash is exactly the tool
  that makes such a change visible, which is the most that is wanted before
  [[certifying-generator]] leans on syntax keying. Only the Nat suite is
  hashed; extending the golden set is cheap when there is a reason.
