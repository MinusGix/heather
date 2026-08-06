---
title: "fmt's Debug for Branches prints 37 of 52 fields, so write_exact is not total over it"
status: closed
labels: [kernel, testing, diagnostics]
created: 2026-08-06
updated: 2026-08-06
code: crates/kernel/src/fmt.rs @ 33c65ef
---

Found by the cache-hardening round (2026-08-06,
[[parallel-checking-and-caching]] log): the kernel `Debug` impl for
`Branches` prints 37 of the struct's 52 fields — every `Vec`/`Fin`/`Wf`
branch and every strict-equality branch is absent from the printed form.

The cache no longer cares: its structural walker destructures `Branches`
with no `..`, hashes all 52, and `tests/merkle.rs::every_recursor_branch_is_hashed`
pins that (mutate each field, demand 52 distinct hashes). But two other
consumers of the printed form still inherit the gap:

- **[[elaboration-determinism]]'s golden hash** hashes `write_exact`
  output, so `NAT_SUITE_GOLDEN` is blind to those 15 fields: an elaborator
  change that altered only (say) a `tm_elim_wf` branch of an emitted
  recursor would not move the golden hash. The determinism *equality* test
  is unaffected (derived `PartialEq` sees every field); only the
  cross-build golden instrument has the blind spot. Today's Nat suite may
  not exercise the missing branches at all — worth establishing when
  fixing, since it decides whether the constant moves.
- **Humans debugging**: a `{:?}` on a recursor silently omits those
  branches, which is exactly the kind of "the term I printed is not the
  term I have" that budget elision was designed to make impossible to
  mistake (elision at least prints `…`).

Fix shape — and the fix round should treat this as an **audit of every
impl in `fmt.rs`**, not a one-struct patch: `Branches` was found by
accident of the cache walker rewrite, and nothing establishes that
`Motives` or the other multi-field impls are total. The day's lesson
(2026-08-06, twice) is that stated assumptions pinned by canaries lose to
exhaustiveness the compiler checks — so per impl: destructure with no
`..` inside the impl where feasible, or add a mutate-every-field totality
control. For `Branches` specifically: extend the impl to print all fields (keeping the `node()`
budget discipline), then re-run the determinism suite and update
`NAT_SUITE_GOLDEN` deliberately iff it moves, with the move's reason
recorded in the constant's comment. 

## When

Small and contained; any session. Wants doing before the golden hash is
next relied on to certify "output unchanged" across a refactor that
touches recursor emission.

## Log

- 2026-08-06: Fixed (2026-08-06): all four struct Debug impls in fmt.rs now destructure with no `..` under #[deny(unused_variables)], so a new field fails the build until the printer learns it — the enum impls already had this by construction. Branches went from 37 to all 52 branches, labelled in declaration order matching the cache walker's destructuring; budget discipline unchanged. NAT_SUITE_GOLDEN did not move, and that is a measurement: the printer change touches every rendered Branches, so an unmoved hash proves the suite (and today's elaborator, which constructs no ElimCodeTy/ElimCodeTm) emits no code recursor — reasoning recorded on the constant. Out of scope, noted: value.rs Debug impls still use `..`; fine while nothing hashes a Val, inherits this defect if write_exact is ever pointed at values. Full scripts/test green.
