---
title: The closed-pair table is one gate's: every declaration walks the module's large types once
status: open
labels: [kernel,conversion,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

[[conversion-closed-pair-memo]] keeps convertible closed pairs for one gate.
Every declaration of a module that mentions one large type still walks it
once: after that change, `Sigma` against `Sigma` in `lib/std/tactic/grind.hthr`
was 741 misses of about 0.7 ms, each declaration's first meeting of the same
type (numbers in that issue's log).

## What stands in the way

- **The keys are addresses.** A named code's body is one node for the
  process, but the spelling it is compared with is built again for each
  declaration, so a table that outlived a gate would not be hit. A key that
  is not an address means a structural identity for closed syntax: interning
  at construction or at image load, or a memoized structural hash with the
  authoritative `==` behind it (a hash alone must not decide a kernel
  verdict).
- **Ψ grows.** A pair of spellings that mention only constants is
  convertible in every extension of the signature it was judged in
  ([[psi-references-by-level]]), but not under another interface boundary,
  and not if either mentions a universe or global variable.
- **The counters are exact and worker-order-invariant today**
  (`scripts/timings`). A table shared across gates makes a declaration's
  cost depend on which were checked before it on that worker.

## Acceptance

- A measurement first: how many of a gate's distinct pairs are structurally
  a pair an earlier gate of the module judged.
- If built: the counters stay reproducible at width one, and the design
  note says what they mean at other widths.

## Log

- 2026-11-10: The first obstacle has a place to stand now. Since
  [[free-variable-bounds-in-the-node]] a syntax node carries a head the kernel
  fills on demand, with room for a word more. A memoized structural hash kept
  there (with `==` behind it, as this issue says a hash must have) is the key
  that is not an address. Not started; the measurement in Acceptance still
  comes first.
