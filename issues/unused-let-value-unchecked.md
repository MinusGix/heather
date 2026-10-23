---
title: An unused let's value never reached the kernel
status: closed
labels: [frontend,elaboration,soundness-of-checking]
area: language
code: crates/elab/src/statements.rs
created: 2026-10-23
updated: 2026-10-23
---

`let p = P(2, refl); 0` with `record P { a: Nat, h: a = 3 }` elaborated,
while `P(2, refl)` on its own, or `let p = P(2, refl); p.a`, was refused by
the kernel. Spotted on PR #102 with an unused `let x = A(2, refl); 0` at a
value-parameterised inductive, never filed then.

**Cause.** A `let` is an alias, not a kernel binder
(docs/let-and-blocks-design.md §2.2), so its value is in the kernel's input
only where a use splices it. The elaborator leaves conversions (a `refl`'s
endpoints, a constructor's field types) to the gate, so an unused value was
checked by nobody. The same shape had two more owners: `omega(e, …)` and
`ring(h, …)` bind their written facts as aliases and drop the ones the
certificate does not cite.

## Resolution (2026-10-23)

docs/let-and-blocks-design.md §11. A block wraps every value no use
spliced around its result as `(λ _: T. body)(v)`; `omega` and `ring` do the
same around their proofs. "Spliced" is recorded only by `resolve`
(`Alias::splice`); type reads and search candidates use `resolve_reading`.
A renaming `let y = x;` (every pattern variable of a desugared `match`) has
no value of its own and shares `x`'s record.
Checking every value regardless of use was measured and rejected (an order
of magnitude more kernel work on the heaviest `lib/std` items).

Tests: `crates/elab/tests/let_and_blocks.rs` §6 (every `let` form, a
value-parameterised type, a neutral and an open element type, the term shape
of used and unused values, a `meta fn`), `omega_fact_arguments.rs`
(`an_uncited_argument_still_faces_the_kernel`), `lib_std_ring.rs`
(`an_unused_hypothesis_still_faces_the_kernel`).

Left open: [[parameter-default-unchecked-at-declaration]].
