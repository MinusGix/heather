---
title: Compile the specification's own shapes, starting with Sha2::extend at SHA-256
status: open
labels: [native,datarepr,generator,cryptography]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-14
updated: 2026-11-14
---

There are two SHA-256s: `lib/std/crypto/sha2.hthr` over lists, `Nat`
recursion and a record of eight words, and `lib/native/crypto/` over arrays
in a laid record with word loops. The second exists because `runtime fn`
cannot take the first, and proving them equal is hand work. Design:
`docs/specification-shapes-design.md` (the transfer of `datarepr-design`
§3 grown to bounded lists held as arrays, counts held as words, a
step-after recursion as a loop, and specialisation at a closed argument;
then the record-function generator as it is).

## Scope

- The stack and queue representations of `[A; n]` with their laws, `rev`
  between them, and `Nat::loop_refines` with its word form, in a library.
- The transfer as a Heather generator over §3.1 to §3.4 of the design,
  declining anything else with its reason.
- One request: `Sha2::extend` at `Sha2::sha256()`.

## Done when

`Sha2::extend` at SHA-256 is compiled from `sha2.hthr` as written: the
generator publishes the `runtime fn`, its `refines` and the end statement
over bytes, all checked; a perturbed pass law is refused; the linked code
computes a NIST block's schedule. No hand copy is written for it.

## Log

- 2026-11-14: design note and hand-run (`lib/_tests/native/spec/extend_handrun_tests.hthr`): at `Nat` lengths, the refinement of a stack-held loop to `Sha2::sha256().extend` checks with one generic loop theorem and the representation's two laws; the per-function proof is a `rewrite` by four reads, a push law, and one application. The word level is not hand-run. Waiting on Minus's agreement before the slice.
