---
title: omega spells a lambda binder of type `BitVec(8)` as `BitVec` in its atom list
status: open
labels: [omega,proofs,elaboration,display]
area: tactics
created: 2026-11-11
updated: 2026-11-11
---

An atom that contains a lambda whose binder has an applied type is spelled
with the type's head alone, and the generated atom list then fails to
elaborate. The hypothesis need not be one the goal uses, nor one listed.

```text
theorem respell_binder(xs: List<BitVec(8)>, k, t: Nat, byte: BitVec(8),
    short: t < xs.update(k, λ (_: BitVec(8)) => byte).len(), whole: xs.len() = 16, before: t < xs.len()): t < 16 {
    omega(before, whole)
}
error: `BitVec` takes 1 value argument(s): write `BitVec(n)`. …
  generated Omega atom list: … list::List::len(list::List::update(xs, k, λ (x: BitVec) => byte)) …
```

The same theorem over `List<Nat>` with `λ (_: Nat) => n` checks. Found
writing `Loan::put_reads` (`lib/std/arch/x86_64/x86_64_lending.hthr`, U4
step 4a-1 of [[native-one-compiler]]): a span's bytes after a store are
`xs.update(k, λ _ => byte)`, and its length fact is in scope wherever the
arithmetic about the span is done. The workaround there is to transport the
bound by `j` along `len_update` and `whole` instead of calling `omega`.

Two defects meet. The speller drops the binder type's value argument
(`display.rs`, the family of [[omega-respells-atoms-without-implicits]],
closed). And omega reflects a fact that is neither listed nor connected to
the goal ([[omega-listed-facts-only]]).

## Acceptance

- The theorem above checks.
- A lambda binder at a type with a value argument spells so that it
  elaborates to the same term, wherever a generator spells terms as source.

## Log

- 2026-11-11: Filed from U4 step 4a-1.
