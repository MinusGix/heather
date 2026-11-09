---
title: Registering DecEq at a carrier makes its existing x.eq_dec(y) calls ambiguous
status: closed
labels: [elaboration, traits, classes]
area: language
created: 2026-11-09
updated: 2026-11-09
---

`instance(n: Nat) DecEq<BitVec(n)> { eq_dec := BitVec::eq_dec }` breaks every
receiver call `x.eq_dec(y)` at a `BitVec` (e.g. `lib/std/os/linux/linux_calls.hthr`):
"`eq_dec` here is both a member of `DecEq<BitVec>`, reached through the
receiver's type, and `BitVec::eq_dec`". The class member *is* that
function, so nothing is ambiguous. `Nat` has the same shape
(`instance DecEq<Nat> { eq_dec := Nat::eq_dec }`) and `a.eq_dec(h)` at a
`Nat` was accepted (the old `list_algos::count`), so the difference is
probably the value-parameterised instance; not investigated.

Cost now: `BitVec` has no `DecEq`, so `List::occurrences` and
`perm_iff_occurrences` (lib/std/data/perm.hthr) do not reach byte lines,
nor does `DecEq<List<BitVec(8)>>`.

## Done when

A receiver member reached through a class instance whose field is the
same-named carrier function resolves to it without an ambiguity error, and
`bitvec.hthr` registers `DecEq<BitVec(n)>`.

## Log

- 2026-11-09: Done. The coinciding-readings test (`field_is_global`, crates/elab/src/dispatch/receiver.rs) took only type binders; it now takes an index binder whose callee parameter is an implicit of the same domain with no default or solver, and reads through a dictionary the resolver minted at closed arguments (a global whose body is the instance applied) to the instance's literal. The value-parameterised instance was the difference, as guessed. bitvec.hthr registers `DecEq<BitVec(n)>`; probes in lib/_tests/std/bitvec/bitvec_tests.hthr and lib/_tests/lang/receiver_coincidence_tests.hthr (with a different-function control that stays ambiguous).
