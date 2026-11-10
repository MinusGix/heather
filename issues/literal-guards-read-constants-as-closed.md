---
title: Literal guards read a reference to a definition as closed since constants
status: closed
labels: [elaborator,regression,indexed-families]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Two guards in the elaborator ask "is this term a literal: does it read no
local variable and name no definition?" and answered it by weakening the
term and comparing: `t.shift_local(1) == t && t.shift_global(1) == t`.
Since [[psi-references-by-level]] a committed definition is a **constant**,
which no weakening moves, so the second test stopped seeing a reference to a
definition and both guards began to call `seven`, `same(3)` and a partially
applied `same` literals.

## What broke

`iwf_family.rs`'s `literal_closed` decides whether a match on an indexed
family abstracts the scrutinee's index in the motive. A literal index is not
abstracted (its literals also spell the signature); anything else is. With a
definition read as a literal, a match at a definition-valued index held
every arm to that index:

```
inductive Acc<P>: (a: P) → Type { Stop(a: P): Acc<P>(a), Step(a: P, b: P, c: Acc<P>(b)): Acc<P>(a) }
def seven: Nat = 7;
theorem acc_at_def(x: Acc<Nat>(seven)): Acc<Nat>(seven) {
    match x { Stop(a) => Stop(a), Step(a, b, c) => Step(a, b, c) }
}
// error: `Stop` constructs `Acc<Nat>(a)` at its written result index,
// which is not the expected `Acc<Nat>(seven)`
```

Accepted on 3d26280, refused on e01ceec (#533). The same for an index that
is a call (`same(3)`), a function named without arguments, and a `def` of a
user inductive. No library module has the shape, which is why the suite
stayed green. Only type-parameter indices reach the guard: a `Nat` or
inductive index is inverted before it.

`display.rs`'s `type_name_shape_at` uses the same test for the value
arguments a type name's `def` applies its family to. Display only.

## Fix

`gendefs::names_global(t)`: whether `t` names a binding of Ψ at all,
constant or variable, by the kernel's reference walk (`reindex_global` with
a map that refuses). Both guards ask it. A third site with the same
spelling, `named_type`'s memo guard, means "mentions no global variable"
and is right as it stands (the 2026-11-10 log of
[[psi-references-by-level]]).

Probes: `lib/_tests/lang/open_index_tests.hthr`, `acc_at_def`,
`acc_at_fn`, `acc_at_inductive_def`, `acc_at_call`, `acc_at_var`, and the
other side of the guard, `acc_at_literal`, which is refused.

## The general lesson

"Weakening changes it" has been used as a stand-in for "mentions a
variable of this kind" three times now (local closedness before
[[empty-substitution-tail-decoration]], then twice here). It is only ever
a proxy. A guard should ask the question it means: `names_global` for "no
definition", `heather_kernel::subst::global_var_bound_*` for "no global
variable".

## Log

- 2026-11-10: Fixed as described: `gendefs::names_global`, asked by `literal_closed` and by the display's type-name shape. Probes in `lib/_tests/lang/open_index_tests.hthr` (five accepted, one refused literal). `scripts/test --pr`: 3047 passed, 0 failed, 2 ignored. Found while classifying the elaborator's `shift_global` sites for [[identity-rescopes-after-constants]]; the sweep for the same proxy (`shift_global(k)` compared with its argument) found one more site, `named_type`'s memo guard, which means "no global variable" and is right.
