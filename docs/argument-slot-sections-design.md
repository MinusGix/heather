# Argument-slot sections

Status: implemented (2026-08-19). Tracking issue:
`issues/argument-slot-sections.md`.

## 1. Surface

`·` (U+00B7 MIDDLE DOT) is an anonymous argument place in a checking
position. A section elaborates as the corresponding ordinary lambda:

```heather
·                   // λ x => x
f(·, ·)             // λ x y => f(x, y)
f(·₀, ·₀)           // λ x => f(x, x)
f(·₂, ·₀)           // λ x _ z => f(z, x)
```

Plain slots are distinct arguments in lexical left-to-right order. Subscripted
slots use zero-based identity: repetition repeats an argument, and the largest
index determines the introduced telescope, including deliberately unused
positions. Adjacent Unicode subscripts form one base-ten index, so `·₁₀` is
slot ten. Ordinary digits are not subscripts and do not join the token.

Indexed and unindexed slots cannot mix in one section. Separate nested
sections may use different styles.

## 2. Checking-only ownership

A slot is neither a hole nor an inference metavariable. It needs an expected
function type, and the smallest checking position capable of introducing it
owns it. For example, in

```heather
fn eval(f: Nat -> Nat) -> Nat { f(0) }
fn result() -> Nat { eval(Succ(·)) }
```

the argument of `eval` owns the slot even though the declaration body is also
a checking position. A slot that reaches inference, or escapes to a
non-function expected type, gets the dedicated “needs an enclosing checking
position with a function type” diagnostic.

Explicit lambdas and sequent binders are abstraction boundaries. An outer
section scan does not cross them; checking their bodies may start new sections
normally.

## 3. Elaboration

The syntax tree retains `ArgSlot(Option<u64>)`. Checking first probes a cloned
elaborator with capture disabled only at the current boundary. Nested checking
positions remain enabled and therefore get first refusal. If a slot escapes
and the current expected type is a Pi, the current section is rewritten to an
ordinary untyped explicit lambda whose impossible source names are then
handled by the existing lambda checker.

Ownership cannot depend on which argument is visited first. When one slot
escapes, the elaborator probes each free slot independently while sibling
slots act as disposable neutrals. This partitions slots captured by smaller
checking positions from those owned by the current boundary before mode
checking and lowering. The probes are clones, so goals, warnings, derived
instances, mismatch notes, and the disposable terms never enter committed
elaboration.

Lowering to the established lambda path is load-bearing: dependent Pi
substitution, de Bruijn order, implicitness coherence, and kernel checking are
not reimplemented for sections.

## 4. Bounds and present boundary

An indexed section may introduce at most 256 arguments. This is a frontend
resource bound against enormous source-controlled subscripts, not a semantic
arity limit.

Slots currently introduce consecutive explicit Pi binders. An expected
implicit binder is governed by the ordinary lambda coherence rule; sections
do not silently synthesize or skip implicit binders.

## 5. Projection sections

A slot may be the receiver of a chain of bare field projections: `·.lines`
is `λ s => s.lines`, and `·.inner.count` is `λ s => s.inner.count`
(`issues/field-projection-sections.md`). Nothing new is lowered. A field
access is not a checking position, so it cannot own its receiver's slot:
`resolve_dot` passes the receiver's escape on instead of reporting a missing
field, and the enclosing function-typed position lowers the section to the
ordinary lambda. The field is then looked up at the binder's type, taken
from the expected Π, so a field of some other record with the same name is
refused rather than chosen by name.

Two details keep this consistent with §3:

- A masked sibling (`first(·.a, ·.b)` while the other slot is probed)
  projects to the same disposable neutral a masked slot is, without reading
  any field: its receiver has no type yet, and the probe only asks who owns
  the target.
- A projection section passed at a function-typed parameter whose domain
  still has unsolved implicits (`apply_to<A, B>(f: Cell<A> -> B, c:
  Cell<A>)` called as `apply_to(·.count, c)`) is owned by that parameter,
  which is function-typed whatever solves it. Inferring it escapes, so the
  call is re-planned with the section deferred like an unannotated lambda
  (`apply_implicit`'s restart) and checked once `c` has solved `A`. A bare
  `·` at such a domain is left as it was: it escapes to the enclosing
  section. A slot under a call (`apply_to(idn(·.count), c)`) is not covered
  either and is still refused there, as `idn(·)` already was.

The shorter spelling `.lines` at a function-typed position is not provided:
it would be a new parser form, and `·.lines` keeps sections to one marker.

## 6. Acceptance

`crates/elab/tests/argument_slots.rs` pins plain identity/distinctness,
repetition, reordering, omission, dependent telescopes, multi-digit indices,
smallest-boundary ownership independent of traversal order, lambda/sequent
boundaries, and the mixed-mode, resource-bound, inference, and non-function
diagnostics; and projection sections (§5) at concrete and open receiver
types, beside other slots, with neutral receivers, and refused without a
function type, at a missing field or at a mismatched field type. The standard library contains direct uses in impossible Nat and
Int branches, so whole-library checking exercises the feature outside its
focused suite.
