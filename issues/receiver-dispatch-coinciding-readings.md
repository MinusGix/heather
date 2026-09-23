---
title: Receiver dispatch: accept a class member and a same-named global when they are one term
status: closed
labels: [frontend,elaboration,traits,ergonomics]
code: crates/elab/src/dispatch/receiver.rs:165 @ ab5f21a
created: 2026-09-22
updated: 2026-09-23
---

Receiver dispatch refuses `n.le_dec(m)` in any module that sees both
`Nat::le_dec` and `Cmp`, although `instance Cmp<Nat>` fills that field with
`le_dec := Nat::le_dec`. The two readings are one term, and the error protects
nothing. Namespacing `std` (every carrier's kit moving to `Nat::…`, `Bool::…`
with `self` receivers) makes this the common case rather than the corner:
`le_refl`, `le_dec` and every future class field named after the carrier-owned
lemma that fills it.

## The rule as it stands

`docs/traits-receiver-dispatch-design.md` §4 rule 2: an ordinary type-owned
member and a class member at one carrier are an error naming both, because
preferring either would let a library addition silently reinterpret a call.
`crates/elab/src/dispatch/member.rs:135` builds the `other` reading (a
type-owned member, a bare name in scope, or a builtin) and
`crates/elab/src/dispatch/receiver.rs:165` raises the error after a successful
dispatch.

## The change

Refuse only when the readings **differ**. After dispatch succeeds and `other`
is a global (the first two kinds, never a builtin), unfold the resolved
dictionary's field by a bounded, local step — δ on the instance global only,
ι on the record projection, the instance's parameters instantiated — and
compare the result with the other reading's global: same key, same universe and
type arguments. Equal: accept, and emit the **direct global**, so terms and the
kernel see exactly what they see today. Unequal, or not reducible to a bare
global by that step: the current error, unchanged.

Not general conversion: the test must stay cheap, decidable, and off the
inference hot path's cost profile. Literal-form instances (`field := global`)
are the case that matters and reduce to a name comparison.

Why this keeps the invariant: no reading is *preferred*. When the two coincide
there is one meaning; when a later instance or a local dictionary fills the
field differently, the call becomes an error — growth introduces errors, never
reinterpretations (`docs/modules-design.md` §4). Rule 4 (scope beats registry)
is what makes the local-dictionary case a real difference and not a
false positive: the test reads the dictionary dispatch actually resolved.

Check the type-subject route too (`A.le_dec(x, y)`,
`crates/elab/src/dispatch/projection.rs:98`): if it raises the same rule-2
refusal, it gets the same test.

## Tests (docs/testing-generated-terms.md axes)

- Coincident, literal-form instance: `n.le_dec(m)` with `Cmp` visible checks,
  and the elaborated term is `Nat::le_dec` applied, not a projection.
- Negative control, scope: a local `[d: Cmp<Nat>]` whose `le_dec` is a
  *different* decider (not convertible — a refl against an accidentally equal
  dictionary pins nothing) still raises the rule-2 error.
- Negative control, registry: an instance filling the field with a lambda or
  another global still errors.
- Generic instance at an **open** carrier (`instance<A> … List<A>`, receiver
  `xs: List<A>` with `A` a binder) coincides after instantiation.
- A checking position, not only inference.

Then drop the qualified spellings the rule forced in `lib/std` where the
receiver form reads better, and amend §4 rule 2 of the dispatch design with one
paragraph.

The larger alternative, making import order irrelevant so the instance can sit
beside its kit, is [[package-order-independence]]; this fix does not wait on it.

## Log

- 2026-09-22: LANDED on branch `worktree-agent-a1438f0235de5ed71` (off ab5f21a).
  `Elaborator::field_is_global` (`crates/elab/src/dispatch/receiver.rs`) is the
  one local step, read syntactically: instance global → λs binding types only →
  record spine entry → the other reading's global, applied to exactly the
  instance's binders. On coincidence dispatch returns `Ok(None)` and the other
  reading runs, so the term is the direct global (tests compare bindings).
  Deviations, all folded into `docs/traits-receiver-dispatch-design.md` §4 rule 2:
  (1) an added parameter-table condition — the same global with `self` not first
  is a different call; (2) generic instances coincide only in the one-equation
  shape (type binders only, `g` taking them as leading implicits, subject domain
  syntactically the carrier), so `requires` instances still refuse; (3) the
  type-subject route stays an unconditional refusal — its readings apply `g` to
  different argument lists. `lib_algebra`'s `sub := sub` ambiguity fixture now
  coincides by design; it moved to a λ field plus a positive.
  Suite: HEAD ab5f21a is red independently (tests call `result::map` against a
  committed `Result::map`, and `lib_algebra`'s five other `slow_acceptance_*`),
  so no green full run exists to compare; the furnace run was INCOMPLETE with
  22 of 23 failures reproduced on unmodified HEAD, the 23rd the fixture above.
  Residue: dropping the qualified spellings rule 2 forced in `lib/std` belongs
  to the namespacing refactor in progress.
- 2026-09-23: Merged with the intro-by-type / app@ line: a class dictionary is now emitted as an unannotated `pair@` spine, and its field applications as `app@`. `field_is_global` reads both through `spelling::pair_of`/`app_spine`. A `pair@` layer writes no field carrier, so for a generic instance the one-equation test reads the carrier off the instance's declared type: unfold it to its record Σ under the n type binders, walk to entry idx+1, strengthen past the earlier entries, and take the field's Π domain (`declared_field_carrier`). Any other shape keeps the rule-2 error. Without this, `Nat::le_refl`/`le_dec` in int.hthr and a_generic_instance_coincides_at_an_open_carrier were refused on the merge. New negative control: a_generic_instance_with_a_respelled_subject_domain_still_refuses (subject domain `LL(A)`, convertible to the carrier but not the same pattern).
