---
title: A conjunction passed for an equation argument is refused only by the kernel
status: closed
labels: [frontend,elaboration,diagnostics]
area: language
created: 2026-10-04
updated: 2026-10-28
---

Found while proving the stat pass (`lib/elf64_stat_width.hthr`, 2026-10-04).
A proof of a conjunction passed where an equation is expected gets past the
elaborator, and only the kernel refuses it, at the whole declaration, with no
span and no types:

```heather
theorem bad4(a, b: Nat, p: (a = b) ∧ (b = b)): b = a { sym(p) }
// error: the kernel rejected `bad4`: NotConvertible
//   --> …:1:1
theorem bad2(a, b, c: Nat, p: (a = b) ∧ (b = b), q: b = c): a = c { trans(p, q) }
// the same; `trans<Nat>(p, q)` and a `let r: (a = c) = trans(p, q)` too
```

`sym` and `trans` are ordinary prelude theorems (`crates/elab/src/prelude.hthr`)
whose equation's sides are implicit, so the check of `p` against `?a = ?b`
should fail to unify `Eq` with `∧`. Something in that path accepts it instead
(the sibling [[check-fallback-discards-expected-type]] was the inference
fallback; that one is closed, so this is a different route).

How it cost time: one projection too few (`regs.right…right` stopping at the
last conjunction instead of its right side) inside a 40-line proof. The
kernel's refusal named the theorem only; finding the line took a bisection
with `axiom hole<A>(): A;` stand-ins, and it hid behind an unused `let`
(dropped before the kernel sees it), so a stand-in for the *use* passed while
the bad `let` was still in the source.

Not a soundness problem (the kernel refuses), a diagnostics one: the
elaborator should point at `p` and say it is a conjunction, not an equation.

The counting that produced the bad projection is [[conjunction-facts-read-by-counting]].

## Log

- 2026-10-04: A second shape of the same gap, in `lib/elf64_row_fields.hthr`'s `row_selected`: inside a `match first as λ f => … → RowAt(…, f, …) → …` whose arm bound the refined record as `head1`, a record built from `page := head.page` and `holds := head1.holds` elaborated, and the kernel refused it (`PageNext` "where a type that displays the same is expected"). Here the kernel's message did carry a span. The elaborator treated `head1.page` and `head.page` as the same; they are different variables.
- 2026-10-25: Another mismatch only the kernel refuses, under a let-bound or β-redex head: [[elab-accepts-mismatch-under-redex-head]].
- 2026-10-26: The filed `bad4`/`bad2` are now reported by the elaborator at `p` (`this has type `And<a = b, b = b>`, but `a = b` is expected here`), since `OwedChecks` (#168): `sym`/`trans`'s equation sides are implicit, so `p` was an inferred argument. The redex-head case is closed. The second shape in the log (a refined record's `head1.page` taken for `head.page`) is not rechecked.
- 2026-10-28: The second shape rechecked against a reconstruction (`match first as λ f => RowAt(f) → RowAt(f)`, an arm building `RowAt(head.page, head1.holds)`): reported at `head1.holds` as `this has type `head1.page = 0`, but `head.page = 0` is expected here`. The original source did not survive the native-v0 burn, so this is the shape, not the file.

## Resolution (2026-10-28): the class, not the instance

**The class.** The elaborator records, the gate decides: every place the
elaborator puts a term at a type it did not itself compare records a
candidate (a checking mismatch, an inferred argument's owed check, a written
`refl`, a `decide`), and when the gate refuses, the first candidate whose
probe decides the refusal is where it is reported. A route that places a
term *without* recording is invisible to that scheme, and its refusals come
back as a bare `NotConvertible` at the declaration. This issue's filed case
was one such route (inferred arguments, closed by `OwedChecks` in #168);
[[check-fallback-discards-expected-type]] and
[[elab-accepts-mismatch-under-redex-head]] were the same symptom from other
routes, each found by bisection. Closing routes one at a time cannot
guarantee the next one, because the list of routes is kept by hand.

**The net.** The kernel is the one place every placement passes through, so
the kernel says where. `typing::locate_refusal` (and `locate_type_refusal`
for statements) re-runs a refused check with a recorder that keeps the
innermost failing term check: Γ, the term, the expected type, the inferred
type when the check reached its closing conversion, and the error. It runs
only on a refusal no recorded probe decided (one more kernel check of the
refused declaration; nothing on any accepting path: an `Option` checked on
the error branch of `tm_check`). `Elaborator::kernel_refusal` then:

- looks the located term up among the recorded sites, **by syntax**: a
  written `refl` at the same Γ claiming the refused equation, or a checking
  site at the same Γ comparing the same two types. A site whose probe was
  only inconclusive (out of the note's small budget) is still the site, and
  the kernel has now decided it, so the report moves there. That was live:
  the interval search pins (`lib/_tests/std/num/float/interval_tests.hthr`,
  `creal_interval_tests.hthr`) are `refl`s whose sides outrun the note
  budget, and were reported at the whole declaration; they are now at the
  `refl`, with both sides.
- otherwise reports `KernelSite::Unrecorded`: the gate's verdict and the
  declaration's span, plus `no checking site recorded this refusal: the
  kernel refused `p`, which has type `And<a = b, b = b>`, where `a = b` is
  expected (an elaborator gap: …)`. The names are the recorded sites' where
  their Γ is a prefix, the declaration's parameters by position, then fresh.

**The guarantee.** `ElabError::Kernel` carries `site: KernelSite`
(`Recorded`, `Unrecorded`, `Other` for fuel/levels/generated definitions).
An `Unrecorded` refusal is never the user's mistake alone, so nothing may pin
one: `support::assert_refused` fails on it whatever the expected `Refusal`,
and `heather check --expectations` refuses to let any `expect-error`
directive match it. A new route that forgets to record is then (a) still
readable — term and both types — the first time anyone meets it, and (b)
unpinnable, so it cannot settle into the corpus as an accepted refusal.

**Census.** Every `expect-error` in `lib/` (80 refusals over `lib/_tests`)
and every `Refusal::Kernel` pin in the elab tests passes the new rule: no
live unrecorded refusal is pinned. The interval pins above were the only
ones the locator moved.

**Tests.** `crates/kernel/tests/typing.rs`:
`locate_refusal_names_the_innermost_failing_check` (a variable under a λ,
not the λ; a λ at `Nat` with no inferred type; a passing check locates
nothing). `crates/elab/tests/check_reports_mismatch.rs`:
`an_unrecorded_refusal_names_the_refused_term_and_both_types` re-opens the
filed gap with the test-only `Elaborator::forget_owed_argument_checks` and
asserts the net's message, flag, verdict and span for both filed cases; its
control `a_recorded_site_still_reports_at_the_argument`.

Not covered: the located term carries no source span (kernel syntax has
none), so an unrecorded refusal names its term rather than pointing at it.
