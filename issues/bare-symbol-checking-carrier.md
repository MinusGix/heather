---
title: Resolve a bare operator symbol in argument position from the expected domain carrier
status: open
labels: [design,frontend,ergonomics]
created: 2026-08-11
updated: 2026-08-11
---

A bare symbol between delimiters resolves by rung 1 (a binder that named it)
or rung 3 (fallback) only — with no operand there is no carrier to probe
(crates/elab/src/lib.rs, resolve_op_name; docs/operators-onto-classes-design.md
§4). That is why `sum_all` may write `mconcat(+, xs)` (its `<A: Monoid(+)>`
is the rung-1 binder) while `concat` cannot write `mconcat(++, xss)`: `concat`'s
monoid is at `List<A>`, which is no tyvar, so no constraint slot can name the
symbol, and `++` has no fallback. `any_of`/`all_of` are the same story at
`Bool` — `mconcat(||, bs)` refuses today.

The wanted extension: in a **checking** position whose expected type is known
— an argument slot, here `A -> A -> A` with `A := List<B>` — a bare symbol
could take rung 2 from the expected domain's carrier head, exactly the probe
an *applied* symbol takes from its left operand. User motivation (2026-08-11):
`mconcat(++, xss)`, `mconcat(||, bs)`, `mconcat(&&, bs)` read better than the
positional names — the symbol says what is going on at the carrier.

Design questions the round has to answer, not assume:
- The probe direction inverts: an applied symbol infers its operand and reads
  the carrier off the result; here the carrier arrives from *outside*, through
  whatever implicit instantiation has already decided about the callee's type
  parameters at that argument's turn. Order sensitivity is the risk to pin.
- Rung order: a binder still wins (rung 1 before any type is looked at), and
  the no-fallback refusals must stay refusals when the expected domain's
  carrier has no row — with the diagnostic naming the carrier it tried.
- The negative controls of docs/testing-generated-terms.md apply: open element
  type (`concat<A>` itself), concrete carrier, and a checking position is the
  feature, so the negative control is a carrier with no designation.

If it lands, the library collects: `concat`, `any_of`, `all_of` respelled with
their symbols, and the algebra.hthr comment explaining why positional naming
was load-bearing gets rewritten (the constraint slot story stays untouched).
The adjacent mconcat questions filed the same day — the name and any dedicated
syntax in [[mconcat-surface-story]], implicit operation parameters on lemmas
in [[mconcat-single-implicit-op]] — read better after this than before it.

## What it assumes from elsewhere

- **[[list-append-symbol]]** owns `++` (closed). Assumed here: only that the
  designation at `List<A>` is generic over the element.
- **[[binder-symbol-as-notation]]** is adjacent but separate: `as` installs a
  spelling for a *declared* binder; this issue is about a *reference* with no
  binder at all.

## Log

- 2026-08-11: User review (2026-08-11): wanted. The framing to design toward — bare symbols in argument position make operators less magical, one unified presentation of "you can just talk about operators" whether applied, constrained, or passed. Acknowledged more complex than the respelling it enables; complexity budget is the probe-direction inversion already named above.
