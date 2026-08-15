---
title: Default fold := via abs in the datarepr clause form
status: open
labels: [design,compiler,ergonomics]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 4, user-ratified
(2026-08-15). The clause form already defaults omitted `C_abs`/`C_inv`/
`fold_law` to `refl`; `fold` stays required though `Bin` shows the
canonical default by hand — fold *through* `abs` (`spec_rec ∘ abs`),
under which `fold_law` is (nearly) refl. The correctness basis need not
be what runs (design §1.2), so this default is semantically clean.

With `fold := via abs` and `inv := True` defaulted, a minimal real repr
is `R`, `abs`, one `mk` per constructor, and only the non-refl laws.

Bonus the round should collect: a repr whose fold is NOT defined through
`abs` becomes expressible as the deliberate case, giving the suite the
control point §3.3's as-landed note 5 records as missing (the
`refines_inv` transport direction is unobservable when fold is defined
through `abs`).

## Log

- 2026-08-15: Reshaped by the obligation-records design (docs/obligation-records-design.md §1.2 FINDING C, §5): this issue and the slot mechanism both want to give an OMITTED clause a meaning, and they disagree. Settled direction there: omission keeps (and gains) the meaning 'take the default', an OPEN obligation is written explicitly as 'field := ?', and a clause that is neither is checked as today — so the two rounds do not collide as long as ordering holds. If the rounds merge, that one sentence is the whole rule; if they do not, the slot round lands '?' first so this round has an unambiguous omission to define. The bonus this issue records (a repr whose fold is NOT through abs, as the missing §3.3 control) is untouched.
