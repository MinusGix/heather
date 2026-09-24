---
title: The unifier learns nothing through constructor values: a Cons-congruence cannot solve from its own goal
status: closed
labels: [frontend,elaboration,inference,unification,inductives]
created: 2026-09-24
updated: 2026-09-24
---

The expected type teaches the unifier nothing through a **constructor value**.
`unify_tm` has congruence for applications, `Succ`, numerals and the type
codes, but no case for the pair/injection forms (`pair@`, `inl@`, `inr@`, and
their `app`-era spellings) that an inductive's constructor value is built
from. So a congruence lemma whose implicits appear only inside constructor
values cannot be solved from the goal, even when the goal is syntactically the
lemma's own conclusion:

```heather
theorem cc({l, r: Nat}, {lt, rt: List<Nat>}, h: l = r, t: lt = rt): Cons(l, lt) = Cons(r, rt) { … }
theorem t0(): Cons(1, Cons(2, Nil)) = Cons(1, Cons(2, Nil)) { cc(refl, cc(refl, refl)) }
// error: this argument of `cc` was deferred — the type of its parameter `h`
// still mentions an implicit that could not be inferred
```

Found by the #1b unifier slice's library sweep (2026-09-24). It is why
`lib/std/arch/x86_64/model.hthr`'s three `@byte_cons_cong(…)` calls (~1526)
still write every endpoint, and it is the last feature-shaped `@` in `lib/`
besides the `Decide` instance heads
([[instance-binder-occurrence-through-binder-types]]). Those sites also need
the goal's right side `rr_bytes(opcode, rm, reg)` unfolded before it shows
`Cons`. That is general rigid-side δ, which [[unify-succ-under-addition]]
deliberately did not add (it reduces only toward a successor), so a fix
here may want both.

Direction: congruence through the constructor-value forms, keyed by the same
head reading `matching_value_spine` uses. Learn-only like every case, so the
kernel still judges. Under [[elab-unifier-completeness]].

## Log

- 2026-09-24: 2026-09-24: Landed (docs/unifier-completeness-design.md §10.1): congruence through supf/sup, pairs and injections in both spellings, and λ bodies; the rigid-side reduction generalised to canonical_head, so a goal side behind a definition unfolds to its constructor. The three byte_cons_cong calls write no endpoints. Test in crates/elab/tests/implicit_args.rs; full suite 2943 passed.
