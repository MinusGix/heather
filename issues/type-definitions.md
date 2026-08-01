---
title: Named type-level definitions, so a statement shape can have a name
status: open
labels: [frontend, syntax, elaboration, design]
created: 2026-08-01
updated: 2026-08-01
---

`refines` cannot be a definition. The `fuel_monotone` round landed it as a
statement *shape* — spelled out verbatim in `refines_refl`, twice in
`refines_trans`'s hypotheses, and again in its conclusion — because a `fn`
body is an expression and `->` is not an expression, so there is no way to
write

```heather
type Refines(p1: Prog, i1: Ir, p2: Prog, i2: Ir, b: Nat -> Nat) =
    (env: Val) -> (vs: Val) -> (n: Nat)
    -> eval(n, p1)(env, i1) = Out(vs) -> eval(b(n), p2)(env, i2) = Out(vs)
```

(doc §13 note 7 records the gap; `docs/ir-simulate-design.md` §6 wants the
name, since `converges`/`refines` are the interface clients see.)

Two routes, not necessarily exclusive:

1. **A `type` declaration** — parameterized synonym, elaborated once,
   δ-transparent at its uses. Small, closed-form, no new typing questions
   beyond where it may be used.
2. **Types in expression position generally** — the motive-body round
   already added `ExprKind::TyLit` and parses a motive body with the type
   grammar ([[motives-as-lambdas]] log, 2026-07-31); `a = b` as a term
   already elaborates through its code `TmId : Ty l`
   (docs/surface-universe.md §13). Letting `->` into expression position
   would make a type-valued `fn` an ordinary `fn` and subsume route 1 —
   but it is a grammar decision with ambiguity surface, and codes cap the
   level ([[surface-universe]]).

Either route should answer: does the name survive into diagnostics (a
`Refines(…)` that unfolds on first mismatch is barely better than no name),
and does conversion see through it for free ([[schema-construction-caching]]
territory if not).

Customer list, so far: `refines` (three spellings today), `converges` once
[[surface-existential]] makes it statable, and every `Compile`-instance
obligation [[compile-typeclass-design]] will want to abbreviate.
