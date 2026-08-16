---
title: Sketch: named arguments at call sites
status: open
labels: [frontend,syntax,design]
created: 2026-07-27
updated: 2026-08-16
---

**Sketch, not scheduled.** Raised by the user while
[[at-and-type-arguments]] was being settled, and filed because it is a third
knob on the same axis rather than a separate idea.

```heather
sym(p)                       // everything inferred
sym(p, a := x)               // one implicit pinned by name
map(xs := ys, f := g)        // explicit arguments, order-free
```

## Why it belongs next to the `@` work

[[surface-polymorphism]] and [[at-and-type-arguments]] left the surface with
two *positional* overrides — `@` for value implicits, `<…>` for type
parameters — and both are all-or-nothing. `@sym(a, b, p)` exists only because
there is no way to say "infer `a`, but let me give `b`". Named arguments
subsume both cases and are finer-grained:

- `@f(…)` becomes sugar for "every implicit given, positionally", and would
  arguably stop earning its own syntax.
- `f<T>(…)` likewise, for the type parameters specifically.
- The `calc` desugaring emits `@trans(a, b, c, p, q)` (`parser.rs`'s
  `calc_expr`) purely to force the endpoints; named arguments would let it
  name the two it cares about and leave the rest alone. That desugaring has
  now been fragile twice.

## The reason it is cheaper here than in Rust

Rust has postponed named arguments for a decade, and the reason that bites
hardest there **is already paid for here**: in Rust a parameter *name* is
private to the body — documentation, not interface — so making names callable
would retroactively turn every rename into a breaking change across the whole
ecosystem.

In Heather parameter names are **already API**, deliberately and in writing:
[[goal-holes]] names an argument-position goal after the callee's parameter
("proof-parameter names are API precisely so this reads",
`crates/elab/src/lib.rs`'s `ParamMeta`), `on ?bound := …` discharges by that
name, and `ParamMeta` carries it for exactly this purpose. So the semver
question that stalls Rust does not arise; the names are load-bearing already.

The other Rust obstacles are worth checking against this design rather than
assuming they transfer:

1. **Trait methods.** An `impl` may name its parameters differently from the
   trait declaration, so it is genuinely ambiguous which names a caller at a
   generic type may use. Lands here with [[compile-typeclass-design]] /
   [[surface-records]], not before — but the answer should be decided *with*
   that round, since a record of operations is where it first bites.
2. **Indirect calls.** A function *value* has a `Type::Pi`, and `Type::Pi` has
   no names — the same structural gap
   [[implicit-binders-in-function-types]] documents for implicitness. So
   named arguments would work on named callees and not on λ-bound ones, which
   is a two-tier rule and wants a decision, not a silent restriction.
3. **Default arguments.** Rust has repeatedly bundled the two and stalled on
   the pair. **Keep them apart.** Defaults are a separate feature with their
   own evaluation-order and elaboration questions, and nothing here needs
   them.

## Design questions

1. **Spelling.** `f(a := x)` reuses `:=`, which already means "discharge" in
   `on ?g := e` — arguably the same idea (fill this named slot). `f(a: x)`
   collides with type ascription; `f(a = x)` collides with the equality type
   former, which is the one `=` Heather deliberately merged onto
   ([[surface-syntax]]). `:=` looks right for that reason.
2. **Mixing with positional.** The usual rule — positional first, named after,
   no gaps — or fully order-free? Order-free is harder for the elaborator only
   because the Π spine is ordered; the arguments still have to be *elaborated*
   in dependency order, since a later parameter's type mentions an earlier
   argument. That is the real constraint and it should be stated, not
   discovered.
3. **Does naming an implicit make it explicit?** `sym(p, a := x)` gives `a`
   and leaves `b` inferred, which is the whole point. `apply_implicit` already
   carries a per-parameter mask; this is that mask with a third state
   (`inferred` / `positional` / `given-by-name`).
4. **Constructors and `match` arms.** `Cons(head := x, tail := xs)` is natural
   and the field names already exist (`FieldDecl.name`). Whether *patterns*
   get the same (`Cons(head, tail)` by name rather than position) is
   [[surface-records]]' question too, and the two should agree.

## Out of scope for the sketch

Default arguments, variadics, and any form of overloading.

## Log

- 2026-07-27: Filed as a sketch after [[at-and-type-arguments]] landed. Not
  scheduled: it wants [[surface-records]] first, because the trait/record
  layer is both where argument lists get long enough to need it and where the
  trait-method naming question has to be answered anyway.
- 2026-07-27: **[[surface-records]] landed, and it added a second payoff —
  worth pulling this forward for.** A record's constructor is an ordinary
  constructor, so `Monoid(unit: 0, op: f)` would be an ordinary *call* with
  named arguments, saying exactly what the braced literal
  `Monoid { unit: 0, op: f }` says. The braced form is now marked provisional
  (docs/surface-records.md §6), because retiring it in favour of this would
  delete a whole ambiguity class: `{` after an expression collides with every
  position where a *block* follows one (`match m { … }`, a declaration's
  result type), which currently needs a Rust-style suppression flag lifted
  inside brackets. That flag is a standing hazard rather than a one-time cost
  — every future block-preceding construct has to remember it, and
  [[effects-direction]] will bring more of them. A call is in parentheses, so
  it has none of that.

  Concretely, this issue now buys: finer-grained `@`/`<…>` overrides (the
  original motivation), `calc`'s fragile fully-explicit `@trans` desugaring,
  and the record-literal ambiguity. Open question 4 above ("constructors and
  `match` arms") is no longer a nice-to-have but the load-bearing case.

  Also relevant to open question 4, from the same round: [[method-receiver-position]]
  argues the receiver should stop being positional at all, which is the same
  observation one layer up.
- 2026-08-16: Adjacent feature ratified in principle (2026-08-16, from the true-prop-trivial-hypotheses discussion): default argument values declared at the binder (x: T := e), the chosen mechanism for discharging definitionally-trivial hypotheses on generated refines signatures, and per the user a wanted general tool — including defaults that run a tactic search over the surrounding context, not just a stored term. Defaults are half the reason named arguments exist, so the two likely design together; this issue is the natural home.
