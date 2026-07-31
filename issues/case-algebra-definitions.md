---
title: Sketch: functions defined per-constructor, dispatch as an object
status: open
labels: [frontend,syntax,elaboration,metaprogramming,design]
created: 2026-07-31
updated: 2026-07-31
---

Design sketch, deliberately ahead of need (user, 2026-07-31, off the
[[ir-simulate-design]] round). The observation: ir_v1's `step` is not an
arbitrary function — it is a CASE ALGEBRA for `Ir`, one clause per
constructor, with the recursive call passed in as a value `ev` and the
knot tied elsewhere (`eval`, on fuel). That shape was forced by
performance ([[simulate-conversion-cost]]: single ih occurrence), but it
is also exactly how the kernel already thinks: an eliminator application
IS a dispatch table — a telescope of per-constructor cases. The surface
writes that object as a monolithic `match` and loses the structure.

The feature space, from mild to radical:

1. **Named per-constructor clauses** as separate declarations that the
   elaborator assembles into one function (strawman only:
   `fn step@LetCall(...)`). Buys: per-clause reuse and testing, diffs
   that touch one constructor touch one declaration, and a natural
   anchor for structurally named goals — this is [[split-on-arms]]'s
   naming question appearing on the definition side.
2. **The algebra as a first-class value**: a record of clauses for an
   inductive (the inductive's declaration induces the record type — one
   field per constructor, field types from the constructor telescopes).
   `fold : Alg(D, M) -> D -> M` is then THE eliminator worn as a
   library function, and `step`-shaped open recursion (`ev` passed in)
   is the algebra over the one-layer functor. Generic derived artifacts
   ([[generators-in-the-language]]) would consume such records rather
   than bespoke Rust telescopes.
3. **The performance hook, which makes this more than aesthetics**: the
   single-ih dispatch discipline that [[simulate-conversion-cost]] forced
   should be the SHAPE THE ELABORATOR EMITS, not a style users must know.
   A per-constructor definition form can guarantee it by construction —
   the sugar's lowering is precisely ir_v1's `step`/`eval` factoring.

Boundaries to hold if this is ever built: tables stay CLOSED per
inductive (an open/extensible dispatch would poison intensional instance
keying and [[elaboration-determinism]]); and clauses are one function's
clauses, not typeclass-style scattered instances — coherence by
construction, not by resolution.

Not scheduled; wants [[nested-match-patterns]] first (its elaboration is
the substrate) and profits from [[generators-in-the-language]] thinking.

## Sketches (2026-07-31 discussion, condensed)

Two objects, distinct on purpose — conflating them is what makes
dispatch-table designs muddy. For each inductive `D` and result `M`:

- **`D::Cases<M>`** — one field per constructor, self-typed fields stay
  `D`. Case analysis; no recursion. What ir_v1's `step` is.
- **`D::Alg<M>`** — self-typed fields replaced by `M`. A catamorphism's
  algebra; `fold` ties the knot. What `size` over `Rose` is.

**Rung 1 — the records, writable TODAY** (generic records, function-typed
fields, and `fold`'s termination shape all already elaborate):

```heather
record ListAlg<M> { nil: M, cons: (head: Nat, tail_r: M) -> M }
fn fold<M>(a: ListAlg<M>, xs: List) -> M {
    match xs { Nil => a.nil, Cons(h, t) => a.cons(h, fold(a, t)) }
}
```

So rung 1's feature content is a *generator*: `inductive D` also emits
`D::Cases/Alg/cases/fold` — [[generators-in-the-language]]'s cleanest
warm-up artifact, far simpler than the tier lowerings.

**Rung 2 — open recursion, and the performance discipline made
structural.** `step_cases(ev, prog, env) : IrCases<Res>` closes over the
recursive call; `eval`'s Succ arm becomes
`cases(step_cases(eval(k, prog), prog, env), ir)` — the single-ih shape
[[simulate-conversion-cost]] forced is now a consequence of the form.
Surface sugar (spelling strawman only):

```heather
fn step(ev: Val -> Ir -> Res, prog: Prog, env: Val) match (ir: Ir) -> Res {
    Ret(rs) => ...,
    _       => Stuck,
}
```

declaring three things: `step`, the reified `step.cases`, and *named
clauses* `step.Ret`, … — real definitions, so `step` on `Ret(rs)` unfolds
to `step.Ret(env, rs)` and each clause is its own lemma target
([[split-on-arms]]'s naming, appearing on the definition side).

**Rung 3 — dependent algebras: induction as a record you fill in.**
`D::Elim<P: D -> Type>` with one field per constructor returning
`P(that constructor)`; a proof by induction is a record value, holes per
field are named goals. Names its own blocker: **dependent/higher-kinded
record parameters** (`P: Rose -> Type`; also value parameters,
`IrAlgSound(a: IrAlg<Ir>)`) — the one genuinely new surface capability
in the ladder; type params today are first-order `A: Type<n>`.

**Rung 4 — passes as algebras, certified once.** A rewrite pass is
`IrAlg<Ir>`; its obligation is the induced per-clause law record; and

```heather
theorem pass_sound(p: CertifiedPass, ir: Ir): refines(fold(p.alg, ir), ir)
```

is proved ONCE against `elim`. Pass authors discharge eight local
lemmas and never write the induction — [[certifying-generator]]'s
prove-once shape at pass level. This rung is why *first-class* beats
*sugar*: the proof of a fold has the shape of its algebra, and only a
reified algebra lets one generic theorem quantify over that shape.
Further out: algebra composition with certified fusion
(`fold a ∘ fold b = fold (a ⊙ b)`) — certified deforestation of pass
pipelines.

Direction note (user, 2026-07-31): part of the appeal is deliberately
making algebra-style objects *central* to the language — a faux form of
internal-language-style reasoning, where structured folds and their laws
are the default idiom rather than a pattern. Keep that framing in mind
when weighing rung 3/4 against their prerequisite features.

## Log

- 2026-07-31: Sketches folded in from the 2026-07-31 discussion (see section above): Cases-vs-Alg distinction, rung 1 writable today (feature = generator), rung 2 makes the single-ih discipline structural, rung 3 surfaces the real blocker (dependent record parameters), rung 4 is per-clause-certified passes with a generic pass_sound. Plus the user's framing: algebras deliberately central, as faux internal-language reasoning.
