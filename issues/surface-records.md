---
title: "Records: named-field Sigma sugar"
status: open
labels: [frontend,syntax,elaboration,design]
created: 2026-07-26
updated: 2026-07-27
---

Named-field records desugaring to `Σ`, with `p.field` projection and
non-dependent `A × B`. Specified as a requirement in [[front-end-sugar]]
("Σ sugar — now concrete, motivates the whole issue") since 2026-07-23;
this is the work item.

```
record Monoid<A> { unit: A, op: A -> A -> A, unit_l: (x: A) -> op(unit, x) = x }
```

## Why now, and why after [[surface-polymorphism]]

A trait, an algebraic structure, a `Compile` instance and an
optimization-pass interface are all *records of functions*, and none of them
exists without this — [[compile-typeclass-design]] is blocked on it directly.
But a monomorphic record is nearly useless, since every interesting record is
generic in its carrier, so this lands after (or with) polymorphism rather
than before.

Most of the substrate is already there and already exercised:

- `Type::Sigma`, `Pair`, `Fst`, `Snd` are v0 formers, and **η for pairs is
  definitional** (`conv.rs:668`), which is what makes `let (a, b) = p`
  transparent and what tier 0's field-offset scheme already leans on.
- The tier-0 lowering (`docs/inductive-tier0-lowering.md`) already builds a
  Unit-terminated Σ spine per constructor with field projection as
  `fst(snd^j)`. A record is that scheme with one constructor and named
  accessors.
- A dependent field (`unit_l` above mentions `unit` and `op`) is exactly why
  the spine is Σ and not a product; that part is designed.

## Open questions

1. **Is `record` a distinct declaration form, or a one-constructor
   `inductive` with accessor sugar?** The second is less machinery but
   inherits the nominal tag discipline and the tier classification; the first
   is a second declaration path to keep in step. Related: a record should
   *not* be recursive — that is an `inductive`.
2. **Projection vs. pattern.** `p.op` and `let { unit, op } = p` are both
   wanted; with Σ-η they are interchangeable, which is worth pinning as a
   test rather than assuming.
3. **Where the level goes.** A record over `A : Ty 0` lives at level 1 as
   soon as it stores a type. State the level rule before writing code —
   non-cumulativity has bitten twice already
   ([[unit-level-and-vec-preservation]], `docs/unit-empty-level-indexing.md`).
4. [[dependent-field-injectivity]] applies here verbatim: a later field whose
   type mentions an earlier one is the *normal* case for a record, not the
   exotic one.

Not in scope: instance resolution / typeclass search
([[compile-typeclass-design]]), and coercions of any kind.

## Log

- 2026-07-27: **LANDED.** docs/surface-records.md (§11 records what
  implementing corrected), crates/elab/tests/records.rs — 33 tests, workspace
  at 508. `record Monoid<A> { unit, op, unit_l }` declares, `m.op(x)(y)`
  projects and applies, `Monoid { … }` constructs in any field order, and
  `let { unit, op } = m;` destructures. No kernel change and no ch. 07 pass,
  as predicted: a record is a one-constructor tier-0 inductive and every term
  emitted is one that generator already emitted.
  - **The scheme missed a blocker on its own line one** (§11.1):
    `reject_function_fields` rejected *any* field containing a `->`, so
    `op: A -> A -> A` — the motivating example of this issue — did not
    declare. The check was keyed on the field type's **shape** when the
    property it wanted is a **self-occurrence**: a function field is
    infinitary because the declaration appears in it, and one that does not
    mention it is an ordinary `Type::Pi` payload. Corrected to reject a `Π`
    field mentioning the declaration, in domain or codomain. `Acc` stays
    rejected and now says why; `inductive Endo { Mk(f: Nat -> Nat) }` now
    works. This hid because until records there was no reason to put a
    function in a field — the same shape as the container-field and
    dependent-field restrictions, a limitation written down as a property of
    the tier when it was a property of the check.
  - **The literal collides with every block-preceding position** (§6.1, added
    while implementing): `match m { … }` would read the arm block as a record
    literal. Rust's fix, and Rust's cost — a suppression flag in the `match`
    scrutinee, the `match` motive and a declaration's result type, lifted
    inside brackets. Consequence worth knowing: a record literal in a
    `theorem` **statement** must be parenthesised, which is exactly where η
    statements live.
  - **η holds** (§10.6, the load-bearing test):
    `(P { x: p.x, y: p.y }) = p` by `refl` at a neutral `p`, and again at a
    record with a dependent field. Σ-η and `Unit`-η through the nominal tag
    together, as tier-0 §3.3 predicted.
  - `.` moved from parser to elaborator with **no regression**: the cheap
    negative test (is this name anybody's field?) keeps every pre-records use
    off the resolution path entirely, so `p.sym()`, `p.inj(1)`, `p.absurd()`,
    `.cong(Succ)`, `calc` and `xs.map(f)` elaborate exactly as before. Two
    parser unit tests asserted the old desugaring and were rewritten to assert
    the `Dot` shape instead; nothing else in 508 tests moved.
  - Found and not fixed, both logged: `.trans()` reads backwards under the
    receiver-last convention (`q.trans(p)` is `trans(p, q)`) — pre-existing,
    an argument for [[named-arguments]] — and [[numeral-stack-depth]], filed
    separately, which is unrelated to records and cost an hour of bisection
    that looked like a projection loop.
  - Still out of scope as scoped: record equality *construction* (§7 — the
    [[setoid-auto-lifting]] route for function fields), bundled records (a
    `Type`-valued field, §3), anonymous `⟨…⟩` literals, record update, and
    instance resolution ([[compile-typeclass-design]], which this unblocks).

- 2026-07-27: **Scheme written: `docs/surface-records.md`**; implementation is
  the next code round. All four open questions above are answered there, and a
  fifth was found that is larger than two of them.
  - Q1 → **both, because they are different questions.** The *lowering* is the
    tier-0 one unchanged (a `record` desugars to a one-constructor
    `InductiveDecl` plus a field table; that doc already treats records as its
    own `n = 1` case), but `record` is its own *surface* form, because a bare
    one-constructor inductive cannot reject recursion at the declaration,
    cannot expose fields outside a `match` arm, and has no name for the
    literal. One internal path, so nothing goes stale.
  - Q2 → both, sequenced: projection first (it is what the trait layer needs),
    named destructuring second (it is sugar over the same projections, and
    `match` already covers it). The test that earns its keep is **not** that
    the two spellings agree — true by construction — but **η**:
    `Monoid { unit: m.unit, … } = m` by `refl` at a *neutral* `m`, which
    exercises Σ-η and `Unit`-η through the nominal tag together.
  - Q3 → there is **no level decision here yet**, because `TyKind` has no way
    to write `Type` (`ast.rs:152`), so no field can store one and every
    writable record joins to 0. What there is, is a level *discipline*:
    state the rule as `⊔` of the field levels (which the spine builder already
    computes) and never write `Level::Zero`. The real question arrives with
    the **bundled** record (`carrier: Type`), named in the doc as its own
    round so it is a grammar change rather than a generator rewrite.
  - Q4 → applies verbatim and will be *hit*, since a law field mentioning
    earlier fields is the normal case. But the more useful observation is that
    records want the **converse** operation: inductives needed to *destruct*
    an equality (`inj`), records need to *construct* one, and that is a
    different blocker. Scoped out, with the shape of the answer recorded: full
    field-wise equality for a record with no function fields once
    [[dependent-field-injectivity]] lifts, and a canonical setoid symbol
    quotienting functions otherwise — i.e. [[setoid-auto-lifting]], already
    filed for exactly this class. So this is a later round, not a hole, and it
    is **not** a funext dependency.
  - **Q5, new and the round's real work: `.` collides with field projection.**
    `.f(args)` is desugared *in the parser* (`parser.rs:571–596`) to a call to
    a **global** `f` with the receiver appended last, and `p.f` with no
    parentheses does not parse. For a record of functions — which is what a
    trait, a `Compile` instance and an optimization-pass interface all are —
    `m.op(x, y)` must mean `(m.op)(x, y)`. Decided: **move `.` out of the
    parser into the elaborator** and resolve it against the receiver's
    inferred type (field wins over a global of the same name; fall back to
    today's desugaring otherwise, including when the receiver is not
    inferrable). This is a change to landed `surface-operators` behaviour and
    is the only regression risk in the round — `.cong(Succ)` especially, which
    reaches an inference position.
  - Also decided: the literal is **braced and named** (`Monoid { unit: 0, … }`),
    order-free, normalized to declaration order in front of tier 0's ordinary
    positional constructor path. Lean's anonymous `⟨0, f⟩` is wanted and
    deferred as a small follow-up — it is a checking-position positional form,
    the same shape as an unsaturated constructor against an expected `Π`, so
    the machinery already exists; it is deferred on lexer support, not design.
- 2026-07-26: Prelude probe (see [[at-and-type-arguments]]) says the inference this round needs is already there: polymorphic sym/trans infer their carrier at Nat and at a declared type, through the method sugar and in chains, with zero failures from implicit uses. The blocker in the way is not the unifier but the surface: '@' currently means every parameter positional, so a callee that gains a type parameter breaks every '@'-call to it. Worth settling before records, since a record of generic operations is exactly the case.
