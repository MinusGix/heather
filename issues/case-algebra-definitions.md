---
title: Sketch: functions defined per-constructor, dispatch as an object
status: open
labels: [frontend,syntax,elaboration,metaprogramming,design]
area: language
created: 2026-07-31
updated: 2026-08-19
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
The broader mathematical-library direction — container presentations, generic
fold laws, free constructions, derivatives, and zippers — is owned separately
by [[datatype-container-algebras]]; this issue owns the declaration and
generated-artifact surface it may eventually consume.

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
field are named goals. **This rung is now explicitly live**: the dependent
record parameter is a value parameter (`D::Elim(P: D -> Type)`), the shape
made available by record types as type-valued functions and exercised by
`ListElim` / `TreeElim` in [[datatype-container-algebras]]. The old claim that
this needed a new higher-kinded type-parameter feature was stale; generation
of the datatype-shaped shell, not expressibility of the object, is what
remains here.

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
- 2026-08-18: Rung 3's recorded blocker is corrected by implementation, not
  speculation: [[datatype-container-algebras]] now ships explicit
  `ListElim<A>(P: List<A> -> Type)` and `TreeElim<A>(P: Tree<A> -> Type)`
  records plus their structural consumers. An existing theorem (`append_nil`)
  is supplied entirely as a record of constructor obligations, and the tree
  rebuild proof consumes both differently indexed IHs. No language change was
  needed; this issue stays open for generation / per-constructor definition
  surface and the Cases/open-recursion rungs it owns.
- 2026-08-18: Rungs 1--3 now all have explicit real consumers. The missing
  Cases/open-recursion control landed as `IrCases<M>` + `ir_cases` in
  `lib/certgen/ir_v1.hthr`; `step_cases(ev, prog, env)` is an ordinary record value
  whose clauses capture the recursive evaluator, and `step` is its generic
  dispatch. All eight constructor equations are definitional, while an
  independent constructor-classifying consumer pins that this is reusable
  case analysis rather than interpreter-only factoring.

  One old motivation is deliberately weakened by the measurement history:
  the single-IH factoring was once performance-critical, but value-domain
  conversion removed that cliff. Cases still earns its place structurally --
  named/reusable dispatch and an explicit open-recursion boundary -- not as a
  performance primitive. No declaration sugar was needed for the probe. The
  remaining feature question is now only whether and how to generate the
  known shell (including its eventual subject-owned names), not whether the
  three objects are expressible.
- 2026-08-18: Rung 4's first probe is implemented
  (`docs/certified-pass-algebra-probe.md`). On `Tree`, a certified mirror is a
  first-class algebra plus Leaf/Node relational laws, and one generic theorem
  turns those into size preservation for every tree; the wrong Node clause is
  kernel-refused locally. This confirms the proof architecture without new
  language machinery.

  The real-`Ir` version hit a stop condition before semantics: the dependent
  algebra induction exhausts conversion fuel at eight constructors, including
  after relation-to-equality specialization. [[ir-pass-dependent-fold-fuel]]
  owns that refusal. Consequently this issue's IR claim remains OPEN: after
  the mechanical scale boundary is paid, it still owes one genuinely
  semantics-changing pass with `Refines`-shaped local laws. The Tree result is
  evidence for the method, not permission to call an optimizer shipped.
- 2026-08-18: The mechanical IR-scale claim is now paid and
  [[ir-pass-dependent-fold-fuel]] is closed. The cause was the fallback
  projection of the value-parameterized law record: Γ held its
  component-respelled type while emitted `Fst`/`Snd` annotations used the
  inline Σ. Respelling only those annotations preserves structural reads and
  makes the arbitrary-relation eight-constructor induction check at default
  fuel. The concrete `add(0, tag)` pass is certified; `Succ(tag)` is refused.
  This issue remains open for the claim it already separated: a genuinely
  semantics-changing IR pass with execution-refinement laws, and only then a
  decision about generating the known algebra shell. Suite 1926, bench
  106/106.
- 2026-08-18: Rung 4's semantic acceptance is paid by the missing-arm
  extension pass. Its `NoArm` clause emits `Arm(Ret(RNil), NoArm)`, making the
  first formerly missing tag converge while preserving every previously
  successful run at the same fuel. Direct `Refines` alone was not a
  compositional algebra relation: `Arm` and `NoArm` both evaluate to `Stuck`,
  while `LetMatch` observes them through `pick_arm`. The successful relation
  therefore pairs direct-evaluation forwarding with selected-arm forwarding;
  the Arm law dispatches between the body and tail hypotheses, and LetMatch
  consumes that second observation. `ir_fold_sound` builds the global
  certificate and its direct field yields existential convergence refinement.
  Mutating existing arm bodies is refused. No declaration/generator machinery
  was added: constant-match fusion is the next value test before that choice.
- 2026-08-19: The next value test lands: a certified constant-match-fusion
  algebra rewrites a fresh constructor followed by `LetMatch(0, arms,
  Ret(outputs))` when the selected arm is `Ret(arm_outputs)`. It composes the
  arm's `fields ++ con ++ env` references with the continuation's
  `arm_outputs ++ con ++ env` references, including the mandatory Succ shift
  from pre-constructor `args` into the post-constructor environment. Gather
  lemmas certify that composition; the LetCon law combines them with its
  recursive execution hypothesis, and the existing relation-indexed fold
  supplies global same-fuel refinement. A non-empty-field/four-output control
  computes on both sides; omitting the Succ shift is refused. General
  instruction-chain fusion is deliberately declined because landed IR v1
  stores no output arity on multi-output binders (recorded in
  `docs/ir-simulate-design.md` §13 note 10). This is now optimizer evidence,
  not only pass-architecture evidence; generation remains a separate choice.
