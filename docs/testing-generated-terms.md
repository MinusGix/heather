# Testing generated terms: the axes a test has to vary

The elaborator generates kernel terms — the `vec.rs` schemas, the tier-0/1/`Wf`
lowerings, `nth` and friends. The kernel re-checks every one, so a bug here is
never a kernel soundness bug; it is one of two things:

- a **rejection** of a valid program (a wrong *annotation*), or
- a **checked theorem about the wrong object** (a wrong *encoding*).

Both are found only by a test whose instance is general enough to expose the
distinction. This codebase has now paid five times for a test that was too
special, in three distinct ways, so the axes are written down here rather than
rediscovered.

## The three axes

**1. Scrutinee shape: literal *and* neutral.** At a literal length or a closed
constructor form everything β-reduces, and a wrong annotation is discarded
before it is ever compared. At a neutral one nothing reduces and the
annotations carry the whole burden. Every `vec.rs` schema has both; that is
why the module's tests come in pairs.

**2. Instance generality: closed types hide shifts.** A de Bruijn shift error
on a *closed* type is the identity. `map`, `fold` and `tabulate` were all
tested at element type `Nat` and all passed for a phase, while `tabulate`'s
index-function type was shifting by one too few
(`docs/container-proofs.md` §10.1). The control is an element type that
mentions an ambient variable — `Vec(Nat; m)` under `Γ = (m, …)` is enough.

**3. Mode: computing is not checking.** A test that only *evaluates* — closed
values, `refl` at a numeral — never compares an annotation against a goal.
A plain child's ih annotation in a container constructor was wrong for a whole
phase because phase 2's mixed-constructor test only computed
(`docs/container-proofs.md` §10.2). It takes a **proof**, where the ih's stated
type has to convert with the goal, to notice.

And the standing fourth and fifth. The fourth is about direction rather than
instance:

**4. Positive tests cannot distinguish a type from a quotient of it.** Building
and projecting still work when a field has been silently dropped, because
dropping a field makes a *smaller* type. Only a negative control — two values
that must *not* be equal, a false theorem that must be rejected — sees it
(`docs/container-fields.md` §9.1).

The fifth is about *cost* rather than correctness, and it is the one a
performance fixture has to vary:

**5. Nesting depth of non-tail recursive calls.** A fixture that grows a
*chain* — more fuel, more instructions, a bigger payload — measures the
per-step constant and nothing else. The thing that explodes is depth:
recursive calls in scrutinee position, `match f(x) { … f(y) … }`, where
each level's work is re-done inside the level above it. `conv/simulate-depth`
and `conv/simulate-payload` are linear and flat respectively, and they were
*right* about what they measured; they were blind to a ~×22-per-loop-iteration
exponential in the same interpreter, because neither varies nesting
(`issues/whnf-sharing-term-growth.md`). The general form of the axis is
broader than "recursive call": it is **anything the code carries forward
stored as an unforced redex** — a configuration field, even an identity
wrapper, does it too (same issue, the falsified step-machine section). So
the control is a family parameterized by depth, `N = 1..8`, asserting a
*ratio* between levels rather than an absolute time.

And a sixth, found 2026-08-04, about *arity* rather than instance or mode:

**6. Case-tree emitters need at least three constructors.** A lowering that
emits a `Case` *tree* (`Inl`/`Inr` over a summand spine) has an inner-`Case`
path that two constructors never take: with two summands there is one node
and no `#rest` branch. `wf_case_tree`'s `Inr` annotations were shifted by
one too few for the inner context — `d + 1` where the substitution's
`embed(…, 2)` says two binders past `cx` — and the same closure was shared
by `idx_case_tree`/`indexed_case_tree`. Invisible at a closed payload type
(axis 2 again, the annotations then mention no ambient variable) *and*
invisible at ≤2 constructors; the symptom is a kernel `LevelMismatch`,
never a wrong answer. Minimal reproducer: a three-constructor tier-1
inductive with an open payload, `match`ed. So the control for anything that
emits a case tree is one declaration with **three or more constructors,
crossed with axis 2** — and the middle constructor's arm is the one that
sits under the inner node.

Refined 2026-08-05, by the *same* defect surviving in the one case-tree
emitter that round did not touch — tier-0's `inductive.rs::case_tree`, where
`inner_motive`'s injection landed two binders past `cx` and was shifted by
`d + 1`. Three constructors and an open payload are **not sufficient**: the
control needs a third condition, a **dependent motive**, one that actually
mentions `z`. At a non-dependent motive the injection is substituted for a
variable that does not occur, so the mis-shifted annotations are discarded
before the kernel is ever shown them — and every tier-0 test at three
constructors and an open payload passed for a phase. The reproducer is that
pair plus `as λ z => f(z) = z`
(`docs/match-equation-split-design.md` §11.2), pinned in
`crates/elab/tests/inductive_tier0.rs`. Note what found it: the `match h : e`
convoy, whose motive `Π (e = z). M` is dependent *by construction* — so the
equation binding doubles as a stress test for every motive consumer in the
elaborator.

## The evidence

| defect | what hid it | axis |
|---|---|---|
| `unit-level-and-vec-preservation` | level-0 instances only | 2 |
| `tyvar-scoping-in-lowered-fields` | closed field types | 2 |
| container fields silently dropped (`container-fields.md` §9.1) | every test positive | 4 |
| `tabulate`'s index-function shift (`container-proofs.md` §10.1) | element type `Nat`, always closed | 2 |
| plain child's ih length (`container-proofs.md` §10.2) | mixed constructors only ever computed | 3 |
| `wf_branch`'s container-length projection context (`surface-polymorphism.md` §10.1) | closed *type parameters* — an inductive could not be instantiated at an open type until `fn f<A>` existed | 2 |
| exponential conversion cost in the IR interpreter (`whnf-sharing-term-growth`) | two bench fixtures that varied fuel depth and payload, never nesting | 5 |
| `Vec`/`Fin`/`El` strip-blind at canonical indices (`sprop-design.md` §5.4 correction; `seq-strip-type-former-negatives`) | `seq_transp.rs` lengths were context variables, never literals | 1 |
| `wf_case_tree`/`idx_case_tree` inner-`Inr` shift (fixed in the 2b-generator round, 2026-08-04) | every case-tree consumer had ≤2 constructors or a closed payload — the inner `Case` never met an ambient variable | 6 (× 2) |
| tier-0 `case_tree`'s inner injection shift (fixed 2026-08-05) | the same, **plus** every three-constructor open-payload tier-0 test having a *non-dependent* motive, which substitutes the bad annotations away | 6 (× 2, × dependence) |
| `forded.rs::ctor_spine_at` re-lowering the skeleton at **no** type arguments (fixed 2026-08-05) | a parameterized forded family always had a *recursive* skeleton in the tests, and every non-recursive one was monomorphic — the two were never crossed, and each half alone is blind | 2 (the axis was **unwritable**, see below) |

Note the shape of that table: four of six are axis 2, and in every case the
generalization that would have caught it costs one extra test with one extra
context entry.

The sixth is worth reading twice, because it says something the first five did
not: for a whole phase the axis-2 control was **not writable**. `Rose<A>` at
an open element type needs a declaration with a type parameter, and until
`surface-polymorphism` there was no such thing. When an axis cannot be varied,
that is itself the finding — the missing language feature is also a missing
test.

The last row (2026-08-05) is the second time "the axis could not be varied"
was itself the finding, and this time the obstacle was a *defect* rather than
a missing feature. The sweep of `issues/dependent-motive-crossing-sweep.md`
set out to cross axis 6 with axis 2 on the forded `idx_case_tree`, which
means writing one declaration that is forded, non-recursive **and**
parameterized — and that declaration did not elaborate at all. So the axis-2
control for a lowering is worth attempting even when it looks routine: the
attempt is a test of whether the instance exists, and here it found a
name-resolution leak (`unknown type \`A\``, pointing at the declaration) on
every use of a whole class of declarations. Corollary for a *crossing* sweep:
when two conditions have each been tested alone, that is not evidence their
product works.

The 2026-08-03 row widens the jurisdiction: it was hiding in the
**kernel's own suite**, not in a generated-term schema. This doc was written
for elaborator schemas, but the axes apply to any test whose scrutinee-like
position can be either canonical or stuck — a `Vec` *length* is a scrutinee
in that sense, and `seq_transp.rs` only ever made it a variable. When a test
exercises a rule keyed on canonical-vs-neutral, vary that key; the schema/
kernel boundary is not where the discipline stops.

## The minimum for a new schema

Four tests, and they are cheap because they are the same term at four
instances:

1. literal scrutinee — **and assert it computes**, not merely that it types
   (`conv` against the expected reduct, not just `check`);
2. neutral scrutinee;
3. open element/result type, mentioning an ambient variable;
4. one use in a *checking* position — a proof, or anything where the annotation
   must convert with a goal rather than being reduced away.

Plus, for anything that lowers a declaration rather than building a schema, a
negative control per encoding decision (axis 4).

## Where the test goes

At the level the term is *generated*, not only the level it is used
(`docs/container-fields.md` §10.1). Both `map`/`fold` step-domain bugs were
caught in seconds by `vec.rs`'s own test module; through three layers of
elaboration the same bug surfaces as an opaque `NotConvertible` on a user
program, and the search starts from the wrong end.
