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

Note the shape of that table: four of six are axis 2, and in every case the
generalization that would have caught it costs one extra test with one extra
context entry.

The sixth is worth reading twice, because it says something the first five did
not: for a whole phase the axis-2 control was **not writable**. `Rose<A>` at
an open element type needs a declaration with a type parameter, and until
`surface-polymorphism` there was no such thing. When an axis cannot be varied,
that is itself the finding — the missing language feature is also a missing
test.

The last row (2026-08-03) widens the jurisdiction: it was hiding in the
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
