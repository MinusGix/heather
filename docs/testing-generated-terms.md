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

And the standing fourth, which is about direction rather than instance:

**4. Positive tests cannot distinguish a type from a quotient of it.** Building
and projecting still work when a field has been silently dropped, because
dropping a field makes a *smaller* type. Only a negative control — two values
that must *not* be equal, a false theorem that must be rejected — sees it
(`docs/container-fields.md` §9.1).

## The evidence

| defect | what hid it | axis |
|---|---|---|
| `unit-level-and-vec-preservation` | level-0 instances only | 2 |
| `tyvar-scoping-in-lowered-fields` | closed field types | 2 |
| container fields silently dropped (`container-fields.md` §9.1) | every test positive | 4 |
| `tabulate`'s index-function shift (`container-proofs.md` §10.1) | element type `Nat`, always closed | 2 |
| plain child's ih length (`container-proofs.md` §10.2) | mixed constructors only ever computed | 3 |
| `wf_branch`'s container-length projection context (`surface-polymorphism.md` §10.1) | closed *type parameters* — an inductive could not be instantiated at an open type until `fn f<A>` existed | 2 |

Note the shape of that table: four of six are axis 2, and in every case the
generalization that would have caught it costs one extra test with one extra
context entry.

The sixth is worth reading twice, because it says something the first five did
not: for a whole phase the axis-2 control was **not writable**. `Rose<A>` at
an open element type needs a declaration with a type parameter, and until
`surface-polymorphism` there was no such thing. When an axis cannot be varied,
that is itself the finding — the missing language feature is also a missing
test.

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
