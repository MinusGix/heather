# Local evidence for decrease obligations

Owner: `issues/termination-local-evidence.md`.

## Selection

An explicit `on` discharge takes priority. Otherwise the lowering tries local
bindings, nearest first, for a type convertible to the decrease goal. Each
candidate is checked in an isolated elaborator with only the goal's and
candidate's dependencies. Unknown unrelated locals do not prevent selection;
unknown required types or unspellable shadowed dependencies decline it.

If no direct proof fits and Omega is available, the lowering collects at most
16 relevant inequality hypotheses and tries the existing arithmetic closer.
The surface filter recognizes `nat::Lt`, `nat::Le`, their unqualified names,
and `<`/`<=`, and requires a shared local name with the goal. This is a cheap
filter, not evidence of validity: ordinary elaboration and kernel checking
validate the trial theorem. A failed trial is discarded and the previous
default closer or unsolved obligation remains available, preserving the
remaining goal's diagnostics.

The arithmetic proof mentions selected hypotheses through fresh local aliases,
so normal obligation lifting captures their dependency closure. Automatic
proofs use the same unscaled user goal as manual discharges in mutual groups;
the existing checked rank arithmetic still justifies the lowered call.

## Record fields and type recovery

Proof fields participate through an explicit binding:

```heather
let small = progress.bound;
recurse(progress.next)
```

There is no implicit traversal of records. This keeps the visible local
context in control of selection and avoids recursive searches through data.
For an unannotated projection whose inferred type has no source spelling,
the stored record field signature supplies a candidate: substitute the
receiver's written type/value arguments and projections for preceding fields.
The candidate must re-elaborate to the inferred type before use. Unsupported
receiver shapes decline this fallback conservatively.

## Proof boundary

Evidence queries contain local bindings, not provisional recursive signatures.
A call's decrease obligation is created before its result enters scope, so a
result cannot justify its own call. An earlier call's result is available to
later calls only in a body that must also construct that result through its
own checked decrease proof. Speculative elaborators have independent inline
kernel pools; trial declarations and errors do not commit to the live session.
All emitted obligations and callers still pass the ordinary kernel gate.

This adds no general proof search, automatic record descent, equality-fact
search, or exhaustive arithmetic context exploration. The 16-fact cap and
shared-name filter can leave goals for a manual discharge.

## Client and validation

The calculator retains its local `small` proofs and removes both ordinal
`on ?dec2 := small` discharges. Its existing AST examples, open-input pipeline
law, and false-result controls remain acceptance gates.

`termination_local_evidence.rs` covers direct proofs without Omega, an
unannotated dependent record field, symbolic arithmetic requiring multiple
facts, unrelated unknown lambda locals, and false, reversed, insufficient,
and circular evidence. An invalid explicit discharge is rejected even when
automation could succeed; failed cases are followed by a clean declaration
in the same elaborator. Existing mutual recursion, typed-context, measure,
and unfolding suites cover compatibility and earlier-result evidence.

Focused acceptance: **41 passed, 0 failed** across six test targets.

Full `scripts/test`: **2659 passed, 0 failed, 5 ignored**.
The post-suite benchmark gate reports six Nat timing flags and no slope
failures, recorded in `issues/kernel-benchmark-nat-baseline-drift.md`.
The baseline is unchanged. Tracker and whitespace checks pass.
