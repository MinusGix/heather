---
title: "Checking falls back to inference and discards the expected type, so an ordinary mismatch is a kernel rejection"
status: closed
labels: [frontend,elaboration,diagnostics]
created: 2026-08-17
updated: 2026-08-17
---

Found while writing negative controls for
[[match-arg-of-polymorphic-callee-needs-motive]] (2026-08-17). The simplest
type error in the language does not get an elaborator message:

```heather
fn d5<A>(xs: List<A>) -> List<A> { 3 }
// error: the kernel rejected `d5`: NotConvertible
//   --> …:3:1     (the whole declaration; the `3` is not pointed at)
```

The cause is one line, and it is the *end* of `elab_check_skel`
(`crates/elab/src/lib.rs`, the `_ =>` arm): when no syntactic arm claims the
expression, checking infers it and throws the inferred type away —

```rust
let (t, _, _) = self.elab_infer_at(cx, e, if suppress { None } else { Some(&head) })?;
Ok(t)
```

The expected type is passed *in* as a hint for implicit solving, and it is
never *compared* with what came back. So every mismatch that reaches this arm
is discovered by the kernel, at the declaration, with no span and no types.

## Why it is worth its own issue rather than a shrug

The architecture says the kernel is the judge, and it should stay the judge —
this is not a request to typecheck in the elaborator. It is a request to *say
what happened* before handing over. Three things make it live now:

- The class is not exotic. A literal at the wrong type, a variable at the
  wrong type, an arm that disagrees with its `match`'s motive — all of them
  land here. [[match-arg-of-polymorphic-callee-needs-motive]]'s synthesis adds
  one more route to it (arms that disagree, where a motive-less `match` in
  inference position used to stop earlier with a message about the motive).
- [[elab-unifier-completeness]]'s 2026-08-04 log records the same complaint
  from the other end — a polymorphic function at a monomorphic argument type
  dying as a bare kernel `LevelMismatch` — and calls it "a diagnostics dent on
  a shape a user would consider ordinary". Same dent, and this is where it is.
- It interacts with [[le-diagnostics-print-raw-el]]: whatever this reports has
  to print two types, and printing types is that issue's problem.

## Shape of the fix, and the one caution

Compare at the fallback — `conv_ty` at `Layer::Prog`, the same gate
[[auto-refl-empty-block]] runs for its one speculative `refl` — and on failure
report at `e.span` with both types respelled. Convertibility is decidable
here, so there is no "inconclusive" branch to design.

**The caution is cost, and it is why this is not a five-line change.** That
fallback is on every checking path in the elaborator, so a conversion call
there is a conversion call per checked expression, and conversion is the
system's most expensive operation. A round taking this measures — per
CLAUDE.md, this one *does* name performance as part of the point — and the
cheap version is worth costing first: compare only when both types are already
in whnf, or only at the leaf forms (literal, variable) where the inferred type
is free.

## What it assumes from elsewhere

- **[[auto-refl-empty-block]]** (closed) owns the precedent for calling the
  kernel from the elaborator. Assumed here: only that `conv_term` at
  `Layer::Prog` is available and is what a speculative check uses.
- **[[le-diagnostics-print-raw-el]]** owns type display. Assumed here: only
  that printing a type as surface is that issue's job, not this one's.

## Acceptance

`fn d5<A>(xs: List<A>) -> List<A> { 3 }` reports at the `3`, naming both
types, and no longer says `the kernel rejected`. A negative control keeps the
kernel as the judge: a declaration the elaborator accepts and the kernel
refuses still reports as a kernel rejection, because that is the gate working.
And the round records what the added conversion costs on the bench suite.

## Log

- 2026-08-17: Wave L2'/L3 datum (2026-08-17): the round ran three deliberate controls to establish what the language refuses, and all three came back as `the kernel rejected 'f': NotConvertible` with the theorem's own span and nothing else — no arm, no subterm, no side of the equation. The controls were (a) filter_filter with the convoy equation removed, (b) filter_append with the inner motive removed ([[goal-motive-by-scrutinee-abstraction]]'s control), (c) count(2, [2,1,2]) = 3, the negative control now in crates/elab/tests/lib_list_algos.rs. For (c) that message is fine — the theorem is one line. For (a) and (b) the refused thing is one arm of a twenty-line proof, and knowing WHICH arm is the whole content of the diagnosis.
- 2026-08-17: LANDED, and the filed shape changed in two ways that are worth more than the fix.

DESIGN (on this issue; the printing half has the doc).

(1) TWO SITES, not one. The filed cause is the `_ =>` arm of `elab_check_skel`, but the acceptance case -- a numeral at the wrong type -- does not reach it: `ExprKind::Num` has its own checking arm, and `elab_num_check`'s tail discards the inferred type identically once its `Fin` branch declines. Both now call one helper.

(2) RECORDED, NOT RAISED. Raising the mismatch at the expression was tried first, and it loses races it should not enter: it preempted three more specific diagnostics raised further down the same declaration (records.rs's dependent-field injectivity refusal, traits.rs's arity/spelling error, lib_algebra's "`+` has no designation at `List`" note), replacing a message that says what to do with one that says only what disagreed. So the mismatch goes into a per-declaration slot (cleared beside `op_fallback_notes`, first-writer-wins) and is consulted at exactly one place: the kernel gate, when the gate rejects with `NotConvertible`. The kernel is therefore still literally the judge -- nothing is reported that the gate did not reject -- and a better diagnostic downstream still wins, because it is raised in the ordinary way. The operator note travels with either message.

(3) READABLE OR SILENT. The report speaks only when BOTH types spell entirely as surface (`spell_type_clean`, no raw node) and the two spellings DIFFER. The look-alike case is real: `And<...>` against `And<...>`, whose type arguments are the whole difference ([[display-inductive-type-arguments]]), reads as a compiler bug and says less than the gate's own line. Both filters are silence, not error.

MEASUREMENT (the round's point; protocol per docs/frontend-benchmarking.md, `scripts/bench-frontend --no-heavy`, same machine, a git worktree at HEAD as the control): full version, a conversion at every expression reaching the fallback, +2.6% total / +6.5% elab-phase against the control; cheap version, leaves only, +2.2% / +5.7%; and the CONTROL AGAINST ITSELF, re-run, +2.9% / +8.5%. The noise floor is larger than either delta, so the added conversion is not measurable on this suite and cost does not decide. That is why the FULL version landed and the cheap variants the issue proposed -- leaves only, whnf'd types only -- were not worth their narrowing: they buy nothing measurable and cover less. What decided the shape was the message, not the microseconds.

EFFECT: `fn d5<A>(xs: List<A>) -> List<A> { 3 }` now reports at the `3`, "this has type `Nat`, but `List<...>` is expected here". Twelve existing pins moved, all from a bare `NotConvertible` to a stated mismatch, and the new messages are the argument for the round: "this has type `3 = 3`, but `n = n` is expected here" (the tier-0 weakening control, whose own comment says only a test that can tell those apart sees the defect), "this has type `a = b`, but `b = a` is expected here", "this has type `Bool`, but `leb(n, m) = True` is expected here", and two datarepr/obligation clause laws printed in full on both sides.

Tests: crates/elab/tests/check_reports_mismatch.rs (6) -- the literal, a variable, a call, plus three controls: `refl` at a false equation is still a kernel rejection; a mismatch the display cannot state is still a kernel rejection; and an expected type that only CONVERTS (`El(Alias())`, a delta- and beta-step from `Nat`) is still accepted, which is the axis a syntactic check would fail.

RESIDUE: a mismatch whose types do not spell cleanly still arrives as a bare kernel rejection. The look-alike half of that is [[display-inductive-type-arguments]]'s; the rest is the "readable or silent" decision, which owes nothing.
- 2026-08-17: 2026-08-17, post-merge datum for the residue above: the two motive defects filed the same day ([[goal-motive-by-scrutinee-abstraction]], [[nested-match-on-field-binder-motive]]) are NOT localized by this round, verified on the Box repro after merging. Their arms are proved by `refl`, which has its own checking arm and is this round's own control case. That is not a miss — it is the boundary this round drew deliberately — but it means the most expensive diagnosis in the library push, 24 sites across two rounds, still arrives as a bare declaration-span NotConvertible. Whoever takes the motive pair should expect to find it the way both rounds did, with a goal hole.
