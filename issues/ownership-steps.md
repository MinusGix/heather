---
title: Paths as data: steps, their denotation, and an apartness decider
status: closed
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Package 2 of `docs/language/ownership-design.md` §16: paths as data. The checker (§15.3) decides overlap of two places on their steps and emits a residual where it cannot; level 2's references (§15.5) are a block and steps. Today a path is a pair of functions (`lib/std/machine/path.hthr`), which has no decidable equality, so `PathSame` and "a carrier of paths cannot decide its validity" exist to work around it.

## Scope

- **`Steps`**: a list of steps, each a field, an element at an index, a window, a key, or an enum's variant, over atoms (a literal or a variable), so a place is a root and steps.
- **`denote`**: steps to a `Path`, by `Path::then` over the per-step paths the library has (`Path::elem`, `Path::window`, `Part::path`, `Store::key_path`, `Path::entry`).
- **`Steps::apart`**: a decider on two step lists (the first differing step apart), answering yes, no, or a residual over the atoms where an index is open. Sound against `Apart` by `Apart::under`, `Apart::then_both`, `PathIn::apart_sound`, `keys_apart`; say where it is complete.
- **Customers**: `split_at_mut`, an element held while another is stored, and two fields of one record, each re-derived by evaluating the decider.
- What `PathSame` and `Footprint` become once steps exist (the design review calls `Footprint` redundant beside `Held`); do not delete them here, say what a later round should do.

## Done when

The module and its probes pass the library gate, the decider is proved sound and its completeness stated, and the three customers are theorems by evaluation with a `¬` or a refusal for each overlapping case.

## What it assumes from elsewhere

- **[[ownership-library-join]]** (closed) gives keys as path steps and fields with footprints.
- **[[ownership-checker-call-and-write-view]]** is extending the checker's experiment; this issue adds modules beside it (`atom`, `steps`, `value_steps`) and moves only `Atom` out of `place_check.hthr`.

## Log

- 2026-11-25: Built, on branch `claude/ownership-steps`.

  **Modules.** `lib/lang/ownership/atom.hthr` (new, shared): `Atom` moved out of `place_check.hthr` with `word`, `val`, `bound`, `closed`, `closed_val` (place_check now imports it; its probes pass unchanged but for one `import atom`), and `Obligation`: `Spans(lo1, n1, lo2, n2)` apart or `Keys(i1, g1, i2, g2)` different, with `verdict`, `All`, and `settle` (no / yes owing nothing / yes owing it). The checker's `Residual(lo, n, i)` is `Spans(lo, n, i, Lit(1))`, verdicts equal by `refl` (`residual_is_spans`). `lib/lang/ownership/steps.hthr` (new): `Step` (`SField(i)`, `SElem(a)`, `SWindow(lo, n)`, `SKey(index, gen)`, `SVariant(c)`), `Sel` (a step with its atoms read), `StepModel<S>`, `StepModelLaws`, `Steps::denote`, `Step::apart`, `Steps::apart`. `lib/lang/ownership/value_steps.hthr` (new): the model. `path.hthr` gains, additively, `PathLawsOn`, `Path::KeepsFit`, `PathLaws::on`, `Path::then_laws_on`, `Path::then_keeps_fit`, `Apart::under_on`.

  **Typing discipline: untyped steps, denoted through a model in one value type.** A typed step indexed by source and target is an inductive family indexed by `Type`, a universe above what the kernel evaluates cheaply (Tarski universes; no data quantifies over `Type` in the library), and a chain of them needs an existential over the intermediate type. A shape universe with `List<Val>` inside is a nested inductive, which the elaborator refuses (`mutual-inductive-design.md` §1). So steps are plain data the decider reads with `same` and spans, and their meaning is a `StepModel<S>`: a path in `S` per selection, with a step that does not fit the value reading nothing. Soundness is proved once over any model with `StepModelLaws` (each step lawful where what it writes fits, every write keeping every step's fit, selections apart giving `Apart`). The model built is level 2's universe: `Val` = word, sequence, record, variant, store, a mutual group with `Vals` and `VSlots`, carried to `List<Val>` and `Store<Val>` by lawful steps so that each step is the library's path after one step in (`Path::elem`, `Path::window` then the vector as a sequence, `Store::key_path`). The one cost of the untyped universe: a window's value is a sequence of its length, and a write of anything else writes nothing, so it is lawful only where the written value fits; hence `PathLawsOn` and `Apart::under_on`, and the descent through a common window prefix needs every step's write to keep a sequence's length (`Val::keeps`).

  **Decider.** `Steps::apart(xs, ys)` walks the common prefix (equal spellings, `Step::same`, which equal open atoms satisfy) and compares the first difference: `None` where one list is a prefix of the other, the first difference overlaps at literals, or two kinds meet; `Some(Nil)`; `Some([o])` where an atom is open. It reads no value and no word, so a verdict is closed data checked by `refl`. **Sound**: `Steps::apart_sound` by `Apart::under_on` down the prefix and `Apart::then_both` after the difference; the model's step-pair facts are `PathIn::apart_sound` under the step into a sequence or record, `Store::keys_apart_sound` under the step into a store, and `Val::tags_apart` for variants. **Complete**: on closed steps it owes nothing (`Steps::apart_closed`); two lists first differing at closed steps whose selections are apart are found apart (`Steps::apart_at_difference`, `Step::apart_complete`); each kind of refusal has a `¬Apart` at a value (`value_steps_tests`). Incomplete after an open index followed by more steps, between two kinds, and between steps never valid together: [[steps-decider-completeness]].

  **Customers, by evaluation** (`value_steps.hthr`): `Val::split_apart` (verdict by `refl`, the owed `Span(0, k)` apart from `Span(k, m)` by `omega`), `Val::split_apart_under` (the same under a common field), `Val::split_closed`; `Val::elems_apart`, `Val::hold_while_store`, `Val::hold_window_store` (§15.3's `xs[0..8]` beside `xs[9]`, nothing owed); `Val::fields_apart`, `Val::nested_fields_apart`, `Val::variants_apart`, `Val::keys_apart`. Controls (`lib/_tests/lang/ownership/value_steps_tests.hthr`): overlapping windows, a split whose owed fact fails at the words, the same element, a field and a part of it, the same key, a variant and its payload, each a `¬Apart` by evaluation; `split_writes` reads the two halves written back as the whole. Checking the model module takes a few seconds.

  **`PathSame` and `Footprint` once steps exist** (not deleted here): `PathSame` stays only as regrouping of a denotation; `KeyIn`'s shape-recording goes to steps; `Footprint` is replaced by steps and place states at level 2 and `Held` at level 3. [[paths-as-steps-retire-workarounds]]. A byte-level model (`Part::path`, `Path::entry`) for placement: [[steps-byte-model]].

  **Elaborator notes.** A `match` on a member of a mutual group with an explicit `as` motive is refused ("cannot set the rest of its mutual group aside"); the inferred motive works, so the model's proofs match on `Val` without `as`. A member theorem `VSlots::of_list` recursing on `VSlots` could not resolve `VSlots::of` in this module ("qualified by `VSlots`, which is neither…"); renamed to `slots_of_list`. A two-type reduction did not reproduce it, so nothing is filed.
- 2026-11-25: Verified: `scripts/test --pr` — `== suite: 3517 passed, 0 failed, 2 ignored ==`. Done-when met; residue filed as [[steps-decider-completeness]], [[steps-byte-model]], [[paths-as-steps-retire-workarounds]]. Closing.
