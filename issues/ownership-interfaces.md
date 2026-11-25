---
title: Ownership: the interfaces of §21 as modules (total steps, values, the body and its meaning)
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The first package of the real ownership modules: the interfaces of `docs/language/ownership-design.md` §21, written as modules of definitions over which the checker, the two readings and `check_sound` are later built once (§20.6 step 2). §21 is the specification; a definition that cannot be written as §21 states it goes back to the coordinating session and is not adjusted in the module.

## Scope, in order, each landed before the next

1. **The total step model, in place** (§21.1 last bullet, §21.5 probe 1): `steps.hthr`'s `StepModel` and `StepModelLaws` become a total read `at`, a total modification `over`, a Boolean fit of a step to an owner, laws where the step fits and relative to what was read there; `Steps::apart_sound` re-proved over it.
2. **Values** (§21.1): `Shape`, the type environment and `El`, `Struct` (sharing class; opaque, record, sequence) with each kind's laws, `Dyn`, and `Dyn`'s instance of the total step model from the structures' laws alone. Instances by hand: a user record; `List<A>`, `[A; n]` and `Bytes(n)` as sequences each spelling its accessor's bound; a word type that is not `Nat`. Probes: reads under each instance's bound are the source's term by conversion; `value_steps.hthr`'s customers restated at `Dyn`.
3. **The body and its meaning** (§21.2, §21.3 first two bullets): `Place`, `Stmt`, `Body` (`Ret`, `Yield`, `Do`, `Join`, `Jump`), `Func`, one environment of `Dyn`s, the meaning in continuation form over a world of callee meanings; the pins of `coded_tests.hthr` restated, §21.5 probe 3, a `while` with `decreases` and a `for`.
4. **§21.5 probe 2**: one environment against two, at doubling sizes, with a word type other than `Nat`.
5. **The remaining interfaces as definitions only** (§21.3 third bullet, §21.4): level 2's heap, objects with holes, canonical references, the run's outcome; the residual kinds, the verdict's tree, and the statements of a function's safety and of `check_sound` as `Type`-valued definitions, each stated at one small function.
6. **Retire what this replaces**: `value_steps.hthr`, `coded.hthr` and their tests when covered; `PathLawsOn` and `KeepsFit` from `lib/std/machine/path.hthr` if nothing else uses them.

`call_check.hthr` and `place_check.hthr` are not edited.

## What it assumes from elsewhere

- **[[ownership-coded-values]]**: the sixth experiment, whose result (§20.5, §18.4 item 4) fixes the value sort.
- **[[ownership-join-chain-cost]]**: the one known non-linear shape.
- **[[ownership-write-bounds]]**, **[[ownership-pin-after-join]]**, **[[ownership-world-depth-zero-postconditions]]**: requirements on what is built over these interfaces.

## Done when

Items 1 to 6 have landed with `scripts/test --pr` green, or the package stopped after a landed item with what remains stated; `ownership-design.md` has a §22 "The interfaces as built".

## Log

- 2026-11-25: **Item 1 landed: the total step model, in place** (`lib/lang/ownership/steps.hthr`).
  - `StepModel<S> { at, over, fits, like }`: a total read and a total modification per selection, a Boolean "this step fits this owner", and `like(sel, read, written)`, the relative fit (§21.1's "relative to what was read there": for a typed value its code, for a window its length). §21.1 lists three components; the laws need the fourth.
  - `StepModelLaws`: `still` (a step that does not fit modifies nothing); where it fits, `over_at` (a modification whose result is like what was read is read back), `over_over` (two are one), `over_read` (a modification reads only what was read); `like_refl`; `keeps` (every modification keeps an owner like what it was like); `apart` (selections apart are `ApartAt`: a modification through either leaves the other's read, and the two commute, for any functions).
  - Not a law: "a step that does not fit reads its owner back". The soundness never reads an unfit step, and at `Dyn` it is false beside a write (item 2's log).
  - `Steps::at`, `Steps::over` compose the steps; `Steps::apart_sound` gives `Steps::Apart(m, ws, xs, ys)`, re-proved by `ApartAt::under` down the common prefix (a case split on the step's fit: where it fits, `over_at`/`over_over`/`over_read` with `keeps`; where not, `still`) and `ApartAt::then_both` after the difference. No `Path`, `PathLawsOn` or `KeepsFit` is used.
  - The path-based model `value_steps.hthr` and `coded.hthr` were built on moved into `value_steps.hthr` as `PathModel` (renamed, verbatim), until both retire in item 6.
  - `scripts/test --pr`: `== suite: 3518 passed, 0 failed, 2 ignored ==`.
- 2026-11-25: **Item 2 landed: values** (`shape.hthr`, `sequences.hthr`; probes `shape_tests.hthr`, `sequences_tests.hthr`), with the coordinator's decisions A (the pad) and B (the index) applied.
  - **The index (B, a change to item 1)**: `Sel`'s indices are `Ix`, a number or a word at a width (the variable's own value, `Dyn::ix`). `Sel::apart` and the obligations read them through `toNat` (`Atom::ix_nat`, `Atom::spans_ix`), and an instance reads them at its own accessor's type. The legacy path model reads numbers through `Ix::of_nats`.
  - **Codes**: `Shape { SWord(Width), SNamed(k) }`, `Width { WNat, WBits(n) }` (`u64` is `SWord(WBits(64))`), `El`, `Dyn`, `Dyn::back`, `Dyn::get` (an `Option`, for callees), and `Dyn::ix`/`Dyn::index` for indices.
  - **Structures**: `Struct { sharing, pad, kind }`, with `Sharing { Plain, Object, Linear }` and `Kind { Opaque, Record(fields), Sequence(Seq) }`.
    - `Seq` holds: the element's shape, its length, a total read and update at an `Ix`, `inside`, the accessor's proposition, `make` (n copies, for the body's `fresh`), and windows (`Win`: their shape, length, read, guarded update, `inside`, proposition).
    - Laws: `RecordLaws`, `SeqLaws`, `WinLaws` (relative to the length read) and `WinLen` (a window's length as the environment reads it).
  - **The model**: each step at a code is a `Part` or none.
    - A step with no part reads the word 0, not the owner. An owner-back read makes the decider unsound beside a write: `[SField(2)]` and `[SField(0)]` on a record of two fields.
    - `Dyn::like` is code equality, plus length equality through a window.
    - `Dyn::model_laws` derives the model's laws from `StrsLaws` alone.
  - **Instances (A)**, each reading through its type's own total accessor with that accessor's pad:
    - `List<A>` takes its pad as a parameter. Its windows are lists (`Seq::list_win`, the window's type given by `to`/`of`). It has 9 window laws, proved through `List::ext_nth`.
    - `[A; n]` takes its pad as a parameter (`Vec::at`, `Vec::put`).
    - `Bytes(n)` reads at a `u64` index (`Bytes::at`, `Bytes::put`). Its laws need unique identity proofs at `Nat` for the length proof: `Nat::uip`, Hedberg's argument from `Nat::dec`, in the module ([[uip-from-decidable-equality]] would move it to the library).
    - No real type was excluded for want of a pad in this package.
  - **Probes**, all by `refl`:
    - `ps[i].x` over a list of records.
    - `v[i]` over `[u64; 16]`, which is `Vec::at`.
    - `s[i]` over `Bytes(n)`, which is `Bytes::at` at the word. A number index reads 0.
    - Writes against the source's update and `Bytes::put`.
    - A window of a list.
    - The decider's customers at `Dyn`, with refused controls and `¬` theorems at values:
      - split_at_mut, with the left half kept after the right is written.
      - An element held while another is stored.
      - A window held while an element past it is stored.
      - Two fields of an element, and one field of two elements.
      - Two bytes at `u64` indices.
  - Keys and variants (`value_steps.hthr`'s last two customers) are outside the first fragment (§21.1) and are not restated.
  - **Retired**: `value_steps.hthr` and its tests. The legacy path model moved to `coded.hthr` until item 3 retires it.
  - `scripts/test --pr`: `== suite: 3518 passed, 0 failed, 2 ignored ==`.
- 2026-11-25: **Items 3, 5 and 6 landed, item 3 reworked to the coordinator's decisions** (`body.hthr`, `level2.hthr`, `verdict.hthr`; probes `body_tests.hthr`, `interfaces_tests.hthr`; §22 updated).
  - **The meaning is total.** The optional meaning is taken out. A join's codes come from its yes arm, and the no arm is cast with the yes value as fallback. A callee is `List<Dyn> → List<Dyn>`, an ill-coded call answers no results, and a missing result binds the word-zero `Dyn`. Every pin is `mean(…) = the source's term`.
  - **The code check** `Func::coded` refuses an ill-coded join, a call whose argument codes are not its signature's, and a word primitive or test at a non-word. Each has a `= False` probe beside an accepted twin, and each junk meaning is pinned (`join_ill_coded_junk`, `call_ill_junk`, `ill_word_junk`). `CheckRefusesIllCoded` ties a checker to it.
  - **The environment** is `Var { Arg(i), Loc(j) }`, reached only through `Env::push`/`Env::get` and their laws. The long-lived local is filed as [[ownership-long-lived-local]] with its measured shape. Item 4 rerun on this environment: unchanged, since the object is a local and sinks (§22.3).
  - `guarded_whole` now pins its whole answer. `early` (an inner return) still pins only through a word continuation.
  - **D's sequence twin**: `past_end_apart`, `past_end_reads_pad`, `past_end_kept` (`sequences_tests`).
  - **Retired (item 6)**: `coded.hthr` and its probes, and `PathLawsOn`/`KeepsFit` from `lib/std/machine/path.hthr`.
  - `scripts/test --pr` at 8880e3ca: `== suite: 3518 passed, 0 failed, 2 ignored ==`.
