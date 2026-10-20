# Roadmap: areas and their importance

Started 2026-10-20 from Minus's list of the project's core areas. This file
owns three things: **the list of areas**, **their importance order**, and
**the milestones** that effort is allocated toward. Everything else is owned
by an issue or a design doc, and this file links to it rather than restating
it (`issues/README.md`, rule 1).

**The importance order below is a proposal, not a decision.** It was drafted
by a Claude round from the state of the tracker, with the reasoning written
next to it, so that Minus can move areas up or down by editing one table.
Once Minus has edited it, delete this paragraph.

## How the tracker uses this file

- Every open issue names its **area** in its frontmatter (`area: tactics`),
  and may name the **milestones** it serves (`milestone: [tac-in-heather]`).
  An area is the one place the issue's work lands; labels stay as free-form
  topics (`reals`, `omega`, `x86`) and can cross areas.
- `scripts/issue areas` prints the areas in rank order with their open and
  closed counts and each milestone's open issues. `scripts/issue list --area
  A` / `--milestone M` filter; `scripts/issue tag <slug>… --area A
  [--milestone M,N]` retags without touching `updated:`. The web viewer's
  **Areas** tab shows the same order, with each area's direction and
  milestones.
- `scripts/issue check` reads the two tables below. An unknown area or
  milestone in an issue is an error; open issues with no area are one
  warning with a count.
- The tables are read by the script, between the HTML comment markers. Keep
  one row per line and the column order as it is.

### What the tiers mean

- **focus**: most rounds go here. A focus area that is blocked pulls work
  from an enabling area rather than waiting.
- **steady**: worked on continuously, at a lower share, usually because a
  focus area is a customer.
- **next**: starts once a named milestone lands. Until then it gets design
  notes and a survey, not implementation.
- **horizon**: tracked so its needs shape decisions now. No rounds yet.
- **enabling**: the language, kernel and tooling everything else stands on.
  Not ranked against the directions. Its work is *pulled* by a direction's
  milestone or blocker, and an enabling issue with no puller waits.

## Areas

<!-- areas -->
| rank | area | tier | name | direction |
|---|---|---|---|---|
| 1 | `heather-in-heather` | focus | Heather in Heather | Write real programs, compile them natively with proofs, and move the compiler's logic out of Rust into Heather, toward dogfooded optimisation passes. |
| 2 | `tactics` | focus | Tactics | Anything systematic is closed by some tactic: cheap specialised tactics, a few high-value general ones, and tactics written in Heather. |
| 3 | `interaction-trees` | focus | Interaction trees | Reason about effectful programs intuitively: interaction trees over container events, meeting the native program logic. |
| 4 | `mathematics` | steady | Mathematics | Fundamental classes and APIs first, then reals, floating point, and the fields Minus cares about (asymptotics, measure, locales, combinatorics). |
| 5 | `constructive` | steady | Constructive mathematics | Make constructive mathematics natural: ask for the specific property a proof needs, which choice could supply but specific types supply without it. |
| 6 | `heather-in-lean-coq` | next | Heather in Lean/Coq | Translate Heather proofs and their dependencies into Lean or Coq so they can be checked outside Heather. |
| 7 | `machine-learning` | next | Machine learning | Bring Minus's Lean ML formalization (Wick) into Heather, improved, as a target for both the mathematical and the programming tooling. |
| 8 | `gpu` | horizon | GPU | A Triton-like kernel language, proved correct and efficient against a GPU model, reusing the floating point, numerics and ML proofs. |
| 9 | `rust-in-heather` | horizon | Rust in Heather | Translate Rust code into Heather to prove properties about it. |
| 10 | `lean-in-heather` | horizon | Lean in Heather | An autotranslator from Lean to Heather over a formal model of Lean, so Lean proofs can be cited (not a first-class Lean or mathlib port). |
| — | `language` | enabling | Language and elaborator | The surface language and its elaborator: syntax, inference, classes, inductives, modules, diagnostics, lints, editors. |
| — | `kernel` | enabling | Kernel and type theory | The kernel, its type theory (DeLaM and extensions), the metatheory, and checking cost. |
| — | `infrastructure` | enabling | Infrastructure | The test suite, caches and module images, performance measurement, and the CLI around them. |
<!-- /areas -->

## Milestones

A milestone is a usable result, stated so that someone can tell when it has
happened. Issues serve one through `milestone:`; the list of issues is
`scripts/issue list --milestone <id>`, not a copy here.

<!-- milestones -->
| milestone | area | status | done when |
|---|---|---|---|
| `hih-program-logic` | heather-in-heather | open | Native code is stated and proved through one program logic (one effectful code tree, rules proved once) instead of the five "this code runs" shapes, and the assembly layer is redesigned on it. |
| `hih-memory` | heather-in-heather | open | A native program allocates on the heap, under a byte-addressed memory model whose certificates bound and track the allocation. |
| `hih-passes` | heather-in-heather | open | A compiler pass (certificate emission or an optimisation) is a Heather metaprogram with its proof, and Rust only moves its output around. |
| `hih-self` | heather-in-heather | open | A first component of Heather itself (candidate: the lexer, on the parser library) is written in Heather and compiled natively. |
| `tac-in-heather` | tactics | open | A tactic is written in Heather through a host elaboration interface, and one tactic that lives in Rust today has a Heather counterpart. |
| `tac-general` | tactics | open | A general-purpose rewriting and congruence-closure tactic (grind-like) closes the routine goals that today need hand `trans`/`cong` towers, and hands back its search state when it fails. |
| `tac-arith` | tactics | open | Linear integer arithmetic is complete and certified (CutSat), and polynomial inequalities go through the ring normaliser. |
| `it-library` | interaction-trees | open | The container-event interaction-tree library exists: bind, iter, trace refinement, and the bridge to `converges`/`fuel_monotone`. |
| `it-native` | interaction-trees | open | A native program's theorem says its run refines an interaction tree. |
| `math-classes` | mathematics | open | The algebra and order class hierarchy (semiring to ordered field, lattices) is settled, with a documented API that clients use without restating laws. |
| `math-reals` | mathematics | open | Reals have their completeness interfaces and basic analysis (sequences, limits, continuity) on top of the regular Cauchy reals. |
| `math-float` | mathematics | open | IEEE-style binary floating point, rounding and error bounds are proved against the reals, ported from Minus's Lean formalization. |
| `math-metatheory` | mathematics | open | A result from heather-coq (for example a small logical-relation proof) is restated and proved in Heather. |
| `cons-specific-choice` | constructive | open | A library convention, with inference behind it, for asking for the specific property instead of choice, with per-type instances that discharge it without an axiom. |
| `export-fragment` | heather-in-lean-coq | open | A closed, layer-free fragment of the library (Nat and List lemmas) is translated to Coq or Lean and rechecked there. |
| `ml-survey` | machine-learning | open | Wick is surveyed: what transfers, what must be redone better, and the mathematics and tooling it needs from Heather. |
| `gpu-model` | gpu | open | A design note fixes the GPU execution model and the kernel-language level (tile IR, Triton-like) to prove against, with what it needs from the other areas. |
| `rust-design` | rust-in-heather | open | A design note fixes the Rust subset, the semantics source (MIR or surface), and what the translation needs from `hih-memory` and `it-library`. |
| `lean-fragment` | lean-in-heather | open | A design note says which fragment of Lean translates into Heather and how impredicative `Prop` is handled. |
<!-- /milestones -->

## Why this order (the proposal)

Three things decided the ranks: what Minus said leads, what unblocks the most
other areas, and what is ready to be worked on now.

1. **Heather in Heather leads** because it is the project's stated goal (fast,
   broad, certified native code) and because it compounds: once passes are
   Heather metaprograms, every later optimisation is dogfooded. It also
   decides what "a program" means for interaction trees, Rust and GPU.
2. **Tactics are second** because they multiply every other area,
   mathematics included, and because with generated code a specialised
   tactic is cheap. The step that matters most is *writing tactics in
   Heather* (`tac-in-heather`). It shares its meta-layer interface with
   `hih-passes`, so the two focus areas pull the same enabling work.
3. **Interaction trees are focus despite being early** because the native
   program logic (`hih-program-logic`) is meant to be stated so that ITree
   refinement comes out as a lemma, not a re-founding. Designing them late
   would mean redoing that logic. The library itself waits on surface
   inductives with function-typed fields (see its section).
4. **Mathematics is steady**, not focus: it runs all the time and is the
   main customer of tactics, but most of its fields are worth more after the
   class hierarchy settles. Floating point is ranked early inside it,
   because GPU and ML both need it and Minus already has a Lean version.
5. **Constructive mathematics is a principle more than a workload.** It is
   carried out inside mathematics and the language (assumption profiles,
   evidence search). It keeps its own area so its milestone has an owner.
6. **Heather in Lean/Coq comes before the other translations** because
   exporting is the easy direction. Heather is predicative and has no K, so
   a layer-free proof asks less of its target than Lean or Coq provide. It
   buys an external trust story early.
7. **ML is next, GPU after it.** ML needs mathematics (linear algebra,
   analysis, probability) and floating point, and a survey can start now.
   GPU needs those *and* a mature native story.
8. **Rust in Heather and Lean in Heather are horizon.** Rust needs a memory
   model and a program logic (`hih-memory`, `hih-program-logic`,
   `it-library`). Lean import meets impredicative `Prop`, which a predicative
   Heather cannot host directly, so its first step is the design note
   (`lean-fragment`), not code.

## The areas

### Heather in Heather (`heather-in-heather`)

**Goal.** Heather should give a good programming-language experience, have
lots of optimisation passes, and stop putting logic in Rust where Heather can
hold it. Parts of Heather itself are reimplemented in Heather so that
specific optimisations are dogfooded. That needs more data-structure work,
and above all a way to track allocations.

**Where it stands.**
- The native x86-64 path works end to end: reflect to FunctionIR, select and
  lay out in Rust, emit a certificate as Heather source, and check it in the
  kernel. It produces static ELF executables whose runs are stated against a
  Linux trace model (`docs/native-compiler-architecture-review.md`,
  `docs/native-architecture-review.md`). `wc` as a command and stream filters
  (`tr`) are the clients (`docs/native-wc-command-design.md`,
  `docs/native-stream-filter-design.md`).
- Layout and jump computation moved from Rust into Heather in 2026-10,
  proved by evaluation. Programs are stated over Runs, Straight and
  stretches (`docs/native-runs-design.md`, `docs/native-straight-runs-design.md`).
  The last list layouts are parked as uniformity work
  ([list-layouts-onto-labels](../issues/list-layouts-onto-labels.md)).
- Still in Rust: reflection, instruction selection, register placement, the
  encoder, certificate emission (`crates/elab/src/heather_emit.rs`) and the
  declaration generators. They are untrusted, but they are Rust.
- Data structures for programs: List, Tree, bounded lists, finite sets,
  strings, and a certified parser library (`lib/std/parser/`). Runtime
  representation is not yet separated from the kernel's
  ([datarepr-separation](../issues/datarepr-separation.md)).

**Blockers.**
- *The assembly layer.* Code "runs" in five shapes, and nothing above a
  fetched step holds a store or a syscall
  ([native-one-program-logic](../issues/native-one-program-logic.md),
  [native-stack-refactor](../issues/native-stack-refactor.md),
  [x86-64-machine-model](../issues/x86-64-machine-model.md)). This is the
  "kinda eugh" Minus named, and it should be redesigned before more programs
  are written on it.
- *Memory and allocation.* There is no heap model and no allocation
  accounting ([memory-bound-certificates](../issues/memory-bound-certificates.md),
  [byte-memory-access-model](../issues/byte-memory-access-model.md),
  [ownership-discipline-over-code](../issues/ownership-discipline-over-code.md)).
- *A meta layer that can host passes.* Moving emission or a pass into
  Heather needs the in-language routes
  ([in-language-certificate-emission](../issues/in-language-certificate-emission.md),
  [generators-in-the-language](../issues/generators-in-the-language.md)) and
  the same host interface tactics need
  ([host-elaboration-interface](../issues/host-elaboration-interface.md)).
- *Certificate cost* grows with code size, and code quality is what makes
  more code ([x86-certificate-per-declaration-constant](../issues/x86-certificate-per-declaration-constant.md),
  [function-ir-x86-proof-scaling](../issues/function-ir-x86-proof-scaling.md)).

**Milestones.** `hih-program-logic` first, since every later program is
written on it, then `hih-memory`. `hih-passes` can proceed in parallel
because it is meta-layer work. `hih-self` comes after both
([self-hosting-first-component](../issues/self-hosting-first-component.md)).

### Tactics (`tactics`)

**Goal.** Anything systematic should be solved by some tactic. That means
more varied tactics: specialised ones are cheap with generated code, and a
few general-purpose ones are worth real design.

**Where it stands.** Certifying tactics exist for Presburger arithmetic
(`omega`, with CutSat), bit-vectors (`bv_omega`), commutative rings (`ring`),
case splitting (`split_all`), positivity, `decide`, relational congruence
(`rel_cong`), and `calc` chains (`docs/certifying-arithmetic-automation-design.md`,
`docs/ring-normalization-design.md`, `docs/relational-context-round.md`).
All of them are written in Rust in `crates/elab`. Metaprograms with
quote/splice exist, but there is no interface yet for writing a tactic in
Heather.

**Blockers.** The host elaboration interface and a checked construction API
([host-elaboration-interface](../issues/host-elaboration-interface.md),
[heather-checked-construction-api](../issues/heather-checked-construction-api.md),
[elabcode-abstraction-layer](../issues/elabcode-abstraction-layer.md)). There
is no general rewriting tactic, so routine equalities are hand `trans`/`cong`
towers ([grind-port](../issues/grind-port.md),
[monoid-normalisation](../issues/monoid-normalisation.md),
[equation-rewrite-in-goal](../issues/equation-rewrite-in-goal.md)).

**Milestones.** `tac-in-heather`, then `tac-general` (written in Heather if
the first has landed), with `tac-arith` continuing as arithmetic clients
need it.

### Interaction trees (`interaction-trees`)

**Goal.** Work with programs intuitively. heather-coq has evidence that
interaction trees will work. What is missing is more design, integration
with Heather, and the library itself.

**Where it stands.** The fit investigation is written
(`docs/interaction-trees-fit.md`). It proposes container events
(`Cmd`, `Resp`) over trees cut at fuel, with no kernel coinduction. Its key
conjecture was answered yes in heather-coq: depth-indexed bisimilarity
coincides with the greatest fixed point over container events
([interaction-trees-container-model](../issues/interaction-trees-container-model.md)).
The effects story (uniqueness threading first, interaction trees for trace
semantics) is open in [effects-direction](../issues/effects-direction.md).

**Blockers.** The surface cannot write a tree yet: a continuation field
`k: Resp(c) -> Tree` is a recursive function-typed field, which needs the
tier-2 (W-lowered) inductive generator
([inductive-compiler](../issues/inductive-compiler.md)). The native program
logic has to be designed to meet it
([native-one-program-logic](../issues/native-one-program-logic.md)).

**Milestones.** `it-library`, then `it-native` together with
`hih-program-logic`.

### Mathematics (`mathematics`)

**Goal.** Mathematics good enough to duplicate the heather-coq work in
Heather (keeping heather-coq outside it is still valuable), and to make
floating point proofs easy. Beyond that: reals in depth, Minus's own interest
in asymptotics, perturbation theory and transseries as a stronger basis than
filters or undergraduate calculus, combinatorics with the typing made
reasonable, measure and probability theory, locale theory, decidability,
and good fundamental classes and APIs, with custom language extension points
where a part is important enough.

**Where it stands.** In `lib/std`: Nat, Int, Rat with a complete order
theory, regular Cauchy reals (sum, product, inverse, order, Bishop bridge),
relation-indexed algebra up to semiring and ring layers, orders, setoids and
relations, finite sets with list and tree backends, bit-vectors, and
`x⁻¹`/`xⁿ` notation without junk values (`docs/regular-cauchy-reals-round.md`,
`docs/creal-*-round.md`, `docs/rational-order-round.md`). Nothing yet for
measure, probability, combinatorics, asymptotics, locales or floating point.
Open design for those that have issues:
[frame-and-locale-foundations](../issues/frame-and-locale-foundations.md),
[localic-real-numbers](../issues/localic-real-numbers.md),
[real-completeness-interfaces](../issues/real-completeness-interfaces.md),
[decidable-relations-and-comparison](../issues/decidable-relations-and-comparison.md).

**Order inside the area (proposal).** (1) Classes and APIs (`math-classes`),
because every field after it states itself in them. (2) Reals and floating
point (`math-reals`, `math-float`:
[floating-point-formalization](../issues/floating-point-formalization.md)). (3) Decidability and combinatorics, the
fields where tactics pay most. (4) Measure and probability, which ML needs.
Locales come in here too, since valuations on locales are one constructive
road to measure. (5) Asymptotics and transseries, on the reals and orders.
(6) The metatheory needed to restate heather-coq (`math-metatheory`):
syntax with binders, substitution lemmas, logical relations. The IWf former
landing in the kernel (`docs/iwf-former-design.md`) is what makes its
inductive families writable.

### Constructive mathematics (`constructive`)

**Goal.** See how far constructive mathematics can be made natural. Choice
and similar statements are assumed less often. Instead a statement takes the
*specific* property it needs. Choice could always supply that property, but
some specific types supply it without choice.

**Where it stands.** The kernel is predicative and has no axioms by default
(axioms are explicit, with provenance: `docs/axiom-provenance-design.md`).
The reals are constructive, with apartness and a Bishop bridge. The pieces
the principle needs already exist in some form: assumption scopes and
profiles ([implicit-logical-assumptions](../issues/implicit-logical-assumptions.md)),
searched evidence (`docs/positivity-evidence-design.md`), and `Decide`
instances. What is missing is the convention that ties them together
([default-inhabited-nonempty](../issues/default-inhabited-nonempty.md),
[apartness-structures](../issues/apartness-structures.md),
[real-number-foundation](../issues/real-number-foundation.md)).

**Milestone.** `cons-specific-choice`.

### Heather in Lean/Coq (`heather-in-lean-coq`)

**Goal.** Translate Heather proofs and their dependencies into Lean or Coq so
they can be verified outside Heather. The foundations differ, but much of
the difference is in how things are done, or can be handled by replacing
equality with another symbol. Proving which fragment can be trusted across
the two is further off and needs more mathematical maturity in Heather.

**Where it stands.** Nothing is translated. heather-coq formalizes Heather's
*metatheory* (logical relation, decidable conversion, the extension rules),
which is not proof export, but it is the reference for what each kernel rule
means. The likely first fragment is proofs that never use the DeLaM code
layers or `sEq`.

**Milestone.** `export-fragment`
([heather-proof-export](../issues/heather-proof-export.md)).

### Machine learning (`machine-learning`)

**Goal.** Look over Wick, Minus's Lean project that formalizes a good amount
of machine learning, and bring it into Heather. It needs work to become
fundamentally better, and it is a good target for both mathematical and
programming tooling.

**Where it stands.** Nothing in Heather yet. It depends on `math-classes`,
`math-reals`, `math-float`, and later on measure and probability.

**Milestone.** `ml-survey` ([wick-survey](../issues/wick-survey.md)).

### GPU (`gpu`)

**Goal.** Design or adapt a Triton-like setup (or something better) whose
kernels are proved correct and efficient against a model of the GPU, as is
being done for CPU code. That brings the floating point formalization,
numerics proofs and ML proofs to automated proofs of kernel accuracy and to
optimisation.

**Where it stands.** Nothing yet. It needs `hih-program-logic` (or its GPU
analogue), `math-float`, and the ML mathematics.

**Milestone.** `gpu-model`
([gpu-kernel-model-design](../issues/gpu-kernel-model-design.md)).

### Rust in Heather (`rust-in-heather`)

**Goal.** Translate Rust code into Heather to prove properties about it.

**Where it stands.** Nothing yet. Prior art to read before designing:
functional translations such as Aeneas (Rust to Lean through MIR), and
separation-logic approaches. It needs `hih-memory` and a program logic.

**Milestone.** `rust-design`
([rust-translation-design](../issues/rust-translation-design.md)).

### Lean in Heather (`lean-in-heather`)

**Goal.** Eventually, an autotranslator from Lean to Heather (and possibly
back) over a formal model of Lean, in the style of the recent con-leche
work, so that Lean proofs can be used. It is not first-class Lean support
and not a mathlib import. The point is that Heather can say it is a
high-value language.

**Where it stands.** Nothing yet. The foundational gap is impredicative,
definitionally proof-irrelevant `Prop` against Heather's predicative kernel.
Which fragment translates, and through what model, is the first question.

**Milestone.** `lean-fragment`
([lean-translation-fragment](../issues/lean-translation-fragment.md)).

### Enabling areas (`language`, `kernel`, `infrastructure`)

Most open issues live here: the elaborator, surface syntax, classes,
inductives, diagnostics and lints (`language`); the kernel, DeLaM extensions,
metatheory and conversion cost (`kernel`); the test suite, module images,
caches and perf tooling (`infrastructure`). They keep their own roadmap
issues ([frontend-roadmap](../issues/frontend-roadmap.md),
[lint-roadmap](../issues/lint-roadmap.md),
[perf-dashboard](../issues/perf-dashboard.md)). When a direction's milestone
needs one of their issues, the issue names that milestone. That is how an
enabling issue shows it has a puller.

## Changing this file

- Reordering areas or changing a tier is a decision Minus makes. Record it
  as a one-line entry in the log below, with the reason.
- A new area needs a row, a section, and at least one milestone.
- When a milestone lands, set its status to `done`, link the PR in the log,
  and leave the row so the history stays readable.

## Log

- 2026-10-20: Areas, tiers and milestones proposed from Minus's list. The open
  issues were tagged by area, and milestones were set only where an issue
  clearly serves one. Closed issues are left untagged.
