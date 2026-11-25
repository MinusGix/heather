# Roadmap: areas and their importance

Started 2026-10-20 from Minus's list of the project's core areas. This file
owns four things: **the list of areas**, **their priority**, **the milestones**
(and submilestones) that effort is allocated toward, and **the design
principles** that cut across areas. Everything else is owned by an issue or a
design doc, and this file links to it rather than restating it
(`issues/README.md`, rule 1).

**Priority is not a sequence.** The numbers say where effort goes when it has
to be split, not what must finish before what starts. The unit of work is a
milestone, or a submilestone of one: pick a milestone, fill it out, land it.
Because the areas are mostly disjoint in code, several of them can be worked
at once by separate agents (see [Parallel lanes](#parallel-lanes)). Minus
reviewed the first draft on 2026-10-20; changes since are in the log.

## How the tracker uses this file

- Every open issue names its **area** in its frontmatter (`area: tactics`),
  and may name the **milestones** it serves (`milestone: [tac-in-heather]`).
  An area is the one place the issue's work lands; labels stay as free-form
  topics (`reals`, `omega`, `x86`) and can cross areas.
- `scripts/issue areas` prints the areas in priority order with their open and
  closed counts and each milestone's open issues, submilestones nested under
  their parent. `scripts/issue list --area
  A` / `--milestone M` filter; `scripts/issue tag <slug>… --area A
  [--milestone M,N]` retags without touching `updated:`. The web viewer's
  **Areas** tab shows the same order, with each area's direction and
  milestones.
- `scripts/plan-digest` renders this file's areas and milestones with each
  milestone's progress and last activity, every open issue as one line, and
  the last month of master, into `/mnt/project-files/plan/` (the project's
  shared folder) for readers without a checkout. It reads a commit
  (`--ref`, default `origin/master`), not the working tree, and is
  idempotent; `--fetch` refreshes first.
- `scripts/issue check` reads the two tables below. An unknown area or
  milestone in an issue is an error, and so is a submilestone whose parent
  is missing or belongs to another area; open issues with no area are one
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
  Not prioritised against the directions. Its work is pulled by a
  direction's milestone or blocker, and it also invests ahead of demand: an
  issue labelled `wanted` (one two or more directions will clearly need, or
  that Minus asks for) may be worked with no puller, built at its proper
  general design rather than the slice one customer needs. A round hurt by
  a weak foundation says so with a dependency request rather than working
  around it silently (`docs/agent-policy.md` §1–§4).

## Areas

<!-- areas -->
| priority | area | tier | name | direction |
|---|---|---|---|---|
| 1 | `heather-in-heather` | focus | Heather in Heather | Write real programs, compile them natively with proofs, and move the compiler's logic out of Rust into Heather, toward dogfooded optimisation passes. |
| 2 | `tactics` | focus | Tactics | Anything systematic is closed by some tactic: cheap specialised tactics, a few high-value general ones, and tactics written in Heather. |
| 3 | `interaction-trees` | focus | Interaction trees | Reason about effectful programs intuitively: interaction trees over container events, meeting the native program logic. |
| 4 | `mathematics` | steady | Mathematics | Fundamental classes and APIs first, then reals, floating point, and the fields Minus cares about (asymptotics, measure, locales, combinatorics), all designed constructive-first. |
| 5 | `heather-in-lean-coq` | next | Heather in Lean/Coq | Translate Heather proofs and their dependencies into Lean or Coq so they can be checked outside Heather, and so Heather can show it is trustworthy. |
| 6 | `machine-learning` | next | Machine learning | Bring Minus's Lean ML formalization (Wick) into Heather, improved, as a target for both the mathematical and the programming tooling. |
| 7 | `gpu` | horizon | GPU | A Triton-like kernel language, proved correct and efficient against a GPU model, reusing the floating point, numerics and ML proofs. |
| 8 | `rust-in-heather` | horizon | Rust in Heather | Translate Rust code into Heather to prove properties about it. |
| 9 | `lean-in-heather` | horizon | Lean in Heather | An autotranslator from Lean to Heather over a formal model of Lean, so Lean proofs can be cited (not a first-class Lean or mathlib port). |
| — | `language` | enabling | Language and elaborator | The surface language and its elaborator: syntax, inference, classes, inductives, modules, diagnostics, lints, editors. |
| — | `kernel` | enabling | Kernel and type theory | The kernel, its type theory (DeLaM and extensions), the metatheory, and checking cost. |
| — | `infrastructure` | enabling | Infrastructure | The test suite, caches and module images, performance measurement, and the CLI around them. |
<!-- /areas -->

## Milestones

A milestone is a usable result, stated so that someone can tell when it has
happened. A **submilestone** names its parent in the last column: it is a
piece of the parent small enough for one round or one agent, and the parent
is done when its own "done when" holds (normally, once its submilestones
have landed). Add submilestones when a milestone is picked up and its pieces
become clear; not every milestone needs them up front. Issues serve one
through `milestone:`; the list of issues is `scripts/issue list --milestone
<id>`, not a copy here.

<!-- milestones -->
| milestone | area | status | done when | parent |
|---|---|---|---|---|
| `hih-program-logic` | heather-in-heather | open | Native code's meaning is stated against interaction trees through one program logic, and a compiler from an effectful source to x86-64 is proved correct against it once, replacing the hand-proved per-program stack. |  |
| `hih-pl-source` | heather-in-heather | open | An effectful source denotes Linux trees, compiles to x86-64 by a Heather function, and the compiler's correctness theorem is proved once. | hih-program-logic |
| `hih-pl-first-program` | heather-in-heather | done | `tr` is built through the verified compiler with no per-program proof (the per-function certificate path was retired in B2, 2026-10-24). | hih-program-logic |
| `hih-tools` | heather-in-heather | done | Small GNU-compatible tools are built by `write-elf` through the verified compiler with no per-program proof, and pass tests against GNU under `LC_ALL=C`. Closed at nine (`cat`, `cat FILE…`, `head -c`, `head -n`, `yes`, `yes STR`, `echo`, `tr`, `wc`), which stay as a regression corpus; `grep -F`, `sort` and `tac` move to `nh-procedures` and `nh-heap` (2026-10-31, `docs/native/compiler-milestones-proposal.md` §8). | hih-program-logic |
| `hih-memory` | heather-in-heather | open | A native program allocates on the heap, under a byte-addressed memory model whose certificates bound and track the allocation. |  |
| `hih-memory-model` | heather-in-heather | open | Byte-addressed memory with explicit access outcomes is a library model that the native machine model and the program logic both use. | hih-memory |
| `hih-alloc-metering` | heather-in-heather | open | Certificates state an allocation bound, over a platform model that meters allocation. | hih-memory |
| `hih-first-alloc` | heather-in-heather | moved | Moved into `nh-heap` (2026-10-31): one native program allocates, frees or bounds its heap, and its theorem says so. | hih-memory |
| `hih-passes` | heather-in-heather | open | A compiler pass (certificate emission or an optimisation) is a Heather metaprogram with its proof, and Rust only moves its output around. |  |
| `hih-self` | heather-in-heather | open | A first component of Heather itself (candidate: the lexer, on the parser library) is written in Heather and compiled natively. |  |
| `self-lexer` | heather-in-heather | open | Heather's lexer is a `runtime fn` compiled natively, and its token stream matches `crates/syntax/src/lexer.rs` on every file under `lib/` (`docs/native/compiler-milestones-proposal.md` §5). | hih-self |
| `self-compiler` | heather-in-heather | open | `Source::compile` and its checks are compiled natively, and `write-elf` runs that binary in place of the fork's kernel evaluation, with the kernel's check of the emission unchanged. | hih-self |
| `hih-native-heather` | heather-in-heather | open | An ordinary Heather function marked `runtime fn` compiles under a setup (a library generator that boxes it, checks a judgment over its code, and is proved sound once) with no per-program proof, and two setups exist: the default one, and one that gives the compiler facts the default cannot (`docs/native/compiler-milestones-proposal.md` §4). |  |
| `nh-front` | heather-in-heather | open | The `runtime fn` generator is written in Heather, and the default setup compiles first-order pure functions (words of any width, `Bool`, flat records and enums, `match`, loops, byte arrays) with an agreement certificate; `compile-x86` runs on it instead of its Rust reflector. | hih-native-heather |
| `nh-procedures` | heather-in-heather | open | Calls compile to procedures with frames on the process stack and contracts derived from their bodies: a helper's code is emitted once, a non-tail recursive function compiles, and `grep -F` passes its GNU tests. | hih-native-heather |
| `nh-effects` | heather-in-heather | open | A `runtime fn` talks to the system through `uniq` capabilities in the sequencing surface, denoting trees through `Source`; `cat FILE…`, `wc` and `head -n` are rewritten in it and pass their GNU tests. | hih-native-heather |
| `nh-heap` | heather-in-heather | open | A `runtime fn` builds and reads lists and trees in an arena through `datarepr`, with exhaustion a defined exit; `sort` and `tac` pass their GNU tests. | hih-native-heather |
| `nh-ownership` | heather-in-heather | open | A second setup checks Rust-style ownership over reflected code, is proved sound once against the byte memory model, and the compiler uses its evidence for in-place updates and frees. | hih-native-heather |
| `nh-library` | heather-in-heather | open | A `runtime fn` over buffers its caller owns is exported under a named contract (a System V subset plus a memory footprint), proved once, and linked into a Rust binary; the first exports are the lexer's scanner and SHA-256's compress (`docs/native/native-lexer-crypto-roadmap.md` §2). | hih-native-heather |
| `hih-pl-spec` | heather-in-heather | open | Linux's calls and answers are a tree container, and `Sim` (the machine produces exactly a tree's traces) is bridged both ways to `LinuxRuns`, with `tr`'s spec written as a tree. | hih-native-heather |
| `hih-pl-wp` | heather-in-heather | open | One computed weakest precondition over every `Asm` item (syscalls and proved pieces included) and one loop rule are sound once, probed for elaborator cost. | hih-native-heather |
| `hih-crypto` | heather-in-heather | open | Cryptographic primitives have a specification in Heather, compiled code proved to implement it, a constant-time theorem under a named leakage contract, and native runs against published vectors (`docs/native/native-lexer-crypto-roadmap.md` §4). |  |
| `crypto-hash` | heather-in-heather | open | SHA-2 is specified once for both word widths, its compress and streaming update are `runtime fn`s proved against the specification, and the compiled SHA-256 replaces the scalar path of `crates/cache/src/sha256.rs` with every cache key unchanged. | hih-crypto |
| `hih-kernel-model` | heather-in-heather | open | A model of the kernel's reduction in Heather states the facts its accelerations rely on, and proves them, so that an optimisation checked nightly can be promoted to proven (`docs/kernel/kernel-model-design.md`). |  |
| `hih-km-probe` | heather-in-heather | done | The fold classifier's probe is sound: a run that is not blocked on a probe variable is, at the same fuel, the run of every instance (`Tm::whnf_inst`, `Tm::whnf_inst_settled`). | hih-kernel-model |
| `hih-km-runs` | heather-in-heather | done | Iterating an affine or synchronous fold class over a run is the unary fold, in the model with Σ, projections and runs (`Tm::fold_affine`, `Tm::fold_affine_peeled`, `Tm::fold_sync`). | hih-kernel-model |
| `tac-in-heather` | tactics | done | A tactic is written in Heather through a host elaboration interface, and one tactic that lives in Rust today has a Heather counterpart. |  |
| `tac-host-interface` | tactics | done | Heather code can read a goal, build a checked term, and report failure with its search state, through one scoped host interface. | tac-in-heather |
| `tac-first-port` | tactics | done | One tactic that lives in Rust today (candidate: `split_all` or `monoid` normalisation) has a Heather implementation that closes the same goals. | tac-in-heather |
| `tac-general` | tactics | open | A general-purpose rewriting and congruence-closure tactic (grind-like) closes the routine goals that today need hand `trans`/`cong` towers, and hands back its search state when it fails. |  |
| `tac-arith` | tactics | open | Linear integer arithmetic is complete and certified (CutSat), and polynomial inequalities go through the ring normaliser. |  |
| `it-library` | interaction-trees | done | The container-event interaction-tree library exists: bind, iter, trace refinement, and the bridge to `converges`/`fuel_monotone`. |  |
| `it-function-fields` | interaction-trees | done | A surface inductive can have a recursive function-typed field (`Vis(c, k: Resp(c) -> Tree)`), lowered through W, with match and recursion over it. | it-library |
| `it-core` | interaction-trees | done | Events as containers, the fuel-cut tree, `bind`/`iter`/`mrec`, and the structural laws, with the definitional ones checked as such. | it-library |
| `it-refinement` | interaction-trees | done | Trace refinement and depth-indexed equivalence, with the bridge to `converges`/`fuel_monotone` and one handler into world threading. | it-library |
| `it-native` | interaction-trees | done | A native program's theorem says its run refines an interaction tree. |  |
| `it-coinductive` | interaction-trees | done | Interaction trees diverge for real: a coinductive tree over container events with `bind` and `iter`, `approx` into the finite tree, and bisimilarity and eutt as `M` instances, bridged to the finite library's `Same` (`docs/kernel/kernel-coinduction-design.md` §6). |  |
| `it-cotree` | interaction-trees | done | `CoTree<R>(E)` with `bind`, `map`, `translate` and fuel-free `iter`, its approximations as a `Program` (`spin` diverges with no fuel), and strong bisimilarity as indexed codata with reflexivity, symmetry, transitivity, the monad laws, a `bind` congruence and the bridge to `Same` (`docs/itrees/coitree-design.md`). | it-coinductive |
| `it-eutt` | interaction-trees | done | Equivalence up to taus on `CoTree` as indexed codata with drop counts: reflexivity, symmetry, transitivity, `CTau(t) ≈ t`, the monad laws, and equivalent trees giving programs that refine each other (`docs/itrees/coitree-design.md` §7). | it-coinductive |
| `it-program-bridge` | interaction-trees | done | The fuel-free loop over a finite body and `Program::iter` refine each other, as do `program(bind(t, h))` and `Program::bind` of the programs; finite trees embed with exactly their traces (`docs/itrees/coitree-design.md` §8). | it-coinductive |
| `it-codata` | interaction-trees | done | A surface `codata` declaration lowers onto the kernel's `M`, with constructors, `match` through `out`, and guarded corecursive functions compiled into one `corec` (`docs/inductives/codata-elaborator-design.md`). | it-coinductive |
| `it-world-loops` | interaction-trees | done | Loops over a world have a fuel-free meaning: a `Source`'s `Repeat` has a fuel-free meaning over `CoTree::iter`, bridged to the fuelled one by `iter_refines`; `Io::cat`, `tac`, `sort` and `write_all` take no `passes`; the cat agreements state `Eutt` through the coinductive `Io::Reads` (`docs/language/effects-capabilities-design.md` §4). |  |
| `math-classes` | mathematics | open | The algebra and order class hierarchy (semiring to ordered field, lattices) is settled, with a documented API that clients use without restating laws. |  |
| `math-reals` | mathematics | open | Reals have their completeness interfaces and basic analysis (sequences, limits, continuity) on top of the regular Cauchy reals. |  |
| `math-float` | mathematics | open | Binary floating point (formats as data, a relational rounding spec with one executable rounding, error bounds, arithmetic and the error-free transformations) is in `lib/std/num/float/`, proved over dyadics and transferable to any ordered field (`docs/library/floating-point-design.md`; rounds 1–5). |  |
| `float-values` | mathematics | done | Formats, finite floats and floats, `Dyadic` with its ring and order, value order as a `StrictOrder`, successor and predecessor, and the standard constants proved canonical by evaluation. | math-float |
| `float-rounding` | mathematics | done | `RoundsTo` for the five IEEE modes, one executable rounding on a dyadic plus sticky proved to satisfy it, its uniqueness, successor/predecessor with spacing, and the mode laws (landed, design §11–§12). | math-float |
| `float-error` | mathematics | done | The standard model (relative error at most `u` in the normal range), the subnormal absolute bound, `ulp`, and γ-composition (landed, design §13). | math-float |
| `float-arith` | mathematics | done | Add, sub, mul, fma, div, sqrt and format conversion, each with value, signed-zero and special-value theorems. | math-float |
| `float-eft` | mathematics | done | Sterbenz, Fast2Sum, TwoSum, TwoProduct, Veltkamp splitting, the recursive sum's bound and Kahan's compensated step are proved (landed, design §19; Kahan's whole-loop bound is `float-kahan-bound`). | math-float |
| `float-bits` | mathematics | open | Bit-level encode/decode with the round trip, the OCP storage formats, NaN payload policies and exception flags. Not needed for `math-float` to be done. | math-float |
| `float-reals` | mathematics | done | Rounding is stated at `CReal` through a transfer lemma to any ordered field: faithful rounding computes, and correct rounding computes from apartness from the breakpoints. Not needed for `math-float` to be done. | math-float |
| `float-transcendental` | mathematics | open | Correctly rounded `exp` and `log`, from a `CReal` series plus a Padé apartness proof. Not needed for `math-float` to be done. | math-float |
| `float-p3109` | mathematics | open | The IEEE P3109 low-precision formats are `Format`s of the float library: precision one, unsigned formats, one zero and one NaN, saturation as an operation parameter, round-to-odd and stochastic rounding, and the encoding's bijection with the bit patterns, checked against the standard's tables (`issues/float-p3109.md`). |  |
| `p3109-values` | mathematics | done | Every P3109 format is a `Format` (precision one included, signed or unsigned, finite or extended), with its maximum exponent derived from the reserved codes rather than tabulated, and `RoundsTo`'s nearest-even tie rule correct at precision one. | float-p3109 |
| `p3109-projection` | mathematics | open | P3109's projection (a rounding mode, round-to-odd and the stochastic modes' support included, then a saturation mode) is stated and computed, with its faithfulness, its agreement with rounding in range, and Fast2Sum's exact overflow error under saturation. | float-p3109 |
| `p3109-encoding` | mathematics | open | Every P3109 format's decode from `K`-bit patterns is a bijection onto `Float(F)`, proved once for all formats, and its values match the standard's tables by evaluation. | float-p3109 |
| `math-metatheory` | mathematics | open | A result from heather-coq (for example a small logical-relation proof) is restated and proved in Heather. |  |
| `math-specific-choice` | mathematics | open | A library convention, with inference behind it, for asking for the specific property instead of choice, with per-type instances that discharge it without an axiom. |  |
| `math-finite` | mathematics | open | A finite type is a class with enumeration, cardinality and quantifiers decided by evaluation; finite maps, multisets and big operators are stated over it; and a dot product over `Fin n` needs no local sum lemma. |  |
| `math-order-fixpoints` | mathematics | open | Galois connections, closure operators and checked post-fixpoints are a library that liveness and one domain over words instantiate, well-founded order combinators are cited by `decreases` clauses, and one order hierarchy serves carriers at `Type` and `Type<1>`. |  |
| `math-binding-syntax` | mathematics | open | A binding signature generates well-scoped terms whose renaming and substitution laws are proved once, with `kernel_model` and one reflected IR as instances, or a design note records why hand-rolled syntax stays (`issues/generic-binding-syntax.md`). |  |
| `math-number-theory` | mathematics | open | `gcd` through the Chinese remainder theorem, `ZMod(n)` as a ring (a field at a prime, words at `2^w`) and univariate polynomials with division are in the library, with one cryptographic field's arithmetic and exact division by a constant stated over them. |  |
| `math-formal-languages` | mathematics | open | Regular languages have a denotation, derivatives and a DFA proved once, cited by the regex compiler; Kleene algebra with tests has its relational model, and one control-flow rewrite over `StructuredRegion` is proved by an equation in it. |  |
| `export-fragment` | heather-in-lean-coq | open | A closed, layer-free fragment of the library (Nat and List lemmas) is translated to Coq or Lean and rechecked there. |  |
| `ml-survey` | machine-learning | done | Wick is surveyed: what transfers, what must be redone better, and the mathematics and tooling it needs from Heather. |  |
| `ml-layers` | machine-learning | open | A layer grammar (linear, pointwise activation, compose, fork, residual) over computed shapes, with reverse mode defined once and proved against the formal derivative on polynomial layers, and a two-layer network that evaluates at `Rat` (`docs/surveys/wick-survey.md` §6). |  |
| `ml-float-forward` | machine-learning | open | One small network's forward pass runs at `Float(F)` and at `Rat`/`CReal`, with a composed error theorem between them, using `float-error`. |  |
| `ml-descent` | machine-learning | open | Deterministic gradient descent converges on an L-smooth, strongly convex (or PL) objective over an ordered field, with one concrete known-answer instance proved by evaluation. |  |
| `ml-gaussian-states` | machine-learning | open | Gaussian states on a polynomial algebra, Wick's theorem by perfect matchings, and cumulants by Möbius inversion on the partition lattice. |  |
| `gpu-model` | gpu | open | A design note fixes the GPU execution model and the kernel-language level (tile IR, Triton-like) to prove against, with what it needs from the other areas. |  |
| `rust-design` | rust-in-heather | open | A design note fixes the Rust subset, the semantics source (MIR or surface), and what the translation needs from `hih-memory` and `it-library`. |  |
| `lean-fragment` | lean-in-heather | open | A design note says which fragment of Lean translates into Heather and how impredicative `Prop` is handled. |  |
| `lang-sequencing` | language | open | Blocks bind over any carrier with a `bind` (`let x <- e;`, `e;`), and pure functions have `let mut`, `:=`, `for`, `while` and early exit, lowered to folds with unfolding equations; `mono.hthr` has no `bind` towers (`docs/native/compiler-milestones-proposal.md` §3). |  |
| `lang-proof-modularity` | language | open | Proofs compose against interfaces: opt-in interface definitions, lemma registries that automation reads, invariant and contract rules for loops and procedures, and large proofs that keep their sharing, each retiring rules from `docs/proof-patterns.md` (`docs/native/compiler-milestones-proposal.md` §6). |  |
<!-- /milestones -->

## Why these priorities

Three things decided them: what Minus said leads, what unblocks the most
other areas, and what is ready to be worked on now.

1. **Heather in Heather leads** because it is the project's stated goal (fast,
   broad, certified native code) and because it compounds: once passes are
   Heather metaprograms, every later optimisation is dogfooded. It also
   decides what "a program" means for interaction trees, Rust and GPU.
2. **Tactics are second** because they interweave with everything: they
   make writing complex code, not only proofs, faster and nicer, and with
   generated code a specialised tactic is cheap (see
   [Design principles](#design-principles)). The step that matters most is *writing tactics in
   Heather* (`tac-in-heather`). It shares its meta-layer interface with
   `hih-passes`, so the two focus areas pull the same enabling work.
3. **Interaction trees are focus** because the native program logic
   (`hih-program-logic`) is meant to be stated so that ITree refinement comes
   out as a lemma, not a re-founding. Designing them late would mean redoing
   that logic. Surface inductives with function-typed fields are part of this
   area's own work (`it-function-fields`), not a wait on someone else.
4. **Mathematics is steady**, not focus: it runs all the time and is the
   main customer of tactics, but most of its fields are worth more after the
   class hierarchy settles. Floating point is ranked early inside it,
   because GPU and ML both need it and Minus already has a Lean version.
5. **Constructive mathematics is not an area** but a design principle across
   mathematics (see [Design principles](#design-principles)). Its one concrete
   milestone, `math-specific-choice`, lives in mathematics.
6. **Heather in Lean/Coq comes before the other translations** because what
   Heather wants to show is that it is trustworthy, more than it needs to
   import other systems' logic. Exporting is also the easy direction: Heather
   is predicative and has no K, so a layer-free proof asks less of its target
   than Lean or Coq provide.
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
  Linux trace model (`docs/native-compiler-architecture-review.md@4acf2fe`,
  `docs/archive/native-architecture-review.md`). `wc` as a command and stream filters
  (`tr`) are the clients (`docs/archive/native-wc-command-design.md`,
  `docs/archive/native-stream-filter-design.md`).
- Layout and jump computation moved from Rust into Heather in 2026-10,
  proved by evaluation. Programs are stated over Runs, Straight and
  stretches (`docs/native-runs-design.md@4acf2fe`, `docs/archive/native-straight-runs-design.md`).
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
  are written on it. The design is `docs/native/native-program-logic-design.md`.
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
written on it (submilestones `hih-pl-source` and `hih-pl-first-program`;
`hih-pl-spec` and `hih-pl-wp` moved under `hih-native-heather` on
2026-11-01, as the spec and program logic its setups are proved against; it waits on `it-core` and burns the hand-proved
process stack first; its `hih-tools` made native programs real tools,
`docs/native/native-real-programs-plan.md`, and closed at nine of them). Since
2026-10-31 the direction is `docs/native/compiler-milestones-proposal.md`:
ordinary Heather compiles. `hih-native-heather` grows the compiler by
language feature and by setup (`nh-front`, `nh-procedures`, `nh-effects`,
`nh-heap`, `nh-ownership`; `hih-pl-spec` and `hih-pl-wp` are the Linux spec
and weakest precondition it is proved against), with its rounds in that document's §7, and
`hih-memory` (submilestones `hih-memory-model`, `hih-alloc-metering`; its
first allocation is `nh-heap`) underneath. `hih-passes` can proceed in
parallel because it is meta-layer work; its first round is
[function-ir-pass-in-heather](../issues/function-ir-pass-in-heather.md). `hih-self` is `self-lexer` and then
`self-compiler`, on the compiler `hih-native-heather` builds.
Since 2026-11-10 `docs/native/native-lexer-crypto-roadmap.md` charts two
targets through these milestones: the lexer linked into the compiler
(`self-lexer`, through `nh-library`: exports over memory the caller owns) and
cryptography (`hih-crypto`, first `crypto-hash`: SHA-2, with the cache's own
SHA-256 as its customer).
`hih-kernel-model` is independent of all of them: it models the kernel's
reduction in Heather so that the kernel's own accelerations, and later the
caches, can be proved rather than checked nightly
([kernel-model](../issues/kernel-model.md)).

### Tactics (`tactics`)

**Goal.** Anything systematic should be solved by some tactic. That means
more varied tactics: specialised ones are cheap with generated code, and a
few general-purpose ones are worth real design.

**Where it stands.** Certifying tactics exist for Presburger arithmetic
(`omega`, with CutSat), bit-vectors (`bv_omega`), commutative rings (`ring`),
case splitting (`split_all`), positivity, `decide`, relational congruence
(`rel_cong`), and `calc` chains (`docs/certifying-arithmetic-automation-design.md@4acf2fe`,
`docs/tactics/ring-normalization-design.md`, `docs/showcase/relational-context-round.md`).
Tactics are also written in Heather, as request trees `Tac<A>` the
elaborator answers through one host interface
(`docs/metaprogramming/host-elaboration-interface-design.md`, `lib/std/tactic/tactic.hthr`):
`split_all` (ported from Rust), `apply`, `first_of`, `mono`, `norm_num`,
`intervals`, and `generate` for declaration groups (`derive.hthr`). The
arithmetic deciders (`omega`, `ring`, `linarith`) keep their search in Rust
with a Heather certificate.

**Blockers.** What the host interface still lacks is native oracles with
checked certificates and `Tac` on the tree library's `ITree`
([host-elaboration-interface](../issues/host-elaboration-interface.md)), and
generators at open types and in sections
([generator-ctors-open-types](../issues/generator-ctors-open-types.md),
[generate-in-sections](../issues/generate-in-sections.md)). `grind`
closes an equation by congruence closure over the goal's equations and hints
given at their instances, and fails with its graph
(`docs/tactics/grind-design.md`); until it instantiates lemmas itself
([grind-e-matching](../issues/grind-e-matching.md)), routine equalities
that need a lemma are still hand `trans`/`cong` towers or hint lists
([grind-port](../issues/grind-port.md),
[monoid-normalisation](../issues/monoid-normalisation.md)).

**Milestones.** `tac-in-heather` (submilestones `tac-host-interface`,
`tac-first-port`), then `tac-general` (written in Heather if
the first has landed), with `tac-arith` continuing as arithmetic clients
need it.

### Interaction trees (`interaction-trees`)

**Goal.** Work with programs intuitively. heather-coq has evidence that
interaction trees will work. What is missing is more design, integration
with Heather, and the library itself.

**Where it stands.** The fit investigation is written
(`docs/itrees/interaction-trees-fit.md`). It proposes container events
(`Cmd`, `Resp`) over trees cut at fuel, with no kernel coinduction. Its key
conjecture was answered yes in heather-coq: depth-indexed bisimilarity
coincides with the greatest fixed point over container events
([interaction-trees-container-model](../issues/interaction-trees-container-model.md)).
The effects story is decided (2026-10-21): a uniqueness-threaded surface
that denotes interaction trees
([effects-direction](../issues/effects-direction.md)); building that surface
is [effects-uniqueness-surface](../issues/effects-uniqueness-surface.md).

**First work.** The surface can write a tree: a continuation field
`k: Resp(c) -> Tree` is a recursive function-typed field, lowered by the
tier-2 (W) generator since 2026-10-20, with `match` and structural recursion
through `k` (`docs/inductives/inductive-tier2-w-lowering.md`;
[recursive-function-fields](../issues/recursive-function-fields.md); the
tier scheme itself is owned by
[inductive-compiler](../issues/inductive-compiler.md)). Events as a *value*
parameter (`ITree<R>(E)`) lower since 2026-10-21
([tier2-value-parameters](../issues/tier2-value-parameters.md),
`docs/language/surface-value-parameters.md` §6). The core library is
`lib/std/itree/itree.hthr` (`docs/itrees/itree-core-round.md`): events, the tree with a
`Cut` leaf, `bind`/`iter`/`interp`/`mrec`, and the laws, the ones through `Vis`
up to a structural equivalence `ITree::Same` (finite trees need no depth
index; fuel plays its part). Traces, refinement across fuel, the bridge to
`converges`/`fuel_monotone`, and a state handler that is world threading are
`lib/std/itree/itree_trace.hthr` and `lib/std/itree/itree_state.hthr`
(`docs/itrees/itree-refinement-round.md`), so `it-library` is done. Native code
meets the trees through `Sim` (`lib/std/os/linux/linux_x86_64_sim.hthr`):
every program `write-elf` builds has a theorem that its ELF simulates its
source's tree at every fuel, so `it-native` is done
([native-one-program-logic](../issues/native-one-program-logic.md),
[native-elf-every-program](../issues/native-elf-every-program.md)).

**Milestones.** `it-library` through its submilestones `it-function-fields`,
`it-core` and `it-refinement`, then `it-native` together with
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
`x⁻¹`/`xⁿ` notation without junk values (`docs/library/creal.md`,
`docs/creal-*-round.md`, `docs/library/rational-order-round.md`), and point-free
foundations: frames, locale maps, points, nuclei and formal-topology
presentations over `Type<1>` carriers (`docs/library/frame-locale-design.md`), and the
real line as a locale with Heine–Borel and Cauchy reals as its points
(`docs/library/localic-reals-design.md`). Nothing
yet for measure, probability, combinatorics, asymptotics or floating point.
Open design for those that have issues:
[inductive-formal-covers](../issues/inductive-formal-covers.md),
[localic-real-numbers](../issues/localic-real-numbers.md),
[real-completeness-interfaces](../issues/real-completeness-interfaces.md),
[analysis foundations](library/analysis-foundations-design.md) (differential structure and dominance as the core, finite sums, asymptotics and expansions as first instances; its §13 orders the rounds),
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
landing in the kernel (`docs/kernel/iwf-former-design.md`) is what makes its
inductive families writable; mutual families
(`docs/inductives/mutual-inductive-design.md`) and families whose premises quantify
over an argument (`docs/kernel/iwf-infinitary-design.md`, a logical relation's
shape) lower onto it or onto `W` without a kernel change.

**Constructive design** (a principle across this area, see
[Design principles](#design-principles)). The kernel is predicative and has no axioms by default
(axioms are explicit, with provenance: `docs/kernel/axiom-provenance-design.md`).
The reals are constructive, with apartness and a Bishop bridge. The pieces
the principle needs already exist in some form: assumption scopes and
profiles ([implicit-logical-assumptions](../issues/implicit-logical-assumptions.md)),
searched evidence (`docs/library/positivity-evidence-design.md`), and `Decide`
instances. What is missing is the convention that ties them together
([default-inhabited-nonempty](../issues/default-inhabited-nonempty.md),
[apartness-structures](../issues/apartness-structures.md),
[real-number-foundation](../issues/real-number-foundation.md)), which is the
milestone `math-specific-choice`.

### Heather in Lean/Coq (`heather-in-lean-coq`)

**Goal.** Translate Heather proofs and their dependencies into Lean or Coq so
they can be verified outside Heather. The foundations differ, but much of
the difference is in how things are done, or can be handled by replacing
equality with another symbol. Proving which fragment can be trusted across
the two is further off and needs more mathematical maturity in Heather.

Export is wanted more than import: it is how Heather shows it can be
trusted.

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

**Where it stands.** Wick is surveyed (`docs/surveys/wick-survey.md`): what
transfers, what to redo (models as programs at `Rat`/`CReal`/`Float`,
canonical structure computed rather than searched, algebra before measure),
and what it needs, with follow-up issues. Nothing is implemented yet. It
depends on `math-classes`, `math-reals`, `math-float`, finite linear algebra,
and later on measure and probability.

**Milestones.** `ml-survey` (done, [wick-survey](../issues/wick-survey.md)).
`ml-layers` ([ml-tensor-shapes](../issues/ml-tensor-shapes.md),
[ml-layers-reverse-mode](../issues/ml-layers-reverse-mode.md)) is the
recommended first round, after finite big operators and the start of
[finite-linear-algebra](../issues/finite-linear-algebra.md). Then
`ml-float-forward` ([ml-scalar-refinement](../issues/ml-scalar-refinement.md)),
`ml-descent` ([ml-deterministic-descent](../issues/ml-deterministic-descent.md))
and `ml-gaussian-states` ([ml-gaussian-states](../issues/ml-gaussian-states.md)),
which is independent of the others and can run in the mathematics lane once
[set-partition-combinatorics](../issues/set-partition-combinatorics.md) exists.

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
enabling issue shows it has a puller. Work with no puller yet is still
legitimate when it is `wanted` (`docs/agent-policy.md` §1); milestones of
the enabling areas' own, judged by what they unlock, are proposed in
[enabling-area-directions](../issues/enabling-area-directions.md).

`language` has two milestones of its own, both pulled by
`hih-native-heather` and the tactics (`docs/native/compiler-milestones-proposal.md`
§3, §6): `lang-sequencing`, one sequencing surface for any carrier and for
pure imperative code, and `lang-proof-modularity`, proofs that compose
against interfaces rather than code.

## Design principles

These are not areas. They shape decisions in every area, and a design doc
or review should say how it meets them.

- **Constructive-first mathematics.** Much of the mathematics has to be
  designed with constructivity in mind from the start, not patched later. A
  statement takes the *specific* property it needs rather than assuming
  choice or excluded middle. Choice could always supply that property, but
  specific types supply it without choice (a decidable equality, a located
  real, a finite enumeration). Apartness and located structures come first
  where the classical theory would use plain inequality. Axioms stay
  explicit (`docs/kernel/axiom-provenance-design.md`).
- **Tactics everywhere.** Anything systematic should end up closed by a
  tactic, in programs as much as in proofs. When a round writes the same
  shape of proof or code by hand a third time, it files a `tactics` issue
  naming the milestone it was working on, so the tactic's customer is
  recorded with it.
- **Logic in Heather, not Rust.** New compiler or elaborator logic goes into
  Heather when Heather can hold it. Rust stays the untrusted plumbing.

## Parallel lanes

Disjoint areas can be worked at once by separate agents. What decides
whether two rounds can run together is the code they touch, so each lane is
listed with its main footprint. Two rounds in different lanes rarely
conflict; two rounds in one lane should be sequenced or split by
submilestone.

| lane | main footprint |
|---|---|
| Native code (`heather-in-heather`) | `crates/cli/src/native*`, `crates/elab/src/function_ir*`, `heather_emit.rs`, `lib/native/`, `lib/certgen/`, `lib/std/arch/`, `lib/std/os/` |
| Tactics | `crates/elab/src/{omega,omega_cert,cutsat,ring,bv_omega,goal_combinators,relational_context}*`, `lib/std/tactic/`; later the meta layer |
| Kernel model (`heather-in-heather`) | `lib/kernel_model/`; it reads `crates/kernel/src/eval/` and changes it at most in comments |
| Interaction trees | `lib/std/itree/`; `crates/elab/src/inductive.rs` and the W lowering for `it-function-fields`, shared with `language` |
| Mathematics | `lib/std/{num,algebra,relation,data}/`, `docs/showcase/` |
| Export, ML, GPU, Rust, Lean | new crates or scripts and design notes; nearly disjoint from everything |
| Kernel | `crates/kernel/` |
| Language, infrastructure | `crates/elab` core (`lib.rs`, `expr.rs`, `unification.rs`, `traits.rs`), `crates/cli`, `scripts/` |

Shared hotspots that every lane can touch, and where parallel rounds do
collide: the elaborator core files above, `crates/elab/src/prelude.hthr`,
the native support lists (`read_command.rs` SUPPORT/IMPORTS and the test
lists), `CLAUDE.md`, and this file's log. Issue files are one per issue and
merge cleanly. The suite's CPU rails are per process, so parallel agents on
separate machines do not slow each other's tests.

## Changing this file

- Changing an area's priority or tier is a decision Minus makes. Record it
  as a one-line entry in the log below, with the reason.
- A new area needs a row, a section, at least one milestone, and a lane.
- A submilestone is added when its parent is picked up; give it a "done
  when" a single round can meet.
- When a milestone lands, set its status to `done`, link the PR in the log,
  and leave the row so the history stays readable.

## Log

- 2026-10-20: Areas, tiers and milestones proposed from Minus's list. The open
  issues were tagged by area, and milestones were set only where an issue
  clearly serves one. Closed issues are left untagged.
- 2026-10-20: Minus's review. Priority guides allocation and is not a
  sequence; milestones gain submilestones; parallel lanes added, since
  disjoint areas can run on separate agents at once. Constructive mathematics
  stops being an area and becomes a design principle across mathematics
  (`cons-specific-choice` becomes `math-specific-choice`). Tactics are noted
  as cross-cutting, for code as well as proofs. Function-typed fields are
  interaction-tree work (`it-function-fields`). Export is wanted for showing
  trustworthiness, more than import.
- 2026-10-20: `math-float` scoped to rounds 1–5 of `docs/library/floating-point-design.md` after Minus's review of the design. Its submilestones are `float-values` through `float-eft`, plus `float-bits`, `float-reals` and `float-transcendental`, which do not block it.
- 2026-10-21: Minus's review of the program logic design: native code is
  rebuilt on interaction trees as a compiler proved correct once, after the
  tree library; the hand-proved process stack burns first.
  `hih-program-logic`'s "done when" is restated to match and its
  submilestones are `hih-pl-*` (`docs/native/native-program-logic-design.md`).
- 2026-10-21: `it-core` (PR #94) and `it-refinement` landed, so `it-library` is
  done. `it-refinement`'s depth-indexed equivalence is carried by the
  structural `ITree::Same` plus refinement across the fuel family
  (`docs/itrees/itree-refinement-round.md`), not by a relation of its own.
- 2026-10-21: `ml-survey` done (`docs/surveys/wick-survey.md`). Its proposed ML
  milestones wait for Minus's review before they are added here.
- 2026-10-22: Minus adopted the survey's four ML milestones (`ml-layers`,
  `ml-float-forward`, `ml-descent`, `ml-gaussian-states`) as proposed in
  `docs/surveys/wick-survey.md` §6; the follow-up issues are tagged with them.
- 2026-10-21: `float-values` marked done: round 1 (PR #85) and round 2's
  successor/predecessor (PR #95) cover its "done when"
  (`docs/library/floating-point-design.md` §10, §12).
- 2026-10-21: Minus's answers on the native rebuild
  (`docs/native/native-program-logic-design.md` §10): the ideal version from the
  beginning (abstract read sizes in S1), kernel evaluation of the compiler
  first with native speed later, a uniqueness-threaded surface that denotes
  trees, and a kernel round for coinductive types planned now rather than
  waiting for a customer (`issues/kernel-coinductive-types.md`, area
  `kernel`). The source's shape (S3) stays open.
- 2026-10-22: `it-coinductive` added for the coinductive tree library on the
  kernel's `M` (PR #111), with `it-codata` (the elaborator's `codata`
  surface) as its first submilestone, done on this round's PR.
- 2026-10-22: `M` got codes on the same PR (`docs/kernel/kernel-m-codes-design.md`),
  so codata declarations sit at layer c with everything else.
- 2026-10-22: indexed codata (`docs/inductives/codata-indexed-design.md`), the index
  read by observation; `SBisim`'s reflexivity, symmetry and transitivity are
  corecursive functions. The library is next under `it-coinductive`.
- 2026-10-22: `it-cotree` added and done: the coinductive tree library with
  strong bisimilarity (`lib/std/itree/coitree.hthr`), after codata signatures got
  names of their own (`docs/inductives/codata-named-signature-design.md`). eutt and the
  bridge to the fuelled programs remain (`issues/coitree-eutt.md`,
  `issues/coitree-program-bridge.md`).
- 2026-10-22: `it-eutt` added and done (`lib/std/itree/coitree_eutt.hthr`), with
  bisimilar and eutt-related trees refining each other as programs. The
  `iter` half of the program bridge stays open
  (`issues/coitree-program-bridge.md`). Simulation between finite trees over
  different events, with the loop rule `cat` needs, landed in the same round
  under `it-library` (`docs/itrees/itree-simulation-design.md`).
- 2026-10-24: `it-program-bridge` added and done
  (`lib/std/itree/coitree_bridge.hthr`): the coinductive loop and `bind`
  against the fuelled programs, both directions, closing
  `issues/coitree-program-bridge.md`.
- 2026-10-24: `hih-kernel-model` proposed, with `hih-km-probe` done and
  `hih-km-runs` next, for Minus's review. Minus asked for a Heather-in-Heather
  step as the way to let optimisations of the core be proven rather than
  checked nightly (`docs/infrastructure/testing-architecture-design.md` §5), and none of the
  area's milestones modelled the kernel. The first round proves the fold
  classifier's probe argument (`docs/kernel/kernel-model-design.md`).
- 2026-10-24: `hih-km-runs` done (`lib/kernel_model/kernel_runs.hthr`): the
  affine and synchronous run folds join the unary fold in the model with
  pairs, projections and runs (`docs/kernel/kernel-model-design.md` §7).
- 2026-10-26: `hih-tools` added under `hih-program-logic`, at Minus's request
  to get from cat to real programs. It is the plan in
  `docs/native/native-real-programs-plan.md`: bytes, compile capacity, a program
  builder, then argv, `open`, data size and decimal I/O, then the tool suite.
- 2026-10-28: `hih-pl-first-program` marked done: `tr a-z A-Z` is built by
  `write-elf` through the verified compiler with no per-program proof
  (PR #210, `issues/native-source-bytes.md`), after B2 (PR #156).
- 2026-10-31: `tac-host-interface`, `tac-in-heather` and `it-native` marked
  done. The host interface reads goals, builds checked terms and reports
  failures with what it tried (rounds 1–2¾), and `split_all` has a Heather
  port that closes the Rust one's goals (`tac-first-port`). Every program
  `write-elf` builds gets `<s>_elf_runs`, `SimProgram` of the ELF
  against `src.denote(args)` (`Source::elf_runs`), and
  `sim_every_run` says a run that got a returning trace's answers produced
  exactly that trace's events. The claim holds at every fuel, so liveness is
  not stated. The host interface's remaining work
  (oracles, `Tac` on `ITree`, generator gaps) stays open in its issues
  without a milestone.
- 2026-10-31: Minus re-aimed the compiler work (`docs/native/compiler-milestones-proposal.md`, §8 records the decisions). `hih-tools` closes at nine tools as a regression corpus. `hih-native-heather` is added (`runtime fn` setups: `nh-front`, `nh-procedures`, `nh-effects`, `nh-heap`, `nh-ownership`), and `hih-first-alloc` moves into `nh-heap`. `hih-self` gets `self-lexer` and `self-compiler`. `language` gains `lang-sequencing` (binding over any carrier) and `lang-proof-modularity` (opt-in interface definitions). Ownership is the second setup by Minus's lean, to be confirmed when its round starts.
- 2026-10-31: `float-reals` marked done: `RoundsTo` and the error model's transfer stated once over any ordered field with a morphism from `Rat` (`RoundsToReal` its `CReal` reading), faithful rounding of an enclosed real that always ends, correct rounding from the grid gap (`docs/library/floating-point-design.md` §17–§18, issues/float-reals-ordered-field.md).
- 2026-11-01: `hih-pl-spec` and `hih-pl-wp` move from `hih-program-logic` to `hih-native-heather` (Minus, after the daily step-back review): with the compiler work re-aimed at `runtime fn` setups, they had no milestone pulling on them, and they are the Linux spec and the program logic that the setups' one-time soundness proofs (`nh-effects`, `nh-procedures`, `nh-heap`) are stated against. Their "done when" and their issues' milestone tags are unchanged; `hih-program-logic` keeps `hih-pl-source` and the done `hih-pl-first-program` and `hih-tools`.
- 2026-11-01: `it-coinductive` marked done: its submilestones had landed, and the last open issues under it closed on this round's PR (`Eutt::bind_cong`, issues/coitree-eutt-bind-cong.md; nested constructors above a corecursive call, `docs/inductives/codata-elaborator-design.md` §5.4). Indexed nesting and corecursion up to friendly functions are filed without a milestone (issues/codata-nested-guards-indexed.md, issues/codata-corecursion-up-to.md).
- 2026-11-02: Minus: the enabling tier stops waiting on a puller. Pulling
  alone had encouraged the minimal work a feature needed, and native code
  had to be burned for accumulating it. Enabling work now also invests
  ahead of demand (`wanted`), and a round hurt by a weak foundation files a
  dependency request instead of a silent workaround. Both, with what
  threads decide alone and what they ask, are in `docs/agent-policy.md`.
- 2026-11-04: `it-world-loops` added (Minus asked for the thread): the customer half of the coinductive loop decision (`docs/language/effects-capabilities-design.md` §4, §7.5), after the loop lemma up to `Eutt` landed (#409). It serves `nh-effects` without being under it, since it is about what a tree means, not about the setup.
- 2026-11-04: `it-world-loops` marked done on the same round's PR: its one issue (issues/effectful-loops-without-passes.md) closed, with the bridge proved both ways (`Source::tree_co_refines`, `tree_co_refined`).
- 2026-11-10: `nh-library`, `hih-crypto` and `crypto-hash` added with `docs/native/native-lexer-crypto-roadmap.md` (Minus asked for the roadmap to a lexer linked directly and to cryptography that is verified and run). Both targets are libraries, not programs: `nh-library` is the exports-over-borrowed-memory work that had no milestone (`issues/native-library-exports-design.md`), and the linked lexer no longer waits on `nh-effects`. `self-lexer`'s done-when is left as written for Minus to move.
- 2026-11-10: first round toward `nh-library` and `crypto-hash` (`docs/native/native-lexer-crypto-roadmap.md` §10). Minus confirmed "linked directly" means linked into the binary, and named the numeral crate as a later linked target (`issues/numeral-linked.md`, under `nh-library`). In the tree: compiled functions linked into a Rust crate under a regeneration gate (`crates/linked`), the SHA-2 specification with "abc" proved at both widths, narrow widths in the verified lowering, and the word functions of SHA-512 and SHA-256 certified and proved against the specification. Neither milestone's done-when is met: both wait on arrays in the pure fragment and the export contract over caller-owned memory.
- 2026-11-10: second round, the lexer's lane (`docs/native/native-lexer-crypto-roadmap.md` §10). Heather's scanner is an automaton written in Heather (`lib/lang/lexer/lexer_scan.hthr`), every family of its states certified and linked, with the longest-match loop in Rust over it (`crates/linked/src/scanner.rs`) and as an evaluated specification (`lexer_tokens.hthr`). It gives the Rust lexer's kinds and spans on every Heather source in the repository. `self-lexer` is not met: the values, the compiled loop and the switch are open, and the automaton is twenty-three programs where it should be one (`issues/runtime-generator-program-size.md`, `issues/compile-x86-certificate-memory.md`). The read half of caller-owned memory is the next piece on this lane.
- 2026-11-10: third round, the limits the second recorded (`docs/native/native-lexer-crypto-roadmap.md` §10). The automaton is one program: `scan_step` is a `runtime fn` of two dozen functions, one certificate and one export. Linking cites facts each function published (`docs/native/runtime-fn-setups-design.md` §16.14), `compile-x86` reads and checks a function at a time, and the kernel compares a closed verdict's type in one run (`issues/type-conversion-one-sided-delta-steps.md`). A program's cost follows its largest function; a function is bounded by its emission statement (`issues/native-function-emission-one-statement.md`). `self-lexer` still wants the values, the compiled loop and the switch.
- 2026-11-10: fourth round, the emission limit (`docs/native/native-lexer-crypto-roadmap.md` §10). A function of a hundred comparisons certifies as one function (`issues/native-function-emission-one-statement.md`, closed): the kernel reads a counter written a successor at a time as the run it spells (`issues/succ-chain-numbers-fold-unary.md`), the lowering's register file is data, and the placement search keeps counted sets. The statement is still one conversion; emitting a region at a time is filed, not built (`issues/native-function-emission-in-parts.md`), and past a hundred comparisons the generator refuses first (`issues/runtime-generator-large-function-limits.md`). The read half of caller-owned memory is still the next piece on the lexer's lane.
- 2026-11-10: five mathematics milestones added after Minus accepted a ranking of foundational areas (asked for as general foundations that also serve native code and Heather-in-Heather): `math-finite`, `math-order-fixpoints`, `math-binding-syntax`, `math-number-theory`, `math-formal-languages`, each with first-round issues. The library is deep where a customer drove it (reals, floats, x86) and thin in the discrete mathematics programs and compilers are made of. Minus's decisions: analysis and locale work is not paused and is taken as it comes; the order hierarchy should be unified across universes, with language work if it needs it (`issues/order-hierarchy-across-universes.md`); generic binding syntax is welcome, with a design round first to find its problems. On tactics: `simp` first, tunable and wrappable, and a specialised variant of a tactic is acceptable where it is stronger for one domain (`issues/simp-tactic.md`).
- 2026-11-24: Minus re-aimed `nh-ownership`: ownership becomes the default `runtime fn` discipline (stated and guaranteed: refusal, never a silent copy), not a second setup, with stored references and shared mutation in scope together. The brief a design session starts from is `docs/language/ownership-design.md`; the milestone's done-when is left for that design to restate.
- 2026-11-25: Minus put the IEEE P3109 formats in scope after reading the FLoPS paper (`docs/papers/2602.15965v3.pdf`): `float-p3109` with submilestones `p3109-values`, `p3109-projection` and `p3109-encoding`; tracking issue `issues/float-p3109.md`. It does not block `math-float`.
- 2026-11-25: `p3109-values` done: `Format` has precision one and a reserved count, ties go to the even code, the overflow tie follows the largest float's parity, and `lib/std/num/float/p3109.hthr` builds every P3109 format, checked against the working group's value tables (`docs/library/float-p3109-design.md` §5).
