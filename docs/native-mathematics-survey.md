# What mathematics native proofs lack, ranked by the proofs it would shorten

Minus asked (2026-11-09) for a thread on the general mathematics Heather
lacks that matters most for modelling native programs and proving many
things about them: not basic data structures, but the theories underneath.
This note answers from master at `a5d7cb5`, reading `lib/native` (61 files,
about 41,000 lines), `lib/std/arch`, `lib/std/os`, `lib/std/machine` and the
mathematics they import.

It is a survey. It files issues and changes no library or compiler code.
It extends `docs/compilation-vision.md` (facts, passes, setups) and
`docs/effects-locality-design.md` (footprints, the frame theorem over worlds)
and does not reopen their decisions. Locale theory
(`issues/frame-and-locale-foundations.md`, point-free topology) is a
different "frame" and is not touched here.

## Method

Three passes, as in `docs/stdlib-math-awkwardness-survey.md`.

1. **Counting idioms.** `grep -o` over `lib/native`, `lib/std/arch` and
   `lib/std/os` for the shapes a missing theory leaves behind: a lemma kit
   defined more than once, a side condition repeated at every call, a
   bespoke soundness proof per analysis. The counts are citations, not
   theorems: each is one place a proof spends a line on the idiom.
2. **Reading** where the counts concentrate: `native_alloc`,
   `native_compile_homes`, `native_compile_correct`, `x86_64_byte_memory`,
   `x86_64_stack`, `x86_64_fetched_code`, `linux_x86_64_io`,
   `linux_x86_64_sim_paid`, `memory`, `bitvec_nat`, `lib/lang/facts`.
3. **Probes** for the claims that something is missing (§9), checked with
   `heather check` on the release binary.

The ranking is by how many native proofs a theory would shorten *today*,
then by how many open milestones are waiting on it. A theory that only a
future round needs ranks below one that today's proofs pay for at every
call.

## 0. Summary

| # | Theory | What native proofs pay today | Waiting on it | Issue |
|---|---|---|---|---|
| 1 | Boolean algebra of finite sets, decided | ~1,080 membership citations (`Mem`, `absent`, `union`, `minus`, `Inside`); ~30 set lemmas local to `lib/native` | liveness, ports, register sets, every footprint | `finite-set-membership-solver` |
| 2 | Machine words as ℤ/2ⁿ | ~240 `Nat::pow(2, …)` no-overflow side conditions; no `add_mod`, no `ModEq`, `ring` refuses words | `function-ir-pass-arithmetic-folds`, strength reduction, address arithmetic | `machine-words-modular-ring` |
| 3 | Transition systems and simulation diagrams | four copies of the reflexive-transitive closure kit; ~100 citations of their lemmas; inclusions between them by hand | every pass's correctness composing (`hih-passes`) | `transition-systems-and-simulations` |
| 4 | Address intervals and interval sets | `Space::Apart`/`Distinct` pointwise, re-proved per region kind (~140 citations); layouts as hand prefix sums | `wp-view-separating-product`, `x86-call-memory-footprints`, the arena | `address-interval-sets` |
| 5 | Monotone dataflow, checked post-fixpoints, Galois connections | liveness's loop sets and `Ix::hi` each proved sound by hand | `facts-on-demand`, `unique-fact`, `Writes`, every new analysis | `dataflow-checked-fixpoints` |
| 6 | Numeric domains over words: wrapped intervals, known bits | `InBounds` producers and `fits` side conditions by hand | `InBounds`, folds, alignment, shifts | `word-abstract-domains` |
| 7 | Separation algebras for ownership | none yet (memory framing is §4's) | `nh-ownership`, the arena's allocator | `separation-algebra-ownership` |
| 8 | Total preorders, lexicographic order, permutations | `Sorted`/`isort` at `Nat` only, in `lib/lang` | `sort`, `uniq`, `comm` (`nh-heap`) | `sorting-order-theory` |
| 9 | Codecs as partial isomorphisms | one round-trip theorem per instruction form | each new instruction, ELF, the self-hosted lexer | `codec-round-trips` |
| 10 | Independence of effects (trace equivalence) | none yet | a reordering pass consuming `Writes`; `world-separable-frame` | `effect-independence` |

Two further findings are owned elsewhere, and this note only adds evidence to
them: point updates of a store (`Valuation::set_other`, `read_gpr_other`,
`Memory::get_set_*`, `nat_map_get_set_*`, `Env::*_set_other`, ~265
citations over five store types) belong to
`issues/state-location-and-frame-kit.md`; and the hand transitivity towers
(`within_trans` and its kin, ~450 citations; `trans`/`cong_fn`/`j`, ~2,800)
are automation, owned by `tac-general` (`docs/tactics-survey-2026-11-08.md`).

**Recommended order**: 1 and 2 first, independently (each is self-contained
and pays at once); then 3; then 4, which `wp-view-separating-product` should
build on; then 5 with 6 as its first numeric domain. 7–10 wait for the round
that needs them, each named in its issue.

What this note does **not** recommend: general graph theory for control flow
(dominators, SCCs, reducibility), because FunctionIR's `StructuredRegion` is
a tree and loop heads are explicit, so a dataflow framework over the region
tree needs none of it; a step-indexed higher-order separation logic (Iris),
because Heather's memory is a total function and its loops are fuelled or
coinductive, which first-order footprints (§4) and the existing `CoTree`
theory already cover; and fractional permissions, until something is
concurrent.

---

## 1. Finite sets of identifiers: a Boolean algebra, decided

**Today.** The register allocator, liveness, port directories and register
pools all represent sets as lists: `List<Nat>` with `absent`, `holds`,
`union`, `minus`, `Inside` in `lib/native/native_alloc.hthr:96–102, 896`,
and `List<Gpr>` with `Gpr::absent_*` in `native_compile_homes`. Liveness is
`live_before(reads, written, out) = reads.union(out.minus([written]))`, and
every statement, region and loop of the compiler's correctness proof carries
membership facts across these operations. The counts over `lib/native`,
arch and os: `Mem(` 257, `absent(` 237, `union(` 81, `Inside(` 64,
`minus(` 55, `holds(` 44, and `mem_append_l/r` 50 more; about 1,080 in all.
`lib/native` defines about 30 set lemmas of its own (`List::union_left`,
`inside_union`, `inside_minus`, `absent_mem`, `disjoint_mem`,
`absent_append`, `Gpr::absent_mem`, …) and proves each consumer's membership
step by chaining them.

**The theory.** A membership goal over set expressions built from atoms by
∪, ∖, ∩, `++`, `Cons` and a filter is decided by propositional logic on
the atoms' memberships: every operation is pointwise, so `x ∈ e` is a
Boolean function of the bits `x ∈ A₁, …, x ∈ Aₖ` (the Boolean algebra of
sets is the power of the two-element one). Inclusion `∀x. x ∈ e₁ → x ∈ e₂`
is the same check at a generic `x`. Elements written as literals (a
`Cons(r, …)`) add equality atoms `x = r`, decided with the element type's
decidable equality and case split at most once per distinct literal.

**What to build.** A reflective tactic, Heather-side: reify a goal into a
`SetExpr` (atoms, unions, differences, intersections, singletons), a
denotation `mem(x, e): Bool` that computes membership through `absent`, a
soundness lemma `mem(x, e) = True ↔ Mem(x, ⟦e⟧)`, and a truth-table check of
hypotheses ⇒ goal whose verdict is `= True` by `refl` (the closed-verdict
rule, `docs/proof-patterns.md`). Over the lists the compiler already uses,
so nothing migrates to `FiniteSet`. Probe P4 (§9) shows `grind` does not
do this today; P5 shows the hand chain one step costs.

**Why first.** It has the largest count by an order of magnitude, it is
local (no class, no instance, no change to the compiler's definitions), and
every later footprint theory (§4, §5, §7) produces goals of this shape.

## 2. Machine words as ℤ/2ⁿ

**Today.** `lib/std/bitvec/bitvec_nat.hthr` opens with *"Bounds are
mathematical, never modular"*: `toNat_add` needs `a.toNat() + b.toNat() <
2^n`, `toNat_sub` needs `b <= a`, and so on. That was the right first
choice (no-overflow facts are what `bv_omega` and the decimal parser needed),
but the modular half was never added. `Nat::pow(2, …)` appears about 240
times in native, arch and os, almost all as a `fits` premise threaded to a
lemma. `nat.hthr` has `div_mul_add_mod`, `mod_lt`, `mod_mul_mod`, but no
`add_mod`, `mul_mod`, `mod_add_mod` and no congruence relation; `BitVec`
has `add_comm` and the cancellations but no associativity in its theorem
list and no ring instance, so `ring` refuses at words (P1).
`issues/function-ir-pass-arithmetic-folds.md` is waiting for exactly the
missing statements: `ofNat(a).add(ofNat(c)) = ofNat(a + c)` at an open
width (P3).

**The theory.**
- *Congruence modulo m* on `Nat` and `Int`: an equivalence compatible with
  `+`, `*` and powers (`ModEq`), with `add_mod`, `mul_mod`, `mod_mod_of_dvd`
  and the power-of-two facts (`mod 2^n` of `mod 2^(n+k)`). These are
  `Nat`/`Int` facts and live in `nat.hthr`/`int.hthr`
  (`facts-live-in-their-type-file`).
- *`BitVec(n)` is the ring ℤ/2ⁿ*: `toNat(a + b) = (toNat a + toNat b) mod
  2^n`, the same for `*`, `neg`, `sub`; a `CommRing<BitVec(n)>` instance at
  `RelId` so `ring` normalises word expressions.
- *`ofNat: ℕ → BitVec(n)` is a semiring homomorphism at every width*, and
  truncation `BitVec(n + k) → BitVec(n)` a ring homomorphism. That is what a
  fold proves "at every width", which FunctionIR's valuations demand.
- *Signed reading*: `toInt(a) ≡ toNat(a) (mod 2^n)`, so a signed identity is
  a ring identity plus a range fact.

The no-overflow lemmas stay, now as corollaries (`mod_of_lt`). Customers:
constant folding and strength reduction in FunctionIR passes, address
arithmetic in a wrapping space (`rip_compose` is associativity in ℤ/2⁶⁴),
and checksums and hashes in tools.

## 3. Transition systems and simulation diagrams

**Today.** The reflexive-transitive closure of a step relation is defined
four times, each with its own kit: `Steps`/`Reaches` in
`lib/std/relation/relation.hthr:275`, `MachineRuns`/`MachineSteps` in
`x86_64_stack.hthr:170`, `FetchedRuns`/`FetchedSteps` in
`x86_64_fetched_code.hthr:228`, `LinuxStepsN`/`LinuxSteps`/`LinuxPlus` in
`linux_x86_64_io.hthr:354–380`. Each has its `refl`, `one`, `cons`,
`append`, `trans`; and the inclusions between them
(`machine_runs_of_fetched`, `linux_steps_of_fetched`,
`linux_steps_of_machine`, `LinuxIo::steps_of_stack`) are each an induction
by hand, where one generic `Star` would make them `star_monotone` at an
inclusion of steps. Nothing in native uses relation.hthr's copy. About 100
citations of these lemmas; `Site::Runs`, `LoopRuns` and `Target::Runs` are
further run predicates over the same shape. `SimPaid`
(`linux_x86_64_sim_paid.hthr`) is a star-with-plus simulation diagram
spelled for one tree type.

**The theory.** The small-step library CompCert's `Smallstep` and
Leroy's lecture notes keep: `Star`, `StarN` (counted, which is why the
copies count: "counting keeps concatenation a plain induction"), `Plus`;
inductive invariants; determinism and what it gives (runs determined,
`linux_runs_determine`'s shape); simulation diagrams (lock-step, plus,
and star with a well-founded measure for stuttering), their vertical
composition, and "a forward simulation into a deterministic target is
also a backward one". Stated over any step relation, once.

**Why third.** It dedups what exists, and it is what a chain of certified
FunctionIR passes composes through: each pass proves one diagram, and the
chain is composition, not a new proof (`hih-passes`). The tree-side
simulation (`itree_sim.hthr`, `Program::Simulates`) stays: it is about
trees, not states, and §3's diagrams are its machine-side partner.

## 4. Address intervals and interval sets

**Today.** `lib/std/machine/memory.hthr` states span facts pointwise:
`Space::Distinct(a, k)` and `Space::Apart(a, k, b, l)` quantify over offsets
`p < k`, `q < l`. Each region kind then re-proves that offsets below the
top are addition and that two spans are apart: `BitVec::space_apart`,
`space_apart_above`, `DataRegion::toNat_at`, `perm_from`, `allows`,
`Layout::buffer_apart` (with `List::total_take_nth`/`total_take_apart`,
prefix sums by hand in `native_compile_facts`), `scratch_below_stack`,
`Homes::Apart`, `arena_cells_within`. About 140 citations.

**The theory.** Half-open intervals `[a, a + k)` in a `Space` with a
no-wrap condition, and their algebra: containment, disjointness,
adjacency, split and concatenation, each decided by comparing endpoints
(one `omega` or one `leb` verdict once the endpoints are numbers). Finite
unions of intervals (as sorted disjoint lists) form a Boolean algebra with
computable ∪, ∩, ∖, so a footprint is a value, and §1's solver handles the
membership goals left over. A **packing lemma**: sizes `s₀, …, sₖ` laid
out consecutively from a base are pairwise disjoint intervals at the
prefix sums, which is the shape of `Layout`, frames, scratch and the arena.

**Who waits.** `wp-view-separating-product` needs "a view local to a
footprint" and "disjoint footprints"; it owns the product of views and
should take its footprints from here. `x86-call-memory-footprints`, the
arena (`nh-heap`) and the ownership setup's `NoAlias` facts likewise. The
point-update laws of a store stay with `state-location-and-frame-kit`; this
issue owns only the sets of addresses.

## 5. Dataflow: checked post-fixpoints and Galois connections

**Today.** `lib/std/algebra/lattice.hthr` has meet and join semilattices
over `PartialOrderRel`; there are no monotone maps, fixpoints or Galois
connections anywhere in the library. Liveness is an analysis whose loop
sets are found by search and *checked* closed (`Homes::closed`,
`region_checked`, `native_alloc.hthr:296–320`), which is the right
principle (untrusted search, checked witness), but its soundness is proved
for liveness alone. `Ix::hi` (`lib/lang/facts/in_bounds.hthr`) is the upper
half of an interval analysis, proved for itself. The `known` facts the
segments carry (`List<Fact>`) are a third analysis.

**The theory.** A dataflow framework over the region tree: a lattice of
abstract values, a transfer per node, monotone; a *checked post-fixpoint*
at each loop head (`F(X) ⊑ X`, decided) is enough for soundness by Park
induction, so the solver stays untrusted and no least fixpoint is ever
computed in the proof. A Galois connection (or just a concretisation `γ`
with local soundness of each transfer) carries the result to the concrete
semantics. Forward and backward (liveness) instances.

**Why it matters.** Facts on demand (`docs/compilation-vision.md` §6.2) will
want many analyses: `InBounds`, `Unique`, `Writes`, constant propagation
across loops. With the framework, each is a lattice, a transfer, and one
local lemma per node kind; without it, each is a new global proof.

## 6. Numeric domains over words

**Today.** The `fits` premises of §2's no-overflow lemmas and the `InBounds`
facts are discharged by hand or by `omega` per site, and `Ix::hi` only
bounds from above over naturals.

**The theory.** Two abstract domains, proved sound once and plugged into §5:
*wrapped intervals* over `BitVec(n)` (sound under wrap-around and
signedness-agnostic; Navas, Schachte, Søndergaard, Stuckey, "Signedness-
agnostic program analysis", APLAS 2012) and *known bits* (tristate numbers,
as the Linux eBPF verifier uses; Vishwanathan et al., "Sound, precise, and
fast abstract interpretation with tristate numbers", CGO 2022, whose
multiplication was proved sound). Intervals discharge `fits` and
`InBounds`; known bits give alignment (low bits zero), shift and mask
facts. Needs §2 for wrapped arithmetic and §5 for the framework.

## 7. Separation algebras for ownership

The memory side of framing does not need a separation algebra: memory is a
total function, stores keep everything outside their span
(`X86Profile::store_outside`), so a predicate *local* to a footprint is
preserved by a store outside it. That is dynamic frames (Kassios, FM 2006)
rather than separation logic, and §4 plus `state-location-and-frame-kit`
give it.

Where a partial commutative monoid earns its place is **ownership**: the
ownership setup (`nh-ownership`, `ownership-discipline-over-code`) wants
"this function holds `xs` exclusively" as a resource that composes, splits
when a borrow is taken and recombines when it ends. That is a PCM
(exclusive ownership of footprints, read-shares later), with a separating
conjunction on predicates over it and a frame theorem. File it now so the
ownership round starts from the class rather than inventing one; build it
with that round.

## 8. Later theories

- **Sorting and permutations** (`sorting-order-theory`). `lib/lang/list_algos`
  has `Sorted`, `isort` and `count` at `Nat` only. `sort` (an `nh-heap`
  target) compares byte strings: it needs a lexicographic order on lists
  from an order on elements, proved a total preorder; `Sorted` generic in
  the relation; a permutation relation with its congruences; "two sorted
  permutations of one list are equal" under a total order (so a spec names
  the output); stability for keyed sorts.
- **Codecs** (`codec-round-trips`). `x86_64.hthr` proves a decoder
  round-trip per instruction form (`decode_instruction_of_rr_encoding`,
  `_mov_ri_`, `_setcc_`, `immediate_bytes_roundtrip`, …); utf8, ELF and the
  decimal reader repeat the pattern. Codec combinators (fixed-width
  little-endian fields, bit fields, sequencing, choice by tag) with
  round-trip and prefix-freeness proved once per combinator (Rendel and
  Ostermann's invertible syntax descriptions; Narcissus, ICFP 2019) would
  make a new instruction form a composition.
- **Independence of effects** (`effect-independence`). A reordering pass
  that consumes `Writes` facts (vision §3.2) needs: an independence relation
  on actions (disjoint footprints), trace equivalence as the congruence
  generated by swapping adjacent independent actions (Mazurkiewicz traces),
  and "equivalent traces have the same effect". `world-separable-frame` is
  the world-side analogue and should share the vocabulary.
- **Relational (2-safety) reasoning** for constant time is owned by
  `native-constant-time` (`docs/constant-time-survey.md`), which already
  reduces it to a one-run leakage transformer; nothing filed here.

## 9. Probes

Run with `heather check --cache` on the release binary at `a5d7cb5`;
`/mnt/project-files/native-math-survey/native_math_probes.hthr` holds them.

| Probe | Claim | Result |
|---|---|---|
| P1 | `ring` normalises word sums | refused: "`ring` proves an equation at `Int` or `Nat`, or a `≈` goal at a carrier with a `CommRingOfInt` instance" (§2) |
| P2 | `omega` reads `x.mod(8) < 8` | proved: a literal modulus is already in reach, so §2's congruences can lean on it |
| P3 | `ofNat(a) + ofNat(c) = ofNat(a + c)` at an open width | kernel: `NotConvertible`; no lemma states it (§2, `function-ir-pass-arithmetic-folds`) |
| P4 | `grind` proves `Mem(i, b) → Mem(i, (a ++ b) ++ c)` | refused: "the goal is not an equation, and the facts hold no contradiction" (§1) |
| P5 | the same goal by the list kit | proved, one `mem_append_l` around one `mem_append_r`: the step §1 automates |
| P6 | `toNat(a + b) = (toNat a + toNat b) mod 2^n` by `omega` | stuck: CutSat's model sets the `mod` atom to 0 and the sum to 1, since nothing links them (§2) |

## 10. Where each issue sits

Areas and milestones are set on the issues; `scripts/issue show <slug>`
prints them. In short: §1 is `tactics` (a decision procedure), §2–§8 are
`mathematics`, and each names the native milestone it serves (`hih-passes`,
`hih-memory-model`, `nh-front`, `nh-heap`, `nh-ownership`).
