---
title: Datarepr: kernel representation vs runtime representation
status: open
labels: [compiler,design,runtime]
area: heather-in-heather
milestone: [hih-memory, nh-heap]
created: 2026-07-24
updated: 2026-10-28
---



Decided in discussion (2026-07-24), recorded here because it keeps getting
re-derived: **the representation the kernel checks is not the representation
that runs.** Inductive types are specification objects; runtime data
structures are chosen separately and linked by certified refinement — the
same discipline as Isabelle's `code_datatype` + refinement lemmas or
CakeML's translator, and the sound version of what Coq's
`Extract Inductive nat => int` does by fiat. Canonical example: unary Peano
`Nat` for reasoning, GMP-style `Nat` at runtime.

## Execution model this sits inside

Ordinary `fn`s are **kerneltime**: they are the mathematics side, evaluate
by kernel computation ("a distinct sort of computable"), and are never
themselves compiled. Only `runtime_fn` crosses to hardware. Sketch
(docs/archive/surface-v2.md has variants):

```heather
fn blah(x: Nat) -> Nat { … }             // 1. ordinary kerneltime code

fn blah_ir() -> List(Instr) {
    lower(blah.code)                     // 2. cross the boundary: syntax as data
}

instance Compile[Cpu] for blah {
    fn ir() -> List(Instr) { blah_ir() }
    theorem equiv(x: Nat):               // 3. certify against the interpreter
        simulate(ir(), [x]) == Some(blah(x)) { … }
}

runtime_fn main() { blah(7) }            // 4. run via any in-scope certificate
```

`main` is special only to the compiler (itself a Heather kerneltime
library): it does typeclass inference for `Compile[Target]` instances over
the call graph and emits their certified IR. The `Compile` class itself is
owned by [[compile-typeclass-design]]; `simulate`/IR by
[[ir-simulate-design]]. This issue owns the **representation** layer:

- A **datarepr typeclass** (name tentative) picks the runtime
  representation of each inductive. `runtime_fn` uses it by default and
  requires it in the background — the user's mental sketch, to be worked
  out here.
- The refinement obligation: datarepr instances carry the proof linking
  runtime operations to the spec inductive's constructors/eliminator
  (shape TBD — iso? simulation relation per operation?).

## Consequences already being relied on

- Efficiency of *kernel* encodings is off the ledger entirely: unary
  heights, Σ-of-Units tags, O(n) numerals never run. This is load-bearing
  for the branching-inductives decision
  (docs/inductives/branching-inductives-choice.md §3, [[tier1-branching-constructors]])
  — do not re-admit "the encoding is big/slow" as an argument there.
- The flat-IR escape hatch is off the table for the same reason: the IR
  datatype is a spec object chosen for provability.
- If route A (W + funext) were taken there, stuck `transport`s in
  kerneltime terms would be datarepr's problem at the boundary:
  representation-preserving coercions can compile to no-ops, certified in
  `equiv`. (Noted 2026-07-24 discussion; nothing depends on it yet.)

## Open

- Multirepr within one function (deferred with §5.3's trigger): the
  one-repr-per-closure default is an assumption, not a ceiling — any actual
  conversion function holds two reprs of one spec type, so the activation
  round must make mixing at least workable ("assume same repr" ambient,
  mixing explicitly entered). Ratified 2026-08-15, sharpenings in §5.3.
- Decider provenance for the decide-and-bubble rung (§2.5e) — to be picked
  *with* [[class-ops-prop-vs-bool]] at the first outcome-path round.
- Spec-side quotient types, if multiset-flavored programs arrive
  (FINDING 3, §6.4) — recorded pressure, not this issue's design.

Settled by the doc and the two review passes (previously open here): the
class shape and refinement statement (§1, FINDING 1 ratified); keying
(§4, ratified); default instances (naive by fiat in v1, auto-pick
meta-program v2+, naive always mintable — §5.1–5.2, ratified); reprgen
architecture (§3, ratified); Bin-as-repr-of-Nat v1 stretch (§5.1,
ratified); the repr-typed-result transfer (implemented, §3.3's second
as-landed note); multi-repr defaults at the runtime_fn boundary and conversions
as ordinary certified Impls (§5.3, ratified with sharpenings — see Open).
Also settled: via-derived's obligation is the weak abs-image form, carrier
equality its congruence discharge, canonical-form `inv` the opt-in that
makes them coincide (user-confirmed 2026-08-15; doc §1.2 restated in
place). The v1 charter itself is spent: both halves are in-tree.

## Log

- 2026-08-13: Two notes from the showcase critique (2026-08-13). (1) The open item "default instances: derived naive representation for every inductive" is confirmed wanted, but naive need not be the DEFAULT — the default may be a smarter auto-pick; spelling sketched as `datarepr List<A> = repr::inductive_repr();` where a meta-program inspects the declaration and picks (e.g. linear vec for list-shaped, boxed tree only as fallback) — consistent with generators-in-the-language. Even naive Nat can beat unary by a general induction-pattern recognizer without reaching for GMP. (2) The iterator question landed here: [[iterators-as-list-repr]] — iterators as a lazy repr of List with certified fusion, spec side stays List; its open half is API-naturality (cost-honest signatures per repr).
- 2026-08-14: Design discussion IN PROGRESS (user + coordinator, pre-round; nothing final until the round charter). Leanings so far: (1) the refinement obligation is ABSTRACTION FUNCTION + INVARIANT (abs: Repr -> Spec total kernel-side, inv: Repr -> Prop), NOT an iso — non-surjectivity is what absorbs machine finiteness, so no bignum-style always-available fallback; partiality moves into per-operation outcomes (v' + OutOfMem) or preconditions, per-operation policy. (2) TWO BASES, kept distinct: a correctness basis (constructor images + a fold refining the recursor — must exist as the certificate anchor, need not be what runs, transfers every structurally-defined spec fn) and a cost basis (push/index-style hand overrides in an open per-operation Impl registry, each with its refines theorem). (3) Effect bubbling: +OutOfMem appears ONLY on repr-side Impls, composing monadically in that generated layer; the spec fn stays pure forever. Nonsense-error accumulation handled by a strengthening ladder: generated weak certificate first, manual theorem erasing the OutOfMem arm under a bound later — degrees of honesty, soundness never at stake. (4) The transfer engine is a CERTIFYING GENERATOR (certgen's sibling, untrusted-by-construction, in Heather per generators-in-the-language; no unrestricted implemented_by ever). (5) Platform model: the checked failure is bound-violation/reported-alloc-failure; OS overcommit means actual exhaustion is OUTSIDE the semantics, a recorded trusted-boundary assumption like fuel. (6) Layout is DATA: a Rust-flavored surface (Box for indirection, real field order) elaborates to a programmatic layouting value users can replace, so arcane hand layouts prove the same obligations; C-ABI mimicry is a target-indexed carrier property, v2+. (7) v1 needs none of the byte level: named reprs + abs/inv + structural obligations over the Nat IR, naive repr made official — the certgen parameterized-instantiations customer needs only this. Literature downloaded to docs/: coqeal-refinements-for-free-cpp2013.pdf (parametricity transfer), lifting-transfer-huffman-kuncar-cpp2013.pdf, autoref-lammich-itp2013.pdf, fiat-adt-synthesis-popl2015.pdf. Still to settle before the charter: explicit confirmation of abs+inv over iso; outcome-vs-precondition default policy; whether multi-repr-per-program (with certified boundary conversions) is v1 or deferred.
- 2026-08-14: Discussion round 2 (user + coordinator): DECIDED — (1) abs+inv over iso is CONFIRMED by the user. (2) Partiality policy resolved by SOURCE: input-determined partiality (index bounds) is a PRECONDITION, canonical, with auto-dispatch from context and a block-level dispatch mode deriving the runtime-checked Result form when the condition is decidable; machine-state-determined partiality (alloc failure) is an OUTCOME TYPE, forced (no argument-side proof can discharge the model's may-fail), erasable only by the strengthening ladder under an explicit capacity bound. Pending user confirmation of this split as the default. (3) Multi-repr deferred-not-killed; guardrails recorded: inter-repr conversions are ordinary certified Impls (abs_B(conv(r)) = abs_A(r)), NEVER compiler-inserted, and the via-naive composite is never inserted silently either; defaults-at-runtime_fn-boundary vs inferred-with-defaults stays open. ALSO AGREED: the via-derived proof route is first-class (a custom Impl may certify by same-domain equivalence to the correctness-derived Impl, taking its certificate by transitivity — the derived body plays certgen's hand-run role); Repr-with-operation-members and Impl both get dedicated surface syntax (a datarepr declaration form) elaborating to the class-level truth, since a bare instance cannot name operations today; '+ OutOfMem' stays surface intent over a plain sum, not a type-theory commitment (graded reading belongs to [[effects-direction]] if ever). The 4GB-envelope aside filed as [[memory-bound-certificates]]. Remaining before the round charter: user's yes/no on the partiality split; everything else (spellings, keying, generator integration) is the round's job.
- 2026-08-14: Discussion round 3, closing the pre-charter phase: the user CONFIRMS the input-determined-vs-machine-state partiality split (noting it is forced by the fundamental alloc-like function whose IR carries the OutOfMem possibility; a push proof can erase it relative to the machine model given no-resize), and confirms the syntax and multi-repr positions. The floated THIRD class (machine-width side conditions, e.g. index-fits-isize) is resolved as a DISPATCH POLICY, not a semantic class: width conditions are preconditions in kind, but (a) most are SUBSUMED BY inv and never surface (inv already bounds len, so i < len implies i fits — the repr invariant pays for the width facts inside a maintained repr), and (b) those that genuinely surface at boundaries default to DECIDE-AND-BUBBLE — the condition is decidable, so the generated layer emits the runtime check and bubbles the failure arm through the same plumbing as OutOfMem (the user's decide_result tactic is this rung exposed to users) — with the asymmetry that a bubbled width condition is ALWAYS erasable in principle by discharging the precondition, where OutOfMem is erasable only relative to an assumed capacity. Dispatch ladder: silent discharge from context/inv > decide-and-bubble > manual; per-condition default is the knob. ALL pre-charter questions are now settled; the design round may be chartered. Edge-case semantics acknowledged as the round's roughest part — the charter should name it.
- 2026-08-14: **Design round: docs/native/datarepr-design.md landed** (sections: §1 class semantics/Impl registry, §2 partiality+dispatch worked on index/push/Nat→u64, §3 the transfer generator "reprgen", §4 keying, §5 staging, §6 the sorted-bag falsifier, §7 literature, §8 rejected alternatives). Three FINDINGS: (1) constructor images cannot all be total on machine-finite carriers — resolved as *consumption total, construction under the partiality policy* (§1.3); (2) naive-repr availability is not the rejected bignum fallback — operational vs semantic (§8); (3) the bag falsifier survives by declining — order-forgetting reprs need spec-side quotients, pressure recorded at that door (§6.4). RECOMMENDED (not decided): per-closure error sums at the runtime_fn boundary; rung dispatch declared per Impl definition; declaration-syntax keying both layers; multi-repr defaults at the runtime_fn boundary; Bin-repr-of-Nat as v1 stretch. The "## Open" list above now reflects the doc. Literature verdicts in §7.5; Lifting/Transfer's right-totality (and its partial-quotients-get-no-code cost) is the clearest deliberate divergence.
- 2026-08-14: User live-read of docs/native/datarepr-design.md secs. 1-2 (2026-08-14), verdicts recorded: FINDING 1 RATIFIED (constructors have to be limited; consumption-total stands). Sec. 2.5 items: (1) per-closure error sums LIKED; (2) RATIFIED as declared-per-Impl, explicitly not wholly automatic ('this API can do an out of mem' is sane); (3) not wholly sure, stays open; (4) wants a concrete sketch beyond the always-Err control note; (5) CONFIRMED with a sharpening logged on [[guarded-to-option-adapter]]: rung-2 deciders must be runtime-computable (Compile-bearing when used for compilation) — Decidable alone is not sane-to-run. Sec. 2.4 writer-declares-the-rung: confirmed (matches 2.5(2)). Smaller notes: Out flipped to Out<T, E> in the doc (done); the 'sub-repr' coinage in 2.5(3)/2.3 is questioned — prefer 'a repr with a stronger inv' or a value-plus-proof reading, no new concept; the fold algebra type deserves its own name; a more first-class 'impl fn VecList::length' spelling is wanted if the refines proof can attach cleanly; datarepr-as-metaprogram-over-inductive-fields (MultiArrayList-style) noted as the direction 1.4 should stay compatible with; Nat-as-u64 disliked as an example repr (Nat's value is unlimitedness) though the finding stands. Two issues spun off: [[unnameable-generated-names]] (generated names unnameable-by-default, # sigil sketch), [[guarded-to-option-adapter]]. Secs. 3-8 review pending; nondeterminism-of-machine-state question raised, answered in discussion (refines is arm-wise so it never predicts the arm; determinism-relative-to-threaded-machine-state is simulate's natural v2 shape; effects-direction owns the full route).
- 2026-08-15: **Review pass 2 (secs. 3-8, user skim-read): all remaining RECOMMENDED items RATIFIED.** §3 reprgen phases ratified ("neat"), with the noted wrinkle that an eventual pure-Heather self-hosting of the generator makes the phase machinery trickier — no action now. §4 keying ratified, including the avoided instance-flapping failure mode. §5 naive repr ratified exactly as the doc stages it: always available to mint, dev-time default in v1, NOT the long-term actual default (auto-pick v2+). §5.1 Bin "a great test target". §5.3 ratified with two sharpenings (now in the doc): (a) one-repr-per-closure is the default assumption, not a ceiling — conversion functions inherently hold two reprs, so multirepr-within-one-function must be designed at-least-workable at activation (new Open item); (b) any future automatic conversions ride the language's general auto-conversion mechanisms (some repr pairs are near-free to swap), never repr-specific compiler insertion. Defaults-bind-at-runtime_fn-boundary accepted as "very typeclass-esque". The doc's RECOMMENDED items are now all decided; the Open list is reduced to the v1 charter plus the deferred design questions.
- 2026-08-15: **v1 first-half round chartered** (§5.1 items 1–4; reprgen = second half) **and its verification probe fired the stop-condition.** Probes: (a) the class/instance sugar hosts the Repr record incl. theorem-valued fields, but §1.1's fold_law sketch had `adapt` on the recursor side — kernel-probed `NotConvertible`; corrected in the doc (adaptation runs spec-step→repr-ward only, `abs` at the child; naive stays `refl`). (b) The `plen`/`TksP<Nat>` decline (crates/elab/tests/certgen_tier1.rs) is genuinely name-availability-shaped — hand-monomorphized it generates today; the flip is deliverable. (c) REFUTED: `calc.hthr`'s `run` is not one decline away — four independent certgen widenings block it even hand-monomorphized (ledger now on [[certifying-generator]]'s status header). Re-charter: item 3 narrows to mint-the-name+embed and the fixture flip; the `run` acceptance is dropped from v1 (doc §5.1 item 3 as-landed note; docs/showcase/README.md `run` row corrected). Items 1, 2, 4 unaffected; round continuing.
- 2026-08-15: **v1 first half implemented and green; the issue stays open for the second half and the runtime seam** (crates/elab/src/datarepr.rs + tests/datarepr.rs; narrative and all deviations in docs/native/datarepr-design.md's as-landed notes on §1.2, §1.4, §4, §5.1). Both `datarepr` forms, `repr::naive()`, `impl f for Rp`, the certgen minting flip (`plen`/`TksP<Nat>` emits, decline preserved unminted), and the `Bin` stretch with both Impl routes. Suite 1500 → 1521, bench clean. Spun off: [[theorem-field-projection-oom]], [[receiver-method-shadows-record-field]]; new Open item above on via-derived's availability (the §1.2 as-landed FINDING); nameable-names deviation logged on [[unnameable-generated-names]]. Second half (reprgen) is the next charter.
- 2026-08-15: **v1 second half (reprgen) implemented and green; v1 is complete except the repr-typed-result transfer** (crates/elab/src/reprgen.rs + tests/reprgen.rs; narrative in docs/native/datarepr-design.md's as-landed notes on §1.2 restated, §3.1, §3.3, §5.1). Phases 0–4 emit derived bodies + closing induction + refines + the registering impl over both naive and Bin reprs, §3.5's mutation controls in place (forced emission at Bin deliberately, since the naive carrier is the spec type). Three §3.1 corrections found by the hand-run before code (the closing lemma is an induction, not conversion; explicit `j` motives where anti-unifying cong can't generalize inside the algebra; phases 0/1 interleave). Five named declines at §3.3, incl. the recursive-child-outside-self-call refusal that is invisible at naive and was a live bug at Bin. New Open items above: the repr-typed-result stage (with its previously-undescribed third lemma, `inv`-preservation of the fold) and callee-Impl resolution. Suite 1521 → 1531, bench clean.
- 2026-08-15: **The repr-typed-result stage lands; v1 is complete.** A spec fn
  returning `S` now transfers (`crates/elab/src/reprgen.rs`), so arithmetic at
  `Bin` is in reach — `double_spec` generated end to end. Narrative, the three
  lemmas, the one part of the estimate that was wrong (no per-repr `abs`
  congruence is needed), the new image-spine fragment predicate and a recorded
  limit of one mutation control: docs/native/datarepr-design.md §3.3, second as-landed
  note (§3.1's deferred datatype note amended too). New fixture `BinC` — `Bin`
  under a canonical-form `inv` — is where `inv`-carrying obligations are now
  controlled; it shares the carrier with `Bin` in `crates/elab/tests/support`.
  Spun off rather than fixed drive-by:
  [[reprgen-self-call-args-unchecked]]. Suite 1531 → 1541, bench clean.
- 2026-08-15: **Callee-`Impl` registry resolution lands; §3.1 phase 0 is complete.** A callee that touches `S` is now resolved against the registry, transcribed to its `Impl`'s body on the repr side, and closed in the certificate by that callee's `refines` (and `refines_inv` where it returns `S`); a callee with no `Impl` that is in the fragment is generated first, in the same emission, in topological order. Narrative and the four findings in docs/native/datarepr-design.md's third as-landed note on §3.1 (and the sharpened §3.3 bullets). The load-bearing one, found by the hand-run before code: an arm's algebra is spelled once and typed twice, so a callee is spelled through its `Impl` on BOTH sides and the bridge to the spec function is built in the closing induction, not at the anchor law — from which the charter's expected `inv`-hereditarity obligation turns out NOT to be owed (its only customer is the recursive-child shape, refused on typing grounds first), so no `Repr` field is added and §1.1/§1.4 are untouched. The schema-datatype verdict stands negative a second time: a resolved callee is a second spine node kind with the same four slots and the proof walk gains no branch. Provenance-indifference is tested, not asserted (byte-identical caller emission over a generated vs. a hand-written callee `Impl`). Spun down rather than fixed: [[reprgen-self-call-args-unchecked]] closed — its sibling half fixed here, its headline half unreachable (the elaborator's own recursion check refuses it first). Suite 1541 -> 1553, bench clean.
- 2026-08-15: Surface ergonomics audit filed as [[datarepr-surface-ergonomics]] (user request): probed against the CLI — the fixtures' curried/annotated fold spelling is optional today (n-ary + unannotated multi-binder λ check), and the genuine gaps are ranked (no surface syntax for transfers + named-artifacts-only impl clauses as the headline design round; fold-via-abs defaulting as the small one).
- 2026-08-15: Surface note (2026-08-15): §1.2's Impl registry gained its designed surface via the obligation-records round (docs/language/classes/obligation-records-design.md; pointer added at the design doc's §1.2) — inline clauses, the ? reporting hole, ':= derive()' (the first surface-requested transfer), via_derived(p), and provenance on registry entries. No change to this issue's Open list; the registry semantics were already settled here.
- 2026-10-28: Proof repair survey (2026-10-28): a canonical-form `inv` repr is the paper's algebra isomorphism, and abs+inv is its strict generalisation (`docs/surveys/proof-repair-algebra-survey.md` §3). It filed [[reprgen-recursive-child-via-embedding]].
- 2026-11-05: gardener: cites a file it shares with [[datarepr-guarded-images]] (`crates/elab/src/datarepr.rs`); [[datatype-container-algebras]] (`docs/surveys/proof-repair-algebra-survey.md`); [[surface-syntax]] (`docs/archive/surface-v2.md`).
