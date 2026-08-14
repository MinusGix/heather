---
title: Datarepr: kernel representation vs runtime representation
status: open
labels: [compiler,design,runtime]
created: 2026-07-24
updated: 2026-08-14
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
(docs/sketches/surface-v2.md has variants):

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
  (docs/branching-inductives-choice.md §3, [[tier1-branching-constructors]])
  — do not re-admit "the encoding is big/slow" as an argument there.
- The flat-IR escape hatch is off the table for the same reason: the IR
  datatype is a spec object chosen for provability.
- If route A (W + funext) were taken there, stuck `transport`s in
  kerneltime terms would be datarepr's problem at the boundary:
  representation-preserving coercions can compile to no-ops, certified in
  `equiv`. (Noted 2026-07-24 discussion; nothing depends on it yet.)

## Open

- Shape of the datarepr class and its refinement statement.
- Interaction with intensional instance keying (instances key on syntax —
  [[compile-typeclass-design]]): does datarepr key on the type's
  declaration the same way?
- Default instances: derived naive representation for every inductive, so
  `runtime_fn` works out of the box before anyone hand-tunes?

## Log

- 2026-08-13: Two notes from the showcase critique (2026-08-13). (1) The open item "default instances: derived naive representation for every inductive" is confirmed wanted, but naive need not be the DEFAULT — the default may be a smarter auto-pick; spelling sketched as `datarepr List<A> = repr::inductive_repr();` where a meta-program inspects the declaration and picks (e.g. linear vec for list-shaped, boxed tree only as fallback) — consistent with generators-in-the-language. Even naive Nat can beat unary by a general induction-pattern recognizer without reaching for GMP. (2) The iterator question landed here: [[iterators-as-list-repr]] — iterators as a lazy repr of List with certified fusion, spec side stays List; its open half is API-naturality (cost-honest signatures per repr).
- 2026-08-14: Design discussion IN PROGRESS (user + coordinator, pre-round; nothing final until the round charter). Leanings so far: (1) the refinement obligation is ABSTRACTION FUNCTION + INVARIANT (abs: Repr -> Spec total kernel-side, inv: Repr -> Prop), NOT an iso — non-surjectivity is what absorbs machine finiteness, so no bignum-style always-available fallback; partiality moves into per-operation outcomes (v' + OutOfMem) or preconditions, per-operation policy. (2) TWO BASES, kept distinct: a correctness basis (constructor images + a fold refining the recursor — must exist as the certificate anchor, need not be what runs, transfers every structurally-defined spec fn) and a cost basis (push/index-style hand overrides in an open per-operation Impl registry, each with its refines theorem). (3) Effect bubbling: +OutOfMem appears ONLY on repr-side Impls, composing monadically in that generated layer; the spec fn stays pure forever. Nonsense-error accumulation handled by a strengthening ladder: generated weak certificate first, manual theorem erasing the OutOfMem arm under a bound later — degrees of honesty, soundness never at stake. (4) The transfer engine is a CERTIFYING GENERATOR (certgen's sibling, untrusted-by-construction, in Heather per generators-in-the-language; no unrestricted implemented_by ever). (5) Platform model: the checked failure is bound-violation/reported-alloc-failure; OS overcommit means actual exhaustion is OUTSIDE the semantics, a recorded trusted-boundary assumption like fuel. (6) Layout is DATA: a Rust-flavored surface (Box for indirection, real field order) elaborates to a programmatic layouting value users can replace, so arcane hand layouts prove the same obligations; C-ABI mimicry is a target-indexed carrier property, v2+. (7) v1 needs none of the byte level: named reprs + abs/inv + structural obligations over the Nat IR, naive repr made official — the certgen parameterized-instantiations customer needs only this. Literature downloaded to docs/: coqeal-refinements-for-free-cpp2013.pdf (parametricity transfer), lifting-transfer-huffman-kuncar-cpp2013.pdf, autoref-lammich-itp2013.pdf, fiat-adt-synthesis-popl2015.pdf. Still to settle before the charter: explicit confirmation of abs+inv over iso; outcome-vs-precondition default policy; whether multi-repr-per-program (with certified boundary conversions) is v1 or deferred.
- 2026-08-14: Discussion round 2 (user + coordinator): DECIDED — (1) abs+inv over iso is CONFIRMED by the user. (2) Partiality policy resolved by SOURCE: input-determined partiality (index bounds) is a PRECONDITION, canonical, with auto-dispatch from context and a block-level dispatch mode deriving the runtime-checked Result form when the condition is decidable; machine-state-determined partiality (alloc failure) is an OUTCOME TYPE, forced (no argument-side proof can discharge the model's may-fail), erasable only by the strengthening ladder under an explicit capacity bound. Pending user confirmation of this split as the default. (3) Multi-repr deferred-not-killed; guardrails recorded: inter-repr conversions are ordinary certified Impls (abs_B(conv(r)) = abs_A(r)), NEVER compiler-inserted, and the via-naive composite is never inserted silently either; defaults-at-runtime_fn-boundary vs inferred-with-defaults stays open. ALSO AGREED: the via-derived proof route is first-class (a custom Impl may certify by same-domain equivalence to the correctness-derived Impl, taking its certificate by transitivity — the derived body plays certgen's hand-run role); Repr-with-operation-members and Impl both get dedicated surface syntax (a datarepr declaration form) elaborating to the class-level truth, since a bare instance cannot name operations today; '+ OutOfMem' stays surface intent over a plain sum, not a type-theory commitment (graded reading belongs to [[effects-direction]] if ever). The 4GB-envelope aside filed as [[memory-bound-certificates]]. Remaining before the round charter: user's yes/no on the partiality split; everything else (spellings, keying, generator integration) is the round's job.
