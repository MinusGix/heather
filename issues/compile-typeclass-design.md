---
title: Design the Compile typeclass and certificate coupling
status: open
labels: [compiler, typeclass, design]
blocked-by: [ir-simulate-design]
created: 2026-07-22
updated: 2026-09-07
---

The certifying-compilation contract: a function is compilable iff it has a
`Compile` instance containing (a) IR production and (b) an `equiv` theorem
that the IR simulates to the same result as the kerneltime function. The
compiler consumes only proof-carrying instances — privileged operationally,
never logically.

## Current runtime eligibility policy (2026-09-07)

A function must have a handwritten `Compile` instance or an explicit marker that
synthesizes one. There is no automatic derivation for unmarked functions. This
supersedes the 2026-08-13 log's “annotate nothing” proposal and its interpretation
of the marker as merely an optional eager assertion. [[runtime-compile-opt-in]]
owns implementation; marker spelling remains open. [[runtime-extern-c-abi]] owns
explicit foreign ABI selection, independently of the native default convention.

Settled so far:

- Coupling via same-typeclass membership is sufficient (equiv need not
  literally reference a sibling field); producing IR standalone without a
  source function stays legitimate.
- Multiple targets: index the class by target — `Compile[Cpu] f`,
  `Compile[Gpu] f` — rather than allowing multiple instances of one class.
  Coherence per (f, target); target selection is instance resolution, not
  ambiguity-breaking.
- Instances are keyed on *syntax* (boxed code is intensional), so
  coherence is per-syntactic-definition and refactoring a function
  invalidates its instance. Deliberate choice, not an accident.

Open: whether "typeclass" is even the right notion here vs. something more
bespoke; revisit once the kernel exists.

## Log

- 2026-07-23: Surface-syntax round 1 leaning recorded (docs/sketches/surface-v1.md §6): dictionaries are first-class values (records over Σ), so trait-vs-typeclass is purely resolution policy; lean coherent-by-default (canonical instances suit certifying compilation and intensional instance keying), explicit named dictionaries as the multiple-structures escape. Full design still owned by this issue.
- 2026-07-23: Round-2 sketch adds: let instance C for T = v; scoped override — safe specifically because instances are certificate-carrying (semantics pinned by equiv proof; instance choice is operational, coherence = predictability not soundness). Resolution-from-main composes: compiler walks the call graph resolving in-scope instances per site. Also surfaces the elaboration-determinism requirement implied by keying on elaborated syntax (.code).
- 2026-07-23: Round-3 sketch: ctx-parametric instances (ir(ctx: CallCtx)) with forall-ctx equiv — specialization certified by one theorem, not per copy; artifact dedup keys on (function syntax, ctx descriptor); descriptor coarseness is the design lever (CallCtx shape is an [[ir-simulate-design]]-adjacent decision). Context facts may include caller proofs (e.g. bounds evidence) so ir() may optimize justified-by-theorem.
- 2026-07-26: Blocked in practice on two now-filed prerequisites rather than on design: [[surface-records]] (a trait is a record; the surface has no record form) and [[surface-polymorphism]] (a trait is a record of GENERIC operations, and there are no type parameters on fn/theorem today). Roadmap items 11-12; this issue picks up after them.
- 2026-08-01: **Design round (docs/compile-typeclass-design.md).** [[ir-simulate-design]] closed today, so this unblocked; the sketch answers the standing open question — typeclass vs bespoke — by splitting it on the logical/operational line: the LOGICAL content of an instance is an ordinary record value (dependent fields = the certificate type mentions the IR fields; Converges in the ∃-form is the certificate, as ir_v1's own log predicted), and the OPERATIONAL content (resolution, coherence, [Cpu] indexing, .code keying) is deferred to the round that builds a resolver, each item recorded with its prerequisite. v1 shape: record CompileNat2(f: Nat -> Nat -> Nat) { prog, entry, cert } — per-signature, embeddings baked in, coupling by value parameter; the generic story stays with [[generators-in-the-language]]/[[datarepr-separation]]. Acceptance sketch §7: declare it, check add_instance (which IS [[end-to-end-compile-instance]]), negative controls, and a second instance for the same spec through a different IR to demonstrate coherence-is-policy.
- 2026-08-01: **Implementing round, same day — §7's acceptance lands in full.** lib/ir_v1.hthr gains `CompileNat2(f: Nat -> Nat -> Nat) { prog, entry, cert }` (item 1), `add_spec` + `add_instance` — the milestone value, prog = add_chain(), entry = ir_call2(), cert = add_converges_through_calls repackaged (item 2, closing [[end-to-end-compile-instance]]) — and `add_instance_loop`, the second instance for the SAME spec through ir_loop() directly (item 4: coherence demonstrated as policy — two values of one type, semantics pinned by both certificates). Item 3's controls ride inside crates/elab/tests/ir_v1.rs's full-library test: a wrong-result spec under the real certificate and a wrong entry under the real certificate are both refuted, so the coupling (spec by value parameter, entry substituted into cert's type) is doing work rather than decorating. Cost: +0.35s release (34.1s), +5s debug (203s of the 300 CPU-s rail; header note updated). What stays open here: the class layer (§5 — resolution, [target] indexing, .code keying, ctx-parametric instances), each recorded with its prerequisite; CallCtx descriptor shape is the standing design question.
- 2026-08-07: 2026-08-07: The class layer (§5) is SUPERSEDED by the general traits design ([[traits]], docs/traits-design.md): resolution-from-main becomes 'the compiler is one client of the general resolver'; [Cpu] target indexing is STRUCK — Compile certifies function→IR and the IR is arch-agnostic, so arch belongs to the IR→native stage ([[datarepr-separation]]), and class indexing dissolves into ordinary record parameters anyway; let-instance and .code keying carry over into that design's §5/§6. Also corrected: §6's 'blocked on the level-1 record round' was stale — bundled records landed 2026-07-27 (universe.rs); the remaining blocker for signature-generic Compile is per-type embeddings only. CallCtx stays owned here.
- 2026-08-13: Discussion (2026-08-13, showcase critique) on how the target reaches Compile. Keep the target as a PARAMETER/index rather than a bare Compile chosen by ambient platform conditions: cross-compilation needs instances for several targets held simultaneously, and artifact caches key on target. But the index should be a *description* — a record of target facts (word size, endianness, ISA features) — not a nominal tag, so one instance can be generic over "any 64-bit LE target" with conditional instances discriminating within the indexed form; that subsumes the conditional-instance reading and gives fn-level compile access to compile-time target facts (the trait-view raised in discussion: special features exposed at the IR level, variation by target). Derivation spelling agreed leaning: `instance Compile for f := derive_runtime_fn(f);` — an instance whose value a meta-function computes, no derive keyword; matches this issue and certifying-generator's eval(generate(box f)) guess. The lazy/eager split: the compiler's walk from main demands instances with a default deriving rule (annotate nothing), while marking a fn runtime_fn is an eager per-declaration assertion for error locality only.
- 2026-08-14: Datarepr keying answered (docs/datarepr-design.md §4, RECOMMENDED): Repr keys on the spec inductive's elaborated declaration, Impl on (fn's .code identity, repr name) — the same intensional bargain as Compile, for the same cache-predictability reason; definitionally-equal-but-distinct types bridge only by explicit certified conversion Impls.
- 2026-08-25: The first concrete native-target owner is [[x86-64-machine-model]]: it defines the canonical relational target contract and typed-instruction/encoding seam downstream of FunctionIR. This issue continues to own source-function-to-IR certificate packaging; it assumes only that a later lowering can target that separately reviewed machine relation.
