---
title: Design the Compile typeclass and certificate coupling
status: open
labels: [compiler, typeclass, design]
blocked-by: [ir-simulate-design]
created: 2026-07-22
updated: 2026-08-01
---

The certifying-compilation contract: a function is compilable iff it has a
`Compile` instance containing (a) IR production and (b) an `equiv` theorem
that the IR simulates to the same result as the kerneltime function. The
compiler consumes only proof-carrying instances — privileged operationally,
never logically.

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
