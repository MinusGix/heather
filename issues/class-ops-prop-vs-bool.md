---
title: Class operations across the kerneltime/runtime split: Prop laws, Bool programs, certificates between
status: open
labels: [design,traits,compiler,stdlib,delam]
created: 2026-08-07
updated: 2026-08-17
---

From reviewing `Cmp<A>` (`le : A -> A -> Bool` with `= True` laws,
2026-08-07). The question "should `le` return `Bool` or `Prop`?" dissolves
differently in Heather than in Lean, because a mathematical function and the
evidence that it has executable code are separate objects.

Current lean (2026-08-09): the public mathematical API should contain **one
propositional relation** — `le : A -> A -> Prop` (or plausibly `SProp` where
irrelevance is wanted). A raw mathematical instance need not be decidable. An
executable instance gives that same `le` a `Compile` instance whose runtime
representation and correctness theorem implement the decision. There need not
also be a public `leb : A -> A -> Bool`; in many Lean APIs that function is an
artifact of making computation visible in the mathematical interface.

This makes the default split:

- **Specification:** `le : A -> A -> Prop`, used by all mathematical laws and
  notation.
- **Execution evidence:** a `Compile` instance for that predicate, carrying
  whatever Boolean/runtime representation and semantic relation says that the
  result decides `le(x, y)`.
- **Optional reification:** a named Boolean/reflection object only where a
  mathematical consumer genuinely needs to manipulate the Boolean function
  itself (Boolean algebra, circuits, finite automata, short-circuit structure,
  reflection proofs), not merely in order to run the proposition.

The landed `Cmp` (Bool plus `= True`) remains an honest v1: it inlines the
specification into its decision procedure. A future migration should not be
designed until the questions below determine whether it becomes the
proposition-facing order class, a deliberately reified decided refinement, or
temporary compatibility surface.

Open sub-questions, recorded not answered:

1. **Logical decidability versus runtime compilability.** A value of
   `Decidable(p)` permits kerneltime case analysis into `p + not p`; a Compile
   instance supplies executable code and a correctness theorem. Does Compile
   canonically induce `Decidable`, does it only induce a runtime branching
   interface, or are those intentionally different claims?
2. **Representation of a compiled proposition.** Is `Prop` represented by
   `Bool` through the general Datarepr/refinement machinery, or does compiling
   a proposition need a predicate-specific certificate shape? Owned on the
   compilation side by [[datarepr-separation]] and
   [[compile-typeclass-design]].
3. **Source branching.** What evidence must `if p { ... } else { ... }` demand
   when `p : Prop`: logical `Decidable(p)`, executable `Compile(p)`, or a small
   interface both can provide?
4. **Explicit reflection.** If a library really needs `b : Bool` together with
   `b = True <-> p`, is that an ordinary record constructed from Compile, a
   class, or simply a theorem about a separately named Boolean function?
5. **Class dictionaries.** What does a Compile instance for a relation
   projected from a class dictionary look like: per concrete instance,
   parametrically from compiled fields, or attached to the dictionary value?
6. Whether `SProp` fields in classes interact with record lowering or
   elimination restrictions today.

## Log

- 2026-08-09: Direction corrected in the high-level library discussion. The
  preferred default is no parallel `leb`: state the mathematical relation once
  in Prop/SProp and let a Compile instance provide its executable decision.
  A reflected Bool function must justify itself as mathematical data. The
  remaining design seam is whether logical decidability and runtime
  compilability share one consumer interface or remain distinct evidence.
- 2026-08-09: Rider from the algebra.hthr cleanup review (2026-08-09): a symbol spelling for Cmp's le belongs to this issue, not to a designation today — <= already lexes and means Le, the proposition, at the non-associative comparison rung, so designating <= at a carrier to the Bool-valued le would make x <= y a Bool in one file and a Type in another. The right home is the bridge this issue designs: the spec-side class owns <=, and the decided refinement stays named (leb/le) until then.
- 2026-08-16: **Direction settled in the std-API design discussion, and sub-questions 1–3 answered.** The user's position, stated against this issue's own framing: privilege Prop, keep proof relevance, and let the compiler do erasure "if it wants". Four decisions, in the order they force each other. (1) **Propositions are types and they are relevant.** No `Prop` sort; `SProp` stays exactly where [[sprop-strict-prop]] put it — opt-in squashing for index constraints and guard predicates, generator-internal, never a library-facing distinction. (2) **No `Bool` in any spec API and no `= True` anywhere.** `Bool` remains a data type for when Booleans are the subject (Boolean algebra, circuits) and inside generated code; every `= True` statement in `lib/` is a migration target. (3) **A decided relation gets exactly one extra name: its decider**, returning `P \/ ~P`, found by resolution and *derived* where the relation is structurally recursive — owned by [[decide-class]], which also records sub-question 1's answer (Decide and Compile stay distinct; Compile strictly refines it in demand, since decidable-but-insane is easy to exhibit). Sub-question 3 (what `if p` demands) falls out: `Decide`, because it is the uniform-branching interface, with `Compile` needed only when the code must run. (4) **Erasure is the compiler's job, not the type system's** — and this is the load-bearing one. Lean puts irrelevance in the *sort* because that is its only erasure mechanism; Heather has datarepr/`Compile`/certified refinement, so "these proofs do not exist at runtime" can be a theorem about a compilation rather than a restriction on the theory. Keep relevance in the language, get erasure from the compiler, pay neither price. That reading also answers sub-question 2 the same way: a compiled proposition is a datarepr question, not a sort question. **What the two-object Prop/Bool split in Lean actually buys, unbundled**, since this issue had it as one thing: (a) erasure, which (4) handles elsewhere; (b) the elimination restriction — under irrelevance you cannot eliminate `P \/ ~P` into `Type` to pick a branch, which is *why* `Decidable p : Type` is a second object there, and which **does not apply here** because relevance keeps them in one universe; (c) proof size for reflection, `ble(n,m) = True` being small where a derivation is large — and under [[nat-order-kit]]'s recursive `Le` the proposition itself reduces to `True` at closed arguments, so reflection is already free and this reason evaporates too. (d) Genuine duplication in Lean's *programming* APIs (`List.contains` vs `a ∈ l`), which is the pain the user was recoiling from and which even Mathlib does not have on the math side — `≤` on `Nat` is the inductive `Nat.le`. **Where proof relevance actually costs, recorded so the plan is not surprised:** only where a proof is *stored in data whose equality is then compared* — a refinement value `{i : Nat | i < len(xs)}`, a forded index constraint riding inside an indexed value (which is what `sEq` was landed for, and the 2b setoid acceptance is the evidence it works), and `transp` towers that irrelevance would collapse at convertible endpoints. It does **not** cost anything for proofs merely *consumed* as hypotheses, which is the whole Nat/List order and arithmetic kit. The cheapest mitigation is a library convention rather than a mechanism: prefer proof-as-parameter over proof-in-data (`nth_g(xs, i, h)` over a subset value). On whether [[setoid-auto-lifting]] absorbs the rest — partially, and the boundary matters: setoids decide *which equality you reason with*, not *which terms are convertible*, so where a stored proof makes two values non-convertible the tactic does not restore a silent kernel success, it discharges an obligation that now exists. Viable (it is Coq-without-SProp for a decade) but the cost lands in checking speed and in a `Proper`-style obligation at every abstraction boundary. Complementary, not competing: squash removes the obligation, setoids automate it where removal is unavailable. This issue keeps sub-questions 4, 5 and 6; the landed `Cmp` (Bool plus `= True`) is now formally on the migration list, owned by [[nat-order-kit]]. Sequencing for the library push is [[std-api-waves]].
- 2026-08-16: 2026-08-16: The Cmp migration this issue put on the list is PAID (see [[nat-order-kit]], docs/nat-order-design.md §3). Cmp's le is now A -> A -> Type, its law is the relation rather than an equation with True, and deciding moved to a third field returning P ∨ ¬P — the interface [[decide-class]] will generalize, filled locally so nothing waited on that class. Two data for sub-questions 4-6. (a) The predicted cost of relevance did not appear anywhere in this round: no proof is stored in compared data, and the one place a hypothesis is consumed — or_pick_dec's refuting arm — got SHORTER than the Bool version, since the caller's proof closes the branch with no transport where cmp_pick needed a j. (b) The elimination-restriction argument (b) in the 2026-08-16 entry is now exercised rather than argued: le_dec eliminates into Type to pick a value, which is exactly what Lean needs a second object for, and it works because relevance keeps them in one universe. leb/leb_bool survive as decision procedures that no specification names; list_algos's = True kit is the remaining migration and belongs to [[std-api-waves]] L3.
- 2026-08-17: First customer for the second filter this doctrine predicts (wave L3, 2026-08-17, [[std-list-mem-and-perm]]). mem_filter states only ONE direction: Mem(a, filter(xs, p)) -> Mem(a, xs). The converse needs p(a) as a hypothesis, whose only spelling with a Bool predicate is p(a) = True, which this doctrine bans from a specification — so the fact is left UNSTATED rather than encoded. What would state it is the Decide-valued filter that [[std-list-api]] called "a second function, not a replacement" when it chose A -> Bool for the program. The choice still looks right; what is now known is what it costs — filter's characterization theorem, not its laws (filter_append, filter_filter, filter_map all went through at Bool).
