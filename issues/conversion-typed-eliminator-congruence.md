---
title: Typed neutral congruence for the eliminators: stop re-comparing annotations well-typedness forces
status: open
labels: [kernel,conversion,performance,design]
area: kernel
created: 2026-09-06
updated: 2026-10-20
---

The 2026-09-06 round made conversion's `app`/`fst`/`snd` neutral rules
typed: heads compared, the head's inferred Π/Σ read, the argument compared
at that domain; the stored annotations are never related to each other
(`crates/kernel/DESIGN.md`, Algorithms; [[function-ir-x86-proof-scaling]]).
The same inheritance from ch. 06's untyped conversion is still in the
remaining neutral arms of `Conv::tm_ne`: two `elim_Wf`s compare shape and
arity (`self.ty(env, s1, s2)`, `tm_at_nat(k1, k2)`), two `elim_Nat`s /
`case`s / `J`s / `transp`s compare motives, branch telescopes and type
components structurally, at every meeting of the two neutrals. On a
Wf-lowered inductive the shape is the sum-of-Σs, so one such comparison is
the size of the declaration.

It did not show on the x86 workload only because record projections are
named globals ([[theorem-field-projection-oom]]); any proof that compares
two neutral matches on one scrutinee — the setoid transfer proofs, the
relational-context certificates — is the shape that pays.

## What is redundant and what is not

- **Redundant** given well-typedness and convertible scrutinees: the
  *shape* and *arity* of `elim_Wf`, the `A`/`B` of `case`, the `I`/`a` of
  `J`/`transp` — all determined by the scrutinee's inferred type.
- **Not redundant**: motives and branches. Two eliminations of the same
  scrutinee may differ there, so they stay compared — but at the *inferred*
  telescope (one `wf_step_telescope` off the scrutinee's type), not at two
  stored copies.

## Acceptance

- Each eliminator arm reads the scrutinee's inferred type
  (`tm_nee_c` + `Conv::delta_to_head_ty`) for every component the typing
  rule forces, and compares only motive and branches.
- The kernel suite, the conv differential oracle and the certgen controls
  are unchanged; measure on a relational-transfer fixture that compares
  neutral matches, not on the x86 module.
- DESIGN.md's Algorithms bullet extended from "application and projection"
  to the eliminators.

## What it assumes from elsewhere

- **[[function-ir-x86-proof-scaling]]** landed the pattern for `app`,
  `fst`, `snd`; this issue extends it and owes nothing back.

## Log

- 2026-09-12: New datum from [[elaborator-canonical-type-spelling]]'s refuted round (docs/elaborator/record-projection-reference-design.md §9.7): the reused_callee certificate's `Sigma`/`El(?)` bucket — 14,682 misses / 9.16 s, 24.7% of a 37.1 s kernel gate — is the `Fst`/`Snd` *typing* rule reconstituting `Σ(fst_ty). snd_ty` and converting it against the reference `El (app(D#tycode_fn^δ; ā))` the receiver's inferred type carries, once per field read. The elaborator-side fix (spell the read as a reference) was measured and refuted: it moves the compare under evaluation, where chain depth multiplies it. A typing rule that reads the receiver's inferred Σ off its type (the typed-congruence shape this issue already owns for conversion) removes the bucket without moving any read; it is the surviving route and a kernel change, so it waits for a chartered kernel round.
- 2026-09-13: The typing-rule route this issue was handed on 2026-09-12 is closed off, not by measurement but by the code recursor: the x86 certificates' proof terms are checked at layer c, where `tm_fst`/`tm_snd` (crates/kernel/src/reduce.rs, rec.rs) bind `u_p : □(g ⊢ Σ U_S U_T)` with the real pair, so the annotations must be checked against the receiver's Σ — conversion may skip what typing establishes, typing may not. The bucket's cost was the post-unfold component spelling, and it is gone elaborator-side (docs/elaborator/record-projection-reference-design.md §9.8; [[elaborator-canonical-type-spelling]]). This issue keeps its own scope: the remaining eliminator arms of conversion, measured on a relational-transfer fixture.
- 2026-09-16: Typing-side twin with a measured customer (docs/kernel/conversion-query-traversal-design.md §2.2, §5): 35.7 % of `complete_post`'s 3.68 M conversion queries are the `App` rule converting the `Π` it rebuilds from its own `dom`/`cod` annotations against the `Π` it just inferred for `fun`, and 54.2 % are `Ty 0 ≈ Ty 0` at type-argument slots. A typed `App` rule reading `dom`/`cod` off `fun`'s inferred type is a real ~36 % constant factor on that family; deliberately not taken in that round (an exponential is the subject), its own before/after under the constants protocol.
- 2026-10-16: Checked against the formalization (heather-coq `ELIM_CONGRUENCE.md`, MinusGix/heather-coq#22): its algorithmic conversion's neutral `J`, `case`, `elim_W`, `elim_Wf` and `elim_IWf` rules now compare only the scrutinees, the motive's level, the motive and the branches/steps, with soundness, completeness and decidability re-proved (no axioms). **Forced, levels included**: `J`'s `A`, `a`, `u` and their level; `case`'s and `elim_W`'s `A`, `B` and both levels; `elim_Wf`'s `A`, `N` and level; `elim_IWf`'s `X`, `S`, `n`, `o`, `c`, its two levels and the index. The levels need no argument of their own: a type's level is unique, and the formers' injectivity hands back each component's level. **Not forced**: the motive, its level (probably redundant via the motive comparison, not checked), the branches, and `elim_IWf`'s induction-hypothesis types, which the formalization still compares because `eqtm_elimIWf` states them as an admissible premise; dropping them waits on a `dnth` congruence over its annotations, so for the kernel that comparison is redundant in theory but unproved there. Motives may be compared in either elimination's stored telescope or one read off the inferred type; the formalization uses the left one (convertible to the inferred one), which needs no read of the scrutinee's type.
- 2026-10-20: Checked in the formalization (heather-coq `ELIM_CONGRUENCE.md`, MinusGix/heather-coq#24): `elim_IWf`'s induction-hypothesis types are forced too. Along equal signatures (which the scrutinee forces) and equal motives they are equal: `dnth`'s index lemma is already relational in its length and family, and composing it with the motive gives the equation at the computing layers (`Validity/IWfIhEq.v`, no axioms). The formalization's algorithmic `elim_IWf` arm now compares only the scrutinees as neutrals, the motive's level, the motive and the step, with soundness, completeness and decidability re-proved; **the kernel's `elim_IWf` neutral arm may skip the IH types as well** (it was the one comparison the 2026-10-16 entry left in place). The typing rule keeps the IH-type premise (conversion may skip what typing establishes, not the reverse). The motive's level stays compared: it is redundant declaratively (motive equality plus level uniqueness), but dropping it from the algorithm needs a level-heterogeneous soundness of type conversion, and it is one level comparison.
- 2026-10-20: **Landed for `case`, `elim_W`, `elim_Wf` and `J`** (crates/kernel/src/conv.rs, `Conv::tm_ne`). Each arm compares the motive's level, the motive, the branches/step and the scrutinees, and none of what the scrutinee's type forces: `case`'s and `elim_W`'s `A`/`B`, `elim_Wf`'s shape and arity, `J`'s `A`/`a`/`u`, levels included. Motives and branches are compared in the left elimination's stored telescope (the formalization's choice), so no type is read off the scrutinee. `elim_Nat` had nothing forced. `transp` is left as is: its proof is irrelevant and never compared, so no scrutinee forces `I`/`a`/`b`. `elim_IWf` landed typed from the start with `IWf` (heather#79; its entry below). **The scrutinees stay last**: comparing them first ran `function_ir_recursive_certificates::an_immediate_add_certifies_at_its_sign_extension` out of fuel, and the original order passes it. Tests: `crates/kernel/tests/conv_elim_congruence.rs` (each eliminator at a neutral and a literal scrutinee, forced annotations spelled `El «Nat»` / `(λx. x) 0` / `0 ⊔ 0` on the right, and negative controls: a differing branch, a differing scrutinee, a motive that agrees with `Nat` on every constructor but not on the neutral). A fuel pin asserts the differently spelled pair converts in the budget of two identical ones; it fails on the old arms. `scripts/perf ab --base origin/master` on `tree_list_set_transfer`, `list_setoid`, `algebra_rel` (3 samples, load average 3.3 on 4 CPUs, so the seconds are weak): **counters**: `eval_drives` −24.3 % / −17.4 % / −17.7 %, `eval_steps` −10 of ~10⁵, conversion query and miss counts identical. **Seconds**: kernel gate −10.7 % / −12.0 % / −14.2 %, separate on two of the three files, wall inside the spread. DESIGN.md's Algorithms bullet now covers the eliminators.
- 2026-10-20: The kernel's `elim_IWf` neutral arm (`conv.rs`, landed with `IWf`, [[iwf-former]]) takes the 2026-10-20 entry at its word. It compares the scrutinees as neutrals, the motive's level, the motive and the step, and not the ih types, the signature or the index.
- 2026-11-05: gardener: cites a file it shares with [[conv-query-identity-env-per-gamma]] (`crates/kernel/src/conv.rs`); [[emission-walker-residual-sites]] (`docs/elaborator/record-projection-reference-design.md`); [[indexed-families]] (`crates/kernel/src/conv.rs`); [[kernel-psi-bound-cache]] (`crates/kernel/src/reduce.rs`); [[reducer-step-frame-size]] (`crates/kernel/src/reduce.rs`).
