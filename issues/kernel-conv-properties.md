---
title: Property-test conversion once typing lands (PER, subject reduction, C_A cross-check)
status: closed
labels: [kernel, delam, testing]
blocked-by: [kernel-typing]
created: 2026-07-22
updated: 2026-07-23
---

## Log

- 2026-07-22: conv.rs's golden tests can't cover the risk that a C_A telescope/branch-type is wrong the same way in all three hand-maintained tables (Branches docs, subst.rs map_branches, conv.rs rec_ca) - the same caveat as tests/common/mod.rs. Once kernel-typing lands, well-typed terms become generatable/checkable and three properties open up: (1) reflexivity t ~ t for checked terms (PER lemma, ch. 08); (2) subject-reduction-flavored: if t steps by recursor beta, the fired branch instantiation type-checks against conv.rs's instantiated branch type - a machine cross-check of the G_A tables; (3) conv respects whnf: t ~ whnf(t). Blocked on kernel-typing.
- 2026-07-22: Unblocked: kernel-typing landed (typing.rs). check_term/infer_term can now generate/verify well-typed inputs for conversion properties; note branch telescopes are shared via src/rec.rs, so a C_A cross-check between conv and typing exercises the same tables (independent re-elaborations live in tests/typing.rs).
- 2026-07-23: Implemented as tests/conv_properties.rs over a new type-directed well-typed-term generator (tests/common/wt.rs, synthesis along the ch. 04 rules; check_term is the oracle, asserted by a generator-sanity property). Properties: (1) reflexivity t ~ t; (2) subject reduction — every step_term reduct re-checks at the original type, routing reduce.rs's recursor-beta fire() through typing.rs's G_A telescope checks (the C_A cross-check; wt.rs carries a fourth independent transcription of the branch depth table); (3) t ~ whnf(t), both orientations; plus: the identity recursor is the identity in one beta-step on generated code. Coverage at 1000 seeds: ~16% of terms contain code recursors, ~18% letboxes/elim_Nat, ~39% step at head; generated code heads span all 13 branches. One generator subtlety found: layer-c App annotations copied from a head's Pi type may mention Prog-layer globals invisible at layer c — filtered via the checker.
