---
title: Property-test conversion once typing lands (PER, subject reduction, C_A cross-check)
status: open
labels: [kernel, delam, testing]
blocked-by: [kernel-typing]
created: 2026-07-22
updated: 2026-07-22
---

## Log

- 2026-07-22: conv.rs's golden tests can't cover the risk that a C_A telescope/branch-type is wrong the same way in all three hand-maintained tables (Branches docs, subst.rs map_branches, conv.rs rec_ca) - the same caveat as tests/common/mod.rs. Once kernel-typing lands, well-typed terms become generatable/checkable and three properties open up: (1) reflexivity t ~ t for checked terms (PER lemma, ch. 08); (2) subject-reduction-flavored: if t steps by recursor beta, the fired branch instantiation type-checks against conv.rs's instantiated branch type - a machine cross-check of the G_A tables; (3) conv respects whnf: t ~ whnf(t). Blocked on kernel-typing.
- 2026-07-22: Unblocked: kernel-typing landed (typing.rs). check_term/infer_term can now generate/verify well-typed inputs for conversion properties; note branch telescopes are shared via src/rec.rs, so a C_A cross-check between conv and typing exercises the same tables (independent re-elaborations live in tests/typing.rs).
