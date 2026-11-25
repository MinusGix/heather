---
title: Ask a function's residuals as one statement restated over the source's terms, so their discharge costs one conversion
status: open
labels: [ownership,library,performance]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-residuals-from-source-proofs]] (its log of 2026-11-25 has the measurements). `check_sound`'s `discharge` asks for `Owed::All(rs, pres, words)` at the meaning's final words, and a discharge written as a tuple `⟨p₁, ⟨p₂, …⟩⟩` is converted component by component: each residual re-runs the meaning to the state it reads, and nothing is kept between components. One residual costs a linear pass over the body; a residual per statement costs about 160·N² kernel steps (10.4M, 4.2 s, at 256 statements). Restated at the source's terms and moved by one ascription, the same conjunction costs one conversion that shares the meaning's evaluation: 62k steps at 256, linear.

## Wanted

- The checker's interface asks for the discharge in the form a generator can give at once: the residual list's statement at the reflected state, which a generator proves by ascribing its restated conjunction (`f::restated(xs, x₀…)`, the residuals at the source's terms) to it. Either `check_sound` keeps its premise and the generator's term is the ascription (what `hop_site_restated` in `lib/_tests/lang/ownership/site_facts_tests.hthr` does), or the checker emits the restated statement itself, run on the untrusted evaluator, with one theorem that it is the residuals' statement.
- The elaborator's check of a deep anonymous tuple against a literal conjunction is superlinear (1.7 s of elaboration at 256 components, against 21 ms in the gate). A generator writing kernel terms does not pay it; a probe written in source does. Measure where it goes before choosing.

## Done when

A generated function with a residual at every statement discharges in time linear in its body at 256 and 512 statements, measured as `docs/proof-patterns.md` §7 says (a fresh store per run).
