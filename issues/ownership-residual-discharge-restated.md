---
title: Ask a function's residuals as one statement restated over the source's terms, so their discharge costs one conversion
status: closed
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

## Log

- 2026-11-25: Done in [[ownership-site-facts-into-the-checker]]. `check_sound` keeps its premise, now one statement (`Owes::Due`: every residual at the state its site reads, along the meaning) at the parameter words spelled, and a generator's term is one ascription of its restated conjunction to it (`hop_site_restated` in `lib/_tests/lang/ownership/site_facts_tests.hthr`). Measured, fresh store per run, a residual at every statement, at 64, 128, 256, 512 statements: the restated conjunction built as a recursive statement and proof, ascribed once, costs 12.2k, 23.5k, 46.2k, 93.0k kernel steps (76 ms total at 512): linear. Where the elaborator's cost went: written as a literal conjunction and a literal tuple, the kernel stays linear (8.3k to 60.5k at 32 to 256, gate 7 to 56 ms) but elaboration is 13, 58, 274, 1850 ms, in checking the anonymous tuple against the literal conjunction, not in the gate; the recursive form pays none of it, so a generator emits that form (or kernel terms). The tuple converted component by component against the checker's statement is still quadratic (57.7k at 16 to 7.65M at 256). Filed: [[elaborator-literal-tuple-against-conjunction-cost]].
