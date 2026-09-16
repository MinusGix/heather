---
title: Reduce checker cost for proof-carrying parser composition
status: open
labels: [frontend,parsing,performance,proofs]
created: 2026-09-15
updated: 2026-09-15
---

## Problem

The independent calculator grammar proof exposes substantial checking cost in
composing `Result<Certified<...>,Failure<...>>`. Initial versions exceeded the
6 GiB test rail, both with the default gate and with serial checking. Splitting
production bodies, flattening `Certified`'s success fields and using generic
Result eliminators allowed the full theorem and its refusal tests to check.
The serial diagnostic run still took 139 seconds for the calculator target.
This is an observation about the checked fixture, not an attribution to any
particular compiler subsystem.

The old shape nested `parsed: Success(source,begin)` and
`evidence: R(source,begin,parsed.end,parsed.value)`. The current shape exposes
value/end/forward/evidence directly. Nested concrete Result matches were
replaced by `result::fold` and `and_then`; see `expr_body`, `factor_body` and
the parentheses helpers in `docs/showcase/calc_parser.hthr`. Generic higher-order
certified finishing was also more expensive in this client than small concrete
production helpers. Do not infer proof erasure from successful projections.

## Scope and protocol

Profile elaboration, generated types/terms, conversion and retained state
separately, using a reduced production-composition fixture and the full checked
calculator. Identify the contribution of concrete indexed record instantiation,
nested elimination and generic dictionary arguments. Also inspect `selected_head`'s use of the list eliminator when only the head
witness is needed. These are hypotheses to investigate, not established root
causes.

Use `scripts/test`, keep the resource rails, isolate loading from proof checking,
and compare the same gate width. The acceptance fixture currently selects one
worker; establish the default parallel-gate cost separately. Record checked
outputs/refusals and deterministic counters before interpreting wall time.
Preserve the open grammar theorem, source/span invariants and empty axiom audit.

## Acceptance

- A reduced reproducer and an attributed cost explanation.
- A cheaper checked representation or implementation, with the same guarantees.
- Both ordinary and proof-carrying parser clients remain usable.
- No larger cap or silently trusted image substituted for actual checking.

## What it assumes from elsewhere

- [[parser-grammar-soundness]] owns the independent grammar and success theorem.
- [[parser-certificate-ergonomics]] owns user-facing certificate composition.
- [[parser-cached-cursor-cost]] owns cursor traversal and representation costs;
  this issue owns checking semantic evidence even on short inputs.

## Log

- 2026-09-15: Attributed (2026-09-15, release + value-metrics, W=1, one furnace E5 box, cold): calc_parser.hthr 142 s wall / 4.9 GB serial, 71 s / 16.6 GB at W=8. close_body 35 s (30 s gate, 2.7 s emit alone, 9.6 M conv shortcut hits); parser_primitives::complete_post 28 s (21 s gate, 7.0 M shortcut hits, 6.2 M steps); paren-path refl theorems ~3.5 s each at ~5 k steps (0.7 ms/step vs 3 us/step in calc.hthr). Traces: close_body's 22 k misses are one closed Pi/Pi comparison (Recognized<..> partial application vs Certified's relation domain) repeated inside Fst/Snd chain annotations at up to 21 binder depths, <4 s total; complete_post's are nested projection chains (s.end.offset through Success then Cursor), Sigma/El-code. Root cause: every parser record is telescoped AND dependent, and register_rec_projs declines exactly that combination, so every field read is project_field's inline walk with its tail-substitution exponent -- boundary 1 of [[per-instantiation-projection-boundaries]]. 17-line reproducer (Certified-shaped record read through chained receivers, probes/t_pc1..4): 9.5 ms / 413 ms / 7.8 s / allocator abort >3.8 GB at chain depth 1/2/3/4, zero misses and zero eval steps, i.e. pure emitted-term size. Round chartered: named projections for telescoped dependent records (the closed fam/proj/tail triple over the telescope), design pass first.
- 2026-09-15, implementation (landed in the round's dirty tree; no commit). **Named projections for telescoped dependent records** (docs/telescoped-record-projections-design.md §3/§4), with §2's three prerequisites and a spelling pass over the device's own telescope domains. Release + `value-metrics`, `--kernel-workers 1`, one furnace E5 box, parent binary and changed binary in one job. **Reproducers, parent → changed:** `t_pc1` 11.0 → 6.1 ms; `t_pc2` 440.5 → 23.8 ms; `t_pc3` 8058.5 → 88.2 ms; `t_pc4` **allocator abort at 8.0 GB → 266.4 ms**; `t_pcev3` 3812.4 → 33.5 ms. Conversion misses and evaluator steps are **zero on both sides** at every depth — the device removed the emitted-term size without buying a conversion, which is what the spelling pass is for. Per-receiver growth 3.9× / 3.7× / 3.0×, a small falling constant against the parent's 40× / 18× / abort. Declaration items rise by a bounded amount that does not grow with chain depth: `Cur` 0.5 → 6.5 ms, `Cert` 2.7 → 90.3 ms (`3·nfields + 1` Ψ bindings per record, [[record-projection-defs-declaration-cost]]'s cost arriving at a second family). Process wall/maxrss: `t_pc3` 10.28 s / 820 MB → 1.15 s / 98 MB; `t_pc4` 19.50 s / 8.04 GB → 1.37 s / 115 MB. **Showcase** `docs/showcase/calc_parser.hthr`, W=1: wall 137.46 → **123.34 s**, maxrss 4.940 → **4.579 GB**, run total 135.2 → **121.4 s**, kernel gate 109.8 → **99.4 s**, misses 338 755 → 370 817, eval steps 13.03 M → 16.73 M. Items: `close_body` 34.27 → 29.79 s, `parser_primitives::complete_post` 26.66 → 21.93 s, `number_grammar` 3.81 → 2.81 s, `checked_expr` 2.84 → 2.64 s, `parentheses` 3.53 → 3.23 s, `nested_parentheses` 3.18 → 2.91 s, `missing_close` 3.20 → 2.90 s — the paren-path refl theorems all still check inside the default fuel. **Default gate width:** 69.46 s / 17.55 GB → **61.87 s / 15.51 GB**. **Head pairs** (count / seconds, showcase, W=1). Parent top five: `El(?)/Wf` 39 252 / 2.31 s, `Vec/Unit` 37 677 / 0.05 s, `Sigma/El⌜⌝` 33 757 / 3.64 s, `El⌜⌝/El(?)` 32 310 / 2.22 s, `Vec/Sigma` 30 748 / 1.56 s. Changed top five: **`Pi/Pi` 47 010 / 4.87 s**, `El(?)/Wf` 38 988 / 2.22 s, `Vec/Unit` 37 629 / 0.05 s, `El⌜⌝/El(?)` 32 314 / 1.77 s, `Vec/Sigma` 30 725 / 1.52 s. The row the device exists to remove halved: `Sigma/El⌜⌝` 33 757 / 3.64 s → 16 744 / 1.62 s — the kernel's `Fst`/`Snd` rule reconstituting `Σ(fst). snd` against the receiver's own reference, boundary 1's signature. **The one new large row is `Pi/Pi`, 23 711 / 4.23 s → 47 010 / 4.87 s**, and it is docs/telescoped-record-projections-design.md §5's named follow-up. The comparison itself is the one this issue's 2026-09-15 attribution already traced on `close_body` — a partially applied `Recognized<…>` relation against `Certified`'s function-typed `relation` parameter domain; it was **not** re-traced this round (the `HEATHER_CONV_MISS_TRACE=close_body` run printed the first module's `Pi`/`Pi` block rather than `close_body`'s, and the bar did not fail, so no trace was required). §5 predicted the *count* would fall by the chain-depth factor once the device replaced the `Fst`/`Snd` chains; it rose instead, at +0.64 s against −2.02 s on the row it replaced, because the device makes `D#projⱼ`'s statement carry that `Π` once per read rather than once per node. §5's trigger — "`Pi/Pi` a top row after the device has landed" — has therefore **fired**: naming a declaration's function-typed value-parameter domain, on [[elaborator-canonical-type-spelling]]'s line, is the next slice and is a new definition kind rather than a spelling change. **Not reached:** `Certified`'s own field reads in `probes/t_pcr3.hthr` are unchanged (qchain1/2/3 and qev3 identical to the parent at zero misses), because `instance_match` still declines for it — see [[type-code-fn-template-stale]]'s 2026-09-15 pass-2 entry for the two remaining decline reasons and the slice that closes them; `t_pcr3`'s whole-file wall still falls 67.97 → 57.47 s and its RSS 2.19 → 1.70 GB on the other parser records.
- 2026-09-15 (same round), what the suite moved. `scripts/bench --check` against a `--save` taken on the parent tree on the same box: **ok, 112 comparisons within thresholds**. The full `scripts/test` moved five fixtures and nothing else; all of them are the `3·nfields + 1` Ψ bindings §7 predicted, arriving at the prelude's `CollectionLiteral<C>(n)` (2 fields, `fromLiteral` mentions `element`, so +7). `nat_suite.rs`/`implicit_args.rs`/`match_recursion.rs` 10 → 17, `goal_holes.rs` 9 → 16, `nat_suite.rs`'s bodied-binding vector to eight generated definitions ahead of the prelude's four theorems, and `determinism.rs`'s `NAT_SUITE_GOLDEN` (a hash over Ψ's printed form) to `0x9d693d5d3245eccb`. **One behaviour change that is not a count**: `lib_algebra::one_law_three_structures` and `operation_indexed_classes::slow_acceptance_the_wrong_unit_is_refused` still refuse the wrong unit, but the message changed — a class dictionary's `A.unit` is now `CommMonoid#projⱼ^δ ā v` rather than an inline `fst(sndʲ v)`, so the disagreement is caught in the **checking** position (`this has type or(x, (CommMonoid#bool#or).unit) = x, but or(x, True) = x is expected here`) instead of further down, and the message names the two types where it used to name the declaration. The two controls now assert the substance (the instance's type mentions the registered unit, the stated one is the wrong literal) rather than the declaration's name; the refusal itself is unmoved and both were re-read, not just re-run. `crates/elab/tests/record_projection_size.rs`'s parameterized-record fallback test now exercises the **new** route (`Monoid<A>` is telescoped and dependent) off a computed receiver, a bare binder and an open element type — its comment was rewritten to say so. The x86 rails (`function_ir_x86_scaling.rs`, `crates/cli/tests/native*.rs` including `caller_native_memory_same_27/28`) are green inside their existing budgets and their records are non-dependent, which is what the dependency test was meant to partition.
- 2026-09-15: Coordinator (2026-09-15): the slice above is landed as one commit after independent review and a second full scripts/test. What it bought on the showcase is the bar and no more (~10 % serial, ~2 GB at W=8) because `Certified`/`Cursor`/`Success` instantiations still decline instance_match at ordinary use sites on the two-spellings boundary (design §2.3 amended); the reproducer's exponent is gone. Next slice, chartered on [[elaborator-canonical-type-spelling]]: spell a closed type argument alike at binder types and application annotations, then name function-typed value-parameter domains (`Pi/Pi` top row). Re-take the showcase table after each; this issue closes when close_body and complete_post are ordinary items.
- 2026-09-15: Coordinator (2026-09-15): second slice landed — the instance matcher sees through names (docs/closed-argument-and-parameter-domain-spelling-design.md). Showcase 123.1 → 78.5 s serial, 4.58 → 2.39 GB; default width 62.1 → 41.4 s, 15.8 → 7.0 GB; close_body 29.9 → 6.9 s. complete_post unmoved at ~21 s and is now the largest item: attribute it next (a library theorem; its misses are nested Success/Cursor chains, 110 k, unchanged by both slices). Residual on close_body is the quote pair, [[quote-see-through-bounded-arm]].
