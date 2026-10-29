---
title: Find why the compiler's lemmas at a neutral target run millions of kernel steps
status: open
labels: [performance,native,kernel,proofs]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-29
updated: 2026-10-29
---

The compiler is proved once, so its lemmas are stated over a neutral
`Target`, `Env` or program. Some of them still cost the kernel millions of
evaluator steps, measured alone with `--only` over a replayed prefix (cloud
box, width one, `perf/bench/targets.md` T4):

- `native_compile_args::Target::goes_arg_found`: about 5.2M steps, and
  about nine seconds of gate.
- `function_ir_lower_calls::call_step`: about 4.6M steps in one gated term,
  and about nine seconds.

Both step counts agree within about 1% between the cold module check and
`--only`, so it is these proofs' own work, not something shared. At a neutral target
there is little closed data to run, so the steps are probably closed layout
and offset arithmetic (`t.layout().…`, `buffer_offset`, `stack_offset`)
unfolded and evaluated at each use, or conversions that unfold a definition
to compare it with itself. Find out which, with the kernel's counters and gdb
stack samples, then either restate (a stage lemma, a `have` naming the fact
once, `docs/proof-patterns.md`) or file the kernel or elaborator mechanism.

## Cases

`scripts/bench-probes --filter native/goes-arg-found`, `native/call-step`;
`native/arg-cells-store` is a small member of the same family for the inner
loop.

## Done when

Both lemmas are a small fraction of their current steps, or the reason they
cannot be is written down with its owner.
