---
title: Find why the compiler's lemmas at a neutral target run millions of kernel steps
status: closed
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

## Log

- 2026-10-29: Found and fixed (2026-10-29, cloud box, `scripts/bench-probes`, exact counters). Neither lemma was running closed arithmetic: almost all their kernel time was **conversion misses between two spellings of one type**, found with the `value-metrics` miss trace (`HEATHER_CONV_MISS_TRACE`) plus a throwaway patch naming each miss's application head.

  - `goes_arg_found`: 1,048 `Sigma/Sigma` misses, 9.9 s of its 14.5 s gate, every one at a `t.field` read. A closed dependent record's named projections (`register_rec_projs`) took their argument at the record's raw inline lowering, where `X86Profile` (a coded declaration) is spelled out: about 100 K nodes, against the receiver's own type, which the statement spells with `El(X86Profile#tycode)` (about 5 K). Each read converted the two. The projections' binder now takes the emission spelling (`annotation_type`), the same one a statement gives the record.
  - `call_step`: the same shape at `omega`. A lifted proof and a named atom list are globals whose context is the elaborator's `Cx` as stored (coded declarations inline: `Stack<M>` about 97 K nodes), and the slot reference `u^{id}` checks each body binder, whose type is the emitted spelling, against that context, per binder per call. Lifted slots are now allocated over `Elaborator::emitted_cx` (each binder's type in the emission spelling, memoized per declaration).

  | case | steps before | after | kernel s before | after |
  |---|---|---|---|---|
  | `native/goes-arg-found` | 5,208,171 | 573,636 | 15.3 | 1.3 |
  | `native/call-step` | 4,613,905 | 96,213 | 11.1 | 0.6 |
  | `native/arg-cells-store` | 169,610 | 5,372 | 0.34 | 0.02 |

  Both lemmas are now about a tenth and a fiftieth of their steps; closing. The mechanism is not native-specific: any closed dependent record with a coded field, and any `omega`/`ring` inside a context that holds a coded declaration, paid it.
