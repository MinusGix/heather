---
title: Refresh the probe benchmark cases: three no longer run, two no longer probe a cost
status: closed
labels: [performance,tooling]
area: infrastructure
created: 2026-11-11
updated: 2026-11-12
---

`scripts/bench-probes` no longer measures what its case list says. Found on 2026-11-11 while writing [[performance-overview-2026-11-11]].

- `cert/yes-pieces` and `cert/yes-labels` exit 1: the frozen certificate `perf/bench/fixtures/yes_tool_elf_certificate.hthr` no longer checks against the library.
- `algebra/pos-of-mul-pos-nonneg` exits 1: `--only` names `ordered_field::OrderedField::pos_of_mul_pos_nonneg`, which no module of the closure declares any more (the sign rules moved to their weakest class).
- `native/emit-extends` runs 17 evaluator steps and `tactic/attempt-from` 930, against 5,560 and 588,235 on 2026-10-29. Both take under 20 ms now, so they no longer probe a cost.

`perf/bench/results.tsv` was rewritten on 2026-11-11 with the eleven cases that ran (the cloud CPU differs from the 2026-10-29 record's, so the script replaced the file whole).

`scripts/perf snapshot --corpus full` had the same kind of rot: it named `lib/certgen/ir_v1.hthr`, which left the library, and failed before writing anything. That is fixed alongside this issue (the corpus now names `native_compile_correct` and `closed_interval`, the two heaviest subjects of the library gate).

## Done when

Every case in `perf/bench/cases.tsv` runs, the certificate fixture is regenerated or replaced by a case that cannot go stale (a `write-elf` into a scratch file, then `--only` on its pieces), and the two trivial cases are replaced by today's heaviest declarations: `native_compile_correct::Target::perform_call`, `supremum::OrderComplete::below_located`, `itree_trace::IsTrace::split_bind`.

## Log

- 2026-11-12: Done. `cert/*` are a new case kind, `cert`: the harness runs `write-elf lib/native/native_tools.hthr yes_tool` once (unmeasured), copies the certificate to `yes_tool_elf_certificate.hthr` under `target/bench-probes/out/certificates/` (a module's stem must be an identifier), and runs `--only` on its items matching a glob (`yes_tool:yes_tool_elf_piece_*_is`, `yes_tool:yes_tool_elf_at_*`). The frozen fixture is deleted. `native/emit-extends` and `tactic/attempt-from` gave way to `native/perform-call`, `analysis/below-located` and `itree/split-bind`. `algebra/pos-of-mul-pos-nonneg` ran again once retargeted at `OrderedSemiring::`, but at 485 steps and 0.04 s it no longer probed a cost either, so it is retired too. A `--save` now drops rows of cases the list no longer names. Every case ran on the cloud box at d64c439 (`--heavy` included) and `perf/bench/results.tsv` is re-recorded; the new rows are in `perf/bench/targets.md` T7.
