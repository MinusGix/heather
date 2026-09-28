# Design pass 2 scripts (2026-09-15) — `docs/closed-argument-and-parameter-domain-spelling-design.md`

Five furnace round trips, in order. `probes/s3_base/gendefs.rs` is HEAD's
(`51f5e59`) copy of the one file the spike touched; the scripts swap it in and
out to build the before column, because the remote checkout is not a git
repository (see the bench section of `probes/README.md`).

- `s3_trace.sh` — the trace read. `HEATHER_CONV_MISS_TRACE=close_body` on the
  showcase and on `probes/t_pcr3.hthr`, aggregated by `trace_agg.py`, plus the
  baseline `HEATHER_GENDEF_DECLINES=1` listing. **`t_pcr3` has no `Pi/Pi` row
  at all** — its items have zero conversion misses, so the trace read has to
  be taken on the showcase.
- `s3_excerpt.sh` — `first_difference_excerpt` for the top `Pi/Pi` groups.
  `trace_agg.py` truncates a record at 260 characters, which cuts the excerpt
  off; this prints whole records and buckets them by the
  `expected len=… inferred len=… first difference at …` signature. That
  bucketing is what shows the two equal-count groups.
- `s3_spike.sh` — spike iteration 1 (see through **names**), base and spike
  built in one job: decline listing, `t_pcr3`, showcase serial, head pairs,
  both columns.
- `s3_spike2.sh` — iteration 2 (see through quotes as well). **Refuted**:
  `fatal runtime error: stack overflow` on every workload. Kept so the next
  reader does not re-derive it; the design's §5.2 says why.
- `s3_suite.sh` — the **full** `scripts/test` on iteration 1, with the failure
  names. The fast lane is not enough for a generator change.

Output directories (`probes/out_s3*`) live on the remote box and are **not**
synced back, so anything you want to read must be printed by the script
itself.
