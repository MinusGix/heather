---
title: A hole beside a splitting field default is an internal error
status: open
labels: [elaborator,tactics,bug]
area: tactics
created: 2026-10-01
updated: 2026-10-12
---

A `?hole` in a record construction whose omitted field has a tactic default
that splits (`split_all`) stops elaboration with an internal error instead of
reporting the hole's goal:

```heather
fn lines_program() → Filter<Nat>(counting(line_step), 0, [λ c => c], Line(λ c => c), lines) {
    Filter(λ bytes => ?todo)
}
```

gives `error: internal: more goals than the pre-count reserved` at `?todo`
(found 2026-10-01 while writing the stream filter's programs,
docs/archive/native-stream-filter-design.md). With a default that closes without
splitting (`Filter<Stateless>` with `counts = Nil`) the same hole is
reported as an unsolved goal, as it should be. The hole's goal slots are
pre-counted from the source, and the default's tactic run appears to open
goals the count did not reserve.

Repro: the module above, with `newline`/`line_step` as in
`examples/x86-native/wc_l.hthr`, importing `filter_program`,
`stream_filter` and `function_ir_loop`.

Related: [[field-defaults-under-locals]].

## Log

- 2026-10-12: 2026-10-12: Parameter defaults (docs/named-arguments-design.md §9.6) fill an omitted parameter the same way, so a `?hole` beside a call whose omitted default splits presumably meets the same pre-count; not reproduced.
