---
title: "Facts on demand: open producers, search with a budget, a compiler that skips what it cannot prove"
status: open
labels: [compiler, design, traits, tactics]
area: heather-in-heather
milestone: [hih-native-heather]
created: 2026-11-01
updated: 2026-11-01
---

`docs/compilation-vision.md` §6.2 (Minus, 2026-11-01): facts are open classes
with lazy dispatch methods, the cheap producer first and a fuel-bounded
search last, a check being a search with a small budget, and a failed search
skipping the optimization. This issue owns making that real.
`docs/facts-on-demand-design.md` is the design and the record of the first
round.

## What landed (2026-11-01)

- **Search rules**: an evidence rule whose premise has a default
  (`h: i < n := omega`) is built as a call, so the tactic runs in the goal's
  context, and is tried after every plain rule (`crates/elab/src/resolve.rs`,
  `is_search_rule`). No image change.
- **`Synth`**, a host request running `:= infer`'s search at a handle,
  refused with the trace when nothing answers
  (`docs/host-elaboration-interface-design.md` §21).
- **`request` / `request_in` / `budgeted`** (`lib/std/tactic/fact_request.hthr`):
  producers, then the requester's fallbacks under a request budget, each
  answer checked at the goal; `None` means skip.
- **`InBounds` over a checked-reads language** (`lib/lang/facts/`): the
  compiler proved once for any facts (`Compiled::runs`), producers (verified
  range analysis, user lemmas), the compiler's budgeted exhaustive check,
  and the `compile_reads` generator. Probes:
  `lib/_tests/std/tactic/fact_request_tests.hthr`,
  `lib/_tests/lang/facts/read_facts_tests.hthr`.

## What is left here

- Facts over `rt` code once `runtime fn` reflects bodies: the same request
  over `rt` reads, with a call's facts as the request's locals (design §8).
- Ordering several search rules about one fact by cost, or letting a check
  closed by computation be a plain-rule premise despite Paterson's condition
  (design §8 (a)–(c)).
- A `fact` marker, only if facts and propositions ever need to differ.

## What it assumes from elsewhere

- **[[infer-proposition-evidence]]** owns evidence rules and their search.
  Assumed: rules about one relation coexist and each is a kernel-gated
  trial.
- **[[runtime-fn-reflected-language]]** owns `rt`. Assumed: its reads can be
  addressed by a generator the way `prog_read(p, i)` is here.
- **[[unique-fact]]** owns the second fact.

## Log

- 2026-11-01: Filed with the first round: search rules, `Synth`, `request`,
  and `InBounds` end to end (of four reads, three checks dropped by the
  range analysis, the range analysis and the exhaustive check; the fourth,
  a real out-of-bounds read, kept).
- 2026-11-05: gardener: cites a file it shares with [[regex-dfa-compiler]] (`docs/compilation-vision.md`).
