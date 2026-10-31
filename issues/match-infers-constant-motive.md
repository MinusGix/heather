---
title: A motive-less match in inference position takes its constant motive from any arm
status: open
labels: [elaboration,match,inference]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 3 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §6).

`matching::infer_match_constant_motive` only tries arms that bind nothing. Any arm is a candidate: elaborate it in its binder context and strengthen its type past those binders. A type that mentions one declines that arm. Also allow `match h:` in inference position, with the constant motive and the slice-1 equation.

## Done when
- Probe P3 (`let x = match t { A(n) => n, B(m) => m }`) checks; this is the sequencing design's probe P2 (docs/sequencing-surface-design.md §5.1), whose `let x: T =` annotation becomes optional.
- A dependent arm type is still refused, naming the written-motive spelling.
