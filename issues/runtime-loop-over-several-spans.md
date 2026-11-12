---
title: A runtime fn's loop is lent one span only
status: open
labels: [native,runtime,generator]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-12
updated: 2026-11-12
---

A `runtime fn` that loops is lent one span: `Setup::GuardedSpans` and `runtime_measured_instance` (`lib/native/runtime/runtime.hthr`, `rt_loop.hthr`) build the measured instance for a function whose world is a file of one span. A function with no loop may read several spans, and a loop may call a function lent another span of the same file, but a loop whose own parameters include two spans is refused.

Customers: a comparison of two buffers (`memcmp`, a constant-time equality for a digest), a copy from one span to another once the write half is exported, a lexer that reads the source and a table.

## What it would take

`Fun::GuardedBy<I, K>` is already keyed (the worlds are indexed by the file and the recursion by a key), so the family is there: the key becomes the tuple of the spans, or the file itself. The generator's reading of the parameters (`rt_lent`) takes one leading span and its length word; it would take each leading pair. The loop's lowering keeps the home words of every lent span in place, which is two more pinned registers a span, and that meets [[function-ir-planner-register-pressure]] at once: a calling loop over two spans has one free register in its body.

## Done when

A `runtime fn` that compares two lent spans byte by byte in one loop compiles, with its `agrees_over` at every file.
