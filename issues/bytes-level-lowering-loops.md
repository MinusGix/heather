---
title: The bytes level's plain loop lowered by Site::loop_iterates on fuel
status: open
labels: [native,function-ir,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Item 5 of [[bytes-level-lowering]]: the plain loop (`Body::Loop`), by `Site::loop_iterates` on the run's fuel with the counter-free head `Stack::LoopAt` and `loop_turns`, `loop_body_runs_by` at `Mem := heap_in` (`lib/native/bytes_level/bytes_level_lower.hthr`). A pass has its own valuation (its locals start empty), so the head carries the state as words in registers, a reference as its address, which `Stack::LoopAt` already states over any words.

## Done when

`Body::emit` lowers a loop and `Body::emit_emits` covers it; the language's `countdown` probe compiled with its theorem.

## What it assumes from elsewhere

- **[[bytes-level-lowering-routines]]** owns the scope valuation's existence. Assumed: a pass's run determines its valuation as a routine's does.
