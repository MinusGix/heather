---
title: Lower the optimizer and the statement compiler's functions under the least room table
status: open
labels: [native,x86,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-16
updated: 2026-11-16
---

Two loose ends of [[function-frame-sized-by-use]]:

- The optimizer's `Function::lowers` (`function_ir_optimize.hthr`) and its probe in `crates/cli/src/native/verified.rs` still lower under `index_rooms()` (`136 * Succ(g)`); any room table the lowering accepts would do, and `program_room` or the planned table is smaller.
- The statement compiler emits its functions under `program_room` (every function saving six registers) because its bound must not depend on `homes.places`. compile-x86 instead reads each function's saves off its placement and states the least table as a literal; the statement compiler could do the same, with `program_calls_room` computed from that table.
