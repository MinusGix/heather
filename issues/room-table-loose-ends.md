---
title: Lower the optimizer and the statement compiler's functions under the least room table
status: closed
labels: [native,x86,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-16
updated: 2026-11-17
---

Two loose ends of [[function-frame-sized-by-use]]:

- The optimizer's `Function::lowers` (`function_ir_optimize.hthr`) and its probe in `crates/cli/src/native/verified.rs` still lower under `index_rooms()` (`136 * Succ(g)`); any room table the lowering accepts would do, and `program_room` or the planned table is smaller.
- The statement compiler emits its functions under `program_room` (every function saving six registers) because its bound must not depend on `homes.places`. compile-x86 instead reads each function's saves off its placement and states the least table as a literal; the statement compiler could do the same, with `program_calls_room` computed from that table.

## Closed

- The statement compiler's functions are emitted under the homes' own table (`Homes.rooms`, `Prog::links(functions, places, rooms, names)`, `Homes::calls_room`), and `write-elf` states the planned one (`program_rooms_planned`) as a literal. With no table given it is `program_rooms`, as before. `docs/native/native-procedure-frames-design.md` §6.5.
- The optimizer's `Function::lowers` and its probe stay under `index_rooms()`: that call asks only whether a placement lowers and reads nothing of the room, so a smaller table changes no answer and costs its evaluation at every probe.
