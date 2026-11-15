---
title: Store marks a function, not one list for the program
status: open
labels: [native,function-ir,memory]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

What a program may store is one list of marks for the whole program
(`program_stores_within(functions, marks)`, `function_ir_writes.hthr`,
docs/native/native-library-exports-design.md §4.1): every function's stores are
read against it at the function's own buffer numbers. That was exact while
a callee's buffers were its caller's first buffers under the same numbers.

A call over views (`Lend`, §3.1 of the design) lets numbers differ: a
callee that stores into its buffer `0`, called over a view of its caller's
buffer `2`, asks the marks to have `0` and `2` both, and so lets every
other function store into its own buffer `0` and `2` as far as this check
goes. Nothing unsound follows: a function's stores are still inside the
loan it was called with (`Stack::Trail`, `Loan`), and the contract at each
lending asks the lending's marks to cover the program's. It is coarse: a
lender must lend to write wherever any function of the program stores at
that number.

## Scope

- Marks a function: `program_stores_within` over a table of marks, one row
  a function, a function's stores and its lends' written views read
  against its own row, and a lend checked against its callee's row (each
  buffer the callee marks is a view lent to write).
- The contract at a lending (`Site::CallsLent`, step V4b) then asks the
  lending's marks to cover the callee's row, not the program's.
- `Lending::writing`'s marks in the generated certificate
  (`crates/cli/src/native/verified.rs`) come from the entry's row.

## Done when

A program with a function that stores into its buffer `0` and a caller that
lends it a view of its own buffer `1`, its buffer `0` lent to read by its
own caller, is accepted, and the same program with the callee's store
moved to a buffer lent to read is refused.

## Log

- 2026-11-12: Built as step V4b of the views (docs/native/native-library-exports-design.md §3.1), because working the lowering of a call over views through showed it is needed there and not only coarse: with two views of one buffer, one to read and one to write, the lender's written view marks its buffer `0`, and under one list the callee would be asked to have its view `0` lent to write, which is the half lent to read.

  - `function_ir_writes.hthr`: `StructuredRegion::Asks(needs, written)` (a call asks that `written` lets be written what its callee needs; a call over views asks it of the views), `ProgramNeeds(functions, needs)`, and as data `program_marked(functions, tables)` with `program_marked_needs` (rows by `marks_row`, a callee's row within its caller's or within the views' by `marks_within`). `program_needs_all` is the instance of one answer for every function, for a program with no call over views (`program_lendless`).
  - `function_ir_lower_calls.hthr`: `Site::CallsLent` is the contract at every lending of the program's counts, a function at a time under a lending that lets it write what it needs. The region theorem takes `region.Asks(needs, lending.written)`, a call is proved against its one callee's contract (`call_step` takes it), the program's induction is `emit_functions_calls_lent`, and `lower_program_lent_needs` is the theorem for a lowered program. The statements at one lending (`emit_functions_after_lent_calls`, `lower_program_lent_correct`, `compiled_returns_over`, `compiled_returns_run`) are corollaries and take `program_lendless`; `program_stores_within` now says it too, `program_quiet` gives it, and a placeless program has it until the placeless check takes a view's base.
  - Probes: `function_ir_writes_tests.hthr` (rows of a caller and its callee, the rows that leave a need out, a reader beside a storer), `function_ir_views_tests.hthr` (the rows of `lending` and of `halving`; no rows are right for a view lent to read whose callee stores through it), `function_ir_lower_reads_tests.hthr` (`beside`: lowered, the reader meets its contract under a lending to read and the storer under one to write, and the storer under the lending to read is refused).

  What is left of this issue: the done-when program needs a call over views to lower (V4c), and the generated certificate still states one list (`{prefix}_marks`, `compiled_returns_written`), which is right for every export there is, none of which lends views. The certificate takes rows when an export does.
