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
docs/native-library-exports-design.md §4.1): every function's stores are
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
