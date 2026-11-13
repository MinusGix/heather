---
title: A statement lends the buffers it names, and windows of them
status: open
labels: [native,ir,memory,design]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

A statement of `Source` calls a function over buffers by lending the source's first `lent` buffers, whole and in order (`Prog::function_call`, `Layout::homes_block`, `Layout::fits_lent`, `lib/native/native_compile.hthr`). It cannot lend a view: `StructuredRegion::scoped` refuses `Lend` ("a call over views is a function's to make, not yet a statement's", `lib/native/native_structured.hthr`), and `StructuredRegion::Ok` is false of it (`lib/native/native_compile_structured.hthr`).

What a program does instead is call a function that lends. `tail_c_window` (`lib/native/native_tools.hthr`) is the tool: its statement lends its two buffers whole to `copy_window`, which lends a window of each to its loop. That closed [[source-buffers-as-views]]'s done-when by composition and it is enough for everything built so far.

## What the composition does not give

- **Which buffers.** A call lends the first `lent` buffers, so a tool declares its buffers in the order its callee takes its spans (`tail_c_window` declares `out` before `text` for that reason), and a tool with three buffers cannot call one function over the first and third. A function written in FunctionIR can renumber (`view_lender` lends its second buffer as its callee's first, `lib/_tests/native/native_compile_tests.hthr`); a `runtime fn` cannot, its spans being the file's in order.
- **How many.** `Layout::fits_lent` asks `arguments + 2 * lent <= 6`: three buffers and no words, or two and two. Past six registers is [[function-call-past-six-words]].
- **A window with no function between.** A statement that would lend bytes `a` to `b` of a buffer to a reader goes through a lender written for the purpose. At the `rt` level a lender's first view is its written span (`FTm::own_first`, `lib/native/runtime/rt_file.hthr`), so a `runtime fn` that only reads cannot lend at all, and the lender is hand-written FunctionIR.

## What building it takes

- `Stmt`'s `Compute(Call(…))` naming the buffers it lends, and `Lend` accepted by `scoped` with its views over them.
- In the statement compiler: `Target::lending(held, count)` over a list of views and not a count (`Target::CalledWith`, `Target::loan`, `Target::goes_calls`, `Target::Lends`, `function_answer`, `Target::function_performs`, `lib/native/native_compile_function.hthr`), and the facts a view's bounds need. The function compiler reads them off its path (`File::at_most`); a statement has no such record, so either the statement compiler grows one or a statement's view is checked by code it emits (a compare and a branch to an exit) and the proof reads the branch.
- The meaning already has the case (`env.compute(call, Lend(…))`, `lib/native/native_structured_meaning.hthr`).

## Done when

A tool lends its second and third buffers to a function of two spans, and a window of a buffer to a function that reads, with no lender written for either; controls: a window past the buffer's length and a store through a view lent to read are refused.

## What it assumes from elsewhere

- **[[statement-byte-nodes-on-shared-leaf]]** would take a statement's home as a word, which this issue makes one.
- **[[views-of-one-buffer-apart]]** owns two views of one buffer.
