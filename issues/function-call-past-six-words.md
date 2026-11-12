---
title: A call passes at most six words, and a span is two of them
status: open
labels: [native,x86,ir,design]
area: heather-in-heather
milestone: [nh-library,crypto-hash]
created: 2026-11-12
updated: 2026-11-12
---

A call of a compiled function passes its arguments in RDI, RSI, RDX, RCX, R8 and R9 and nothing on the stack, so a function takes at most six words. A span is two of them, its address and its length. The lowering has six places for a call's arguments (`argument_registers`, `lib/native/function_ir/function_ir_lower_calls.hthr`), a statement's call checks `arguments + 2 * lent <= 6` (`Layout::fits_lent`, `lib/native/native_compile.hthr`), and `compile-x86` answers that it "passes at most six, in registers" (`crates/cli/src/native/verified.rs`).

Where it already binds:

- `copy_window(out: span mut, text: span, from, end)` is exactly six, so a third word (a count apart from the window) had no room.
- A loop keeps its state in its parameters: `copy_span` is two spans, a count and an index. A loop over two spans with two more words of state does not fit, and a `runtime fn` has no other place for state than a parameter or a span.
- The hash's `compress(state, block)` is four words before any index or round count, which leaves two.

## Ways through

- Arguments past the sixth at the caller's RSP, as the System V convention has them. The frame already has the room laid out by one constant; the contract (`CalleePre`) would say where they are read, and an export's Rust declaration follows the same convention with no change.
- A span of words: the state a loop cannot hold in registers kept in a buffer the caller lends. This needs no new convention and is what the hash does with its eight state words anyway. It costs a load and a store for each use.

## Done when

A function of eight words is compiled and called from a function and from Rust, with its contract proved as the six-word ones are; control: nine is refused with the count named.

## What it assumes from elsewhere

- **[[function-frame-sized-by-use]]** owns the frame's size, which outgoing arguments add to.
- **[[native-register-moves-and-convention]]** owns the convention's statement.
