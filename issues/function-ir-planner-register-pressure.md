---
title: The register planner loses a value in a calling loop's body where an operand's register or a wanted one would do
status: open
labels: [native,ir,x86,planner]
area: heather-in-heather
milestone: [self-lexer,nh-library]
created: 2026-11-12
updated: 2026-11-12
---

Found compiling the scanner's token loop for linking ([[native-library-exports-design]] round E3, [[self-lexer-linked]]): `heather compile-x86` answered "the verified lowering refused this program with the planner's placement" for `scan_from` (`lib/lang/lexer/lexer_span.hthr`) as it was first written, twice, and each time the function was fine and the placement was not. The lowering is right to refuse a placement it cannot check; the planner (`StructuredRegion::plan_in`, `Node::choose_by`) is untrusted search and is where this is.

## What the loop has

A loop over a span that calls: five words of state (the span's address and length, and three the pass changes), a counter, and the body's calls. A function that calls plans from `call_pool`, which is the caller-saved registers without RAX, so inside the body three registers are free for everything the body computes: the two the state and the counter leave, and RAX between calls.

## The two refusals

1. **A node that reads its operand last still takes a fresh register.** The test was `i < length && !(state = FAIL || state = DEAD)`: three bits live at once (the bound's, and the two equalities) with a constant in the third register. The second equality reads that constant for the last time, so its bit could take the constant's register (`CMP; SETcc` into it). `choose_by` gives an operand's register only to arithmetic and moves (`prefers_operand`), finds no register free, and answers RAX, which held the first equality's bit. The `||` after it then reads a value no register holds. Writing the test the other way round (the state first, the bound last) keeps two bits live and is what the source does now.

2. **A value put where a later output is wanted, with no way back.** The pass's three new words were computed in the order state, offset, last: a call, an addition, a call. Each call's result has to leave RAX (the planner counts a value as read past a call when any call of the region comes before its read, the call that made it included), the addition's operand is still read by the second call so it cannot be written in place, and the third value finds no free register. It takes the first dead one in pool order, which is the register the *offset's* next value is wanted in; the offset's move then goes elsewhere in that arm, the two arms of the pass disagree, and the meet loses it. Planning the branch `apart` does not help: it keeps clear of wanted registers only while another is free. With the offset as the last parameter the addition is computed last, in place, and every value lands where it is wanted; that is the parameter order in the source now.

Both were found with a probe that mirrors `emit_calls` and names the node it refuses, the places it was given and what each register held (`scripts/lowering-refusal-probe.hthr`: copy it beside the module, name the function, check it).

## What would fix it

- `choose_by`: a comparison (and any node whose instruction form allows it) may take the register of an operand that dies at it, as arithmetic does.
- A value whose only read is a move into an output takes that output's wanted register when it is free at the move (coalescing by looking one node ahead), before any other dead register.
- `read_past_call` per value: a call's own result is not read past that call. This alone would have let the third value stay in RAX.
- Say which function and which node was refused in `compile-x86`'s message (the probe's first line), so the next one does not need a probe.
- Beyond the heuristics: the callee-saved registers behind a save and restore in the frame, which the function contract already has room for, would more than double what a calling loop's body has.

## Done when

The scanner's loop compiles in either order of its test and with its parameters in the specification's order (`state, i, last`), the source says so by being written that way, and `compile-x86`'s refusal names the function and the node.
