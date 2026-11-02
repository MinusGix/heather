---
title: write-elf: state each part's live-in set so a join costs one step of liveness
status: open
labels: [native,compiler]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-02
updated: 2026-11-02
---

Found by [[native-heap-arena]]'s `sort` (docs/native-heap-arena-design.md §3.1).

`write-elf` states a program a part at a time and joins the parts with
`Stmt::emits_then_of`. Since that round the live-out sets are literals
(`emission::live_literals`), but a `Then` join still has to show that its
first part's literal is `right().live_with(…)` of its sibling, and the kernel
does that by working out liveness over the whole sibling. Inside a loop the
sibling is the rest of the loop's body, and liveness costs about the
statements times the square of the live set (list unions and differences),
so one join can run out of a declaration's fuel while every part is small.
`sort` was past it until its pass stopped reading lengths back from cells;
a larger loop body, or more words live across one, will meet it again.

## Fix

State each part's live-in set as a literal theorem
(`{p}_li_{id}: s.live_in(homes, o) = [..]` and the `live_head` form where a
part starts with known words), proved at a whole part by `refl` and at a
join from its children's by the equations `live_in`/`live_head` already
compute by (`Then`: the first part's over the rest's), so a join rewrites
with its sibling's theorem and evaluates one step. Untrusted as ever: the
sets are read on the fork, the kernel checks the equations.

## Done when

A tool whose loop body's liveness alone is past a declaration's fuel (a
probe in `native_compile_tests`, or `sort` with its lengths read back from
the cells again) writes its ELF, and no join's evaluation grows with its
sibling's size (`--timings`, `scripts/timings` on the joins' steps).
