---
title: prog_sound needs every postcondition to allow the depth-zero answer, which a promised nonempty view does not
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-site-facts-into-the-checker]]. `prog_sound` builds a program's world by depth, and at depth zero every call answers its argument, the word 0 and an empty view, so `IdleOk` asks every postcondition to allow that answer. Since every element read owes its bound, a read through a view a callee answered needs the callee to promise a nonempty view, which the depth-zero answer breaks: `returned_sound` and `beside_sound` in `lib/_tests/lang/ownership/call_check_tests.hthr` are composed by hand from depth two, as `after_sound` was for a postcondition on a word. Each such program needs its depths composed by hand, and a recursive one cannot be.

## Wanted

A world that states termination (the meaning clocked, §18.1) so `prog_sound` needs no postcondition of a depth-zero answer, or a `prog_sound` that composes from the first depth at which every postcondition holds.

## Done when

`returned_sound`, `beside_sound` and `after_sound` hold at every depth from `prog_sound` alone.
