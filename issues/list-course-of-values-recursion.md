---
title: Course-of-values recursion on lists and other inductives, not only Nat
status: closed
labels: [frontend,elaboration,termination,stdlib,design]
created: 2026-09-18
updated: 2026-09-18
---

`utf8::decode` consumes one to four bytes per step, so its self-call lands
on a grandchild (or great-great-grandchild) of the scrutinee. Structural
recursion on lists refuses that — "argument `bytes` has to be one of the
recursive fields bound by the enclosing `match`. A deeper subterm is refused
too" — while `Nat` admits it since [[recursion-at-deeper-subterms]]
(`docs/course-of-values-recursion-design.md`, customer `nat::half`). The
`decreases` route is no help either: a measured body written with the
equation bindings its obligations need gets no unfolding equation
([[unfolding-computed-scrutinee]]), so nothing about it is provable at an
open tail.

The decoder therefore recurses on a **fuel** that `decode` sets to the byte
count (`lib/std/utf8.hthr`, `decode_at`), spending exactly as many steps as
bytes so the proofs' induction hypothesis is the bare recursive call. It
works, but it is an API shaped by a language limit, which the library is not
supposed to do ([[string-char-spec-types]] round 2, design §5.5).

Extend the course-of-values window to any inductive: a self-call on a
subterm reached through a chain of recursive-field projections of the
scrutinee, bounded by a constant depth, the way `Nat`'s window is. Customer:
rewrite `decode_at` as `decode` recursing on `rest2`/`rest3`/`rest4`
directly and delete the fuel.

## Log

- 2026-09-18: Design 2026-09-18: docs/list-course-of-values-design.md — the Nat window with `pred` replaced by the recursive-field projection, on chain-shaped Wf inductives; convoy by term with constructor rebuild; customer is the fuel-free `utf8::decode`.
- 2026-09-18: **Done.** `crates/elab/src/wf.rs` carries the `Nat` window to
  chain-shaped `Wf` declarations: `tail_D` as a `Branches::Tail` eliminator,
  the window and convoy threaded as `WfRec`/`WfConvoy`, and
  `GuardKind::Wf.cov` holding the chain, the window and both anchors. The
  customer landed with it — `lib/std/utf8.hthr`'s `decode` recurses on
  `rest`/`rest2`/`rest3`/`rest4` directly, `decode_at` and the fuel are gone,
  and theorems 3–6 close (`decode_at_encode_chars` is now
  `decode_encode_chars`, with no `list_len` anywhere in its statement).
  `docs/list-course-of-values-design.md` §7 records the five amendments the
  implementation made, of which the load-bearing one is that a `Wf` arm's
  child is not a subterm of the arm's value, so the convoyed `match`'s
  codomain is rebuilt rather than synthesized.
- 2026-09-18: Landed 2026-09-18 with the fuel-free `utf8::decode` as customer; a possible gap in the convoy reindexing is [[cov-convoy-motive-second-ambient]].
- 2026-09-18: Landed 2026-09-18 with the fuel-free `utf8::decode` as customer; a possible gap in the convoy reindexing is [[cov-convoy-motive-second-ambient]].
