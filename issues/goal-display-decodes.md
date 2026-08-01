---
title: Goal statements and expected-type diagnostics print undecoded codes
status: open
labels: [frontend,diagnostics,ergonomics]
created: 2026-08-01
updated: 2026-08-01
---

From the [[el-reader-decode-audit]] round (2026-08-01): every structural *reader* of a wrapped type now decodes, but the one place a wrapped type reaches a HUMAN does not. `theorem t(v: Nat): B(v) { ?g }` renders the goal as `?g : El[0](app(u1^{·^1}; [0,1] Nat → Ty 0; x0))` — discharge works fine (`on ?g := …` checks), so this is diagnostics-only, but the display is unreadable exactly where readability is the product.

Two sites, same class, one round:
1. Goal statements (`?g : …` rendering): decode/δ-unfold for DISPLAY only — the elaboration itself must keep the lazy wrapped form (that laziness is load-bearing, docs/types-as-expressions.md).
2. `elab_lam_check`'s "a lambda needs a function type here, found {expected:?}" prints the undecoded expected type; one line, same display-decode helper.

Care: display-decode should be bounded (the audit's rule of thumb, docs/record-type-values.md §6.3 — reduce as little as possible) and must never affect what is checked, only what is printed. A negative control worth having: a deliberately unreadable-before, readable-after goal in the test suite, plus one where decode hits its bound and falls back to the raw form rather than looping.
