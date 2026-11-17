---
title: bv_decide: send algebra to ring, bit-level leftovers to SAT
status: open
labels: [bitvec,solver,tactics,feature]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

Products of two variables are out of reach for SAT (8-bit `x * y = y * x` is over a million hints). Goals that are algebra modulo `2^n` belong to `ring` over words. A combined tactic could normalize with `ring` first and send only the bit-level remainder (masks, shifts, comparisons) to `bv_decide`.

Parent: [[lrat-certified-bitvector-decision]].
