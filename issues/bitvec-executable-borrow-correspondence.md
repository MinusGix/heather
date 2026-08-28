---
title: Prove the structural borrow bit agrees with arithmetic borrow
status: open
labels: [stdlib,mathematics,proofs,x86]
created: 2026-08-28
updated: 2026-08-28
---

`std/bitvec` now has two subtraction-borrow views. `borrow_sub(n,a,b)` is the
reusable arithmetic proposition `toNat(a) < toNat(b)`. `borrow_sub_bit` is the
linear ripple-borrow Boolean required by executable machine semantics without
normalizing an open comparison at width 64.

## Acceptance

- Prove `(borrow_sub_bit(n,a,b) = True) ↔ borrow_sub(n,a,b)` at an open width
  and open operands.
- Expose convenient forward and backward theorems, parallel to the existing
  carry API.
- Cover incoming borrow internally if that makes the induction statement
  compositional; the public subtraction theorem starts with no incoming
  borrow.
- Retain closed yes/no controls at small and machine widths, but do not present
  them as the correspondence proof.

## What it assumes from elsewhere

- **[[fixed-width-bitvectors]]** owns both the structural and arithmetic views.
  This issue owns only their generic correspondence.

## Log

- 2026-08-28: Filed from the x86 `SUB`/`CMP` slice. The executable ripple is
  linear and its closed borrow/no-borrow controls compute at widths 4 and 64.
  The architecture uses it for `CF` and the low-nibble instance for `AF`; the
  open arithmetic bridge remains deliberately explicit here.
