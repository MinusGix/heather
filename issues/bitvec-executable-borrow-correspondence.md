---
title: Prove the structural borrow bit agrees with arithmetic borrow
status: closed
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
- 2026-08-28: Closed constructively at open width and operands.  The proof
  strengthens the induction with an incoming borrow, normalizes the
  bit-with-tail arithmetic on both sides, and uses the even/odd strict-order
  laws now exposed by `std/nat`.  `borrow_sub_bit_true_iff` is the public
  equivalence; `borrow_sub_of_bit_true` and `borrow_sub_bit_of_borrow` are its
  forward and backward APIs.  Open-width tests exercise the equivalence and
  both directions, including the width-64 specialization; the existing
  closed yes/no controls remain computational controls rather than standing
  in for the theorem.
