---
title: Stage generic leaf summaries for larger arithmetic bodies
status: open
labels: [compiler,x86,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Finding

While testing checked caller saves, the selected arithmetic leaf below required
RAX/R11/R10 and generated a source-to-x86 certificate, but the generic
`probe_leaf_summary` declaration was rejected with kernel `OutOfFuel` under
the existing default budget:

```heather
import bitvec;

fn leaf(left: BitVec(64), right: BitVec(64)) -> BitVec(64) {
    bitvec::bxor(64,
        bitvec::add(64, bitvec::band(64, left, right), bitvec::sub(64, left, right)),
        bitvec::add(64, bitvec::bor(64, left, right), bitvec::bxor(64, left, right)))
}
```

The failure precedes all composed-caller save proofs. The save/restore fixture
uses the already accepted two-register leaf instead. No budget was increased.

## Acceptance

- Stage the generic leaf-summary conversion so the source/ABI contract above
  checks with neutral inputs under existing budgets.
- Keep exact instruction indexing, fetched-call premises, and corruption
  refusal; do not replace neutral inputs with literals or relax the contract.
- Add this source as a regression control and run the full suite.

## What it assumes from elsewhere

- [[x86-reusable-callee-certificates]] supplies the generic leaf-summary boundary.
- [[function-ir-x86-proof-scaling]] owns source-to-IR/body proof scaling.
- [[x86-composed-caller-register-saves]] owns the checked save/restore customer.
