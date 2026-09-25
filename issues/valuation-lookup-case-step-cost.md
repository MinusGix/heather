---
title: A case step at a BitVec(64) result costs in proportion to the width
status: open
labels: [kernel,performance,x86,certificates]
created: 2026-09-25
updated: 2026-09-25
---

## Scope

A `match` on a Nat literal whose result type is `BitVec(64)` costs about 1.3K
evaluator steps per `Succ` it peels, whatever the arms hold. A plain nested
Nat match with a `Nat` result costs 2 steps per level, and the same lookup at
`BitVec(1)` about 230. So the cost follows the result type's width, not the
work: something materialises `BitVec(width)` (a 64-deep Σ chain) at every case
step.

Measured 2026-09-25 while making composed certificates scale
(`docs/native-first-program-design.md` §10.1), with `probes/dec/lookup*.hthr`
(untracked). A valuation `λ width id => match id { Zero => …, Succ(id_1) => … }`
looked up at id 51 costs 67 710 steps, at id 200 costs 262 006, and at id 0
costs 65. Replacing the arms with neutral `values(width, 0)` changes nothing.

Every generated `_valuation` in the structured and loop certificates has this
shape, so a lookup of port `k` costs about `1.3K × k` steps, and port ids reach
the hundreds in a long body. The crossing carries in `structured_cert.rs`
dispatch with `Nat::leb` over their few entries instead (flat, about 23K per
lookup), which is a workaround at one site, not the fix.

## Acceptance

- Attribute the per-step cost: which evaluation of the motive or result type
  happens per case step, and why its width matters.
- Either the kernel stops paying it (a lazy motive, or not re-evaluating a
  closed result type per step), or the generators use a lookup whose cost does
  not grow with the id. Say which, on evidence.
- A bench family or test pinning the per-step cost flat in the id.

## Log

- 2026-09-25: The structured generator's valuations now avoid the cost (`valuation_body` in `structured_cert.rs`). They dispatch on the id through a balanced `Nat::leb` tree, so a lookup costs a logarithmic number of comparisons, not a step per `Succ`. The kernel cost itself remains, and so does the bench pinning it.
