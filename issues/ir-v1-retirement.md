---
title: Retire ir_v1 and certgen onto FunctionIR, or keep it as the source IR
status: closed
labels: [ir,design]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-20
updated: 2026-10-24
---

Whether `ir_v1` and the certifying generator over it (`lib/certgen/ir_v1.hthr`,
`lib/certgen_*.hthr`) are retired onto FunctionIR, or kept as the Nat-level
source IR.

Split out of [[native-one-program-logic]]'s third question: the native
program logic (`docs/native/native-program-logic-design.md` §1) does not touch
`ir_v1`, so the question belongs to the round that picks one source IR for
a compiler pass written in Heather (`hih-passes`). The design's lean (§3.2):
retire it in burn B2, once [[function-ir-verified-lowering]] compiles the
pure examples, since FunctionIR is what the verified compiler reads; keep it
frozen until then, because the certgen tests are its only users.

## What it assumes from elsewhere

- **[[certifying-generator]]** owns certgen.
- **[[in-language-certificate-emission]]** owns moving emission into Heather.

## Log

- 2026-10-24: Done in B2 (2026-10-24): retired. `lib/certgen/ir_v1.hthr` and certgen are deleted; FunctionIR is the one source IR. A frozen copy stays as an elaborator corpus, `crates/elab/tests/fixtures/ir_v1.hthr`, used by `crates/elab/tests/ir_v1.rs` (its acceptance and the emission-walk guard) and the frontend bench.
