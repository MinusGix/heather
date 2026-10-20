---
title: Retire ir_v1 and certgen onto FunctionIR, or keep it as the source IR
status: open
labels: [ir,design]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-20
updated: 2026-10-20
---

Whether `ir_v1` and the certifying generator over it (`lib/ir_v1.hthr`,
`lib/certgen_*.hthr`) are retired onto FunctionIR, or kept as the Nat-level
source IR.

Split out of [[native-one-program-logic]]'s third question: the native
program logic (`docs/native-program-logic-design.md` §1) does not touch
`ir_v1`, so the question belongs to the round that picks one source IR for
a compiler pass written in Heather (`hih-passes`). Lean at filing: retire it
then, since FunctionIR is what the x86 path lowers and what passes would
read; keep it until that pass exists, because the certgen tests are its
only users and cost nothing while frozen.

## What it assumes from elsewhere

- **[[certifying-generator]]** owns certgen.
- **[[in-language-certificate-emission]]** owns moving emission into Heather.
