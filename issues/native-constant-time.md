---
title: Prove that native code is constant-time under a stated leakage contract
status: open
labels: [native, x86, security]
area: heather-in-heather
created: 2026-10-30
updated: 2026-11-10
milestone: [hih-crypto]
---

Minus (2026-10-30), after BearSSL's *Constant-Time Crypto* and
*Constant-Time Mul* pages: constant-time functions for crypto and security
should be something Heather can prove and require. Not scheduled; kept for
secure code, beside [[native-secret-erasure]].

Design and survey: `docs/surveys/constant-time-survey.md`. In short, constant-time
is non-interference on a leakage trace (control flow, memory addresses,
operands of variable-time instructions), stated relative to a
**leakage contract** that names which instructions are variable-time on
the CPU. The x86-64 default is Intel's DOIT list, so `DIV`/`IDIV` and the
bit scans leak their operands. The compiler reduces the two-run property
to a one-run **leakage transformer**: the target's leakage is a function,
computed from the program text, of the source's leakage. The source side
is a label checker over FunctionIR and `Stmt`, proved sound once, whose
verdict is `= True` by `refl`. The compiler theorem becomes `SimProgram`
plus the transformer (plus `Canonical` at erasure cuts), and every later
pass must produce both.

## Scope when picked up

The note's §11 is the order: the statement and transfer lemma first, then
the transformer for the current compiler, then `Select` and the checker,
then a constant-time library and a first program (a MAC compare, shared
with the erasure work), then contract lines for `MUL`/`DIV` as they enter
the model. A secret surface type, if-conversion as a pass, and speculative
constant-time come later and separately.

## What it assumes from elsewhere

- **[[native-secret-erasure]]** / `docs/surveys/zeroization-survey.md` shares the
  label machinery: the checker's labels discharge erasure's source
  obligation on kept words (survey §8).
- **[[native-procedure-contracts]]**: a procedure callable from
  constant-time code needs a leakage clause in its contract.
- **[[cost-aware-semantics]]**: a cost semantics could share the leakage
  instrumentation, but equal cost is not constant-time.
- Multiplication and division in FunctionIR and the x86 model
  ([[std-nat-multiplication]], [[nat-div-mod-lemma-kit]]) are where the
  variable-time instructions arrive.

## Log

- 2026-11-05: gardener: cites a file it shares with [[native-compiled-code-shape]] (`docs/surveys/zeroization-survey.md`); [[ownership-discipline-over-code]] (`docs/surveys/constant-time-survey.md`).
- 2026-11-10: Scheduled under `hih-crypto` by `docs/native/native-lexer-crypto-roadmap.md` §4.
  The note asks for step 1 (the leakage transformer over the machine's `Step`
  and the statement of the property) **before** the second primitive is
  compiled, not after: every instruction form added for cryptography
  ([[x86-narrow-and-rotate-forms]], [[x86-wide-multiply-and-carry]]) then
  states its leakage when it is added, where retrofitting means revisiting
  each form. SHA-2 is the easy first customer (no secret-dependent branch or
  address); Poly1305 and X25519 are where it bites.
