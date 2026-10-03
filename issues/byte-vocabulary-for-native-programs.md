---
title: Byte comparisons and literals a native step can write and the frontend lowers
status: closed
labels: [native,frontend,surface-syntax,function-ir,design]
created: 2026-10-01
updated: 2026-10-03
---

A native program's step still spells byte tests as
`b.unsigned_lt_bit(BitVec::ofNat(10))`, and equality as two nested
comparisons (`wc_l.hthr`'s `newline`, `wc.hthr`'s `space_byte`). The
surface has no shorter form the native frontend recognises:

- `<` is Prop-valued (`Lt`), and no `LinearOrder<BitVec(n)>` exists. `if b < x`
  lowers to a `decide` match on `Or`, which the structured reflection refuses
  (it branches only on a resolved `Bool`).
- `==` is not Heather syntax ("`==` is not used in Heather").
- `10` at `BitVec(8)` has no `Numeral` instance. A char literal is a `Char`,
  and there is no `CharLiteral<BitVec(8)>`.
- The FunctionIR source frontend's only Bool producer is `unsigned_lt_bit`,
  and the x86 lowering has no equality comparison.

The questions are design questions, not plumbing:

- Should a step read Prop-valued comparisons through `decide` (the frontend
  then recognising decision procedures), or should bytes get Bool-valued
  operations under their own names?
- Does equality become an IR node (`sete`) or stay two comparisons?
- What must a literal instance reduce to so the frontend still sees
  `ofNat(width, n)`?

The structured reflection matches the literal head, so an unreduced class
projection would not match.

## Log

- 2026-10-02: Costed 2026-10-02 for [[native-programs-read-like-programs]] (read-only survey):
  - Frontend (function_ir_source/structured.rs ~:459-527): Bool producers are inputs/fields/constants/Inl-Inr and `unsigned_lt_bit` with literal width only; literals must be literally `ofNat(w, k)`; no whnf. Helpers with literal-width BitVec params are expanded structurally (`produce`), so per-width helpers built from `unsigned_lt_bit` and `&&`/`||`/`!` (lib/std/bool.hthr) should expand today (untested); width-generic `{n}` helpers are not expanded.
  - IR has UnsignedLessThan/SignedLessThan only; no Equal node. x86: all Jcc condition codes exist and decode generically; SETcc only SETB/SETL; CMP sets zf = is_zero_bits(sub); no proved `is_zero(sub a b) = eq_bit(a, b)` law, no `BitVec::eq_bit`.
  - `Numeral<BitVec(n)>` / `CharLiteral<BitVec(8)>` would arrive as an unreduced instance projection, which the frontend refuses; needs a closed-instance reduction (elaborator or frontend recogniser).
  - `if P` desugars to `match decide<P>()`, refused (frontend branches on resolved Bool only).
  Proper path ≈12–15 files: eq_bit + its x86 laws, IR Equal node (~20 sites), SETE step form, literal reduction, optional decide recognition.
- 2026-10-02: Decided (user, 2026-10-02): decided propositions — if b = '\n' through Decide instances; frontend recognises decide of BitVec comparison/equality and connective instances; specs use a Bool of a decidable prop. Equality is a real IR node. docs/native-programs-read-like-programs-design.md §3 S3, §5.1.
- 2026-10-02: V1/V3/V4 (2026-10-02, design §4.1): && expands eagerly and the filter step declines it (RegisterPressure, 2 live temporaries) — connectives must lower as short-circuit branches; ZF of CMP = equality proved at any width (~50 lines, no borrow law); literal instances elaborate but arrive unreduced — reduce closed instance projections in elab_overloaded_num_check.
- 2026-10-02: 2026-10-02 part 1 landed: eq_bit + Decide<a = b> at BitVec, <,<= designations, Numeral<BitVec(n)>, CharLiteral<BitVec(8)> (lib/std/bitvec/byte.hthr), literal embeddings reduced, literal arguments deferred. if b = '\n' / ∨ / ∧ / < elaborate and compute. Next: Equal IR node + SETE, frontend decide/connectives.
- 2026-10-02: 2026-10-02 part 2 landed (fd95e486): Equal node + SETE + zf law; eq_bit is a frontend producer. Frontend reading of decide/connectives paused: native-frontend-decided-matches.
- 2026-10-03: 2026-10-03: S4 landed: every example step spells its byte tests as decided propositions (if b = '
  ', 'a' <= b ∧ b <= 'z'), and spec predicates as decide_bit<…>(). The frontend also compiles a Bool helper whose body is a connective as branches. Closing: the vocabulary exists, lowers, and the programs read with it.
