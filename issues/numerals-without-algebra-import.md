---
title: Numerals at BitVec without importing algebra
status: closed
labels: [language,frontend,diagnostics]
area: language
created: 2026-11-02
updated: 2026-11-03
---

A numeral at `BitVec(w)` (`let x: BitVec(8) = 10`, `c.eq_bit(10)`, `[97, 10]` at `List<BitVec(8)>`) works only when the module imports `algebra`. The instance `Numeral<BitVec(n)>` is declared in `lib/std/bitvec/bitvec.hthr`, but without the class `algebra::Numeral` in scope the numeral is a `Nat`. The error then says "this has type `Nat`, but `BitVec(8)` is expected here", which gives no hint that an import is missing. Probed 2026-11-02, following Minus's PR #394 review: the native code was writing `BitVec::ofNat(10)` everywhere because the numeral did not work.

## Scope

- A numeral in a checking position at a carrier with a `Numeral` instance resolves it whenever the instance is visible (its module imported), whether or not `algebra` is. The class is the elaborator's own protocol, as `Bind`/`Pointed` are, so the user should not have to name it.
- Failing that, the mismatch at a numeral notes that `Numeral<…>` has an instance in an imported module and that `import algebra;` brings the class into scope ([[explain-why-an-import-is-needed]]).

## Done when

A module importing only `bitvec` (and what `BitVec` needs) writes `fn f() → BitVec(8) { 10 }`, and a probe pins it to `BitVec::ofNat(10)` by `refl`.

## Log

- 2026-11-03: Done. The literal classes are read by identity (`Elaborator::syntax_class`, keys in `crates/elab/src/literals.rs`): `algebra::Numeral`, `char::CharLiteral`, `string::StringLiteral`, `rat::HexLiteral`, `rat::DecimalLiteral` apply whenever their module is in the closure. Probe: `lib/_tests/std/bitvec/literal_closure_tests.hthr` (imports bitvec and byte only). The broader prelude question went to [[std-prelude-facade]].
