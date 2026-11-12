---
title: Exclusive or, complement and rotates at BitVec have no symbol (^ is power)
status: open
labels: [surface-syntax,bitvec,design,ergonomics]
area: language
created: 2026-11-12
updated: 2026-11-12
---

`+ - * << >> & |` are designated at `BitVec(n)`, and `<`/`≤` are the unsigned orders. Exclusive or, complement and the rotates have no symbol: `^` at `BitVec(n)` is `BitVec::pow`, as it is at every other carrier. `lib/native/crypto/sha256_round.hthr` is the cost in one place (2026-11-12): every line of the round is a chain of `.bxor(…)`, complement is `x.bxor(0xffffffff)`, and a rotate is a pair of shifts joined by `.bor`.

To decide (Minus's, it is surface):

- **Exclusive or.** `^` is taken by power. Candidates: `⊕` with an ASCII spelling beside it (`^^`), or keep the method and add only the rotates. Rust's and C's `^` would need power to move, which the mathematics library uses everywhere.
- **Complement.** Prefix `!` is Boolean negation and `¬` is the proposition's; `~` is free.
- **Rotates.** Methods are enough (`x.rotate_right(6)`); what is missing is that the reflected fragment and FunctionIR have them ([[bitvec-rotates-and-wide-ops]], [[function-ir-alu-core]]).

Each new symbol is a token in three lexers (the Rust lexer, tree-sitter and `lib/lang/lexer`, whose compiled form is linked, so `scripts/linked` and `scripts/lexer-probes` rerun) and a designation slot.

Done when: the round functions of SHA-256 read as FIPS 180-4 §4.1.2 writes them.
