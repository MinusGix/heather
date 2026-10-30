---
title: omega reads a Bool guard `b.IsTrue()` by its structure
status: open
labels: [omega,tactics,proofs,ergonomics]
area: tactics
milestone: [tac-arith]
created: 2026-10-30
updated: 2026-10-30
---

`omega` skips a fact whose type is `b.IsTrue()`, whatever `b` is. Guards built
from `Nat::leb`, `&&`, `||` and `!` are how the library carries
proof-irrelevant side conditions (`Format::canonical`, the x86 asm tables,
FunctionIR evaluation), so every client takes them apart by hand with
`is_true_and` / `leb_sound` / `leb_complete` before omega can see them: 24
library files do (x86_64_asm_table 40 uses, function_ir_eval 38,
native_structured_meaning 26, …). `docs/bool-guard-reflection-design.md` §3.2
has the before/after at `Format::canonical`.

Wanted: before giving up on a `b.IsTrue()` fact, read `b` by structure:

- `n.leb(m)` as `n <= m` (`Nat::leb_sound`), and `!n.leb(m)` as `m < n`;
- `a && b` as both (`Bool::is_true_and`), `a || b` as a disjunction
  (`Bool::is_true_or`, then the existing `Or` split), `!a` as `¬a.IsTrue()`
  (`Bool::is_true_not`);
- a Bool definition by one δ step, as defined propositions already are
  (design §11 of `docs/omega-measure-reduction-design.md`), so
  `F.canonical(m, b).IsTrue()` reads through `canonical`'s `let`s;
- a stuck `match n { Zero => x, Succ(_) => y }` by splitting `n = 0` /
  `0 < n`, the way §16 splits a truncated subtraction.

A goal `b.IsTrue()` is the converse (`leb_complete`, `is_true_and_intro`,
`is_true_not_intro`), refuting the negated guard.

Open question: an opaque Bool atom (`F.specials.reserves_top()`) is
propositional. `rt: r.IsTrue()` beside `(!(r && …)).IsTrue()` is a
contradiction only propositionally; either omega gets a propositional atom
kind (a case split on `r.is_true_dec()` per atom, bounded like the
subtraction splits) or such atoms stay the caller's to discharge.

Acceptance: `Format::canonical_elim`'s conjuncts close as `omega(ok)` (the
`∨` conjunct may stay a `reflects_elim`), a library `canonical_elim` whose
conjuncts only feed omega is replaced by `omega(….ok)`, probes in
`lib/_tests/std/tactic/omega_tests.hthr` for each connective, and a negative
control that a guard over an unreadable Bool function is still skipped with
a residual that names it.

Related: [[decide-bit-is-the-comparison]] (the other route, which removes the
Bool/Prop gap at definitions instead of in the tactic).
