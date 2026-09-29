---
title: omega can't use a record field of a local as an atom
status: open
labels: [omega, proofs, elaboration, ergonomics]
created: 2026-09-29
updated: 2026-09-29
---

`omega` fails with "Omega could not spell a natural expression" when a goal
or a fact in scope has a record projection of a local as an atom:

```text
record WcState { lines: Nat, words: Nat, bytes: Nat, inside: Bool }
theorem x2(s: WcState, a: Nat): s.words + a = s.words + a { omega }        -- could not spell
theorem x4(w: Nat, a: Nat): w + 1 + a = a + w + 1 { omega }               -- ok
theorem v5(w: Nat, s: WcState, sp: Bool, h: wc_next(sp, False, s).bytes = w): w + 0 = w { omega }
                                                                            -- could not spell
```

Found writing `examples/x86-native/wc.hthr`'s fold proofs (docs/native-wc-design.md
§6, V5). The facts are about states (`s.words`, `step_fold(…).bytes`), so every
arithmetic step needed a helper theorem over plain `Nat`s (`add_grown`,
`words_grown`, `joins_word`, `starts_word`, `from_zero`), applied with the
projections as arguments. The fact `v5` fails on is only *in scope*, not in the
goal, so an unrelated `let` can break an `omega` that worked.

The display speller has a record-projection path (`crates/elab/src/display.rs`,
the `GenDef::RecProj` case), so the term omega meets is probably a reduct
(`named_arithmetic_reduct`'s whnf, or an atom normalisation) whose projection
no longer has the generated-definition head. Not investigated further.

Shape of a fix: key and spell an atom by the term as written when its reduct
has no spelling, and skip (rather than fail on) a fact in scope that doesn't
spell. Then drop wc's helper theorems for inline `omega`s.
