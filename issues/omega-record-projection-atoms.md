---
title: omega can't use a record field of a local as an atom
status: closed
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

Found writing `examples/x86-native/wc.hthr`'s fold proofs (docs/archive/native-wc-design.md
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

## Log

- 2026-09-29: Done (docs/omega-measure-reduction-design.md §10). The term omega met was not a
  reduct: `WcState` is closed and not dependent, so it registers no projection
  definitions and `s.words` *is* the inline walk `fst(snd(snd(s)))`, which the
  speller had no case for. Fixed in the speller: a field read spells as `r.name`
  from the receiver's type (`field_read`), and a record value spells as its
  constructor (`ctor_value`). In source spellings only, a projection nothing
  else names spells as its bounded weak head (`projection_reduct`). In omega, a
  projection whose weak head is arithmetic is reflected as that reduct, and
  `convertible_atom` compares field reads by receiver. An unrelated unspellable
  fact was already declined rather than fatal
  (omega-inside-match-arms, 2026-09-28), so v5 closed as soon as the fact spelled.

  Dogfooding: examples/x86-native/wc.hthr loses `add_grown`, `words_grown`,
  `joins_word`, `starts_word`, `from_zero`, `from_zero_outside`. Its folds and
  `wc_next_words` use inline `omega`, the latter at the arms' reduced statements.
  `count_wc_input` states `wc_words`/`wc_bytes` in typed `let`s, because omega
  does not unfold one head into another (§5). Tests:
  crates/elab/tests/omega_record_fields.rs (10 rows; 9 fail on the old
  elaborator, and the tenth is the already-fixed unrelated fact).
