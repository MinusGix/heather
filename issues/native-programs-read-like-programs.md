---
title: A native program reads like a program: the author-ergonomics round
status: closed
labels: [native,surface-syntax,stdlib,design]
created: 2026-10-02
updated: 2026-10-03
---

Round anchor. A native program should read like a program in another
language, with proofs only as long as their ideas. Today
`examples/x86-native/wc.hthr` has 320 lines: about 25 are program, about 30
spec, and the rest hand proof and plumbing. The round is scoped in
docs/archive/native-programs-read-like-programs-design.md.

In scope (2026-10-02, user agreed):
- byte tests as words a reader knows ([[byte-vocabulary-for-native-programs]]);
- library fold lemmas, so a count's proof is one per-byte fact
  ([[fold-count-lemmas]]);
- `computes` from per-count facts, and counts named once
  ([[filter-computes-from-count-facts]]);
- `List::split_by` for word-like specs ([[list-split-by]]);
- every example program (wc, wc_l, tr, tr_s, tr_d) rewritten in the new style.

Riding along if small: [[record-update-syntax]] and
[[split-all-closed-tonat-literals]].

Out of scope:
- the effectful author surface (waits on ITrees, [[native-one-program-logic]]);
- argv, files and flags ([[native-wc-as-a-command]]);
- formatting beyond `%7d` ([[native-proven-formatting-api]]);
- the 0xA0 word-break question ([[wc-words-no-break-space]]).

## Log

- 2026-10-02: Decisions (user): byte tests are decided propositions (if b = '\n', Decide connectives, frontend recognises decide trees); record update is s with { f = e }. Design doc §5.
- 2026-10-02: V1–V5 run (design §4.1): none refutes; S3 amended (connectives as short-circuit control flow — eager && hits RegisterPressure in the filter step); S6 now required (split-all-reduce-defined-heads); ZF⇔equality proved without a borrow law; literal reduction risk = Int literals library-wide.
- 2026-10-02: S6 landed: split_all reduces defined heads at decided matches, restates later binders simplified, states literal facts; Cons(Nil, xs) infers. Residue: split-all-revise-hypotheses. Suite 3156 passed.
- 2026-10-02: S1+S2 landed: wc.hthr 320 → 115 lines, wc_l proof two theorems; executables match host tools. Suite 3156. Next S3 (byte vocabulary).
- 2026-10-02: Filed literal-classes-need-importing (S3 papercut).
- 2026-10-02: S3: library + literals (5c32d454) and Equal node (fd95e486) landed; frontend decided matches paused for design (native-frontend-decided-matches, WIP on branch s3-frontend-wip). Filed split-all-through-decisions, filter-default-spells-program-names, native-narrow-compare-fusion.
- 2026-10-03: S4 landed: wc, wc_l, tr, tr_s, tr_d rewritten with decided byte tests (if b = '
  '; predicates as decide_bit<…>()); wc 115 → 84 lines, tr_s/tr_d proofs are one per-byte split_all fact through quiet_computes; counts through fold_counts_*. split_all: eq_bit comparisons with Nat facts, comparison helpers split at the comparison, operands read through constructor encodings; omega splits Nat ≠; frontend compiles a Bool helper that is a connective as branches. S5 (record update) not taken.
- 2026-10-03: S5 landed: `s with { f = v }` (record-update-syntax closed); wc_step's arms name only what they change.
- 2026-10-03: 2026-10-03: Round complete: S1–S6 landed; every in-scope and riding-along item is closed. Next on this line: argv/files/flags (native-wc-as-a-command).
