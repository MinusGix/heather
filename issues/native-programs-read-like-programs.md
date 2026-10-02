---
title: A native program reads like a program: the author-ergonomics round
status: open
labels: [native,surface-syntax,stdlib,design]
created: 2026-10-02
updated: 2026-10-02
---

Round anchor. A native program should read like a program in another
language, with proofs only as long as their ideas. Today
`examples/x86-native/wc.hthr` has 320 lines: about 25 are program, about 30
spec, and the rest hand proof and plumbing. The round is scoped in
docs/native-programs-read-like-programs-design.md.

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
