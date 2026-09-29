---
title: A proven C-style formatting API for native programs (POSIX %d first)
status: open
labels: [x86,native,stdlib,design]
created: 2026-09-28
updated: 2026-09-28
---

The certified `wc` prints GNU's fixed-width pipe format (`"%7d %7d %7d\n"`)
because one field per 8-byte word keeps the formatter and the stores simple
([[native-wc]], `docs/native-wc-design.md` §8). Wanted as well (user,
2026-09-28):

- POSIX's minimal `"%d %d %d\n"` as a basic capability: variable-width
  fields, so unaligned stores or a byte-granular output buffer.
- Longer term, a C-style API ("like C, but proven in Heather") for easier
  conversion of existing programs: printf-style formatting, buffered output
  and the like, each call carrying its meaning as a theorem against a spec
  such as `decimal_digits`.

Nothing here is designed yet. The native formatter today is
`lib/decimal_line.hthr` (four digits in one word, below 10000) and the
three-field `field_word` of the wc round.
