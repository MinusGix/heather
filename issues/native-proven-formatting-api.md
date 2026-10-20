---
title: A proven C-style formatting API for native programs (POSIX %d first)
status: open
labels: [x86,native,stdlib,design]
area: heather-in-heather
created: 2026-09-28
updated: 2026-10-04
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
`lib/decimal_line.hthr` (four digits in one word, below 10000) and
`lib/field_line.hthr` (`%7d` plus a separator as two words, `field_low` and
`field_high`, below 10^7) of the wc round.

## Log

- 2026-10-03: First piece designed: `%*d` for any 64-bit count and any width, a hand-proved library loop over a table of powers of ten (docs/native-wc-command-design.md §7), owned by [[native-wc-as-a-command]]. POSIX `%d` is its width-1 case.
- 2026-10-04: `%*d` landed as library code (`lib/elf64_format_width.hthr`, `format_runs`): RAX count, RDX width, RDI cursor; output `padded_decimal(w, n)`. POSIX `%d` is `w = 1`. No client yet; [[native-wc-as-a-command]] C4 is the first.
