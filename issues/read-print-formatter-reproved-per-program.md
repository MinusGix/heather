---
title: Name the print formatter's certificates independently of the program
status: open
labels: [x86,native,performance]
created: 2026-09-28
updated: 2026-09-28
---

## Problem

A `--print` read-loop build certifies the decimal formatter (`line_word`,
`line_start`, `line_length` from `lib/decimal_line.hthr`) through the typed
generator, with declaration and module names built from the program's prefix
(`generate_format(elab, &prefix)` in `crates/cli/src/native.rs`, giving
`{function}_native_line_word_format` and so on). The formatter's code and
register placements are fixed for the profile and don't depend on the
program, but the names do, so every new program re-certifies it cold.

## Attribution (2026-09-28, release CLI, one kernel worker)

- Cold `wc -l --print`: 70 s. The bundled library prefix is about 27 s (shared,
  replayed warm across programs), the formatter 37 s (`line_word` 28.6 s,
  7812 declarations over 177 structured nodes), the program's loop pieces
  5 s, its certificate 2 s.
- Warm rebuild of the same program: 2.6 s.
- The same program with its function renamed (`count_lines` →
  `count_newlines`), over the warm cache: the formatter was re-proved from
  scratch, about 30 s of 36 s.
- The exit profile has no formatter: cold 35 s, of which the loop pieces are
  6 s and the certificate 1.3 s.

## Shape of a fix

Pass a fixed prefix (say `print_format`) to `generate_format`. Program
prefixes end in `_native`, so the names can't collide. The certificate
already reads the parts' names from `FormatPart::prefix`. Measure with
`scripts/perf ab` on a renamed program, as above; the formatter share should
drop to the image-replay cost.
