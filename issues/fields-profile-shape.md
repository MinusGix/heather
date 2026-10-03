---
title: --fields prints exactly three counts from R13–R15
status: open
labels: [native, cli, design]
code: crates/cli/src/native/read_fields.rs @ 357c0afa
created: 2026-09-29
updated: 2026-10-03
---

`build-x86 --read-loop --fields` accepts a record of three or four fields
whose first three are `Nat`, and prints those three in `%7d %7d %7d` for
counts below 10^7. The shape comes from the state process (four state
registers, R13 R14 R15 R8, zeroed by a fixed init block) and from
elf64_read_fields' tail (three fields, fixed offsets and separators).

`wc -c`, `wc -w`, `wc -lw` and wider counts don't fit without new
flags. The general answer is the formatting API filed as
[[native-proven-formatting-api]]; until then, a tail generic in the number of
fields (a list of (register, separator) pairs) and a state width taken from
the record would cover the `wc` flag combinations.

## Log

- 2026-10-03: Superseded by [[native-wc-as-a-command]]'s design (docs/native-wc-command-design.md §6.2, §11): its row loop prints any subset of columns, and C4 deletes the `Fields` finish. Close this when C4 lands.
