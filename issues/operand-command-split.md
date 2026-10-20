---
title: Split the operand loop from what wc prints, with cat as a second client
status: open
labels: [native,x86,design]
area: heather-in-heather
created: 2026-10-07
updated: 2026-10-07
---

The command library is named for commands in general but encodes `wc`'s
control flow: `command_events` always makes the stat pass when GNU would,
computes GNU's width (`elf64_command_events.hthr:84-88`), prints a row of
padded counts and the name per operand, and a `total` row after two operands
(`:137`). `elf64_command` hard-codes the same phases. A `cat FILE...` could
reuse the operand cursor, the open/read/close events, the read head and the
write loop, but nothing above them. `head -n 5` fails earlier, at the
argument scan, which knows only flag letters that select columns
(`command_program.hthr:73`).

Wanted: split the operand loop from what it prints.

- A generic operand command: an option spec (flags now, option arguments
  later), an optional stat pass, then per operand open, the filter's reads
  and close, with a per-operand hook and a final hook, and a status function.
- `wc`'s rows, width rule and total as one instance of the hooks.
- `cat FILE...` as the second client, with the empty stat pass and an
  emitting step, to show the split is real.

Limits worth lifting on the way, each fixed in today's code: at most four
counts in registers (`elf64_command.hthr:55`), at most eight columns
(`command_program.hthr:19`), and one status bit.

## What it assumes from elsewhere

- **[[native-wc-as-a-command]]** owns `wc` as built. Assumed here: only that
  `wc`'s claim may be restated over the generic command as long as it says
  the same thing.
- **[[native-label-assembler]]** and [[command-trace-by-append]] make this
  much cheaper; neither is required first.
