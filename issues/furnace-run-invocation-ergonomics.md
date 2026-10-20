---
title: furnace run: take a shell command, and own the log
status: open
labels: [tooling,infrastructure,ergonomics]
area: infrastructure
created: 2026-09-16
updated: 2026-09-16
---

Two small things about invoking `furnace run`, both of which cost a round trip
on 2026-09-16.

**1. The command is not a shell command.** `furnace run -- 'cmd1; cmd2'` fails
with

```
bash: line 1: /work/<checkout>/cmd1; cmd2: No such file or directory
```

— the whole string is taken as a program path. It needs
`furnace run -- bash -c '…'`, which is easy once known and invisible before.
Either accept a compound string directly, or add `furnace run-bash` (or
`--shell`) that wraps it, or fail with a message that says what to write.

**2. Output handling is the caller's problem.** Every invocation here is
`furnace run -- bash -c '…' > scratch.log 2>&1` launched in the background,
then polled for a marker string echoed at the end of the remote command,
because output arrives in coarse chunks and there is no other completion
signal. A `--log <path>` that writes the remote job's output to a file, plus an
exit-status line the caller can wait on, would replace the marker-echo
convention that every caller currently reinvents.

Both are ergonomics rather than capability, which is why they are one issue.
The capability problems are [[furnace-concurrent-jobs]] and
[[furnace-run-round-trip-latency]].

## Log

- 2026-09-16: Filed after losing one round trip to (1) and using the
  marker-echo workaround eight times for (2).
