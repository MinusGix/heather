---
title: Stop passing issue prose through argv
status: open
labels: [tooling,tracker,ergonomics]
created: 2026-09-16
updated: 2026-09-16
---

`scripts/issue log <slug> <text>` takes the entry as a shell argument. Log
entries are prose with code spans, so they contain backticks, and on 2026-09-16
one entry was written as

> The // imports of `docs/showcase/calc_parser.hthr` are the sharp case…

because zsh executed `` `pair` ``, `` `int` `` and `` `omega` `` as commands
inside the double-quoted argument and substituted their (empty) output. The
entry was committed-adjacent before it was noticed, and had to be repaired with
a script.

The fix is to stop passing prose through argv: accept the text on **stdin**
when it is not given positionally (`scripts/issue log <slug> < entry.md`), or a
`--body-file`. `issue new --body` has exactly the same exposure and should get
the same treatment.

Small, and the kind of thing that keeps firing: writing prose with code spans is
the normal case for this tool, not the exotic one.

## Log

- 2026-09-16: Filed after repairing a mangled log entry in
  `issues/lint-unused-imports.md`.
