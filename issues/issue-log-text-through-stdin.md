---
title: Stop passing issue prose through argv
status: closed
labels: [tooling,tracker,ergonomics]
created: 2026-09-16
updated: 2026-09-17
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
- 2026-09-17: Landed. `log` reads the entry from stdin when no positional text is given, and
  both `log` and `new` take `--body-file <path>` (with `-` for stdin); the inline
  positional and `--body` forms stay for short entries. Three details beyond the
  filing:

  - A multi-line entry is indented two spaces into its list item, fenced blocks
    included, so a heredoc is now the normal way to write one — this entry was
    written that way, and the backticks in it are the test.
  - Refusing is part of the fix: `log` with no text and a tty on stdin exits with
    what to write rather than blocking on a read, and inline-plus-`--body-file`
    is an error rather than a silent precedence rule.
  - `--title` has the same argv exposure and was left alone. Titles are one short
    line and none of the 595 in the tracker carries a code span; if one ever
    needs to, that is the moment to give it the same treatment, not now.

  `issues/README.md` records the convention next to the CLI listing. Closing.
