---
title: Wire the CLI to check files and print diagnostics
status: closed
labels: [cli,frontend,diagnostics]
created: 2026-07-24
updated: 2026-08-22
---

`crates/cli/src/main.rs` is still `println!("heather: nothing to do yet")`.
Everything needed to make it real now exists: `Elaborator::with_prelude()`
parses, elaborates and kernel-checks a source string, and [[goal-holes]]
added the first rendering — `ElabError::render(&src)` (line:col resolved)
and `Display for ElabError` — including the unsolved-goal listing.

Deliverable: `heather check <file.hthr>` that elaborates the file and prints
diagnostics, exit code 0/1. That is roughly ten lines; the reason to open an
issue rather than just do it is that the *diagnostic* side deserves a small
amount of design once it has a user:

- **Source snippets.** Today a diagnostic is `line:col: message`. A caret
  line under the offending span is the obvious next step and needs the
  source threaded (it already is, in `render`).
- **Error accumulation.** `elab_source` stops at the first bad declaration
  (`for decl in &file.decls { self.elab_decl(decl)?; }`). Per-declaration
  recovery — check the rest, report all — is cheap and is what makes the
  goal listing usable on a file with several open proofs. Note the goal
  listing itself already accumulates *within* a declaration.
- **`ElabError::Kernel` carries no span** (only the declaration name and a
  payload-light `TypeError`). It is the one error a user cannot locate. If
  the CLI makes that painful, the fix belongs in the kernel's error type,
  not in the CLI.

## Why it is worth doing soon

The goal listing is, per [[goal-holes]], "the tooling face of the whole
design" — and it currently has no face: it is only reachable from tests. A
`check` subcommand is also the natural harness for [[stress-proof-suite]]
programs, which otherwise have to be embedded as Rust string constants.

## Log

- 2026-07-27: Promoted to roadmap item 15, ahead of the IR round — see [[frontend-roadmap]] 2026-07-27.
- 2026-07-30: DONE: `heather check <file>...` lands — exit 0/1 (2 for usage/IO/prelude failure), ok-lines on stdout, diagnostics on stderr. All three design items resolved: (1) snippets — `ElabError::render_snippet(src, file)` prints `error:` + `--> file:line:col` + a caret line (char-counted columns, multi-line spans caret their first line); `render` stays the compact harness form. (2) accumulation — `Elaborator::check_source` recovers per declaration; safe because globals/Ψ/ctors are registered only after the kernel gate, so a failed declaration leaves nothing behind (verified: a later use of it is a plain unbound-name error, and a good declaration after a failure still registers). Parse errors stay wholesale — no recovery point in a half-parsed file. (3) `ElabError::Kernel` now carries the declaration's span — the whole-declaration span, since a TypeError speaks about an elaborated term with no source position; anything finer is the kernel-error-type round the issue predicted. Tests: crates/elab/tests/check_diagnostics.rs (9) + crates/cli/tests/check.rs (5, driving the real binary over fixtures). Full suite green, 49 binaries.
- 2026-08-22: The CLI now styles diagnostic structure at the terminal boundary:
  yellow warnings, red errors, cyan locations/gutters, severity-colored carets
  and summaries, and green success markers. Redirected streams, `NO_COLOR`,
  and `TERM=dumb` remain plain; the elaborator renderer is unchanged. Source
  excerpt coloring is intentionally split to
  [[diagnostic-source-syntax-highlighting]].
