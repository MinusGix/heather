---
title: A build killed at the CPU rail leaves no timings and no certificate
status: closed
labels: [native, tooling, perf]
code: crates/cli/src/native.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

`build-x86` writes `--timings` and the certificate only when the check
returns. A refused certificate is fine (the table is written before the error
is reported), but a build killed by `ulimit -t` leaves nothing, and a
certificate that fails to parse is reported by line and column in a file
that was never written.

Found in the `wc` round (docs/archive/native-wc-design.md §6.1): one declaration
ran for 20+ CPU-minutes, and finding it took a temporary hook that dumped the
certificate (`HEATHER_DEBUG_CERT`) and cut it at a marker
(`HEATHER_DEBUG_CUT`), then bisecting by rebuilds. Both were removed before
committing.

Shape of a fix: write the certificate before checking it (to a sibling path
that is not the published one), and stream timing rows as declarations
finish, or on SIGXCPU, so the last row names the one that was running.
Related: [[closed-length-facts-evaluate-encodings]], what the bisection found.

## Log

- 2026-09-29: Fixed. The certificate is written to `<out>.certificate.unchecked.hthr` before it is checked (replaced on each build, removed once the certificate is published), and its diagnostics — and a build's source modules' — now carry `file:line:col` with the line quoted, so a refusal points into a file that exists. A file `--timings` table is live, for `heather check` too (`stats::live_table`): header at once, one row appended per closed scope, and `<stem>.open.tsv` beside it listing the open scopes, the running declaration last; the end-of-run dump rewrites it with the final rows (docs/instrumentation-design.md §4 says which lines a killed run's table has provisional). No SIGXCPU handler: nothing is buffered, and bash's `ulimit -t` kills with SIGKILL anyway (zsh's with SIGXCPU). Tests: `stats::tests::a_live_table_holds_every_closed_row_and_names_the_open_ones`, `timings.rs::a_killed_run_leaves_its_rows_and_what_was_running` (fails without the live table), and the native tests assert the unchecked copy is left on refusal and gone on publication.
