---
title: scripts/perf ab compares two binaries, so it cannot A/B a library or showcase source change
status: closed
labels: [tooling,performance]
created: 2026-09-19
updated: 2026-09-19
---

`scripts/perf ab` (2026-09-19, `perf/README.md`) builds two compiler binaries and
interleaves cold checks of a fixed corpus. That is the right shape for a kernel or
elaborator round and the wrong one for a *source* round: a change to `lib/` or to
a showcase is the same binary over two source trees, and `ab` would build one
binary twice, find the hashes equal, and refuse the run — correctly, by its own
rules.

The gap has a consumer already: [[showcases-predate-their-ergonomics]] and
[[record-type-partial-application]]'s showcase half both change `.hthr` text in a
file whose cold check is the thing at risk (it needs more than 8 GiB and cannot be
cached), so both want exactly this measurement and neither can have it.

Wanted: a `--source-patch FILE` mode that holds the binary fixed and reverses the
diff over the *sources* between samples, keeping everything the binary mode
already gets right — interleaving, the per-sample spread and the `separate` /
`SPREAD EXCEEDS THE DELTA` verdict, counters reported apart from seconds, the
load warning. Two things change: the provenance check becomes "the two source
trees differ and the binary is the same", the mirror image of today's assertion;
and the counters are no longer expected to be identical — for a source change they
are the *result*, since term growth is what the round is about, so the report
should stop calling a moved counter a behaviour change and instead rank the
columns that moved.

`ReversePatch` in `scripts/perf` already does the risky half (apply, restore,
re-hash every file the patch touched and refuse a half-applied restore), so this
is mostly wiring plus the inverted assertion. `scripts/perf ab-selftest` is where
the verdict logic is pinned.

## Log

- 2026-09-19: Landed as `scripts/perf ab --source-patch FILE` (perf/README.md, "A source
  change"). The wiring was the small half, as this issue guessed; the content is
  the four things that had to be inverted rather than shared:

  - **Provenance.** `source_patch_setup` asserts the mirror of the binary mode's
    hash check — the two *source* trees must differ and the binary must not. Three
    refusals: a patch naming no files, a patch whose reversal leaves every named
    file byte-identical, and a patch touching `crates/` or `Cargo.*`, which breaks
    the premise that the binary is fixed (that case is plain `--patch`, which
    rebuilds). `ReversePatch.reverted_hashes` exists only to make the second one
    checkable: there is no hash of the reverted tree until the tree has been
    reverted once.
  - **Interleaving.** The `before` side is measured inside the `ReversePatch`
    context, re-entered per sample, so the two sides stay interleaved rather than
    measured in two blocks. That is `2 × samples` patch/restore pairs, each with
    the existing hash verification, and the end-to-end run below shows the tree
    restored and verified after every one.
  - **What a moved counter means.** Inverted in `report_ab` behind
    `args.source_mode`: in binary mode a move is a behaviour change, here it *is*
    the result, so the moved columns are ranked by relative move instead of listed
    alphabetically. `ab-selftest` now pins both readings and the ranking.
  - **The corpus.** Defaults to the corpus entries the patch touched, because the
    old default (the showcase alone) would measure a file the change may not
    reach. Where no patched file is in the corpus the report says so, so that "no
    change" is not read as a finding. Noted in the help and the README:
    `docs/showcase/calc_text.hthr` is not in the corpus, so it needs `--file`.

  Verified end to end, not just by selftest: a probe declaration appended to
  `lib/std/num/nat.hthr`, `--heather target/release/heather`, two interleaved samples.
  One binary hash on both sides, the corpus auto-picked `lib/std/num/nat.hthr`, and
  the counters moved by exactly what one declaration costs (`decls_gated`
  512 → 514, `check_terms` +1, `cache_hashes` +1, 21 columns identical) while every
  seconds row correctly returned `SPREAD EXCEEDS THE DELTA — not a result` at that
  scale. The five refusal paths were each exercised and none of them touched the
  working tree. `ab-selftest`: 15 assertions, all ok.

  One thing the mode deliberately does **not** do, per the user's verdict of
  2026-09-19 recorded in [[showcase-spec-relations-as-records]]: it measures, it
  does not gate. A readability round is not a perf round — if the nicer spelling
  costs, the finding is a language or kernel issue to file, not a veto on the
  edit. The README says so where someone reaching for this tool will read it.
