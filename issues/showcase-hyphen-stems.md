---
title: Two showcase files cannot be modules at all: a hyphen in the stem
status: closed
labels: [showcase,tooling,docs]
created: 2026-09-19
updated: 2026-09-28
---

Two showcase files have a hyphen in their stem, so `heather check` refuses them
before it reads a line:

```text
error: `docs/showcase/result-parser.hthr` cannot be a module: a module is named
by its file stem, which must be an identifier
```

- `docs/showcase/result-parser.hthr` — the runnable `?`-propagation customer,
  cited as such by `docs/language/result-propagation-design.md` and
  [[result-propagation]].
- `docs/showcase/relational-contexts.hthr` — the executable relational-context
  showcase, cited by `docs/showcase/relational-context-round.md`.
- `docs/showcase/finite-sets-idealized.hthr` has the same stem problem and does
  not check anyway, so it is only affected if it ever becomes checkable.

Nothing noticed because both are reached only through `include_str!` from an
in-process test, where the harness supplies the module name and the file stem
never participates. So a reader told "the runnable customer is
`result-parser.hthr`" cannot run it, and the `-L` incantation in the README
that would work for any other showcase fails here in a way that names no fix.

Found by validating every row of the showcase manifest with a real check
([[showcase-harness]], 2026-09-19), which is what the manifest is for.

**The fix is a rename** (`result_parser.hthr`, `relational_contexts.hthr`) plus
the two `include_str!` paths and the prose references. It is deliberately not
bundled with the harness round: the references include issue **log** entries,
which are historical records that a rename would either falsify or leave stale,
and that wants its own decision about which to do.

## What it assumes from elsewhere

- **[[showcase-harness]]** owns the manifest that found this. Assumed here:
  only that a `test-only` tier exists to mark these files until they are
  renamed.

## Log

- 2026-09-28: LANDED: renamed `result-parser.hthr` to `result_parser.hthr` and `relational-contexts.hthr` to `relational_contexts.hthr`, without changing their contents. Updated both `include_str!` paths, current documentation links and the result-propagation issue body. Historical issue log entries and the original failure descriptions retain the old filenames; this entry records the mapping rather than rewriting history. Both manifest rows now use the CLI tier, with one standalone CLI regression test each alongside the existing in-process tests. The showcase README gives `scripts/showcase check result_parser` and `scripts/showcase check relational_contexts`. Both standalone checks and all eight CLI showcase tests passed. Final plain `scripts/test`: 3,025 passed, 0 failed, 5 ignored.
