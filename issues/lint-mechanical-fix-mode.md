---
title: Apply the lints that determine their own fix
status: open
labels: [tooling,lint,frontend,ergonomics]
area: language
created: 2026-09-16
updated: 2026-09-16
---

Some lints determine their own fix. When the runner says

```
warning: constructor payload `e` is not used in this arm; write `_` instead
warning: this builds a concrete list with a manual `Cons`/`Nil` spine; write `[…]` instead
warning: consecutive calls to the same function can use one argument list; write `f(a, b)` instead of `f(a)(b)`
```

there is exactly one rewrite that satisfies each, it is local, and it cannot
change elaboration. On 2026-09-16 the `calc_parser.hthr` pass applied eighteen
of the first kind by hand (a Python script with eighteen asserted
substitutions, then a full re-check to confirm nothing moved).
`docs/showcase/calc.hthr` alone still raises about twenty of the other two.

Proposal: mark each lint in the runner as *mechanically fixable* or not, and
give the fixable ones a rewrite to emit. `heather check --fix` applies them;
without the flag nothing changes. A lint that cannot name a unique rewrite —
anything about naming, structure, or a choice between spellings — is simply
not marked, and this feature never sees it.

What has to be true for this to be safe, and is worth stating as acceptance:

- A fix is a **source range and a replacement string**, produced by the lint
  that fired, not reconstructed by the driver from the message.
- Applying all fixes for one file is one pass; overlapping ranges are refused
  rather than resolved by ordering.
- `--fix` re-checks after writing and reports if the file no longer checks,
  which should be impossible and is therefore worth asserting.
- Fixes are not applied to files outside the checked path set (the library's
  own warnings show up when a showcase file is checked — those are not the
  caller's to rewrite).

Note this is not a formatter and must not become one: no reflowing, no
whitespace policy, no touching a line a lint did not fire on. A separate
formatter is in progress and owns all of that.

## What it assumes from elsewhere

- **[[lint-roadmap]]** owns lint profiles and sequencing. Assumed here: only
  that a lint carries enough structure to attach a rewrite to, and that
  "mechanically fixable" is a property of the individual lint rather than of a
  profile.

## Log

- 2026-09-16: Filed after applying eighteen `write \`_\` instead` fixes by hand
  in one file.
