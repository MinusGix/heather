---
title: Retire the braced record literal now that a named call says the same thing
status: open
labels: [frontend,syntax,cleanup]
created: 2026-08-18
updated: 2026-08-18
---

The braced literal `Monoid { unit: 0, op: f }` was marked **provisional** the
day it landed (`docs/surface-records.md` §6, 2026-07-27), on the explicit
condition that [[named-arguments]] would make it redundant. That has now
happened: `Monoid(unit := 0, op := f)` is an ordinary constructor call, permuted
by the same function, and `crates/elab/tests/named_arguments.rs` proves the two
spellings equal by `refl`.

## What retiring it buys

Not one form fewer — a whole **ambiguity class**. A braced literal is the only
reason `{` can follow an expression, which collides with the three positions
where a *block* already does (`match m { … }`, `match m as x -> M { … }`,
`theorem t(): a = b { … }`). The fix is Rust's: a parser flag,
`Parser::no_record_lit`, set in those three positions and lifted inside every
bracket. `docs/surface-records.md` §6 calls that flag "a standing hazard rather
than a one-time cost — every future block-preceding construct has to remember
it, and [[effects-direction]] will bring more of them."

Retiring the literal deletes the flag, its ten set-sites, its lifting sites,
§6.1's parenthesis rule, and the tests written against that rule.

## Why it was not done in the named-arguments round

Because it is a **migration**, not a feature, and bundling a sweep into the
round that introduces the successor makes a bisect over either of them useless
(docs/named-arguments-design.md §10.2). The work is: rewrite every braced
literal in `lib/`, the fixtures and the tests; remove the flag and its sites;
delete §6.1 and re-baseline its tests.

## The criterion this round should meet first

Stated in §10.2 and repeated here because this issue owns it: the braced form
goes when the named-call spelling has **shipped and been used in `lib/`**, and
when the `⟨…⟩` anonymous literal question (also deferred in §6) has an answer —
because if `⟨…⟩` lands, `{ … }` loses its second customer too and the two
retirements are one edit rather than two.

As of filing, the first half is met (shipped; `lib/std` uses named calls at
`Iff`/`And`) and the second is not.

## What it assumes from elsewhere

- **[[surface-records]]** owns the literal and its §6.1 flag. Assumed here:
  only that §6 marked the form provisional on this exact condition.
- **[[named-arguments]]** owns the successor spelling. Assumed here: only that
  a record constructor is nameable by field, which it is.
