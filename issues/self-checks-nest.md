---
title: The kernel's self-checks checked inside themselves
status: closed
labels: [kernel,testing]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

The kernel's slow self-checks (`crates/kernel/src/checks.rs`) each derive
again something the kernel acted on: that a subtree a substitution skipped is
unchanged, that a memo's answer for a shared node is what mapping, judging or
comparing it again gives. Each did so by running the ordinary code for the
node, and the ordinary code checks. So a check ran the checks of everything
under it, each of which ran the checks under it.

With one check in sixteen (the default) the nesting dies out and nobody saw
it. With every check on (`SkipVerification::Full`: the kernel's property
tests, and the whole `scripts/test --long` lane) it costs the *paths* of the
checked term, not its nodes, and costs them on the native stack:

- **A skipped chain is verified once per level, recursively.** `sub_tm`'s
  skip verification called `map_term`, whose child went back through
  `sub_tm_answered`, was skipped, and was verified by `map_term`: one native
  frame set per level, never reaching the spine loop. A closed
  `vec_items_chain` of 100,000 overflowed an 8 MiB stack
  (`crates/kernel/tests/deep_terms.rs`, `a_deep_chain_shifts`). This one
  arrived with the bounds in the node head
  (`issues/free-variable-bounds-in-the-node.md`): until then a node's
  bounds were only consulted at its second query, so the first traversal of
  a fresh term took no skip and had nothing to verify.
- **A shared chain is checked as a tree.** The typing memo re-judged a hit
  with `tm_check_inner`, under which each child was a hit, re-judged in
  turn: `T(k) = 2·T(k-1)`. The forty-link chain of
  `typing_memo_tests::a_shared_chain_is_judged_once_per_link` ran into the
  300 s CPU rail. The substitution memo's hit check and syntax equality's
  pair check had the same shape.
- **The counters read the checks.** Only the typing memo's check ran under
  `stats::unobserved`. A skip's verification walk counted its nodes and its
  memo hits as the run's, so a debug build's substitution counters depended
  on the level: `let_and_blocks::a_shared_let_chain_stays_shared_under_binders`
  saw "elaboration's shifts grew 2084 → 524356 for k = 8 → 16" with every
  check on, and `subst::tests::a_shared_chain_stays_shared_through_shift_and_substitution`
  failed the same way.

## What was done (2026-11-10)

One helper, `checks::rederive(claim, f)`, runs every check. Inside it no
check is taken (`verify_this_skip` answers no, and does not move the sampling
stride), no counter moves (`stats::unobserved`), and for `Claim::Skip` no
skip is taken either (`checks::unskipped`), so the walk that verifies a
skipped node verifies everything in it, once, by the traversal's own memo and
its own spine loop. All twelve sites go through it: the two skips and two
memo hits of `subst.rs`, the five of `typing.rs` (the typing memo's and the
closed-conversion memo's), the closed-pair table of `conv.rs`, syntax
equality's pair memo, and the constant check of `GlobalCtx::commit`.

`deep_terms::verifying_every_skip_is_flat_shared_and_uncounted` holds the
three properties: a 100,000-deep closed chain, a closed and an open tower of
64 shared pairs (`2^64` paths), shifted with checks off and with every check
on, and the two counter rows equal. It overflows the stack without the fix.

## How it was found

The `--long` lane had not run on master since the kernel library became a
package of its own: `scripts/test --long` asked for the feature
`heather-kernel/long-checks`, which no longer exists, and stopped at Cargo's
error. Fixed in the same change (`heather-kernel-lib/long-checks`). What the
lane says about master once it runs is [[long-lane-state-2026-11]].
