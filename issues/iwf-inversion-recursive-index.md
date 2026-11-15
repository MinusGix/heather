---
title: "IWf match inversion at a recursive declared index type"
status: open
labels: [elaborator,indexed-families]
area: language
created: 2026-10-22
updated: 2026-10-22
---

`docs/kernel/iwf-former-design.md` §8.3's tier 1 (a `match` at a
constructor-headed index inverts the motive by the index type's own
eliminator, so impossible arms are `tt`) is implemented for `Nat` and for a
flat declared index type (`Elaborator::iwf_match_motive`,
`crates/elab/tests/iwf_match_tiers.rs`). At a **recursive** declared index
type (a `Wf`-lowered one, such as a user-declared list or tree used as an
index) the scrutinee index's head is not read: `Elaborator::index_head`
reads it with `read_ctor` against a `Sum` spine, which a `Wf` lowering does
not have. Such a `match` falls to tier 2 (abstraction) or the constant
motive, so an impossible arm must be written and the arms are not refined
by the constructor.

What it needs: read a `Wf` constructor value's head and arguments (its
`sup_f` label through the shape's spine, the children through `nth`), as
`read_ctor` already does for tier 1 values, and check that `index_case`'s
`elim_Wf` branch (`wf_branch_env`) hands the inversion the same argument
terms. heather-coq's `probes/IwfLowering2.v` checked this case (`allTail`
at `List a`) in the formalization's rules, so no kernel change is expected.

## Log

- 2026-11-05: gardener: cites a file it shares with [[indexed-families]] (`docs/kernel/iwf-former-design.md`).
