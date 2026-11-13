---
title: A tactic under `if h: c { … }` does not see the test unless the branch writes `h`
status: open
labels: [elaboration,tactics,ergonomics]
area: language
created: 2026-11-13
updated: 2026-11-13
---

```heather
fn a2(j: u64) → Nat { if h: j < 48 { let p: (j + 16).toNat() < 64 = bv_omega; 1 } else { 0 } }
// `bv_omega`: `j + 16` may overflow 64 bits; … locals [j: u64, …]
fn a3(j: u64) → Nat { if h: j < 48 { let q: j < 48 = h; let p: (j + 16).toNat() < 64 = bv_omega; 1 } else { 0 } }
// ok
```

The parser lowers `if h: c` to a `match` on `decide_bit<c>()` with a hygienic equation binder (`#if_bitN`), and binds `h` (`let h = decide_true<c>(e)`) only in a branch whose tokens name `h` (`crates/syntax/src/parser.rs`, `names_from`). A tactic's reading of the context (`omega_cert::local_fact_entries`) passes over `#` names. So where the branch does not write `h`, nothing in scope states the test: `omega`, `bv_omega` and a parameter's default (`inside: i.toNat() < n := bv_omega`) find no bound. A `match h: a.unsigned_lt_bit(b)` does not have the gap, since its equation has the user's name.

**A fix that was tried (not merged):** name the equation `__if_bitN` where some branch does not bind `h`. `bv_omega` then reads it as it reads a `match h:`'s (`a.unsigned_lt_bit(b) = True`), and the term is unchanged. It changes what every tactic under such an `if` sees, so it needs the whole library elaborated again before it merges (CLAUDE.md). It is in `/mnt/project-files/wip/proof-carrying-index.patch`.

## Done when

`a2` above checks, and the whole library elaborates with the change.

## Log

- 2026-11-13: Filed from PR #551's thread (indexing with an implicit proof). Related: [[found-proof-differs-across-recursion-companions]].
