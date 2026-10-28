---
title: Proved contracts with a memory footprint
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp, hih-pl-source]
created: 2026-10-21
updated: 2026-10-28
---

`Contract` is `pre`/`post` over `Gprs`, and `Contract::Runs` requires
`e.memory = s.memory` (`lib/std/os/linux/linux_x86_64_wp.hthr`). Code that spills to its
frame, calls a function whose frame is below it (S4 round 3), or stores into
a buffer (`docs/native-effect-source-design.md` §6) changes memory, so it
cannot enter `Wp` as a `Proved` item. The effectful source compiles every
pure leaf to a `Proved` item, so this is on S3's path. Found while writing
that design (§2.4).

## Scope

- A contract names a footprint (a range, or a view-relative place such as
  the frame below RSP or a buffer's range): memory outside it is unchanged,
  and `post` relates the memory inside it before and after.
- `wp_item`'s `Proved` arm hands the view the footprint's change (the view's
  `Stores`-like arm), and `wp_item_goes` is reproved.
- S4's region and function theorems restated as such a contract, so a
  lowered region with spills or calls is a `Proved` item.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns `Wp`, `Contract` and the view interface.
- **[[wp-stack-items]]** owns `CallTo`/`Spill` as `Wp` items; the two
  should share the footprint notion.
- **[[byte-memory-access-model]]** owns the memory a footprint is over.

## Log

- 2026-10-24: 2026-10-24: [[wp-stack-items]] landed calls as a second table, `Callee`: pre/post over the view and the state (given the return address), honesty in continuation form so a body is proved by `Wp` (`Callee::returns_by`). Its footprint is whatever the view says after the call, not a range. A `Proved` contract with memory could take the same shape (view-relative, the view after as an output), and the two tables may then be one.
- 2026-10-25: S3.2 landed without this ([[native-effect-source-compiler]], closed): its leaves are register-only dataflow regions entering by S4's `Region::lower_correct`, and its proofs run over the code's `Goes` claim rather than `Wp`, with memory handled by the region invariant `Target::Placed`. A leaf that spills or calls needs a footprint contract, now on [[native-compile-wider-leaves]]'s path.
- 2026-10-28: Abate et al.'s WP-preservation paper (docs/wp-preserving-compilation-survey.md §4) states compiled functions' target contracts as the correspondence plus pre, with a per-cell footprint and nothing over the whole memory. That supports the view-relative footprint proposed on 2026-10-24. [[native-procedure-contracts]] is the effectful-procedure customer.
