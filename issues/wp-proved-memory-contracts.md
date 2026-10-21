---
title: Proved contracts with a memory footprint
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-wp, hih-pl-source]
created: 2026-10-21
updated: 2026-10-21
---

`Contract` is `pre`/`post` over `Gprs`, and `Contract::Runs` requires
`e.memory = s.memory` (`lib/linux_x86_64_wp.hthr`). Code that spills to its
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
