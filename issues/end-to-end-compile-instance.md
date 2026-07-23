---
title: "Milestone: hand-written Compile instance checked end-to-end"
status: open
labels: [milestone, compiler]
blocked-by: [kernel-v0-scope, ir-simulate-design, compile-typeclass-design]
created: 2026-07-22
updated: 2026-07-22
---

The moment the language's thesis is validated: one small pure function (e.g.
`add`), a hand-written `Compile` instance producing IR for it, and an `equiv`
proof checked by the Rust kernel. No generator required.

After this lands, the certifying generator ([[certifying-generator]]) is
"just" automation of what was done by hand.
