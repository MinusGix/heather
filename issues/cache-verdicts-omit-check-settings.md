---
title: "Cache verdicts don't record the fuel/univs they were earned under"
status: open
labels: [tooling, cli, robustness]
created: 2026-08-06
updated: 2026-08-13
code: crates/cache/src/store.rs @ 33c65ef
---

A rung-1 cache entry says "the kernel accepted this check key" but not
under which settings: the fuel budget and the `univs` bound are passed to
`typing::check_*` by the caller and appear nowhere in the check key, the
entry, or the kernel fingerprint (verified 2026-08-06 — `grep fuel` over
`crates/cache/` and `gate.rs` is empty).

Not a soundness gap: fuel exhaustion is a completeness limit, so a verdict
earned at high fuel never vouches for an ill-typed term. The failure mode
is **reproducibility**: if the default fuel ever changes (or becomes a
flag), a declaration can be accepted warm that a cold run would reject
with fuel exhaustion — "the cache changes the answer", which for a build
gate is its own bug class, and exactly the divergence the planned
fresh-vs-replay oracle ([[parallel-checking-and-caching]] rung 2) exists
to catch. Today both are compiled-in constants, so the gap is latent; the
cheap moment to close it is before any of them is configurable.

Fix shape (pick at implementation time): fold the check-relevant settings
into the entry as columns checked on read (a mismatch is a miss, loudly
counted), or into the kernel-semantics fingerprint if "settings" are
considered part of the semantics. Columns are gentler: a fuel *increase*
could then still choose to honor old entries (a verdict at lower fuel
holds at higher), which a fingerprint bump cannot express.

## When

Triggered: the moment fuel or univs becomes configurable from the CLI, or
rung 2 lands — whichever is first.

## Log

- 2026-08-13: A second consumer of the store, and a narrowing verified while wiring it. The certgen test binaries now replay verdicts through the same store code (target/decl-cache, [[elaborator-snapshot-across-test-binaries]]'s round — which also extended the gate seam to quote.rs's Layer::Meta site, with the layer folded into the item's identity via the hashed binding). Checked 2026-08-13: DEFAULT_FUEL is a crates/kernel/src/typing.rs constant, so the kernel-semantics fingerprint already invalidates every entry on a fuel change — the gap this issue records opens only if fuel moves out of kernel source or becomes a flag. The univs bound is a hardcoded 0 at the three elab gate call sites (crates/elab/src/lib.rs, gendefs.rs, quote.rs), same compiled-in latency. Trigger unchanged; when it fires, the fix lands in the entry columns and covers the CLI store and the test store alike, since they are one code path.
