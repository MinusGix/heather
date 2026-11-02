---
title: The elaborator's Cx copies Vec<String> columns at every clone; make it a persistent binder spine
status: open
labels: [elaboration,performance,representation]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Make the elaborator's local context `Cx` a persistent binder spine with shared names, so that cloning it is O(1) instead of a fresh `String` per binder.

## Problem

`Cx` (`crates/elab/src/context.rs` ~20) keeps its per-binder data in vectors: `names: Vec<String>`, `skels`, `aliases`, `tyvars` (each with a `String` name), `dicts`, `index_ambiguity: Vec<(String, String)>` and `op_locals`. Next to them, `gamma.entries` is already a persistent snoc list. There are 143 `cx.clone()` sites, and each one copies every column, allocating each name again. Local lookup is `cx.names.iter().rposition(|n| n == name)`, a string compare per binder (`lib.rs` ~9914, `application/callable.rs` ~71, `dispatch/member.rs` ~477, `statements.rs` ~460).

The kernel had the same shape and fixed it ([[context-representation-clones]], closed); the elaborator's half never followed.

Measured with the gdb sampler (`docs/data-oriented-survey.md` §2): a `Cx` clone or drop is in 12–14% of cold samples on calc_parser and lib/std/num + tactic, and `String::clone` is in 9–12%. Much of that comes through [[elab-probe-clone-copies-attempt]], but not all of it.

## Proposal

- One persistent spine of binder nodes `{ name: Rc<str>, skel }` that runs parallel to `gamma.entries`. Aliases, type variables and dictionaries become persistent lists of `Rc` entries, so a clone is a few refcount bumps.
- Accessors (`cx.lookup(name)`, `cx.name_at(i)`, `cx.push…`) in place of direct `cx.names` use (192 sites, mostly `push`, `len` and `rposition`).
- Names as `Rc<str>` at least, or as interned symbols if [[resolver-lookup-constant]]'s interner lands, so that `rposition` compares words.
- `Cx::prefix(n)` walks to the n-th node, as `CtxEntries::prefix` does. `Cx::hygienic` rebuilds the spine once, the same cost as today.

There is no kernel change and nothing observable changes. Acceptance: `scripts/perf ab` counters identical, wall time down.

## What it assumes from elsewhere

- **[[elab-field-lifetimes-explicit]]** regroups `Elaborator`, not `Cx`. Its branch removed `Cx::quoted` in favour of the dynamic scope's `quote_depth`. Assumed here: nothing else about `Cx`'s fields.
