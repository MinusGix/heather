---
title: Paths as data: steps, their denotation, and an apartness decider
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Package 2 of `docs/language/ownership-design.md` §16: paths as data. The checker (§15.3) decides overlap of two places on their steps and emits a residual where it cannot; level 2's references (§15.5) are a block and steps. Today a path is a pair of functions (`lib/std/machine/path.hthr`), which has no decidable equality, so `PathSame` and "a carrier of paths cannot decide its validity" exist to work around it.

## Scope

- **`Steps`**: a list of steps, each a field, an element at an index, a window, a key, or an enum's variant, over atoms (a literal or a variable), so a place is a root and steps.
- **`denote`**: steps to a `Path`, by `Path::then` over the per-step paths the library has (`Path::elem`, `Path::window`, `Part::path`, `Store::key_path`, `Path::entry`).
- **`Steps::apart`**: a decider on two step lists (the first differing step apart), answering yes, no, or a residual over the atoms where an index is open. Sound against `Apart` by `Apart::under`, `Apart::then_both`, `PathIn::apart_sound`, `keys_apart`; say where it is complete.
- **Customers**: `split_at_mut`, an element held while another is stored, and two fields of one record, each re-derived by evaluating the decider.
- What `PathSame` and `Footprint` become once steps exist (the design review calls `Footprint` redundant beside `Held`); do not delete them here, say what a later round should do.

## Done when

The module and its probes pass the library gate, the decider is proved sound and its completeness stated, and the three customers are theorems by evaluation with a `¬` or a refusal for each overlapping case.

## What it assumes from elsewhere

- **[[ownership-library-join]]** (closed) gives keys as path steps and fields with footprints.
- **[[ownership-checker-call-and-write-view]]** is extending the checker's experiment; this issue does not touch `lib/lang/ownership/`.
