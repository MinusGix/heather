---
title: A kernel NotConvertible inside a term no checking site recorded stays unlocated
status: open
labels: [kernel,diagnostics]
area: kernel
created: 2026-09-24
updated: 2026-09-24
---

Residue of [[elab-accepts-projection-through-opaque-theorem]] (2026-09-24).
Every elaborator checking arm now records its inferred/expected pair, and a
decided mismatch is reported at its site even when the types do not spell.
What is still unlocated is a refusal inside a term the elaborator *built*
rather than checked: a lowering, a synthesized motive, a certificate term
assembled in Rust. There the gate's `NotConvertible` still lands on the
declaration.

The issue's second question stands for that case: could the kernel's
conversion report the first mismatching pair of sub-terms (a path, under the
budget-bounded `Debug` of `crates/kernel/src/fmt.rs`)? It is a kernel change,
so weigh it against keeping the kernel un-fancy until it is verified. A
report-only path that
re-runs conversion after a refusal would keep the checking path untouched.
Not urgent: no instance is known today that the site notes miss.

## Log

- 2026-11-05: gardener: cites a file it shares with [[kernel-coinductive-types]] (`crates/kernel/src/fmt.rs`).
