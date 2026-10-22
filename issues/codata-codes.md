---
title: Codes for M so codata can be quoted
status: open
labels: [codata,coinduction,kernel,codes]
area: kernel
created: 2026-10-22
updated: 2026-10-22
---

`M`, `corec` and `out` have no codes, so they exist at layers p and m only.
Declarations over codata are bound at p since round 1
(`docs/codata-elaborator-design.md` §6), which means they cannot be quoted:
no `code { … }` mentions codata, and the code recursor never sees it.

When a metaprogram needs codata (a tactic over codata goals, certgen of a
stream processor), give `M` codes as `IWf` got them: a `TmM` code former,
`El` decoding, and four code-recursor branches (`ty_m`, `tm_m`, `tm_corec`,
`tm_out`; `docs/kernel-coinduction-design.md` §5), with the step telescope
of `tm_corec` the widest so far. Comparison of boxed code stays syntactic,
so bisimilar code stays distinguishable as code.

Once that lands, the p-layer choice in `Elaborator::decl_layer` can retire
for codata (bind at c again), and `needs_computing_layer` shrinks to
whatever is still code-less.
