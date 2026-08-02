---
title: How the elaborator knows which meta fn elaborates what
status: open
labels: [metaprogramming,elaboration,design]
created: 2026-08-02
updated: 2026-08-02
---

Filed off the [[in-language-map]] landing (2026-08-02). The evaluation hook is name-keyed: elab_vec_map consults meta_defs for the literal name 'map_code', documented at the dispatch site as 'the name is the contract; there is no attribute system in this round'. Right for one artifact, wrong for five: as [[quotation-stage-artifacts]] adds templates, each needs its own hard-coded consultation point, and nothing stops a user meta fn named map_code with an incompatible shape beyond the loud shape-mismatch error.

The question is the registration seam: does a template declare what it elaborates (an attribute or naming convention the elaborator indexes), or does the elaborator ask the meta layer (a resolver-style query, which is the seam [[lsp-from-the-meta-layer]] and [[generators-in-the-language]]'s later stages both want to plug into)? Constraints worth keeping: the untrusted-generator property (registration affects WHICH functions get the in-language path, never soundness — the kernel gates every emitted term regardless), honest declines (a template that cannot take an instance falls back to Rust; a registered template that evaluates wrong fails loudly), and the Rust schemas staying as oracles.

Not scheduled; wanted when quotation-stage-artifacts reaches its second or third template, or when the fragment transcriber needs a dispatch story of its own.
