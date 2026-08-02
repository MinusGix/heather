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

## Log

- 2026-08-02: fold_code port data: the light generalization (try_map_code_hook -> try_vec_code_hook, name + rest-args parameterized) was enough and cheap, but the CALL site did not generalize — elab_vec_fold hard-codes the name, its argument vector in the template's Pi order, and the knowledge that the first two args are Tarski Type<0> codes. That two-code prefix is now baked into the shared hook and is exactly what tabulate_code (one type parameter, Fin-indexed function) and nth_code will break: next port must widen the shared prefix or pass a full argument list. Nothing beyond the loud error stops a user meta fn of incompatible shape, as filed.
