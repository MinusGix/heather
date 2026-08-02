---
title: The evaluation hook re-evaluates and re-infers map_code per use site
status: open
labels: [elaboration,performance,metaprogramming]
created: 2026-08-02
updated: 2026-08-02
---

Filed off the in-language-map landing (2026-08-02), per the one-deliberate-round-per-session perf discipline. try_map_code_hook (crates/elab/src/quote.rs) does, at EVERY .map use site with the template registered: one CtxApp + iterated delta-transparent WHNF of the whole meta term, and one kernel infer_term of the evaluated payload to annotate the App spine. Fine at today's scale (the template is ~30 nodes and the suite is unbothered), but it is per-use work whose result is use-independent: the payload has no free locals (its context was the bare g), so the evaluated payload and its inferred type are the SAME for every use site — the CtxApp substitution only rewrites the context inside code types, which the App spine then never consults. Levers, recorded not scheduled: (1) evaluate and infer once per registered template per elaborator, cache (payload, ty); (2) have elab_meta_decl store the payload type derived from the registered statement instead of re-inferring (the CodeTm's ty field under the context substitution); (3) if templates grow letbox chains at registration time, cache post-letbox normal forms. Trigger: a file with many .map sites showing hook time in a frontend benchmark ([[frontend-benchmarks]]), or a second registered template family.
