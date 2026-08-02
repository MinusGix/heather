---
title: Amortize the quotation slice: tabulate, fold, nth written in the language
status: open
labels: [metaprogramming,frontend,elaboration,stdlib]
created: 2026-08-02
updated: 2026-08-02
---

Filed off the [[in-language-map]] landing (2026-08-02). The slice's machinery (meta fn, quotes, the evaluation hook) now exists and map_code is its only client; the rest of the vec.rs schema family is expressible in exactly the same closed-generic-template shape, and each port retires hand-shifted Rust — tabulate's d+1 codomain subtlety, the one that needed its own open-element regression test, cannot occur in a quote at all. The thesis demonstrated by deletion.

Candidates, easiest first: fold_code (same elim skeleton as map, extra init argument), tabulate_code (the Fin-index helper is where the Rust hand-shifts concentrate), nth_code (already has a kernel-side spelling to mirror, term.rs). Each wants: the template in lib/vec_code.hthr, hook routing in its elab_vec_* dispatch, and the cross-check-by-conversion fixture pattern from crates/elab/tests/in_language_map.rs (literal + neutral + open-element + routing control).

Two gates before this grows past a couple of templates: (1) [[meta-def-registration]] — the name-keyed hook contract stops scaling; (2) note the per-use evaluation cost accumulates per family ([[meta-hook-evaluation-cost]]'s cache lever likely triggers here). The parametric-rigidity note (in-language-map design doc section 7) is the design heuristic: push each artifact to its most generic type first, because genericity is free adequacy.
