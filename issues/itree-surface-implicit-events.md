---
title: ITree operations take their events implicitly, and a claim moves along ≈ by rewriting
status: open
thread: Make compiler correctness proofs elegant
labels: [itree,surface,proofs]
area: interaction-trees
created: 2026-11-16
updated: 2026-11-16
---

`ITree`'s operations take the event signature as their first explicit argument and are written as qualified calls, and its equivalence has no symbol:

```
t.at_similar(prog_len(p), first.live_in(t.homes, rest.live_in(t.homes, out)),
    ITree::bind(Events::linux(), ITree::bind(Events::linux(), first.denote(call, perform, n, env), h), k),
    ITree::bind(Events::linux(), first.denote(call, perform, n, env), k2), env,
    ITree::bind_assoc(Events::linux(), first.denote(call, perform, n, env), h, k),
    run_first(…))
```

`Events::linux()` is written 192 times in `native_compile*.hthr` (88 in `native_compile_correct.hthr`), and every use of `bind_assoc` names both trees in full to move one claim across it.

## Wanted

1. **The signature is implicit.** `fn ITree::bind<A, B>({E: Events}, self t: ITree<A>(E), h: A → ITree<B>(E))`, so the tree above is `first.denote(call, perform, n, env).bind(h).bind(k)`; the same for `map`, `iter`, `Same` and the laws. Check what stops this today (a `self` after an implicit, `E` appearing only in types).
2. **`designation ≈ at ITree<R>(E) := ITree::Same`** with its `Equivalence` instance, so a chain is a `calc` and `bind_assoc` is a `simp_only` law.
3. **A claim moves along `≈` by evidence.** `Target::at_similar` and `Site::goes_same` say `t.At(…, tree, …)` respects `ITree::Same`; registered as an `evidence theorem`, `rewrite(ITree::bind_assoc(…), run)` or `simp_only(ITree::bind_assoc, then := run)` at a goal `t.At(at, live, d.bind(h).bind(k), env)` replaces the five-argument call. [[carrier-respects-as-rewrite-evidence]] and [[rewrite-setoid-sequenced-arguments]] are the open pieces of rewriting along a relation; say here which of them this needs.
4. A statement's continuation type `Flow → ITree<BitVec(64)>(Events::linux())` is written 30 times: a named type (`Target::Rest`) is a library edit, listed in [[native-compile-correct-proof-forms]].

The coinductive trees (`CoTree`, `Eutt`) have the same surface question; [[eutt-tactics]] and [[eutt-setoid-rewrite]] cover their rewriting.

## Done when

`Target::then_nil`'s last step is `rewrite`/`simp_only` with `ITree::bind_assoc` and no tree written out, and `Events::linux()` appears in `native_compile_correct.hthr` only in type signatures (or behind a named type).
