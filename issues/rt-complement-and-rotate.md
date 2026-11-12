---
title: A runtime fn cannot call complement or a rotate: ~e and e.rotr(6) are refused by the generator
status: open
labels: [native,runtime-fn,bitvec,ergonomics]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-12
updated: 2026-11-12
---

A `runtime fn` may call a word operation only if the reflector's table names it (`rt_prim_names`, `lib/native/runtime/rt_reflect.hthr`): `add sub band bor bxor`, the comparisons, the shifts, the extensions and `truncate`. Two the SHA-256 round wants are not there (2026-11-12, after #585 gave them symbols):

```heather
runtime fn ch(e, f, g: u32) → u32 { (e & f) ⊕ (~e & g) }
```

> error: `runtime fn ch`: the generator failed: rt: `complement` is an ordinary fn: mark it `runtime fn`, or the setup has no primitive for it

and `e.rotr(6)` the same way. So `lib/native/crypto/sha256_round.hthr` writes complement as `e ⊕ 0xffffffff` (with a `sha256_ones` lemma and a `j` to get back to the specification's `complement`), and every rotate as a pair of shifts joined by `|`: `(e >> 6 | e << 26) ⊕ (e >> 11 | e << 21) ⊕ (e >> 25 | e << 7)` where the standard reads `ROTR⁶(e) ⊕ ROTR¹¹(e) ⊕ ROTR²⁵(e)`.

Neither can simply be marked `runtime fn`: both are width-generic (`{n: Nat}`), and `complement` is by recursion on the width.

Two routes, not exclusive:

1. **Derived operations, by an equation.** The table gains entries that are not machine primitives but a rewriting into them, each with its theorem: `complement(x) = x.bxor(all_ones)` (`BitVec::bxor_all_ones`, backwards) and `rotr(x, k) = x.shift_right(k).bor(x.shift_left(n - k))` (`refl`, it is the definition; `n - k` evaluates at a literal width and count). The reflector emits the right-hand side and the certificate composes the equation. This is the generator being proved once: no client writes `sha256_ones` again.
2. **Machine primitives**: `not` and `ror`/`rol` in the reflected language, the lowering and the x86 model. Better code (one instruction, not three), a larger change, and a machine-model change is Minus's to merge.

Recommended: 1 first, since it changes no trusted model and the source reads as the standard at once; 2 when an optimiser or a benchmark asks.

A more general form of 1, to weigh: the reflector unfolds any transparent ordinary fn whose body, at the call's closed arguments, is in the fragment (`rotr` is, `complement` is not without its lemma). That would also cover small helpers a client writes, at the cost of the refusal no longer saying which callee was not runtime.

## Done when

`sha256_round.hthr`'s functions are written with `~` and `rotr`, its `sha256_ones` lemma is gone, and `scripts/linked --check` holds (same assembly under route 1).
