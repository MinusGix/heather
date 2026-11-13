---
title: A runtime fn cannot call complement or a rotate: ~e and e.rotr(6) are refused by the generator
status: closed
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

## Log

- 2026-11-12: Built route 1, without composing an equation: each rewriting's right side *converts* to its left at a literal width, so the pin (`f::reflects`, by conversion) holds as it is and nothing in the certificate changed. The table gains `PComplement` and `PRotate(kind)` (`rt_reflect.hthr`), looked up only where they are in scope (`rt_derived_names`: a module without `bitvec_rotate` has no `rotr`).

  - `~x` is reflected as `all_ones ⊕ x`, the literal on the **left**: `Bool::xor` matches on its left operand, so `ofNat(2^w − 1).bxor(x)` computes bit by bit to `complement(x)`'s `!b`, while `x.bxor(ones)` is stuck on the neutral bit (that is why the old proofs needed `bxor_all_ones` and a `j`).
  - `x.rotr(k)` is `x >> k | x << (w − k)` and `x.rotl(k)` its mirror, the definitions (`bitvec_rotate.hthr`), the second count computed by the reflector; the shifts are value-numbered, so `x.rotr(8) ⊕ x.rotl(56)` binds each shift once. A count that is not a literal is refused as a shift's is ("expected a numeral").
  - `sha256_round` and `sha512_round` now read as FIPS 180-4 writes them (`e.rotr(6) ⊕ e.rotr(11) ⊕ e.rotr(25)`, `(e & f) ⊕ (~e & g)`); `sha256_ones`, `sha512_ones` and their `j` steps are gone, and every spec theorem about a word function is `refl`. SHA-512's also moved to `u64` and operators.
  - Probes: `flip`, `flip_low`, `spin`, `spin_low` and the refused `spin_by` in `lib/_tests/native/runtime/runtime_tests.hthr`.

  Assembly (`scripts/linked`): every rotation compiles to the same bytes as the shift pairs did (`sha256_t2`, `sha256_next`, `sha512_t2`, `sha512_next` unchanged). The complement moved one register: with the literal now the XOR's left operand, the emitter writes the result into the literal's register (`xor rdx, rsi` where it was `xor rsi, rdx`), and the AND and XOR after it name the other register. Same instructions, same length; `sha256_t1`, `sha512_t1` and the three programs containing `sha256_t1` (`sha256_compress`, `sha256_update`, `sha256_finish`) were rewritten for that.

  Route 2 (`not`/`ror` in the machine model) is [[x86-narrow-and-rotate-forms]], for when an optimiser or benchmark asks: a rotation is still three instructions.
