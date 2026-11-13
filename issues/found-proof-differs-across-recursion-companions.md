---
title: A proof a tactic finds inside a `decreases` body is found again for each companion, as a different term, and the kernel runs out comparing them
status: open
labels: [elaboration,termination,tactics,conversion]
area: language
created: 2026-11-13
updated: 2026-11-13
---

A `decreases` function whose body holds a proof that a tactic found (an argument left to its default `:= bv_omega`, or `inside := p` at a `let p: … = bv_omega`) can lose its unfolding companions, `f#ext` among them, to "the kernel rejected `f#ext`: OutOfFuel". A `runtime fn` loop is built from `f::ext`, so the loop is then refused ("it has no `ext` companion").

Found 2026-11-13 (PR #551's thread) while making an array element at a word index carry its bound (Minus: indexing requires a proof, found implicitly):

```heather
fn vector_at({w, n: Nat}, v: [BitVec(w); n], i: u64, inside: i.toNat() < n := bv_omega) → BitVec(w) { vector_get(v, i.toNat(), BitVec::ofNat(0)) }
fn vector_put<A>({n: Nat}, v: [A; n], i: u64, a: A, inside: i.toNat() < n := bv_omega) → [A; n] { vector_update(v, i.toNat(), a) }

fn c1(v: [u32; 64], j: u64) → [u32; 64]
    decreases (48 - j).toNat() {
    if h: j < 48 { c1(vector_put(v, j, vector_at(v, j)), j + 1) } else { v }
}
// c1_unfold: no unfolding equation for `c1`: the generated `c1#ext` was refused (the kernel rejected `c1#ext`: OutOfFuel)
```

**What decides it.** The same function passes at `[u32; 48]`, passes with one of the two calls spelled without its proof (`vector_update(v, j.toNat(), vector_at(v, j))`), and passes at 64 with both proofs given as an application of a stated lemma (`inside := lem(j, h)` at `theorem lem(j: u64, h: j < 48): j.toNat() < 64 { bv_omega }`). It fails with one `let p = bv_omega` passed to both calls.

**Cause, as far as it was read.** The companions are built by a walk of the body's syntax (`crates/elab/src/measure.rs`), so the body is elaborated again for each, and a tactic runs again in a context that differs (the recursion's hypothesis, the bound). `omega` reconstructs its certificate against the local context, so the proof comes out a different term. `f#ext` then compares `vector_put(v, j, a, p1)` with `vector_put(v, j, a, p2)`: the kernel compares the arguments of the same head first, and normalising two certificates against each other spends the budget before it would unfold `vector_put` and drop the proof. `measure.rs`'s module doc says exactly this of a decrease's own obligation, and lifts it into `f#obl_N` for the reason.

**Directions.**

1. Lift every proof a tactic finds in a `decreases` body into a declaration of its own, as `f#obl_N` is, so the body and its companions name one term. The statement is not syntactic as a decrease's is (it is a callee's parameter type at the call's arguments), so the lift needs the elaborated site.
2. Make a tactic's proof the same term wherever it is found: prove the statement closed over its atoms and the facts it cites, in an empty context, and apply it. Then nothing about the context reaches the term.
3. An index form that checks its bound and keeps no proof in the term (`v[i]` at a word). Cheap, and the term is what it is today, but the proof is then not there for a compiler that would drop the code's test with it.
4. The kernel's order at a same head (`issues/runtime-link-compares-functions.md`, Minus's).

## Done when

A loop over `[u32; 64]` whose body reads and stores at indices with found proofs has its companions, and `Sha256::expand` written with them compiles.

## Log

- 2026-11-13: Filed with the reproduction above. The scratch probes are `/mnt/project-files/wip/ix2-ext-probe.hthr`; the library and reflector side of the proof-carrying index is `/mnt/project-files/wip/proof-carrying-index.patch`, not applied.
