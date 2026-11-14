---
title: Small surface and inference gaps the SHA-256 proof met, each many times
status: open
labels: [elaborator,surface,proofs]
area: language
created: 2026-11-14
updated: 2026-11-14
---

Met while proving the linked SHA-256 ([[sha256-linked-into-cache]],
`lib/native/crypto/sha256_stream_agreement.hthr`, `lib/std/crypto/sha2_stream.hthr`).
None is deep; each cost a workaround at many sites, and the workarounds
are in the library as written.

1. **No type ascription on an expression.** `(130: u64)` does not parse, so
   a literal that must be a word is bound by a typed `let` first, or taken
   as a parameter with an equation (`fill_of_130` in
   `lib/_tests/std/crypto/sha2_stream_tests.hthr`).
2. **A literal inside a lambda defaults to `Nat`.** In
   `cong_fn(λ (k: Nat) => BitVec::ofNat(k), …)` the width is not found from
   the equation the `cong_fn` is checked against, and `Mutated(t, 48)` in a
   lambda takes 48 as a `Nat`. Written `BitVec::ofNat(k, n := 64)` and
   `let at: u64 = 48` throughout.
3. **A type argument that occurs only under the result's binders is not
   inferred.** `Sha2::pieces_add<A>(size, a): (b: Nat) → (xs: List<A>) → …`
   needs `<u8>` at each call although the arguments applied next fix it.
4. **`++` and `.len()` on a list literal with no element type.** `[b].len()`
   and `xs ++ [BitVec::zero()]` fail where the other operand, or the goal,
   says what the elements are. Worked round with `let single: List<u8> = [b]`
   and helper functions (`Sha2::zero_bytes`, `Sha2::ending`).
5. **A record is not its fields rebuilt, without a lemma.** `Sha2Feed::eta`
   is a `match` proving `Sha2Feed(f.full, f.tail, f.room) = f`. Vectors
   have this by conversion; records could.
6. **`xs.take(0)` and `xs.drop(0)` do not reduce at a neutral list**, since
   both recurse on the list first. `take_zero` and `drop_zero` are cited
   wherever a count computes to zero. Recursing on the count first would
   make them conversions, at the cost of the other stuck case; a `simp`
   default covers it either way.
7. **A false claim proved by a true theorem can run out of fuel** where a
   mismatch is the honest answer, when the two sides differ only deep
   inside a computation. The refusal probes were chosen to differ at a
   constructor for this reason.

## Done when

Each is fixed or has an issue of its own, and the workarounds named above
are removed from the two modules.
