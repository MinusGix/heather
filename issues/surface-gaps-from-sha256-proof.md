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

## Status (2026-11-14, thread "Fix typing gaps from the SHA-256 proof")

Probes: `lib/_tests/lang/expected_type_tests.hthr` (items 1 to 4, each with
a neutral or open variant and a refusal), and `abd_claimed` in
`lib/_tests/native/crypto/sha256_stream_agreement_tests.hthr` (item 7).

1. **Fixed.** `(e: T)` is an expression (`ExprKind::Ascribe`): `e` checked at
   `T`, the whole of type `T`, no term of its own. Only inside parentheses;
   `(x: A)` followed by an arrow is still a binder group
   (`Parser::group_then_arrow`). The tree-sitter grammar has
   `ascription_expression`.
2. **Fixed for a checked call.** An argument that would be inferred at a
   domain still waiting on the call's slots is now checked when reading the
   call's expected type first settles that domain
   (`application::propagate_expected`): `trans(h, cong_fn(λ t =>
   Mutated(t, 48), p))`. Not for a bare name, whose type is its own (and
   whose mismatch is better reported against the implicit it disagreed
   with), nor in a call holding a section's `·`. The read is kept only when every slot the result
   waits on stands bare in it (an equation's endpoint or type, or a type),
   since a learn-only unification of `BitVec(?m + ?n)` against
   `BitVec(63 + 1)` concludes `?n := 1`, and only when the solved result
   converts to the expected type. Still open: a call that is itself
   inferred, `trans(cong_fn(λ t => Mutated(t, 48), p), q)`, whose first
   argument has no expected type until `q` is elaborated; that needs
   checking against a domain with metas, which this elaborator's per-call
   scratch world does not do.
3. **Fixed.** A spilled argument (past the declaration's parameters) whose
   domain is already known is checked there and the spill continues, so a
   later one teaches the implicit: `pieces_add(4, 16, 16 * k, xs)`.
4. **Fixed where something must name the container.** A collection literal
   stays checking-only (a container is ambiguous,
   `crates/elab/tests/list_literals.rs`), but as a method call's receiver,
   where a type is needed to find the method at all, a non-empty literal is
   a `List` of its first item's type (`Inference::list_receiver`), so
   `[b].len()` resolves; and a literal on the left of an operator takes the
   carrier from the expected type or the other operand, as a numeral does:
   `[BitVec::zero()] ++ xs`.
7. **Located, not decided.** The false claim `digest_spec` at "abc" for
   "abd" spends the gate's whole step budget (about a million steps, under
   half a second): the two sides are calls of `digest` on lists that differ
   in one byte, so conversion evaluates both, and no cheap check can say
   two calls of one function disagree (they might collide). The verdict
   stays `OutOfFuel`, but the refusal now moves to the first checking site
   whose two types spell differently and names the part that differs
   (`MismatchNotes::fuel_note`: "which differs at `99` against `100`").

## Done when

Each is fixed or has an issue of its own, and the workarounds named above
are removed from the two modules.
