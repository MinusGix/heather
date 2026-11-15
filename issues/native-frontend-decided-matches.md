---
title: Decided matches in the structured frontend
status: closed
labels: [native,frontend,function-ir,design]
created: 2026-10-02
updated: 2026-10-02
---

## Resolution (2026-10-02): (e), a decision carries its bit

The user chose (e) ("a bit weird, but it will work"), with `bit` beside
`dec` rather than replacing it. Landed:

- `Decide<P> { dec, bit: Bool, reflects: Reflects(P, bit) }` moved from
  `logic` to `bool`. BitVec bits are the comparison bits; `∧ ∨ ¬` are
  `&& || !`; other instances use `or_bit`/`or_bit_reflects` of their `_dec`.
- `if P` without a binder lowers to `match decide_bit<P>()`; the elaborator
  reads `decide_bit` at a resolved instance as the instance's bit. `if h: P`
  is unchanged.
- The frontend reads Bool connective matches as short-circuit branches
  (from branch `s3-frontend-wip`, minus its instance-tree reader and its
  `split_all` changes, neither needed now). One comparison is `refl`; a
  connective is `split_all; all_goals { refl }` over Bools.

Probes for (e) before building (untracked, `probes/dbit/`): a single comparison is `refl`; an `∨`
by hand-written motives or by `split_all` on the reduced spelling; `split_all` on the
unreduced dictionary spelling is refused by the kernel, which is why the
elaborator reduces it. Reasoning: docs/language/decidable-if-expression-design.md
("Lowering and evidence") and docs/archive/native-programs-read-like-programs-design.md
§3 S3 part 3.

---

The issue as filed:

A native step should test bytes with decided propositions (`if b = '\n'`,
`if b = ' ' ∨ ('\t' <= b ∧ b <= '\r')`), which the user chose on 2026-10-02
(docs/archive/native-programs-read-like-programs-design.md §5.1). The library side
landed (5c32d454, fd95e486). The structured frontend side is paused for a
design round (user, 2026-10-02). This issue owns that design.

## What exists (branch `s3-frontend-wip`, 27a6364a, not merged)

- `Builder::branch` reflects a `decide<P>()` match into nested conditionals on
  comparison bits, which is short-circuit code. It reads `P` through the
  instance tree: `logic::And/Or/Not::Decide`, `BitVec::unsigned_lt::Decide`,
  `unsigned_le::Decide` (as `¬(b < a)`) and `BitVec::Decide#Eq`. It reflects
  Bool `&&`, `||` and `!` matches the same way. A wc_l step with
  `if 10 <= b ∧ b < 11` reflects and generates code.
- split_all looks through the applied-match equation idiom
  `(match x as λ c => (x = c) → …)(refl)`, unfolds `_dec` decisions, and
  links a comparison spelled the same way twice.

## The blocker

The generated `{prefix}_source_expands` (expansion = source) was `refl`. The
expansion branches on bits and the source on `decide`, and case-of-case is
not definitional.

## Options, costed against the code

- **(a) split_all proves it: blocked.** Abstracting the bit inside a
  decision's proof terms (the idiom feeds `h : bit = True` to
  `borrow_sub_bit_true_iff(…).mp`, whose type mentions the bit through a
  global's signature) gives a motive that is ill-typed at a general `z`. The
  elaborator accepts it and the kernel refuses
  (`probes/ergo/t_s3_z5.hthr`-style goal: an explicit bit match against an
  `if`). Single-definition goals happened to pass (u2/u3).
- **(b) Direct lemma bridging, about 800+ lines.**
  - The expansion keeps the source's decide form at each head, so `refl`
    stays. The observation bridges with `Reflects`/`decided_select`/
    `and|or|not_select`, all checked in a probe (design §3 S3).
  - Helpers whose body is an `if` (`space_byte`) can be neither inlined nor
    crossed by `refl`. The final proof needs the code's value and the
    observation's values to be convertible, so the crossing link in
    `structured_cert.rs` needs a bridge too.
- **(e) `Decide` carries its bit.** Add `bit: Bool` and `reflects:
  Reflects(P, bit)`, with defaults for old instances. An evidence-free `if P`
  then elaborates to `match P.bit`, which for the BitVec instances is
  definitionally the bit match the frontend already compiles. This is a
  language-level change to what `if` means (close to Lean's `ite`/`decide`).
  Connectives still need eager 1-bit `band` (register pressure unproven) or
  small bridging.

Related: [[native-programs-read-like-programs]],
[[byte-vocabulary-for-native-programs]], [[split-all-through-decisions]].
