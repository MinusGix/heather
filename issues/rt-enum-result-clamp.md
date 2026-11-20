---
title: Drop an enum result's clamp where the word returned is already a tag
status: closed
labels: [native,runtime-fn,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-20
updated: 2026-11-20
---

A `runtime fn` returning an enum returns its tag word clamped at the last
tag (`Ty::clamp` in `lib/native/runtime/rt_lower.hthr`;
docs/native/runtime-fn-setups-design.md §16.16): a `Const`, an unsigned
compare and a branch at every return. The clamp exists because a program
is linked as a function on every word (`program_linked_files`), and inside
the lowering an enum's word that is no tag reads as the last constructor
(`Ty::Holds` at `Enum` is the word clamped, `EnumInfo::read`). A function
that returns a parameter's word unchanged would otherwise return a word
that is no tag where its meaning returns the last constructor. On every
word a contract passes (a tag) the clamp changes nothing, so its cost is
the only thing a caller could notice.

Most enum results are already tags: a constructor (`Lit`, a `Const` of its
index), a `match` or `if` whose arms are constructors, and (once enums are
passed to calls) a callee's result. Two ways to drop the clamp there:

1. **Track exactness in the lowering.** A second invariant beside
   `Ty::Holds`: the word at an enum's port is at most the last tag. It
   holds of a constant, of a branch whose arms keep it, and of a callee's
   answer; not of a parameter's word. The clamp is emitted only where the
   result's term is not known exact, and `Ty::out_reads` uses the
   invariant where it holds. Local to `rt_lower`.
2. **Link at real values only.** State a function's agreement (`Ty::Answers`)
   with a premise that each enum parameter's word is a tag, and
   `program_linked_files` at the words each function's contract admits.
   Then `Ty::Holds` at `Enum` can be the exact tag and nothing is clamped
   anywhere, but the linking statement (function_ir_eval) and every
   consumer of `Ty::Answers` change.

Route 1 is the smaller step and keeps linking as it is.

A related ABI point: C passes an `enum` as an `int`, so the upper 32 bits
of its register are unspecified by System V, while the contract passes the
tag as a whole 64-bit word. Compilers write the 32-bit register, which
zero-extends, so callers work in practice; reading an enum parameter
through a 32-bit `Resize` at entry, as a `u32` parameter is read, would
make the contract the ABI's.

## Resolution (2026-11-20)

Route 2, at Minus's ask to remove the clamp entirely: agreements and the
program's linking are stated at admitted words (`Ty::Admits`,
`program_linked_files` with `admits`), `Ty::Holds` at `Enum` is the exact
tag, and `Ty::clamp` is deleted. docs/native/runtime-fn-setups-design.md
§16.16, "Linking at admitted words". The ABI point above belongs to a C
`datarepr` of an enum, not to the default tag word.
