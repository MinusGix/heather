---
title: Give every inductive whose field types mention a function its type codes
status: closed
labels: [elaboration,performance,native]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-31
updated: 2026-10-31
---

Found by [[native-certificate-second-pass]]. An inductive's lowering is
registered as a run of generated definitions (`gendefs.rs`): one payload
code per constructor, the spine sums, the `Wf` shape and arity, and the
whole-type `TyCode`. Each is pushed onto Ψ one after the other from a
lowering read once, at the start. A global in that lowering (a function
called in a field's type: `Asm`'s `measured: bytes.len() = len`, `Char`'s
validity proof, `Prog` through `Asm`) is a de Bruijn index counted from
the end of Ψ, so after the first push every later code read it one
binding off, naming the code pushed just before instead of the function.

What followed, silently:

- The kernel refused the later payload codes, the shape and the
  whole-type code. The elaborator treats a refused generated code as
  absent, so nothing failed.
- With no `Asm#tycode`, every `Asm` and `Prog` type and value was spelled
  as its whole inline lowering. `respell_ty_at` declined `Asm` with
  `no-closed-code` about forty times per `At` of a program literal (the
  symptom [[constructor-literal-respell-cost]] measured and memoised
  around), and the kernel converted inline lowerings against each other
  where a reference would have matched by name.
- The registry's guard copies (what a reader matches a lowering against
  to find its code) were stored at the registration scope and compared at
  the reader's, so even a code that had been accepted was never found
  again once Ψ grew.

## What changed

- Registration reads the lowering at the scope each push sees
  (`Elaborator::read_now`), so every code names the function it means.
- A guard copy that mentions a global records the scope it was taken at
  (`GenDefLayer::guard_at`, written by `module_delta`'s commits so a
  replayed module image carries it too). A reader weakens it to its own Ψ
  length and local context before matching or unspelling, as the kernel
  unfolds a reference: a global's substitution tail carries the context
  length, so a copy cut in the empty context is applied to the reader's
  frame (`guard_read`). The reads are memoised per (Ψ length, frame), so a
  literal's constructors share one.
- Guards with no global are read as before, unchanged and unweakened.

Test: `wf::tycode::a_lowering_that_mentions_a_function_gets_every_code`
(an inductive whose second constructor's field calls a function, and a
recursive one). Every code exists; the lowering respells to its `TyCode`
reference after Ψ has grown, converts both ways and unspells to today's
lowering; under a binder the reference is minted and unspelled in that
context. Negative controls: the stale spelling (the function one binding
over) and the lowering of another context do not respell, and a wrong
proof in the late field is still refused, by its reason. It fails on the
parent commit at the first missing payload code.

## Effect

The shape, not the numbers (those are in [[native-certificate-second-pass]]):
a write-elf certificate's program literal (`at_#`) no longer pays
per-constructor respell declines or inline-lowering conversions, which
cut that family to under half on `cat_files_tool` and to about a third on a
32-pass cat. Everything else that mentions `Asm`, `Prog` or `Char` in a type
now carries a reference instead of the inline sum.
