---
title: Erased fields of a record a runtime fn takes: the arena's claims beside its laid words
status: open
labels: [ownership,native,reflector]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
---

`docs/language/ownership-design.md` §13.4 is settled for the arena by [[ownership-stores-and-keys]]: erased state a `mut self` method changes is an erased field beside the laid record (`Heap { arena, claims, ok }`, `lib/native/runtime/arena_handles.hthr`), not a parameter of its type. Today `Heap` is an ordinary record and its functions ordinary `fn`s; the compiled arena is still `Arena`'s `runtime fn`s.

What compiling `Heap`'s functions needs: the reflector dropping a record's erased fields (here `claims` and `ok`, never read by code, only by proofs) the way [[runtime-erased-parameters]] drops erased parameters, so a `mut self` method of `Heap` lowers to `Arena`'s words alone and its certificate is about them. Which fields are erased has to be stated somewhere the reflector reads (a mark on the field, or a type whose values have no layout).

## What it assumes from elsewhere

- **[[runtime-erased-parameters]]** owns dropping erased parameters. Assumed here: only that a dropped field is the same question one level in.

## Log

- 2026-11-25: Round started (branch `claude/ownership-erased-fields`). The route, written down before building, and why the pin stays one conversion linear in the function:

  - **How a field is marked.** One recognition for parameters and fields (`rt_erased_param`): a field is erased when its type is `Erased<A>` or a proposition. The kernel's irrelevance test alone does not make `HeapInv(a, claims)` or `Heap::Valid(h, w)` (an equation) a proposition, and `Heap::read`'s `valid` is such a parameter, so the test is widened, for parameters and fields alike, to *propositions by their form*: an equation, a function type into a proposition, an inductive whose constructors all carry only propositions (a record of them, `Or`, logic's `True` and `False`), and a definition that unfolds, or a recursion stuck on an open argument whose arms are, one of those (`Nat::Le`, `Arena::Apart`). So `ok: HeapInv(…)` needs no wrapper; `claims: Store<Claim>` and a window's `key: Key` are data and are wrapped, `Erased<…>`, as design note §13 item 8 decided for erased data. The classification is untrusted: a wrong verdict is a pin the kernel refuses, since every statement holds at a local of each erased thing.
  - **What compiles.** A `runtime fn` whose record is a plain record of exactly one laid field (`arena: Arena`) and erased fields, and which may take records whose fields are 64-bit words and erased fields (`w: Window`), is reflected as the laid field's function: the local `h` stays a local, `h.arena` stands for the laid record (its field reads are the accessors' reads, a call's record is it), a word field of a record parameter is a word of the code (in field order, where the parameter stands), and a read of an erased field as data is refused by name. A body ending `Mutated(Heap(a′, …), v)` is read as `Mutated(a′, v)`: the erased fields' new values are never walked.
  - **The pin.** `T::m::runs_held(own, h, length, xs…, holds)` takes the whole record `h` (and each record parameter whole) where the function does, the span holding `h.arena`, and states the held meaning against `HWorld::through(T::m(h, …), λ r => r.arena)` (`Mutated(m.after.arena, m.value)`; a function that only reads, `unchanged(h.arena, T::m(h, …))`), at every value of the erased fields. The kernel unfolds `T::m` once, the projections of its result reduce by ι to the laid record's after and the value, and from there it is the comparison the laid record's own function would make: the erased fields' terms are discarded by the projection and never compared. No two meanings are compared, and nothing on the right has a span, a world or an environment, so it is the ordinary pin's cost.
  - **What does not change.** Records with no erased field publish the same declarations from the same terms: the new reading runs only where the record is not laid; `FTm::Sem`, `HWorld` and every reflected language's meaning are untouched (the one addition beside `HWorld` is a plain projection helper). Callers of a function of such a record, and an answer carrying an erased field (`Heap::alloc`'s `Grant`, a `Window` with its key), are left for later rounds and refused by name.
