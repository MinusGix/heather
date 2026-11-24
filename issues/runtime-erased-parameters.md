---
title: Proof and erased parameters of a runtime fn, so an access carries its obligation into compiled code
status: closed
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

An access that carries its obligation has to compile (vision principle 13; `docs/language/ownership-design.md` §10.6). Today the reflector drops only trailing squashed arguments of a call, and a `runtime fn` of a laid record that takes a proof parameter is refused ("a type with no runtime layout"), which is why the arena's window `read` and `store` (`lib/native/runtime/arena.hthr`) are ordinary functions. This is the proof-parameter item of [[runtime-record-function-limits]], taken as its own round with a second half.

## Scope

- **Proof parameters of a `runtime fn`, in every shape the generator has** (pure, span, `Bytes(n)`, laid record): a parameter whose type is a proposition is erased wherever it stands, the callee's meaning and published agreement are stated under it, and a caller's found proof (`:= bv_omega`) is checked where the call is written and dropped from the code.
- **Erased data parameters**: a parameter marked as having no runtime presence (a generation, a region's token), erased the same way, and refused where the code would compute with it.
- **The customer**: the arena's `read` and `store` become `runtime fn`s keeping their found proofs, with their ledger rows (`lib/_tests/native/runtime/runtime_ports_tests.hthr`).
- Controls: a function that branches on an erased parameter is refused by name.

## Done when

The arena's `read` and `store` are compiled `runtime fn`s with their agreements published, a call with a found proof compiles to code with no trace of it, and the refusals are pinned.

## What it assumes from elsewhere

- **[[runtime-record-function-limits]]** owns the other limits of laid-record functions.
- **[[loops-on-one-combinator]]** owns the loop modules its round 4 moves; this issue stays out of them and says which loops over an erased parameter wait.

## Log

- 2026-11-24: 2026-11-24, branch `claude/ownership-erased-parameters`. Built:

  - **What is erased.** A parameter is erased when its type is a proposition, tested as the kernel tests it: two locals of the type are assumed and compared, so a squash `∥P∥` is one and an equation is not (`rt_is_proof_ty`, `rt_reflect.hthr`); or when its type is `Erased<A>` (`lib/std/core/erased.hthr`, exported by `runtime`), a value the meaning reads and the code does not carry (`rt_is_erased_ty`). Why a type and not a binder mark is recorded in `docs/language/ownership-design.md` §13 item 8: no parser (which `ownership-parameter-modes` is changing), one place every shape reads a parameter's type, and an erased binder mode can lower to it later.
  - **The reflector** opens an erased parameter wherever it stands and binds it to no variable (`rt_held_words` for a laid record, `rt_params_under` for words, `rt_params_proved` for a span or `Bytes(n)`, which already skipped proofs and now skips `Erased` too; callee signatures likewise). A use of an `Erased` value as data is refused by name ("an erased parameter (`Erased<A>`) used as runtime data"), whether a parameter, a field read `g.value` or a branch on it. A call's erased arguments are dropped at any position, not only trailing.
  - **The pin, for a function with erased parameters.** For a laid record: `T::m::runs_held(params…, own, t, length, xs…, holds)` takes a local for each erased parameter *where the function takes it* (`runtime_own_erased` walks `T::m`'s type at the arguments before each), and the pin inside it is the same conversion as before, `held meaning(T::m::rt, env) = T::m(params…, t, xs…)` with those locals among `xs`: a wrong reflection still fails it, and it holds at every proof and every erased value because the body cannot compute from them (a proof by irrelevance, an `Erased` by the reflector's refusal, checked again by the conversion). The code `T::m::bytes` is the reflection written out and mentions none of them. For a `Bytes(n)` the same (`runs_bytes` opens every binder of `f`; `runtime_bytes_words` drops proofs and `Erased`).
  - **The customer.** `Arena::read` and `Arena::store` are `runtime fn`s keeping their found proofs (`inside`, `fits`); `store` became `mut self`, answering the element it replaced, and the laws read its `.after`. Ledger rows `port_arena_window_runs` (both run on bytes) and `port_arena_window_held` (both `runs_held` at an open arena, window and proofs) replace the refused `Arena::port_read`.
  - **Probes** `lib/_tests/native/runtime/runtime_erased_tests.hthr`: a proof between words and last, at literal indexes (computed) and open ones (`runs_held` at a neutral proof), a proof whose type names a record parameter (`Ring(cap)`), a found proof in a checking position, an `Erased<u64>` beside a proof, a `Bytes(n)` with both in the middle; controls: a branch on an erased value, a function answering it, a call whose proof is missing, a record function calling one that takes a proof, a loop taking one, and the shapes not built.

  Not built, refused by name and moved to [[runtime-erased-pure-shadow]] with what the attempt found: a plain function of words or a span writer taking an erased parameter (each is compiled from the function itself, typed by its own signature, so it needs a proof-free shadow; the shadow tried, `f::erased := f::rt.meaning(world)`, failed at the instance's pin at a neutral file and in linking), and so a *compiled caller* of a function taking a found proof (a record function calling one is refused too). Calls with found proofs inside a compiled body (`a.heap.at(base + i)`, `s.at(i)`) were already traceless and still are. Loops taking an erased parameter wait for [[loops-on-one-combinator]] round 4 (`rt_held_loop`, `rt_bytes_loop`, `rt_io_loop`, untouched). Open item 4 of the ownership note (erased state a `mut self` method changes, the arena's generation) is not built.
- 2026-11-24: Closed: the done-when is met for the arena (`read` and `store` compiled with their agreements published, the found proofs inside their bodies leaving no trace, the refusals pinned) except a *compiled caller* of a function that takes a found proof, which needs the shadow and is the done-when of [[runtime-erased-pure-shadow]].
