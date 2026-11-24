---
title: A plain runtime fn, or one over a span, taking an erased parameter: compile it from a shadow
status: open
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

A plain `runtime fn` of words, and a function over a span that writes it, cannot take an erased parameter (a proof, an `Erased<A>`): each is refused by name ("a function of words that takes an erased parameter … is not compiled yet", "a function over a span that takes an erased parameter …"; probes in `lib/_tests/native/runtime/runtime_erased_tests.hthr`). A function of a laid record and one of a `Bytes(n)` take them ([[runtime-erased-parameters]]). The difference is what each compiles: a record's or a `Bytes(n)`'s code is compiled from *the reflection written out* (`HWorld::of_record`, `o.compiled` in `runtime_span_publish`), a closed term with no proof in it, and only `runs_held` / `runs_bytes` mention the function, at every value of its erased parameters. A plain function's `Compile(f)` instance, and a span writer's, are typed by `f`'s own signature (`Setup::compile`'s `typed: Itself(F) = Itself(Ty::Lent(…))`), and a caller's table lists the callee itself as a total function of its words. Neither has room for a parameter the code does not take.

## The design tried (2026-11-24) and where it stopped

Compile a *shadow*: `f::erased := f::rt.meaning(world)`, a function of the words alone, with the table's own entry a default (`link_own` answers a function's own index with its own meaning, and its code never calls it); `Compile(f::erased)` is the instance, `f::reflects : f::rt.meaning(f::world)(xs…) = f(xs…, ps…)` the pin at every value of the erased parameters (by conversion, `refl`), and a caller's table lists `g::erased` for a callee that takes one. Built on a branch of the round and taken out again, because:

- **The instance's pin compares the shadow with the meaning at a neutral file.** `Setup::at_every` is `refl` at each file `b`: for `f` it is `f ≡ rt.meaning(w.at(callees, b))`, which the kernel decides by running the meaning against `f`'s body. For the shadow both sides are the meaning, at `World(…, [])` and at `World(…, b)`; their argument comparison fails at the file, and the fallback ran out of the conversion budget even for `n / d` (spelling the shadow's world as `w.at(table, no_file)` did not help). A lemma that a function lent nothing means the same at every file (`Tm::ty_static` is the type-level one, `rt_lower.hthr`) would make the pin a citation instead of a conversion.
- **Linking the shadow exhausted the address-space rail** (`runtime_linked`, a one-line identity `id_a(x, p: ∥…∥)`): somewhere in the linking proof (`Compile::part`, the tables at each file) the shadow is compared with itself at two worlds the same way.

The alternative that avoids both: compile a plain function, too, from its reflection written out as a closed function of its words (what `runtime_span_publish` builds for a record, `o.compiled`), and state `f::agrees` against `f` at every value of its erased parameters through the pin. That is the record shape's route, generalised; it changes what `f::program`'s sources are for every function that takes one, which is why it was not done in the round that only needed the record shape.

## Done when

`runtime fn f(…, p: ∥P∥, …)` of words compiles, `f::agrees` holds at every proof, a caller with a found proof compiles to code with no trace of it, and the probes in `runtime_erased_tests.hthr` move from refusals to rows.

## Also waiting here

- **A function of a laid record calling one that takes an erased parameter** (refused, "a call of a function of a laid record that takes an erased parameter is not taken yet"): the caller's held meaning names the callee as a function of record and words (`Writer::runs`), the same gap at the record level. With the callee's reflection written out as its mark, the caller's pin would read the callee's code; what the mark owes would be `T::n::runs_held` at the call's proof, which the caller has where the call is written.
- **Loops** taking an erased parameter wait for [[loops-on-one-combinator]] (round 4): the loop layer (`rt_held_loop`, `rt_bytes_loop`) hands the recursion its words, and an erased parameter would ride beside them.
