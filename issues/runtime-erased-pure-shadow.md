---
title: A plain runtime fn, or one over a span, taking an erased parameter: compile it from a shadow
status: closed
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
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

## Log

- 2026-11-25: Second wave of `docs/language/ownership-design.md` §12: taken as its own round. It is on the critical path: the judgment's obligations (`Valid`, `Apart`) travel as erased proofs, so a compiled caller of a function that takes one is what lets them reach compiled code.
- 2026-11-25: Round started (branch `claude/ownership-erased-callers`). The route, written down before building, and why it avoids each wall the shadow hit:

  - **What is compiled.** A plain function of words that takes an erased parameter is compiled from its reflection written out (`f::words`, published as `Setup::of_erased(f, λ xs… => …)`): a closed Heather function of the code's words whose body is what the reflection's meaning reduces to (each operator's `Op::sem`, a let through `Setup::once`, a branch through `Setup::either`, a call of the table's entry by its global), the way `runtime_span_publish` writes out a laid record's function. `instance Compile(f::words)` is the ordinary plain instance at that term (`Setup::compile`, `typed_refl`, `at_every`); its world's entry 0 is the term, its callees their globals.
  - **Wall 1, the instance's pin at a neutral file.** The shadow's pin compared two *meanings*, at `World(…, [])` and at `World(…, b)`, so the kernel compared their worlds argument by argument, failed at the file, and unfolded both. Here one side is the written-out term, which has no world in it: the pin `f::words ≡ rt.meaning(w.at(callees, b))` unfolds the meaning once against a λ that names the same globals, the same conversion an ordinary plain function's pin is (the function's body against its meaning), and a function lent nothing has no `Byte` node, so `b` is never read. No lemma that a function lent nothing means the same at every file is needed, because no two meanings are compared.
  - **Wall 2, linking.** The shadow was itself a meaning at a world, and the link compares each table at each file, so it compared the shadow with itself at two worlds. `f::words` is a global whose body is a λ over globals, exactly what every table entry already is; a caller's table lists `Global(g::words)` and its instance `g::compile`, so the link meets it as it meets any callee (one δ to `Setup::of_erased(g, …)`, which the instance is stated at letter for letter).
  - **What is stated of `f`.** `f::reflects : rt.meaning(world)(xs…) = f(xs…, ps…)` at a local for every erased parameter where `f` takes it, by `refl`: the reflection pinned against `f` at every proof and every erased value, as the record shape's `runs_held` is. `f::agrees` (and `agrees_also`, `agrees_at`) state the program against `f(xs…, ps…)` the same way; each is checked by the one conversion `f::words(xs…) ≡ f(xs…, ps…)`, the written-out body against the elaborated one, linear in `f`.
  - **A caller.** A runtime fn calling `g(x, p)` with a found proof reflects the call as `Call(g::words, [x])` (`rt_callee` lists `g::words` where `g` published one), so its code passes no proof; its own pin compares `g(x, p)` with `g::words(x)`, unfolding the callee once per call site (the record shape's proposal for its callers says the same). A citation of `g::reflects` there would need a rewrite under the caller's binders; left as residue if it shows as cost.
  - **Scope this round.** Loop-free, lent nothing, parameters words, `Bool`s or counts (no enum or record parameter, which `f::agrees` case-splits or reads back), no recursion; each other shape refused by name.
- 2026-11-25: Built and verified (branch `claude/ownership-erased-callers`), on the route logged above:

  - `runtime fn f(…, p: ∥P∥, …)` and `f(g: Erased<A>, …)` of words compile from `f::words := Setup::of_erased(f, λ xs… => …)` (`runtime_erasing`, `RtWriting::value`, `runtime.hthr`); `instance Compile(f::words)` is the ordinary plain instance. `f::reflects` and `f::agrees` (with `agrees_also`, `agrees_at`) take a local for each erased parameter where `f` does (`runtime_params_erasing`) and hold at every proof and every erased value. Neither wall recurred: the pin and the link checked within the default rails, the whole probe file in seconds.
  - A compiled caller passing a found proof (from a literal, from its own `if h:` test, or its own proof passed on) lists `g::words` (`rt_callee`, `rt_written_of`) and its code passes no word for the proof (`half_of::arities = [1, 2]`). The linker reads `g::words` back to `g` (`runtime_erased_source`, `runtime_entry_id`). A function of a laid record calling one of words that takes a proof compiles too (`Slots::halve`).
  - A span writer taking one takes the written-out path of a `Bytes(n)` function (needs `import runtime_data;`), its `reflects` and `runs_over` stated against `f` at every erased value.
  - Functions taking none publish exactly as before (empty mask, `runtime_params_at`'s telescopes, every statement at `f`); `scripts/test --pr` with `HEATHER_PR_NATIVE=all` on the final tree: `== suite: 3514 passed, 0 failed, 2 ignored ==`.
  - Probes in `runtime_erased_tests.hthr` moved from refusals to rows; controls kept (an erased value computed with, a missing proof, a loop, a record function calling one of the record that takes a proof).

  Decisions: the written-out function is named `f::words`; a theorem's erased locals stand where `f` takes them (as the record shape's `runs_held`); the writer covers `Var`, `Lit`, `Prim`, `Call`, `Let`, `If`, `IfEq`, `Make`, `Field`, `Inject`. Not built, each refused by name and filed: [[runtime-record-calls-erased]] (a record callee's mark owes its agreement at every word, where no proof exists) and [[runtime-erased-written-out-shapes]] (enum and record parameters beside an erased one, a body with a match on an enum or a fold, a function lent a span, an export that takes one through `compile-x86`, the caller's per-call-site unfolding). Loops wait for [[loops-on-one-combinator]] round 4.

  The done-when is met: closed.
