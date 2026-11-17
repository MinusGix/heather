---
title: Three nested match h: over one pipeline equation, and the kernel rejects what the elaborator built
status: open
thread: Make compiler correctness proofs elegant
labels: [elaborator,matching,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-17
updated: 2026-11-17
---

`Source::calls_built` (`lib/native/native_compile_correct.hthr`) inverts a four-stage `None`/`Some` pipeline behind `compiled: src.compile_calls(low, homes) = Some(program)` and needs the equation of three of its stages (`emitted`, `coded`, `linked`). Written with `match h:` at each stage, after [[case-split-refines-hypotheses-under-calls]]:

```
match emitted: src.main.emit(src.entry(low, homes), layout, [], layout.deep_label()) {
    None => absurd(compiled),
    Some(c) => match coded: src.procedures.procedures_code(exit0(c.prog), layout, 0, c.names) {
        None => absurd(compiled),
        Some(d) => match linked: d.prog.deep_exit(layout).links(src.functions, homes.places, d.names) {
            None => absurd(compiled),
            Some(whole) => match whole.laid_out() {
                False => absurd(compiled),
                True => { … let r: CallsBuilt(src, low, homes, program) = CallsBuilt(c, emitted, …); r },
            },
        },
    },
}
```

Two things, found 2026-11-17 on master f38a8af8:

1. **The kernel rejects it.** With the last arm reading `let same: (Some(whole) = Some(program)) = compiled; … subst(same, linked)`, the elaborator accepts the declaration and the kernel answers `NotConvertible. this has type CallsBuilt where a type that displays the same is expected; they differ in something the display does not show`, at the arm's result `r`. A term the elaborator built and the kernel refuses is a defect in the motive the named form builds, whatever the proof should have been.
2. **The documented exception bites the natural spelling.** `subst(compiled, linked)` passes the refined hypothesis beside `linked` in one call, so `compiled` is then not refined at all, and it is the `None => absurd(compiled)` arm two lines up that reports it (`absurd needs both sides of the equation to be constructor applications`). The error is far from its cause.

The same pipeline with plain `match` at every stage checks (`Source::calls_laid`), so the named form at depth is what differs.

Repro: `/mnt/project-files/compile-proofs/calls_built_named_match_kernel_reject.hthr` is the whole file in the first state; check it in place of `lib/native/native_compile_correct.hthr`.

`calls_built` keeps its written motives until this is fixed.

## Done when

`Source::calls_built` checks in the form above, and a refusal to refine a hypothesis is reported where the hypothesis is used beside `h`.
