---
title: The runtime fn generator's cost grows with the functions a program links, near the native gate's rail
status: open
labels: [native, runtime-fn, performance]
area: heather-in-heather
milestone: [hih-native-heather]
created: 2026-11-06
updated: 2026-11-12
---

Found wiring loops into `runtime fn` (design §16.11). `loop_anywhere.hthr`
as first written (seven runtime fns: two fuel loops at a closed and an open
count, a loop calling a loop, a `Bool` helper) took about 280 CPU-s to
compile cold beyond the warmed runtime closure, against the 300 s rail
`native_program`'s children run under. A `--timings` run attributes it to
the elaborator running the generator, not the kernel gate: `anywhere`'s own
`runtime fn` declaration took about 180 s (gate about 3 s), and each callee
10 to 30 s. Cutting the example to five functions (its closed-count call is
`loop_settle`'s and `loop_multiply`'s already) brought it to about 160 s.

Where the time goes inside the generator is not yet measured: the linking
(`runtime_linked`, every callee's instance and sources re-read per caller)
and the published statements' elaboration (`infer(built)` on the instance)
are the candidates. A tool-sized runtime program would meet this first.

## Log

- 2026-11-10: Measured while probing for `docs/native/native-lexer-crypto-roadmap.md`
  (2026-11-10, cloud box): the generator spends seconds per small word
  function (Σ1 and T1 of SHA-256, a handful of operations each), and a first
  `compile-x86` of one function is dominated by building the runtime closure
  cold. A hash is tens of such functions and a scanner a table plus a loop, so
  both targets want this cost as `scripts/bench-probes` cases before their
  rounds start, to see it move.
- 2026-11-10: The size side of this cost has its own issue now ([[runtime-generator-program-size]]): the reply's square was removed by holding the program and its sources as solved holes, and what remains (requests linear in the program, one declaration evaluating every lowering) is what the compositional linking proposed there removes.
- 2026-11-10: The linking side is settled ([[runtime-generator-program-size]], closed): a callee's table is read from its published `g::world`, where each caller reflected the callee again, and the linking proof cites each function's published `fits`, so a program's cost is its function count times a small constant. The scanner's `scan_choose`, which links twenty-three callees, is about three seconds in all (`scripts/bench-probes --filter lexer/`). What this issue still owns is the per-function cost of the generator itself (seconds for a small word function, most of it elaboration), which that round did not touch.
- 2026-11-12: Found while publishing `f::sourced` (PR #551, `docs/native/native-library-exports-design.md` §6.3): where the generator's time goes in the host, and a rule that removes part of it. Sampled with gdb on the test build, generating `lexer_span::scan_at`. (1) `Run::reify_app` and `Run::same_ty` call `Run::partial_ty`, which rebuilds the whole hole substitution (`Run::sigma`: a `shift_global` of every solved hole's solution) at each application node read. So a reading costs its application nodes times the run's solved holes, and in the debug build each skipped shift is re-verified by the kernel's skip check (`rederive`), which is why the cost showed in the test build first. (2) A `Blank` argument is a hole of the run, solved by a committed term, and stays in that substitution for everything read later. (3) An application with no `Blank` is memoized (`Run::readings`), one with a `Blank` is read again wherever it is spelled. The linking (`runtime_linked`) left each function's type, the table's type and both sides of each `link_both` to inference: a number of holes linear in the program, the later ones solved by statements about everything linked so far. It now spells them (`runtime_types`, `runtime_conjoined`, `link_every_table`), and the scanner's loop functions generate faster than before the round. **What remains here:** the span generator (`runtime_span_parts`, `runtime_span_linked`, `span_every`) has the same `Blank`s and should get the same treatment; the instance's own construction was not looked at; and the host side is worth an issue of its own if it shows again: `sigma` could be built once per world and reused until a hole is made or solved, where it is rebuilt per application.
- 2026-11-12: A cost that was not size: [[runtime-link-compares-functions]]. With a caller and a callee of one Heather type, the link check compared the two functions as constants, and the kernel settled that by evaluating both bodies; it took a SHA round past the budget where a function of padding parameters passed. The library's spelling was changed so the comparison meets data first. Worth knowing when a link's cost looks unrelated to how many functions there are: look at what the two sides are applications of, and in what order their arguments differ.
