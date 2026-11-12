---
title: A runtime fn's loop is lent one span only
status: closed
labels: [native,runtime,generator]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-12
updated: 2026-11-12
---

A `runtime fn` that loops is lent one span: `Setup::GuardedSpans` and `runtime_measured_instance` (`lib/native/runtime/runtime.hthr`, `rt_loop.hthr`) build the measured instance for a function whose world is a file of one span. A function with no loop may read several spans, and a loop may call a function lent another span of the same file, but a loop whose own parameters include two spans is refused.

Customers: a comparison of two buffers (`memcmp`, a constant-time equality for a digest), a copy from one span to another once the write half is exported, a lexer that reads the source and a table.

## What it would take

`Fun::GuardedBy<I, K>` is already keyed (the worlds are indexed by the file and the recursion by a key), so the family is there: the key becomes the tuple of the spans, or the file itself. The generator's reading of the parameters (`rt_lent`) takes one leading span and its length word; it would take each leading pair. The loop's lowering keeps the home words of every lent span in place, which is two more pinned registers a span, and that meets [[function-ir-planner-register-pressure]] at once: a calling loop over two spans has one free register in its body.

## Done when

A `runtime fn` that compares two lent spans byte by byte in one loop compiles, with its `agrees_over` at every file.

## Log

- 2026-11-12: Built. Nothing below the generator was specific to one span: the loop's lowering keeps `lent + lent` home words (`Fun::shape_lent`), the reflector numbers spans in order (`rt_lent`, `rt_lent_args`), and `Fun::GuardedBy<I, K>` is generic in its key. What was specific was the class's spelling of the family and the generator's proof.

  - `Setup::GuardedSpans(f, lent, …)` is the family keyed by a file's first `lent` spans as a file of their own (`Setup::spans_of`), with the function at those spans (`Setup::at_spans`); `Setup::guarded_spans` gives `Guarded` at each file. The one-span names (`span_of`, `at_span`, `guarded_span`) are gone; a loop over one span is the family at `lent = 1`.
  - `runtime_measured_instance` builds the proof at any `lent`: the function's own values are its code's words with each span in its place's stead (`runtime_spanned`), an ih is asked at the list of its spans and the places the loop was entered with (`runtime_places`), and the pass is at the file's spans. The refusal "a loop over more than one lent span has no instance yet" is removed.
  - Probes (`lib/_tests/native/runtime/runtime_lent_tests.hthr`): `differ_sum(xs, xn, ys, yn, acc, i)` sums the differences of two spans' bytes in one loop. Its `agrees_over` is stated at every file (`differ_sum_linked`), it runs on bytes with each span under its own length word and with the spans crossed, it is placeless and it lowers. `compile-x86` writes it with its certificate checked: `# signature: differ_sum(span, span, word, word) -> word`.

  What it met is the register pressure this issue predicted. Two spans are four home words kept in place, so with the loop's count a body has four registers for its own values. `differ_from`, the same loop with the index before the sum, makes the next index before it reads the bytes and is one register short at the second load; it links and runs, and `differ_from_crowded` states that the lowering has no code for the planner's placement. Logged on [[function-ir-values-in-kept-registers]], which is what gives a loop over spans room.

  Not done here: a function that writes is still a function of one span (`FTm::Source`), and a loop cannot pass a span on in another place. Those are V5a of [[source-buffers-as-views]].
