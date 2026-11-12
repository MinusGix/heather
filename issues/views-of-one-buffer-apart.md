---
title: Lend two views of one buffer, one to write, where the path knows them apart
status: open
labels: [native,function-ir,memory]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

A call over views (`Lend`, [[native-library-exports-design]] §3.1) is lowered only where a view to write is of a buffer no other view of the same call is of (`views_alone`, `lib/native/function_ir/function_ir_lower_views.hthr`). So a function cannot lend one half of a buffer to read and the other to write, though the meaning says what that does (`halving`, `lib/_tests/native/function_ir/function_ir_views_tests.hthr`) and the machine law allows it: `Viewed.alone` (`lib/std/arch/x86_64/x86_64_views.hthr`) asks of a written view and another view that they are of different spans or share no byte. The lowering's report names it ("a view to write shares its buffer with another view", pinned as `halving_refused_why` in `function_ir_lower_views_tests.hthr`).

What uses it: copying within one buffer (`copy_within`), hashing a block of an arena into a state held in the same arena, a parser that reads the input's tail while it writes a prefix in place.

## What it takes

Read off the code as built in V4c:

- **The check.** Beside "no other written view of this buffer" (kept: `Loan::view_written_reads` puts back one window a span, and `put_views_stored` is stated for one), a view to write and a view to read of one buffer pass where the path knows them ordered: one's `end` is the other's `start` (the same id, which is `split_at`), or `File::at_most` of the two. The check then takes the file, as `View::lendable` does.
- **`Lendable`.** Its `alone` field becomes a fact about values: of a written view and another, different buffers, or one's end at most the other's start. `Lendable::parts` already builds `Viewed.alone`'s disjunction and would take the ordered case through `view_inside` (a window's length is at most `end - start`). `Lendable::put_reads_at`'s `only` needs just the part kept.
- **Two written views of one buffer** (`split_at_mut` with both halves written) is a step further: `put_views` puts both windows back, and the machine lemma would be `view_written_reads` for a set of windows of one span. Not needed for the uses above.

## Done when

`halving()` lowers and is stated against its run as `lending()` and `crossed()` are, and the control is two overlapping views of one buffer, one to write, refused.
