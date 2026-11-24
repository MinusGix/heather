---
title: FunctionIR: two comparisons computed in one leaf leave only one fact for the arms
status: open
labels: [native,function-ir]
area: heather-in-heather
created: 2026-11-24
updated: 2026-11-24
---

Found writing the probes of [[views-of-one-buffer-apart]]: `compared_by` in `lib/_tests/native/function_ir/function_ir_lower_views_tests.hthr` first computed `length < end` (10) and `length < start` (14) in one leaf and then branched on 10, then on 14. In the arm where both are false the lowering did not know `end <= length` (`View::lendable`'s report: "no arm taken on the way here says that its end is at most the buffer's length"). Computing each comparison right before its branch (`then([cmp], when(...))`) gives both facts, which is how the probe is written now.

So a fact of the path (`Known::Falsity` read through `falsity_at_most`, `function_ir_lower_reads.hthr`) seems to need its comparison still known when the branch is taken. Read why the first comparison's `Compared` entry is gone by the second branch (likely dropped with its register when the second comparison was placed) and keep it, or say in the design what a front end must emit.

Related: `File::at_most` takes no step of transitivity (`a <= b`, `b <= c` does not give `a <= c`), so a split whose halves are each compared with the length, and not with each other, is not known apart.
