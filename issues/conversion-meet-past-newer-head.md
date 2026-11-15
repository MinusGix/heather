---
title: Conversion unfolds a newer head the other side reduces to, then unrolls it at a closed count
status: closed
labels: [kernel, conversion, native]
area: kernel
milestone: [hih-native-heather]
created: 2026-11-06
updated: 2026-11-06
---

Found wiring loops into `runtime fn` (design §16.11, `docs/native/runtime-fn-setups-design.md`).

A plain `runtime fn` rests on its pin, `meaning(rt, world)(x⃗) = f(x⃗)` by
conversion, and `world` holds `f`'s callees as the functions themselves.
`loop_multiply.hthr`'s `multiply` calls `shift_add` at a closed count, 65.
The kernel's δ-lazy loop (`Conv::tm_w`) unfolds the *newer* of two different
heads, on the ground that a body mentions only older globals. That holds of
bodies, not of arguments: `meaning` is older than `shift_add` but reduces to
`shift_add(…)` through its `world` argument. So the loop unfolded `multiply`,
then `shift_add` on that side, past the spine the other side was about to
reach; `meaning` then unfolded to the same recursion, and both sides unrolled
the count. `shift_add`'s pass has two recursive arms, so the two trees have
2^65 leaves, and a comparison below the recursor's minor premises meets
nothing it can shortcut (each level is a fresh `ElimNat` at a literal, not a
spine). At count 9 the pin passed; at 20 the elaborator's check ran out and
the generator's failure message, showing both sides, ran the compiler out of
memory.

The same shape without the runtime generator
(`lib/_tests/lang/conversion_meet_tests.hthr`): `apply_to(walk, 64, x) =
walk(64, x)`, with `apply_to` declared before `walk`.

## Fix (2026-11-06)

`Conv::tm_w` keeps, per side, the last few spines it advanced past a head the
other side did not have (`Passed`). Whenever one side's head is one the other
side was advanced past, the two spines are compared there before anything
else (and each remembered spine is tried once). Where the other side has no
head left, this side advances one head at a time, at most `MEET_STEPS`,
looking for a remembered head (`Conv::meet_on_the_way`), before unfolding the
rest in one run as before. A failed meet costs the comparison it was
already going to make one level down.
