---
title: Infer an inner match's motive after the outer arm reduces the goal
status: open
labels: [elaborator,match,proof-ergonomics]
area: language
milestone: [none]
created: 2026-11-26
updated: 2026-11-26
---

Motive inference abstracts a scrutinee that the goal reaches after
unfolding ([[goal-motive-by-scrutinee-abstraction]], closed), but not one the
goal reaches only after an *outer* arm's reduction. A proof that follows a
function with nested matches arm by arm has to spell every inner motive.

Seen repeatedly in the P3109 rounds (docs/library/float-p3109-design.md §§6–7):
`Format::project_correct`, `round_odd_fin_spec`, `P3109Layout::half_rt`,
`neg_rt`, `half_dec_inf`, `half_dec_nan` each restate the function's inner
`match` as the motive, and the kernel rejected an unannotated inner match in
`encode_decode` (`match (n - L.B()).eq_dec(0) { … }` inside an arm), fixed by
a constant motive. A related failure: when a predicate is defined by the
same `match` as the function it is applied to (`HighOk` in the second P3109
round), one motive must abstract both copies, and neither inference nor a
hand-written motive did.

Expected: after an outer arm, the goal is put in weak head normal form
again before the inner match abstracts its scrutinee, as the first level
does. Check whether `match h:` case splits ([[case-split-reaches-arguments-of-stuck-calls]])
already cover these shapes; if they do, the fix is documentation in
docs/proof-patterns.md.
