---
title: The join and bound recognisers do not read a constant index, so sums that index are kept from folding
status: open
labels: [native,optimizer]
area: heather-in-heather
created: 2026-11-17
updated: 2026-11-17
---

The optimizer's hand-written recognisers know an index as a base word and a constant (`Ordered.sums` in `lib/native/function_ir/function_ir_learn.hthr`): the joins of byte loads into one four-byte load (`Seen::joining`, `Join::beside`, rules 24 and 29 to 33), and the comparison of a wide access's last byte that the lowering reads (`Seen::ends_at`, `Seen::bound_written`).

With the rule `add_consts` on, `60 + 1` is the constant `61`, and neither reading sees it: four loads at 60, 61, 62, 63 stay four, and a joined load at 60 loses the bound of `60 + 3` and the lowering refuses it. SHA-256 grew by a tenth before `Seen::settles` was taught to leave such a sum alone (a sum of two constants that a load or a store indexes by, or that is past such an index: `consts_folded`, `index_kept` in `lib/_tests/native/function_ir/function_ir_identities_tests.hthr`; `docs/native/optimizer-rules-design.md` §12, "A sum that indexes stays a sum").

That guard is a recogniser's reading leaking into the rules. It goes when either

- the joins and the bound read a constant index as base zero and that constant (the replayer's order rules then need a form for two constants, which a range of one value gives), or
- the joins and bounds are rules themselves, matched over the facts, so they read the sum the replayer still has after it is written as a constant (`Walked::earlier`).

Until then an index like `(i + 4) + 1` over constants is computed at run time where one immediate would do.
