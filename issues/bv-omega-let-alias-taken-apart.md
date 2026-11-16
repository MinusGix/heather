---
title: bv_omega takes a let-bound word apart where it cannot, and fails where the word as an atom would do
status: closed
labels: [tactics]
area: tactics
created: 2026-11-15
updated: 2026-11-16
---

In the binary search's invariant (`examples/binary-search/search.hthr`,
`lower_bound_in_splits`), with `let mid = lo + ((hi - lo) >> 1)` and
`end: mid < hi`, `fits: hi <= n` in scope, `bv_omega` refuses `mid <= n`:
it reads `mid` through the `let`, must show the addition does not
overflow, and cannot see through the shift ("`… may overflow 64 bits`").
Before #660 it proved the goal, reading `mid` as an atom bounded by the
facts that mention it; plain `omega` still does, which is what the example
writes now. The same happens for `j <= mid` from `j < mid + 1` and
`mid < hi`, so the example keeps two small lemmas (`le_of_lt_next`,
`next_le`) that only need the atom.

Done when a word `bv_omega` cannot fully take apart is kept as an atom
(its `toNat` bounded by `2^64` and by the facts in scope) instead of
failing on its side conditions, so the three goals above are one
`bv_omega` each with the full context in scope.

## Log

- 2026-11-16: Fixed: a word whose side conditions omega refuses is kept as an atom, bounded by its range and the facts that mention it (docs/tactics/bv-omega-design.md §5.1). The binary search's three range facts about `mid` are each one `bv_omega` in the invariant; next_le and le_of_lt_next are gone. Probes: lib/_tests/std/tactic/bitvec_omega_tests.hthr ("kept whole").
