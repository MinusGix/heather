---
title: simp_only(f) never tries a measured function's branch equations seven tests deep
status: open
labels: [tactics]
area: tactics
created: 2026-11-16
updated: 2026-11-16
---

In the UTF-8 example (`examples/utf8/utf8_check.hthr`, `valid_from_decides`),
`simp_only(utf8_valid_from, stops, discharge := bv_omega)` takes the loop's
branch in eight of its steps, every one whose branch is at most six tests
deep: ASCII, a continuation byte, the two-byte cases (with
`bad: utf8_two_at(s, n, i) = 0` in scope), and the three-byte "too few
bytes left" case (`True::False::False::False::True::False`).

The same call, with the same kind of facts in scope, refuses the five
steps whose branch is seven or eight tests deep (three- and four-byte
sequence checked, four-byte "too few bytes left"): "the two sides do not
meet … no law fired". The report's "blocked at the normal form" list
names every shallower law with the side condition it lacked, and none of
the deep ones, so the deep laws are not refused for a side condition: they
read as not matching at all (`Outcome::Miss` in
`crates/elab/src/rewrite/simp.rs`). Adding the lead-byte test as a
hypothesis in the law's own spelling
(`lead_below(…, 0xF8, t5): s.byte_within(n, i).zero_extend(56) < 0xF8`)
does not change it. The example keeps those five steps citing the named
equations (`utf8_valid_from::True::False::False::False::True::True::True`
and so on).

Done when those five steps are `simp_only(utf8_valid_from, …,
discharge := bv_omega)` like the other eight, or the report says which
part of a deep law did not match.
