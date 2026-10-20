---
title: List::split_by and its lemmas in std
status: open
labels: [stdlib]
area: heather-in-heather
created: 2026-10-02
updated: 2026-10-02
---

lib/std/list.hthr has `filter`, `map` and folds, but no split. wc's word spec
is a bespoke `wc_split` with an `onto_first` helper
(examples/x86-native/wc.hthr), where a reader would expect
`bytes.split_by(space_byte).filter(non_empty).len()`.

Wanted: `List::split_by<A>(self xs: List<A>, sep: A → Bool) → List<List<A>>`.
`n` separators cut a list into `n + 1` pieces, some of them empty, matching
Rust's `split` and Haskell's `splitWhen`. Add the lemmas a client reaches for:
append, the count of pieces, and concatenation with the separators restoring
the list. Also `non_empty` or `is_empty` on lists, if they are missing.

Related: [[fold-count-lemmas]], whose run-count lemma is stated over it.

## Log

- 2026-10-02: 2026-10-02: List::split_by (via split_onto/onto_first), List::non_empty, List::len_filter_cons landed in std. Still wanted: piece count (len = filter(sep).len + 1), append, concat-with-separators lemmas.
