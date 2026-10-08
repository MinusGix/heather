---
title: List::count, and fold-count lemmas stated over it
status: open
labels: [stdlib,native,ergonomics]
created: 2026-10-07
updated: 2026-10-07
---

`wc.hthr:40` states the line count as `bytes.filter(newline).len()`, and the
fold lemma it meets is `counts_filtered` (`lib/filter_program.hthr:134`), whose
statement repeats that shape. The list library has no counting function.

Wanted:

- `List::count<A>(xs, p: A → Bool) → Nat`, with `count_nil`, `count_cons`,
  `count_append` and `count_eq_len_filter`, so specs say `bytes.count(newline)`.
- The fold-count lemmas stated over `count` (`fold_counts_filtered` and its
  helper), so a program's meaning and the library lemma read the same.
- Possibly a `lines` helper for byte lists (`xs.count(is_newline)` under the
  byte classes of [[byte-type-and-predicates]]). It is only worth a name if
  more than `wc` wants it; POSIX `wc -l` counts newlines, not lines, so the
  name should not suggest splitting.

Small, library-only. The `filter(...).len()` spelling may need to stay
accepted where existing proofs rely on it, through `count_eq_len_filter`.

## What it assumes from elsewhere

- **[[fold-count-lemmas]]** (closed) owns the fold lemmas. Assumed here:
  only that restating them over `count` is a compatible change.
