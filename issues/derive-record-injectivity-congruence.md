---
title: Derive injectivity and congruence lemmas for records and constructors
status: open
labels: [stdlib,elaboration,inductives,proofs,ergonomics]
created: 2026-09-18
updated: 2026-09-18
---

Records get their injectivity and congruence lemmas written by hand:
`string.hthr` states `chars_injective` / `cong_chars`, `char.hthr`
`code_injective` / `cong_code`, and both are one `j` each
([[string-char-spec-types]]). The notion is simple enough to derive:

- **Congruence** of every projection: `p: a = b` gives `a.f = b.f`.
- **Injectivity** over the *relevant* fields: two records are equal when
  their non-`Prop` fields are, because a squashed (or `Prop`-level) field is
  irrelevant to equality. `Char` is the shape: `code` decides, `valid:
  ∥scalar(code)∥` is ignored. `String` is the degenerate one-field case.
- **Constructor injectivity and disjointness** for inductives (`Cons`
  injective in both fields, `Nil ≠ Cons`), which `string.hthr` also
  re-derives by hand (`nil_ne_cons`, `cons_eq`, `cong_head`, `cong_tail`)
  and which belong in `list` generically.

A derived `Eq`-style bundle — or the lemmas generated per record/inductive
and attached to the type's namespace — would let `Decide<a = b>` for a
record follow from `Decide` on its relevant fields without a hand-written
decision either (see [[derive-decide-instances]]).
