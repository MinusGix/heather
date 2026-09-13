---
title: The conversion shortcut's speed is a std Arc specialization the kernel never wrote down
status: open
labels: [kernel,conversion,performance,representation,docs]
created: 2026-09-13
updated: 2026-09-13
---

The kernel's syntactic reflexivity shortcut — `typing.rs:678`'s
`expected == inferred`, 2.78 M hits per omega module, and `conv/dom.rs`'s
`tm_eq_fast` — is fast because of a `std` **specialization**, not because of
anything the kernel wrote. `impl PartialEq for Arc<T>` dispatches through
`ArcEqIdent` (`library/alloc/src/sync.rs:3524-3559`), whose `T: Eq` instance is
`ptr::eq(…) || **self == **other`. `Type` and `Term` `derive(Eq)`, so the
pointer test fires at the root and at every child, and comparing two trees that
share a subtree stops at the shared node.

Nothing in the kernel says so. Three consequences:

- **It is load-bearing and undocumented.** The 2026-09-13 arena design pass
  (`docs/kernel-arena-terms-design.md` §4) initially costed hash-consing as
  worth the whole 2.78 M-hit walk, and was wrong for exactly this reason. The
  next reader will make the same mistake.
- **It is fragile in a way the compiler will not catch.** Wrapping a child in
  any other handle — a newtype, an arena-id wrapper, a `Box` — silently loses
  the shortcut with no error and no test failure, only a slope. Dropping the
  derived `Eq` (leaving `PartialEq`) does the same.
- **`ty_eq_fast` and `tm_eq_fast` disagree** (`conv/dom.rs:1665-1673`):
  `ty_eq_fast(a,b)` is `Rc::ptr_eq(a,b)`, `tm_eq_fast(a,b)` is `a == b`. Given
  the specialization, `tm_eq_fast` is pointer-first *and* structural, so the
  asymmetry says types deliberately refuse the structural fallback where terms
  take it. That may be measured; it carries no comment either way.

## The fix, which is small

A comment in `term.rs` beside the `derive(PartialEq, Eq)` on `Type`/`Term`
naming the specialization and what depends on it, plus a comment on the two
`*_eq_fast` hooks saying which of them takes the structural fallback and why.
Optionally a bench case that would move if the shortcut were lost (two large
structurally-equal trees, one pair sharing its root and one pair not).

## Trigger

Any round that touches the term representation, the `Eq`/`PartialEq` derives,
or the conversion shortcut — and `kernel-arena-terms-frozen-prefix` first of
all, whose adequacy draft explicitly notes that index equality is sound but
not complete for structural equality.
