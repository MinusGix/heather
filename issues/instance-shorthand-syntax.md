---
title: Instance shorthand: anonymous-constructor literals for trivial instances
status: open
labels: [frontend,syntax,ergonomics,traits]
area: language
created: 2026-08-07
updated: 2026-08-20
---

Split from [[requires-placement-syntax]] (2026-08-07, user call: a different Thing). For instances whose content is a bare value or two, the literal form still names every field: `instance Default<Nat> { default := 0 }`. Sketch: an anonymous-constructor spelling, `instance Default<Nat> ⟨0⟩` (or the syntactically-honest-but-meh `instance Default<Nat> := ⟨0⟩`), Lean-style — positional fields in declaration order, supporting more than one argument since other classes are also 'trivial' in this sense (a Cmp is two fields). Questions for its design pass: ASCII spelling (⟨⟩ needs one; `(| |)`? `{{ }}`?); whether it is instance-only or the record anonymous constructor generally (probably the latter, with instances inheriting it — records are the substrate); how missing-field diagnostics read when positional. Cheap, unscheduled; wants nothing.

## Log

- 2026-08-20: Existential introduction is a second concrete customer for the
  general record literal. `∃ x, P(x)` is type-forming binder syntax, so writing
  the symbol cannot replace the constructor call by itself; a positional
  literal could turn `Exists(witness, proof)` into `⟨witness, proof⟩` without a
  special existential-only introduction form.
