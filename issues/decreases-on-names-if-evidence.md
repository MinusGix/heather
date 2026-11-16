---
title: A measure's `on` could not name an `if h:` evidence, and a `let` under named tests lost the unfolding
status: closed
labels: [elaboration,termination]
area: language
created: 2026-11-15
updated: 2026-11-15
---

Found writing the UTF-8 validator (`examples/utf8/utf8_check.hthr`), two
defects of a measured body's `on ?decN` discharge:

1. **`h` unbound in the `on`.** `if h: 0 < n { … f(n - 1) … }` binds its
   evidence only when a branch names `h` (the parser's `names_from`, so that
   a branch that does not is a plain convoy). The `on ?dec1 := { … h … }`
   that discharges the call's obligation comes after the body, so the
   evidence was never bound and the discharge read "unbound name `h`".
   The parser now reads the names of the body's `on` clauses ahead of the
   body (`Parser::on_names_ahead`) and counts them as named.
2. **No unfolding when a `let` feeds the call under named tests.** With
   `let w = …; if z: w = 0 { … } else { f(n - w) }`, the body's lifted
   `f#obl_1` quantified the tests' equations (its statement reads the alias
   `w`, so `select_scope` takes equations about needed binders), while the
   companions, which read the body with its `let`s inlined, selected none
   and cited the obligation unapplied: `f#ext` was refused and `f` had no
   `f_unfold`. A companion now cites the body's own lifted declaration over
   the binders it quantified (`Rewrite::known`).

Probes: `halve` and `hop` in `lib/_tests/std/core/branch_equations_tests.hthr`.
