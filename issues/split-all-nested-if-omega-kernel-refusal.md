---
title: split_all then omega over a nested if is refused by the kernel
status: closed
labels: [tactics,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-06
---

Found writing the `for`-loop probes (2026-11-02). After `split_all`, `omega`
closes each goal, and the kernel then refuses the theorem when the function
is a nested `if` whose two conditions decide different propositions:

```heather
import logic; import bool; import nat; import list; import omega;
record St { words: Nat, inside: Bool }
fn stepB(s: St, b: Nat) → St {
    if b = 32 { St(s.words, Bool::False) } else { if s.inside = Bool::False { St(s.words + 1, Bool::True) } else { s } }
}
theorem b_words(s: St, b: Nat): stepB(s, b).words <= s.words + 1 { split_all; all_goals { omega } }
```

The refusal reads "the kernel rejected `b_words`: NotConvertible … which has
type `or_elim` where a type that displays the same is expected". With only
one `if`, the same proof checks. With the state as separate parameters, `fn
stepF(w: Nat, i: Bool, b: Nat) → Nat { if b = 32 { w } else { if i =
Bool::False { w + 1 } else { w } } }` is refused before the kernel instead:
"`omega` got stuck: Omega could not spell a natural expression".

This is the step-fact shape that `docs/sequencing-surface-design.md` §7.2
expects to be one line, and a `for` loop's generated step (`f::step`)
has exactly this shape.

## Done when

Both theorems above check, or are refused by the elaborator with a located
reason.

## Log

- 2026-11-06: Fixed. Two defects, one per theorem.

  - `b_words` (and already a single `if s.inside = False`, which the issue did
    not try): `if c` is `match decide_bit<c>()`, and Bool's `Decide<a = b>`
    bit is `or_bit(a.eq_dec(b))`, whose type arguments spell `s.inside = False`
    as a quoted `Id`. The search found the blocker `s.inside` below that call
    and lifted it into the enclosing reduct by replacing only the call's
    position, so the reduct kept `s.inside` in `or_bit`'s type arguments while
    its argument was at `z`: a motive that restates the goal at `s.inside` but
    is no type at any other `z`, which only the kernel noticed. Nat's
    `Decide<n = m>` bit is `n.same(m)` with no such type argument, which is why
    the Nat `if` checked. `stuck_scrutinee` now lifts a blocker with
    `abstract_scrutinee` (`lifted`), abstracting every occurrence of the
    scrutinee in the reduct, as the top-level motive already did.
  - `stepF`: `i: Bool` is a finite local, split first; the `if i = False` is
    then a match on `or_bit(eq_dec(False, False))`, which computes to a
    constructor, so the search does not split it, but `simplify_goal` left it
    standing because the call's value is evidence no source spells. A `Case`
    whose scrutinee computes to a constructor now takes its arm.
  - The class: `motive_is_a_type` checks every split's motive is a type under
    `z`, so a partial abstraction is reported at the `split_all` instead of as
    an Unrecorded kernel refusal of the declaration.

  Probes in lib/_tests/std/tactic/omega_tests.hthr.
