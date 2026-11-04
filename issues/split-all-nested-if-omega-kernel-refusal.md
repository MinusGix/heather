---
title: split_all then omega over a nested if is refused by the kernel
status: open
labels: [tactics,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-02
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
