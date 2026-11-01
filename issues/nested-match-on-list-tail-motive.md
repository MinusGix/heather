---
title: A motive-less nested match on a Cons tail does not specialise the arm's binder types
status: closed
labels: [frontend,elaborator,proofs,ergonomics]
area: language
created: 2026-10-26
updated: 2026-11-01
---

A `match` with no `as` motive, on the tail binder of a `Cons` arm that sits
inside a `match` on a function's own Pi binder, does not abstract the tail
in the binder types it checks against. Found by `native-source-bytes`
(`Target::goes_single`, `lib/native/native_compile_bytes.hthr`, which now
writes its motive).

```heather
fn total(xs: List<Nat>) → Nat { match xs { Nil => 0, Cons(x, rest) => x + total(rest) } }
theorem nested(P: Nat → Type): (xs: List<Nat>) → P(total(xs)) → Nat {
    λ xs => match xs {
        Nil => λ _ => 0,
        Cons(x, rest) => match rest {
            Nil => λ h => { let k: P(total([x])) = h; 0 },  // h: P(total(Cons(x, rest)))
            Cons(_, _) => λ _ => 0,
        },
    }
}
```

`h` keeps the type `P(total(Cons(x, rest)))` in the `Nil` arm, where
`rest` is `Nil`. With `match rest as λ r => P(total(Cons(x, r))) → Nat`
it checks. In `goes_single` the same shape first showed as a kernel
`NotConvertible` at the arm with no surface spelling: the elaborator
accepted the arm and the kernel refused the declaration.

Close relative: [[nested-match-on-field-binder-motive]] (closed
2026-08-17), whose fix rebuilt the constructor value around the abstracted
field for tier-0 arms. `List`'s `Cons` tail is the recursive field, which
that fix may not cover.

## Done when

The repro checks with no written motive, and `Target::goes_single` drops
its `as`.

## Log

- 2026-10-31: 2026-10-31: still fails after dependent-match-compiler slice 2. Standalone (rest a parameter, goal P(total(Cons(x, rest))) → Nat) it checks; inside the outer Cons arm it does not, so the outer arm's goal spells the tail some other way than Var(rest) (tier-2 List on W) and abstract_scrut finds nothing. A field_rewrap-style respelling for recursive fields is the likely fix.
- 2026-10-31: 2026-10-31: root cause traced (see match-clause-equations' log): the tail binder is a read of the W kids function, the goal spells supf(inj x; f'), and rebuilding the value around the abstracted tail needs Empty-domain η the kernel does not have. Shares its fix with eqbind-deep-pattern-kernel-rejects.
- 2026-11-01: Fixed by match-clause-equations (design §7.1). The repro checks with no motive (lib/_tests/std/data/list_tests.hthr tail_goal_refined). Target::goes_single no longer exists; the one library motive of this shape, decode_near_control's inner match on the tail (x86_64_block.hthr), is dropped instead.
