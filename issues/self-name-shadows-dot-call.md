---
title: A lemma's own name makes a same-named dot call on another carrier ambiguous
status: closed
labels: [frontend,elaboration,ergonomics]
created: 2026-10-15
updated: 2026-10-20
---

Found moving `lib/std/rat.hthr` to implicit endpoints (PR #42, 2026-10-15).
Inside the body of

```heather
theorem Rat::mul_le_mono_r({x, y, z: Rat}, h: x <= y, hz: Rat::zero() <= z): x * z <= y * z {
    …
    let scaled = (a * q).mul_le_mono_r(c * p, e * r, h, omega);   // a, q: Int
```

the dot call is refused as ambiguous (a residue of
[[member-shadows-receiver-member]], whose fix keys on the subject's carrier): "`mul_le_mono_r` here is both
`Int::mul_le_mono_r`, reached through the receiver's type, and a name in scope
on its own". The other reading is the theorem's own name. While its first
parameter was `x: Rat`, receiver-member resolution discarded it, because its
subject carrier (`Rat`) differs from the receiver's (`Int`)
(docs/receiver-member-resolution-design.md §2). With the endpoints implicit,
the subject is the first explicit parameter `h: x <= y`, whose carrier is not
known, so the ambiguity stays.

The workaround is the qualified call `Int::mul_le_mono_r(a * q, …)`. It is
needed exactly where a `Rat` lemma uses the `Int` lemma of the same name, which
is the common case for a carrier built on another.

Possible fixes, to decide:

- A subject whose type is a proposition about other values (`Rat::Le(x, y)`,
  an equation) cannot be an `Int` receiver; treat its carrier as known and
  distinct.
- Or drop the declaration's own name from the ambient readings of a dot call
  inside its body when the call's receiver could not be its subject.

## Acceptance

- The body above checks with the dot spelling, and `rat.hthr` drops its
  qualified `Int::mul_le_mono_r`/`Int::mul_lt_mono_r` calls.
- A real ambiguity (an ambient function whose subject could take the receiver)
  is still reported.

## Log

- 2026-10-20: Fixed: the subject test widens from "known carrier differs" to "every type the subject's type can reduce to is disjoint from the receiver's carrier" (`subject_excludes`, docs/receiver-member-resolution-design.md §2). A closed definition is read at its own parameters, `case`/`elim_Nat` stuck on a neutral are read branch by branch (an `elim_Nat` recursive result adds nothing), Π/universe/equation/Unit/Empty are disjoint from every carrier; anything else declines. Applies to the self-reference, committed globals and locals alike. `rat.hthr` spells both main scaling calls as dot calls (the two at a literal `0` receiver stay qualified, since a bare `0` receiver defaults to `Nat`); `type_members` pins three positives and two negative controls (a family with a `Nat` branch, a local family `F: Nat -> Type`).
