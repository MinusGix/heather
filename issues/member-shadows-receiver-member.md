---
title: A member under declaration shadows the same-named member reached through a receiver
status: closed
labels: [frontend,elaboration,traits,ergonomics]
created: 2026-09-18
updated: 2026-10-15
---

Declaring a member whose body reaches the same-named member of another type
through a receiver is refused: `fn S::len(self s: S) → Nat { s.chars.len() }`
reports "`len` here is both `List::len`, reached through the receiver's type,
and a name in scope on its own". The name in scope is the member *being
declared*. Both `bounded_list` (`bounded_len`) and `string`
(`string_len`, [[string-char-spec-types]]) dodge it by delegating to a
plain function, which is a wacky shape to copy into every wrapper record.

Inside `fn T::m`, a receiver call `x.m()` at a receiver whose type is not
`T` should resolve to the receiver's member without consulting the
declaration under construction — the declared member cannot apply to a
receiver of another type, so there is nothing ambiguous. Likely one check in
the receiver-dispatch route (`docs/language/classes/traits-receiver-dispatch-design.md`,
`docs/language/classes/imported-receiver-dispatch-design.md`); remove the two delegations when
it lands.

- 2026-09-22: Landed the carrier check in nominal member dispatch. The
  in-progress declaration's subject type is read from its already-elaborated
  telescope in the prefix where that type is scoped. A known-different outer
  carrier removes only that self-reference from the competing readings;
  equal or unknown carriers stay ambiguous, as do every local, alias and
  committed global. `type_members` pins both halves and retains the existing
  cross-module ambiguity controls. The two library delegations are no longer
  required and can disappear with their surrounding API refactors.

## Log

- 2026-10-15: Residue: [[self-name-shadows-dot-call]]. The carrier check misses a member whose first explicit parameter is a proof (implicit endpoints), so `Rat::mul_le_mono_r` still clashes with `Int::mul_le_mono_r` in its own body.
