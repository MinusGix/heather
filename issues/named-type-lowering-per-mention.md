---
title: A named type was lowered again at every mention
status: closed
labels: [elaboration,performance,inductives]
created: 2026-10-12
updated: 2026-10-12
---

Found 2026-10-12 while attributing `field_high_certifies`, the fast lane's
heaviest test ([[suite-iteration-chokepoints-2026-10]]).

## What was found

`Elaborator::lower_named` lowered a declared type's whole structural encoding
(`lower_instance`: the Σ/Sum/Wf spine, every field type, recursively) at
**every mention** of its name. `Instruction` is a large Sum of records whose
fields name `Gpr`, `BitVec(n)`, … again, and `StructuredCode` is built over
it, so a declaration whose signature only names `StructuredCode` twice spent
most of its time lowering it. A probe of 800 such one-line declarations
(cloud box, debug build): `fn s(x: StructuredCode) → StructuredCode { x }`
went from 6.0 to 1.6 ms each, `Instruction` from 2.7 to 0.37 ms.

The generated certificates gain less than that suggests: `field_high`'s own
module went from 65.7 to 60.1 s of item time (decl_type 5.5 → 3.0 s). End to end,
`field_high_certifies` is unchanged within noise (A/B in
[[suite-iteration-chokepoints-2026-10]]). Its
cost is spread over the kinds of declaration the structured generator writes
per node (`decodes`, `correct`, `graph`, `byte_length`, `preserves`, …, none
past an eighth), and is dominated by the kernel gate and by elaborator `whnf`
of the computed-from-code types, not by lowering
([[suite-iteration-chokepoints-2026-10]] has the ranking).

## What changed

- **A per-elaborator memo** (`named_type_memo`), for a bare (no type or
  value arguments) declaration from a *finished* module, keyed by the
  declaration's `Rc` address and `in_generated()`. Not memoized: the current
  module's declarations (a later declaration can still change what a field
  name resolves to), a use site with class dictionaries, a meta environment or
  inside a quotation, and any result that is not closed over the locals.
- **A hit is weakened past the globals committed since** (`shift_global` by
  the Ψ growth, and the entry re-stored at the new length): Ψ is de Bruijn, so a type lowered when Ψ had `n` bindings
  names its globals one index short for each declaration committed after. The
  first memo cut missed this, and the kernel caught it as "`DecodedInstruction`
  where a type that displays the same is expected" in `x86_64_fetch`
  (`u1268` vs `u1269`: the `≤` in `valid_length`). A hit after Ψ shrank (a
  rollback the module/session clears did not cover) re-lowers.
- **Field types no longer see the use site's binders or `let` aliases**
  (`lower_ctor`: the inherited names are renamed out of reach, the aliases
  cleared before the value parameters are pushed). A pre-existing hygiene
  bug, and the one thing that made a bare lowering depend on where it was
  written:

  ```
  fn y() → Nat { 3 }
  record R { x: Nat, p: x = y() }
  fn f(y: Nat → Nat, r: R) → r.x = 3 { r.p }   // refused: `y()` read as the parameter
  ```

  With a memo, which reading won would have depended on which mention came
  first. Regression test:
  `inductive_tier0::a_field_type_does_not_see_the_use_sites_binders`
  (with a negative control).
- Cleared wherever `result_only_memo` is (module delta replay and commit,
  session rollback).

Verification: a whole-`lib` check with every hit cross-checked against a
fresh lowering (`HEATHER_MEMO_CHECK`, a probe since removed) reported no
mismatch.

## Left

- A hit still pays one `shift_global` traversal of the whole type per new Ψ
  length, i.e. about once per declaration (the probe's remaining 0.2 ms type
  phase). Storing the lowering Ψ-relative to the declaring module would make
  hits free; not worth it until a profile says so.
- The current module's own declarations are never memoized, so the library
  module that declares `Instruction` (`x86_64`) gains nothing.
