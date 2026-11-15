---
title: A value-parameterised constructor does not fix an implicit from its field
status: closed
labels: [elaborator,inference,diagnostics]
area: language
created: 2026-10-21
updated: 2026-10-21
---

Found while writing the float rounding laws (`lib/std/num/float/round.hthr`,
`Float::Le`). `Float(F)` is an inductive with a value parameter whose `Fin`
constructor carries `f: Finite(F)`. With `fn Float::Le({F: Format}, a, b:
Float(F))`, the type

```
Float::Le(Float::Fin(f), Float::Fin(g))      // f, g: Finite(F)
```

is refused with "cannot infer the value argument(s) of `Float` here — a
value parameter appears only inside a field's type". But the field's type
does determine it: `f: Finite(F)` fixes `F` once the constructor argument is
checked. The same refusal hits `Float::Le(Float::Fin(d), Float::Inf(b, hm))`
inside a match motive. It goes through when an earlier argument already has
the type (`Float::Le(r, Float::Inf(…))` with `r: Float(F)`) or with the
implicit named: `Float::Le(F := F, a := Float::Fin(f), b := Float::Fin(g))`,
which is what the library and `lib_std_float_round.rs` write today.

Two asks:

1. Infer the parameter from the constructor's field arguments when nothing
   else fixes it (elaborate the field against `Finite(?F)` and read `?F`
   off the argument), as for an ordinary function call.
2. The diagnostic's suggestion `Float::Le<…>(…)` is itself refused ("takes
   no type arguments") for a value implicit; it should suggest the named
   form `F := …`.

Related: `record-types-as-type-valued-functions.md` and
`record-partial-application-under-inferred-callee.md` hit the same message
in record positions.

## Resolution (2026-10-21)

Both asks done. `infer_ctor` hands value parameters to `infer_ctor_values`
(`crates/elab/src/constructor.rs`): the constructor's payload is lowered with
the parameters as scratch-world metas and each field type is unified with its
argument's through the call path's `unify_arg_ty`, then the construction is
built at the solution by the checking route
(`docs/language/surface-value-parameters.md` §4.1). `Float::Fin(f)` and
`Float::Inf(b, h)` both infer, so the four `Float::Le(F := F, …)` spellings in
`lib/std/num/float/round.hthr` and the one in `lib_std_float_round.rs` are plain
now. The call note for an unpinned value implicit suggests `name(F := …, …)`
instead of `name<…>(…)`. Tests: `crates/elab/tests/inductive_value_parameters.rs`
§7 (field of another value-parameterised type, a proposition field, literal and
open parameters, nested construction, records, an open element type, a
child-only constructor, tier 2, and three negative controls).
