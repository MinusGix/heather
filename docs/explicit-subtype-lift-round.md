# An explicit lift written in Heather

The subsequent [packaging round](packaged-subtype-round.md) shortens the
showcase with a reusable representation record. The raw template interface
described below remains its implementation layer.

The [positive addition example](showcase/lift_positive.hthr) uses a named
Heather code template to construct its wrapper. The templates live in
[`lib/lang/subtype_code.hthr`](../lib/lang/subtype_code.hthr); no subtype-specific
construction rule lives in the compiler.

```heather
fn lifted_add(x, y: PositiveNat) -> PositiveNat {
    emit_code(lift_binary_code)(Nat, PositiveNat, λ n => 0 < n,
        λ z => z.value, λ n p => PositiveNat(n, p), add,
        λ a b => add_positive(a.value, b.value, a.valid), x, y)
}
```

The arguments say which values the representation contains, how to project
and construct it, which ambient operation to use, and why its result satisfies
the invariant. The template generates the constructor application and all
operand projections. Evidence remains ordinary relevant evidence in this
customer. No field names or implicit coercions are recognized specially.

`emit_code(name)` runs a visible `meta fn` with exactly one context parameter
and a `Code` result. Its code payload becomes an ordinary expression at the
use site, where its parameters are applied and checked normally. The compiler
rescopes the template to the current global context, evaluates it with the
existing fuel bound, and kernel-checks the emitted payload. It does not accept
arbitrary meta signatures, execute runtime code, or register new declarations
from inside a meta program. The surrounding `fn` or `theorem` names the result.
The two argument lists have different roles: template invocation and payload
application. The call-style lint preserves this boundary instead of suggesting
an invalid flattened call.

Generic type and value parameters live inside the quotation, following the
existing vector templates. Consequently this is template emission with
explicit ingredients, not yet reflection over the supplied operation's body.
It does not require opening addition's implementation: the closure proof is
its relevant interface for construction.

The companion `lift_binary_value_code` emits the projection proof. Besides
the same ingredients, it takes the representation's constructor law:

```text
project(pack(a, p)) = a
```

A constructor of the requested type need not preserve its argument. This
extra law is what connects the generated operation to the ambient operation.
For `PositiveNat` it is proved by `refl`. The generated theorem checks against
`lifted_add(x, y).value = x.value + y.value`. Associativity then reuses
`add_assoc` through the emitted wrapper, just as in the manual round.

Replacing the closure argument with `?closure` leaves an ordinary goal for
the closure function. An `on ?closure := ...;` clause supplies that function
and resumes checking. The generator does not silently add a caller premise.
Automatic closure discovery remains open; this round accepts explicit evidence.

The interface deliberately exposes the ingredients before packaging them into
a reusable representation record or inferring them. A future lift request can
assemble these same ingredients from a selected target signature. Automatic
theorem discovery, conditional signatures, law-instance assembly, squashed
evidence adaptation, and general dependent transfer remain separate work.

See [the design](smart-subtype-inheritance.md) and
[the implementation issue](../issues/explicit-subtype-code-template.md).

Validation: the final plain `furnace run -- scripts/test` passed with 2,374
tests passed, none failed, and 5 ignored. The ordinary CLI also checked the
showcase, with only existing unused-payload warnings in its library imports.
