# Expected types in annotated callbacks

`issues/callback-expected-type-propagation.md`.

## Diagnosis

`result::map(r, λ (a: A) => Some([a]))` was refused even when the enclosing
result specified `Result<Option<List<A>>, E>`. The lambda's domain annotation
made `is_checking_only` classify the lambda as inferable. The implicit
application engine therefore inferred its body while the callback's codomain
still contained an unsolved type parameter. `[a]` then failed before the
existing expected-result solving pass ran.

An annotated domain supplies the input type, not necessarily the output type.
An unannotated callback already used per-call deferral. The missing behavior
was scheduling the annotated callback through that same mechanism.

## Change

The application-specific argument classifier treats a fully annotated lambda
as preferring checking, with inference fallback enabled. This uses the
existing reserved argument slot, withheld state, expected-result solver and
retry loop; it adds no shared or cross-call metavariable world.

- If the parameter type is known when visited, check the callback immediately.
- Otherwise reserve its term, continue through later arguments, solve from
  the expected result, and check the callback when its type becomes known.
- If the callback itself must supply missing type information, use the
  existing inference fallback. An underconstrained checking-only body still
  reports its inference error; collection literals do not default to List.

The global `is_checking_only` predicate is unchanged: standalone annotated
lambdas and equality endpoints that can already infer retain that behavior.
Unannotated callbacks retain their existing rules. Binder annotations are
still checked against the expected domain, and the kernel validates emitted
terms as before. Comments on the shared deferral metadata now describe both
result-only calls and annotated callbacks.

## Client and boundary

The calculator pipeline laws now use:

```heather
calculate(ts).map(λ (n: Nat) => Some([n]))
```

Both qualified map and receiver syntax are acceptance cases, so method
selection is independent of this fix. The expected type reaches nested
constructors and collection literals without explicit map type arguments or
a `Some<List<Nat>>` annotation.

This mechanism needs an expected result or another argument to determine the
missing type, or a callback whose body can infer. A callback stored in an
unannotated let does not acquire a type from an unrelated later call.
Selecting the right endpoint as an equality's type source when the left
cannot infer is separately tracked by
`issues/equality-endpoint-checking-context.md`.

## Validation

`crates/elab/tests/callback_expected_types.rs` covers qualified and receiver
calls, an equality's checked endpoint, expected function results, later
arguments, nested constructors, multi-binder lambdas, open types, neutral
receivers, dependent codomains, captured locals, and inference fallback.
Controls reject underconstrained collections, incompatible lambda domains,
wrong element/container types, self-application, and a false equation.
The ordinary calculator acceptance checks the simplified pipeline laws.

Full `scripts/test`: **2652 passed, 0 failed, 5 ignored**.
The isolated `scripts/bench --check` gate reports seven Nat timing flags,
with no slope failures. The baseline is unchanged; observations and the
outstanding investigation belong to `issues/kernel-benchmark-nat-baseline-drift.md`.
