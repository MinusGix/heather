---
title: Infer equality types from an available endpoint when the other needs checking
status: closed
labels: [frontend,elaboration,inference,proofs,ergonomics]
created: 2026-09-14
updated: 2026-09-21
---



## Reproduction

Found while extending [[callback-expected-type-propagation]] acceptance.
With `result`, `option`, and `list` imported, this direction checks after
that application fix:

```heather
fn boxed<A,E>(r: Result<A,E>) -> Result<Option<List<A>>,E> {
    result::map(r, λ (a: A) => Some([a]))
}
theorem forward<A,E>(r: Result<A,E>):
    boxed(r) = result::map(r, λ (a: A) => Some([a])) { refl }
```

Reversing the endpoints fails on `[a]` needing an expected container type:

```heather
theorem reverse<A,E>(r: Result<A,E>):
    result::map(r, λ (a: A) => Some([a])) = boxed(r) { refl }
```

`expr.rs`'s `TyKind::Eq` path generally infers the left endpoint, then
checks the right against that type. The numeral-carrier exception does not
cover this callback application. Here the other endpoint could supply the
type, but the failed application is in inference position, so its expected
result is unavailable. A typed helper or the forward equation is a current
workaround.

## Scope and acceptance

- Choose a usable endpoint to supply the equality's type when the other
  requires checking. Both equations above should check with open types and
  a neutral receiver.
- Preserve the endpoints' written orientation in the emitted `Id`; this
  issue does not insert `sym` or change elimination rules.
- Preserve numeral-carrier behavior and standalone inferable lambdas.
- Refuse incompatible endpoint types and a false equation; retain an
  actionable error when neither endpoint supplies a type.
- Isolate failed inference attempts so goal state, names, diagnostics, and
  generated declarations cannot leak between attempts. Avoid indiscriminate
  duplicate elaboration of every ordinary equality; justify the selection
  policy and exercise the existing equality clients.

## What it assumes from elsewhere

- **[[callback-expected-type-propagation]]** owns checking callbacks once an
  application has an expected result; assumed here: supplying that result
  makes the callback in this repro check.
- **[[equality-orientation-ergonomics]]** owns broader proof-consumer symmetry;
  this issue is only endpoint type inference and keeps oriented `Id` intact.

## Log

- 2026-09-21: LANDED. Equality lowering now gives a left endpoint containing
  a checking-only form a cheap syntactic classification before doing any
  extra work. Only in that class does it use the existing isolated cloned
  inference probe: if the left cannot anchor and the right can, it infers the
  right and checks the left at that carrier. The constructed `Id` retains the
  written `(left, right)` order. If either premise is absent, the old
  left-to-right path runs and retains its diagnostic. This accepts both the
  issue's reversed annotated-callback example and the motivating parser-style
  generic call `([xs]).flatten() = xs`, where the collection-literal receiver
  was deferred behind the call's unsolved type argument. Controls retain
  incompatible endpoint rejection, kernel rejection of a false equation, the
  old error when neither endpoint anchors, and numeral-carrier behavior.
  Tests: `crates/elab/tests/equality_endpoint_checking.rs`,
  `callback_expected_types.rs`, `carrier_numerals.rs`, and `lib_algebra.rs`.
