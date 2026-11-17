---
title: "A generated `known` resolves to a declaration named `known`"
status: open
thread: Make compiler correctness proofs elegant
labels: [tactics,elaborator,hygiene,proofs]
area: tactics
milestone: [lang-proof-modularity]
created: 2026-11-17
updated: 2026-11-17
---

`known` is a tactic only where the name is not shadowed
(`checking.rs`, the `KNOWN` arm; `Elaborator::shadowed` counts a global).
The elaborator also writes it itself: `induct`'s default leaf for an arm left
out (`function_induction.rs`, `INDUCT_LEAF_DEFAULT`) and the tested forms in
`tested.rs`. Those are surface `Var("known")`, so where a declaration named
`known` is reachable under the bare name they are that declaration.

Inside a `List::` theorem the bare name reaches `List::known`
(`lib/native/function_ir/function_ir_pass.hthr`). `List::procedures_hosted`
in `lib/native/native_compile_correct.hthr` hit it: `induct
List::procedures_code(…)` with `Cons::None` left out was refused with

```
error: this has type `List<Fact> -> Nat -> Option<Nat>`, but `And<…>` is expected here
```

at the `induct` itself, naming neither the case nor `known`. The arm is
written `Cons::None => absurd(code)` there until this is fixed.

Reduced:

```
fn List::known(self xs: List<Nat>, id: Nat) → Option<Nat> { None }
theorem List::clash(self xs: List<Nat>, n: Nat, o: Option<Nat>, e: o = Some(n), f: o = None): n = 0 { known }
// error: this has type `List<Nat> -> Nat -> Option<Nat>`, but `n = 0` is expected here
```

A user who writes `known` under a declared `known` gets the declaration, which
is the ordinary rule. What the elaborator writes should not depend on the
module's names: give the generated leaf a spelling no user can write (as
`POS_SEARCH` is `__pos_search`) that the `KNOWN` arm accepts without the
shadow test, and use it at every generated site.

## Log

- 2026-11-17: filed from the `induct` adoption in `native_compile_correct.hthr`.
