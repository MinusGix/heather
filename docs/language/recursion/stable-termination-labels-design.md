# Stable names for manual decrease proofs

Owner: `issues/stable-termination-obligation-names.md`.

## Source contract

Attach a label to the complete recursive call and discharge it at the end
of the declaration body:

```heather
fn down(n: Nat) -> Nat decreases n {
    match n { Zero => 0, Succ(k) => down(k) decreasing tail }
    on decreasing tail := nat::lt_succ_self(k);
}
```

`decreasing` is contextual postfix syntax. Parentheses make attachment clear
when calls nest: `down(k, down(k,0) decreasing inner) decreasing outer`.
For Result propagation, write `(parse(xs) decreasing tail)?`.

Labels are unique within one declaration, including its branches and nested
lambdas. Each member of a mutual group has its own namespace. A label must
attach to a saturated positional call to a member of the current measured
recursion. It cannot label an arbitrary expression or a nonrecursive call.
A label does not require a manual discharge: automatic local evidence and
the default closer remain available.

Ordinary holes and decrease labels have separate namespaces: `?tail` and
`decreasing tail` can coexist. Existing unlabeled calls still use `?decN`,
with the same traversal numbering. A labeled call uses its label instead of
an ordinal handle; naming one site does not stop it contributing to the
numbering of other calls. New clients should use labels wherever edits must
not retarget a manual proof.

Duplicate labels, multiple labels on one call, duplicate named discharges,
unknown named discharges, and labels on nonrecursive calls are errors.
Explicit proofs are checked against the labeled site's actual goal and
retain priority over automation.

## Lowering

The parser encodes a call label in an unspellable `#decreasing:` named-slot
key with an inert value. This is surface metadata: existing traversals,
module-image serialization, and Result propagation preserve its association
with the application. Measure lowering consumes it before ordinary argument
elaboration. It is not a callable parameter or an additional kernel term.
Isolated local type queries strip this metadata before inferring the call.

The corresponding `on` uses an unspellable goal key in the same private
namespace. The ordinary obligation lifter carries the discharge into the
selected call's proof declaration. Generated declaration names remain
ordinal implementation details; source proof selection uses the stable key.
The recursion representation, rank arithmetic, and kernel gate are unchanged.

## Validation

`stable_termination_labels.rs` covers inserted and reordered independent
calls, nested calls, mutual groups with open element types, Result
propagation, ordinary same-spelled holes, label diagnostics and false proofs
that fit another site's goal. Existing numbered-discharge, unfolding, and
calculator tests remain acceptance gates.

Focused elaborator acceptance: **39 passed, 0 failed**. The generated
Tree-sitter grammar, keyword inventory and highlighting are updated; all
**9 editor corpus cases pass**, including a named decrease proof. Syntax
acceptance also covers nested attachment and malformed label forms.

Full `scripts/test`: **2666 passed, 0 failed, 5 ignored**. Tracker and
whitespace checks pass.
