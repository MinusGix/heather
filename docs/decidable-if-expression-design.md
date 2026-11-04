# Decidable `if` expressions

## Decision

Heather's source `if` branches on a proposition with a `Decide` instance:

```heather
if a <= b { b } else { a }

if h : P {
    // h : P
    yes(h)
} else {
    // h : P -> False
    no(h)
}
```

The condition is a type-level proposition `P`, decided by its `Decide<P>`
instance. This keeps specification-level branching aligned with the existing
`Decide<P>` abstraction instead of exposing its `P ∨ ¬P` representation at
each call site.

**A `Bool` condition** (2026-11-02, issues/bool-conditions-and-literals.md):
`if b`, `if !b`, `if a && b` with Bool operands branch on that Bool. The
parser cannot tell the two apart, so it lowers both the same way and the
elaborator picks by the condition's type (`Elaborator::elab_condition`): the
proposition reading is tried first, and only when it fails is the condition
elaborated as a term; at `Bool` the scrutinee is that term itself, which is
what `decide_bit<b.IsTrue()>()` is by the `IsTrue` instance's `bit := b`.
With evidence, `if h: b` is `decide<b.IsTrue()>()`, so `h: b.IsTrue()`. A
condition that is neither is refused naming both readings. This is not a
`Bool`-to-proposition coercion in type positions generally: only the
parser's lowered `if`/`while` call (its head carries the condition's span)
takes it, and a written `decide_bit<b>()` still says `b` is not a type.

**A connective mixing the two** (2026-11-03,
issues/mixed-bool-prop-condition.md): when neither whole reading applies and
the condition is a connective (`∧`, `∨`, `↔`, a non-dependent `→`, `¬`, or
`&&`, `||`, `!` with a proposition operand), it is read on the proposition
side with each `Bool` operand as `b.IsTrue()`
(`Elaborator::mixed_condition`). `if b ∧ n = 0` decides
`b.IsTrue() ∧ n = 0`, whose bit is `b && n.same(0)` by the instances, and
`if h: b ∧ n = 0` gives `h: b.IsTrue() ∧ n = 0`. The proposition side was
chosen because it keeps evidence available. A `Bool` subtree is one operand
(`(a || b) ∧ n = 0` reads `(a || b).IsTrue()`), and the Boolean doubles
between a proposition and a `Bool` mean the connective they decide. `&&`
binds tighter than `=`, so `b && n = 0` is `(b && n) = 0` and never reaches
this reading; write `b ∧ n = 0` or `b && (n = 0)`.

`if` is a true grammar keyword and therefore cannot be used as a binding
name. Both branches are braced blocks, so local `let` statements are available
without introducing another branch-body syntax.

## Lowering and evidence

The parser lowers

```heather
if h : P { yes } else { no }
```

to the same match tree as

```heather
match decide<P>() {
    Inl(h) => yes,
    Inr(h) => no,
}
```

The two occurrences of `h` inhabit separate scopes and have types `P` and
`P -> False`, respectively. `MatchForm::If` is retained only as source
provenance for diagnostics; computation and dependent elimination continue
through the ordinary match implementation.

**The form without a binder matches on the decision's bit** (2026-10-02,
issues/native-frontend-decided-matches.md):

```heather
if P { yes } else { no }
// is
match decide_bit<P>() { True => yes, False => no }
```

`Decide<P>` carries `bit: Bool` and `reflects: Reflects(P, bit)` beside
`dec`, and lives in `bool` for that reason. At a resolved instance the
elaborator reads `decide_bit<P>()` as the instance's own bit
(`b.eq_bit(10)` for `b = '\n'`, `x || y` for `P ∨ Q`), the way a literal's
embedding is read. Why: matching on `dec` puts a match on a match (the
instance's own match on the comparison) under every `if`, and case-of-case
is not definitional, so a native step written with `if` could not be its
generated expansion by conversion, and `split_all` had to abstract the
comparison inside the instance's proofs. A match on the bit is the match a
step's code makes.

A proof about a function an evidence-free `if` defines cases on the bit:
`decide_bit_split<P>(M, yes, no)` gives each side its evidence
(`Int::le_max_l`).

Normal implicit resolution supplies `Decide<P>`. Consequently an explicit
local dictionary takes precedence in exactly the same way it does for a
direct call to `decide<P>()`. A failed search is reported at the `if` and
prints the written condition rather than the parser-generated call.

## Checking and inference

In a checking position the lowered match uses the existing dependent motive
synthesis. Branches can therefore establish results whose indices follow the
actual `Inl` or `Inr` decision, rather than being restricted to choosing two
values of a non-dependent type.

An `if` can also infer a constant result type. Elaboration tries a branch in
its proper evidence context, then accepts the inferred type only when it can
be strengthened back into the surrounding context without that evidence. It
checks both branches against that outer type. This supports direct expression
use and unannotated `let` bindings while preventing a branch-local proof from
escaping its scope. A genuinely evidence-dependent result still needs an
expected type, just as an otherwise ambiguous dependent match does.

## Standard-library use

`Int::max` and `Int::min` are the initial representative users:

```heather
fn max(a, b: Int) -> Int { if a <= b { b } else { a } }
fn min(a, b: Int) -> Int { if a <= b { a } else { b } }
```

Their `Decide<Le(a,b)>` instance is declared before these definitions because
Heather resolves declarations in source order.

## Boundaries

- This feature says nothing about efficient runtime compilation of arbitrary
  proofs; that remains the `Compile`/representation boundary.
- `if let`, `let else`, and pattern conditions are separate language designs.
- The syntax deliberately requires `else`; proposition branching has two
  evidence-producing cases and neither is silently discarded.

## Verification contract

Focused tests cover closed Nat decisions, equivalence with explicit matching,
both evidence types, dependent proofs, local dictionaries, block bodies,
constant-type inference, missing-instance diagnostics, and rejection of raw
`Bool` conditions. The Int library tests cover the representative standard-
library migration.
