# Tactic reference

Heather does not have a separate tactic language. The forms below are proof
expressions recognized in checking position; their result is an ordinary term
checked by the kernel. Names are contextual and normally yield to a local or
user declaration of the same name.

## Quick reference

| Form | Purpose | Requirements |
|---|---|---|
| `refl` | Definitional equality | Goal is `a = b`; kernel conversion proves it |
| `{}` | Try `refl`, otherwise leave a goal | Any checking position |
| `decide` | Prove a decidable proposition by reflection | `import logic;`, a `Decide<P>` instance |
| `omega` | Certified linear arithmetic | `import omega;` and its dependencies |
| `rel_cong(h)` | Lift a relation proof through the goal's context | Relation infrastructure and compatibility evidence |
| `rel_derive` | Derive function compatibility from its expression | Relation infrastructure; may raise compatibility goals |
| `rel_derive(h)` | Derive a pointwise relation using supplied input evidence | Same |
| `split_all; all_goals { p }` | Exhaust finite locals, run `p` at each leaf | Finite non-recursive, non-indexed locals |
| `absurd(p)` | Eliminate an impossible constructor equality | `p` equates distinct constructors |
| `trivial` | Construct `True` | Goal is `True` |

Holes (`?g`) and `on` discharges are goal management rather than tactics;
`match`, `split`, `calc`, `apply`/`give`, and sequents are syntax that composes
proof expressions.

## `refl`

`refl` constructs equality reflexivity and asks kernel conversion to compare
the endpoints. It can close computed equalities. It does not prove arbitrary
true propositions or equalities that need induction or a lemma.

## `decide`

At a goal `P`, `decide` resolves `Decide<P>` and constructs the library's
proof-by-reflection term. It is best for closed or sufficiently reducible
goals:

```heather
import logic;
import nat;

theorem small_order(): nat::Le(2, 5) { decide }
```

A false closed goal is rejected by the kernel. An open goal may be too
symbolic to reduce even when an instance exists. `decide<P>()`, with
parentheses/type arguments, remains the ordinary library function; the bare
checking-position name is the tactic.

## `omega`

`omega` reconstructs a certificate for supported Presburger-style natural
and integer arithmetic, then parses and checks that certificate at the
original goal:

```heather
import omega;

theorem bounded(a, b: Nat, h: a <= b): a < Succ(b) { omega }
```

It handles supported linear equalities, inequalities, disequalities, and
logical structure. Non-linear multiplication, unsupported functions, or
missing hypotheses can make it report that it got stuck. The implementation
is untrusted automation: the generated proof still passes through ordinary
elaboration and the kernel.

## `rel_cong`

```heather
theorem mapped(x, y: A, h: x ≈ y): f(x) ≈ f(y) {
    rel_cong(h)
}
```

`rel_cong(h)` searches the source and target expressions in the expected
relation goal for a context surrounding the supplied relation proof. It then
uses registered compatibility evidence for functions crossed by that
context. Missing evidence appears as a goal such as `?compatibility`, which
can be discharged with `on`.

## `rel_derive`

Bare `rel_derive` proves a `PreservesRelation`-style goal by comparing two
symbolic inputs through the function expression. `rel_derive(h)` is the
pointwise version when an input relation proof is already available. It
composes known compatible functions and raises goals for unknown branch or
operation compatibility.

```heather
theorem compatible<A>(f: A -> A): PreservesRelation(same, same, f) {
    rel_derive
}
```

## Choosing a tactic

Use `refl` for computation, `decide` for a proposition with a reducing
decision procedure, and `omega` for symbolic linear arithmetic. Use
`rel_cong` when you already have a relation proof to lift through a context;
use `rel_derive` when the goal asks for compatibility of a function itself.
Use explicit `match` for meaningful induction and `split_all` only for a
genuinely finite exhaustive proof.
