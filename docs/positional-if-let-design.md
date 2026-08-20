# Positional `if let` V1

Positional `if let` is the expression-valued spelling of one interesting
pattern and one default:

```heather
if let Some(x) = value { use(x) } else { fallback }
```

It lowers to the same `ExprKind::Match` and the same pattern matrix as:

```heather
match value { Some(x) => use(x), _ => fallback }
```

There is no new eliminator and `else` is required. Both branches are ordinary
block expressions, and nested positional patterns use the existing deep-pattern
compiler. As with explicit `match`, its existing termination and indexed-field
restrictions still apply.

## Equation evidence

The optional name precedes the pattern:

```heather
if let hy : Some(x) = value { use(x, hy) } else { fallback }
```

Here `=` separates the pattern on its left from the scrutinee on its right; it
is not a literal type annotation. In the success block the inferred type is:

```heather
hy : value = Some(x)
```

This deliberately agrees with `match hy : value`: equations consistently run
from the original scrutinee to the constructor-shaped arm value. The parser
gives the underlying convoy equation an unspellable internal name and inserts
a local alias only in the success block. Thus the `else` block receives no
equation (and no negative match evidence), while the generated term remains
one ordinary equation-bearing match.

Equation evidence inherits the homogeneous identity boundary of
equation-bearing `match`: the unbound form works for indexed families wherever
an ordinary match does, but the named form is refused when constructor indices
would require heterogeneous equality. Such proofs should use an inversion
principle instead.

## Deliberate boundaries

- Constructor fields are positional. Named fields belong to
  `issues/named-patterns-by-field.md`.
- Negative evidence in `else` belongs to
  `issues/if-let-negative-evidence.md`.
- Irrefutable `_` is rejected because it makes the second branch unreachable;
  ordinary `let` is the appropriate construct.
- `let pattern = value else ...` and early-return forms are separate
  control-flow designs.

