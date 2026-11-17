# Classes, instances, and operators

## Classes

A class is a parameterized record registered for instance search:

```heather
class Monoid<A> {
    unit: A,
    op: A -> A -> A,
}
```

Classes may extend parents and may tag parent paths when the same ancestor
appears more than once:

```text
class Ring<A> extends AddMonoid<A> as additive,
                      MulMonoid<A> as multiplicative { ... }
```

A class may also be indexed by values:

```text
class Monoid<A>(op: A -> A -> A) { ... }
```

## Instances

An instance may define members in a declaration block:

```heather
instance Monoid<Nat> {
    fn unit() -> Nat { 0 }
    fn op(x: Nat, y: Nat) -> Nat { add(x, y) }
}
```

Or assemble the class record from existing values:

```heather
instance Monoid<Nat> {
    unit := nat::zero,
    op := nat::add,
}
```

Generic instances use `<A>`; value-generic instances put implicit value
binders immediately after `instance`. `requires` adds solver-filled evidence:

```text
instance<A> Monoid<List<A>> requires ma: Monoid<A> { ... }
instance(n, m: Nat) Decide<Le(n, m)> { ... }
```

Resolution searches local evidence before the global registry. A named
solver parameter may be passed explicitly as a named argument, or all value
implicits may be exposed with `@`.

## Receiver dispatch

A parameter marked `self` chooses the argument filled by method notation:

```heather
fn cong(f: A -> B, self p: x = y): f(x) = f(y) { ... }
```

Then `p.cong(f)` supplies `p` at that position. Class and record members also
participate in receiver dispatch based on the receiver's type.

## Operator designations

```heather
designation + at Nat := add
designation<A> ++ at List<A> := append
designation prefix - at Int := neg
```

A designation tells the resolver what an operator means at a carrier. Prefix
and infix slots are separate. The designated operation is a bare global name;
ordinary implicit inference instantiates it at the use site.

The operator itself is a value when it is written alone in parentheses, as in
Haskell: `(<=)`, `(+)`, `(++)`. It means what the designation at the carrier
its position asks for says, so at a list of bytes `(<=)` is
`BitVec::unsigned_le`:

```heather
theorem sorted(s: List<u8>): s.SortedPerm((<=), s.insertion_sort((<=))) {
    s.insertion_sort_correct(BitVec::unsigned_le)
}
```

The carrier comes from the parameter's type, which a receiver or an earlier
argument has to have fixed: `List::insertion_sort((<=), [3, 1, 2])` has none
yet when the symbol is read and is refused. Directly between an argument
list's delimiters the parentheses may be left off, `xs.foldl(+, 0)`. `(-)` is
subtraction; to fix one operand, write an argument slot, `· <= 10`.

An operation binder can install a local symbol in its own scope:

```text
fn associative<A>(op as ∙: A -> A -> A, a, b, c: A): ... { ... }
```

## Big operators

`∑ k < n, e` is the sum of `e` over the indices `0, 1, …, n - 1`, and
`∏ k < n, e` the product. Both are spellings of one fold from
`std/algebra/big_operator` (`import big_operator;`):

```heather
theorem nat_sum_four(): ∑ k < 4, k = 6 { refl }
theorem factor<A: Semiring(≈, +, *)>(c: A, n: Nat, f: Nat → A): c * ∑ k < n, f(k) ≈ ∑ k < n, c * f(k) {
    Semiring::mul_range_l(c, n, f)
}
```

The index is a `Nat`. The sum is taken under whatever `+` (or `*`) the body's
carrier designates, so the same notation sums naturals, rationals, Cauchy
reals, or an open semiring's elements, and every law in the module (splitting,
reindexing, Fubini, distributivity, the triangle inequality) applies to it.
The body is an arithmetic expression running as far right as one can, and it
stops at a relation: `∑ k < n, f(k) + 1` sums `f(k) + 1`, while in
`∑ k < n, f(k) ≈ s` the sum is the left side of `≈`. Parenthesise the sum to
add something after it: `(∑ k < n, f(k)) + f(n)`.

## Precedence summary

From tighter to looser among value operators: prefix `-`; `*`, `/`, `%`, `∙`
and `⊓`; `+`, `-`, `++`, and `⊔`; `<<` and `>>`; `&`; `|`; `&&`; `||`;
comparisons. `++` is right-associative;
ordinary arithmetic operators are left-associative. `<`, `<=`, `=`, and `≠`
form a single non-associative comparison level and cannot be chained.
