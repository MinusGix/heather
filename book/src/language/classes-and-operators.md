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

An operation binder can install a local symbol in its own scope:

```text
fn associative<A>(op as ∙: A -> A -> A, a, b, c: A): ... { ... }
```

## Precedence summary

From tighter to looser among value operators: prefix `-`; `*` and `∙`; `+`,
`-`, `++`, and `⊔`; `&&`; `||`; comparisons. `++` is right-associative;
ordinary arithmetic operators are left-associative. `<`, `<=`, `=`, and `≠`
form a single non-associative comparison level and cannot be chained.
