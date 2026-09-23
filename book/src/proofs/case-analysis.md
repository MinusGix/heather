# Case analysis and calculation

## `match` as elimination and induction

`match` eliminates an inductive value. For recursive types, a recursive
function or theorem obtains induction hypotheses through the same syntax; no
separate `induction` keyword exists.

```heather
theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k) => cong_succ(add_zero(k)),
    }
}
```

The expected goal is used to synthesize a dependent motive when possible. Add
`as λ z => T` when you need to state the motive explicitly.

## Statement-position `split`

Inside a block, `split` is a vertical spelling of the same match:

```heather
theorem choose(b: Bool): P(b) {
    split b;
    on False := false_case;
    on True := true_case;
}
```

The `on Constructor(...) := ...;` lines here are branches, not goal
discharges. They are parsed into one ordinary `match`. `split h : value;`
adds an equation binder just like the expression form.

## Decidable branching

```heather
if P {
    proof_when_P
} else {
    proof_when_not_P
}
```

This resolves `Decide<P>` and matches on its `Or<P, ¬P>` result. `if let`
performs positional pattern matching with an else branch. Neither construct
adds a kernel rule.

## Equational `calc`

```heather
calc {
    start
        = middle := first_step,
        = finish := second_step,
}
```

The chain proves `start = finish` and desugars to right-nested transitivity
with explicit endpoints. A one-step chain is its proof. Step proofs can be
`refl`, theorem calls, holes, or any other expression of the required
equality.

Homogeneous relation chains use `≈`:

```heather
calc {
    a ≈ b := hab,
      ≈ c := hbc,
}
```

The selected relation and its transitivity support come from the surrounding
relation setup. Do not mix `=` and `≈` within one chain.

## Finite exhaustive goals

```heather
split_all;
all_goals { refl }
```

This pair case-splits every local whose type is a finite, non-recursive,
non-indexed inductive, then checks the same body independently at every leaf.
Recursive and indexed locals are left alone. The generated tree is ordinary
nested `match` syntax after elaboration.
