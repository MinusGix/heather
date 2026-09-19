# Constructors as function values

Tracking issue: `issues/constructors-as-function-values.md`. Prerequisite:
`docs/surface-function-types.md` (a function *type* must be writable before a
constructor can be checked against one). Read §4 of
`docs/inductive-tier0-lowering.md` alongside §3 below — the constructor
lowering is unchanged by this round, only the position it is invoked from.

---

## 1. What is missing

An ordinary global is a function value; a constructor is not.

```heather
fn twice(f: Nat -> Nat, n: Nat) -> Nat { f(f(n)) }
fn inc(n: Nat) -> Nat { Succ(n) }

twice(inc, 0)              // ok
twice(Succ, 0)             // error: unbound name `Succ`

inductive Box { Wrap(Nat) }
fn ap(f: Nat -> Box, n: Nat) -> Box { f(n) }
ap(Wrap, 1)                // error: `Wrap` takes 1 argument(s), found 0
```

Two independent causes, and they want two independent fixes:

1. **`Succ` is not a name.** `resolve` special-cases `Zero` and nothing else;
   `Succ` exists only as the *applied* form matched at the top of
   `elab_infer`'s application arm. `Zero` works bare because it needs no
   arguments — it is a value, not a special case of a function.
2. **A declared constructor is saturated-only.** The bare-constructor checking
   arm calls `build_ctor` with an empty argument list, which is an arity error
   against an expected `Π` rather than an η-expansion.

---

## 2. The scheme

**η-expand the constructor at the expected type.** A constructor is not a
kernel value in any tier — tier 0 makes it an injection into a sum of Σs, tier
1 wraps that in `sup_f` — so there is nothing to *pass*; the function value has
to be built, and the only place its domains can come from is the type checking
it. So the rule is: one λ-binder per missing argument, peeled off the expected
`Π`, with the saturated constructor underneath.

```
C(a₁ … a_j)  ⇐  Π(x_{j+1} : A_{j+1}). … Π(x_m : A_m). D
    ⇝  λ x_{j+1} … λ x_m. ⟦C(a₁ … a_j, x_{j+1} … x_m)⟧ at D
```

Three consequences worth stating, because they are what make this small:

- **The saturated builder is untouched.** `build_ctor` is called exactly as it
  is today, at `D` — the codomain reached after peeling — with a longer
  argument list. Every tier distinction (`sup_f`, the children tuple, the
  container tail) lives inside it and needs nothing from this round.
- **The extra arguments are *surface* variables, not terms.** Each peeled
  binder is pushed into the elaboration context under an unspellable `#`-name
  and the corresponding argument is `Var("#argₖ")`. So the fields are still
  elaborated by `build_fields`/`build_children` in checking position against
  the encoding, exactly as a user-written `C(…, x, …)` would be.
- **Partial application is the same feature.** `Cons(1)` against
  `List -> List` is `j = 1, m = 2`; nothing distinguishes it from the bare case
  except where the argument list starts. It lands here, not later.

### 2.1 `Succ` as a value

Two lines in `resolve`, next to `Zero`, and no expected type needed:

```
Succ  ⇝  λ(n : Nat). Succ n   :   Π(_ : Nat). Nat
```

This is *inference*, not checking, which matters more than it looks: an
argument to a callee with implicit parameters goes through `elab_infer`
(`apply_implicit` drives its meta solutions off the argument's inferred type),
so `p.cong(Succ)` — the exact spelling `issues/surface-operators.md` deferred —
is fixed by this half and not by §2's.

Like `Zero`, this is checked before locals and aliases, so a binder named
`Succ` does not shadow it. That is not a considered position, it is
consistency: `Succ(x)` in the application arm already ignores shadowing. If
either becomes shadow-aware both should, together.

### 2.2 Why this cannot mis-lower

`docs/inductive-tier0-lowering.md` opens by naming the hazard class this
module has to stay out of: a bug that produces a *checked theorem about the
wrong type* rather than a rejection. The η arm stays out of it structurally:

- the built term's type is `Π(A_{j+1}) … Π(A_m). D` **by construction**, since
  every domain is the one peeled off the expected type and `D` is the expected
  codomain — the arm cannot silently produce a function of some other type;
- the fields' annotations continue to come off `D`'s encoding, not off the
  peeled domains, so a domain that disagrees with its field yields a `Pair`
  whose `fst_ty` says one thing and whose `fst` is a variable of another —
  ill-typed, and the kernel rejects the enclosing declaration.

That last point is the elaborator's standing doctrine (`elab_check`: the
mismatch "is caught by the kernel's final check of the declaration … errors
cannot slip through, only be reported later"), so the η arm does **not** grow
a conversion check of its own. Deviating would mean duplicating conversion at
one arbitrary site.

The one case that needs a real diagnostic is arity: an expected type with
fewer `Π`s than the constructor has missing fields. There, peeling stops on a
non-`Π` and the message says how many were provided versus needed, rather than
falling through to `build_ctor`'s "found 0".

### 2.3 The tiers come along

Nothing in the arm is tier-aware, and both tier-1 shapes work because the
synthetic argument is a surface expression:

- a **plain child** (`Node(Leaf)` at `Tree -> Tree`) becomes `Var("#arg")`
  checked against `⟦D⟧` by `build_children` — the same path an open child
  already takes;
- a **container** (`Node(0, 1)` at `[Rose; 1] -> Rose`) becomes `Var("#arg")`
  checked against `Vec(⟦D⟧; len)`, where `len` is still projected out of the
  label just built. A vector *literal* is checking-only, but a vector-typed
  variable is not, so the container tail needs no special case.

A **dependent** expected type is likewise free: the codomain is used under the
binder just pushed, so `Π(n : Nat). [Rose; n] -> Rose` peels correctly.

---

## 3. What stays rejected

| Written | Message |
|---|---|
| an *unsaturated* declared constructor in inference position (`let f = Wrap;`) | today's arity/ambiguity error, unchanged — but see §5.1: re-applied to saturation (`Cons(1)(xs)`) it works |
| `Cons` where `Nat -> List` is expected | "`Cons` needs 2 more argument(s), but the expected function type provides only 1" |
| `Wrap` where a non-function, non-`Box` type is expected | today's "`Wrap` is a constructor of `Box`, which is not the expected type here" |
| a domain that disagrees with the field it fills | a kernel rejection of the declaration (§2.2) |

One row that *looked* like it belonged here does not: `D(v̄)` where a
**universe** is expected is not a constructor at all. No constructor inhabits
`Type`, so the expected type selects the declared *type former* instead, by
the same disambiguator this round established and pointed the other way
(`docs/record-type-values.md`, landed 2026-08-01). Nothing in §2 changes — the
universe arm runs before the constructor arms and always did.

The first is the one to justify. Inferring a constructor's function type means
building its field telescope as a `Π` — walking the Σ spine of `⟦cᵢ⟧`, and for
tier 1 rebuilding the child and container types outside `build_children` —
which is a second, independent copy of the lowering's knowledge of field
layout. That is precisely the duplication the tier-0 doctrine ("one function
per numbered rule, annotations read off the type being eliminated") exists to
forbid. It also cannot work for a parameterized declaration, where the type
arguments are monomorphized rather than inferred (§2 there). `Succ` escapes
this only because its type is a constant.

So: constructor-as-value needs a checking position. Every position the
motivating examples occupy is one — `apply_explicit` checks each argument
against the parameter's domain — with the single exception of an argument to a
callee that has implicit parameters, which `apply_implicit` *infers*. That gap
is real and stays open; it is a symptom of `apply_implicit` inferring where it
could check, which belongs to `issues/elab-unifier-completeness.md`.

One last boundary, drawn after this round: the universe row above extends
**one arrow further in** as of 2026-09-19. A record type partially applied
against an expected `Π` whose *ultimate* codomain is a universe η-expands over
its remaining **value parameters** rather than over the constructor's fields
(`docs/record-type-partial-application.md`). That arm, like the universe arm,
runs before the constructor arms, and it declines wherever the spine ends at
the record itself — which is every case §2 owns, the partial application of
§5.2 included.

---

## 4. Acceptance checklist

Every positive item is elaborated and then re-checked by the real kernel.

1. `twice(Succ, 0) = 2` by `refl`, and `Succ` bare at an annotated
   `Nat -> Nat`.
2. η holds against the builtin: `(λ (x: Nat) => Succ(x)) = Succ` by `refl`.
3. `p.cong(Succ)` — the deferred spelling — with `cong` taking `f` explicitly
   and its endpoints implicitly.
4. `ap(Wrap, 1)` for a declared tier-0 `Box`.
5. Partial application: `Cons(1)` at `List -> List`, with
   `Cons(1)(Nil) = Cons(1, Nil)` by `refl`.
6. A parameterized declaration at a checking position: `Some` at
   `Nat -> Option<Nat>`, and the *same* constructor at `Bool -> Option<Bool>`
   in one file (the type arguments come from the expected type, so both work
   and neither infers).
7. Tier 1, plain child: `Node(Leaf)` at `Tree -> Tree`, applied.
8. Tier 1, container: `Rose`'s `Node(0, 1)` at `[Rose; 1] -> Rose`, applied.
9. A dependent expected type: `Node(0)` at `(n: Nat) -> [Rose; n] -> Rose`.
10. Each §3 rejection, with its message asserted — including the negative
    control that a *wrong* domain (`f: Bool -> Box` filled with `Wrap`) is
    rejected rather than mis-lowered.
11. The whole existing suite still passes.

Landed as `crates/elab/tests/constructor_values.rs`, nine tests, one per item
above (4.8 and 4.9 share one, as do the §3 rejections).

---

## 5. What implementing it corrected

The scheme survived, and the two halves cost what they were quoted at — the
`Succ` entry is literally the two lines of §2.1, and the η arm is one loop.
One case was missing from it, and one claim in §4 was written without checking
that the surface can express it.

### 5.1 The curried spelling needed re-association, not a telescope

`Cons(1)(xs)` is not a constructor application at all as far as the elaborator
was concerned: it is an application *whose head is an application*, so
`as_named` gives `None` and it goes to inference on the head — which is
`Cons(1)`, exactly the unsaturated case §3 leaves rejected. So the checklist's
own item 5 (`Cons(1)(Nil) = Cons(1, Nil)` by `refl`) failed against the first
implementation, and the tier-1 analogue `Node(x)(x)` with it.

The fix is not the field telescope §3 argues against. A constructor's function
value *is* its η-expansion, so the curried spelling is definitionally the
saturated one, and flattening the spine — `ctor_spine` in `lib.rs`, which peels
nested `App` heads and concatenates the argument lists — makes the saturated
builder see them alike. Six lines, no new knowledge of the lowering, and it
lands in both modes: in checking position it feeds the η arm, and in inference
position it feeds `infer_ctor`, which now sees a saturated application and
succeeds where the head alone could not.

That is worth stating as the actual boundary, because it is narrower than §3
implied: **an unsaturated constructor needs a checking position only when it
stays unsaturated**. Re-applied to saturation it needs nothing, which is the
analogue of `add(1)(2) = add(1, 2)` from `docs/surface-function-types.md` §9.11
and the case a user is most likely to write.

### 5.2 Partial application can only drop *trailing* arguments

§2 says "nothing distinguishes partial application from the bare case except
where the argument list starts", which is true but reads as though any subset
of the fields could be left out. The surface has no spelling for that —
arguments are positional, so `C(a₁ … a_j)` fixes a *prefix* — and the η arm
appends the peeled binders to the end for the same reason. A test for "the
first field left missing instead of the second" was written and then deleted:
there is nothing to write.
