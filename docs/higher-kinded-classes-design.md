# Classes over a type constructor

Status: **landed**, 2026-10-31. Tracking issue:
`issues/higher-kinded-classes.md`, round R2a of
`docs/sequencing-surface-design.md` (§2.1, §12). Probes:
`lib/_tests/std/core/type_constructor_tests.hthr`.

Three pieces, each small, and none of them a kernel change: a bare generic
name as a type constructor value, the unifier's `?M(A) ≟ D<…, A>`, and a
class whose parameter is a type constructor. With them,

```heather
class Bind<M: Type → Type> { bind: {A, B: Type} → M(A) → (A → M(B)) → M(B) }
instance Bind<Option> { bind := Option::and_then }
instance Bind<Tac> { bind := Tac::bind }

fn twice({M: Type → Type}, x: M(Nat), b: Bind<M> := infer, p: Pure<M> := infer) → M(Nat) {
    b.bind(x, λ n => p.pure(n + n))
}
theorem twice_tac() : twice(Tac::Pure(4)) = Tac::Pure(8) { refl }
```

checks, resolves at both carriers, and computes.

---

## 1. What the kernel already had

`<A>` parameters of an inductive are substituted at each use
(`docs/inductive-tier0-lowering.md` §2), so `Option<Nat>` is an inline
sum. But every tier-0 and tier-1 generic declaration also registers a
**code function** `D#tycode_fn : Π(A₁ : Ty 0)…. Ty l`
(`docs/per-instantiation-type-codes-design.md`), and `respell_ty` spells an
inline instance as `El(app(D#tycode_fn^δ; ā))`. That global *is* the type
constructor, as a kernel term of type `Type → Type`. Pieces 1 and 2 are
mostly a matter of using it.

Tier-2 declarations (on `W`, such as `Tac`) and codata register no code
function (`inductive.rs`: "Tier 2 names its leaf predicate and nothing
else"). For those the constructor is spelled as a λ, below.

## 2. A bare generic name is a constructor (piece 2)

```
D  ⇐  Π(x₁ : Ty l₁). … Π(x_m : Ty l_m). Ty l
    ⇝  D#tycode_fn^δ                         (registered, at that profile)
    ⇝  λ x₁ … x_m. ⌜D<El x₁, …, El x_m>⌝      (otherwise)
```

`check_generic_former_value` (`inductive.rs`), reached from
`check_type_former_value`, which already did the same for a record's value
parameters (`docs/record-type-partial-application.md`). Same disambiguator:
no constructor inhabits a universe, so a Π-spine ending in `Ty l` wants the
type former. It commits only on a bare name with no written type arguments,
and only for a declaration with type parameters and no value parameters,
index or codata index.

The η-short spelling matters beyond aesthetics. A class field `M(A)` at
`M := Option#tycode_fn` is `El(app(Option#tycode_fn^δ; ⌜A⌝))`, the reference
spelling the rest of the elaborator already reads as `Option<A>`. The λ
leaves a β-redex in every field type, and both spellings are
kernel-equal.

Refusals, each a declaration under `// expect-error` in the probes:

- an arity mismatch: "`Option` takes 1 type argument(s), but the expected
  type constructor provides 2 before its `Type`". When the expected type
  has fewer arrows than the declaration has parameters (`Result` at
  `Type → Type`), the message adds that a constructor fixing the others is
  a λ the author writes;
- a domain that is not a universe (`Option` at `Nat → Type`): "a type
  parameter takes a type".

## 3. The unifier: `?M(Nat) ≟ D<…, Nat>` (piece 1)

The pattern is `El(app(?M; ⌜Nat⌝))`. `unify_ty` already had an arm for a
pattern spelled through a declaration's code against an inline subject: it
respells the subject with `respell_ty` and aligns the two. That arm required
a **committed** head. It now also takes an **applied meta**
(`flex_applied_head`), and the existing application congruence then does
the rest. Its aligned-spine rule (`matching_value_spine`) lets `?op(x, y)`
learn `append<A>`: a pattern spine of length `k` against a rigid spine of
length `n ≥ k` whose leading `n − k` arguments are type arguments gives

```
?M := app(D#tycode_fn^δ; a₁ … a_{n−k})        and   pᵢ ≟ a_{n−k+i}
```

That is the first-order approximation Lean and Haskell use: the head plus
the leading arguments, with the last ones abstracted. Its consequence for
`Result<A, E>` is that `?M(Nat) ≟ Result<Bool, Nat>` takes
`?M := Result<Bool, _>`, abstracting the **error** type. §6 discusses this.

Value-parameter declarations come along free, since `Box(Nat)` respells the
same way (`record Box(A: Type)`).

This adds no new kind of guess. A subject that already arrived in the
reference spelling met the same congruence before this round, so a
predicate implicit `?P(n)` against `El(app(List#tycode_fn^δ; ⌜Nat⌝))` learned
`?P := List#tycode_fn^δ` then too (learn-only, judged by the kernel). The
arm now makes the answer independent of which spelling the subject arrived
in.

### 3.1 A type with no code function: the constructor spelling

`Tac<Nat>` cannot be respelled, because `Tac` registered no code function.
`U::constructor` (`Elaborator::constructor_spelling`, `gendefs.rs`) asks a
second question, only from this arm and only after the registered route
declined: spell the subject as `El(app(λ x̄. ⌜D<El x̄>⌝; ā))`. It computes
the declaration's code function at the all-`Ty 0` profile (what
`register_ty_code_fn` would have pushed), recovers `ā` with the same
positional hole matcher `instance_match` uses (factored out as
`instance_match_entry`), and keeps that matcher's identity step. The
template at the recovered arguments must be the subject syntactically, so
a guess is either right or declined.

The matcher learned two formers for this. `W` has its positions under the
shape's binder, and the positions are a `case` over the shape. Both are
declines turned into matches, never answers that need arguing (the
matcher's own rule).

The congruence cannot take a λ-headed subject, because `unify_tm`
contracts a β-redex head before anything else. So `flex_spine` applies the
first-order rule to that pair directly: `?M` takes the head with the
leading arguments, and the remaining arguments pair up.

Cost: one open lowering of the declaration per call. The only caller is a
meta applied to arguments meeting a subject the registered route declined,
which no code before this round wrote.

## 4. Classes over a constructor (piece 3)

**Grammar.** A class head's parameter may carry a kind:
`class Bind<M: Type → Type>`, `class StateM<S, M: Type → Type>`
(`class_tyvar_list`). Any type parses as a kind. What makes one a
constructor is that its argument is checked at it. The tree-sitter grammar's
`type_parameter` already admitted `name: expr`.

**Lowering.** A kinded parameter is a term, so the class's record takes it
as a **leading value parameter**: `class Bind<M: Type → Type> { … }` is
`record Bind(M: Type → Type) { … }`, the shape probe P1 had already shown
computes as a dictionary. Unkinded parameters stay type parameters, and the
class's own index parameters follow the kinded ones.

**The head keeps its spelling.** `Bind<Option>` is still what an instance
head, a `requires` binder or a `:= infer` parameter writes. Every reader
of a `ClassRef` (registry key, canonical name `Option::Bind`, ancestor
renaming) keeps seeing the angle-bracket form, because the instance key
is still the resolved head of the first written argument. One rewrite at
`elab_ty` (`kinded_class_ty`) turns the written head into the record
application when it is elaborated:

```
Bind<Option>         ⇝  Bind(Option)
StateM<S, M>(op)     ⇝  StateM<S>(M, op)
```

The argument becomes an expression, so `Option` meets §2 and a parameter
`M` is a local. `Traits::kinded`, a set of the names of kinded classes,
keeps the rewrite off every other named type.

**Registry state.** `ClassInfo.kinds` records each parameter's kind, and
the module image carries it, which is why the image magic moved
(`HTHMOD …\x1c`, `HTHIFC …\x19`). An instance's literal of a kinded class
is spelled without type arguments and takes the constructor from the
expected type, as an indexed class's literal already did.

**Resolution** is unchanged: candidates are tried and kernel-checked
against the goal (`docs/traits-layer2-design.md` §3.1), and `Bind(?M)`
with `?M` solved converts with `Bind(Option)` the ordinary way.
`solver_carrier_head` now reads a kinded carrier's solution off the
application, so the instance at the solved constructor is tried first. For
a solution `D#tycode_fn^δ`, the preferred key is `D`'s. The search trace
shows `Bind<List>`, not `Bind<M>`.

**Refusals.** An unsolved constructor names itself rather than suggesting
`twice<…>`, which cannot give a value implicit: "the goal of `b`
(`Bind<M>`) needs the type constructor `M`, which this call does not
determine … Write it (`twice(M := Option, …)`)". A constructor with no
instance is the ordinary "no instance for `Bind<List>`" trace.

## 5. What implementing this found

These are for R2 (`issues/binding-statements.md`) and for Minus.

1. **No implicit-λ insertion.** `pure := λ a => Some(a)` against
   `{A: Type} → A → M(A)` is refused ("`Some` is a constructor of `Option`,
   which is not the expected type here"), because the λ's `a` binds `A`. That
   is `docs/implicit-binders-design.md` §6.2's decision, not a gap in this
   round. Instances write `λ {A} a => Some(a)` or a reference
   (`Option::and_then`), and §2.1 of the sequencing note's
   `pure := λ a => Pure(a)` needs the `{A}`.
2. **The class `Pure` collides with `Tac`'s constructor `Pure`.** A class's
   record constructor is named after the class
   (`docs/traits-layer1-design.md` §2), so in a module that sees both,
   `Pure(a)` means the dictionary. The probes qualify `Tac::Pure`. R2 should
   choose before the classes enter the library: qualify at the uses, or
   name the class differently.
3. **`Result`'s varying argument is the first one.** First-order
   approximation abstracts the last argument, so `M(A) ≟ Result<A, E>`
   abstracts `E`. A `Result` instance over `λ A => Result<A, E>` is refused
   at the declaration today (the binder `E` is not seen in a λ carrier, and
   a λ has no head for the canonical name). There are two ways out, and
   [[class-instance-at-lambda-carrier]] owns the choice. *Decided and built
   2026-11-02: the type declares its slot (`inductive Result<A, E> varies
   A`), and instances sit at `λ (A: Type) => Result<A, E>`
   (`docs/lambda-carrier-instances-design.md` §7).* One is to put the
   varying argument last (`Result<E, A>`, Haskell's `Either e a`), which
   the approximation then handles. The other is λ-carrier instances plus a
   use-site rule that picks `λ A => Result<A, E>`, which is no longer
   first-order.
4. **Tier-2 declarations register no code function.** `Tac` is spelled as a
   λ wherever it is a constructor, and §3.1 recomputes its template per
   call. Registering code functions for tier 2 would retire both, but it
   would also respell every `Tac<…>` in emitted terms across the library,
   which needs its own measured round
   ([[tier2-type-code-functions]]).

## 6. Relation to [[parametric-type-families]]

That decision round asks whether `<A>` should become a kernel family, and
listed pieces 1 and 2 here among what it would retire. They turned out not
to need it. The code function each tier-0/1 declaration already registers
is that family at the type level, so a bare `Option` is a kernel term of
type `Type → Type`, and the unifier's question is first-order against its
spelling. Generic **functions** were already abstracted over `A : Ty 0`.
What stays monomorphized is the inline lowering at each use, which
`respell_ty` names back. What is left of that round's case is therefore
its cost side: elaboration time and term size of per-use substitution,
trial-by-kernel-check resolution, and universe-level profiles other than
all-`Ty 0`. It no longer gates this round.
