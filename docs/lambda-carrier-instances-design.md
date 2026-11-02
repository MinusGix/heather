# Instances at a carrier that is not `Head<…, A>`

Status: **built** 2026-11-02. Minus chose route 5 (the type declares its
varying slot), built on route 4's partial-application carriers. §7 is the
design as built; §1–§6 are the comparison that led to it. Probes:
`lib/_tests/std/core/type_constructor_tests.hthr`,
`lib/_tests/std/core/binding_statements_tests.hthr`. Tracking issue:
`issues/class-instance-at-lambda-carrier.md`. Builds on
`docs/higher-kinded-classes-design.md` (R2a) and
`docs/sequencing-surface-design.md` §13 (binding statements).

The issue lists three options and none is satisfying on its own. This note
separates the two questions they mix, records what master does today
(probed on `c80799c`), compares seven routes including the three, and
recommends one.

---

## 1. Two questions, not one

1. **Declaration.** How does an author *write* a carrier that is not a bare
   name: `Result` varying in `A`, `CoTree<R>(E)` varying in `R`,
   `Parser<T, A>` varying in `A`? Whatever the spelling, the instance needs
   a registry key, a canonical name, and every binder (`E`, `T`) recoverable
   from the head.
2. **Use site.** Given `x: Result<Nat, Bool>` at a parameter `M(A)`, how is
   `?M` chosen? This is the hard half, because `?M(?A) ≟ Result<Nat, Bool>`
   has **no most general solution**: `M := Result<·, Bool>, A := Nat` and
   `M := Result<Nat, ·>, A := Bool` are both solutions, neither an instance
   of the other (and so are the constant constructors). Unification alone
   cannot choose. Something else has to: a **convention** (abstract the last
   argument), a **declaration** (the type says which argument), or the
   **candidates** (the instances in scope say).

Note that in `Bind::seq(e, k)` and `bind(x, f)` the argument is itself a
meta (`?M(?A)`), so Miller-pattern or Rocq-style "abstract the occurrences
of the argument" unification never applies: there is no rigid argument to
abstract.

## 2. What master does today

Probes (scratch files, not committed), each run with
`heather check -L lib`:

| Probe | Result |
| --- | --- |
| `pick({M}, x: M(Nat))` at `r: Result<Nat, Bool>` | refused, **misleadingly**: "this has type `Result<Nat, Bool>`, but `Result<Nat, Nat>` is expected". The approximation took `M := Result<Nat, ·>` and the mismatch surfaces as a type error. |
| `twice(r)` at `Result<Nat, Bool>` | "no instance for `Bind<Result>`": the goal is really `Bind<Result<Nat, ·>>`, displayed as `Bind<Result>`. |
| `instance<E> Bind<λ (A: Type) => Result<A, E>>` | refused at the declaration (occurrence check). |
| `fn ResultE(E: Type) → Type → Type { λ A => Result<A, E> }`, `instance<E> Bind<ResultE(E)>` | **declares**. At `r: Result<Nat, Bool>` resolution tries `ResultE::Bind` and rejects it ("cannot infer `E`"). At `r: ResultE(Bool)(Nat)` it **resolves and computes** (`twice(Ok(3), M := ResultE(Bool)) = Ok(6)` by `refl`). |
| `twice(Ok(3), M := λ A => Result<A, Bool>, b := …, p := …)` | checks and computes by `refl`: the kernel and elaborator are fine with a λ carrier once it is chosen. |
| `inductive Res2<E, A>`, `pick(r: Res2<Bool, Nat>)` | works (first-order approximation). |
| `instance<E> Bind<Res2<E>>`, `pick_at(Res2<Bool>, r)` | refused: "`Res2` takes 2 type argument(s), found 1". Partial application is refused both as a value and as a carrier. |
| `pick(p: Parser<Bool, Nat>)` | works. **Parser is not a λ case**: its varying argument is already last, and only the partial-application carrier `Parser<T>` is missing. |
| `pick(t: CoTree<Nat>(E))` | "could not infer `M`". The value parameter `E` comes after the type parameter, so no reordering of type parameters puts `R` last, and the aligned-spine rule refuses to abstract past a value argument anyway. |

So the customers split: **Parser** needs only partial-application carriers;
**Result** needs either a reorder or a real use-site rule; **ITree/CoTree**
needs a real use-site rule whatever is reordered (`<R>` cannot follow
`(E)`).

## 3. How other systems answer

- **Haskell** has no type-level λ at all, so unification stays first-order
  and principal. The answer is the convention (`Either e a`, `StateT s m a`,
  monadic slot last) plus `newtype` wrappers (`Flip`) for the other slot.
- **Lean 4** uses the same last-argument approximation and the same
  convention (`Except ε α`, `StateT σ m α`, `ReaderT ρ m α`). For monads
  that are not inductives it uses **named defs** kept folded during
  elaboration (`def StateT σ m α := σ → m (α × σ)`, instance at
  `StateT σ m`) — option 3 plus the convention. `Id` is a def precisely so
  that no instance is ever at `fun α => α`. Lean also has `unif_hint` for
  teaching the unifier one non-pattern problem (route 5 below).
- **Rocq** (ext-lib, ITrees): evarconv's first-order approximation and the
  convention again (`Monad (sum T)`, `itree E R` with `E` first, instance
  at `itree E`). Typeclass search will happily instantiate an evar in the
  goal with the *first* instance that fits, which is why `Hint Mode … !` is
  used to forbid searching at an unsolved carrier. Canonical structures are
  the precedent for "the unifier consults an instance table keyed by a
  rigid head" (`?S.carrier ≟ T` is solved by looking `T` up).
- **Agda** does no first-order approximation: `?M ?A = A ⊎ B` stays a
  postponed constraint. Instance search runs on a goal with metas, unifies
  each candidate's type with the target (which may solve those metas), and
  **commits if exactly one candidate survives, postpones if several, errors
  if none** (Agda manual, instance arguments, "overlap resolution"). The
  standard library still names its constructors (`Sumₗ`, `Sumᵣ` in
  `Data.Sum.Effectful.Left/Right`), and `do` is syntactic over the `_>>=_`
  in scope.
- **Scala** (2.13 partial unification, Scala 3) abstracts the last argument
  too; type lambdas (`[A] =>> Either[A, E]`, kind-projector's
  `Either[*, E]`) are writable in instance heads but never inferred, so
  cats orders `Either[E, A]`.

Everyone who infers the carrier either fixes the order by convention or
lets the candidates decide (Agda). Nobody infers type lambdas by
unification.

## 4. The routes

Each route says what it enables, what it costs or breaks, and how it fits
the elaborator and kernel.

### Route 1 — reorder (`Result<E, A>`) plus partial-application carriers (issue option 1)

- *Enables*: `instance<E> Bind<Result<E>>`, η-short carriers
  (`app(Result#tycode_fn; E)`), no new inference at all.
- *Costs*: the churn is small (44 `Result<` occurrences in `lib/`, eight
  files) but it moves Heather off Rust's `Result<T, E>` order, which is the
  one a reader expects. It needs route 4 anyway.
- *Breaks/limits*: a **convention**, so each future carrier must be
  designed around it, and it cannot reach `CoTree<R>(E)` at all (type
  parameters precede value parameters in Heather's spelling). A type that is
  a monad in two slots gets one of them.

### Route 2 — λ carriers, resolution chooses (issue option 2)

- *Enables*: any carrier, written as a λ. The kernel is already fine with it
  (§2, the explicit-`M` probe).
- *Costs*: the use-site rule is the whole design, and the issue leaves it
  open. A λ has no head, so the key and canonical name have to be read off
  its body. Every `M(X)` is a β-redex in emitted terms.
- Route 6 is this route made precise.

### Route 3 — named constructor (issue option 3)

- *Enables*: a head for free (`ResultE`), the occurrence check passes
  today, and when values are spelled `ResultE(Bool)(Nat)` it already works
  end to end. This is Lean's model for `StateT`.
- *Costs*: one boilerplate `fn` per (type, slot), and **values arrive spelled
  through the type, not the constructor**: an `Ok(3)` or a library function
  returning `Result<A, E>` never mentions `ResultE`. So it needs the same
  use-site rule as route 2, or it requires authors to write their types
  through the alias, which nobody will do consistently.
- *Keep it* for carriers with no inductive head (a `State` monad whose type
  is `S → A × S`): there a name is the only head available, as in Lean.

### Route 4 — partial-application carriers (new, small)

Accept `D<a₁ … a_k>` with fewer type arguments than `D` declares, at a
`Type → … → Type` position, as `app(D#tycode_fn^δ; a₁ … a_k)`, both as a
value (piece 2) and as an instance head (`instance<T> Bind<Parser<T>>`).

- *Enables*: Parser's instances today, and the η-short (cheapest) spelling
  for every carrier whose slot is last. No inference changes: the
  first-order approximation already produces exactly this term (§2).
- *Costs*: `check_generic_former_value` stops requiring a bare name;
  occurrence check reads binders in the written arguments (it already does
  for `Result<Nat>`-shaped heads via `ty_as_expr`). Tier 2 and codata, which
  have no code function, would spell it as a λ as they do today.
- *Limits*: by itself it does nothing for Result or CoTree.

### Route 5 — the type declares its constructor slot (new; a unification hint)

An attribute on the declaration (say `inductive Result<A, E>` marked as a
constructor in `A`) makes the approximation abstract that argument instead
of the last, and registers the matching code function or λ.

- *Enables*: Result without a reorder; deterministic, unifier-local, no
  coupling to resolution; even `pick(r)` with no class gets the intended
  answer.
- *Costs*: a per-type global choice, which is route 1's convention moved
  into an attribute. A second instance at another slot is impossible. It
  still needs the declaration half (sections or λs), and it does not cover
  headless carriers. New surface on every type declaration form.

### Route 6 — carriers chosen by candidates (new; route 2 made precise)

**Declaration.** A carrier is any type-constructor term whose body has a
**rigid head** after unfolding: a bare name, a partial application
(route 4), a section `Result<·, E>` / `CoTree<·>(E)` (`·` is already
Heather's argument slot, Scala's kind-projector reads the same way), a λ,
or a named constructor (route 3). Its key and canonical name come from that
head (`Result`), with a slot suffix when one class has instances at two
slots of one head. The occurrence check reads binders through the λ. Two
refusals at declaration: a carrier whose bound variable is the head
(`λ A => A`, the identity monad: it would fit every subject, so it must be
a named type, as Lean's `Id` is), and one whose bound variable does not
occur where the matcher recovers it (a constant constructor).

**Use site.** Inside one call (`apply_implicit`'s scratch world; nothing
crosses calls, keeping that file's stated decision):

1. When `?M(p̄) ≟ D<ā>` meets an applied meta that is the carrier of a
   **kinded solver obligation** of the same call (`b: Bind<M> := infer`,
   `Bind::seq`'s dictionary), the unifier does not approximate. It records
   the pair as postponed, and nothing (neither `?M` nor `?A`) is learned
   from it.
2. `retry_obligations` gains one step before readiness: for an obligation
   `C<?M>` whose `?M` has postponed pairs, take each instance of `C`,
   instantiate its binders as fresh metas, contract `carrier(p̄)` (β, and δ
   for a named constructor), and unify it with the subject. These are
   scratch-world structural unifications, not elaborations.
3. **Exactly one fits**: commit `?M` to it, replay the postponed pairs
   (now first-order: `Result<?A, ?E> ≟ Result<Nat, Bool>` learns `?A`),
   and resolution proceeds exactly as today, kernel-checked. **None**: fall
   back to the last-argument approximation, so the existing "no instance
   for `Bind<List>`" trace is unchanged. **Several**: refuse, naming the
   fitting candidates and suggesting `M := …`.
4. An applied meta with no kinded obligation (`pick`) keeps today's
   approximation.

- *Enables*: Result in its current order, CoTree/ITree, Parser (through
  route 4's spelling, the cheapest), named constructors when the value is
  spelled through the type, and two classes at two different slots of one
  type. Option and Tac go through the same step and get the same answers as
  today.
- *Fits the doctrine*: the occurrence-check message says "search selects
  among candidates and never guesses an argument". Route 6 is selection
  among candidates; `E` is recovered by unifying a candidate's carrier with
  the subject, never invented. A unique fit or a refusal, never the first
  fit (Rocq's footgun).
- *Costs*: a postponed-pair list in the call's scratch world and one
  carrier-selection step in `retry_obligations`; the occurrence check and
  key computation learn λ/section bodies; probably no image change (the
  instance's type already carries its carrier). Selection unifies one
  carrier per instance of the class (`Bind` has two today) instead of
  narrowing by head first, which matters only as `Bind` grows
  (`issues/resolution-candidate-fan-out.md`).
- *Kernel*: none. A λ carrier `λ A. El(app(Result#tycode_fn; A, E))` makes
  every `M(X)` a one-step β-redex whose contractum is the reference spelling.
  That is unlike `Tac`, whose λ carries Tac's whole inline type
  (`issues/tier2-type-code-functions.md`). Contracting at instantiation
  keeps emitted terms in the reference spelling.
- *Risks*: inference becomes import-sensitive in one place: importing a
  second fitting instance turns a working call into an ambiguity refusal
  (never into a different answer). Agda accepts the same trade.

### Route 7 — rejected

- **Higher-order unification / abstracting occurrences** (Rocq's `apply`
  heuristic, Miller patterns): the argument is a meta in `bind` and `seq`,
  and when it is rigid (`Result<Nat, Nat>`) the abstraction is ambiguous
  again. Not unique, not predictable.
- **Wrapper types** (`newtype Flip`, Lean's structure wrappers): every value
  is wrapped and unwrapped at the boundary, which is the friction binding
  statements exist to remove.
- **Explicit `M :=` at each use**: works today (§2) and stays the escape
  hatch, but binding statements have no place to write it.

## 5. Comparison

| | Result as is | CoTree / ITree | Parser | Headless (`State`) | New inference | Convention imposed | Kernel |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 reorder | by reordering | no | needs 4 | no | none | yes | none |
| 2 λ, open | yes, rule undefined | yes | yes | no head | undefined | no | β-redexes |
| 3 named fn | only if spelled through it | same | same | **yes** | none / needs 6 | no | δ-redexes |
| 4 partial app | no | no | **yes** | no | none | slot last | none, η-short |
| 5 declared slot | yes | yes | yes | no | unifier-local | per type | none |
| 6 candidates | **yes** | **yes** | yes (with 4) | yes (with 3) | in-call, unique-or-refuse | no | small β |

## 6. Recommendation (as first proposed)

**Route 4 now, route 6 as the rule, route 3 for headless carriers, and keep
`Result<A, E>`.**

1. *Route 4 first*, a small round: partial-application constructors as
   values and carriers. It unblocks the parser-combinator port
   (`instance<T> Bind<Parser<T>>`) with no inference change, and it is the
   spelling route 6 prefers whenever the slot is last.
2. *Route 6 second*: section/λ/named carriers at declaration, and
   carrier selection by candidates at the use site. It covers Result,
   CoTree and ITree without a convention, and is the only route that does
   not ask each type to be designed around the unifier.
3. *Do not reorder `Result`.* The churn would be small, but route 6 makes
   it unnecessary, and the reorder still does not help CoTree.
4. If import-sensitive inference is unacceptable, route 5 is the fallback:
   the same reach for inductive carriers, decided per type instead of per
   instance set.

Independent of the choice: the misleading `Result<Nat, Nat> expected`
diagnostic and the `Bind<Result>` goal display (§2) are worth fixing on
their own (`issues/applied-meta-approximation-diagnostics.md`).

## 7. Decision and design: the type declares its varying slot

Minus chose route 5 over route 6 (2026-11-02): inference stays local to the
unifier and does not depend on which instances are in scope, and it also
fixes the plain `pick(r)` call that route 6 left on the approximation.
Route 6 remains an extension for a type that ever needs two slots inferred.

### 7.1 Declaring the slot

```heather
inductive Result<A, E> varies A { Ok(value: A), Err(error: E) }
```

`varies X` is a contextual clause after the parameter lists (and before an
index telescope or the body), on `inductive` and `record`. `X` names a type
parameter. A value parameter, an indexed declaration or a `codata` one is
refused for now, since none of them has a code function to abstract a
parameter of.

**Default.** With no clause the slot is the last type parameter, which is
the argument the aligned-spine approximation already abstracts, so no
declaration that inferred before changes. A declaration with value
parameters (`Box(A: Type)`) keeps the aligned rule unchanged.

### 7.2 The constructor at a slot

For `D` with type-level spine `a₀ … a_{n−1}` and slot `s`, the constructor
fixing the others is

```
C_s(ā∖s)  =  app(D#tycode_fn^δ; a₀ … a_{n−2})                       when s = n−1
          =  λ (x: Ty l_s). app(D#tycode_fn^δ; a₀↑ … a_{s−1}↑, x, a_{s+1}↑ … a_{n−1}↑)   otherwise
```

η-short when the slot is last (one global applied, the reference spelling
of every `M(X)`), and otherwise a λ whose body is one code-function
application, so `M(X)` is a single β-step from the reference spelling. One
helper builds it, and its three readers below share it, so a carrier
written at a declaration and one learned at a use site are the same term.

### 7.3 The three readers

1. **Partial application as a value** (route 4): `Parser<T>` or
   `Res2<Bool>` checked at `Type → Type` is `app(D#tycode_fn^δ; ā)`
   (positional; the missing arguments are the trailing ones). Today only
   the bare name is accepted.
2. **The unifier.** The applied-meta arm (`flex_applied_head` with a
   pattern spine of **one** argument) learns `?M := C_s(ā∖s)` and pairs the
   argument with `a_s`, instead of taking the head plus the leading
   arguments. Longer pattern spines (`?M(x, y)`) keep today's aligned rule.
3. **Instance carriers.** A kinded class's instance head may be a bare
   name, a partial application, or a λ `λ (A: Type) => D<…, A, …>` whose
   bound variable sits exactly at `D`'s slot and nowhere else. The carrier
   is elaborated to `C_s` so that resolution unifies it structurally with
   what the use site learned; its registry key and canonical name are
   `D`'s (`Result::Bind`); the occurrence check reads binders in the fixed
   arguments. A carrier abstracting any other position is refused at the
   declaration and names the declared slot: inference never produces it,
   so such an instance is unreachable. (A section `Result<·, E>` is a
   possible later spelling of the same λ.)

### 7.4 What it leaves

- A second inferred slot per type (a functor over `Result`'s error) is
  unavailable; `M := λ E => Result<A, E>` written at the call still works.
- A carrier with no head (`State`) is a named type-level `fn`, as in Lean.
- Tier-2 declarations (`Tac`) and codata have no code function, so their
  constructor is the λ over the inline lowering, as today; its per-use cost
  stays with `issues/tier2-type-code-functions.md`. CoTree additionally
  needs `constructor_spelling` to learn codata and value parameters.
- The tree-sitter grammar has `varies_clause`. Its `parser.c` is
  regenerated with the binding statements
  (`issues/tree-sitter-binding-statements.md`).
- Instances at the λ carrier are written `λ (A: Type) => Result<A, E>`. A
  section `Result<·, E>` would be shorter, but `·` is not a type yet.

### 7.5 What building it found

1. **A carrier argument's own code applications were never unspelled.**
   `unspell_ty_deep` substitutes a code function's arguments into its
   template and stopped there. When an argument is itself a type
   constructor (`Bind(app(Res2#tycode_fn; ?E))`), the template applies it
   (`M(A)` in a field), and the substituted instance still holds
   `El(app(app(Res2#tycode_fn; ?E); A))`. The pattern side kept that code
   spelling, the subject side was inline, and an instance binder (`E`) was
   never learned from the goal. The instance is now unspelled again when an
   argument is headed by a code function.
2. **A head meta solved to a λ was paired positionally.** Once `?M := λ A.
   Result<A, Bool>`, a later `?M(?B) ≟ Result<Nat, Bool>` (a nested
   `Bind::seq` checked against the outer one's `M(B)`) went through the
   application congruence. That congruence pairs `?B` with `Bool`, the
   argument the λ *fixes*. Now the solved head is substituted and the redex
   contracted before any pairing. An η-short solution never met this,
   because its spine lines up with the subject's.
3. **The reader in the unifier is two places, not one.** A subject already
   in the reference spelling reaches `unify_tm`'s application congruence
   without passing `unify_ty`'s re-spelling arm, so the slot rule
   (`slot_pair`) sits in both.

### 7.6 Where the pieces are

- `Inductive::varies` (`crates/elab/src/inductive.rs`). It is in the module
  image, which is why the magic moved (`HTHMOD …\x1d`, `HTHIFC …\x1a`).
  The parser reads `varies` (`varies_clause`).
- `Elaborator::slot_view`, `check_slot_lambda`, `code_fn_prefix` and the
  free `slot_lambda` (`crates/elab/src/gendefs.rs`): the constructor at a
  slot, as the unifier, a written λ and a partial application make it.
- `U::slot_view` and `slot_pair` (`crates/elab/src/unification.rs`).
- `check_generic_former_value` (partial application) in `inductive.rs`.
- `check_lambda_carrier` (the unreachable-carrier refusal), and the λ
  cases of `head_name` and `expr_var_count`, in `crates/elab/src/traits.rs`.
