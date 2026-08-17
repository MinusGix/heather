# The logical connectives, and their notation

Source of truth for `lib/std/logic.hthr` and the grammar that spells it
(`issues/std-logic-module.md`, landed 2026-08-16). Tests:
`crates/elab/tests/logic.rs` (meaning), `crates/syntax/src/parser.rs`'s test
module (spelling).

## 1. Why the library had none

Every proposition in `lib/std` was an equation or a `->` chain, because those
were the only things sayable. That absence is the direct cause of the
`leb(n, m) = True` idiom in `std/nat`: with no `∨` there is no way to state
`n <= m ∨ m <= n`, and with no `⊥` there is no way to state a refutation, so
a Bool-valued function plus an equation stood in for both.

Retiring that idiom (`issues/class-ops-prop-vs-bool.md`, 2026-08-16 — state
the mathematical relation once, propositionally) therefore needs this module
first. It is a prerequisite, not a companion.

## 2. Propositions are types, and they are relevant

There is no `Prop` sort and this module does not want one. Relevance is the
default ontology; `SProp` stays opt-in for evidence that should be invisible
(`issues/sprop-strict-prop.md`); erasure is the compiler's business
(`datarepr` / `Compile`) rather than the type system's.

The consequence that matters here is a *simplification*: a connective is an
ordinary record or inductive, its elimination is field access or `match`, and
nothing in the module is a special form. In particular there is no
elimination restriction to work around — a proof of `P ∨ ¬P` can be
eliminated into `Type` to choose a value, which is what makes `Decide`
(`issues/decide-class.md`) a one-field class rather than a second universe.

## 3. What is declared, and what is not

| | spelling | why |
|---|---|---|
| `True` | **not declared** | the kernel's `Unit^0` under a surface name (`issues/true-prop-trivial-hypotheses.md`); its η rule is judgmental proof irrelevance, which an `inductive True { intro }` would throw away |
| `False` | `inductive False {}` | zero constructors, so a `match` on it has zero arms and proves anything — see §6 for what it took to be spellable |
| `Not` | `fn Not(P: Type) -> Type { P -> False }` | a `fn`, so `¬P` stays *definitionally* an implication and a proof of it is applied rather than unwrapped |
| `And` | `record And<P, Q>` | a non-dependent Σ; elimination is `.left`/`.right` |
| `Or` | `inductive Or<P, Q> { Inl, Inr }` | elimination is `match` |
| `Iff` | `record Iff<P, Q> { mp, mpr }` | **not** `And<P -> Q, Q -> P>`: named directions, because an `Iff` is applied far more often than it is taken apart |
| `Exists` | `record Exists<A>(P: A -> Type)` | the value-parameterized Σ (`docs/surface-value-parameters.md`), generalizing `ir_v1.hthr`'s `Converges` |

**Type parameters, not value parameters of type `Type`.** `And<P, Q>`
monomorphizes per instantiation (`docs/inductive-tier0-lowering.md` §2), which
is what a connective wants; a `record And(P: Type, Q: Type)` would carry a
`Type` and sit at level 1, which `issues/surface-existential.md`'s closing log
already recorded as breaking against level-0 machinery.

## 4. The notation

Unicode is *the* spelling, not an alternative to an ASCII digraph set. `λ` and
`∙` already lex, so this follows a precedent rather than setting one. `<->` is
the single deliberate ASCII survivor — the connective people reach for
casually — and it lexes to the **same token** as `↔`, so nothing downstream
can tell them apart.

| written | desugars to | node |
|---|---|---|
| `¬P` | `Not(P)` | `ExprKind::App` |
| `P ∧ Q` | `And<P, Q>` | `ExprKind::TyApp` |
| `P ∨ Q` | `Or<P, Q>` | `ExprKind::TyApp` |
| `P ↔ Q`, `P <-> Q` | `Iff<P, Q>` | `ExprKind::TyApp` |
| `∀ x: A, P` | `(x: A) -> P` | `TyKind::Fn` — a **synonym** |
| `∃ x: A, P` | `Exists<A>(λ (x: A) => P)` | `ExprKind::App` over a `TyApp` |

`TyApp` rather than a `TyLit` wrapper because `expr_as_ty` already reads a
`TyApp` on a name back as `TyKind::Named` — so in type position the desugared
node is byte-for-byte the `And<P, Q>` a writer could have typed.

**The target names are fixed in the parser**, unlike `+`/`*`/`++`, which emit
a symbol for the resolver to place. The test is `op_symbol`'s own: a
connective is a *type former*, like `=`, not an operation a carrier can have,
and there is nothing a designation could say about `∧` at a carrier because
its operands are propositions rather than values of one.

### 4.1 Precedence

Tightest to loosest:

```
  =  <=  <        (the comparison rung, unchanged)
  ¬
  ∧
  ∨
  ->
  ↔
```

Three of these are worth their reasons:

- **The connectives are looser than the comparison rung**, which is the
  *opposite* of where `&&`/`||` sit. The Boolean doubles are arithmetic — they
  combine `Bool` values, and `x && True = x` wants to be `(x && True) = x`.
  These combine propositions, and a proposition is what a comparison
  produces. Both readings are right; they are simply different rungs.
- **`¬` is looser than `=`**, so `¬ a = b` is `¬(a = b)`. The reading everyone
  writing it wants, and Lean's.
- **`↔` is looser than `->`.** This one needs machinery: the arrow parses its
  codomain with `ty()`, which reaches `expr()` and would take the `↔` for
  itself, giving `P -> (Q ↔ (Q -> P))`. `Parser::no_iff` — set by
  `Parser::cod` at the three codomain sites, mirroring `no_eq` — is what makes
  the loosest rung actually loosest.

`∧` and `∨` are **right-associative** (the fixity `++` chose, and for the same
proof-relevant reason: `And(p, And(q, r))` is the nesting the record builds
and projects). `↔` is **non-associative**, like the comparison rung, with its
own targeted message.

### 4.2 The two rewinds

`ty_atom` returns early for an applied type (`D<A>`) and for a parenthesized
group, so either as a connective's *left operand* would leave the connective
dangling and report at whatever the declaration expected next. Both rules now
decline when `at_connective()`, rewind, and let the expression grammar build
the whole type — the same move the `D<A>` rule already made for a following
`(` (`docs/surface-polymorphism.md` §1).

### 4.3 One binder group per quantifier

`∀ x, y: A, P` writes; `∀ x: A, y: B, P` does not, and gets a message naming
the nesting that replaces it. Forced rather than chosen: after the
annotation, a comma could begin either a second group or the body, and the
body may itself be a bare name, so the two readings are genuinely ambiguous.
The flat spelling is caught by a two-token lookahead (`ident :` cannot be a
body, since `:` is not in the expression grammar) rather than left to fail
downstream.

## 5. What the round did not need

No kernel change and no new checking rule. Every declaration in §3 elaborated
on the first attempt against the language as it stood; the notation is a lexer
window, three parser rungs, a precedence flag and two rewinds. That is the
sense in which the connectives were *missing* rather than *unsupported*.

The two elaborator changes it did need (§6) are both about **names and
inference**, not about the connectives: neither would have been needed to
write the module, only to write it with the names it wanted.

## 6. Two things the module needed from the elaborator

Both were found by writing the module rather than by designing it, and both
were fixed the same day (2026-08-16) rather than worked around.

### 6.1 `False` the type beside `False` the constructor

`bool::False` — the *constructor* — already exports the name, and resolution
keyed name first and kind second, so a file importing both was told `False`
was ambiguous **in type position**, where a constructor could never have been
meant. (`True` escapes this only by not being a declaration: it is the
kernel's `Unit^0` under a surface name.)

Two rules now make the two coexist, and **both are shrinks, never choices** —
in each case the dropped reading could not have checked where it was dropped,
which is the invariant `docs/modules-design.md` §8 already states for the
expected-type route:

- **Type position never considers a constructor a candidate.**
  `names::resolve_kinds` takes the candidate kinds, and `lookup_inductive`
  passes `[Inductive]`. A constructor is not a type, so a `TyKind::Named`
  resolving to one could never have elaborated.
- **An expected type that is an inductive never considers a type *name* a
  candidate.** `only_ctors_visible` used to stand the expected-type route down
  whenever any visible candidate was not a constructor; an `inductive` is now
  admitted beside them, because a type name denotes a value whose type is a
  *universe* and so could never inhabit the expected inductive. A `fn` of the
  same name still stands the route down, and must: it may well return the
  expected type, so between it and a constructor there is a real decision.

The second needed one more fix to fire at all: **the expected type is whnf'd
first**. A declared result type arrives structural, but a parameter's domain —
what an argument is checked against — can still be a reference that only
δ-unfolds to the lowering `tag_of` reads. Before it, `theorem t(): Bool
{ False }` resolved and `idb(False)` did not, which is the same question in
two spellings.

Expression position is deliberately untouched where both readings are
possible. The asymmetry is the point: shrinking is licensed by impossibility,
never by preference.

### 6.2 `Exists` inferring its type argument

The bare record spelling needed `Exists<Nat>(λ (k: Nat) => …)`, even though
the predicate's own binder says what `A` is. `Elaborator::valparam_targs` now
infers each value argument and matches its type against the parameter's
*declared surface type*, reading a solution wherever the declared side is
exactly a type parameter — so `A -> Type` meets `Π(Nat). Ty 0` and `A := Nat`
falls out of the domains.

First-order and one-sided, on the doctrine `infer_ctor` already states: the
declared side is a skeleton with the parameter names as holes, and anything
deeper is unification. **Domain-only through an arrow**, because a solution
read out of a codomain would have been extracted from under a binder where it
may mention the bound variable. A partial type-argument list is still an
arity error; filling some and inferring the rest is a different feature.
