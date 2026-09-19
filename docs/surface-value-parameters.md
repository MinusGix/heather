# Value parameters on `record`: the surface's value-indexed Σ

Status: **landed**, 2026-08-01. Tracking issue: `issues/surface-existential.md`
(route 1). The feasibility report this implements is
`docs/surface-existential-investigation.md`; its §C is the gap list, its §F the
consumer shapes, its §H the risks. Read that first — this document records the
grammar, the rule, and the decisions that were open in it.

No kernel change. Every term this emits is a `Σ`/`Pair`/`Fst`/`Snd`/`Id` the
tier-0 generator already emitted; what is new is *where the field types come
from*.

---

## 1. The grammar

```
record   := "record" name tyvars? valparams? "{" field ("," field)* ","? "}"
tyvars   := "<" name ("," name)* ">"
valparams:= "(" param ("," param)* ","? ")"
param    := name ("," name)* ":" type
```

The production is shared: `class` and `inductive` heads read the same list, and
as of 2026-08-17 so does `instance`, where it is what makes an instance generic
over a **value** (`docs/value-generic-instances-design.md`). The run of names
sharing one annotation — `(n, m: Nat)` — arrived with that round, for the
reason a `fn`'s parameter list has it: a reader who has written
`fn f(n, m: Nat)` has no way to know the head is a different production.

Both lists are optional and they compose, in that order:

```heather
record Halts(m: Nat)              { n: Nat, h: dbl(n) = m }
record Box<A>(k: Nat)             { v: A, n: Nat, h: dbl(n) = k }
record Converges(p: Prog, env: Val, ir: Ir, vs: Val) {
    n: Nat,
    h: eval(n, p)(env, ir) = Out(vs),
}
```

A **type** parameter (`<A>`) is a type the use site supplies; a **value**
parameter (`(m: Nat)`) is a *term* it supplies. That is the whole distinction,
and it is why one name cannot be both (rejected at declaration time).

The position is unambiguous and was previously a parse error
(`record R(m: Nat)` was `expected `{` (field list), found LParen`). `fn` and
`theorem` share no grammar with `record`/`inductive` — they have their own
inline binder loop — so nothing else moved.

The parameter list is a **telescope**: parameter `j`'s type may mention
parameters `0..j`. A function-valued parameter (`ev: Val -> Ir -> Res`) is
fine; the field restriction that used to forbid function *fields* keys on
self-occurrence, not on shape (`surface-records.md` §11.1).

Rejected, each with its own message: a value parameter on an `inductive` (§6),
a duplicate, a collision with a type parameter, and a collision with a field
name (the field would shadow the parameter in the field types after it, which
is legal and never meant).

---

## 2. The rule: substitute at lowering

A record is lowered afresh at every use site (type parameters are
monomorphized, `surface-records.md` §1.1). A value parameter rides the same
mechanism with a *term* in place of a type:

- the use site's arguments are checked against the declared telescope in the
  **ambient** context, each one extending an alias list so the next parameter's
  declared type can mention it (`Elaborator::valparam_args`);
- `lower_ctor` then binds each parameter as an `Alias` at `depth =
  cx.names.len()` — the elaborated argument, inlined at each use, weakened by
  `names.len() - depth`.

`Alias` is the same carrier a `let` binding uses and the same `depth` device
`TyVar` uses; nothing was invented. The weakening is the entire correctness
content: the field spine pushes the nominal tag and then each earlier field on
top of the ambient context, so a use of a parameter in field `j` sits `1 + j`
binders deeper than the argument it denotes.

**This is the one thing the kernel cannot check.** An un-shifted parameter is
captured by the witness field and writes a well-formed but *different* — and
typically trivially inhabited — proposition: `Σ n. dbl n = n` where `Σ n. dbl n
= m` was meant, inhabited by `⟨0, refl⟩` at every `m`. Both spellings type-check.
The observers are therefore **propositional**: `crates/elab/tests/value_parameters.rs`
§7 asserts that `Halts(m)` at an *open* `m` is not provable by either
`Halts(0, refl)` or `Halts(m, refl)`, neither of which is a type error under the
captured encoding. See `surface-existential-investigation.md` §H risk 3.

---

## 3. Use-site formation

`Converges(p, env, ir, vs)` **in type position** already parsed before this
round: the parser's applied-type-is-never-called backtracking delivers it as
`TyKind::OfExpr`, and `elab_ty` tries the family hooks before the generic
infer-and-decode path. This round adds `try_valparam_ty` alongside
`try_indexed_ty` on that same road.

A bare `Converges` where the arguments were meant is a named error listing the
parameters. Wrong arity is an arity error. The arguments are **checked**, not
merely counted, against their declared types.

Since 2026-08-01 the same road is taken from **expression** position whenever
the expected type is a universe: `fn BoxedT(v: Nat) -> Type { Boxed(v) }`
routes to this `TyKind::OfExpr` handler rather than to the constructor, which
is what makes a value-parameterized record a first-class `Val -> Type` value
(`docs/record-type-values.md`). Everything in this section is what runs there,
including the arity message — it is the same `valparam_args`.

Since 2026-09-19 a **prefix** of the telescope is enough, whenever the expected
type is a function type whose ultimate codomain is a universe: `Grammar(level)`
against `(source) -> Cursor<T>(source) -> … -> Type` η-expands over the value
parameters left over and lowers the saturated spelling through this same
handler (`docs/record-type-partial-application.md`). So a record used "as a
relation" needs no wrapper `fn`, and the arity message there is the one that does
**not** come from `valparam_args`: it counts the telescope against the arrows
the expected type supplies.

---

## 4. Construction: checking position supplies the parameters

This was the one open design decision
(`surface-existential-investigation.md` §C.5, risk 4). Closed the recommended
way: **checking position only.**

A value parameter appears only inside a *field's* type — never as a field, and
never as an argument to the constructor — so recovering it from
`Converges(50, refl)` is higher-order unification, not the narrow
field-type-is-a-parameter reading `infer_ctor` does for type parameters. The
round declines to build that unifier.

Construction therefore needs **no new code at all**: `build_ctor` already reads
every annotation off the expected type, and the expected type is the encoding
with the parameters already substituted. Both spellings go through it:

```heather
fn h4() -> Halts(4) { Halts(2, refl) }            -- call spelling
fn h4() -> Halts(4) { Halts { n: 2, h: refl } }   -- literal spelling
fn from_argument() -> Nat { takes(Halts(2, refl)) }
```

Inference position is a named diagnostic that says which positions do work.
`R<Nat>(a, b)` is *not* a spelling: `<…>` supplies type arguments, and value
arguments are a different list it cannot reach.

**Edge behaviour worth knowing (corrected 2026-08-02).** The annotated
`let x: T = e;` was *not* one of the working checking positions when this was
written — not because of this round, and not for the reason given here. The
cause was `expr()`'s comparison rung, reached through `ty_atom`'s
fall-through, rather than "the type grammar has `a = b`"
(`docs/let-and-blocks-design.md` §1.1(1)); `let x: Nat = 3;` was
`parse error: expected `=`, found Semi` along with every other annotation that
reached that fall-through. Fixed by `docs/let-and-blocks-design.md` §3: the
annotation is read with the rung suppressed, an equality annotation is
parenthesised, and the annotated `let` is now a working checking position. The
diagnostic still names a declared result type, which is no worse for it.

---

## 5. Destruction, and levels

Nothing needed changing. `project_field` walks the Σ spine substituting each
earlier projection into the tail, `elab_arm` does the same with aliasing, and
`let { n, h } = c;` shares that code. All three are indifferent to *where* a
type in the spine came from, so a substituted value parameter costs them
nothing. All three are exercised at a **neutral** receiver, where nothing
computes.

**Levels.** A value parameter is a term, so it contributes **no** level — the
same asymmetry `Vec`/`Wf` have for their arity terms. The record's level is
still the Σ join of its *field* levels, computed by the existing fold. A
uniformly-level-0 suite cannot see a dropped join, so the acceptance keeps one
level-1 declaration (a `Type`-valued field) and pins both halves against the
prelude's level-0 `sym`: `LevelMismatch` at level 1, and through at level 0.

---

## 6. Parameters are not indices — and the diagnostic now says so

A **parameter** is uniform across constructors and lowers by substitution. An
**index** varies per constructor result and needs fording. That line was
already drawn (`issues/indexed-families.md`), but the classifier's own message
pushed the wrong case across it: a result index that is a bare variable in
*every* constructor was diagnosed as "not constructor-headed … the general
(fording) case", when it is not an index at all.

That arm is now split (`inductive.rs`, `parse_result_index`):

- **every** constructor's index a bare variable → "…is a **parameter**, not an
  index", naming `record D(n: Nat) { … }`;
- otherwise → the old fording message, unchanged, because that case really is
  the general one.

Both are pinned in `crates/elab/tests/indexed_families.rs`.

**Record-only this round.** Value parameters are accepted on `record` and
rejected by name on `inductive`. The reason is not difficulty but discipline: a
`record` has one constructor, so uniformity across constructors is free, and
"substitute at lowering" is the *whole* lowering. On an `inductive` the same
list needs the uniformity check per constructor and an interaction with the
index telescope, and doing that half-way is how a parameter gets silently
mis-lowered as an index. Filed as follow-up on
`issues/surface-existential.md`; no consumer needs it.

---

## 7. What this does not do

Route 2 — a general `Sigma<A, B>` with `B` a type family — stays deferred, for
the reasons `surface-existential-investigation.md` §E measured: no `Ty` form
denotes a family, `->` is not an expression, and parameters are monomorphized
by design. Route 1 subsumes every consumer named today, and the ∃-closure
relation between the two means nothing re-proves when route 2 lands.

`inj` on a value-parameterized record with dependent fields is still diagnosed
rather than derived (`issues/dependent-field-injectivity.md`). No consumer needs
it.
