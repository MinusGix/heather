# Value parameters on `record`: the surface's value-indexed Σ

Status: **landed**, 2026-08-01; on `inductive` 2026-10-21 (§6,
`issues/tier2-value-parameters.md`); inference position 2026-10-21 (§4.1,
`issues/value-param-constructor-implicit-inference.md`). Tracking issue: `issues/surface-existential.md`
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

Rejected, each with its own message: a duplicate, a collision with a type
parameter, and a collision with a field name (the field would shadow the
parameter in the field types after it, which is legal and never meant). On an
`inductive` (§6, since 2026-10-21) the field check runs over every
constructor, and two more refusals apply: a recursive occurrence other than
the uniform `D<p̄>(v̄)`, and value parameters beside an index.

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

Inference position was, until §4.1, a named diagnostic that said which
positions do work. `R<Nat>(a, b)` is *not* a spelling: `<…>` supplies type
arguments, and value arguments are a different list it cannot reach.

### 4.1 Inference position, since 2026-10-21

The reading above was too pessimistic: the parameter's occurrences in a field
type are rigid spines (`Finite(F)`, `F.specials.has_inf().IsTrue()`), so
recovering it is the same first-order problem a call poses when its domain is
`Float(?F)`, and the call unifier already solves that one. Where nothing
checks a construction, `infer_ctor` now hands value parameters to
`infer_ctor_values` (`constructor.rs`), after the type parameters are found by
the narrow reading:

1. the constructor's payload Σ is lowered (`lower_ctor`) with the value
   parameters as binders past the use site, each declared type read under the
   earlier ones;
2. those binders become the metas of a scratch world, exactly as a callee's
   `Π` binders do in `apply_implicit`;
3. the payload fields are walked in order: a field type with an unsolved meta
   is unified with its argument's inferred type (`unify_arg_ty`, the call
   path's entry), a meta-free one is *checked*, so `refl` and lambdas there
   cost nothing; each argument instantiates the next field's binder, and the
   walk stops once every parameter is solved;
4. the construction is then built at the solved instance by the checking route
   (`lower_instance` + `build_ctor`), which checks every argument against its
   field again — a wrong solution is a type error there, never a mis-lowering.

A parameter no payload field fixes may still be fixed by a child, whose type
is the whole instance (`ctor_from_child`; `Tau(t)` at tier 2). What remains a
refusal names the parameter and, when a field would have fixed it but its
argument only checks (`Halts(2, refl)` alone), that field and why. Pinned in
`crates/elab/tests/inductive_value_parameters.rs` §7.

The call's own note for an unpinned value implicit now suggests the named
spelling (`Float::Le(F := …, …)`), not `<…>`, which is refused for a value.

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

**On `inductive`, since 2026-10-21.** This section used to end "record-only
this round": a `record` has one constructor, so uniformity across
constructors is free, and on an `inductive` the same list needed a
uniformity check per constructor that was deferred rather than half-done.
That check is now the classifier's (`inductive.rs`, `uniform_occurrence`),
and value parameters are accepted on every unindexed `inductive`, at all
three tiers:

```heather
inductive Res(m: Nat) { Good(n: Nat, h: dbl(n) = m), Bad(why: Nat), Gone }
inductive Tree(m: Nat) { Leaf(n: Nat, h: dbl(n) = m), Node(l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m)) }
inductive ITree<R>(E: Events) { Ret(r: R), Tau(t: ITree<R>(E)), Vis(c: E.Cmd, k: E.Resp(c) -> ITree<R>(E)) }
```

### 6.1 The lowering is the record's

Nothing in the lowering moved. `lower_ctor` binds the parameters as aliases
at the use site's depth for **every** constructor, not just a record's one,
so each constructor's field types see the parameter weakened by however many
binders that constructor's spine has pushed (the tag, then its earlier
payload fields; at tier 1 the children are not in the shape, so a payload
after a child sits under fewer binders than its written position). Tier 2
lowers a function field's *domain* in the same field context, so
`E.Resp(c)` sees `E` like any other field type. Construction is still
checking position only (§4) — the injection path and every annotation are
read off the expected type — and `match`, no-confusion and `inj` read the
spine they are handed, so none of them needed a change.

### 6.2 The uniform occurrence

What an `inductive` adds is a recursive occurrence, and that is the
substance of "per-constructor uniformity". A recursive field lowers as a
*child* — its type is the instance being declared, so nothing in it is
substituted. That is right only when the occurrence **is** that instance:
`D<p̄>(v̄)` with the declaration's own type parameters and then its own value
parameters, each a bare name, in declared order. Any other value argument —
`D(Succ(m))`, `D(k, m)` for `D(m, k)`, `ITree<R>(F)` — would make that field
a different instance, i.e. an **index**, and lowering it as a child would
drop the difference with no type error. So it is refused, naming the spelling
that is accepted:

```
field of `F` uses `D` at arguments other than its own parameters: a recursive
occurrence must be `D(m)` exactly — its type parameters and then its value
parameters, each bare and in order. A value argument that varies is an index,
not a parameter
```

The applied spelling reaches a field type as `TyKind::OfExpr` (§3), not as the
`TyKind::Named` the tier-1 rule was written for; `self_head` reads both, so a
bare `D` where `D(m)` was meant, and a `D(0)` on a declaration with no value
parameters, are the same refusal rather than "nested recursion". Since a field
may not share a parameter's name (§1), a bare `m` in the occurrence can only
be the parameter. The same classifier serves the plain child, the container
element (`[D(m); n]`) and the function child's codomain (`A -> D(m)`), so
tier 1 and tier 2 cannot disagree about it.

### 6.3 What stays refused

~~**Value parameters beside an index**~~, accepted since 2026-11-09
(issues/indexed-families-at-any-index-type.md) on the `IWf` route only: a
declaration with both is never route 1's. An occurrence is
`D<p̄>(v̄, e)` (or `D<p̄>(v̄)(e)`), the value arguments the declaration's own
in order, as in §6.2, and the index after them. The shape declaration
carries the value parameters, so the payload is read under them; the index
type, the result and child indices, and a function child's domain are read
with them bound (`field_scope_cx`), and the signature is built at the use's
value arguments (`iwf_sig`/`iw_sig` take them). The bare-variable-index arm
above now names the `inductive` spelling as well as the `record` one, and it
fires only when the children sit at the result's variable too: an
accessibility-shaped family (a child at another index) is a genuine index.

The generators that already refused a value-parameterized record
(`datarepr`, certgen) refuse a value-parameterized `inductive` by the
same test, and an infinitary one with value parameters is not lowered at
declaration time (there is no instance to lower it at); its first use is.

### 6.4 The observers

`crates/elab/tests/inductive_value_parameters.rs`, on the four axes of
`docs/testing-generated-terms.md`. As in §2, the load-bearing half is
propositional: for **each** constructor that mentions the parameter, the
canonical inhabitant of a captured spelling (`A(0, refl)`, `B(0, 0, refl)`,
`Node(l, 0, refl, r)`, `Go(0, refl, λ x => Stop)`) is refused at an open
parameter, and a `match` at an open parameter hands each arm evidence that
`Witness(m)` accepts at that parameter. Beside them: closed computation by
`refl` at literal scrutinees, β at open constructor forms, induction at an
open parameter through a plain child and through `k`, an open element type
(`Bag<A>(m)`, `ITree<R>(E)`), no-confusion and injectivity at an open
parameter, and every refusal of §6.2–6.3.

---

## 6.5 Index defaults (2026-11-09)

A `record`'s value parameter may end `:= e`, an **index default**
(issues/constraint-indices-from-carrier-designations.md):

```heather
record OrderedRingHom<A, B>(map: A → B,
        same_a: A → A → Type := ≈, …, neg_a: A → A := λ x => -x, zero_a: A := 0, one_a: A := 1,
        same_b: B → B → Type := ≈, …)
```

- **A trailing run, positional.** Unlike a `fn` parameter's default
  (docs/named-arguments-design.md §9) the slot keeps its position, so every
  application that writes all the indices reads as before. Only a trailing
  run may have defaults (a parse error otherwise), and an application omits
  a suffix of them; one that omits them all may drop the parentheses.
- **Elaborated at the use site.** The default is checked at the slot's type
  as the application instantiates it, in a context that has the
  declaration's earlier indices and type parameters by name and the *use
  site's* operator symbols. So a bare `≈` is the designation at the slot's
  carrier (`Rat::Same` at `Rat`), or, inside `section<K: OrderedField(≈, …)>`,
  the binder (the carrier-aware rung 1, docs/operators-onto-classes-design.md
  §4). That is what makes `OrderedRingHom<Rat, K>(map)` mean both sides at
  once. A global a default names must be visible at the use site.
- **Refused where it means nothing**: a default that does not elaborate is
  reported at the application, naming the index and its default.
- **Terms, η-short.** A function default is stored η-short: `λ x => -x`
  is `Rat::neg` at `Rat`, and at a section's carrier, where `-x` is the
  designated `OrderedAddGroup::neg(…, x)`, the dictionary field it computes
  to, `K.inv`. A record's type is structural, so a caller recovers its
  indices from the field types by unification, which learns `?neg_b :=
  K.inv` from `?neg_b(map(x))` and nothing from a λ or from a wrapper with
  extra arguments (the unifier's refusal to guess `?f := add(a)` from
  `add(a, x)` stands). So `OrderedRingHom<Rat, K>(map)` elaborates to the
  same indices the explicit header wrote, and `ring`, `mono` and
  `linarith` read the morphism as before.

The record's image carries the defaults, so the module-image format was
bumped.

## 7. What this does not do

Route 2 — a general `Sigma<A, B>` with `B` a type family — stays deferred, for
the reasons `surface-existential-investigation.md` §E measured: no `Ty` form
denotes a family, `->` is not an expression, and parameters are monomorphized
by design. Route 1 subsumes every consumer named today, and the ∃-closure
relation between the two means nothing re-proves when route 2 lands.

`inj` on a value-parameterized record with dependent fields is still diagnosed
rather than derived (`issues/dependent-field-injectivity.md`). No consumer needs
it.
