# Traits, layer 1: the `class` and `instance` declaration forms

Status: **round slice**, carved out of `docs/traits-design.md` (the record) per
its §13 item (a). Tracking issue: `issues/traits.md`.

This document states only what layer 1 decides. Everything it does not
mention is either settled in the record or is layer 2's. §7 is the
"what implementing this corrected" section the house style requires.

**No kernel change, no metatheory obligation.** Every artifact this round
emits is a `record` declaration, a `fn`/`theorem` global, a record literal
and a projection — all of which landed with `docs/surface-records.md` and
`issues/type-owned-members-receiver-slice.md`. The class/instance forms are
a *desugaring into surface AST that is then handed to the existing
declaration elaborator*, which is why the trusted base is untouched.

---

## 1. Grammar

```
item      := … | class | instance

class     := "class" name tyvars? ("extends" classref ("," classref)*)?
             "{" field ("," field)* ","? "}"
classref  := name "<" ty ("," ty)* ">"

instance  := "instance" tyvars? valparams? classref
             ("requires" param ("," param)*)?
             "{" (member* | litfield ("," litfield)* ","?) "}"
member    := decl                      -- an ordinary `fn` / `theorem`
                                       -- (`meta fn` refused: it never reaches Ψ)
litfield  := name ":=" expr
```

`field`, `tyvars`, `param`, `decl` are the existing productions, and
`valparams` — added 2026-08-17 — is the `record` head's value-parameter list,
which is what makes an instance generic over a **value**
(`docs/value-generic-instances-design.md`).

Three notes.

- **`instance`'s body form is chosen by one token.** A body whose first
  token is `fn`, `theorem` or `meta` is the **block** form; anything else is
  the **literal** form. There is no mixed body: a block member is a
  declaration and a literal field is an assignment, and one brace cannot
  hold both without the reader having to look twice.
- **`:=` for the literal field, not `:`.** `record` literals already use
  `name: expr` and `class` fields use `name: type`, so inside `instance
  Monoid<Rat> { … }` a `:` would read as either. `:=` is the record's own
  spelling (`docs/traits-design.md` §3) and is unambiguous against both.
- **`extends` arguments must be the class's own type parameters** —
  `class AddCommGroup<G> extends AddGroup<G>` is legal, `class C<A> extends
  P<List<A>>` is refused this round. See §3.

## 2. A class is a record, plus a table entry

`class C<p⃗> extends … { f⃗ }` elaborates by building the `InductiveDecl`
that `record C<p⃗> { flattened f⃗ }` would have built and calling
`elab_inductive` on it. There is no second lowering, no second field table,
and `C<T>` is a type, `C { … }` a literal, `c.f` a projection, exactly as
for any record — including a **dependent** field (a law mentioning earlier
fields), which is the Σ spine's own property.

The registry entry is `ClassInfo { params, fields (flattened, in order),
parents (direct), ancestors (transitive, deduped, in a deterministic
order) }`, keyed by the class's qualified name. Consumers arrive in layer 2;
this round's own consumer is `extends` and the instance assembler.

## 3. `extends`: flattening by renaming

The child's field list is

> ancestors in deterministic order (depth-first over `parents`, deduped by
> class name, each contributing its own **already flattened** field list),
> then the child's own fields.

deduped by field name, first occurrence winning. Two *unrelated* ancestors
contributing the same field name is a declaration error naming both — the
dedup exists to collapse a shared ancestor reached by two paths, not to
silently merge two different notions.

Instantiating a parent's fields at the child's arguments is therefore a
**renaming** of the parent's type-parameter names, which is why §1 restricts
`extends` arguments to bare type parameters of the child. The general case
(`extends P<List<A>>`) needs a substituting walk that puts an arbitrary `Ty`
where an `Expr`-position name stands, and nothing in the acceptance corpus
or in Mathlib-shaped algebra asks for it; it is refused by name rather than
half-supported. Recorded as residue, not as a limitation of the scheme.

## 4. Instances: the canonical name, the namespace, the value

### 4.1 The canonical name

**`{Head}::{Class}`**, where `Head` is the head name of the class's *first*
type argument (`Rat`, `Nat`, `Pair`, `List`). So `instance Monoid<Rat>`
mints the global `Rat::Monoid`, and that single name is at once

- the **instance value** (a `fn` returning `Monoid<Rat>`), and
- the **namespace prefix** of its block members (`Rat::Monoid::op`).

It is a deterministic function of (class, carrier syntax), so minting is
idempotent and order-independent — §12's content-addressing requirement.
It is *coarser* than §12 asks: two instances of one class whose carriers
share a head (`Monoid<Pair<A, B>>` and `Monoid<Pair<Nat, Nat>>`) collide.
That collision is a **declaration error naming both**, not a silent
overwrite. (Two carriers whose heads share a *name* across modules do not
collide — that is the registry **key**, which is resolved rather than
written as of 2026-08-17: `docs/instance-resolved-key-design.md`. This
paragraph is about the minted name, which is still the written head's.) The narrowing is deliberate and is recorded in §7.1: at layer 1
a *spellable* canonical name is worth more than distinguishing carriers no
layer-1 program can select between, and the full (class, carrier-syntax)
key is layer 2's — it is the resolver's canonical-derivation table that
needs to tell `Monoid<Pair<Nat, Nat>>` from its generic parent, and that
table does not exist yet.

`Head` must name a type in scope (`names_a_type`), which is exactly the
existing member-attachment check: `Rat::Monoid` is an ordinary type-owned
member declaration and inherits the whole `docs/modules-design.md` §4 name
regime for free (locals beat unlisted imports, two modules declaring one
instance are ambiguous at use with both origins named).

### 4.2 Block members

Each `fn`/`theorem` inside the block becomes one synthesized `ast::Decl`
handed to `elab_decl`, **in order**, with

- name `{prefix}::{written name}`,
- type parameters = the instance's `<…>` ++ the member's own,
- parameters = the instance's `requires` binders ++ the member's own.

Everything after that is the ordinary declaration path: the kernel gate, Ψ
registration, `ParamMeta`, implicit insertion, `self`-receiver marking.

**Within-block references.** While a block is being elaborated, an
unqualified name that is an *earlier member of this block* resolves to that
member's global. One table, consulted in `lookup_global`, cleared at the end
of the block. This is the whole of the "later members use earlier members by
name" promise (record §3), and it is a **name** rewrite only: in a *generic*
instance the `requires` binders are ordinary explicit parameters (record §6:
layer 1 has no resolution), so a cross-member call must pass them —
`op(ma, mb, x, y)`. Layer 2 is what makes them implicit and fills them; the
rule stated here is the honest layer-1 one and is pinned by a test.

**Members are reached by projection, not by their three-segment name.**
`Rat::Monoid::op` is registered and resolvable by the elaborator, but the
lexer joins exactly one `::` (`crates/syntax/src/lexer.rs`), so the string
is unwritable in source. It does not need to be: the instance value is a
record whose `op` field *is* that global, so `Rat::Monoid.op` reaches it and
is definitionally equal to it. Lifting the lexer's one-join rule is filed as
residue; nothing here depends on it.

### 4.3 The value

Assembled at the end of the block as one more synthesized declaration:

```
fn {prefix}<instance tyvars>(requires …) -> Class<args> {
    Class { f: ⟨value of f⟩, … }
}
```

with `⟨value of f⟩`, in order of preference:

1. the block member `f`, referenced by its full name — bare when the
   instance has no `requires` binders, applied to them when it has (type
   parameters stay implicit and are inferred from the expected field type);
2. the literal form's written `f := e`;
3. **fill-by-reference** from an already-registered canonical ancestor
   instance at this carrier: `Var({ancestor prefix}).f`. Only an
   *unparameterized* ancestor qualifies — a generic instance's value is a
   function, and deciding what to apply it to is resolution (§8);
4. otherwise: the missing-field error, which is the record literal's own,
   listing what is missing.

Rule 3 is the parent-first half of §4's direction symmetry.

### 4.4 Canonical parents

After the child's value is registered, every ancestor `P` of the class that
has **no** canonical instance at this carrier is synthesized and registered:

```
fn {Head}::{P}<tyvars>(requires …) -> P<args> { P { f: ⟨same value as the child used⟩, … } }
```

— the child-first half. The values are literally the same expressions, so
every projection path reaches the same components and a diamond collapses by
construction rather than by discipline. Ancestors are visited in the
deterministic order of §3, so a grandparent is minted once and reached the
same way from both parents.

### 4.5 Overrides owe agreement

If the block defines a field `f` that an already-registered ancestor
instance also holds, the declaration owes agreement (record §4). It is
discharged by synthesizing

```
theorem {prefix}::{f}#agrees<tyvars>(requires …)
    : ⟨the override⟩ = ⟨the ancestor's projection⟩ { refl }
```

which is precisely "kernel-checked convertibility at declaration time" — the
`refl` is checked by the kernel's conversion through the ordinary
declaration gate, and it leaves a real certificate in Ψ rather than a
side-effect. A failure is re-wrapped as an override-disagreement diagnostic
naming the field, the class and the ancestor.

The propositional-equality fallback for overrides conversion cannot reach
(record §12) is *not* built: at layer 1 the writer's escape is to not
override.

## 5. What layer 1 does not build

No resolution or search of any kind, no `:= infer`, no `let instance`, no
modes/overlap/termination checks, no operator migration, no
generic-carrier method dispatch. `requires` binders are explicit
parameters. An instance is an ordinary record value and is used by being
named.

## 6. Acceptance

Per `docs/testing-generated-terms.md`, varying an **open** carrier, a
**checking** position, a **neutral** receiver and a **negative control**
for each positive:

1. Prelude-shaped classes over `Option`/`Result`/`List`-like carriers,
   including a dependent (law) field, used through an open type parameter.
2. `AddMonoid → AddGroup`/`AddCommMonoid → AddCommGroup`: parent-first
   fill-by-reference, child-first synthesis, and an override with
   agreement — plus the negative control where a disagreeing override is
   refused at the declaration.
3. **Diamond collapse**: the shared ancestor's projection reached along
   both paths is the same value, by `refl` at a neutral instance.
4. Generic instance as a value: `instance<A, B> Monoid<Pair<A, B>>
   requires …` is a dictionary-valued function; applying it and projecting
   computes.
5. The literal form assembles from previously declared globals.
6. Negatives: unknown class, wrong argument count, duplicate instance at a
   carrier head, an `extends` argument that is not a type parameter,
   unknown/missing/duplicate field in the literal form, a mixed body.
7. The full suite green, `lib/ir_v1.hthr` unchanged.

## 7. What implementing this corrected

### 7.1 The canonical name is keyed on the carrier *head*, not the carrier

Recorded above (§4.1). `docs/traits-design.md` §12's content-addressed
minting is keyed on (class, carrier-syntax); layer 1 keys on (class,
carrier head) and refuses collisions. Evidence: the name has to be
*spellable* for the instance to be usable at all in a layer without
resolution, and a spellable name cannot carry a rendered type argument
(`Monoid#Pair<A,B>` is not an identifier). No layer-1 program can select
between two instances at the same head anyway — there is no resolver to
select with — so the refusal costs nothing it could have used, and layer 2
inherits the full key with the table that needs it.

> **Amended 2026-08-17** (`docs/decide-class-design.md` §2). Two things this
> section says have to be read more carefully now that layer 2 exists.
>
> First, what the head key is *for*. It mints the canonical name and it detects
> duplicates — and that is all. The resolver filters candidates on the **class
> key alone** and selects by elaborating each against the goal, so the carrier
> head never enters a search. A reader reaching this section to find out why
> some carrier will not resolve is in the wrong place: it will not be this.
>
> Second, the "spellable" evidence has partly expired, because layer 2 does
> have a resolver. What survives is the weaker requirement that the name be an
> *identifier*, which head-keying still satisfies.
>
> **Amended again 2026-08-17** (`docs/instance-resolved-key-design.md`). The
> key's carrier component is the head's **resolved declaration** —
> `int::Le`, `nat::Le` — and not its written name, so "two carriers with the
> same head collide" is no longer true and §4.1's paragraph about it describes
> a scheme that is gone. The *canonical name* is still built from the written
> head, which is what this section is about; identity and naming came apart,
> and that is the whole change.
>
> The head may now be a **type former** as well as a declared type, so
> `Not::Decide` and `Le::Decide` are canonical names. §4.1's "`Head` must name
> a type in scope (`names_a_type`)" is now `names_a_carrier` — a type, or a
> global whose result after every argument is a universe — and it is applied at
> the member-declaration check, so a type former owns a namespace like any
> other owner. An **equation** carrier is still refused, deliberately: that one
> genuinely wants the full key (§8's first residue item), and
> `issues/decidable-equation-carrier.md` owns it.

### 7.2 `extends` at a non-parameter argument is refused, not lowered

Recorded above (§3). The restriction pays for itself twice: instantiating a
parent's stored fields is a rename, and instantiating a parent's *ancestor
list* at an instance's carrier is a positional lookup rather than a
substituting walk.

### 7.3 A member reference writes its type arguments explicitly

The scheme said the instance's type parameters "stay implicit and are
inferred from the expected field type" (§4.3 rule 1 as first written). They
cannot be: the reference is a **partial** application — the member still
wants its own arguments — and the applicator refuses to mix partial
application with implicit insertion
(`docs/unifier-completeness-design.md` §5.3, `apply_implicit`'s doc
comment). The reference is therefore emitted as `f<A, B>(ma, mb)`: leading
type arguments are consumed by the `param_offset` route, and the remaining
mask may legitimately be a prefix. §4.3 above is written as implemented.

This is invisible at the surface — the writer still writes `op(x, y)` — but
it is the reason a generic instance's assembled value works at all, and it
would have been rediscovered by whoever next emitted a partial application
of a polymorphic global.

### 7.4 An instance is all-or-nothing, by snapshot

An instance emits many globals (members, the value, synthesized parents,
agreement certificates), and the house discipline is that a failed
declaration registers nothing (`check_source`'s recovery). A failure at the
value or at an agreement certificate would otherwise leave the members
behind, so `elab_instance` clones the elaborator on entry and restores it on
failure — which is what the `Clone` impl's own doc comment says the clone is
cheap *for*. Pinned by `a_failed_instance_registers_nothing`, which observes
it the only way it is observable: the same instance declared twice, the
first failing, the second landing on the same names.

## 8. Residue for layer 2 (and one for the lexer)

- **The full canonical key.** (class, carrier-syntax) rather than (class,
  carrier head) — owned by layer 2's canonical-derivation table (§7.1).
  **Answered in its cheap form** by `docs/instance-resolved-key-design.md`
  (2026-08-17), which takes the step this entry did not see was available:
  the *key* never had to be spellable, only the *name* did, so the key became
  a tuple of **resolved declaration references** — (class key, carrier-head
  key, index spelling) — with no component a surface spelling. That is what
  `nat::Le` and `int::Le` being two carriers means, and it needed no
  canonical-derivation table. What is left of this item is the one named
  customer: an **equation** carrier, which has no head to resolve
  (`issues/decidable-equation-carrier.md`, whose cost that round shrank —
  it now wants a carrier entry and its UX, not a new notion of key).
- **Three-segment names are unwritable.** ~~`Rat::Monoid::op` is registered
  and resolvable but not lexable: the lexer joins exactly one `::`.~~
  **Retired** by `docs/instance-resolved-key-design.md` §5 (2026-08-17): the
  lexer joins a **chain**, so `Rat::Monoid::op` and `int::Le::Decide` are
  writable verbatim. The projection spelling stays and is the same value —
  §4.2's claim, now pinned by a `refl`. The paying customer was the qualified
  canonical name, which is the *printed* form of a registry entry and so owed
  `docs/repr-access-spellings-design.md` §2's invariant.
- **Receiver dispatch through an instance.** `member_bases` records a
  member's base name, and an instance member's base under the current scheme
  is `Monoid::op`, not `op`, so `x.op(y)` does not reach it. The concrete
  carrier case would need `member_head` to try `T::C::op` for each class `C`
  with an instance at `T`; the generic case needs receiver sugar to consult
  in-scope dictionaries, which `docs/traits-design.md` §12 already assigns to
  layer 1/2 ergonomics. Neither is built here. **Retired** by
  `docs/traits-receiver-dispatch-design.md` (2026-08-07), which builds both as
  one route and takes neither guess above: dispatch is a resolution goal
  `C<typeof(x)>` handed to layer 2, so the concrete carrier is answered by the
  registry rather than by a `T::C::op` lookup, and the generic one by the scope
  search that already existed.
- **A parameterized canonical parent** offers neither fill-by-reference nor
  an override-agreement partner, for the reason in §4.3: applying its value
  needs the resolver. A generic child of a generic parent therefore writes
  the inherited fields itself, and the missing-field error says which.
- **`requires` binders become instance-implicit at layer 2**, which is what
  turns §4.2's cross-member rule from "pass them" into "they are found".
