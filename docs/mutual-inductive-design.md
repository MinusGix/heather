# Mutual inductive families: one family indexed by its members

Status: **implemented** (2026-10-24), for
`issues/mutual-inductive-declarations.md`; written before the code and kept
as what the code does. Code: `crates/elab/src/mutual_family.rs` (§1–§3),
`iwf_family.rs` and `indexed.rs` (§4–§5), `mutual_rec.rs` (§6); tests:
`crates/elab/tests/mutual_inductive.rs`. The kernel route is
`docs/iwf-former-design.md` §12.2's: a group is one `IWf` whose index says
which member a value belongs to and, for an indexed member, at what. Nothing
here adds a kernel rule; the probes of §9 were run against the real checker,
hand-desugared, before any of this was written.

The customer is the heather-coq port (`docs/heather-coq-port-assessment.md`
§4.1): four mutual syntax sorts and seven mutual judgments, where writing the
encoding by hand is not practical.

---

## 1. Surface form: groups are inferred from adjacency

```
inductive Ty {
    Base,
    Arr(a: Ty, b: Ty),
    Box(n: Nat, t: Tm(n)),
}
inductive Tm : (n: Nat) -> Type {
    Var(n: Nat)                        : Tm(Succ(n)),
    Lam(n: Nat, ty: Ty, body: Tm(Succ(n))) : Tm(n),
    App(n: Nat, f: Tm(n), a: Tm(n))    : Tm(n),
}
```

No keyword. A **run** is a maximal sequence of consecutive `inductive` items;
an edge `D → E` is recorded when a constructor field or result annotation of
`D` names `E`; a **group** is a strongly connected component of the run with
more than one member. This is `docs/mutual-recursion-design.md` §1's rule for
`fn` groups, applied to declarations, for the same reasons: no new item, no
parser arm, and a forward reference that is not part of a cycle is the error
it is today. A singleton component is elaborated exactly as today.

What a group requires of its members, each refused with its own message:

- every member is an `inductive` (not `codata`, not `record`);
- the members declare **the same type parameters**, same names in the same
  order, and every occurrence of a member is at those parameters
  (the uniformity rule every recursive occurrence already obeys);
- no value parameters (an indexed family has none either,
  `docs/surface-value-parameters.md` §6);
- each member is **unindexed, or indexed by one binder** `: (n: I) -> Type`,
  with `I` as for a single family (`Nat` or a declared index type). Members
  may be indexed by **different** index types, or one indexed and one not;
- an indexed member's constructors state their result `: D<p̄>(e)`, at their
  **own** member; an unindexed member's constructors state none;
- a member occurs in a field only as the field's whole type — `E<p̄>` for an
  unindexed member, `E<p̄>(e)` for an indexed one. Nested occurrences
  (`List<E>`, `[E; n]`) and function fields are refused, as they are for an
  `IWf`-route family.

## 2. The lowering: a sum of the members' indices

For a group `D_1 … D_k` (first member `D_1`), two declarations are generated
and elaborated by the ordinary routes, and nothing else:

```
inductive D_1#members {                 -- tier 0
    D_1#member(n: I_1),                 -- one constructor per member, carrying
    …                                   -- its index; none for an unindexed one
    D_k#member,
}
inductive D_1#mutual<p̄> : (j: D_1#members) -> Type {
    <every constructor of every member, as written, with each member
     occurrence  E<p̄>(e)  rewritten to  D_1#mutual<p̄>(E#member(e))>
}
```

and each member is a **view** of the family:

```
⟦D_t<p̄>(m)⟧ = ⟦D_1#mutual<p̄>(D_t#member(m))⟧ = IWf(⟦D_1#members⟧; …)(inj_t m)
```

The family is an `IWf`-route declaration (`docs/iwf-former-design.md` §8):
every child sits at a constructor-headed index, so route 1 never applies, and
the `IWf` route has no restriction the rewrite could trip.

**Why a declared sum and not `Σ(tag : Fin k). I_tag`.** The two are the same
index type up to isomorphism; the coproduct `I_1 + … + I_k` is Dybjer's own
presentation of a mutual family. It is the better spelling here because the
dependency of the index on the tag *is* the sum's: there is no type-valued
function `tag ↦ I_tag`, so the index types need no codes, and a `match` on
the member is the index type's own eliminator, which the `IWf` route's
inversion (§8.3 there) already uses. The `Σ` form needs `I_tag` as codes and a
convoy on `fst j` (§12.2 there) to say what the sum says by construction.

**Nominality.** `D_1#members` and `D_1#mutual` each get a nominal tag; the
members do not need one, since a member is identified by its index
constructor, which belongs to `D_1#members` and to nothing else.

**What is recorded.** The family's `Inductive` carries its `members` (name,
index binder, constructors), which the module image encodes and its
validation checks partition the constructors; each member is registered by
name beside the family, so a written `Tm(n)` resolves to the view and a
`match` on it knows its member. A family instance prints as the member
(`Tm(n)`, `Ty`), and a constructor value as itself (`Arr(a, b)`), in goals
and messages alike.

## 3. Constructors

A constructor is its family's constructor, built by the `IWf` route
unchanged: `sup_i(inj_c(stored fields); ⟨children⟩)`, each child checked at
the member view its field names. A constructor in checking position at
`D_t(m)` checks its written result `D_t#member(e)` against `D_t#member(m)` by
one conversion, which is `IWf`'s rule; at the wrong member the conversion
fails at the index constructor's tag, and the message names both members.

## 4. `match`: per member, by inversion on the member

A scrutinee `z : D_t(m)` is at the index `D_t#member(m)`, which is
constructor-headed, so the `match` takes the `IWf` route's tier-1 inversion
(`docs/iwf-former-design.md` §8.3): the motive cases on the index by
`D_1#members`' eliminator, every other member's constructors land on `Unit`,
and their arms are neither written nor accepted (an arm for another member's
constructor is an error naming the member it belongs to). The member's own
constructors see their goals at their own indices, and β is definitional.

**Inversion is per level.** Within the member's branch the inner index `m`
gets the member's own tiers, exactly as a single family would:

- a variable `m` is abstracted (`Tm(n)`: the arms see `Tm(o_c)`);
- a constructor-headed `m` whose member's constructors all have
  constructor-headed result indices is inverted again, by `I_t`'s eliminator
  (`Even(Succ(n))`: the `Even(0)` arm cannot occur);
- anything else is left as written (tier 2's abstraction, then the constant
  motive), and the kernel judges the candidate as it does today.

So the existing one-level inversion becomes a recursion over the index's
constructor structure. Each level is the old rule; what is new is only that a
branch's code can itself be a case. Single families gain the same depth
(`V(Succ(Succ(n)))` against a family indexed by a declared index type), which
is a strict extension: a motive that inverted before inverts identically.

One detail makes the nesting work. A tier-0 branch's goal mentions the
index *value* `inj_c(v)`, while the level below abstracts the branch's
projections of `v`. So each branch carries `v` and its rebuilding from those
projections, `IdxBranch::value`, and the goal is abstracted through the
rebuilt value, which is `v` by η. A `_` arm expands to the member's own
constructors, never to the family's.

## 5. Recursion on one member

A structurally recursive `fn` on one member is the `IWf` route's recursion,
unchanged: a self-call on a child at the same member is the child's ih, whose
type is the motive at the child's index, `D_t#member(e)`, which reduces to the
goal at `e`. A recursion that varies the member's index (`f(Succ(k), body)`)
rebinds it through the member constructor: the guard's per-child index is the
**inner** index `e`, read off `D_t#member(e)`.

## 6. Mutual recursion over a group: one `elim_IWf`

```
fn size_ty(t: Ty) -> Nat { match t { Base => 1, Arr(a, b) => size_ty(a) + size_ty(b),
                                      Box(n, m) => size_tm(n, m) } }
fn size_tm(n: Nat, t: Tm(n)) -> Nat { match t { … size_ty(ty) … size_tm(Succ(n), b) … } }
```

**Groups.** A run is a maximal sequence of consecutive `fn` (or consecutive
`theorem`) declarations without `decreases`; a group is a strongly connected
component of the run under calls by base name, as in
`docs/mutual-recursion-design.md` §1. A group recurses **structurally** when
each member's body is one `match` on a parameter whose type is a member of
one mutual family, and no two group members recurse on the same family
member. Anything else that is mutual keeps the measure route (`decreases`),
and the refusal says so.

**The lowering**, for a group whose first member is `f`, generated as surface
declarations and checked the ordinary way:

```
fn f#mot<p̄>(j: D_1#member) -> D_1#mutual<p̄>(j) -> Type {
    match j { D_t#member(n_t) => λ t => (x̄_t) -> R_t, … }
}
fn f#rec<p̄>(j: D_1#member, z: D_1#mutual<p̄>(j)) -> f#mot<p̄>(j)(z) {
    match z { <each member's arms, for its own constructors> }
}
fn f_t<p̄>(params_t) -> R_t { f#rec<p̄>(D_t#member(n_t), t)(x̄_t) }
```

- `n_t` is member `f_t`'s **index parameter** (the variable its recursive
  parameter's type is indexed at; none for an unindexed member), `t` its
  recursive parameter, `x̄_t` the rest in declaration order, and `R_t` its
  result type. The motive binds `n_t` by the member pattern and `t` by the
  `λ`, under their own names, so `R_t` and `x̄_t`'s types read as written.
- `f#rec` is one structural recursion on the whole family at a **variable**
  index: one `elim_IWf`, whose step holds every member's arms. Each arm is
  `λ x̄_t => body`, with `n_t` and `t` bound by `let` to the constructor's
  result index and to the constructor itself — this level's values, not the
  top call's — and every self- or sibling call `f_u(ā)` rewritten to
  `f#rec(D_u#member(a_n), a_z, ā_rest)`, which the existing guard lowers to
  the child's ih applied to the rest.
- A family member that no group member recurses on gets the motive `True`
  and the arms `trivial`, so a group need not cover the family.
- Theorems group the same way, with `f#rec` a theorem; a group mixing `fn`
  and `theorem` is refused.
- The motive's universe is the largest level of the members' `(x̄_t) -> R_t`,
  elaborated over each member's own parameters; a universe-polymorphic one
  is refused.

**Which cycles are groups.** A cycle among measure-free declarations is a
group only when one of its members is one `match` on a parameter whose
written type names a mutual member (of this container's groups, or
imported). That is decided from the source before anything is elaborated,
so a group is never formed and then dissolved, and incremental replay, which
keys a group's slice on all its members' source, sees the same grouping as
elaboration. Every other cycle keeps today's behaviour, the forward
reference refusal.

A call counts wherever the body writes it, the types it writes included:
`P ∧ Q` is `And<P, Q>`, so in a `Type`-valued member a sibling call inside a
connective's operand sits in a type argument, and `∀ x: A, P` is a type
literal. The edge scan and the call rewrite both enter written types (a
dependent arrow's binder shadows in its codomain); `∃`'s body is already a
`λ` (issues/mutual-group-type-valued-members.md).

**Errors in the members' terms.** `f#rec` is checked by the ordinary
structural guard, whose messages name the declaration and parameters it
checks. Each rewritten call records its span and callee, and an error from
`f#rec` at a call is reworded: `f#rec`, `#z` and `#j` become the callee, its
recursive parameter and its index parameter.

**Arms.** An arm binds a constructor's fields with plain binders (by
position, or `field := x`); its binders are reused as written unless they
would shadow `n_t`, `t` or a parameter, in which case a fresh binder is used
and a `let` restores the written name. A deep pattern is refused with the
structural guard's own message, which refuses one in any descending `match`.

β is definitional on open data: `f_t(C(…))` unfolds to `f#rec` at a
constructor, the eliminator steps, and each recursive position is
`f#rec(D_u#member(e), c)`, which is what `f_u(e, c)` unfolds to.

**Cost.** The step is a case tree over the shape spine, one arm per
constructor of every member, and each of its Θ(m) case nodes carries its own
convoy motive, which spells the signature's arity, output and child trees
(Θ(m²): the child tree's own convoy motives repeat the arity tree). What
keeps the gate from paying that per node is that none of it reads Γ: the
signature's index leaves are unannotated, so the signature and the motives'
pieces are tail-free, and the kernel's typing memo judges such a node once
per the entries it reads rather than once per Γ. Checking the group is then
about quadratic in the members, and one unfolding by `refl` about linear (β
hands the step its ih as a value, so two unfoldings compare their steps by
identity); `issues/mutual-group-recursion-gate-cost.md` has the measurements.
Since `docs/iwf-named-signature-design.md` the signature is three references
to generated definitions and each motive's ih type one more, so a case node
carries O(1) of it plus the user's motive: about m^1.8, the rest being the
spine's depth.

## 7. What stays refused, and where it is owned

- Indexed families with infinitary premises: their own issue (port
  assessment §4.2).
- Nested occurrences of a member (`List<Tm>`): the nested-inductives issue.
- A member with value parameters, or members with different type parameters.
- A group member whose recursive parameter is at a non-variable index
  (`f(t: Tm(Succ(n)))`): its motive cannot bind the index; the message says
  to generalize the parameter.
- Unfolding companions and `decreases` for a structural group: not needed,
  since β is definitional.
- Implicit, solver and defaulted parameters on a structural group's
  members, method-call spellings of a member (`t.size()`) and members passed
  as values: refused. A call within the group is saturated and positional.
- `rewrite` by an induction hypothesis inside an unfolded goal: the unfolded
  goal holds the recursor, not the member's name, so `rewrite(ih, …)` finds
  no occurrence. This is today's behaviour for any structural `fn` (a plain
  `fn idr` over a `Wf`-route type has it too), not something the group adds;
  a congruence lemma checked by conversion is the workaround the tests use.

## 8. Testing

`docs/testing-generated-terms.md`'s axes, for declarations, `match` and
group recursion each: a literal scrutinee and an open one (β by `refl` on
open data in a theorem, which is also the checking position), an open
element type for a parameterized group, and a negative per positive (an arm
for another member's constructor, a constructor at the wrong member, a
non-uniform occurrence, a group whose members disagree on parameters). One
group has **members indexed by different types** (`Nat` and a declared
index), which is the tag-dependent case the issue asks for, and one has an
unindexed member beside an indexed one.

## 9. Probes (hand-desugared, before the code)

Run against `heather check` on master at 87348e3, with the generated names
written as ordinary ones:

1. A `Ty`/`Tm` family over a declared two-constructor member index type
   checks; a per-member `fn` on `Ty` leaves the `Tm` arms out and computes;
   β at `Arr(a, b)` on open data is `refl`.
2. A combined recursion `rec(j, z) -> Mot(j)` with `Mot` a type-level `match`
   on the member checks, and its wrappers' β on open data, through a sibling
   at a different member and an index `Succ(n)`, is `refl`.
3. A Π-valued motive (`Nat -> Nat` per member) with `λ` arms checks and
   computes: the extra-parameter shape of §6.
4. A dependent motive `Mot(j) -> D(j) -> Type` checks, which is what a
   theorem group needs. Its spelling `Mot(j, z)` with `match j` does not:
   `z`'s type is not refined by the branch (and the kernel, not the
   elaborator, reported it).
5. Today's limits, which §4 and §5 remove: `match` at `EO(WE(Succ(n)))`
   demands the impossible `EZ` arm (one-level inversion), and recursion at
   `Tm(n)` that varies `n` is refused (no rebinding through the member).
6. §6's lowering, hand-written over the probe-1 family (`smot`, `srec`, the
   wrappers): checks, with the arms' `let`s for the index and the
   scrutinee, and its β through a sibling at a different member is `refl`
   on open data.
