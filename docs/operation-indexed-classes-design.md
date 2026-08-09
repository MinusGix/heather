# Operation-indexed classes: design record — `Monoid<A>(op)`

Status: **design pass**, the third entry in the traits-line order agreed at
session close 2026-08-07 (`issues/frontend-roadmap.md`), designed with the user
2026-08-09. Owner: `issues/operation-indexed-classes.md`. Constraints:
`docs/traits-design.md` (classes are parameterized records; the canonical-value
discipline), `docs/traits-layer2-design.md` (the search order, trial-checked
selection, trace-as-data), `docs/traits-owner-dispatch-design.md` and
`docs/traits-named-upcast-design.md` (owner keying, upcast, read-through),
`docs/traits-type-projection-design.md` §6 (the boundary this design was asked
to answer). The operators round is *behind* this document and consumes §7.

This is a decision record, not a round slice: §13 cuts it into implementing
rounds with their own acceptance lists.

---

## 1. The problem, in one line

One instance per (class, carrier) makes the *choice of structure* part of the
class system, and every cost in the current library is that choice's rent:
`lib/std/algebra.hthr` maintains an additive hierarchy
(`AddSemigroup → AddMonoid → AddCommMonoid`) that is `Semigroup`/`Monoid` with
the fields renamed, proves `plus_zero_of_comm` against only that spelling,
exiles Bool's second monoid to a named value the resolver cannot see
(`bool_or_monoid`), and spends its longest comment block justifying which
structure got nominated. Lean pays the same rent at scale: a bundled hierarchy
*and* a predicate-class hierarchy (`Std.Associative`) stating every law twice,
glue instances between them, and `to_additive` — a metaprogram whose entire
purpose is to duplicate lemma libraries across operation spellings.

The user's insight (2026-08-07, recorded on the issue): the operation is
**relevant data recovered from usage, exactly like the carrier type**.
`Monoid<R>` is really `Monoid<R, op>`.

## 2. The decision, in one sentence

> **The operation moves from field to index — `class Monoid<A>(op)` — and the
> indexed class is the *only* law-bearing form: there is no bundled companion
> class, and there are no default instances.** A value index is filled by
> unification, by a scope binder, or by a designation the binder names (§7) —
> never by search, never by priority — and a goal whose value slot survives
> all three is refused by name.

Everything below is this sentence's consequences, plus the two obvious
alternatives (§9) and why each lost.

### 2.1 What is an index and what is a field

The rule: **index what identifies the structure; field what the structure
provides.** For a monoid the operation identifies it — `Monoid<Nat>(add)` and
`Monoid<Nat>(mul)` are different structures and now different *types* — while
the unit is determined by the operation (propositionally, and at every concrete
instance definitionally: `Nat::Monoid(add).unit` reduces to `0`), so it stays a
field. Nothing forces a class to have indices: `Default<A>` and `Cmp<A>`
identify their structure by the carrier alone and stay exactly as they are.
Indexing is opt-in per class by writing value parameters, which records already
have (`record CompileNat2(f: Nat -> Nat -> Nat)`, the precedent the issue
names) — **there is no second class form in the language.** The "two styles"
the issue's synthesis predicted turn out to be one form and a per-class choice
about its parameter list.

## 3. Class and instance declarations

```heather
class Semigroup<A>(op: A -> A -> A) {
    assoc: (x: A) -> (y: A) -> (z: A) -> op(op(x, y), z) = op(x, op(y, z)),
}

class Monoid<A>(op: A -> A -> A) extends Semigroup<A>(op) {
    unit: A,
    unit_l: (x: A) -> op(unit, x) = x,
    unit_r: (x: A) -> op(x, unit) = x,
}

class CommMonoid<A>(op: A -> A -> A) extends Monoid<A>(op) {
    comm: (x: A) -> (y: A) -> op(x, y) = op(y, x),
}
```

The class is still a parameterized record — the value parameter is an ordinary
record value parameter, and `op` is in scope in every field type exactly as `A`
is. `extends` names the parent *at an index*, and a single-op chain passes its
own index up unchanged; flattening, the canonical-value discipline, synthesized
parents and owner-keying are all inherited verbatim, with the index riding
along. (The multi-op case, where one parent is instantiated twice, is §8.)

Instances name their index in the head:

```heather
instance Monoid<Nat>(add) {
    unit := 0,
    assoc := add_assoc,
    unit_l := add_left_zero,
    unit_r := λ (x: Nat) => refl,
}

instance Monoid<Bool>(and) { unit := True,  assoc := and_assoc, unit_l := and_true_l,  unit_r := and_true_r }
instance Monoid<Bool>(or)  { unit := False, assoc := or_assoc,  unit_l := or_false_l,  unit_r := or_false_r }

instance<A> Monoid<List<A>>(append) { unit := Nil, assoc := append_assoc, unit_l := λ (xs: List<A>) => refl, unit_r := append_nil }
```

Both Bool monoids **register**, as equals. Neither is "the" one; nothing in
the system ever has to pick between them, because no goal with an unpinned op
ever reaches the registry (§5). `bool_or_monoid`, the named-value workaround,
becomes a declaration — which is the "declared properly rather than as a
disconnected function" the user asked for, without the nomination that today's
coherence policy extracts as the price.

### 3.1 The registry key

Layer 1's overlap key extends from (class, carrier-head) to **(class,
carrier-head, index-spelling)**: two instances at one key are the same
duplicate-declaration error as today, two at different indices coexist. The
index in an instance head must be **spellable** — a global reference, possibly
applied to the instance's own type parameters (`append` at `List<A>` above) —
so the key is computable from the declaration alone. An arbitrary λ in an
instance head is refused at declaration with the rule stated; a structure
built from an unnamed operation is what *scope* is for (a `let`-bound record
value, exactly as `any_of` shadows today).

Ground-goal lookup matches the index **syntactically first** (whnf-head of a
global reference), and falls back to layer 2's trial with the conversion check
it already performs — so an eta-expanded op or a definitionally-equal alias
(`plus := add`) still finds the instance, at conversion price, and the trace
says the match was by conversion (§11). The trial route being
"accidentally future-proof here" was the issue's own observation; the keyed
path is the fast lane in front of it, not a replacement.

## 4. Constraint binders bind the indices

Today `<A: Monoid>` desugars to one implicit solver parameter. At an indexed
class it desugars to **the index binders, then the instance binder over
them** — the index under its *declared* parameter name:

```heather
fn mconcat<A: Monoid>(xs: List<A>) -> A
// desugars to
fn mconcat<A>(#op: A -> A -> A, #m: Monoid<A>(op) := infer)(xs: List<A>) -> A
```

`#op` is an ordinary implicit binder — filled by unification, like a type
argument, *not* a solver parameter — which is the direct realization of the
insight in §1: the op rides exactly the machinery the carrier type already
rides. Inside the body, `op` is an **ordinary bound variable**:

```heather
fn mconcat<A: Monoid>(xs: List<A>) -> A {
    match xs {
        Nil => A.unit,                 // scope answers Monoid<A>(?op): the binder pins op
        Cons(h, t) => op(h, mconcat(t)),   // no dispatch, no projection — a variable
    }
}
```

The recursive call's own `#op`/`#m` fill from the binders in the room, the
existing behavior. The index binder's name is the class's declared one, so it
is referenceable, shadowable by the normal rules, and collides with a
same-named explicit binder the way any two binders do — the diagnostic for
that collision names the class parameter it came from (the `#`-prefix
discipline from the inline-constraint round is the hook, as there).

Generic laws are stated over the binder and **proved once per theory, not per
spelling**:

```heather
theorem op_unit_of_comm<A: CommMonoid>(x: A): op(x, A.unit) = x {
    trans(A.comm(x, A.unit), A.unit_l(x))
}

theorem nat_add_zero(x: Nat):   add(x, 0) = x      { op_unit_of_comm(x) }
theorem bool_or_false(x: Bool): or(x, False) = x   { op_unit_of_comm(x) }
theorem bool_and_true(x: Bool): and(x, True) = x   { op_unit_of_comm(x) }
```

The three corollaries are the whole payoff in miniature: one proof, three
structures, two of them on one carrier — the sentence the additive hierarchy
existed to fail to say. At each corollary the goal pins `op` by unification
(`add`, `or`, `and` are *in the stated goal*), the ground goal
`CommMonoid<Bool>(or)` hits the registry key, done. **Instance search never
sees an unpinned op in theory use, because a law's statement mentions its
operation — that is what a law is.** The inference worry lives entirely on the
program side, where §5's ladder answers it by refusing rather than guessing.

## 5. The resolver's value-slot ladder

Layer 2's search order (scope ascending, then registry, upcast where the goal
is at an ancestor) is unchanged. What this design adds is a rule about **value
slots**, checked where the goal is built:

> A value slot in a goal is filled by, in order: **(1) unification** — the
> slot is already ground when the goal forms, the normal theory case; **(2) a
> scope binder** — a local of the goal's class whose own index pins the slot,
> which is both the generic-code case (§4's binders) and the local-override
> case (a `let`-bound record value); **(3) a designation the constraint binder
> names** (§7). A goal whose value slot survives all three is **refused by
> name** — the refusal states the slot, the class, and every registered
> instance that *would* answer, as data.

There is no step in which the resolver chooses among instances to fill a value
slot. No priority, no specificity ordering, no "default" — the ladder's three
sources are all *deterministic* (unification has one answer, scope has an
innermost, a designation table has at most one entry), so the first
non-priority property of layer 2 ("selection is by checked trial, and overlap
is a declaration error") survives value indices untouched.

Two consequences worth stating because they are the design's teeth:

- `mconcat(ns)` with nothing pinning the op is an **error**, and the library's
  answer is to spell it: `fn sum(ns: List<Nat>) -> Nat { mconcat(add, ns) }`
  — or the designation form once §7 lands. `all_of` is the fold under `and`,
  `any_of` under `or`, symmetric declarations at last; the `let`-shadow trick
  `any_of` uses today becomes the honest explicit index.
- **The coherence question dissolves rather than moves.** The header essay in
  `algebra.hthr` — why conjunction is THE Bool monoid, why `Monoid<Nat>` must
  share its `op` with the additive chain so two readings of a fold agree —
  exists because the registry had to nominate one structure per carrier. Under
  the ladder nothing nominates, so there is nothing to justify. The deleted
  comment is the design's best single argument for itself.

### 5.1 The dot sugars under the ladder

`T.f` and `x.f(ȳ)` at a member of an indexed class build the goal at the
owner with a **meta in the index slot** — `Semigroup<T>(?op)` — and ride the
same ladder: scope may answer (inside `<A: Monoid>`, `A.unit` and
`x.assoc(y, z)` work, pinned by the binder), and with no scope answer the goal
is refused by name. This **supersedes the flat refusal** recorded at
`docs/traits-type-projection-design.md` §6: the projection round, written
before this design, said "refuse when value indices land"; the decided rule is
*scope first, then refuse*, which is not new machinery — it is layer 2's own
order with the refusal at the ladder's end — and the refusal inherits §6's
diagnostic shape (the multi-parameter narrowing's message, extended with the
value-index case). Receiver dispatch on the *index name itself* (`x.op(y)`)
never fires at all: `op` is not a field of any class, so the cheap negative
test (`class_members`) already excludes it, and inside generic code the binder
variable is the spelling.

`T::C` gains its arguments: **`Nat::Monoid(add)`** is the goal
`Monoid<Nat>(add)`, resolved — the projection round's residue ("`T::C` takes
no arguments", filed on `issues/traits.md`) is discharged by this design,
since an indexed class otherwise has no short dictionary spelling at a carrier
with two structures. Same fallback position in `resolve`, same
value-not-dot-rule character, one grammar addition (an argument list on the
qualified name).

## 6. Perf posture

Nothing in this design adds a conversion the current machinery doesn't
perform. The keyed fast path (§3.1) means two instances at one carrier cost a
key comparison, not two trials; the conversion fallback is entered only on a
syntactic miss, and its price is the trial layer 2 already pays. The
upcast/read-through machinery (`docs/traits-named-upcast-design.md`) applies
verbatim to single-op `extends` chains — the index is one more component that
rides the child's flattened record, and dispatched projections still read
through to the child's own slot. The watch item is §8's multi-op flattening
(more components, two parent assemblies at different indices); it gets a
measurement gate in its own round rather than a guess here.

## 7. The designation interface: `Monoid(+)` — specified here, built by the operators round

The one legitimate customer that §5's ladder leaves unserved is the *author
who wants a symbol*: a fold whose op "is whatever `+` means at the carrier."
The answer is a **designation table** — per (symbol, carrier-head), one entry,
duplicate declaration is an error, generic entries allowed — and a binder form
that names it:

```heather
fn sum_all<A: Monoid(+)>(xs: List<A>) -> A {
    match xs {
        Nil => A.unit,
        Cons(h, t) => h + sum_all(t),
    }
}
```

`<A: Monoid(+)>` binds the index as in §4 *and* (a) fills it, when unification
leaves it open at a call site, by the designation of `+` at the caller's
carrier, and (b) installs the binder as the local meaning of `+` in the body.
At a `Nat` call site `+` designates `add`, the goal grounds to
`Monoid<Nat>(add)`, the registry answers. The designation is not a default
instance: the *source is named in the signature*, per symbol, by the author —
there is no table consulted that the code doesn't point at, and no candidate
set to prioritize.

This document **specifies the interface and defers the implementation** to the
operators-onto-classes round, which needed exactly this table anyway; until it
lands the explicit-index spelling (`mconcat(add, ns)`) is the library's form,
legal forever. Deliberately left to that round: the declaration syntax for
designations; whether non-symbol names can be designated (a designation for
`op` itself was considered and set aside — it is default instances wearing a
smaller hat, and the argument in §9.2 applies); and whether `+` designations
and any operator *class* the round wants are one table or two.

## 8. The diamond: multi-op classes

`Semiring<A>(add, mul)` wants `CommMonoid<A>(add)` **and** `Monoid<A>(mul)` —
the same parent twice at different indices, so flattening collides `unit` with
`unit`. This is where Lean's name-distinct duplication (`Monoid` beside
`AddCommMonoid`, maintained by `to_additive`) would sneak back in, and the
design direction is to stop it at the door:

> **Qualified flattening.** `extends CommMonoid<A>(add) as additive,
> Monoid<A>(mul) as multiplicative` — the child's flattened record holds both
> parents' fields, names qualified by the `as`-tag *where they collide*
> (`additive.unit`, `multiplicative.unit`) and unqualified where they don't
> (`comm` — only one parent has it — autolinks bare). Upcast to either parent
> assembles from the tagged slots by the same canonical-value discipline; laws
> in the child's own block state distributivity over `add` and `mul` directly,
> so qualified paths only ever *fetch proofs*, never appear in statements —
> which is what keeps the issue's explicit-projection skepticism answered.

The recorded alternative, **structures as fields** (`add_m:
CommMonoid<A>(add)` as a dependent field, no `extends`), dodges the collision
at the cost of a path on every fetched law; it stays the fallback if qualified
flattening meets something this pass didn't foresee. Held deliberately loosely:
this is the section that most deserves an adversarial pass in its implementing
round, it is **not needed for round one** (§13), and the round that builds it
inherits §6's measurement gate.

## 9. Rejected alternatives, with reasons

Both rejects were the design's own earlier drafts, in order; this section is
why each lost to its successor.

### 9.1 The bundled companion class (`DefMonoid<A>`, a dependent pair)

The first synthesis: indexed classes own the laws, and a bundled
`class DefMonoid<A> { op: A -> A -> A, is: Monoid<A>(op) }` — a dependent
field pair, which records support — serves programs, receivers, and the
registry's one-per-carrier coherence. It improves on Lean's split (laws stated
once, bundled *contains* indexed, no glue, no `to_additive`) and it lost
anyway: it is a **parallel surface** — every generic function chooses a side,
the sugars work at one class style and not the other, the library carries two
spellings of "monoid" forever — and its entire job list (§2's sentence) turned
out to be servable by the binder desugaring, the ladder, and the designation
table without a second class existing. It survives as a *pattern*: anyone can
write that record; the language just doesn't bless it.

### 9.2 Default instances

The second draft: no wrapper class, but a per-(class, carrier) `default
instance` designation the resolver consults when a value slot survives
unification and scope. Rejected on the user's instinct (2026-08-09), and the
instinct was right for a reason the draft only half-saw: a default table
**keeps the nomination question alive** — which structure is THE monoid on
Bool — and hangs a silent-resolution hazard plus an eventual priority system
off it. Deleting it deletes the question: §5's ladder has no step where the
system prefers one registered instance over another, and the coherence essay
in `algebra.hthr` becomes deletable prose rather than a policy with a
mechanism behind it. What defaults were *for* is covered better: theory never
needed them (op is in the goal), generic code never needed them (op is in the
binder), and call sites that want brevity get it from a designation whose
source is named in the signature (§7) rather than looked up behind the code's
back.

### 9.3 Canonical structures (noted, not drafted)

The Coq/math-comp move — key structures to the carrier's *presentation* so
unification recovers the instance from the type — answers the same question
from the opposite end and was never a candidate here: it wants carrier types
rebuilt as projections of structure packages, which fights every existing
kernel type, the whole frontend, and the trial-checked resolver. Recorded so
the comparison is on file, not because it was close.

## 10. What the library becomes

`lib/std/algebra.hthr` after round one (§13), sketched:

| today | after |
| --- | --- |
| `class Semigroup<A> { op, assoc }` (op a field) | `class Semigroup<A>(op) { assoc }` |
| `AddSemigroup`/`AddMonoid`/`AddCommMonoid` | **deleted** — `CommMonoid<A>(op)` is the one chain |
| coherence header essay | **deleted** — nothing nominates (§5) |
| `instance Monoid<Bool>` (conjunction nominated) | `instance Monoid<Bool>(and)` — an equal |
| `fn bool_or_monoid() -> Monoid<Bool>` | `instance Monoid<Bool>(or)` — registered, findable by op |
| `plus_zero_of_comm` (additive spelling only) | `op_unit_of_comm` — once, spent at `add`, `and`, `or` |
| `any_of` `let`-shadows the registry | `mconcat(or, bs)` — the index, spelled |
| `mconcat<A: Monoid>` + receiver `h.op(…)` | `<A: Monoid>` + `op(h, …)` — a variable (§4) |
| `nat_plus_zero`, `bool_plus_zero` | corollary one-liners of `op_unit_of_comm` |
| `Default`, `Cmp`, `or_default`, `max_of*` | **unchanged** — unindexed classes are untouched |

On the naming worry (user, 2026-08-09): concrete-carrier lemma names
(`add_assoc`, `or_comm`) are not a cost this design adds — they are the
existing, correct state of `std/nat`, and instances *package* them
(`assoc := add_assoc`), which does not change. What reverses direction is
derived laws only, and there the per-carrier names are corollary one-liners
(§4) — cheap to write, systematic (`Nat::Monoid(add).assoc` is a spelling for
free), and the natural first customer for a per-instance corollary generator
when `generators-in-the-language` gets there. No alias mechanism is designed
now; demand files the issue.

## 11. Diagnostics

Trace-as-data throughout, no new vocabulary beyond one word for the ladder:

- **A value slot survives the ladder** → refusal naming the slot, the class,
  the ladder steps tried (unification residue / no scope binder / no
  designation named), and **every registered instance that would answer**, as
  data — at Bool, both monoids, each with its index. Where a designation for a
  relevant symbol *exists* at the carrier, the refusal names it and spells the
  binder that would use it (`Monoid(+)` at `Nat` designates `add` — polish,
  but it is the difference between a refusal reading as principled and as
  obtuse).
- **Duplicate key** (§3.1) → the duplicate-instance error, now naming the
  index as part of the key.
- **Unspellable instance-head index** → refused at declaration with the rule
  and the scope alternative stated.
- **Conversion-matched key** (§3.1) → the trace records that the index matched
  by conversion, not syntactically — the observability hook for the day an
  alias makes a resolution surprising.
- **Index-binder name collision** (§4) → named, with the class parameter it
  desugared from.

## 12. What this assumes from elsewhere, and hands off

- **Modes** (layer 2 residue): this design *narrows* the question instead of
  answering it — value slots are input-moded, always, enforced by §5's ladder.
  A general mode system remains unclaimed by anyone; the issue's note that op
  "is the modes question wearing algebra clothes" resolves as: for algebra,
  the fixed rule suffices.
- **Operators round**: consumes §7 (the designation table and `Monoid(+)`),
  §5.1's `x + y`-as-the-natural-spelling for indexed-class theory, and the
  open questions §7 defers to it.
- **`issues/traits.md`**: owns the residues this discharges or touches —
  "`T::C` takes no arguments" (discharged by §5.1), the multi-parameter
  dispatch narrowing (extended by §5.1's value-index case), and the
  read-through/upcast machinery §6 leans on.
- **Kernel: nothing.** Classes are records, indices are record value
  parameters, instances are record values, resolution proposals are
  kernel-gated as always. No new former, no metatheory obligation.

## 13. Implementing rounds

**Round one — indexed classes end to end.** Value parameters on `class` heads
and single-op `extends` chains; instance heads with spellable indices and the
extended registry key (§3.1); the binder desugaring (§4); the value-slot
ladder with its refusals (§5, §5.1's scope-then-refuse for the dot sugars);
`T::C(args)` (§5.1); the library migration (§10). Acceptance, per
`docs/testing-generated-terms.md`'s axes:

1. **The headline**: one generic law (`op_unit_of_comm<A: CommMonoid>`)
   proved once and spent at three structures, two on one carrier
   (`add` at Nat, `and` and `or` at Bool) — each corollary's goal pinning the
   index by unification alone.
2. **Coexistence**: `Monoid<Bool>(and)` and `Monoid<Bool>(or)` both
   registered; a ground goal at each finds its own; a duplicate at one key is
   the declaration error, naming the index.
3. **The binder**: bare `<A: Monoid>` with the index caller-supplied and with
   it unification-pinned from an argument; the body using `op` as a variable
   and `A.unit` answered by scope; the recursive call filling from the room;
   a generic instance at an **open** element type
   (`instance<A> Monoid<List<A>>(append)`) reached by backchaining with the
   index instantiated.
4. **Refusals as data**: `mconcat(ns)` with nothing pinning the op — the
   refusal names the slot and lists both Bool instances when at Bool; `T.f`
   at an indexed class with no scope binder; the unspellable instance head.
   Each checked for *content*, not just failure.
5. **Keying up to conversion**: an eta-expanded index and a
   definitionally-equal alias (`plus := add`) both finding the
   `add`-keyed instance through the fallback, with the conversion-match
   recorded in the trace; a genuinely different op **not** matching (the
   negative control).
6. **Checking position and neutral scrutinee** where the migrated `mconcat`
   and its lemmas land, per the testing doc; agreement pins: the explicit
   `Nat::Monoid(add).assoc` and the corollary spelling reach one term.
7. Full `scripts/test` (a `lib/` change), suite count recorded.

**Round two — the diamond** (§8): qualified flattening with `as`-tags, a
`Semiring<A>(add, mul)` with distributivity as the exercise, the adversarial
pass this document requests, and §6's measurement gate. Demand-scheduled: no
current library declaration needs two ops.

**Round three — designations and operators** (§7): owned by the
operators-onto-classes round per the standing order; this document is its
input, not its schedule.

Sequencing note: round one supersedes
`docs/traits-type-projection-design.md` §6's refuse-only boundary (per §5.1)
and discharges the `T::C`-arguments residue on `issues/traits.md`; both edits
belong to that round's bookkeeping, not this pass's.
