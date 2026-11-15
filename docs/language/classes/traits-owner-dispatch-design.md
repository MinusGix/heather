# Owner-keyed dispatch, and upcast in the resolver

Status: **round slice**, retiring `issues/inherited-members-undispatchable.md`.
Constraints: `docs/language/classes/traits-layer1-design.md` (flattening, per-field `owner`,
canonical parents), `docs/language/classes/traits-layer2-design.md` (the search order, the
kernel gate on every proposal, trace-as-data),
`docs/language/classes/traits-receiver-dispatch-design.md` (dispatch is a resolution goal; §4's
ambiguity rules, which are *not* re-decided here).

**No kernel change, no metatheory obligation, no new registry.** Dispatch
still builds one goal and calls `resolve_goal`; the resolver still proposes a
term that the kernel checks at the goal (layer 2 §4.4). This slice changes
*which* goal dispatch builds, and adds one more way an in-scope value can
answer a goal.

---

## 1. The problem, in one line

`extends` flattens and a child instance synthesizes its parents, so at any
carrier in a chain **every** class in the chain has both the field and an
instance. Receiver dispatch, which asked "which classes have a field of this
name and an instance here", therefore found all of them and reported
ambiguity — correctly, and forever. `x.plus(y)` — the unsugared `x + y` — is
exactly a call to an inherited member, so a library could have a hierarchy or
receiver sugar, never both.

## 2. The decision: the goal is built at the field's **owner**

`x.f(…)` builds its resolution goal at the class that **declares** `f`, not at
every class whose flattened field list contains it.

```
owners := [ C | C visible here, C declares f (ClassInfo.owner[i] == None) ]
```

`ClassInfo` already stores the per-field owner (layer 1 §2), and layer 1 §3
makes the owner *unique*: a class may not redeclare an inherited field (it is
a declaration error naming the ancestor), so each field name has exactly one
declaring class per chain. Nothing is computed that was not already recorded.

Everything downstream of the candidate list is unchanged: the goal is built
from the receiver's kernel type (receiver-dispatch §2.1), one-parameter
classes only (§2.1), the emitted term is the projection applied receiver-first
(§2.2), and §4's rules 1–7 hold verbatim.

### 2.1 Why this is not a tiebreak

The rejected options were "most-derived wins" and "least-derived wins" — both
*orderings on a set of answering candidates*, i.e. exactly the priority that
receiver-dispatch §4 refuses to have. Owner-keying is not an ordering. It
changes what the candidate set *is*, before anything is resolved: a class that
merely inherits `f` was never asking to answer for `f`, because it never said
anything about `f`. The set is computed from the declarations alone — no
instance is consulted, no resolution is run, no candidate is discarded because
another one succeeded.

The distinction is observable, and the case that observes it is the one the
ambiguity rule exists for: **two unrelated classes declaring one name are
still two owners**, and a receiver call at a carrier where both resolve is
still an error naming both. Nothing about the diagnostic changes. What changed
is only that `AddMonoid` and `AddCommMonoid` stopped being candidates for a
name that `AddSemigroup` declared — and they stopped being candidates whether
or not they have instances.

Least-derived-wins would have coincided with this rule at every program in the
corpus. It is still the wrong rule, because it reaches its answer by preferring
one *answering* class over another, so it would also have picked a winner
between two unrelated classes that happen to sit at different depths of
unrelated chains.

### 2.2 The override / agreement-certificate interaction

The case the issue asked to check: a child instance overrides an inherited
field with a *different* value, carrying an agreement certificate (layer 1
§4.5). Owner-keying dispatches to the **ancestor's** dictionary, so the
question is whether that is the value the writer meant.

It is, and the certificate is why. Layer 1 §4.5 discharges an override by
synthesizing `{prefix}::{f}#agrees : ⟨override⟩ = ⟨ancestor's projection⟩`
with `refl` — kernel-checked *convertibility*, at declaration time, or the
declaration is refused. So the two values are definitionally equal and no
program can tell which one dispatch chose. If the propositional fallback that
record §12 sketches is ever built (an override that conversion cannot reach),
this rule acquires real content and has to be revisited **then**, with the
feature that creates the difference; it is not pre-decided here.

The other half is that a class-level override cannot arise at all: layer 1 §3
refuses a class that redeclares an inherited field. So "the owner" is never a
choice between two declarations of one name in one chain.

## 3. The resolver learns upcast

Owner-keying moves the goal *up* the chain, so the dictionary in scope is now
routinely a *child* of the goal's class:

```
fn f<G> requires m: AddCommMonoid<G> (x: G, y: G) -> G { x.plus(y) }
--  goal AddSemigroup<G>, scope has AddCommMonoid<G>, G open
```

Step 1 of the search (layer 2 §3) compares each local's type to the goal by
conversion, and `AddCommMonoid<G>` is not convertible to `AddSemigroup<G>` —
they are different records. So the resolver gains one rule:

> **Scope upcast.** For a goal whose class is `C`, an in-scope binder or `let`
> alias whose type's class `D` has `C` among its ancestors proposes the
> **canonical parent projection**: the `C`-record built field-by-field out of
> the dictionary's own projections, `C { f: d.f, … }` over `C`'s flattened
> field list.

**Amended 2026-08-08** (`docs/language/classes/traits-named-upcast-design.md`, retiring
`issues/upcast-assembly-cost-at-open-carriers.md`): the rule is unchanged, and
so is the term it proposes. What changed is the *consumer*. Where the upcast
was resolved in order to project one field — which is every dispatch, and four
occurrences out of four in the library's motivating proof — the projection is
taken from the **child** dictionary at the child's own index, and this record
is built, gated and then thrown away. It is the same value: the record's slot
for `f` is `d.f`. See §7.1, which is where building it was argued.

Four things this deliberately is not:

- **Not a registry change.** A *concrete* carrier never needed upcast: layer 1
  §4.4 already synthesizes and registers the canonical parent instance at that
  carrier, so `AddSemigroup<Nat>` is a registry hit. Upcast exists for the
  scope — for the open carrier, where there is no registry entry and no
  synthesized global to name.
- **Not a coercion.** It fires only inside resolution, only at a goal whose
  class is an ancestor of the candidate's, and the term it proposes goes
  through layer 2 §4.4's kernel check like every other proposal. A failure is
  "this candidate is not it", never a term.
- **Not a new value.** The built record's components are literally the
  dictionary's own projections, which is the same construction layer 1 §4.4
  uses for a synthesized parent — so a diamond still collapses by construction
  and `refl` still relates the two paths.
- **Not a search over ancestors.** The ancestor list is transitive and
  flattened already (layer 1 §2), so a grandparent is one step, not a chain
  walk.

### 3.1 Where it sits in the order

```
0. the canonical derived table
1. locals and `let` aliases, innermost first, by conversion   -- exact
1b. locals and `let` aliases, innermost first, by upcast      -- NEW
2. the registry
```

Exact-before-upcast, and both before the registry. The first is because an
exactly-typed dictionary in scope is the value the writer named and an upcast
is a value the resolver built; the second is layer 2 §3's own rule — an
explicit value in scope wins over derivation — and upcast is a scope answer,
not a derivation. Innermost-first is inherited unchanged in both passes.

The upcast pass is skipped outright unless the goal's type is a class
(`tag_of` plus the class table), so `p: n = n := infer` and every non-class
goal cost exactly what they cost before.

### 3.2 The trace

One more `local` line, phrased so the search is readable as data:

```
local: m (upcast to `AddSemigroup`)
```

`local` and not a new key, because the vocabulary is closed (layer 2 §7) and
the fact being reported *is* "answered from the scope, by this binder". A
failed upcast contributes nothing: it is a candidate that did not verify, and
the scope line already says how many binders were consulted.

## 4. Diagnostics

Nothing new is spelled. Precisely:

- **Ambiguity** still names every hit and still says "write the projection you
  meant" (receiver-dispatch §4 rule 3). It now fires only for unrelated
  owners, which is the case it was written for.
- **A failed dispatch** is still trace-as-data (`ElabError::Resolution`), still
  suppressed when the call has another reading (§4 rule 5).
- **A member of a multi-parameter class** is still refused by name (§4 rule 7),
  now naming the *owner* class — which is the class the writer would have to
  project from, and so is the more useful name to print.

## 5. What this lets the library drop

`lib/std/algebra/algebra.hthr` declared `Monoid<A>` flat, with a comment saying why,
and spelled the additive hierarchy's inherited operation as
`Nat::AddCommMonoid.plus(a, b)`. Both were the workaround. With this slice:

- `class Semigroup<A> { op, assoc }` and `class Monoid<A> extends
  Semigroup<A> { unit, unit_l, unit_r }` — the natural chain, and `x.op(y)`
  still dispatches (owner: `Semigroup`), at concrete and open carriers alike;
- `x.plus(y)` and `x.plus(0)` are receiver calls at `Nat` and at `Bool`.

## 6. Acceptance

Per `docs/testing-generated-terms.md`:

1. `a.plus(b)` at `Nat` dispatches and computes to `add(a, b)` — the flipped
   pin (`an_inherited_member_is_reached_at_its_owner`), which is the old test
   turned positive.
2. **Open carrier**: `fn f<G> requires m: AddCommMonoid<G> (x: G, y: G) { x.plus(y) }`
   elaborates and agrees with `m.plus(x, y)` by `refl`; and a lemma stated at
   `AddMonoid<G>` is discharged from an `AddCommMonoid<G>` binder — the upcast
   proper, with nothing concrete anywhere.
3. **Checking position**: the dispatched call used where the carrier type is
   expected, and a class lemma applied at a dispatched statement.
4. **Negative controls**: two *unrelated* classes declaring one member name at
   one carrier still error naming both; upcast does not fire between unrelated
   classes of the same shape (the goal reports its trace instead); and the
   library's own disjunction-vs-conjunction control still distinguishes the
   `Bool` structures.
5. The receiver-dispatch, layer-1 and layer-2 suites green unedited but for
   the one flipped pin and the comments that recorded the workaround.

## 7. What implementing this corrected

### 7.1 The upcast is built as a record literal, not as a projection

"Project the synthesized canonical parent" is how the issue phrased it, and it
is right at a *concrete* carrier — where a synthesized parent global exists to
project. At an **open** carrier there is no such global: the dictionary is a
binder, and layer 1's synthesis runs at instance declarations, not at binders.
So the proposal is assembled the way layer 1 §4.4 assembles a parent value —
the parent record over the child's own components — with the child dictionary
bound as an unspellable `#` alias so the assembly can be written as ordinary
surface field projections and go down the existing constructor path. The
result is the same *value* the concrete route would have projected, which is
why the two carriers do not need two stories.

**Amended 2026-08-08** (`docs/language/classes/traits-named-upcast-design.md`). Everything
above stays true of the assembly and of when it is built. What it *cost* is
the amendment: writing it into the emitted term per occurrence cost ~0.78 s a
time at the kernel gate — the class's dependent Σ-type re-checked per copy,
~100% of it in the law fields — and it was baked into the declaring theorem's
statement, so its call sites paid too
(`issues/upcast-assembly-cost-at-open-carriers.md`). So the assembly is now
built only to *decide* the goal, and where the consumer is a dispatched
projection the field is taken from the child dictionary instead, because the
assembly's `f` slot **is** `d.f`. The library's `plus_zero_of_comm` went 35.9 s
to 0.94 s, and the anonymous and named-dictionary spellings now elaborate to
one term. A named Ψ definition per pair — which is what the issue's log
proposed — was built, measured at 2.2×, and withdrawn; the numbers are in that
document's §5.

### 7.2 Dependent fields need no handling

A law field's type mentions earlier fields (`unit_l` mentions `op` and
`unit`), so the parent record's `unit_l` slot is expected at the type
instantiated by the components already supplied — which are exactly
`#dict.op` and `#dict.unit`, and `#dict.unit_l`'s own type is exactly that.
The constructor path substitutes earlier arguments into later field types
already (`build_ctor`, `docs/language/surface-records.md` §6), so the Σ spine does the
work and this slice writes nothing for it.

## 8. Residue, with owners

- **A propositional (non-`refl`) override** would make §2.2's "no program can
  tell" false. It is record §12's fallback, unbuilt; `issues/traits.md` owns
  it, and this document is the second place that says the two features
  interact.
- **Upcast is scope-only.** A goal `C<T>` at a concrete carrier is answered by
  the registry's synthesized parent, so nothing asks for registry upcast
  today. If `extends` ever gains a non-parameter argument (layer 1 §7.2), the
  synthesis story changes first and this follows it. `issues/traits.md`.
- **Trial cost** gains one more multiplier — the upcast pass is a second scan
  of the scope, gated on the goal being a class. Filed where layer 2 §10
  already files it.
