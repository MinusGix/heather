# Type-level dot projection: `A.unit`, `G.plus(x, y)`, `Nat.zero`

Status: **round slice**, implementing candidate 23 of
`issues/requires-placement-syntax.md` §R2-C (endorsed by the user 2026-08-07,
sequenced behind the owner-keyed-dispatch round, which landed as c596598).
Constraints: `docs/language/classes/traits-owner-dispatch-design.md` (the goal for a member name
is built at its **declaring** class; the resolver's scope upcast),
`docs/language/classes/traits-receiver-dispatch-design.md` §4 (the ambiguity rules, inherited
rather than re-decided), `docs/language/classes/traits-layer1-design.md` /
`docs/language/classes/traits-layer2-design.md` (`ClassInfo`, the search order, trace-as-data).
Designed against `issues/operation-indexed-classes.md`: §6 records where an
indexed class would change an answer instead of pre-deciding it.

**No kernel change, no metatheory obligation, no new resolution machinery, no
new registry.** The feature builds one goal and calls `resolve_goal`; the term
it emits is a record projection — the same term the writer's own
`⟨dictionary⟩.f` already elaborates to.

---

## 1. The problem, in one line

A constrained type variable **is** a structure, and the language had no way to
say so. `<A: Monoid>` (the previous round) removes the dictionary's name from
the signature, but a declaration that needs the dictionary in its *body* had to
put the name back — which is why four of `lib/std/algebra/algebra.hthr`'s six
constrained declarations kept `requires m:` after the inline form shipped
(`issues/requires-placement-syntax.md`, "What landed", correction 4).

## 2. The decision: the subject of the dot may be a **type**

`T.f` and `T.f(ā)`, where `T` denotes a type, become

```
owner  := the class that DECLARES f          -- owner-keying, unchanged
goal   := Owner<T>                           -- T itself is the carrier
dict   := resolve_goal(goal)                 -- layer 2, unchanged
result := π_f(dict)  applied to ā            -- an ordinary projection
```

Receiver dispatch with exactly one word changed: the goal's carrier is the
subject *itself* rather than the subject's type, and consequently **the subject
is not an argument**. Everything else is inherited verbatim — the candidate set
(classes that declare `f`, visible here, one type parameter, sorted by
canonical name), the resolver (scope, then upcast, then registry), the kernel
gate on the proposal, and §4's rules 1–7.

Three things follow from "the subject is not an argument", and they are the
whole difference from receiver dispatch:

- **A bare `T.f` is a projection**, not a refusal. `docs/language/surface-records.md`
  §4.2's "a bare `p.f` is never a method call" is a rule about *method calls*;
  a type projection is not one, so `A.unit` and `G.zero` are values and need no
  parentheses. This is the form §R2-C's own example (`G.plus(x, G.zero)`) is
  written in.
- **A proof field is free.** `A.unit_r(x)`, `G.plus_comm(x, y)` are the same
  projection with a different field type; nothing in the implementation
  distinguishes a law from an operation, and nothing needs to.
- **The emitted term is the explicit spelling's term.** `Nat.zero` *is*
  `Nat::AddMonoid.zero`, `A.op(x, y)` *is* `m.op(x, y)`: same projection of the
  same dictionary, so agreement is syntactic and `refl` between them is not
  even a conversion. Pinned three ways (§8).

## 3. Which subjects are types

### 3.1 The test, and why it is this one

```
type_subject(e) :=
   case elab_infer(e) of
     Ok(t : U)  when whnf U = Ty l   ->  El_l t          -- a binder at a universe
     Ok(_)                           ->  not a type      -- an ordinary value
     Err(_)                          ->  expr_as_ty(e) then elab_ty   -- `Nat`, `Box<Z>`
```

The first arm is the type *parameter* case: `fn f<A: Monoid>` binds `A` as an
ordinary kernel binder at `Ty 0` (`docs/language/surface-polymorphism.md` §2), so it
infers as a value whose *type* is a universe, and `El` of that code is exactly
the carrier `lower_named` would have built for a written `A`. The second arm is
the concrete case: `Nat`, `Bool`, `Box<Z>` are not expressions at all, and
`expr_as_ty` — the reader `docs/language/surface-universe.md` §4 already uses for
"an expression in type position" — is what turns them into carriers.

Stated as one sentence: **the subject is a type when its type is a universe, or
when it is not a value and reads as a type**. The alternative test (syntactic:
"a capitalized bare name") was not built; it would have to answer for
`List<Nat>` and for a lower-case type alias, and it would decide by spelling
what the elaborator can decide by meaning.

### 3.2 Shadowing, and the growth invariant

The order of the two arms *is* the shadowing rule: **a value binder shadows the
type reading**, because a value binder makes `elab_infer` succeed at a
non-universe type and the second arm is never reached. So

```heather
fn f(Z: Holder) -> Z { Z.pt }          // the binder's field, not `Pt<Z>`
```

reads exactly as it read before this round. This is the sharpest case the
growth invariant (`docs/language/modules-design.md` §4) asks about, and it is pinned
(`a_value_binder_shadows_the_type_reading`). Note that the *type* reading of
`Z` in the result position is unaffected — `lower_named` consults `cx.tyvars`
and the inductive table, never value binders — which is the language's existing
(and deliberate) separation of the two namespaces, not something this round
introduces.

The general statement of the invariant here: **every reading this feature takes
was an error before it**. `A.pt` said "this is not a record", `Nat.pt` said "the
receiver's type could not be inferred", `A.op(x, y)` built the nonsense goal
`Mag<Type<0>>` and reported its failure. No spelling that elaborated before
elaborates differently now, with the single decided exception of §4's rule.

### 3.3 Where the test runs

At the **top** of `resolve_dot`, before the record-field branch. Nothing below
could have read a type subject — a universe is not a record, has no namespace
member, and is not a method receiver — so first is the cheapest place that is
also correct, and every `None` leaves every older reading untouched. It is
gated by the same cheap negative test receiver dispatch uses (`class_members`,
a program-wide `HashSet` of every class's field names), so a `.f` where `f` is
nobody's class field costs one hash lookup and nothing else.

## 4. The other reading, and the divergence from receiver dispatch

Receiver dispatch names both readings when a successful dispatch races an
ordinary one (§4 rule 2) and falls back silently when a *failed* one does
(rule 5). Both are inherited. What is *not* inherited is the definition of
"another reading exists", and this is the round's one deliberate divergence:

> **The method desugaring is a competing reading of `T.f(ā)` exactly when its
> callee's subject slot is at a universe** — read off the callee's own declared
> Π-telescope, never by trying the call. And a **bare** `T.f` has no desugaring
> at all, so it never has another reading.

The reason is that the desugaring puts the subject where the receiver goes, and
for a type subject that is a *type in a value slot*. For almost every callee
that is not a reading of the expression, it is a guaranteed type error — and
claiming "each of these is a reading" of a program where one of them cannot be
would make the diagnostic false.

This is the owner-keying move applied one level out: the candidate set is
computed from **declarations alone**, before anything is elaborated, so it is
not a tiebreak and races nothing. The undecidable cases (a builtin method, a
constructor, a telescope that cannot be read) count *as* readings, which is the
conservative direction and keeps receiver-dispatch §7.2's caution about the
Rust-implemented builtins exactly where it was.

The case that pays for this rule is in the library: `std/nat` exports a global
`le_refl`, so `x.le_refl()` on a **receiver** is ambiguous against it and always
will be — but `A.le_refl(x)` on a type subject is not, because `le_refl`'s
first slot is a `Nat`. `max_of_self` could not otherwise have migrated. Both
directions are pinned (`a_global_that_cannot_take_a_type_is_not_a_competing_reading`
and its control `a_global_that_can_take_a_type_names_both_readings`, whose
callee really does begin `(A: Type<0>, …)`).

Concrete carriers get the same rule, not a new one: `Nat.plus` beside a
type-owned `Nat::plus` is one call to the same test with the member as the
callee. When both readings really are available the message names both and
spells each fix.

## 5. The escape: `G::AddCommMonoid`

§R2-C offered `G::AddCommMonoid.plus` as the escape from ambiguity and assumed
it was already writable. Checked (2026-08-08): it **parses** — the lexer joins
`ident :: ident` into one qualified identifier, so `G::AddCommMonoid.plus` is a
`Dot` on the name `G::AddCommMonoid` — and it **did not elaborate**, because
`G` is neither a module nor a type namespace, so the name resolved to
`NoSuchQualifier`.

The decision is to make the *name* mean something, not to add a dot form:

> **`T::C` is the `C` dictionary at the type `T`**: a goal, resolved. Reached
> only from `resolve`'s last stop, where the answer would otherwise have been
> "unbound name".

Three consequences, all of which are why this spelling and not another:

- **It generalizes what the library already writes.** At a concrete carrier
  `Nat::AddCommMonoid` is a registered *global* and is found long before the
  new fallback, so the library's existing spelling is untouched and means the
  same value. The fallback reaches exactly the carriers that have no global to
  name — which is the open ones, where the escape is needed.
- **It is a value, not a dot rule.** `A::Pt` can be bound, passed and projected
  by the ordinary record path, so `A::Pt.pt` needs no code of its own. One
  lexer fact, one resolver fallback, zero grammar.
- **A failure is the search.** `A::Pt` at an unconstrained `A` reports layer
  2's trace, as data, the way every other resolution failure does.

`::` joins exactly once, which is what makes this unambiguous: there is no
`M::T::C` to compete with a module-qualified reading.

## 6. What an operation-indexed class changes (superseded 2026-08-09)

This section was written before the operation-indexed design pass and
predicted the wrong rule. What it said: `T.f` at an indexed class would build
`C<T>(?op)` — a goal with a meta in a value slot — and should therefore be
**refused by name**, the same shape as the multi-parameter narrowing of §4
rule 7. What was decided and built instead
(`docs/language/classes/operation-indexed-classes-design.md` §5.1, implemented in that
document's round one):

- **Scope first, then refuse.** The goal is still built at the owner with the
  index slot open, but a binder in scope of the goal's class — or of a
  descendant, whose `extends` chain passes the index up unchanged — answers
  what the index is, and only a slot that survives that is refused. Inside
  `<A: Monoid>` or `<A: Monoid(op)>` both `A.unit` and `x.assoc(y, z)` work;
  at a concrete carrier with no binder in scope, `Bool.unit` is refused. This
  is not new machinery: it is layer 2's own search order with the refusal at
  the ladder's end.
- **The refusal is richer than this section imagined.** It names the slot, the
  class, and **every registered instance that would answer at this carrier**,
  each with its index — at `Bool`, both monoids. The multi-parameter
  narrowing's message is unchanged and still lives beside it; the value-index
  case is its own diagnostic (`value_slot_refusal`), because "which structure
  did you mean" and "which carrier did you mean" are different questions.
- **The candidate filter is untouched.** It is still `params.len() == 1`; the
  value index is not a filter but a slot to fill, so a class with one type
  parameter and an index is dispatchable and a class with two type parameters
  still is not.
- **`T::C` took its arguments.** §5's escape is now `Nat::Monoid(add)`, which
  is what discharges the residue this document filed on `issues/traits.md`.

Unchanged from the original section, and worth keeping: nothing here assumes a
class has exactly one parameter *in general* — the filter is a narrowing on
dispatchability, and multi-parameter classes remain reachable by the explicit
projection.

## 7. Diagnostics

Trace-as-data throughout, and no new vocabulary (layer 2 §7):

- **Nothing resolved, no other reading** → `ElabError::Resolution` naming every
  goal that was tried (`Monoid<A>`) with the scope/registry trace under it.
  This is the answer to "an unknown field at a type subject should name what
  was tried": the search *is* the diagnosis, and it replaces the "this is not a
  record" the old path produced.
- **Two owners resolving at one type** → both named, with the escape spelled:
  ``write the class you meant (`Z::⟨class⟩.pt`)``.
- **A successful projection racing a real other reading** → both named, each
  fix spelled (§4).
- **A member of a multi-parameter class** → refused by name, the class named
  and the projection spelled (§4 rule 7's message, retargeted to a type
  subject).
- The subject is displayed as the text that was **written** (`A`, `Nat`,
  `Box`), because an open carrier has no nominal tag to render.

## 8. Acceptance

Per `docs/testing-generated-terms.md`, `crates/elab/tests/traits_type_projection.rs`
(25) and two additions to `crates/elab/tests/lib_algebra.rs`:

1. **Open carrier**: an operation (`A.op(x, y)`), a bare value (`A.unit`), an
   **inherited** member reached by upcast (`A.sop` under `<A: Mon>`), and a
   **proof** field in checking position (`A.unit_r(x)` proving
   `A.sop(x, A.unit) = x`).
2. **Concrete carrier**: a declared type, `Nat` (a kernel type with no
   declaration behind it), and a **derived** carrier (`Box<Z>` under a generic
   instance whose body itself projects from its element type).
3. **Agreement**, three ways: `Z.op` vs `Z::Mag.op` at a concrete carrier;
   the type-projecting function vs the `requires`-naming one at an open
   carrier; and the type projection vs the **receiver** dispatch of the same
   member — the two sugars of the last two rounds reaching one term.
4. **Negative controls**: an unconstrained type parameter reports the search;
   a concrete type with no instance reports the registry's account; two classes
   declaring one name at one type name both; a value binder shadows the type
   reading; an unbound name's `.f` errors exactly as before; a record field
   still wins; a multi-parameter class is refused by name; the escape at a
   carrier with nothing to find reports its search.
5. The other-reading rule pinned in both directions (§4), and the bare form
   pinned as having no other reading at all.
6. `lib/std/algebra/algebra.hthr`: `Nat.zero = Nat::AddMonoid.zero` by `refl`, and
   `sum(Nil) = Nat.zero` — the empty fold reduced to the projected unit, which
   is `mconcat`'s migrated `Nil` arm computing.

## 9. What implementing this corrected

### 9.1 The competing-reading test had to be decided from the telescope

§R2-C says "ambiguity is the existing rule, not a new one", and it is — but the
existing rule's *input* ("does another reading exist") is receiver dispatch's,
and transplanting it verbatim made `A.le_refl(x)` ambiguous against the ambient
`le_refl`, which would have blocked the migration this round exists for. §4 is
the correction: the rule is the same, the input is narrowed by reading the
callee's declared subject slot. Found by migrating, not by reading.

### 9.2 A resolution failure in the receiver is a better error than a missing field

`A::Pt.pt` at an unconstrained `A` reported "no field `pt` here (and the
receiver's type could not be inferred)" — the bare-dot branch's message,
because the receiver's inference had failed. It had failed *with the search in
it*. That branch now propagates an `ElabError::Resolution` from the receiver
instead of replacing it, which is a one-line improvement to every receiver
whose own elaboration is a failed resolution, not only to §5's spelling.

### 9.3 The upcast is what a type projection costs, and it can cost a lot

`plus_zero_of_comm` written `<G: AddCommMonoid>` with `G.plus(x, G.zero)`
elaborates correctly and takes **25 seconds**, against 0.7 for the whole file
in the `requires a:` spelling (measured 2026-08-08, release binary, five
runs varying which occurrences were upcast). The cause is not the projection:

- `plus` is declared by `AddSemigroup` and `zero` by `AddMonoid`, so both goals
  are at **ancestors** of the binder's class, and at an open carrier the only
  answer is `docs/language/classes/traits-owner-dispatch-design.md` §7.1's assembly — a fresh
  parent record built over the child's projections, inline, once per
  occurrence, each a Σ-tuple whose components are law *types*;
- writing the same theorem with the exact dictionary
  (`G::AddCommMonoid.plus`, no upcast because the child's flattened field list
  has `plus`) is **0.7s**, and moving upcasts out of the proof body alone takes
  25s to 1.7s. The cost tracks the number of assembled records that conversion
  has to compare, not the number of type projections.

So the feature is cheap and the *ancestor* case is not. The library keeps
`requires` for this one declaration with the measurement written beside it
(§10), and the residue below owns the fix.

## 10. What the library dropped, and what it kept

`lib/std/algebra/algebra.hthr`, after this round. **Historical from 2026-08-09**: the
operation-indexed round rewrote this file — the additive hierarchy and
`plus_zero_of_comm` are deleted, and the table below describes a state that no
longer exists. It is kept as the record of what *this* round moved.

| declaration | before | after |
| --- | --- | --- |
| `mconcat` | `requires m:` + `m.unit` | `<A: Monoid>` + `A.unit` |
| `mconcat_single` | `requires m:` + `m.unit_r(x)` | `<A: Monoid>` + `A.unit_r(x)` |
| `max_of_self` | `requires c:` + `c.le_refl(x)` | `<A: Cmp>` + `A.le_refl(x)` |
| `max_of`, `max_of_true` | `<A: Cmp>` (last round) | unchanged |
| `plus_zero_of_comm` | `requires a:` | **kept**, for §9.3's measurement |
| `or_default` | `d: Default<A> := infer` | unchanged — the general solver default, not part of the `requires` question |
| `nat_plus_zero`, `bool_plus_zero` | `Nat::AddMonoid.zero` | `Nat.zero`, `Bool.zero` |

Five of six constrained declarations are anonymous; the sixth is anonymous the
moment §9.3's cost is paid down, and its comment says so with the spelling to
use. `requires` is **not** removed from the language — that is a separately
ledgered decision (`issues/requires-placement-syntax.md`'s prerequisite list,
to which §9.3 adds one entry) — and it stays pinned in the test corpus by
`the_two_spellings_are_one_term_at_an_open_carrier`,
`the_inline_form_cannot_state_a_nonterminating_instance`, and this file's own
`plus_zero_of_comm`.

## 11. Residue, with owners

- **Ancestor upcast is expensive at an open carrier** (§9.3) — the round's one
  real finding, and the only thing standing between `plus_zero_of_comm` and the
  anonymous spelling. The shape of a fix: the assembled parent is rebuilt per
  occurrence, and layer 2's canonical derived table (§8) cannot hold it because
  it depends on a local binder. `issues/traits.md`, or a perf issue of its own.
- ~~**`T.f` for an indexed class** (§6) — refuse by name when classes gain
  value parameters.~~ **Discharged 2026-08-09** by
  `docs/language/classes/operation-indexed-classes-design.md` round one, and *not* as this
  document predicted: the rule is scope-then-refuse, and §6 above is rewritten
  to say so.
- ~~**`T::C` does not take arguments**~~ — **discharged 2026-08-09** for the
  *indexed* case: `Nat::Monoid(add)` is the goal `Monoid<Nat>(add)` resolved,
  at the same fallback position §5 already used. A multi-parameter class still
  has no short spelling (`C<T, U>` would need a written *type* argument, which
  is a different grammar); that half stays on `issues/traits.md` with the
  multi-parameter dispatch residue it belongs to.
- **`T.f` bare partially applied** — `A.op` is a value, so a class member *can*
  now be partially applied through a type where it cannot through a receiver
  (`docs/language/classes/traits-receiver-dispatch-design.md` §8's "a bare `x.op` never
  dispatches"). This is not a contradiction — the subject is an argument in one
  and not the other — but it is the first spelling that makes a partially
  applied class member writable, and the receiver rule may want revisiting in
  its light. `issues/traits.md`.
- **The subject's type is inferred once more** on the dot path, before the
  three inferences receiver-dispatch §7.3 already records. Same bound (the
  cheap negative test) and same file it is recorded in.

## Complete local multi-parameter dictionaries (2026-09-05)

The one-parameter narrowing above now has a scoped extension. A complete local
`Mapping<S,A>` dictionary fixes both arguments, so `S.send` may project its
`send` field. The subject must match its primary carrier. The actual local term
must still have the declared class type; a shadowed name cannot supply evidence.
Annotated local aliases are included, even for classes without value indices.

Tagged parents also qualify when their recorded path preserves the primary
carrier. Traversal uses ordinary field projections. Two matching dictionaries,
including two differently indexed tagged parents, remain ambiguous. Explicit
value-dictionary projection disambiguates them. No additional type parameters
are inferred from global instances, and reordered carrier paths do not qualify.

The finite-set client uses this for `S.image_union` under `FiniteSets<S,A>`.
Tests in `traits_type_projection.rs` check the resulting term against explicit
projection, beneath binders, through aliases and tagged parents, and against
ambiguity, unrelated carriers, and shadowing.
