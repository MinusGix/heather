# Datarepr: runtime representations by certified refinement — design

Status: **design round, pre-implementation** (2026-08-14). Produced from the
settled pre-charter discussion recorded in `issues/datarepr-separation.md`
(the three 2026-08-14 log entries); this document develops those positions,
it does not relitigate them. Everything marked **RECOMMENDED** goes beyond
the settled constraints and awaits the user's yes/no; everything marked
**FINDING** is a place where the settled positions rub against each other,
with the resolution this document argues for. All Heather code below is
idealized/sketch — none of it has been checked.

Owners of the seams this touches: `issues/compile-typeclass-design.md`
(instance keying, the Compile class), `issues/certifying-generator.md` (the
v1 customer: parameterized instantiations, `List<Tok>`, `calc.hthr`'s
`run`), `issues/iterators-as-list-repr.md` (lazy reprs / API naturality),
`issues/class-ops-prop-vs-bool.md` (deciders for the dispatch ladder),
`issues/memory-bound-certificates.md` (the metered-space model — referenced,
not designed), `issues/effects-direction.md` (the graded reading of `+ E`,
if ever).

The design principle, inherited verbatim from the certifying generator and
protected against every choice below: **the transfer engine is untrusted
because each output carries its own certificate.** No decision here is ever
justified by "the generator is careful"; the kernel is the only careful
party. There is no unrestricted `implemented_by`, ever.

---

## 0. The shape in one paragraph

A spec inductive `S` is a mathematics object; it never runs. A **repr** of
`S` is a carrier type `R` plus a total kernel-side abstraction function
`abs : R -> S` and an invariant `inv : R -> Prop`. The repr carries a
**correctness basis** — constructor images and a fold refining `S`'s
recursor — which anchors every certificate and mechanically transfers every
structurally-defined spec function, and an open **cost basis** — a
per-operation `Impl` registry of hand overrides, each with its own
`refines` theorem, optionally certified **via-derived** (equivalence to the
transferred implementation, certificate by transitivity). Partiality is
policy'd by *source*: input-determined partiality is a precondition under a
three-rung dispatch ladder; machine-state partiality (allocation) is an
outcome type, forced, erasable only under an explicit capacity bound.
Effect bubbling lives only in the generated repr-side layer; spec functions
stay pure forever. v1 is byte-free: named reprs over ordinary kerneltime
types, the naive repr made official, and the certifying generator's
parameterized-instantiations customer (`List<Tok>`, so `calc.hthr`'s `run`
compiles) as the acceptance shape.

Findings called out below, gathered here for the coordinator's eye:

- **FINDING 1 (§1.3)**: the settled text's "constructor images … must
  exist" is in tension with machine-finite carriers (`Succ` has no total
  image on `u64`). Resolution: *totality is `abs`'s requirement only*;
  constructor images are operations in kind and sit under the partiality
  policy like any `Impl`. Consumption of a repr is always total;
  construction is where finiteness bites — that line is clean and worth
  stating as the rule.
- **FINDING 2 (§8)**: "naive repr made official / available for every
  inductive" superficially contradicts "no always-available bignum-style
  fallback". Not a real contradiction — the rejected thing is a *semantic*
  fallback that hides finiteness inside one repr's operations; the naive
  repr is an *operational* default whose semantics is exactly the spec's.
  Recorded so nobody re-derives the tension.
- **FINDING 3 (§6.4)**: the hostile-repr exercise shows `abs`+`inv` cannot
  make an order-forgetting structure represent an ordered spec — the bag
  represents only the sorted image of `List`. The discipline holds by
  declining honestly; the pressure it reveals lands on spec-side quotient
  types, which are out of datarepr's scope by construction.

---

## 1. The class semantics: `Repr` and the `Impl` registry

### 1.1 The `Repr` record (correctness basis)

For a spec inductive `S` with constructors
`c_j : T_j1 -> … -> T_jk_j -> S` (v1 scope: each `T_ji` is either `S`
itself — a recursive position — or a non-recursive spec type left at its
spec type; mixed/nested reprs are deferred, §5), a repr of `S` is, at the
class level, a record. Because the record's *shape* depends on `S`'s
declaration (one image per constructor, arities varying), it is a
**per-inductive generated record type** — the same move as certgen's
`CompileNatK{T}` per-signature records — not one polymorphic class:

```heather
// Generated for S = List<Tok> (sketch; the datarepr form in §1.4 emits this)
record Repr_ListTok {
    R    : Type,
    abs  : R -> List<Tok>,          // total, kernel-side. The ONLY field
                                    // required to be total outright.
    inv  : R -> Prop,

    // Constructor images. Each is an operation in kind (§1.3): total here,
    // but permitted a precondition or outcome under the partiality policy.
    mk_nil  : R,
    mk_cons : Tok -> R -> R,

    // Image laws: commutation through abs, and inv-closure.
    nil_abs   : abs(mk_nil) = Nil,
    nil_inv   : inv(mk_nil),
    cons_abs  : (t: Tok, r: R) -> inv(r) -> abs(mk_cons(t, r)) = Cons(t, abs(r)),
    cons_inv  : (t: Tok, r: R) -> inv(r) -> inv(mk_cons(t, r)),

    // The fold anchor: a fold over R refining S's recursor. The law takes
    // the SPEC step and adapts it repr-ward — abs at the child position;
    // no map S -> R exists to adapt a repr step the other way.
    fold      : (B: Type) -> B -> (Tok -> R -> B -> B) -> R -> B,
    fold_law  : (B, z, s: Tok -> List<Tok> -> B -> B, r) -> inv(r) ->
                fold(B, z, (h, t, b) => s(h, abs(t), b), r)
                  = rec_List(B, z, s, abs(r)),
}
```

Notes on the laws, precisely:

- **`abs` is total and kernel-side.** Non-surjectivity is deliberate and is
  what absorbs machine finiteness: a spec value with no representative is
  fine (nothing requires every `Nat` to fit in a `u64`-backed repr). No
  bignum-style always-available escape exists to restore surjectivity.
- **`inv` is the repr's maintained truth.** Every law and every `Impl`
  certificate quantifies over `inv`-satisfying inputs and (where the result
  is repr-typed) proves `inv` of outputs. `inv` is also the *payer* for
  machine-width facts (§2.4): once `inv` bounds a length field, index
  conditions inside a maintained repr discharge silently.
- **Commutation laws** relate images to constructors *through `abs`*, with
  recursive arguments taken at `R` and abstracted pointwise. In the guarded
  or outcome-typed image case (§1.3) the law is stated on the success arm.
- **The fold anchor** is the certificate anchor and the transfer
  generator's fuel: for any algebra, folding over `R` agrees with the spec
  recursor applied to `abs(r)`. The adaptation marks a real wrinkle, and
  it runs one way only: the fold's step sees the repr child, the spec
  recursor's step sees the spec child, and `abs` at the child position
  converts repr-ward — there is no `S -> R` to adapt a repr step to the
  recursor's side. (The sketch originally wrote `adapt(s)` on the recursor
  side; kernel-probed `NotConvertible`, corrected 2026-08-15 — stated as
  above, the naive instance is `refl`.) For the naive repr the adaptation
  is the identity and `fold_law` is `refl`.
- **The fold need not be what runs.** It must *exist* (with its law) so
  that certificates have an anchor and structural spec functions transfer;
  the cost basis (§1.2) is where speed lives. On a hostile repr the anchor
  fold can be genuinely awkward and slow (§6) — that is by design.

What the fold anchor buys, stated as the transfer theorem it enables: any
spec function `f` defined by structural recursion over `S` — i.e. whose
body is (elaborates to) `rec_S(alg)` — has a derived implementation
`f_impl := fold(alg')` with the certificate
`inv(r) -> f_impl(r) = f(abs(r))` provable schematically from `fold_law`
plus congruence. That schema is the transfer generator's whole proof
obligation for the derived route (§3).

### 1.2 The `Impl` registry (cost basis)

*(The `impl` declaration's surface — inline clauses, the `?` reporting hole,
the `:= derive()` and `via_derived(p)` routes, provenance — is designed and
landed in `docs/obligation-records-design.md` (2026-08-15), which treats this
section's obligation statements as its schema. This section stays the
semantic source of truth for what an `Impl` is.)*

The cost basis is an **open, per-operation registry**: for a spec function
`f` touching `S` and a repr `Rp` of `S`, an `Impl` provides a runtime-side
body and its refinement theorem. Keying reuses the operation-indexed-classes
mechanism (`docs/operation-indexed-classes-design.md`): the *operation is an
index*, so `Impl<Rp>(f)` and `Impl<Rp>(g)` are different types and the
registry is open by construction — no closed field list to amend.

```heather
// Sketch: hand override for length on a vec-flavored repr
impl length for VecList {                 // elaborates to Impl<VecList>(length)
    body := λ r => r.len,                 // signature: f's, with S ↦ R at
                                          // repr positions (+ outcomes per §2)
    refines := λ r h => …,                // : body(r) = length(abs(r))
}
```

The `refines` statement, precisely, for `f : X1 -> … -> Xn -> Y`:

- every occurrence of `S` in the signature maps to `R` (v1 rule: *all*
  occurrences; per-position mixing is deferred);
- hypotheses: `inv` at every repr-typed argument;
- conclusion, by result type: `Y` non-repr — `body(x̄) = f(⟦x̄⟧)` where
  `⟦·⟧` applies `abs` at repr positions; `Y = S` —
  `abs(body(x̄)) = f(⟦x̄⟧)` **and** `inv(body(x̄))`;
- if the body's signature carries an outcome sum (§2), the conclusion is
  stated per arm: the success arm carries the equation(s) above, failure
  arms carry whatever the certificate's honesty rung states (weakest:
  `True`).

**Via-derived is first-class**: a custom `Impl` may discharge `refines` by
relating its body to the correctness-derived implementation and taking the
derived certificate by transitivity. The obligation is the **weak, abs-image
form** (settled 2026-08-15, resolving the first-half FINDING):

> `∀ x̄, inv(x̄) → abs(body(x̄)) = abs(f_derived(x̄))`, plus `inv(body(x̄))`
> at a repr-typed result.

Weak because refinement is a statement about *spec* values: two
implementations that agree under `abs` refine the same `f`, whether or not
they agree at the carrier. Carrier equality — `body(x̄) = f_derived(x̄)` —
is **not a second route**: it discharges this same obligation by one `ap abs`
congruence step, so nothing dispatches on which one a writer proves, and the
strongest available proof is simply the shortest. What makes carrier equality
*available* is a **canonical-form `inv`**: a repr whose invariant forbids
redundant representations (`Bin` ruling out leading zeros) has `abs` injective
on `inv`-satisfying values, and there the two statements coincide. That is the
repr author's opt-in, priced against the maintenance burden every `Impl` then
carries, and it is why `inv` is the right place for it rather than the route.

The derived body plays exactly certgen's hand-run role: the thing you diff a
clever implementation against. This remains the expected *normal* route for
hand overrides (binary search vs. linear member, §6.3) — under the weak form
it is available unconditionally, which is what the first half's `Bin`
counterexample showed the strong form was not.

**As-landed (v1 first half, 2026-08-15), amending §1.2.**

- The two conclusions at `Y = S` land as **two record fields**, `refines` and
  `refines_inv`, rather than one conjunction: there is no conjunction to be
  had without a library, and the `impl` form refuses a repr-typed result that
  omits `refines_inv`.
- `Impl` keys on `(repr name, operation name)`. §4 asks for the operation's
  `.code` identity; the resolved *name* is what v1 uses, because the
  elaborator retains no `.code` handle for an arbitrary global at declaration
  time. The repr half is already declaration-keyed through the repr itself,
  so the weaker half is the operation's, and it is the half a later round can
  strengthen without moving anything else.
- The first half's FINDING — via-derived at the *carrier* is unavailable
  wherever `abs` is non-injective, `Bin`'s leading zeros being the
  counterexample — is **resolved into the paragraph above**: the obligation is
  the weak abs-image form, carrier equality is its strongest discharge rather
  than a rival, and canonical-form `inv` is the opt-in that makes the two
  coincide. The landed `Bin` `add` proves carrier equality and so is already
  in the resolved shape; it is one `ap abs` step from the official statement.

### 1.3 FINDING 1: constructor images are operations, not axioms

The settled text says the correctness basis "must exist". Read as "each
image is a total function", that dies at the first interesting carrier:
`Succ` has no total image on a `u64` carrier — `mk_succ(2^64 - 1)` has
nowhere to go, and no `inv` can exclude it because the *argument* satisfies
any reasonable `inv`. Meanwhile `abs` and `fold` on that same carrier are
unproblematically total (iterating the step function `n` times is ordinary
kerneltime computation). The general fact:

> **Consumption of a repr is always total; construction is where machine
> finiteness bites.** `abs`, `inv`, `fold` — consumers — are required
> total. Constructor images — producers — are operations in kind and sit
> under §2's partiality policy exactly like `push`: an image may be
> guarded by an input-determined precondition (bag `cons`, §6.2), may
> carry an outcome (`mk_succ : u64 -> u64 + WidthOverflow`, default rung
> decide-and-bubble per the settled machine-width policy), or may be total
> (every v1 repr; `Bin`'s `mk_succ`, §5.1).

Resolution (RECOMMENDED, resolving the tension rather than picking
silently): "must exist" means *must exist as certified operations under the
partiality policy* — the commutation and closure laws stated on the success
arm, and the transfer generator's derived `Impl`s inheriting the bubbled
arms wherever a transferred body *constructs*. Nothing weakens: a repr
whose images are total (all of v1) states the plain laws; the fold anchor
and hence all consumption-side transfer is unconditional either way.

### 1.4 The `datarepr` surface form and what elaborates

A bare `instance` cannot express a repr today, for a structural reason: the
record's field list depends on `S`'s constructor list, and instances
instantiate a *fixed* class shape. So (settled) `datarepr` and `impl` are
dedicated declaration forms. Sketch:

```heather
datarepr VecList for List<Tok> {
    R   := VecT,                       // an ordinary kerneltime type in v1
    abs := vec_to_list,
    inv := vec_wf,
    mk Nil  := vec_empty,              // one `mk` clause per constructor;
    mk Cons := vec_prepend,            //   the elaborator checks the list
    fold    := vec_fold,               //   against S's declaration
    // laws follow as ordinary theorem-valued fields, or are `refl` and
    // omitted when definitional (the naive repr omits everything):
    cons_abs := …,
}

datarepr ListTok for List<Tok> := repr::naive();   // the official default
```

Elaboration target: exactly the `class`/`instance` sugar pattern — a
namespace of ordinary declarations (`VecList::abs`, `VecList::fold_law`, …)
with the generated `Repr_ListTok` record assembled at the end. Nothing new
reaches the kernel. `impl f for Rp { … }` likewise elaborates to an
ordinary record value registered at the operation-indexed key.

**Elaborator gaps a landing round must close** (cross-checked against what
instances can hold today, `lib/std/algebra/algebra.hthr`):

1. **The two declaration forms** (parser + elaboration). The novel part is
   not the record sugar (classes already do namespaces-then-record, and
   theorem-valued fields are routine — `assoc := add_assoc`) but the
   **per-inductive record generation**: computing `Repr_S`'s field list
   from `S`'s declaration. Precedent exists in the elaborator's derived
   artifacts (recursors, no-confusion) and in certgen's per-signature
   `CompileNatK{T}` emission; this is that machinery pointed at a
   declaration form.
2. **A name for a parameterized instantiation.** `List<Tok>` is not a
   nameable thing today — this is the *exact* boundary certgen declines at
   ("a monomorphized lowering has no name to spell `embed_T` with",
   `docs/certgen-tier1-source-types-design.md@4acf2fe`). The `datarepr` form is
   itself the minting site: `datarepr ListTok for List<Tok>` introduces the
   monomorph's name, its recursor specialization, and the embed the
   generator asks for. No separate `type` alias feature is required for v1
   (RECOMMENDED: don't add one just for this; let the declaration form own
   the name it needs).
3. **Registry resolution by function-value index** — "find the `Impl` for
   `f` at `Rp`". The operation-indexed-classes machinery already keys
   registration and lookup on the operation; what's new is the *client*
   (the transfer generator / the compiler walk) querying it
   programmatically rather than via surface resolution. Same seam
   compile-typeclass's resolver walk needs anyway.
4. **The outcome sum and `+ E` sugar** — not needed for v1 (byte-free reprs
   have no partial operations, §5.1); when it lands it is surface intent
   over a plain sum (settled), adjacent to `prelude-option-and-friends`.

**As-landed (v1 first half, 2026-08-15), amending §1.4.** Both forms and
`impl` are implemented in `crates/elab/src/datarepr.rs`; acceptance in
`crates/elab/tests/datarepr.rs`. Deviations, each forced rather than chosen:

1. **The artifacts are emitted as surface source and re-parsed**, the choice
   certgen made for its per-signature records and for the same reason: these
   are dependent record types whose field list is computed from a constructor
   list. The consequence is that every generated name must be **nameable** —
   `#` never begins a surface identifier, so a name carrying the sigil
   `issues/unnameable-generated-names.md` points at cannot be written in the
   text that declares it. The names are `Repr_N`, `N_spec_rec`, `Repr_N::⟨clause⟩`
   and the assembled `N`. *Amended 2026-08-16*: they are still the names the
   emission declares, and they are no longer the names the **surface** has —
   `docs/repr-access-spellings-design.md` makes `N::⟨clause⟩` the one spelling
   and refuses the minted ones in user source, which is the same boundary
   `unnameable-generated-names` wants, drawn at resolution instead of at the
   lexer. *Amended again 2026-08-16* (`issues/idiomatic-spelling-pass.md`):
   because the artifacts are re-parsed surface source, the **style** they are
   written in is a standing exercise of the surface's sugar, so the emission
   now writes what a person would — one n-ary argument list spilled across the
   curried Π spine (`Repr_N::fold(B, s0, r)`, not `Repr_N::fold()(B)(s0)(r)`)
   and one unannotated multi-binder λ (`λ B s0 s1 r => …`). The *names* are
   untouched: style and naming are two questions and only the first moved.
2. **The namespace hangs off `Repr_N`, not off `N`** as the sketch has it: a
   member declaration's qualifier has to name a *type* in scope, and `N` names
   the assembled value.
3. **The spec recursor is generated as a named global** (`N_spec_rec`).
   `match` is a form and not a global, so the anchor law has nothing to state
   itself against otherwise. This is what §1.4 item 2 called the monomorph's
   "recursor specialization", and it is per-repr rather than per-type.
4. **Every clause is 0-ary**: each becomes a declaration whose result type is
   exactly the field's type and whose body is the clause. The existing
   currying coercion — the one that lets `op := zop` fill an `A -> A -> A`
   field — then does all the work, including filling a Π-typed *law* field
   from an n-ary `theorem`. A clause must therefore be a name, a call or a
   projection; anything larger is bound to a `fn` first, and is refused
   rather than rendered lossily.
5. **A law clause's binder list includes the `inv` hypotheses**, so a
   hand-written law has to carry them even when `inv` is `True` and they are
   never used. This is real friction on the explicit form (`Bin`'s
   `Succ_abs` needs an `h0` binder it ignores) and the obvious
   fix — letting a clause be applied to the binders the statement quantifies
   over, rather than checked against the whole Π — is deferred, not designed.
   Filed standalone 2026-08-16 as `issues/datarepr-law-clause-inv-binders.md`,
   where the flip of the defaulted `inv` turned the friction into duplication:
   two reprs of one spec type that disagree on `inv` can no longer share a
   law, even when both hypotheses are trivially inhabited.
   *Spent 2026-08-16* (that issue's design section): a law clause that
   mentions one of its statement's own binder names free (`a0…`/`h0…`; `B`,
   `s0…`, `r`, `h` at `fold_law`) is elaborated **under** the statement's
   binders — `Succ_abs := bin_succ_abs(a0)` — and a clause mentioning none
   of them is the whole-Π form, unchanged. Decided syntactically before
   elaboration, never by retry, so each form keeps its own diagnostics.
6. **`inv` is `(r: R) -> Type` and the naive `True` is `Zero = Zero`.** `Nat`
   is a kernel type, so that proposition is in scope wherever a `datarepr`
   is, and `refl` inhabits it. A prelude `True` would be better and belongs
   with `prelude-option-and-friends`.
   *Superseded 2026-08-16* (`issues/true-prop-trivial-hypotheses.md`): there
   is a real `True` now — the kernel's `Unit^0` under a surface name, with
   `trivial` as its canonical inhabitant and η-as-proof-irrelevance giving
   *judgmental* uniqueness of it — and it is what an omitted `inv` defaults
   to. A repr whose `inv` is **written** is untouched: the closure-law default
   is `trivial` exactly when the clause is the trivial one (omitted, or
   written out as `λ r => True`), and `refl` otherwise.
7. **Two rough edges in *using* the assembled value**, both worked around by
   reaching through the namespace, and both worth their own issue:
   `value.fold` is claimed by the builtin vector receiver method before the
   receiver's type is consulted (a name collision with §1.1's field name),
   and projecting a **theorem-valued** field off the assembled record value
   exhausts memory — a user-reachable abort, not a slow check. The namespace
   half of the elaboration is what makes the laws usable at all, which is a
   better argument for it than §1.4's original one.
   *Superseded 2026-08-16* (`docs/repr-access-spellings-design.md` §1): the
   second is fixed and closed, and the first does not reproduce at any repr
   access shape — `.fold` on the assembled value checks. Reaching through a
   namespace is now the *designed* access, not a workaround, and the namespace
   is spelled `N::…` at the author's own name.
8. `datarepr` over **`Nat`** works by writing `Nat`'s constructor list into
   the elaborator: it is a kernel type with no declaration to read one off.

**As-landed (the clause defaults, 2026-08-15), amending §1.4 and the sketch
above.** A repr's *required* clauses are now `R`, `abs` and one `mk` per
constructor; `inv` and `fold` default when omitted, which makes the sketch's
"laws are `refl` and omitted when definitional" true of two data clauses as
well (`issues/repr-fold-via-abs-default.md`). Omitting `fold` was previously an
error, so this is a behaviour change and not only an addition. The rule stays
the one sentence `docs/obligation-records-design.md` §1.2 states: **omitted
takes the default, `?` demands and reports, anything else is checked as today.**

- **Omitted `inv` is `True`**, spelled as the naive repr spells it — since
  2026-08-16 the real prelude `True` and no longer note 6's `Zero = Zero` pun
  (`issues/true-prop-trivial-hypotheses.md`). A generated `refines` signature
  therefore binds `h0: True` and its consumers pass `trivial`; the registry
  statement is unchanged in shape, the binder still being there, which is the
  ratified half of that issue's verdict.
- **Omitted `fold` is the fold *through* `abs`** — §1.1's "the fold need not be
  what runs" taken as the default rather than as permission. Reading `Bin`'s
  hand-written anchor schematically shows what the shape needs and the record
  does not state: a map `S -> R`, because the repr-side step holds its child at
  the carrier while the spec recursor hands it one at `S`. That map is not new
  machinery — it is the spec recursor over the constructor **images**, and
  `bin_of_nat` is exactly it — so the default emits it (`N_emb`) alongside the
  fold.
- **The defaulted anchor law is not `refl`.** `abs ∘ emb = id` is a theorem, not
  a conversion, so `fold_law` is generated as an induction: `N_emb_inv`
  (`inv` of the embedding, one closure law per arm), `N_emb_abs` (the round
  trip, one commutation law per arm and a `j` chain over the recursive
  positions), and `N_fold_via_abs`, the recursor-level equation `fold_law`
  reduces to at `x := abs(r)`. All four come out of the repr's **own** image
  laws, which is the sharper statement of what the default means: at a repr
  whose images are certified, **the fold anchor is derivable rather than an
  independent obligation**. (Consequently no negative control can exhibit a repr
  whose image laws hold and whose defaulted `fold_law` fails; the suite's
  controls aim at the laws instead.)
- **The naive repr is untouched**: its fold is the spec recursor directly, not
  the via-abs default, and every emission stays byte-identical.
- **`fold` and `inv` are listed by `heather obligations`** with `defaulted` /
  `supplied`, so the listing answers "did this repr take the default here?".
  They are still not obligations in the §1.1 sense — a `?` at either is refused
  as a data field — and their `statement` column is the type the clause is
  checked against.

## 2. Partiality and dispatch — the roughest part, worked concretely

The settled policy, restated in one line each:

- **Input-determined partiality = precondition** (canonical). Dispatch
  ladder, per condition, defaulted per condition class and overridable:
  **(1) silent discharge** from context/`inv` > **(2) decide-and-bubble** >
  **(3) manual**.
- **Machine-state-determined partiality = outcome type, forced** (no
  argument-side proof can discharge the model's may-fail); erasable only by
  the strengthening ladder under an explicit capacity bound.
- **Machine-width side conditions are preconditions in kind** whose default
  rung is decide-and-bubble — and most are subsumed by `inv` and never
  surface.
- **Effect bubbling lives only in the generated repr-side layer**,
  composing monadically there. Spec fns stay pure forever.

This section works the three mandated examples and then names the edges
that remain genuinely rough (§2.5) — that honesty is the section's point.

### 2.1 The plumbing the rungs share

The generated layer composes in a plain sum `Out<T, E> = Ok(T) | Err(E)`
with monadic bind; `+ E` on an `Impl` signature is surface sugar for
`Out<·, E>` and nothing more (no grading, no effect system — that reading
belongs to `effects-direction` if ever). `E` is a **per-closure error
enumeration minted at the `runtime_fn` boundary** (RECOMMENDED, see §2.5a):
when the compiler's walk assembles a closure, the failure constructors
contributed by every rung-2 site and every outcome-typed operation in the
closure are collected into one enum, and each generated site injects into
it. Certificates compose arm-wise: the schema is a fold over the body's
bind chain — the same shape as certgen's `cert_body` fold over an
instruction chain, and deliberately so (§3.4).

The **weak certificate** (what the generator emits first, always): success
arm carries the full refinement equation; every failure arm carries `True`.
Sound, honest about what is claimed, silent about when failure happens.
The **strengthening ladder** is then ordinary theorem-proving, never
generator work: a manual theorem showing a failure arm unreachable under a
hypothesis (a discharged precondition; a capacity bound) yields a
strengthened `Impl` — same or pruned body, stronger `refines` — registered
over the weak one. Degrees of honesty; soundness never at stake.

### 2.2 Worked: `index`

Spec side, canonical form: the total guarded function
`nth_g : (l: List<A>, i: Nat, h: i < len(l)) -> A` (the `Option`-returning
`nth` is a different, already-total spec fn and needs nothing from this
section). Repr `VecList` (v2 flavor with a real buffer; the logic is
identical byte-free). The hand `Impl`'s body is the O(1) load; its
`refines`: `inv(r) -> (h: i < len(abs r)) -> load(r, i) = nth_g(abs r, i, h)`.

The precondition `i < len(abs r)` at a *call site* inside a generated body,
by rung:

- **Rung 1, silent discharge.** The generator finds the proof in context:
  the caller's own precondition, a consequence of `inv`, or the `True`
  branch of a dominating decidable test (the decider's soundness lemma
  converts `dec_lt(i, n) = True` into `i < n`). Emitted code: the bare
  load. The proof is `Prop`-erased; nothing runs.
- **Rung 2, decide-and-bubble.** What is emitted, concretely:

  ```heather
  match dec_lt(i, len_impl(r)) {
      True  => Ok(load(r, i)),          // certificate: dec soundness gives
                                        //   h, then the hand Impl's refines
      False => Err(E.IndexOob),         // certificate: True (weak rung)
  }
  ```

  where `dec_lt` is a decider with `dec_lt_sound : dec_lt(i,n) = True -> i < n`
  — precisely `class-ops-prop-vs-bool`'s decided refinement of the Prop
  relation; the ladder's rung 2 is that issue's consumer. `len_impl` is
  itself resolved from the registry (with *its* refinement equation
  rewriting `len(abs r)` to the runtime length — the certificate's `True`
  branch needs `dec` applied to the *spec* bound, so the `len_impl`
  refines theorem is a premise of the arm, not decoration).
  The enclosing `Impl`'s signature gains `+ E`; the failure constructor
  bubbles through the bind chain.
- **Erasure** of a bubbled condition: a manual theorem
  `∀ …, ctx -> dec_lt(i, len_impl(r)) = True` (typically from a caller
  precondition plus `len_impl`'s refines) makes the `False` arm
  unreachable; the strengthened `Impl` returns bare `A`, its `refines`
  proved by case analysis with the `False` case closed by contradiction.
  Bubbled *width/bounds* conditions are **always erasable in principle**
  this way — the asymmetry against `OutOfMem` below is the policy's spine.
- **Rung 3, manual**: the user writes the proof rung 1 couldn't find. Same
  emitted code as rung 1.

### 2.3 Worked: `push`

`push : List<A> -> A -> List<A>` is total in spec. On a buffer-backed repr
its implementation may allocate, and allocation is machine-state
partiality: **no argument-side proof can discharge the model's may-fail**,
because the fundamental alloc primitive's IR carries the `OutOfMem`
possibility (the user's confirmation note: this split is *forced* by that
function's existence). So the `Impl` is outcome-typed, no ladder choice:

```heather
push_impl : R -> A -> Out<R, E>
refines   : inv(r) -> match push_impl(r, a) {
    Ok(r')  => abs(r') = push(abs(r), a)  ∧  inv(r'),
    Err(_)  => True,                       // weak certificate
}
```

**Strengthening under a capacity bound** — the only erasure route:
strengthen the repr, not the operation. A sub-repr `VecListCap(c)` whose
`inv` adds `reserved(r, c) ∧ len(abs r) < c` supports
`push_noresize : R -> A -> R`, total *relative to the machine model given
no-resize* (the settled phrasing), with the plain refines. The theorem that
`push_impl` under that `inv` never takes the `Err` arm is the ladder rung;
it is a statement about the *model* (bounded requests are granted within
reservation), and what the model itself guarantees is the platform
boundary:

- **Platform model (settled)**: the checked failure is bound violation /
  *reported* alloc failure. OS overcommit means actual exhaustion is
  outside the semantics — a recorded trusted-boundary assumption, like
  fuel. The metered-space refinement of this stance (peak-allocation
  theorems) is `issues/memory-bound-certificates.md`; referenced, not
  designed here.

### 2.4 Worked: the `Nat -> u64` narrowing

Machine-width conditions, per the settled resolution, are preconditions in
kind with dispatch-policy defaults — not a third semantic class. Two faces:

- **Inside a maintained repr: subsumed by `inv`, never surfaces.**
  `VecList`'s `inv` carries `len(abs r) < 2^63` (the buffer exists, so the
  bound is *true*, and `inv` is where true facts about a maintained value
  live). An index call that has discharged `i < len` gets `i` fits `u64`
  for free — rung 1 fires via `inv`, and no width check is ever emitted
  inside the repr's own operations. The repr invariant *pays for the width
  facts*; this is the normal case and the reason width conditions were
  refused their own semantic class.
- **At a genuine boundary: decide-and-bubble by default.** A spec `Nat`
  arriving from outside any repr (a `runtime_fn` argument; a spec-side
  computation crossing into a `u64`-backed repr, e.g. `Nat`'s own
  `mk_succ`/`of_nat` image on the `u64` carrier per FINDING 1) has no
  `inv` to lean on. Emitted: `narrow_u64(n) : Out<u64, E>` — the decider is
  the comparison against `2^64`, the sound arm's certificate is the
  injection's commutation with `abs`, the `Err(E.Width)` arm is weak. And
  the asymmetry, stated where it belongs: a bubbled width condition is
  **always erasable in principle** by discharging the precondition
  (`n < 2^64` is a fact about the input); `OutOfMem` is erasable only
  *relative to an assumed capacity*. Same plumbing, different ceilings.

### 2.5 The edges that stay rough (named, with recommendations)

1. **Error-sum identity across separately generated `Impl`s.** If every
   generated `Impl` mints its own error enum, composition needs relabeling
   injections everywhere and certificates chase them. RECOMMENDED: the
   per-closure enum of §2.1 — failure constructors are collected at the
   `runtime_fn` boundary walk and every generated site injects into the one
   closure-wide sum. Cost accepted: an `Impl`'s emitted text is
   closure-relative in its error spellings (parallel to certgen's
   re-derived callee invariants being `Prog`-relative — and retired the
   same way if a prog-extension-style lemma ever generalizes over the sum).
2. **Rung selection changes signatures.** Whether rung 1 or rung 2 fires
   determines whether `+ E` appears — so a *heuristic* choosing rungs makes
   `Impl` signatures flap with the generator's cleverness. RECOMMENDED:
   rung dispatch at an `Impl`'s *definition* is declared (per-condition
   defaults from the settled policy, overridable in the `impl` form), so
   signatures are stable; the heuristic's freedom lives only *inside*
   bodies, where rung 1 vs rung 3 emit identical code and rung 2 only ever
   fires where the declared signature already carries `+ E`. A cleverer
   generator then means fewer runtime checks, never a different interface.
3. **Nonsense-error accumulation is real and stays.** A deep `E.IndexOob`
   in a closure whose spec has no partiality anywhere is honest-but-ugly;
   the weak certificate says nothing on `Err`, which is exactly as much as
   is known. The strengthening ladder is the answer and it is *manual* —
   this design deliberately refuses to make the generator smart enough to
   erase arms, because that smartness would need trusting (or would be
   certified strengthening, which a human can do in the same theorem
   language with better judgment). Degrees of honesty; soundness never at
   stake.
4. **The `Err`-arm certificate's weakness is a choice with a cliff.**
   `Err => True` means a weak-certified closure may fail spuriously and the
   certificate does not distinguish "failed because memory" from "failed
   because the generator emitted a check that can never pass". The
   perturbed-generator negative control for reprgen (§3.5) must include
   exactly this: a body mutated to always-`Err` *satisfies the weak
   refines* — it is refused not by the certificate but by the exactness
   fixtures (a concrete run producing `Ok`), which therefore graduate from
   nice-to-have to load-bearing on the outcome path. Recorded here so the
   landing round prices fixtures accordingly.
5. **Decider provenance.** Rung 2 needs `dec_P` + soundness per condition;
   whether these come from a `Decidable`-style class, from Compile
   instances of the Prop, or from a small hand kit is
   `class-ops-prop-vs-bool`'s open question 1. v1 needs none (no partial
   ops byte-free); the first outcome-path round must pick, and should pick
   *with* that issue, not around it.

## 3. The transfer generator (`reprgen`) — architecture, design only

Certgen's sibling: untrusted-by-construction, heuristic/incomplete allowed,
every output carries a kernel-checked certificate, declining is a supported
answer with a reason, to live in Heather per `generators-in-the-language`.
Certgen certifies spec → IR; reprgen certifies spec → repr-side
implementation (kerneltime objects in v1). They compose in sequence: a
reprgen output is an ordinary Heather `fn` plus theorems, which certgen can
then take to IR — the two certificates composing by transitivity at the
Compile layer, no shared trust.

### 3.1 Phases

Mirroring certgen's four-phase shape deliberately:

- **Phase 0 — resolution.** Collect the callee closure of the target spec
  fn `f` (topo-ordered, certgen's `Prog` discipline) and resolve each
  callee against the `Impl` registry at the chosen repr(s). A callee with
  no `Impl` is recursively a generation target if in-fragment, else the
  decline reason.
- **Phase 1 — eligibility.** `f` is in the fragment iff structurally
  defined over the repr'd inductive (body elaborates to the recursor /
  structural match — the fold-expressible shape), signature repr-mappable
  under the v1 all-occurrences rule (§1.2), and each spec type touched has
  a repr in scope. Honest syntactic predicate; not a soundness boundary.
- **Phase 2 — transcription.** Rewrite the body against the correctness
  basis: the structural match becomes `fold` with the algebra read off the
  arms; recursive occurrences become the fold's accumulator slot; callee
  calls become calls to their registered `Impl`s; construction sites
  become constructor images; on the outcome path, everything strings on
  `Out`-bind per the declared dispatch (§2.5b).
- **Phase 3 — obligation synthesis.** Emit the `refines` statement per
  §1.2's schema (hypotheses from `inv`, conclusion per result type,
  arm-split on the outcome path).
- **Phase 4 — certificate emission.** The proof is a schema fold over the
  transcribed body: `fold_law` opens the anchor, per-arm congruence steps,
  each callee call closed by that callee's `refines`, each image by its
  commutation law, each rung-2 site by decider soundness on `True` and
  triviality on `False`. Structurally this is `cert_body` again — a small
  expression datatype deciding which law applies where, foldable, and (per
  the certgen precedent) the part worth putting in a perturbable library
  file early.

Output: surface text — the `Impl` declarations plus their theorems —
checked by the full pipeline exactly as handwritten code, appended to the
library like certgen emissions. The trust story and the debugging story
("read the file it wrote") carry over unchanged.

**As-landed (v1 second half, 2026-08-15), amending §3.1.** Implemented in
`crates/elab/src/reprgen.rs`; acceptance in `crates/elab/tests/reprgen.rs`.
Three corrections, all found by the hand-run before any code:

1. **Phase 4 is not only a fold over laws — it must emit an induction.** The
   spec function does *not* definitionally equal its own recursor unfolding:
   `f` and the generated `N_spec_rec` are two recursive globals with the same
   arms, and conversion cannot relate them. So every transfer carries a
   `f_is_rec` lemma proved by structural induction, and `refines` is
   `trans(fold_law(…), f_is_rec(abs(r)))`. §1.1's transfer theorem is right
   that the certificate is schematic; what it elides is that the schema
   contains an induction, not just congruences over laws.
2. **The congruence steps must be explicit `j` motives.** The prelude's
   anti-unifying `cong` cannot solve for its function here: the two sides
   differ *inside the recursor's own algebra arguments*, so the least general
   generalization is not the recursive occurrence
   (`issues/congruence-by-anti-unification.md` §3, kernel-confirmed). The
   generator emits `j(ih, λ y q => lhs = motive, refl)` per recursive
   occurrence, chained by `trans` when an arm has more than one.
3. **Phases 0 and 1 interleave.** §3.1 orders resolution before eligibility,
   but the callee set is only known once the arms are decomposed, so the
   implementation runs the fragment check first and scans callees against the
   registry after. The ordering is observable only in which reason a doubly
   ineligible declaration reports.

Not done, deliberately: §3.1 phase 4's "small expression datatype … worth
putting in a perturbable library file early". At this fragment the schema is
*two* lemma shapes, not a tree of law choices, so the datatype would be
scaffolding with no customer until callee-`Impl` resolution and the outcome
path give it branches. The mutation controls it was wanted for are in place
without it (§3.5).

*(Amended by the repr-typed-result stage, 2026-08-15: half of it arrived after
all, and was forced rather than chosen. An arm whose value is at `S` is read
into an **image spine** — constructor nodes down to the recursion's results —
because three artifacts have to walk the same structure in step: the repr side
of the body, `inv` of it, and `abs` pushed through it. It is a Rust `enum` and
not the library datatype §3.1 wants; what it settles is that the datatype's
first branch point is the spine's, not a law-choice tree's.)*

*(Amended again by the callee-resolution stage, 2026-08-15, which was the other
thing §3.1 said would give the datatype branches — and did not. A resolved
callee is a **second node kind of the same spine**, carrying the same four
slots a constructor node carries: an image (`Impl_Rp_g::body()` for
`Repr_N::mk_C()`), a spec spelling (`g(…)` for `C(…)`), a commutation law
(`refines` for `C_abs`) and a closure law (`refines_inv` for `C_inv`). All three
walks — repr spelling, `inv`, `abs` — are unchanged, and the certificate schema
gains no branch at all. The verdict therefore **stands**: the outcome path is
now the only candidate customer, and until it lands the datatype would encode a
tree whose one branch point is a name lookup.)*

**As-landed (callee-`Impl` resolution, 2026-08-15), amending §3.1 phase 0.**
Implemented in `crates/elab/src/reprgen.rs`; acceptance in
`crates/elab/tests/reprgen.rs`. The hand-run found the load-bearing fact before
any code, as it has every round:

1. **An arm's algebra is spelled once and typed twice.** It is fed to `fold` at
   the carrier and quantified over by `fold_law` at `S`, so the only
   expressions an arm may contain are those well-typed under *both* readings.
   That is what forbids a recursive-child binder (§3.3's third bullet, now with
   its reason rather than its symptom), and it is what decides where a callee
   step goes: a resolved callee is spelled `Impl_Rp_g::body(…)` on **both**
   sides — the two readings agree, because the `Impl`'s signature is the spec
   signature with `S ↦ R` and nothing at `S` reaches it from the algebra's own
   binders — and the bridge to the spec function `g` is built in the **closing
   induction**, not at the anchor law. Phase 4's "each callee call closed by
   that callee's `refines`" is exactly right about the ingredient and one lemma
   off about the place.
2. **The `inv` question answers itself, and no new `Repr` field is owed.** A
   callee's `refines` demands `inv` at each repr-typed argument, and the only
   things that can stand there are an image (paid by its closure law), another
   callee's result (paid by that callee's `refines_inv`) or the fold's
   accumulator (paid by the transfer's own `inv`-preservation lemma). **`inv`
   hereditarity** — `inv` of a child from `inv` of the whole, which the stage
   was chartered to expect — is asked for by exactly one shape: a recursive
   child handed to a callee, which item 1 refuses on typing grounds *before*
   the invariant is reached. It is therefore not a missing law but a law only a
   different fold discipline would need; §1.1 and §1.4 are unchanged. Verified
   at `BinC`, where every one of the three payers has content.
3. **The certificate's rewrite chain generalizes from occurrences to sites.**
   Where phase 4 previously indexed the self-calls of an arm, it now indexes
   *sites* — a self-call, closed by the induction's hypothesis, or a resolved
   callee call, closed by the same spine walk that pushes `abs` through an
   image (`refines` reads as a commutation law with the outer `abs` dropped
   when the callee's result is not at `S`, so one walk serves both). Sites do
   not nest: a callee's arguments are read as a spine at `S` and as ordinary
   data elsewhere, and neither admits one, which is what keeps the chain
   linear.
4. **The recursive half landed too.** A callee with no `Impl` that is in the
   fragment is generated first and its artifacts precede the caller's in the
   one emission, so elaborating the text front to back registers each `Impl`
   before the transfer that resolves it. The cycle guard the doc's
   "topo-ordered" implies is defensive only: a callee must be declared before
   its caller, so the surface language cannot spell a mutually recursive pair —
   the same reason non-structural recursion has no fixture.
5. **Provenance is invisible, and that is tested rather than asserted.** A
   caller's emission is byte-identical whether the callee's `Impl` was
   generated by a transfer, written by hand, or (§1.2) certified via-derived —
   the certificate resolves four names and never asks who wrote them, which is
   the cost basis's openness stated as a property.

Two sharpenings found in passing, both free with the above and neither a stage:
an arm may no longer mention the **scrutinee** (it becomes the fold's algebra,
where the matched value is not in scope — previously an emission that could
capture the induction variable and quietly check at the naive repr), and a
self-call's recursive child is read at the recursion **parameter's index**
rather than at its last argument, which un-declines an operation whose `S`
parameter is not last (`issues/reprgen-self-call-args-unchecked.md`, closed:
its other half — a self-call varying a non-recursion argument — is refused by
the elaborator's own recursion check before the generator sees it).

### 3.2 What it consumes

The fold anchor + image laws (correctness basis) of every repr in play;
the `refines` theorems of every resolved callee `Impl`; the dispatch
declarations (§2.5b); on the outcome path, deciders and the closure error
sum. Notably *not* consumed: any byte-level fact — reprgen is complete at
the byte-free v1 scope, which is why v1 can land it.

### 3.3 Decline boundary

Non-structural recursion (until `termination-measures` gives the fragment a
measure story); higher-order arguments; a spec type in the signature with
no in-scope repr; a callee outside the registry and outside the fragment;
mixed repr positions (the all-occurrences rule); any shape whose
certificate schema has no case — with certgen's rule intact: a decline
names its reason, and the checker-accepts/rim-cannot-spell split is a
decline, not drift.

### 3.4 What is shared with certgen, concretely

- **Conventions**: surface-text emission checked by the full pipeline;
  name-prefixing and collision refusal; decline-with-reason; exactness
  fixtures; perturbed-library mutation controls; the frozen-rim/in-language
  walker split when it re-homes (a future `lib/reprgen_code.hthr` under the
  same rules as `lib/certgen/certgen_code.hthr`).
- **Code**: the registry query seam (phase 0) is the same resolver walk
  compile-typeclass needs; the schema-fold certificate machinery is
  `cert_body`'s pattern and plausibly its literal library once both are
  in-language.
- **The direct interface** (the v1 customer): certgen's per-type `embed_T`
  for a parameterized instantiation is exactly what the `datarepr` form
  mints (§1.4 gap 2). certgen does not learn about reprs; it learns a
  *name* — `datarepr ListTok for List<Tok>` gives the monomorph the name
  certgen's rim could not spell, plus the naive repr's images from which
  `embed_ListTok` is generated the way every `embed_T` already is. That is
  deliberately the *entire* v1 coupling: the smallest thing that flips
  `calc.hthr`'s `run` from decline to emission.
- **Via-derived** gives every hand `Impl` a hand-run analogue for free: the
  derived body is the reference the custom body is diffed against, playing
  the role ir_v1's hand-written add section played for certgen.

### 3.5 Negative controls (priced now, per `docs/testing-generated-terms.md`)

A perturbed correctness basis (swap two constructor images) refused at the
commutation law; a perturbed `Impl` body refused by its own `refines`; a
via-derived certificate over a *wrong* equivalence refused; the
always-`Err` mutation of §2.5(4) refused by an exactness fixture (not by
the weak certificate — that asymmetry is the control's point); a forced
emission outside the fragment failing to check.

**As-landed (v1 second half, 2026-08-15), amending §3.3.** The boundary as
implemented, each decline naming its reason:

- **A repr-typed result is deferred** — *spent, 2026-08-15; see the note
  below.* When `f` returns `S`, the fold's
  algebra lives at the *carrier*, so the closing lemma is no longer "the spec
  fn equals its recursor unfolding" but "`abs` pushed through the algebra",
  an induction that chains the image commutation laws. The route is real and
  composes — `hand_run_a_derived_impl_at_bin_where_the_result_is_the_spec_type`
  in the test file is that emission written by hand, and it is the
  specification for the round that automates it. Nothing *parallel* is needed
  — it is the same phases — but it is a stage rather than a tweak, and the
  size is worth recording: it needs a second closing-lemma shape (`abs`
  pushed through the image spine, one commutation law per constructor node,
  with a `j` chain over the argument positions), a generated `abs`
  congruence per repr, and — the part no section currently describes — a
  **third** lemma, `inv`-preservation of the fold, because every commutation
  law demands `inv` at its recursive arguments and the fold's accumulator is
  only known to satisfy it by induction. At `inv = True` that third lemma is
  `refl`, which is exactly why the hand-run does not show it; at the first
  canonical-form invariant it is real. Cost of the deferral, stated plainly:
  at `Bin` (a repr of `Nat`) almost every interesting operation returns
  `Nat`, so this is what keeps arithmetic out of reprgen's reach for now.
- **One parameter at `S`.** A second one would have to be adapted through
  `abs` inside the algebra, which the fold's adaptation does not do.
- **A recursive child may only be reached through a self-call.** It is at the
  carrier on the repr side and at `S` on the spec side, so any other use puts
  a carrier value where the spec body has a spec value — invisible at the
  naive repr, wrong at every other, and therefore refused at both. *(Sharpened
  2026-08-15: the reason under that symptom is that the arm's algebra is
  spelled once and typed twice — at the carrier for `fold`, at `S` for what
  `fold_law` quantifies over — so a child binder has no reading well-typed
  under both. Handing one to a **resolved callee** is the same refusal for the
  same reason: the callee's `Impl` would consume it at the carrier while the
  anchor law holds it at `S`. Lifting the shape needs a congruence for `fold`
  in its algebra argument, which no `Repr` states and which does not follow
  from the fields — that, and not `inv` hereditarity, is what the shape
  actually costs.)*
- **A callee that touches `S`** needs its own `Impl`'s `refines` to close the
  step; resolving those against the registry is the stage after this one
  (§3.1 phase 0's other half). — *spent, 2026-08-15: resolved, generated
  recursively where the callee is in-fragment, and declined by the callee's own
  reason where it is not. See §3.1's third as-landed note.*
- The match must be **total and in declaration order**, with all fields bound
  and no default arm — an honest syntactic predicate, so it declines rather
  than expanding.

Non-structural recursion never reaches the generator: the language's own
termination check refuses it first, which is why §3.3's first decline has no
fixture of its own.

**As-landed (the repr-typed-result stage, 2026-08-15), amending the first
bullet above.** The deferral is spent: a spec fn whose result is `S` now
transfers, and arithmetic at `Bin` is what that buys (`double_spec`, generated,
`crates/elab/tests/reprgen.rs`). The stage's estimate above was right in shape
and wrong in one part; hand-run-first found both before any code, as it has
every time:

1. **The third lemma is exactly as described, and it closes.** `inv`-preservation
   of the fold is an induction over the *spec* value whose arms are the image
   closure laws applied to the inductive hypothesis, one per constructor node of
   the arm's spine. It was hand-run twice before the generator existed: at `Bin`,
   where `inv` is `True` and the lemma is inhabited but says nothing, and at a
   new fixture repr `BinC` — the same carrier under the **canonical-form**
   invariant `bin_of_nat(bin_abs(r)) = r`, whose `Succ_inv` genuinely *consumes*
   its hypothesis. Nothing about the shape changed between the two, which is the
   evidence that `inv = True` was hiding a plumbing question rather than a
   design one. `BinC` earns its keep as the fixture every future `inv`-carrying
   obligation is controlled at; it lives in `crates/elab/tests/support`
   alongside `Bin`, sharing the carrier so the two cannot drift.
2. **The per-repr `abs` congruence is not needed** — the one part of the
   estimate that was wrong. The congruence is wanted in exactly one place
   (carrying `abs` over the anchor law inside `refines`), and there it is an
   inline `j` whose motive is spelled against the derived body's own name:
   `j(fold_law(…), λ y q => abs(f_derived(x̄)) = abs(y), refl)`. That is §3.1
   correction 2's rule applied rather than worked around, and it dissolves the
   question a named per-repr helper would have raised — who owns the name, and
   what happens when two transfers at one repr each emit it.
3. **The fragment predicate gains an "image spine"**: with the result at `S` an
   arm is `S`'s constructors applied down to self-calls on a recursive child,
   with ordinary data at the non-recursive fields. Everything else declines,
   including a numeral where a constructor is expected — the syntactic predicate
   stays honest rather than desugaring. Note what does *not* change: `tail_of`
   still declines. Handing back the recursive child is the third bullet above,
   and a repr-typed result does not rescue it; the fold's algebra does hold that
   child at the carrier, but the anchor law quantifies over the *spec* algebra,
   where the same binder is at `S`.
4. Two conclusions are owed at a repr-typed result (§1.2), so the generator now
   emits `refines_inv` as well, discharged by transporting the third lemma back
   across the anchor law.
5. **A control's limit, recorded because it is easy to mis-read as a control.**
   At `Bin` (and `BinC`) `fold` is *defined* through `abs`, so for an algebra
   that ignores the spec child both sides of `fold_law` are convertible and the
   `refines_inv` transport's *direction* is unobservable — deleting the `sym`
   still checks. The mutation controls therefore aim at the lemma's value rather
   than at its direction, and say so in place. A repr whose fold is not defined
   through `abs` would see it; none exists in the suite yet. — *spent,
   2026-08-15: `UnC` (`crates/elab/tests/support`) folds on the **carrier**
   under a canonical-form `inv`, and there the `sym` cannot be deleted. Both
   halves are needed: at `inv = True` the transported motive is constant, so any
   direction proves it whatever the fold does. The suite pins the control and
   its complement — the same mutation still checking at `BinC` is itself a test,
   so this note cannot be "fixed" by accident
   (`issues/repr-fold-via-abs-default.md`).*

Corrected in passing, and not a stage of its own: calls to `f` in an emission
are now built in **declaration order** rather than as "the other parameters,
then the recursion one". The `Impl` record restates the signature in
declaration order, so an operation taking `S` other than last used to produce
an emission that could not check. Nothing in the suite spelled one; every
existing emission is byte-identical.

## 4. Instance keying

Compile instances key on *syntax* (boxed code is intensional): coherence
per syntactic definition, refactoring invalidates, deliberate.

**RECOMMENDED: datarepr keys the same way, at both layers.**

- A `Repr` keys on the spec inductive's **elaborated declaration** (its
  constructor list with field types, i.e. the same identity the generated
  `Repr_S` record shape is computed from) — for a parameterized
  instantiation, the declaration *plus* the elaborated arguments
  (`List<Tok>`'s identity includes `Tok`'s).
- An `Impl` keys on the pair (spec function's elaborated syntax — the
  `.code` identity Compile already uses — and the repr's name).

The failure mode this avoids: **stale bases surviving a refactor.** Reorder
`S`'s constructors, or change a field's type to something convertible-but-
different, and a nominally-keyed repr still *resolves* — its images and
laws may even still typecheck if arities align — while meaning something
subtly different from what the registry believes; every downstream artifact
cache (per-closure emissions, keyed the way certgen's byte pins are) then
serves results for a type that no longer exists. Under declaration keying
the instance invalidates and must be re-derived — the same
"refactoring a function invalidates its Compile instance" bargain, bought
for the same reason: coherence is predictability, and predictability for a
*compiler cache* has to be syntactic, because the kernel's convertibility
is exactly the thing a cache exists to not re-run.

Consequence accepted with it (same as Compile's): two definitionally-equal
but syntactically distinct inductives do not share reprs. Bridging them,
if ever wanted, is an ordinary certified conversion `Impl` between their
reprs (§5.3's guardrail machinery) — explicit, never resolver magic.

**As-landed (v1 first half, 2026-08-15), amending §4.** A `Repr` keys on
`(the spec inductive's declaration tag, the spelling of the elaborated
arguments)` — the tag is the declaration identity §4 asks for, so editing `S`
invalidates its repr. The argument half is a *spelling* rather than an
elaborated type; for v1's arguments (`Nat`, a nullary inductive) the two
agree, and the gap is worth closing when an argument can be a type expression.
An `Impl`'s operation half is its resolved name — see the note on §1.2.

**As-landed (value parameters, 2026-11-08).** A spec may also be an
inductive applied to closed *value* arguments, `datarepr I64 for SInt(64)`
(`valparam_spec_view`): the field types are instantiated at the arguments
and the key's argument half is their spelling (`"64"`), the same rule.
Each width is its own monomorph; one repr over the telescope is
issues/datarepr-value-parameter-telescope.md. The registry is read back
from tactics by the host request `Repr(ty)` (`repr_of`), which spells a
type's arguments as numerals and answers the repr's global, so a generator
finds `I64::abs`/`I64::emb` from `SInt(64)` alone; the `runtime` generator
does (docs/runtime-fn-setups-design.md §16.13).

## 5. Staging

### 5.1 v1 — byte-free (trigger: already pulled — certgen's parameterized-instantiations stage is waiting on it)

Scope: carriers are ordinary kerneltime types; no layout, no outcome path,
no platform model. Contents:

1. The `datarepr` declaration form elaborating per §1.4 (the two forms, the
   per-inductive record generation, the monomorph naming — gaps 1–3).
2. **The naive repr made official**: `repr::naive()` — carrier = the spec
   type, `abs = id`, `inv = True`, images = the constructors, fold = the
   recursor, every law `refl`. Available for every inductive; *default*
   status stays with the auto-pick meta-program sketched in the issue's
   2026-08-13 note (`repr::inductive_repr()`), which is v2+ — v1's default
   is naive by fiat.
3. **The certgen customer**: `datarepr ListTok for List<Tok> := repr::naive()`
   mints the name and the embed; certgen's parameterized-instantiation
   decline flips to emission by the established fixture-flip discipline.
   As-landed correction (verification probe, 2026-08-15): the originally
   chartered acceptance "`calc.hthr`'s `run` compiles end to end" is NOT
   one decline away and is dropped from v1 — even fully hand-monomorphized,
   `run` sits behind four independent certgen widenings (tier-1 constructor
   fields at a *third* inductive, the binding one; recursive tier-1 result
   types; non-`Nat`-field non-recursive results like `Option<List<Nat>>`;
   the curried higher-order result), each its own generator stage on
   `issues/certifying-generator.md`'s ledger. The minting and the fixture
   flip stand as this item's acceptance.
4. **One non-identity repr, to prove the machinery is not id-only**
   (RECOMMENDED as the v1 stretch item): `Bin` (binary naturals, an
   ordinary inductive) as a repr of `Nat` — `abs` the binary-to-unary
   evaluation, `inv = True`, images *total* (binary is unbounded — chosen
   precisely so v1 needs no outcome plumbing), `fold_law` a real induction,
   one custom `Impl` (`add` on `Bin`) certified **via-derived**. This
   exercises every obligation with non-`refl` content: a genuine `abs`,
   commutation laws that are theorems, an anchor fold that is not what
   should run, the registry, and the transitivity route — all byte-free.
5. reprgen at the matching scope: derived `Impl`s for structural fns over
   repr'd types, phases 0–4, the §3.5 controls. (If the landing round needs
   to split, the declaration forms + certgen customer are the first half
   and reprgen the second; the `Bin` repr's *hand-written* obligations
   don't need reprgen and belong to the first half as its acceptance that
   the record shape is right — the hand-run-first discipline again.)

Acceptance, concretely charterable: items 2–4 checked in the suite (the
`datarepr` forms in a library or fixture file), item 3's flip green with
byte-stability of all existing certgen emissions, §3.5's controls for
whatever reprgen half lands, `scripts/test` full-suite green, no new rail.

Explicitly **not** in v1: the outcome path and dispatch ladder
implementation (designed in §2, first customer is the first partial `Impl`,
which needs bytes or capacity to exist), machine-width anything, layout.

**As-landed (v1 first half, 2026-08-15).** Items 1–4 are in; item 5
(reprgen) is the second half and untouched. Item 4's `Bin` landed with a
genuine `abs` (binary evaluation), a `Succ` commutation law that is a real
three-case induction, an anchor fold that goes through the spec value on
purpose, a `fold_law` that is a real induction over the round-trip lemma
`abs(bin_of_nat(m)) = m`, and `add` at `Bin` **both** ways — the derived route
out of `fold_law`, and a via-derived one whose custom body drops the anchor's
per-step `bin_of_nat`. See the FINDING on §1.2 about when via-derived is
available at all.

**As-landed (v1 second half, 2026-08-15).** Item 5 (reprgen) is in at the
byte-free scope: phases 0–4 over the fragment §3.3's as-landed note describes,
emitting a derived body, its closing induction, its `refines` and the `impl`
that registers it, all checked by the ordinary pipeline. §3.5's controls are
in place as text mutations of a green emission (perturbed algebra step,
perturbed base value, a closing lemma over the wrong statement, a forced
emission outside the fragment) — the forced-emission control runs at `Bin`
rather than at the naive repr on purpose, since the naive carrier *is* the
spec type and a body outside the fragment can still happen to check there.
v1 is therefore complete except for the repr-typed-result transfer, which is
hand-run and specified but not automated.

**Superseded the same day (2026-08-15, commit `d0e6af6`).** The exception in
the paragraph above is spent: the repr-typed-result stage landed, so v1 is
complete without qualification. `reprgen` carries the second closing-lemma
shape (the image spine, `inv`-preservation, `abs` pushed through the spine)
and `arithmetic_at_bin_transfers_when_the_result_is_repr_typed` in
`crates/elab/tests/reprgen.rs` is that transfer generated end to end. §3.3's
"a repr-typed result is deferred" bullet was marked *spent* at the same time;
this sentence was not, and read as a live gap for a day. The estimate there
was right in shape and wrong in one part — the per-repr `abs` congruence is
not needed, an inline `j` against the derived body's own name does that job.

### 5.2 v2+ — bytes (trigger: the first native-lowering / platform-model round)

- **The platform model**: the alloc primitive with reported failure, the
  `Out` path and closure error sums (§2.1), the strengthening ladder in
  anger, the trusted-boundary record (overcommit outside the semantics);
  `memory-bound-certificates` is the metered refinement when a customer
  wants an envelope.
- **Layout is DATA**: the Rust-flavored surface (`Box` for indirection,
  real field order) elaborating to a programmatic layouting value users can
  replace — so an arcane hand layout proves the same §1 obligations, and
  layout choice never touches the proof language. C-ABI mimicry is a
  target-indexed carrier property on top (the target-description-record
  reading from compile-typeclass's 2026-08-13 entry), v2+ within v2+.
- **The width story in anger** (§2.4): `u64`-backed `Nat`, `inv`-subsumed
  widths inside reprs, decide-and-bubble at boundaries.
- **The auto-pick default** (`repr::inductive_repr()`): a meta-program
  inspecting the declaration and picking (linear vec for list-shaped, boxed
  tree as fallback) — generators-in-the-language, ordinary and untrusted
  since every pick's obligations are still checked.
- **Lazy/cursor reprs land here as ordinary citizens**
  (`issues/iterators-as-list-repr.md`): an iterator is a repr of `List`
  whose pipeline operations are registry `Impl`s, and *certified fusion* —
  "this consumer–producer chain materializes no list" — is nothing extra:
  the fused pipeline is one custom `Impl` of the composed spec function,
  certified via-derived against the composition of the stagewise derived
  `Impl`s. That issue's open half (API naturality, cost-honest signatures
  per repr) stays its own; nothing here needs it.

### 5.3 Multi-repr per program — deferred, designed-not-killed (trigger: the first program genuinely wanting two reprs of one type)

Settled guardrails, restated as the activation contract: inter-repr
conversions are ordinary certified `Impl`s
(`abs_B(conv(r)) = abs_A(r)` on `inv_A`), **never compiler-inserted**, and
the via-naive composite is never inserted silently. The open default
question, RECOMMENDED answer: **defaults bind at the `runtime_fn`
boundary** — each `runtime_fn`'s closure carries one repr per spec type,
named explicitly at the boundary or falling to the ambient default;
inference never mixes reprs within a closure in the first cut. Failure mode
avoided: silently materialized conversion chains at seams the user never
sees (the classic quadratic-behind-your-back), and — worse for this
project — certificates whose statements quantify over which repr a value
is in at each program point, a complexity tax with no v1 customer.

Ratified 2026-08-15, with two sharpenings from the review. (1)
One-repr-per-spec-type-per-closure is the *default assumption*, not a
ceiling: any function that actually performs a conversion inherently holds
two reprs of the same spec type, so the activation round must design
multirepr-within-one-function to be at least workable — "assume the reprs
are the same" is the ambient default, mixing is the explicitly-entered
mode. (2) If any conversions ever become automatic, they ride the
language's *general* automatic-conversion mechanisms (there may be repr
pairs close enough that swapping is near-free and livable), never
repr-specific compiler insertion — the never-compiler-inserted guardrail
above is about datarepr minting its own insertion channel, not about the
language-wide coercion story, which owns that decision.

## 6. The hostile-repr falsifier, worked on paper: the sorted-multiset bag

Model: the branching-inductives falsifier — push the discipline until it
cracks or survives, and report which, where, honestly. Repr chosen: the
**sorted-multiset bag** (a binary search tree with multiplicities) as a
repr of `List<A>` with a decidable total order on `A` — chosen over the
rope because it is where the discipline is *most* likely to crack: the
structure forgets exactly what the spec type maintains (order of
insertion).

### 6.1 `abs` and `inv`

`abs : Bag -> List<A>` = the in-order flattening (each element repeated by
multiplicity). Total: fine. `inv` = BST ordering + positive multiplicities.
First observation, immediate and structural: **the image of `abs` is the
sorted lists only.** Non-surjectivity was advertised as the absorber of
machine finiteness; here it absorbs something else — *structure the carrier
cannot express*. The bag is a repr of `List`, but only ever denotes sorted
lists. That is not yet a crack; it is `abs`+`inv` telling the truth.

### 6.2 Constructor images — where it bites

`mk_nil = empty`: fine, laws trivial. `mk_cons(a, b)` must satisfy
`abs(mk_cons(a, b)) = Cons(a, abs(b))` — i.e. inserting `a` must put it
*at the front of the flattening*, which holds **iff `a ≤ min(b)`**. So the
cons image carries an input-determined, *spec-level* precondition:

```heather
mk_cons : (a: A, b: Bag, h: le_all(a, abs(b))) -> Bag
```

Per FINDING 1 this is legal — images are operations under the partiality
policy — and the ladder applies: rung 1 discharges it when the program
builds in sorted order (a merge, a sort's output — real customers); rung 2
emits `dec_le(a, min_impl(b))` and bubbles `E.Unsorted`; rung 3 is manual.
The *unguarded* insert — the operation a bag exists for — is simply **not a
constructor image of `List`**: `insert(a, b)` refines no `List`
constructor, because `abs(insert(a, b))` is `Cons` at an unknown position.
It can still enter the registry, but only as an `Impl` of a spec function
that means it — `insert_sorted : A -> List<A> -> List<A>` (the sorted-
insertion spec fn), for which its refines
`abs(insert(a,b)) = insert_sorted(a, abs(b))` is exactly true, `inv`
preserved. The discipline redirects rather than breaks: *operations that
don't refine constructors refine the spec functions they actually
implement.*

### 6.3 The fold anchor — genuinely awkward, and it holds

`fold_law` demands: fold over the bag = `rec_List` over the in-order
flattening. A bag's *structural* recursion visits tree order, not list
order, so the anchor fold cannot be the structural fold — it must be the
**in-order fold** (fold the left subtree with the continuation "this node
`m` times, then the right subtree"). Definable by ordinary structural
recursion with an accumulator; the law's proof is an induction whose IH
must be generalized over the accumulator, with the glue lemma
`rec_List(alg, xs ++ ys) = …` — the fold-over-append composition. This is
precisely the showcase's documented `append_assoc`/congruence tax
(`docs/showcase/README.md` frictions 2–3) landing where predicted: the
anchor on a concatenation-shaped carrier costs a generalized-IH induction
plus append lemmas. Awkward, slow (in-order folding a tree via `abs`-order
is the derived-not-run case exactly), **but statable and provable with
today's proof vocabulary** — the same over-applied-IH shape
`compile_pushes_eval` already uses. The two-bases split earns its keep
here: nobody runs this fold; it anchors.

(The rope — the tamer sibling — hits *only* this §6.3 shape: `abs` =
flatten, total images (leaf-prepend), and the same fold-over-append
generalized induction, with none of §6.2's preconditions. Worth doing
first in any actual multi-repr round.)

### 6.4 A custom op via-derived, and FINDING 3

`member : A -> List<A> -> Prop`'s decided form `memberb`: derived `Impl` =
the anchor fold (linear); custom `Impl` = BST binary search, O(log n) under
`inv`. Certified **via-derived**: `∀ b, inv(b) -> search(a, b) =
memberb_derived(a, b)` — an induction on the tree using `inv`'s ordering to
prune (the standard BST-search-correct proof), then the derived
certificate by transitivity. Clean; this is the route working as designed,
and the proof is *easier* than direct refinement (the ordering argument
happens once, against a same-carrier reference).

**FINDING 3 — where the discipline honestly stops.** The bag's *point* —
order-insensitive insertion with cheap membership — is not expressible as a
repr of `List` at all: `insert` at an arbitrary position refines no `List`-
valued spec fn except `insert_sorted`, and a program that wants "add these
in any order, then ask questions" is specifying a **multiset**, i.e. a
quotient of `List`, which Heather's spec side does not have. `abs`+`inv`
cannot manufacture the quotient: `abs` must land somewhere, and `List` is
too fine. The discipline **survives by declining** — every obligation above
is either provable or honestly redirected — and what the exercise reveals
is not a datarepr gap but a *spec-side* pressure: if multiset-flavored
programs arrive, the missing object is a quotient spec type (its own
design, nowhere near this issue), after which the bag is its unremarkable
repr with total images. Recorded so the pressure lands on the right door.

Verdict: **the two-bases discipline held** on the hostile pick — one
finding about where images live (FINDING 1, load-bearing), one about the
fold anchor's real cost (the documented append tax, not a new phenomenon),
one honest boundary (FINDING 3, a decline with a forwarding address).

## 7. Literature

What each system settles, adopts, or warns about — read against the two
fixed points that differentiate Heather: the transfer engine is
**untrusted with per-output kernel-checked certificates**, and the
refinement obligation is **abs + inv**, functional, not relational.

### 7.1 CoqEAL (Cohen–Dénès–Mörtberg, CPP 2013): refinements for free

**Mechanism.** The spec/impl link is a *heterogeneous relation*
`R : Spec -> Repr -> Prop`, canonically built from a **spec function**
`Repr -> Spec` or `Repr -> option Spec` (`fun_hrel` / `ofun_hrel`) — i.e.
their primitive points the same way as `abs`, with `inv` encoded as
"not sent to `None`" (partial quotient: `Spec` is a quotient of the valid
subset of `Repr`). Programs are written *once*, generically over an
operational-typeclass signature; correctness is proved only at the
proof-oriented instance; the step to any computation instance is the
**parametricity free theorem** of the closed generic term. Refinement
composition is explicit (`R \o S` with an existential middle), so
refinements stack (rationals → int pairs → generic `C` pairs). Automation
is Coq typeclass resolution used as a logic program over hand-proven
combinator lemmas — so every success is a kernel-checked proof term and
every failure is just "no instance found".

**Adopt.** Three things. (1) The abs-directed function-with-partiality
primitive is direct confirmation of the settled obligation — CoqEAL
independently chose `Repr -> option Spec` over a raw relation, and this
design's `abs` + `inv` is that pair with the domain made a named `Prop`.
(2) The composition lemma proved **once** (`\o`, and Lifting/Transfer's
Theorem 3 — same requirement twice): via-derived transitivity and §5.3's
inter-repr conversion law are instances; the landing round should prove
the general refinement-composition lemma in the library once, not
per-instance. (3) The **eliminator constraint**: CoqEAL had to abandon
`Fixpoint` for `positive_rect` so parametricity lemmas could be stated per
recursion scheme. Heather is accidentally pre-paid here — spec fns already
elaborate through recursors, which is exactly the fold-anchor shape §3's
phase 2 reads off.

**Reject / differ.** Typeclass-search transfer (the paper's own admitted
gaps: polymorphic non-dependent constructions only, no relation
quantification, hand-proven combinator lemmas per inductive) is replaced
by a generator with a *decline boundary* — same net trust (the kernel
checks either way), but refusals name their reason instead of a search
silently failing, and emission is surface text, cacheable and readable.

### 7.2 Isabelle Lifting/Transfer (Huffman–Kunčar, CPP 2013)

**Mechanism.** Two layered packages over the quadruple
`⟨R, Abs, Rep, T⟩` where the transfer relation `T : Repr => Spec => bool`
must be **right-unique and right-total**; `Abs`, `Rep`, and the PER `R`
are derivable from `T`, and `Domainp T` is the invariant. **Lifting**
defines an abstract constant from a raw term, computing the definition,
the *respectfulness* obligation (the one thing the user proves), and the
transfer rule, all by recursion on type structure through **relators**.
**Transfer** rewrites an abstract goal to a raw goal by what is
essentially type inference over a two-term typing judgment, with side
conditions (`bi_unique`, `right_total`, …) propagated compositionally —
notably, a spec-side `∀` transfers to a repr-side `∀ bounded by the
invariant` (`Domainp`), normalized to readable predicates by registered
domain rules. Everything is definitional; outputs are ordinary checked
theorems.

**Adopt.** (1) The decomposition itself: right-uniqueness of `T` *is*
"abs is a function", `Domainp T` *is* `inv` — this design's obligation is
the functional normal form of their relational one, and
`T r s := inv(r) ∧ abs(r) = s` is the canonical bridge if a relational
statement is ever wanted. (2) The quantifier lesson: spec-side `∀`
becomes `inv`-bounded `∀` on the repr side — §1.2's refines schema puts
`inv` hypotheses at exactly that spot, and a future goal-readability pass
should normalize `inv` applied to images into structural facts, their
`Domainp`-rule move. (3) Respectfulness = `inv`-closure + commutation,
split as §1's laws.

**Reject / differ.** **Right-totality** — every spec value has a
representative — is demanded by their `T` and is precisely what machine
finiteness breaks; their own admitted cost is the tell: *partial quotients
get no code equations at all* in Isabelle's code generator (their Table 1).
Heather rejects right-totality at the obligation and buys execution back
through §2's outcome/precondition machinery instead — that trade is this
design's clearest divergence from the literature, made deliberately.
Transfer's product is also theorems (moving proofs between levels), not
programs; the relational generality that serves that goal costs the
first-order equational shape certgen's kit composes with.

### 7.3 Autoref (Lammich, ITP 2013)

**Mechanism.** Automatic *data* refinement in Isabelle: relations built
structurally from **relators**, with representation-changing relators
fusing a parametric part with an invariant by relational composition —
`⟨R⟩list_set_rel = ⟨R⟩list_rel O {(l,s). s = set l ∧ distinct l}`, i.e.
abs+inv packaged as one relation. Per-operation **transfer rules** live in
a priority-ordered database; synthesis solves `(?t, t') ∈ ?R` by
resolution, so the concrete program `?t` is instantiated *as a byproduct
of the proof* — the output theorem is the refinement certificate, and
every heuristic (operation identification via pattern rules, homogeneity
propagation of representation choices, side-condition solving) is
untrusted. Generic algorithms are transfer rules *with premises*,
resolved recursively at low priority so explicit implementations win.
Partial operations are rules with preconditions (`l' ≠ [] ⟹ …`), with
context-propagating `If`/assertion rules to discharge them. Nondeterminism
comes from the enclosing Refinement Framework monad, wrapped as one more
relator.

**Adopt.** Autoref is **reprgen's closest architectural relative**: an
explicitly incomplete synthesizer (the paper accepts incompleteness for
speed after backtracking blowups) that can fail but never lie. Its
priority-ordered rule database is the `Impl` registry with the same
override discipline (specific beats generic — §1.2's hand overrides over
the derived route); its user annotations for implementation selection are
§5.3's never-inserted-silently guardrail arrived at independently; its
preconditioned transfer rules with context propagation are rung 1's
discharge-from-context, relationally spelled. Its admitted per-datatype,
per-recursion-scheme manual setup (~20 lines each) is exactly the cost the
`datarepr` form's generated correctness basis automates.

**Reject / differ.** The nondeterminism monad has no Heather counterpart —
spec fns are total functions and stay so; underspecification is not a
goal, and partiality enters only in the generated layer as outcomes (§2).
Synthesis-inside-the-prover (proof search at every invocation) is replaced
by the certifying-transpiler tempo: emit surface text once, check by the
ordinary pipeline. Fused relation-with-invariant is unbundled into
abs + named `inv` for first-order equational certificates.

### 7.4 Fiat (Delaware–Pit-Claudel–Gross–Chlipala, POPL 2015)

**Mechanism.** Deductive synthesis in Coq: specs are **computations** —
sets of allowed values in a nondeterminism monad, refinement literally
subset inclusion, applied by setoid rewriting. ADTs pair an opaque `rep`
with such methods; swapping representation is one sound step under an
**abstraction relation**, made constructive by the *default
implementation* — the maximally-nondeterministic body that is
automatically a refinement of the old method — after which all work is
ordinary computation refinement. **Honing tactics** (arbitrary Ltac,
untrusted; the kernel rejects unsound derivations) automate domains — the
query-structures library plans SQL-ish specs onto a **`Bag` typeclass**
whose axioms carry the per-operation refinement obligations, with list and
nested-tree instances. Fiat states outright that "abstraction relations
subsume representation invariants": the invariant is carried by the
relation and arrives as a hypothesis in every method refinement.

**Adopt.** (1) The `Bag` class — operations plus refinement obligations
as fields, multiple instances, hierarchical composition — is the `Impl`
registry in typeclass dress, and its "name your indexes, get the rest
derived" ergonomic is the two-bases tempo: mechanical derivation first,
sharpen after, correctness by composed transitivity. (2) The
invariant-as-hypothesis discipline confirms `inv`'s role in every
`refines`. (3) The enforced-modularity trust claim — extend the optimizer
freely, the kernel is the gate — is the untrusted-generator property
stated at POPL; Heather's architecture is that claim with the automation
moved out of the tactic layer into a declining generator.

**Reject / differ.** Fiat's substrate is underspecification: methods that
were never functions, unrealizability handled by weakening specs. Heather
specs are total functions already running kerneltime, so the refinement
direction is representation-only and the nondeterminism calculus (and the
default-implementation trick, whose Heather counterpart is the fold-anchor
derived `Impl` — deterministic, so no maximal-nondeterminism device is
needed) is dead weight. Interactive honing is replaced by batch
decline-or-emit plus the strengthening ladder — theorems in the object
language, not a tactic dialogue.

### 7.5 One-line verdicts

- **CoqEAL**: independent confirmation of abs-directed partial functions
  as the primitive and of eliminator-shaped bodies as the transferable
  fragment; adopt prove-composition-once; reject typeclass-search
  transfer for a declining generator.
- **Lifting/Transfer**: adopt the T = abs+inv decomposition and the
  inv-bounded-quantifier discipline; **reject right-totality** — their
  partial-quotients-get-no-code admission is the cost Heather's §2
  machinery exists to avoid paying.
- **Autoref**: the architectural twin — adopt priority-registry,
  fail-but-never-lie, explicit implementation selection, preconditioned
  rules; reject the nondeterminism monad and synthesis-inside-the-prover.
- **Fiat**: adopt Bag-class-as-registry, invariant-as-hypothesis, and
  enforced modularity; reject nondeterministic specs and interactive
  honing — the ladder is theorems, not tactics.

## 8. Rejected alternatives (shape claims only)

- **Isomorphism as the obligation** (settled, recorded): dies at machine
  finiteness — no `u64` carrier is iso to `Nat`, and forcing surjectivity
  back with an always-available bignum-style fallback smuggles unbounded
  cost into every repr's semantics. Non-surjective `abs` absorbs
  finiteness where it belongs. (FINDING 2 rider: the *naive repr's*
  availability is not this fallback — naive is a separate repr with the
  spec's own semantics, not a hidden escape arm inside a finite repr's
  operations. The rejected thing is semantic, the kept thing operational.)
- **Relational refinement as the obligation** (CoqEAL/Autoref-style
  `R ⊆ Repr × Spec`): abs+inv is its right-total right-unique normal form
  (§7.2), and the functional form keeps certificates first-order equational
  — composable with the existing kit idioms (`cert_body`, calc chains) —
  where relational judgments would need their own composition calculus.
  Relations reappear derivedly (the graph of `abs` on `inv`) wherever a
  theorem wants them; nothing is lost, and the *obligation* stays cheap.
- **Unrestricted `implemented_by`** (trusted replacement of a spec fn by a
  runtime body): never — it is precisely the certificate-free edge the
  whole architecture exists to refuse. (Coq's `Extract Inductive nat =>
  int` is this, by fiat, and is the issue's founding counterexample.)
- **Per-operation simulation relations without a fold anchor** (pure cost
  basis): every operation hand-proved from scratch, nothing transfers,
  and no canonical reference exists for via-derived — the anchor is what
  makes the registry *open* without making it expensive.
- **Compiler-inserted repr conversions / silent via-naive composites**
  (settled guardrail, recorded with its shape-reason): conversion cost
  becomes invisible and certificate statements become path-dependent;
  conversions are ordinary certified `Impl`s a human writes into the
  program text.
- **Graded/effect-typed `+ OutOfMem`**: surface intent over a plain sum
  only; the graded reading is `effects-direction`'s if ever. Buying an
  effect system to spell one error sum inverts the tail and the dog.
- **A third semantic class for machine-width conditions** (settled,
  recorded): width facts are preconditions in kind; `inv` subsumes most,
  decide-and-bubble defaults the rest; a semantic class would triple the
  ladder for zero new discharge routes.
- **reprgen as a trusted elaborator pass** (Rust emitting kernel terms):
  the same wrong altitude certgen's design rejected for the same reasons —
  surface text is checkable by the full pipeline, readable when wrong, and
  is what the in-language re-homing emits anyway.
- **Quotient spec types to license the bag** (§6.4): out of datarepr's
  scope by construction; datarepr must not grow a quotient theory to make
  one repr fit — the pressure is recorded at the spec-side door instead.
