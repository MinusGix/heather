# Repr access spellings: one designed way to reach a repr and its impls — design

Status: **as landed** (2026-08-16). Owner issue:
`issues/repr-access-spellings.md`, spun off `datarepr-surface-ergonomics`
item 5. This document is the design half of that round; the narrative of how it
went is on the issue, once.

The shape it extends was handed over deliberately by
`docs/obligation-records-design.md` §3: an obligation's **printed** path is
`<owner>::<obligation>` — `Impl(add, BinNat)::refines`, `BinC::Succ_inv` —
because an obligation is a member of its owner's namespace and `::` is the
member operator, ratified with the standing instruction that *a lexer artifact
is a cost to pay and not a vote to count*. That round left the form
**print-only**. This one makes it referenceable, and makes it the *only* way.

The principle in one sentence: **a repr's interface is what its declaration
declares, spelled through the name its author wrote, and the elaborator's
minted names are not part of the surface.**

---

## 1. The two-spelling split, and what actually held it up

Before this round the same access had two spellings and neither was designed:

```heather
ListTok().mk_Cons(t)        // project the assembled record value
Repr_ListTok::mk_Cons()     // reach through the minted namespace
```

`docs/datarepr-design.md` §1.4 as-landed note 7 recorded two defects as the
reason the suite reached for the second: `.fold` was claimed by the builtin
vector receiver method before the receiver's type was consulted
(`issues/receiver-method-shadows-record-field.md`), and projecting a
theorem-valued field off an assembled value exhausted memory
(`issues/theorem-field-projection-oom.md`).

Both were re-probed at the top of this round, against the built CLI:

- **The projection defect is fixed** (named projections, `gendefs.rs`), and its
  issue is closed. `ListTok().Cons_abs(…)` and `BinNat().fold(…)` check.
- **The receiver defect does not reproduce on any repr access shape.**
  `resolve_dot` consults the record-field route (lib.rs:4363) *before* the
  method desugaring that the builtins live behind, so a field wins whenever the
  receiver's type infers — and a repr value's type always infers. The residual
  is narrower than the issue's title: when the receiver's type **cannot be
  inferred** (a bare `match` as receiver), control falls through to the method
  path and `fold` is claimed with a diagnostic that says "on a vector receiver".
  That shape is not a repr access point; the narrowed repro is logged on the
  issue and the defect is neither fixed nor designed around here.

So the split was never a design; it was two workarounds, one of which had
already evaporated. Nothing below is bent around either defect.

## 2. The rule

> **Every access point of a repr or an `impl` is reached as
> `<owner>::<member>`, where `<owner>` is the name the *author wrote* — the
> `datarepr`'s name, or `Impl(<op>, <repr>)`. The elaborator's minted names
> (`Repr_N`, `N_spec_rec`, `Impl_R_f`) are not spellable in user source.**

Two corollaries do the work:

1. **The designed name is not the declared name.** `N::abs` is resolved to the
   declaration `Repr_N::abs` by a *resolution alias* (§5), not by declaring the
   member under the designed name. Three reasons, in order of weight: the
   generated artifacts are emitted as surface text and re-parsed, so declaring
   under `N::…` would change emission bytes, which `issues/idiomatic-spelling-pass.md`
   owns and which is a separate deliberate flip; `N` names a **value**, so a
   member declaration `fn N::abs()` would require widening the rule that a
   member's qualifier must name a *type* (lib.rs:5764), for a name that is not
   one; and keeping the two names distinct is exactly what
   `issues/unnameable-generated-names.md` needs — the minted one can grow that
   issue's marker without the surface spelling moving at all.
2. **One spelling means the other one refuses.** A minted name written in user
   source is an error naming the designed form (§6). Generated source keeps
   spelling minted names, and is elaborated in *generated mode*, where the
   refusal is off.

## 3. The access points, enumerated

`N` is the `datarepr`'s name, `C` a constructor of the spec type, `f` an
operation.

### 3.1 Designed: `<owner>::<member>`

| access point | designed spelling | resolves to |
|---|---|---|
| abstraction | `N::abs` | `Repr_N::abs` |
| invariant | `N::inv` | `Repr_N::inv` |
| constructor image | `N::mk_C` | `Repr_N::mk_C` |
| image commutation law | `N::C_abs` | `Repr_N::C_abs` |
| image closure law | `N::C_inv` | `Repr_N::C_inv` |
| the fold | `N::fold` | `Repr_N::fold` |
| the fold anchor | `N::fold_law` | `Repr_N::fold_law` |
| the spec recursor at this instantiation | `N::spec_rec` | `N_spec_rec` |
| the embedding, when `fold` was defaulted | `N::emb` | `N_emb` |
| …and its three lemmas | `N::emb_inv`, `N::emb_abs`, `N::fold_via_abs` | `N_emb_inv`, … |
| an implementation's body | `Impl(f, N)::body` | `Impl_N_f::body` |
| its certificate | `Impl(f, N)::refines` | `Impl_N_f::refines` |
| its invariant certificate | `Impl(f, N)::refines_inv` | `Impl_N_f::refines_inv` |

The list is not arbitrary: **the interface is what the declaration declares.**
The first seven rows are exactly `Repr_N`'s fields other than `R`; the last
three are exactly `Impl_N_f`'s. `spec_rec` is forced — the fold anchor's
*statement* names it (`match` is a form, not a global), so a hand-written
`fold_law` cannot be written without spelling it, and the obligations listing
prints it.

The four via-abs rows are **conditional members**: they exist only at a repr
that let `fold` default (`issues/repr-fold-via-abs-default.md`), because that
is the only case in which the declarations exist. Conditional membership is
deliberate and visible rather than hidden — at a repr that wrote its own
`fold`, `N::emb` is *"`N` has no member `emb`"* with the member list printed,
which is a better answer than a name that silently resolves at one repr and not
at another. The standing customer is the defaults round's own evidence that the
embedding is a real computing function (`crates/elab/tests/datarepr.rs`); an
earlier draft of this design made these internals with no spelling, and that
customer is what refuted it.

Members are 0-ary declarations, so `N::abs` and `N::abs()` both work; the
listing prints the applied form because that is what the statements it prints
contain.

### 3.2 The carrier `R`: value projection, deliberately

`R` is a field of the record with **no namespace member** — the emission
spells the carrier's own type name (`Bin`) wherever it needs it. Its designed
spellings are therefore the carrier's own name, or the projection `N().R`,
which is a type-valued field of an ordinary record value and needs nothing new.
Minting an `N::R` member would change emission bytes to buy a third way of
writing `Bin`.

This is also the honest answer to "which access points are `.`": **`.` is not a
second spelling of the members, it is record projection**, and a repr value is
an ordinary record value. `N().fold` still checks and is still definitionally
`N::fold`; it is not what the documentation, the diagnostics or the suite use,
for three reasons that are all about *when* the value exists and what it costs:
a generator consumes a repr's laws while assembling the very value they are
fields of (`docs/obligation-records-design.md` §1.3 reason 2); projection at a
law field rests on the named-projection device whose declaration cost is
`issues/record-projection-defs-declaration-cost.md`, and η at a neutral receiver
at that size is still a bounded `OutOfFuel`; and a field whose name collides
with a builtin receiver method is one inference failure away from §1's residual.
`N().R` is the one place projection is the designed form, because there is no
member to compete with it.

### 3.3 Internals: no spelling

Refused in user source, with no designed alternative:

- `Impl_N_f::via_derived_obligation` — the `via_derived` **route**'s
  intermediate: the weak abs-image equation the user's own proof discharges
  before the certificate is assembled by transitivity;
- `N_f_impl` — the assembled `Impl` value, which consumers reach through the
  registry (`impl_global`) and never by name.

The line, after the §3.1 correction: **a route's intermediate is an internal;
a declaration's artifact is not.** `via_derived_obligation` is a step in how
one clause was *proved* and says nothing anyone else can rely on; `N_emb` is a
function the repr genuinely has. Promoting an internal later is additive and
costs nothing; retracting a spelling is not, which is why the boundary is drawn
where the evidence is rather than where the symmetry is.

### 3.4 Left spellable, deliberately

- `Repr_N` and `Impl_N_f` **as type names** — `fn p(d: Repr_BinNat)` is the only
  way to write "a value of this repr's record type", and inventing a designed
  spelling for it (the `Repr<List<Tok>>::record_ty` sketch on
  `issues/unnameable-generated-names.md`) is that issue's work, not this one's.
  Recorded as the one place a minted name survives in user source.
- `N` and `N()` — the repr's assembled value. The author wrote `N`.
- reprgen's derived artifacts (`f_derived`, `f_is_rec`, `f_derived_refines`) —
  `docs/obligation-records-design.md` §4.4 deferred namespacing them to
  `unnameable-generated-names` on purpose, and this round does not pre-empt it.

## 4. The grammar cost, paid

`A::b` is a **single lexer token** with exactly one join
(`crates/syntax/src/lexer.rs:130-137`), and the join is adjacency-only, so
`N::abs` needs no grammar at all: it arrives as one `Ident` whose text contains
`::`, exactly as `List::nth` does, and the elaborator splits it. The whole cost
is at the *applied* owner:

```
postfix ::= … | postfix '::' ident        // new
```

`Impl(add, BinNat)::refines` lexes as `Ident("Impl") ( … ) ColonColon
Ident("refines")` — the standalone `ColonColon` token exists already (it is how
`import m::{a, b}` reads) and was consumed nowhere else, so the production is
additive: every expression followed by `::` was a parse error before it.

What it produces is deliberately *not* a new `ExprKind`. The parser renders the
owner structurally — the owner must be `h(a, b, …)` with name arguments — and
emits `ExprKind::Var("Impl(add, BinNat)::refines")`: the printed path, as a
name, whitespace normalized by construction. That buys the round's tightest
guarantee, **printed paths and referenceable paths are literally the same
string**, and it costs no traversal updates in the ~25-variant AST walks
(`reprgen`, `quote`, `spell_expr`, …). An owner of any other shape is a parse
error naming the designed form.

The generality cost is stated rather than hidden: this is a *path* production
for v1's one applied owner, not a general multi-segment path grammar. Modules
will force the general lifting (`A::b::c` is `Ident("A::b") ColonColon
Ident("c")` today), and when they do, this arm is the site to generalize —
nothing here assumes only `Impl` will ever be an owner except the parser's
error message.

## 5. Resolution: an alias, and only as a fallback

`Elaborator::key_of` is the single funnel from a written name to a table key
(globals, inductives, constructors, classes all go through it). The alias lives
there:

> a written name that **does not resolve on its own** and is registered as a
> designed access path resolves to the minted declaration instead.

Fallback ordering, not precedence, so nothing that resolved before this round
can be reinterpreted by it — the same discipline `names::resolve` already
applies to its four readings.

Registration happens where the artifacts are declared: `elab_datarepr` records
the eight repr paths plus one `mk_C`/`C_abs`/`C_inv` triple per constructor,
`elab_impl` records the impl's two or three. Both also record the *reverse*
direction, which is what §6 and §7 consume.

## 6. Diagnostics: the refusal

A restricted name written in user source is refused **at resolution**, before
any "unknown name" can be reported, via a new `NameRes::Restricted(msg)` that
`miss_msg` renders:

```
error: `Repr_BinNat::abs` is a generated name and is not part of the surface —
       write `BinNat::abs`
error: `BinNat_spec_rec` is a generated name and is not part of the surface —
       write `BinNat::spec_rec`
error: `Impl_BinNat_add::refines` is a generated name and is not part of the
       surface — write `Impl(add, BinNat)::refines`
error: `BinNat_emb` is an internal of the defaulted `fold` and has no surface
       spelling — the repr's interface is what its record states
       (`BinNat::fold`, `BinNat::fold_law`)
```

An `Impl(…)::member` path that names no declared `impl` gets its own sentence
rather than the generic qualifier complaint:

```
error: no `impl add for BinNat` is declared, so `Impl(add, BinNat)::refines`
       names nothing
```

**Generated mode** is the exemption, and it is a mode on the elaborator rather
than a property of the text: `elab_generated` raises it for the duration of one
emission, and `Elaborator::elab_generated_source` is the public entry the tests
that re-check emitted text (the perturbed-emission mutation controls) use. This
is deliberate load-bearing preparation: once `unnameable-generated-names` gives
minted names a marker the lexer refuses in user files, *generated text can only
be re-checked in generated mode*, and this round is where the harness learned
to do that. A control that re-checks perturbed generated text through the user
entry point would otherwise start passing for the wrong reason — a refusal on
the name, not on the mutation — which is the one failure mode a mutation
control cannot tolerate.

## 7. `heather obligations`, and printed statements

The listing's `path` column was already the designed form (`Impl(add,
BinNat)::refines`, `BinNat::Succ_abs`); what was not was the **statement**,
which is printed as the source text it is checked as and therefore came out
full of minted names:

```
BinNat  Zero_abs  Repr_BinNat::abs()(Repr_BinNat::mk_Zero()) = Zero
```

That statement is exactly what a user copies to write the proof, so under §2 it
printed something unwritable. Statements are now **de-mangled at the display
boundary** — `Elaborator::obligations()` and the `?` reporting hole — by the
reverse of §5's registration:

```
BinNat  Zero_abs  BinNat::abs()(BinNat::mk_Zero()) = Zero
```

The stored strings are untouched, because the same strings are the *types* the
generated declarations are checked against and rewriting them would change
emission bytes. Display is the only place the two spellings need to disagree,
and it is one function.

## 8. What was migrated

Every hand-written certificate and fixture that spelled a minted name moved to
the designed one: the `reprgen` hand-runs (`Impl_ListTok_length::body()` →
`Impl(length, ListTok)::body()`, `Repr_ListTok::fold()` → `ListTok::fold()`,
`ListTok_spec_rec` → `ListTok::spec_rec`), the `datarepr` acceptance tests, the
obligation-records tests, the record-projection regression file and the CLI
listing's assertion. Two things keep the minted spelling, both because they are
*about* generated source: assertions on emission text, and the hand-forced
emissions the transfer controls feed back in — those go through
`elab_generated_source`, as do the perturbed emissions.

The round's own tests are `crates/elab/tests/repr_access.rs`.

**Emission bytes are unchanged.** Every generator still writes `Repr_N::abs()`,
`N_spec_rec`, `Impl_R_f::body()`. The deliberate flip to the designed spelling
in emissions belongs to `issues/idiomatic-spelling-pass.md`, and when it runs it
is a one-line change to the spelling helpers plus a re-baseline of the emission
assertions — the alias makes it a style choice rather than a compatibility
event.

## 9. Rejected alternatives

- **Declare the members under the designed name** (`fn ListTok::abs()`),
  dropping the alias. Cleanest resolution story, and rejected on three counts
  in §2 — emission bytes, the member-qualifier rule at a value name, and the
  loss of the distinction `unnameable-generated-names` needs.
- **Keep the minted spelling as a deliberate alias** rather than refusing it.
  Cheapest, and it is what "two spellings" *is*. The charter's question is which
  one is canonical; leaving both means the answer is never enforced and the next
  hand-written certificate is a coin flip.
- **Refuse minted names in the lexer now** (the `unnameable-generated-names`
  marker, brought forward). It is the right end state and it is that issue's
  design to make; doing it here would commit the character and the mode split
  on this round's much narrower evidence.
- **A general multi-segment path grammar** (`a::b::c`), rather than one postfix
  arm. Modules will force it; forcing it now means designing module paths as a
  side effect of an ergonomics round.
- **`Impl(f, N).refines`** — a dot on the impl. It reads as projection, it is
  projection, and it would put every certificate citation on the value-must-exist
  side of §3.2 for no gain over the member operator.
