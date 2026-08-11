---
title: Symbol notation on declaring binders: `op as ∙` in class heads and value-parameter lists
status: closed
labels: [design,frontend,traits,ergonomics]
created: 2026-08-09
updated: 2026-08-11
---

Two places want a binder to carry a symbol *as notation* while keeping its
identifier *as interface*, and one device serves both: `op as ∙` — the binder
is still named `op` everywhere a name is consulted, and `∙` is installed as
the local spelling for the declaration's own body.

The rule (revised 2026-08-09, user review): **`as` attaches to a DECLARING
binder occurrence** — a class head's index parameter, or a value parameter in
a `fn`/`theorem` argument list. Never to a *reference*: a linked constraint
slot (`Monoid(op)`) mentions a parameter declared elsewhere, and notation
belongs where the name is born. This is also what makes the device compose:
any function-typed parameter may take a symbol, class or no class, as
temporary local syntax. The curated lexicon caps the blast radius — `as` can
only install symbols that already lex, so the weirdness budget is bounded by
the same table everything else is.

**Customer 1: the class head.** Today `Semigroup`'s law reads
`op(op(x, y), z) = op(x, op(y, z))`; the beautiful spelling is
`(x ∙ y) ∙ z = x ∙ (y ∙ z)`. Writing the head as
`class Semigroup<A>(op as ∙: A -> A -> A)` gets it: the *declared parameter
name* stays `op` — so the empty constraint slot still binds `op`, linked
slots still refer by the caller's own name, diagnostics and the registry
never see a symbol — and inside the class body the index is spelled `∙`,
exactly the installation the constraint symbol slot already performs
(docs/operators-onto-classes-design.md §5(b)).

A symbol-*only* head (`class Semigroup<A>(∙: …)`) was considered and leans
rejected: the empty slot would have no identifier to bind, and generic code
under two constraints of one class would collide on the one symbol. Forcing
the name is the version where nothing downstream changes.

**Customer 2: the value parameter** — this is the `mconcat` question. The
linked form's positional parameter is load-bearing (`any_of`/`all_of`, and
`concat` after [[list-append-symbol]], pass operations that designate no
symbol at their carrier), so `mconcat` cannot move to the symbol slot without
deleting its callers' route. But the parameter's own declaration can carry
the notation:

```heather
fn mconcat<A: Monoid(op)>(op as ∙: A -> A -> A, xs: List<A>) -> A {
    match xs {
        Nil => A.unit,
        Cons(h, t) => h ∙ mconcat(op, t),
    }
}
```

The constraint stays the plain linked slot; callers still pass positionally;
`mconcat_single`'s proof is unchanged. The symbol's scope is the binder's
scope — the rest of the telescope, the result type, and the body — so a
theorem's *statement* may use a parameter's symbol too.

An earlier draft of this issue put the `as` on the constraint slot instead
(`<A: Monoid(op as ∙)>`); rejected on review — that position is a reference,
and it would make the constraint grammar own a feature that has nothing to do
with classes. The three constraint slots (empty / linked / symbol) stay
exactly as the operators round left them.

**The rule to amend.** §5.1 says each referent binds exactly one spelling.
`as` deliberately gives one referent two. The amendment that keeps the
rule's content: the identifier is the binder's **interface** spelling (what
constraint slots, call sites, and diagnostics use) and the symbol is its
**body** spelling — one spelling per role, and §5.2's uniqueness check now
runs over both namespaces (a declaration may not bind `∙` twice, nor `op`
twice, via any mix of slots and `as`).

**The symbol itself.** The intended first customer is the reserved generic
`∙` from [[notation-extensibility]]'s log (2026-08-09): one lexer token,
never designated at any carrier, no fallback name — so away from a binder it
*cannot* mean anything, which is what makes it the right spelling for
`Semigroup`/`Monoid` theory where `+` would whisper commutativity over
`append`. Nothing in the `as` mechanism depends on which symbol; `as +` in a
`CommMonoid` context should work identically.

**Acceptance:** algebra.hthr's three classes and `mconcat`/`mconcat_single`
restated with `∙` bodies, zero changes to any instance, designation, caller,
or proof; a class-free case — a plain higher-order `fn` whose function
parameter takes `as`, used in both body and result type; a negative control
where `∙` appears with no binder in scope (refusal names the symbol and says
no designation and no fallback exist); a duplicate-spelling negative control
(`op as ∙` beside a `∙` symbol slot in one declaration).

## What it assumes from elsewhere

- **[[notation-extensibility]]** owns the lexicon question. Assumed here:
  only that `∙` lands as a curated token (its log already leans this).
- **[[class-default-operators]]** owns whether a class *advertises* a symbol
  to its users' binders. Decided on review (2026-08-09): `as` is strictly
  local and is NOT the advertisement — a declaration gets nice body notation
  without claiming a good default, which is exactly the `Monoid`/`∙` case
  (the lean is that `Monoid` advertises nothing).

## Log

- 2026-08-11: **Landed**, all four acceptance rows. `Param::symbol` carries
  the spelling (`crates/syntax/src/ast.rs`); the parser reads `as` between a
  binder's name and its `:` in both declaring positions; the elaborator pushes
  onto `Cx::op_locals` — the same table the constraint symbol slot pushes onto
  (docs/operators-onto-classes-design.md §5(b)), so there is one installation
  path and no fourth resolution rung. Value parameters install in
  `elab_decl_inner`'s telescope loop (scope: rest of the telescope, result
  type, body); a class head's spellings ride on `Inductive::op_symbols` and are
  installed where the field types are actually elaborated (`lower_ctor`, per
  instantiation), with the use site's spellings cleared first, since a class's
  field types are the class's own source. `∙` lands in the lexer as one token
  (three bytes, hence a three-byte window beside the two-byte one),
  multiplicative precedence, no designation row and no `op_fallback` entry.
  Library: the three algebra classes and `mconcat` restated in `∙`, zero
  changes to any instance, designation, caller or proof. Tests:
  `crates/elab/tests/binder_symbol_notation.rs` (8) and five parser tests.
  Docs: §5.1 amended and a §15 postscript. Decisions taken in flight, all
  three where the spec left room:
  - **A multi-name group refuses `as`**, by the multi-binder round's own
    sentence — a modifier prefixes exactly one name — and with a refusal
    shaped like `self`'s, since one symbol across a shared run would install
    one body spelling for several binders. The group *after* an `as` binder is
    untouched: the mark ends at its own annotation.
  - **A `record`/`inductive` value parameter refuses `as`** (parser-level, by
    name): it is a term the *fields* mention, not a binder with a body to
    spell. Only a class head passes `symbols: true` to `valparam_list`.
  - **`mconcat_single` is left without `as`.** Neither its statement nor its
    proof (`A.unit_r(x)`) spells the operation, so an installation there would
    be a spelling with no use — the noise this issue's own "nothing downstream
    changes" argument is against. `mconcat` carries it; the pair still reads
    as one.
  - **The uniqueness check is symbol-only.** §5.2 over "both namespaces" needed
    new code for one of them: `as` mints no identifier, it gives a second role
    to the one the binder already has, so the identifier half is the existing
    parameter-list rules. `Elaborator::check_symbol_free` is the symbol half,
    and it runs over slots and `as` alike (a class head has its own copy, since
    its head *is* the declaration).
- 2026-08-09: Filed from the algebra.hthr cleanup review; revised same day on
  user review — `as` moved off the linked constraint slot onto declaring
  binder occurrences (class heads and value parameters), generalizing to any
  function-typed parameter as temporary local notation; and `as` decided to
  be separate from [[class-default-operators]]'s advertisement.
- 2026-08-11: User review of the landed round left the record/inductive refusal standing but flagged the reasoning as thin: a record with a value parameter *does* have a body for a spelling — its field types mention the parameter, which is structurally the class-head case. The refusal is really about there being no customer yet plus the installation living in class lowering. If a record shows up whose fields state laws over an operation parameter, lifting the parse-time refusal (parser.rs, valparam_list symbols flag) and installing where record fields elaborate is the shape; reopen or file fresh then.
- 2026-08-11: Second user review pass (2026-08-11): two of the rounds refusals now have open owners. The multi-name-group refusal is REVERSED in [[modifiers-in-shared-binder-runs]] — a modifier attaches to the name it prefixes, per-name, so `g as ∙, h: T` (and `self x, y: T`) will be allowed; not urgent. The record/inductive refusal is promoted from the log entry above into [[record-value-param-symbol]], where an open question belongs.
