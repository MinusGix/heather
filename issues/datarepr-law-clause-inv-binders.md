---
title: A law clause has to spell the inv hypotheses it ignores
status: closed
labels: [design,frontend,ergonomics]
created: 2026-08-16
updated: 2026-08-16
---

`docs/datarepr-design.md` §1.4 note 5, filed standalone after the note's
friction became duplication rather than noise
([[true-prop-trivial-hypotheses]] half 1, 2026-08-16).

A per-constructor law's statement quantifies over the repr's `inv` at every
recursive argument, so a hand-written law clause must bind those hypotheses
even when it never uses them. The note already records the obvious fix and
defers it: let a clause be **applied to the binders the statement quantifies
over** rather than checked against the whole Π.

What made it visible: a law's hypothesis is the repr's OWN `inv`, and two
trivially-inhabited `inv`s are not convertible with each other. Before the
defaulted `inv` became the prelude `True`, `BinNat` (which writes
`inv := bin_inv`, an equation) and `BinMin` (which takes the default) could
share one `bin_succ_abs_law` because both hypotheses were `Zero = Zero`.
They no longer can: `crates/elab/tests/support/mod.rs` now carries
`bin_succ_abs_law` (h0: (Zero = Zero)) and `bin_succ_abs_true` (h0: True) —
the same theorem twice, differing only in a binder neither body mentions.
That is one fixture, not a user report, but it is the shape any two reprs of
one spec type will hit.

Not the same want as default argument values ([[named-arguments]], this
issue's half-2 sibling): defaults fill an argument at a CALL, this fills a
binder at a DECLARATION. Neither implies the other.

## What it assumes from elsewhere
- **[[true-prop-trivial-hypotheses]]** owns the defaulted `inv`. Assumed
  here: only that a repr's `inv` is whatever its own clause says, so two
  reprs of one spec type can disagree on it.

## Design (2026-08-16)

**The clause form.** A law clause — `C_abs`, `C_inv` or `fold_law` — may be
an expression elaborated **under its generated statement's binders**, so
`Succ_abs := bin_succ_abs(a0)` fills a statement quantifying over
`(a0: R) -> (h0: inv(a0)) -> …` without spelling the `h0` it never uses.
The names in scope are the statement's own binder names, which are the
generator's fixed positional convention and are already printed by every
statement (`?` at the clause, `heather obligations`): `a0…` the
constructor's arguments in declaration order, then `h0…`, one `inv`
hypothesis per recursive argument in order; for `fold_law`: `B`, `s0…` (one
step per constructor), `r`, `h`. The implementation reads the names off the
same binder lists the statement schemas are built from (`law_binders`,
`fold_law_binders`), so clause scope and statement cannot drift.

**How the two forms are told apart.** Syntactically, before any elaboration
— never by retrying a failed check. A clause whose expression mentions at
least one of its statement's binder names **free** (the clause's own λ /
`match` / `let` binders shadow, exactly as they would under a real λ) is
the applied form: it is wrapped, at the AST and before the splice, in one
unannotated multi-binder λ over the statement's binder list, and then
spliced and checked exactly as any inline clause is. A clause mentioning
none of them is the whole-Π form, checked as today, diagnostics included.
The rule agrees with what scoping under the binders would do — inside
`λ a0 h0 => …` those names resolve to the binders first — so "mentions a
binder name" and "is meant to be under the binders" coincide. Pinned
consequences:

- a wrong whole-Π value mentions no binder name, stays on the whole-Π
  path, and keeps the whole-Π diagnostic;
- a wrong applied clause fails the **kernel** under the binders, reported
  at the clause's own span with the generated declaration quoted;
- a clause naming a binder that does not exist (`a5`) mentions no actual
  statement binder, stays whole-Π, and gets the ordinary unknown-name
  diagnostic naming `a5`;
- an inline λ that binds the statement's names itself
  (`λ a0 h0 => bin_canon_succ(a0, h0)`) is the whole-Π form — the walker
  is shadow-aware, and the pre-existing inline-clause test pins it;
- within a law clause the statement's binder names shadow same-named
  globals (the shadowing an explicit λ would impose anyway); a global
  named `a0` is reachable by binding the clause to a `fn` first.

**Mechanics.** The wrap happens in `written_clauses`
(crates/elab/src/datarepr.rs), on the clause's AST, before `Splices::add`.
The generator's emission is byte-identical — the generated theorem body is
still one placeholder name — and everything downstream (splice, span
provenance, the clause-located diagnostic, `provenance: inline`) is the
existing inline-clause machinery. The λ stands in checking position against
the generated Π, so unannotated binders are exactly the idiomatic emission
style.

**Non-goals.** This is a declaration-site binder fill only. Call-site
default argument values remain [[named-arguments]]'s half; the generated
statements, the defaulted `inv` and every emission byte are untouched.
`impl` clauses (`refines`, `refines_inv`) are outside this issue's charter;
if their hypothesis binders accumulate the same friction, that is a new
issue against `elab_impl`.

## Log

### 2026-08-16 — designed, landed, closed

The design above, implemented in `crates/elab/src/datarepr.rs`: a
free-mention walk over the clause's AST (`mentions_free`, shadow-aware
through λ / `match` arms / block `let`s / Π binders) against the statement's
binder names, read off the same lists the statement schemas are built from
(`law_binders`; `fold_law_ty`'s binder list split out as
`fold_law_binders` so both readers share it). An applied clause is wrapped
in one unannotated multi-binder λ over those names in `written_clauses`,
before the splice — the emission is byte-identical (the generated theorem
body is still one placeholder) and every downstream mechanism (splice,
clause-located diagnostics, `inline` provenance) is the existing
inline-clause machinery.

The duplication retired: `crates/elab/tests/support/mod.rs` drops
`bin_succ_abs_law` and `bin_succ_abs_true`, and `BinNat` (written
equation `inv`) and `BinMin` (defaulted `True`) both write
`Succ_abs := bin_succ_abs(a0)` — one law, cited by two reprs that disagree
on `inv`, which is exactly the shape the issue was filed on.

Tests (`crates/elab/tests/datarepr.rs`, applied-clause section, +8): the
applied form under both `inv`s consumed afterwards at a neutral value in
checking position; an open element type with a non-recursive argument in
front of the recursive one (`a0`, `a1`, `h0` all distinct); a clause that
genuinely consumes `h0` (`BinC`'s closure law applied); an applied
`fold_law`; the shadow control (an inline `λ a0 h0 => …` stays whole-Π —
also pinned independently by `obligation_records`'
`an_inline_datarepr_clause_law`, which predates the round); and three
negative controls, each guarded against parse-error false greens — a wrong
applied clause refused by the kernel (`NotConvertible` at the clause), the
hypothesis passed where the value goes (kernel refusal), and a
non-existent binder name (`a5`) getting the ordinary `unbound name \`a5\``
diagnostic with the generated statement quoted, which is what shows the
binder names that do exist. Whole-Π regression coverage rides on `BinC`
and `UnC`, untouched.

Non-goals held: no generated statement moved, the defaulted `inv` is
untouched, and no generator emission byte changed (the one generator edit
is the binder-list split, string-identical by construction). Declaration
vs call site stays as filed: default argument values remain
[[named-arguments]]'s half.

