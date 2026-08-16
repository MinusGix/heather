# The equation binding and the `split` statement

Design document for two proving-surface features that turn out to share one
node: `issues/match-with-equation.md` and `issues/split-on-arms.md`.

**Status: no kernel change is required, and none is proposed.** Both features
are `crates/syntax` plus a *small* piece of `crates/elab`, and neither adds an
elimination form. The equation binding is one new field on `ExprKind::Match`
plus a motive wrapper written at the `Type` level; `split`/`on` is a parser
desugaring onto that same node, so "it lowers to the same elimination the
`match` path builds" is true by construction rather than by discipline.

The theme that makes them one round: **both are the elaborator writing a term
the user can already write by hand.** The equation binding writes the convoy
motive `λ z => (e = z) -> M z` and the `refl` it is applied to; `split` writes
nothing at all — it is a second *spelling* of an expression that already
exists, chosen for the position (statement, block-final) where the expression
spelling reads badly. Neither is new power, and the value case for each is
measured against the manual route, not against an absence.

## 1. What this round decides

1. **§3 — `match h : e { … }`** binds `h : e = pat` in every arm. Spelling by
   Lean precedent and by a two-token lookahead that costs the grammar nothing.
   Direction **scrutinee = pattern**, measured against the one surviving
   consumer (§3.2).
2. **§4 — the equation binding is refused on an indexed family**, with a
   message saying why. This is a *finding*, not a deferral: the equation would
   be heterogeneous (§4.1).
3. **§5 — `split e;` is a statement that terminates its block**, and a block
   whose statement list ends in a `split` has no result expression. `on
   Ctor(fields) := expr;` arms discharge it. `split` joins `match`/`fun`/`Type`
   on `binder_ident`'s reject list (rule 3 of
   `docs/let-and-blocks-design.md` §5.2).
4. **§6 — `split` is desugared in the parser** onto `ExprKind::Match` with a
   synthesized `motive: None`. Zero new elaborator arms, zero new exhaustive
   walk arms, and the "same elimination" requirement holds by construction.
5. **§7 — `split h : e;` is accepted**, because after §6 there is nothing left
   to decide: it is the same node with the same field set.

Not in scope, and §9 says what each is owed: `nested-goal-discharge`,
`ih-generalization`, `surface-proof-automation`'s `apply`, and the
inversion-record library route the 2026-08-01 demotion log describes.

### 1.1 Findings that change the shape of the issues

**(a) The equation feature is expressible entirely as a motive wrapper, so it
touches no lowering.** The convoy is `λ z => Id(S, e, z) -> M z` applied to
`refl`, and *every* consumer of a motive in this elaborator —
`elab_match_nat`, `elab_match_fin`, `elab_match_data`'s case tree,
`elab_match_wf` — takes the motive as an opaque `Type` over one extra binder.
Wrapping it with a `Pi` before the call is therefore invisible to all of them,
and the arms' side of the deal is a *surface* rewrite: `body ⇝ λ h => body`,
checked by the ordinary `elab_lam_check` against the arm type, which is now an
arrow. So the whole feature is: one field, one `Pi`, one `Lam` wrapper, one
`App` to `refl`. The issue's guess that this is "plausibly the same
motive-synthesis machinery" as `ih-generalization` overstates the coupling —
it needs *no* motive synthesis at all, only motive *decoration*, and it
composes with an explicit `as λ z => M` motive unchanged.

**(b) `split` needs no goal machinery, and using the goal machinery would have
been wrong.** `issues/split-on-arms.md` proposes constructor goals as ordinary
goals with captured contexts. That route hits a hard obstacle nobody costed:
`goal_base = count_holes(decl)` is a **syntactic pre-count** reserved before
elaboration (`lib.rs:904`), and the number of constructor goals a `split`
raises is not a syntactic property of the block — it is the arity of an
inductive the parser has never heard of. The pre-count would have to be
"however many `on Ctor` statements follow", which is only correct because a
missing arm is an error, i.e. the count is right exactly when the program is
right. Worse, the goal route would need per-goal binder *renaming* at discharge
(the binder names come from the `on` head, not the split), a `Cx` surgery no
other goal performs. The desugaring has none of this: constructor arms are
arms, and the elaborator's existing completeness/duplication/arity checks are
the error behaviour §8 asks for, already written.

**(c) The equation direction the one live consumer wants is
`scrutinee = pattern`, and the issue's note is evidence *for* that direction,
not against it.** `issues/match-with-equation.md` says "`step_mono` wanted
`sym`". Read at the source (`lib/ir_v1.hthr:700-710`): the hand-written convoy
binds `e : r = ev1(env, lbody)` — *pattern = scrutinee* — and then every use is
`sym(e)`. So the `sym` is a tax on the direction the hand-written copy chose,
and the feature removes it by choosing the other one. §3.2.

**(d) The three features named in the 2026-08-01 demotion log are not in
competition, and the equation binding is what makes the inversion lemma
*writable in one line*.** `k_bind_inv` (`lib/ir_v1.hthr:602-611`) is written
today with the target varying in the motive — the trick that avoids the idiom —
and it is four lines of motive for a three-constructor result type. That trick
works because `k_bind_inv`'s *statement* is an implication whose antecedent
mentions the scrutinee. It does not generalize: it is available exactly when
the theorem being proved has the scrutinee in its statement, which is what an
inversion lemma is and what a *use site* is not. So the demotion is right about
urgency and wrong about jurisdiction; §10 measures it.

## 2. Where the pieces stand (surveyed 2026-08-05)

### 2.1 `match`

`match_expr` (`parser.rs:1643-1696`): scrutinee with `no_record_lit` set, an
optional `as <expr>` motive, then `{ arm ("," arm)* }`. `Arm`
(`ast.rs:346-352`) is `ctor`, `binders`, `body`, `span`.

Elaboration has exactly two entry points:

- **checking**, `lib.rs:1662` — `Match { motive: None }`: infer the scrutinee,
  `synth_motive` (`lib.rs:2960`) abstracts it out of the expected type when it
  is a local variable, then `elab_match`.
- **inference**, `lib.rs:2245` — `Match { motive: Some(m) }`: three branches by
  the scrutinee's type (forded family, indexed family, plain), each elaborating
  the motive in its own extended context and calling its own lowering.
  `Match { motive: None }` in inference position is an error (`lib.rs:2307`).

`elab_match` (`lib.rs:2401`) dispatches on the scrutinee's type to
`elab_match_forded` / `elab_match_indexed` / `elab_match_data` /
`elab_match_fin` / `ElimEmpty` / `elab_match_nat`. **Every one of them takes
`motive: Type` (over `Γ, z`) and `mlvl: Level` and treats them as opaque.**
That is finding (a)'s substrate.

Arm bodies are checked, never inferred: `elab_arm`
(`inductive.rs:1634-1686`) aliases the fields and ends in
`elab_check(&acx, &arm.body, expected, mlvl)`; `elab_match_nat` checks the two
arms at `M[Zero]` and `M[Succ k]` directly.

### 2.2 Blocks and `on`

`block_body` (`parser.rs:773-804`): the empty-block `{}` special case, then
`while at_kw("let")`, then one `expr()`, then `while at_kw("on")`, then `}`.
`OnStmt` (`ast.rs:207-219`) carries an `OnTarget`, today `Name(String)` for
`?g` or `Stmt(Ty)` for `_: P`. `on_stmt` (`parser.rs:864-899`) dispatches on
one token: a `Hole` or the identifier `_`. **An identifier head is a parse
error today** — "expected `?name` or `_: P` after `on`" — which is what makes
`on Ctor(fields)` strictly additive.

Goals: `new_goal` (`lib.rs:1083`), `solve_goals` (`lib.rs:1175`), the
declaration-scoped `goal_base`/`frozen`/`strengthen_global` invariants
recorded in `docs/let-and-blocks-design.md` §4.3. None of it is touched by this
round; see finding (b).

### 2.3 The surviving hand-written convoy

`lib/ir_v1.hthr:700-729`, `step_mono`'s `LoopIter` arm. Shape:

```heather
match ev1(env, lbody) as λ r =>
    r = ev1(env, lbody)
    -> k_iter(ev1, lbody, r) = Out(vs)
    -> k_iter(ev2, lbody, ev2(env, lbody)) = Out(vs) {
    Stuck      => λ e q => absurd(q),
    OutOfFuel  => λ e q => absurd(q),
    Out(ws)    => λ e q => j(sym(hyp(env, lbody, ws, sym(e))), …),
}(refl)
```

Three things to note, because each is a line item the feature removes: the
motive's **first arrow** is the equation; each arm **λ-binds** it positionally
alongside the real hypothesis; the whole match is **applied to `refl`**; and
the one real use is `sym(e)`.

## 3. Decision 1: `match h : e { … }`

**The equation binder is written before the scrutinee, `name :`, and binds
`h : e = pat` in every arm.**

```
match h : e (as λ z => M)? { C(x, …) => body, … }
```

### 3.1 Why this spelling and not `match e as r with h { … }`

- **It is unambiguous on two tokens and steals nothing.** `:` never continues
  an expression in this grammar (every `TokKind::Colon` site in `parser.rs` is
  a binder annotation, a record-literal field after `{`, or a declaration
  header), so `Ident Colon` immediately after `match` cannot be the start of a
  scrutinee. `::` is a distinct token, so `match A::b { … }` is untouched. This
  is `code {`'s rule 1 lookahead (`docs/let-and-blocks-design.md` §5.2) at a
  new site, and it needs no backtracking.
- **The alternative spends a keyword and collides with the motive.**
  `match e as r with h { … }` needs `with` (a seventh keyword-headed form, and
  rule 1 does not apply to it), and it overloads `as`, which already introduces
  the motive as a *lambda* — `as λ z => T` — so `as r` would be a second,
  bindery reading of the same token. `docs/surface-universe.md` §13 retired
  exactly one such overload (`as z -> T`); re-introducing one to save a colon
  is a bad trade.
- **It composes with the motive instead of competing with it.** The equation
  binder is a prefix on the *scrutinee* and the motive is a suffix, so
  `match h : e as λ z => M { … }` is readable and means what it looks like:
  the elaborator decorates the user's `M`, it does not replace it. The
  surviving convoy needs precisely this (its motive is explicit and dependent),
  so a design that only served `motive: None` would not have retired it.
- **Precedent.** Lean 4's `match h : e with`, Agda's `with … in h`. Coq's
  `destruct e eqn:h` is the postfix spelling and reads worse for a nested
  scrutinee, which is the case that matters here (`ev1(env, lbody)`).

### 3.2 Direction: `h : scrutinee = pattern`

In arm `Out(ws)` the binder is `h : ev1(env, lbody) = Out(ws)` — **not** the
`sym` of it.

The measurement, at the only live consumer. `hyp` has type
`(e: Val) -> (i: Ir) -> (w: Val) -> ev1(e, i) = Out(w) -> …`, so the use site
wants `ev1(env, lbody) = Out(ws)` — scrutinee on the left. The hand-written
convoy chose the other direction and pays `sym(e)` at its single use; with this
direction the use is bare `h`. One `sym` removed out of one use, which is
100% of the evidence available and is also the direction Lean picked. The
symmetric case (`refl`'s endpoints are interchangeable) means the choice is
free at the *construction* site, so the consumer's taste is the whole
argument.

The convoy is correspondingly `λ z => Id(S, e, z) -> M z`, applied to
`refl : Id(S, e, e)`; at `z := e` the motive's domain is `Id(S, e, e)`, which
is what `refl` inhabits. The other direction would be `Id(S, z, e)`, equally
well typed and one `sym` worse downstream.

### 3.3 Lowering

Given the scrutinee `e : S` at level `ℓ_S`, an arm's binders unchanged, and a
motive `M` over `Γ, z : S` at level `ℓ_M`:

1. `M' := Π (Id(S↑, e↑, z)) . M↑` over `Γ, z : S`, at level `max(ℓ_S, ℓ_M)`.
   (`M` is weakened by one because the `Pi`'s codomain lives one binder
   deeper. The `Id`'s components are weakened by one because they live under
   `z`.)
2. Each arm's **surface** body `b` is rewritten to `λ h => b`, unannotated —
   the expected arm type supplies the domain, which is `elab_lam_check`'s
   contract and the reason no `Id` has to be written twice.
3. The existing path builds the eliminator at `M'`. Nothing below `elab_match`
   knows anything happened.
4. The result is `App(elim, refl)` with `dom = Id(S, e, e)`,
   `cod = result↑`, `dom_level = ℓ_S`, `cod_level = ℓ_M`, where `result` is
   `M[e/z]` — i.e. exactly the type the unconvoyed `match` would have had. So
   the equation binding is **type-transparent**: it changes the term and not
   the type, in both checking and inference position.

The binder `h` lands *after* the constructor's fields, which is the only
possible order (its type mentions them) and the one the surface reads.

### 3.4 What it costs, honestly

Nothing at the kernel, and one duplicated elaboration of the scrutinee in the
`as`-motive case (the user writes `e` in the motive too, as the convoy already
did). The emitted term is the same size as the hand-written convoy — the
2026-08-01 cost note stands: *this feature changes who writes the term, not
what it costs*.

Two residues, stated rather than discovered later:

- **A guarded self-call inside a convoyed `match` on the recursion argument
  sees the ih at the convoyed type** `Id(e, k) -> M(k)`, not `M(k)`, so it
  will not typecheck as a bare application. This is inherent to the convoy
  (Coq and Lean have it too) and it fails loudly at the kernel, not silently.
  It does not affect the convoy's actual use — scrutinizing a *sub*-computation
  — where the recursion variable is not the scrutinee.
- **A hole in the scrutinee of a convoyed `match` with an explicit motive**
  is elaborated twice in two different contexts and hits
  `internal: a hole was re-elaborated in a different context`. Pre-existing
  for any expression appearing in both the scrutinee and the motive; the
  equation feature does not add it, and `match h : e { … }` without a motive
  does not have it.

## 4. Decision 2: refused on an indexed family

`match h : e { … }` where `e`'s type is an indexed or forded family is a named
error:

> the equation binding is not available on an indexed family `F`: an arm's
> index varies with its constructor, so `e = pat` would relate two values at
> different types. Case on the index first, or state the equation you want as
> an inversion lemma.

### 4.1 Why this is a finding and not a deferral

For an indexed family the motive binds **two** things (index, then value) —
`lib.rs:2253-2293` for the forded route, `:2274` for the indexed one — and the
value binder's type is `F(n)` for the motive's *own* index variable `n`, while
the scrutinee has type `F(i)` for the ambient `i`. An equation `e = z` between
them is heterogeneous: it is not expressible in this kernel's `Id`, which is
homogeneous by construction. The generalisation that would express it is
`sEq`-over-`Σ` — precisely the forded family's own encoding — so the honest
form of the request is "the inversion principle of `F`", not "the equation
binding on `F`". That is a different feature with a different home
(`issues/surface-existential.md`'s value-indexed Σ, and the inversion records
the demotion log describes), and it is *already* how the corpus solves this.

`Fin` is **not** refused: `elab_match_fin` takes a single-binder motive at
`Fin(Succ k)` for a fixed `k`, so the equation is homogeneous. `Empty` is not
refused either — the convoy over zero arms is well typed and vacuous.

## 5. Decision 3: the block grammar rule

**A block's statement list may end in a `split`, and a block that splits has
no result expression.** In the grammar of `parser.rs`'s header comment:

```
block     := "{" stmt* ( expr on_stmt* | split_stmt on_arm+ on_stmt* ) "}"
          |  "{" "}"                          -- the auto-refl empty block
split_stmt:= "split" (name ":")? expr ";"
on_arm    := "on" name ("(" name ("," name)* ")")? ":=" expr ";"
```

Three sub-decisions:

- **`split` is last.** A `let` after a `split` is a named parse error ("a
  `split` is the last statement of its block: its arms are the block's
  result"). This is the issue's own "the goals themselves are the result",
  taken literally.
- **Arms and discharges share the `on` loop and are told apart by one token.**
  `on ?g` / `on _: P` is a goal discharge (both already parse); `on Ctor` is a
  split arm. So arms stay **order-free**, which was the point of the form, and
  they may be interleaved with real discharges without ceremony. An `on Ctor`
  in a block with no `split` is a named error.
- **Nullary constructors take no parens**: `on Zero := n;`, matching
  `match`'s `Zero => n`.

`split` joins rule 3's reject list (`binder_ident`), because it is a statement
head followed by an arbitrary expression and so cannot take rule 1's
lookahead — the same argument `match` loses on. Residue, stated: a *global*
named `split` would still be callable everywhere except as the first token of
a block's result expression, where it becomes a loud parse error. Nobody has
one, and `special-forms-as-declarations` does not promise to dissolve this one
because `split` is a grammar keyword, not an elaborator convenience.

### 5.1 Why a block expression may split

`docs/let-and-blocks-design.md` §4.3 refuses `on` on a block *expression*,
because a discharge there would mint a nested goal scope. A `split` arm is not
a discharge — after §6 it is an arm of an expression, consumed by the parser
before `Block::ons` is built — so a split-terminated block expression carries
an **empty** `ons` and the §4.3 refusal never fires. The caution
`docs/let-and-blocks-design.md` §6 recorded ("if `split` becomes a statement, a
block expression containing one raises the nested-goal-scope question again")
is therefore answered: it does not, and the reason is the desugaring, not a new
invariant. A real `?g`-discharge in a split-terminated block *expression* is
still refused, by the unchanged check.

## 6. Decision 4: `split` is a parser desugaring

```
{ stmts…  split e;  on C₁(x⃗) := b₁;  …  on Cₙ(y⃗) := bₙ; }
⟿ Block { stmts…, result: match e { C₁(x⃗) => b₁, …, Cₙ(y⃗) => bₙ }, ons: [] }
```

with `motive: None`, so the block's own expected type drives `synth_motive`
exactly as it does for a hand-written `match`.

Why the parser and not the elaborator:

- **It makes the issue's central requirement unfalsifiable.** "It must lower to
  the SAME elimination the `match` path builds" is a *proof obligation* for an
  elaborator-side implementation and a *tautology* for a desugaring. Likewise
  `match-recursion`'s termination analysis and IH-as-guarded-self-call: they
  apply unchanged because there is nothing to apply them to separately.
- **Every exhaustive walk is already right.** `count_holes` (`lib.rs:4988`),
  `scan_splices` (`quote.rs:885`), `expr_mentions` (`inductive.rs:2861`) and
  `certgen` all handle `ExprKind::Match`; a new node would have needed four new
  arms and `count_holes` under-counting is `internal: more goals than the
  pre-count reserved`, not a wrong answer.
- **Error behaviour comes for free and is already the behaviour §8 wants**
  (`inductive.rs:1480-1525`): unknown constructor, duplicate arm, wrong arity,
  missing arm, and "`match` needs a `Nat` or a declared inductive" for a split
  on a non-inductive.

The cost, stated: those messages say **`match`** where the user wrote `split`.
That is a real wart and it is the price of the tautology above. It is not
misleading — the constructor names and the arm in question are named
correctly — and the fix, if it earns its keep, is to thread a form name into
the five message sites, which is orthogonal to everything here. Recorded as
candidate issue material rather than done, because doing it touches five
messages and their tests for a cosmetic gain.

**Paid 2026-08-16** (`issues/diagnostics-name-the-written-form.md`). A
`form: MatchForm` field on the node carries the spelling that built it, and
every message that names a form asks it. The tautology above is untouched and
is the reason the field is safe: what §6 buys is that both spellings build the
same *elimination*, and the elimination is built from
`scrut`/`eqbind`/`motive`/`arms` — nothing that computes a term may read
`form`, which is why it carries a keyword rather than a variant of behaviour.

Two corrections to the paragraph above, found by doing it. **It is seven
sites, not five**, and not the five listed: three of those (unknown
constructor, duplicate arm, wrong arity) never named a form at all and needed
nothing, while the `Fin` arm check, the `Fin` open-length refusal, the empty
type's "takes no arms" and the missing-motive refusal all did. And it was
**not only cosmetic** — the missing-motive message suggested
`match e as λ z => T { … }`, which is not a spelling a writer who typed
`split` can paste; it now suggests `split e as λ z => T;`, and a test checks
that the suggestion checks.

## 7. Decision 5: `split h : e;` is accepted

The equation binding and the split share one node, so a `split` gets the
convoy for the same one-token lookahead and zero extra elaborator code. There
is no argument for refusing it: `split` is a *position*, not a semantics, and
a statement-position case analysis on a sub-computation wants the equation for
exactly the reason an expression-position one does. Refusing would be the
grammar remembering which spelling the user chose, which is the thing §6 is
designed to prevent.

## 8. Error behaviour, exhaustively

| input | message | site |
|---|---|---|
| `on Foo(x) := …` at a `Nat` split | ``` `Foo` is not a constructor of `Nat` ``` | `elab_match_nat` |
| missing an arm | ``` `match` is missing an arm for `Succ` ``` (`Nat`: "needs both a `Zero` and a `Succ(k)` arm") | `elab_match_data` / `_nat` |
| duplicate arm | ``` duplicate arm for `Zero` ``` | both |
| wrong arity | ``` `Cons` binds 2 field(s), found 1 ``` | `elab_match_data` |
| `split` on a non-inductive | ``` `match` needs a `Nat` or a declared inductive ``` | `elab_match` |
| `on Ctor` with no `split` | ``` `on Ctor(…)` is a `split` arm, and this block has no `split` ``` | parser (new) |
| `let` after a `split` | ``` a `split` is the last statement of its block ``` | parser (new) |
| `split` with no arms | ``` a `split` needs at least one `on Ctor(…) := …` arm ``` | parser (new) |
| `match h : e` at an indexed family | §4's message | `elab` (new) |
| `split` as a binder name | rule 3's message | `binder_ident` (new) |

## 9. Issues this round does not fix

- **`nested-goal-discharge`** — untouched, and §5.1 explains why `split` does
  not re-raise it. `Block::ons` still means "the declaration's goal
  discharges", and a split-terminated block expression carries none.
- **`ih-generalization`** — unaffected. The equation binding decorates a
  motive; it does not generalize one. A convoy whose motive also needs
  generalizing is written the way `step_mono` writes it today, with the
  equation now free.
- **`surface-existential`** — §4 hands it the indexed-family case explicitly.
  The inversion-record device is the answer there and this round says so in a
  diagnostic.
- **`surface-proof-automation`** — `apply` raises the same "statement whose
  goals are the block's result" question `split` does, and §5's rule is the
  answer it should reuse: the statement *is* the result, and the block takes no
  result expression.
- **`match-arm-blocks`** (closed) — a split-terminated block *expression* is
  now a thing, and §5.1 records that it does not disturb §4.3.

## 10. Predictions, so they can be scored

1. The `LoopIter` rewrite is **shorter** (the motive loses its first arrow,
   each of three arms loses one λ-binder, the trailing `(refl)` goes, and the
   one `sym` goes) and **no slower**, since the emitted term is the same up to
   the binder that used to be written by hand. If it is slower, the cause is
   the scrutinee being elaborated twice (once as scrutinee, once in the
   motive), which the hand-written form also did.
2. `split` needs **no** elaborator change at all beyond the `eqbind` field
   plumbing. If it needs one, the cause is that a block's result expression is
   somewhere assumed to be user-written — a span-keyed lookup that a
   synthesized node breaks — and the visible symptom would be a goal inside a
   split arm reporting the wrong site.

---

## 11. Addendum: the implementing round, 2026-08-05

### 11.1 The predictions

**Prediction 1 — the `LoopIter` rewrite is shorter and no slower. CONFIRMED,
with the "slower" half being the interesting one.** `git diff --stat` on
`lib/ir_v1.hthr` is `7 insertions(+), 8 deletions(-)` for the arm itself: the
motive loses its first arrow, three arms lose a λ binder each, the trailing
`(refl)` goes, and the one `sym(e)` becomes a bare `h`. Capped release checks
(`ulimit -v 8388608 -t 300`) before and after, two runs each:

| | run 1 | run 2 |
|---|---|---|
| before | 69.6 s | 67.8 s |
| after | 69.7 s | 64.9 s |

Same, inside the noise — which is the *expected* result and the point of the
2026-08-01 cost note: the elaborator emits the term the user was writing, so
the feature moves who writes it and not what it costs.

**Prediction 2 — `split` needs no elaborator change at all. CONFIRMED, and
measured stronger than stated.** `split`'s entire implementation is
`Parser::split_result` plus an `OnTarget::Ctor` variant; the elaborator's only
`split`-shaped line is an `internal:` arm in `solve_goals` for a variant that
cannot reach it. The acceptance test is stronger than "convertible": the two
declarations' bodies are **byte-identical** under `{:?}`
(`a_split_emits_the_same_term_as_the_match`), which is the assertion a future
elaborator-side `split` would have to break deliberately.

### 11.2 What the round found that no section above predicted

**A live shift defect in the tier-0 case tree, and the convoy is what exposed
it.** `inductive.rs`'s `case_tree` composes the motive with an injection
twice: into `l_expected`, which lands one binder past `cx`, and into
`inner_motive`, which lands **two** — as the `embed(&cx.gamma, 2)` on that very
line says. Both used `injected(…)`, whose summand annotations were fixed at
`shift_local(d + 1)`. So every `Γ`-variable inside an *inner* injection's
annotations was one short, and the symptom is a kernel `LevelMismatch`, never a
wrong answer.

This is **the same defect** the 2026-08-04 generator round fixed in
`wf_case_tree`, `idx_case_tree` and `indexed_case_tree`, and it names a
refinement to axis 6 of `docs/testing-generated-terms.md`: three constructors
and an open payload are **not sufficient**. A third condition is needed —
a *dependent* motive. At a non-dependent one `z` never occurs in `M`, so the
bad annotations are substituted away before the kernel is ever shown them, and
every existing tier-0 test at three constructors and an open payload passed.
The minimal reproducer, now pinned in `crates/elab/tests/inductive_tier0.rs`
beside its two controls:

```heather
inductive Res3<A> { Stuck, OutOfFuel, Out(v: A) }
fn idr<A>(r: Res3<A>) -> Res3<A> { r }
theorem idr_id<A>(r: Res3<A>): idr(r) = r {
    match r as λ z => idr(z) = z { Stuck => refl, OutOfFuel => refl, Out(v) => refl }
}
```

The convoy found it because the convoy makes the motive dependent **by
construction**: `Π (e = z). M` mentions `z` whether or not `M` does. That is
worth recording as a property of the feature, not only of the bug — the
equation binding is a general-purpose stress test for every motive consumer in
the elaborator, and running it over the `Wf`, indexed and forded lowerings is
the obvious next sweep.

### 11.3 Corrections to §3.4's residues

Neither residue bit in practice, and one is smaller than stated: the
scrutinee-elaborated-twice hazard only exists in the explicit-motive spelling,
because that is the user writing `e` twice, and the hand-written convoy had it
too. The `match h : e { … }` form (motive synthesized) elaborates the
scrutinee once.
