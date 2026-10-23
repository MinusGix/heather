# `let`, blocks, and the special-form binder traps

Design sketch for three open issues that turned out to be one cluster:
`issues/annotated-let-swallows-the-equals.md`, `issues/match-arm-blocks.md`,
`issues/j-binder-parse-trap.md`. Round pattern as usual: this document first,
the implementing round against §9's acceptance list.

**Status: no kernel change is required, and none is proposed.** Everything
below is `crates/syntax` plus a small, purely additive piece of
`crates/elab`. The `let` fix is one flag in one position plus one line in
`atom`; the block form is a new `ExprKind` over the *existing* `Block` node
and the *existing* alias mechanism; the binder traps are three lookahead and
shadowing rules keyed on a property each form already has.

The three issues share a theme worth naming, because it is what makes them one
round rather than three: **each is a place where the grammar spends a token or
a name on a special form and never wrote down what that costs the ordinary
program.** `=` is spent on equality and quietly makes an annotated `let`
unwritable; `{` is *believed* to be spent on a record literal and so a block
was never tried; six identifiers are spent on keyword-headed forms and only
one of the six (`code`) pays rent by lookahead.

## 1. What this round decides, and what it does not

Three decisions, each landable alone:

1. **§3 — the `let` annotation position** reads its type with the comparison
   rung suppressed, and the parenthesis escape hatch that `no_eq`'s doc
   comment already promises is made real.
2. **§4 — a block expression** `{ stmt* expr }` in *prefix* expression
   position, reusing the existing `Block` node, carrying **no** `on`
   discharges.
3. **§5 — the special-form binder traps**, fixed by three rules over the
   *whole* set of six keyword-headed atoms rather than a patch for `j`.

Not in scope, and §6 says what each is owed: `nested-goal-discharge`,
`split-on-arms`, `effects-direction`, `special-forms-as-declarations`,
`case-algebra-definitions`.

### 1.1 Findings that change the shape of the issues

Recorded first, because two of the three issues are the wrong size as filed.

1. **The `let` gap is much wider than `Nat`, and its root cause is not
   `ty()`.** The issue and three docs
   (`docs/surface-function-types.md:507-513`,
   `docs/surface-value-parameters.md:133-137`,
   `crates/elab/tests/value_parameters.rs:143-148`) all describe it as "`ty()`'s
   equality case takes the first `=` it sees". That is true of `let n: Nat = 3;`
   and false as a general account. `ty_atom` bottoms out at
   `parser.rs:915-916` in `self.expr()`, and it is **`expr()`'s comparison
   rung** (`parser.rs:947`, `986-1014`) that eats the binder `=` — so the gap is
   *every* annotation that reaches that fall-through, not the ones that look
   like equations. Verified by capped experiment (§2.4): `let q: P = p;` at a
   declared `record P` fails; `let g: Nat -> Nat = fun x => x;` fails;
   `let x: (Nat) = 3;` fails. What works is exactly the set of `ty_atom`
   productions that **return early** — `Type<n>`, `[T; n]`, `D<A>`, `Ctx`,
   `TyCode(g)`, `Code(g |- T)`, `$a` — which is why
   `crates/elab/tests/in_language_fold.rs:71` could work around it with a
   *vector*-typed annotation and why nobody noticed how wide it is.
2. **Option 2's own proposed spelling does not parse today either.**
   `let p: (a = b) = pf;` fails with `expected =, found Semi` (§2.4, `u1`) —
   the parenthesised group falls through `group_is_type` to `expr()`, which
   then eats the binder `=` just the same. So "require parentheses on an
   equality annotation" is not a spelling that already works and merely needs
   to be made mandatory; it is a spelling that must be *created*. This does not
   change the verdict, but it does change what the acceptance list must
   contain.
3. **`no_eq`'s documented parenthesis escape hatch is not implemented, and one
   live diagnostic is therefore lying.** `parser.rs:93-94` says of `no_eq`
   "Same shape as `no_record_lit`: set in the punctuation contexts, and the
   escape hatch is a parenthesis." There is no `with_eq(false, …)` anywhere —
   the only four call sites are `with_eq(true, …)` (`parser.rs:990`, `997`,
   `1528`, `1532`), and neither bracketed context (`atom`'s `LParen` arm,
   `parser.rs:1311-1318`; `ty_atom`'s, `parser.rs:839-844`) clears it. So
   the `CHAIN` message's advice at `parser.rs:1003-1006` — "parenthesise the
   one that is meant to be an operand" — is **false**: `a = (b = c)` is a parse
   error today (§2.4, `w1`). This round's mechanism fixes that as a side
   effect, and §9 requires the test.
4. **The block/record-literal collision is not head-on, and no lookahead
   heuristic is needed.** A record literal is a **postfix** form on a *name*
   head (`parser.rs:1090-1102`: it fires only when the already-parsed
   expression is a `Var` or a `TyApp` over a `Var`). A **prefix** `{` in
   expression position is a parse error in every production today —
   `atom`'s final `match` has no `LBrace` arm and falls to
   `parser.rs:1325`'s "expected an expression". Verified (§2.4, `t2`, `t3`).
   So the disambiguation is **positional**, exactly the argument
   `docs/surface-fin-indexing-design.md` §5.1 made for postfix `[`, and
   `group_is_type` is the *wrong* precedent to reach for. This makes question 2
   materially smaller than `issues/match-arm-blocks.md` supposes.
5. **`j` is neither the only binder trap nor the worst one.** Six
   keyword-headed atoms exist (`Type`, `match`, `calc`, `refl`, `j`, `fun`;
   §5.1), of which exactly one — `code` — pays for its name with a lookahead.
   Four of the six produce a parse error at a use; **two produce a silently
   wrong term**: `let refl = n; refl` elaborates the *use* as `ExprKind::Refl`
   and dies at "`refl` needs an `=` expected type", and `let Type = n; Type`
   reaches the kernel as `Type<0>` and dies at `LevelMismatch` (§2.4, `t5`,
   `u4`). A fix that only unblocks `j` leaves the two dangerous ones standing.

### 1.2 The question this round answers and does not fix

`issues/match-arm-blocks.md` speculates that a shared block form "likely
subsumes `nested-goal-discharge`'s wish for a hole inside an `on` right-hand
side — check when designing." **Checked: it does not, and cannot.**

`nested-goal-discharge`'s refusal is not a grammar limitation. It is
`crates/elab/src/lib.rs:838-843` (`new_goal` refusing while `frozen`),
`lib.rs:924` (`solve_goals` setting `frozen` before the first discharge) and
`lib.rs:952`/`:993` (`strengthen_global(&t, self.goal_base)` on every
solution). The strengthening is sound *exactly because* no goal occurrence
survives in a payload, and a `GlobalSubst`'s payloads are not telescoped among
each other (`crates/kernel/src/subst.rs`, as that issue states). Lifting it
needs discharge in **dependency order** — a graph over "goal A's solution
mentions goal B", cycle rejection, reverse-topological substitution. That is
an elaboration algorithm; no amount of grammar produces it.

The relationship runs the other way, and it is why §4.3 decides what it does:
a block expression must **decline** `on` discharges precisely because
accepting them would mint a nested goal scope, which is the thing that
mechanism cannot yet serve. Recorded here so the speculation stops
propagating; the acceptance list carries the diagnostic that says so at the
`on`.

## 2. Where the pieces stand (surveyed 2026-08-02)

### 2.1 The `let` statement and the annotation position

`let_stmt` (`parser.rs:651-697`) is four forms sharing one binder token:
destructuring (`:659-675`), `let code x` (`:678-685`), and the plain
`let name (: ty)? = expr ;` (`:686-696`). The annotation is
`Some(self.ty()?)` at `parser.rs:687-692`; the binder is `expect_eq`
(`parser.rs:693`, defined `:741-747`), which also carries the `==`-is-not-
Heather hint.

`ty()` (`parser.rs:756-800`) tries a binder group, then `ty_atom`, then a
right-associative `->`. `ty_atom` (`:829-917`) is a ladder of early returns —
`univ` (`:832`), a `group_is_type`-guarded paren (`:839`), `Ctx`/`TyCode`/
`Code`/`$` (`:850-874`), `[T; n]` (`:876`), `D<A>` (`:889`, backtracking on a
following `(`) — ending at `let lhs = self.expr()?; Ok(expr_as_ty(&lhs))`
(`:915-916`).

`expr()` (`:937-959`) is where the `=` goes: `expr_bp(0)`, then
`if self.no_eq { lhs } else { self.comparison(lhs)? }` (`:947`), then the
arrow fall-through. `comparison` (`:986-1014`) is the single non-associative
rung shared by `=`, `<=` and `<`; its doc comment at `:981-985` already names
this issue as the reason a trailing `=` is exempt from the `CHAIN` diagnostic.

`no_eq` is declared at `parser.rs:95` with `with_eq` at `:1035-1040`; see
finding 1.1(3) for the state of its escape hatch.

### 2.2 Blocks, arms, and how a `let` elaborates

`Block` (`ast.rs:155-166`) is `stmts`, `result`, `ons`, and its doc comment
says outright: "Blocks exist only as declaration bodies for now, so 'end of
block' and 'end of declaration' coincide — that is also the scope of a goal."

`block()` (`parser.rs:623-631`) clears `no_record_lit` and calls `block_body`
(`:633-649`), which is `while self.at_kw("let") { … }`, then one `expr()`,
then `while self.at_kw("on") { … }`, then `}`. An `on` before the result gets
a named error (`:638-641`). The all-`let`s-first shape is structural, not
incidental.

A `match` arm's body is `let body = self.expr()?` (`parser.rs:1469`) — the
single line `issues/match-arm-blocks.md` is about. Nothing else in the arm
grammar is involved.

Elaboration of a `let` is **aliasing, not binding**:
`elab_decl_inner` walks `decl.body.stmts` at `lib.rs:677-745` and pushes
`Rc::new(Alias { name, depth: cx.names.len(), term, ty, level })` onto
`cx.aliases` (`:719`, `:738`); the annotated case elaborates the type and
**checks** the right-hand side against it (`:731-735`), the unannotated case
infers (`:736`). Then `elab_check(&cx, &decl.body.result, …)` (`:746`) and
`solve_goals(&decl.body.ons, …)` (`:748`). No kernel binder is introduced by a
`let` anywhere. This is the fact that makes §4 cheap.

`count_holes` (`lib.rs:4117-4223`) is an exhaustive walk with no catch-all,
and it walks the declaration's `stmts`/`result`/`ons` explicitly at
`:4204-4221`. Under-counting is fatal, not cosmetic — `new_goal` returns
"internal: more goals than the pre-count reserved" (`lib.rs:859`).

### 2.3 The record-literal flag, and every keyword-headed atom

`no_record_lit` (`parser.rs:85`, `with_record_lit` `:211-216`) is set in
exactly three block-preceding positions — the declaration's result type
(`:615`), the `match` scrutinee (`:1433`), the `match` motive (`:1444`) — and
lifted inside every bracket (`:1139`, `:1241`, `:1289`, `:1315`, `:1386`,
`:1406`). `docs/surface-records.md` §6.1 is the rationale, and that section
also records that the braced literal is *provisional*, plausibly redundant
with `named-arguments`, and that retiring it "would delete §6.1 outright,
along with the standing hazard that every future block-preceding construct has
to remember the flag."

`atom` (`parser.rs:1194-1327`), in order: `univ()` → `Type`/`Type<n>`
(`:1198`); `match` (`:1201`); `calc` (`:1204`); `refl` (`:1207`); `j`
(`:1211`); `λ`/`fun` (`:1214`); `code {` (`:1220`, **guarded** by
`matches!(self.nth(1), TokKind::LBrace)`); `$` (`:1237`); `@` (`:1254`);
`[` (`:1287`); then holes, numerals, `(`, and a bare `Ident` (`:1302-1326`).
Only `code` consults a lookahead, and `parser.rs:2014-2025`'s test
(`code_is_still_an_ordinary_name`) is the pinned statement that the lookahead
is what buys the name back. `let code x` (`:678`) uses the same trick with a
different follow token.

Elaborator-side name-keyed forms are a different and healthier story: `absurd`
(`lib.rs:1286`, `:1781`), `inj` (`:1770`), `cong` (`:1746`), `Succ`, `Fin`,
`map`/`head`/`cons` all consult `shadowed` (`lib.rs:2599-2608`: local names,
`let` aliases, globals, and the declaration's own name) or `ctor_here`
(`:2612`). They have no trap.

### 2.4 What actually parses today (capped experiments, 2026-08-02)

Run as `(ulimit -v 4194304 -t 30; target/release/heather check <file>)` per
`CLAUDE.md`. Each row is a one-declaration file.

| Input | Result |
|---|---|
| `let n: Nat = 3;` | parse error: expected `=`, found Semi |
| `let q: P = p;` (declared `record P`) | parse error: expected `=`, found Semi |
| `let g: Nat -> Nat = fun x => x;` | parse error: expected `=`, found Semi |
| `let x: (Nat) = 3;` | parse error: expected `=`, found Semi |
| `let q: (a = b) = p;` | parse error: expected `=`, found Semi |
| `let q: a = b = p;` | **ok** |
| `let t: Type<0> = Nat;` | **ok** |
| `let r: [Nat; 3] = [1,2,3];` | **ok** |
| `let q: Opt<Nat> = o;` | **ok** |
| `let x: Type<0> = a = b;` | **ok** (the `surface-universe` counterexample to option 1) |
| `{ 3 }` as a `fn` body's result | parse error: expected an expression |
| `T => { 1 }` as a match arm | parse error: expected an expression |
| `a = (b = c)` in a parameter type | parse error: expected `)`, found Eq |
| `lookup(j, n)` | parse error: expected `(`, found Comma |
| `let refl = n; refl` | error: `refl` needs an `=` expected type |
| `let Type = n; Type` | error: the kernel rejected `f`: LevelMismatch |
| `let fun = n; fun` | parse error: a lambda needs at least one binder |
| `add(match, calc)` | parse error: expected an expression |
| `let j = n; n` (bound, never used) | **ok** — the trap is at the *use* |
| `let code2 = n; code2` | **ok** — `code` itself is fine, by its lookahead |

### 2.5 The existing spellings at stake

Executable sites of the equality-annotated `let`, exhaustively (this is the
whole blast radius of §3):

- `crates/syntax/src/parser.rs:1907` — `let p: n = n = refl;`, in
  `let_binds_with_and_without_an_annotation` (`:1903-1921`).
- `crates/elab/tests/goal_holes.rs:146` — `let strong: add(n, 0) = n = ?g;`,
  the hole-programming pattern of `docs/sketches/surface-v3.md` §2.
- `lib/certgen/ir_v1.hthr:972`, `:975`, `:994`, `:997` — four `let e1`/`let e2`
  `fuel_monotone` steps inside `letcall_conv` and `letmatch_conv`.

**Six sites.** The `<=`-annotated shape `let h: n <= m = pf;` has **zero**
executable sites; it exists only as prose at
`docs/comparison-operators.md:100`.

## 3. Decision 1: the annotation position suppresses the comparison rung

**The `let` binder stays `=`. The annotation is read with `no_eq` set, and
`no_eq` is cleared by every bracket — so a parenthesis is a real escape hatch,
and an equality annotation is written `let p: (a = b) = pf;`.**

Three changes, all in `crates/syntax/src/parser.rs`:

```rust
// let_stmt, parser.rs:687-692
let ty = if matches!(self.peek(), TokKind::Colon) {
    self.bump();
    Some(self.with_eq(true, |p| p.ty())?)     // <- the annotation only
} else {
    None
};
self.expect_eq("`let` binding")?;              // unchanged
```

```rust
// atom's `(` arm, parser.rs:1311-1318, and ty_atom's, :839-844
let e = self.with_eq(false, |p| p.with_record_lit(false, |p| p.expr()))?;
```

and, because the annotation is now the *only* place a binder `=` can follow a
completed comparison, `comparison`'s trailing-operator check
(`parser.rs:1007-1013`) gains `TokKind::Eq` beside `LtEq` and `EqEq`, and its
doc comment's "A trailing `=` deliberately does **not**" paragraph
(`:981-985`) is deleted.

### 3.1 Why this and not the other two

**Option 1 — scan for the last top-level `=` — stays dead.** The issue's log
invalidated it on 2026-07-27 and §2.4 re-confirms the counterexample:
`let x: Type<0> = a = b;` parses and means "bind `x`, at `Type<0>`, to the
proposition `a = b`". A last-`=` scan splits it as annotation `Type<0> = a`,
value `b`. `surface-universe` phase 3 made `=` an expression former; there is
no lookahead over a token stream that can put that back.

**Option 3 — `:=` as the `let` binder — loses on three counts, and the issue's
argument for it is stale.**

- *`:=` is already spoken for.* `issues/effects-direction.md`'s log of
  2026-07-24 records a **constraint**, not a leaning: "Any future
  imperative/assignment-like effect syntax must therefore NOT use bare `=` …
  Use `:=` (user's stylistic lean) or `<-` … pin the assignment glyph early."
  The `annotated-let` issue's claim that option 3 "composes with
  `effects-direction`'s eventual assignment `=`" was written before that log
  and reads it backwards: `=` is *not* available for assignment, which is
  exactly why `:=` is being held. Spending `:=` on `let` would make it mean
  goal discharge (`parser.rs:729`), a `calc` step proof (`:1533`), a local
  binding, and later an assignment — four things, against the two `=` carries.
- *It contradicts a settled decision.* `issues/surface-syntax.md` (2026-07-24)
  settled that Heather merges binding and equality onto one `=`, ML-style,
  disambiguated by `let`. `expect_eq`'s doc comment (`parser.rs:741-745`)
  cites it. Undoing that inside a parse-bug fix is out of proportion.
- *Blast radius: ~40 executable sites against 6.* Every `let` in the corpus
  changes spelling, annotated or not — `lib/certgen/ir_v1.hthr`, the `let` tests in
  `goal_holes.rs`, `records.rs`, `quotation.rs`, `function_types.rs`,
  `el_reader_audit.rs`, nine sites in `parser.rs`'s own suite, and every `let`
  in a dozen docs and sketches. Option 2 touches six (§2.5).

What option 3 genuinely had going for it, and which **option 2 delivers too**,
is the good `a <= b = c` chain diagnostic that `docs/comparison-operators.md`
:105-110 says "will disappear when that issue picks `:=`". It disappears here
instead: once the annotation suppresses the rung, a `=` after a completed
comparison is *always* a chain, so `comparison` can say so. §9 requires that
test and the doc correction.

### 3.2 What breaks, exactly

- **`let p: a = b = pf;` no longer parses as an annotated `let` at an equality
  type.** It parses as annotation `a`, binder `=`, value `b = pf` — and the
  elaborator rejects it, because `a` is a term and not a type. That is a
  *diagnosable* failure but not a good message, so §9 requires a targeted one
  (see below). Six sites, re-spelled `let p: (a = b) = pf;`.
- **`let h: n <= m = pf;` likewise**, re-spelled `let h: (n <= m) = pf;`.
  Zero executable sites; one prose site.
- Nothing else. Every annotation in the "ok" half of §2.4's table is either an
  early return from `ty_atom` (unaffected by `no_eq`) or gains parsing it
  never had.

**The diagnostic that makes the break survivable.** In `let_stmt`, after the
annotation is parsed with `no_eq` set, if the next token is `=` and the
annotation's parse *stopped where a comparison would have continued*, the
error the user gets is currently the elaborator's "not a type". Rather than
teach the parser to detect that, take the cheaper and more honest route: the
elaborator's "this is not a type" path for a `TyKind::Named`/`OfExpr` that
resolves to a **term** in a `let` annotation gains a hint —

> `a` is a term, not a type. If this annotation was meant to be an equation,
> parenthesise it: `let p: (a = b) = pf;` — an annotation does not extend
> across the `let`'s `=`.

That is one hint at one site, and it is the message every one of the six
migrated spellings would have hit.

### 3.3 What it buys, beyond the reported bug

- `let x: T = e;` for **every** `T` — including the bare declared type
  (`let q: P = p;`), the function type, `Fin(k)`, and any parenthesised type.
- `docs/surface-fin-indexing-design.md` §3.2's claim that an annotated `let`
  is an available checking position becomes true; `crates/elab/tests/surface_fin.rs:173-192`'s
  recorded caveat can be deleted and replaced with the test it wanted
  (`let i: Fin(Succ(n)) = FZ;`). This is the axis-3 checking position that
  suite says it is missing.
- `issues/goal-holes.md`'s own recommended spelling `let p: T = ?;` becomes
  writable at a non-equality `T`.
- `a = (b = c)` parses (finding 1.1(3)), so the `CHAIN` diagnostic stops
  lying, and `calc`'s endpoints gain the same escape hatch their flag's doc
  comment already claims.

## 4. Decision 2: a block expression, prefix-only, without `on`

**`{ stmt* expr }` is an expression, recognized in `atom` at a *prefix* `{`,
reusing the existing `Block` node and `block()`. A block expression may not
carry `on` discharges. `let`s still all precede the result.**

```rust
// ast.rs, a new ExprKind
/// `{ let x = e; … result }` — a block in expression position.
Block(Box<crate::ast::Block>),
```

```rust
// parser.rs, in `atom`, immediately before the final `match self.peek()`
if matches!(self.peek(), TokKind::LBrace) {
    let b = self.block()?;                       // shares block_body verbatim
    if let Some(on) = b.ons.first() {
        return Err(ParseError {
            msg: "a block in expression position cannot discharge goals: an \
                  `on` belongs to the declaration's own block \
                  (issues/nested-goal-discharge.md)".into(),
            span: on.span,
        });
    }
    return Ok(Expr { span: b.span, kind: ExprKind::Block(Box::new(b)) });
}
```

Note what does **not** change: `match_expr`'s arm body stays
`let body = self.expr()?` (`parser.rs:1469`). The arm gets blocks because
*every* expression position does — `let` values, call arguments, vector
elements, `on` right-hand sides, `code { … }` payloads, a lambda body. That is
the whole argument for the general form over an arm-local one.

### 4.1 The disambiguation rule, and why `group_is_type` is the wrong precedent

**`{` is disambiguated by position, never by lookahead.** Prefix `{` is a
block; postfix `{` on a `Var`/`TyApp` head is a record literal
(`parser.rs:1090-1102`); `{` where a *statement* is expected is a declaration
body or an arm list, reached by `block()`/`match_expr` directly and never
through `atom`.

`issues/match-arm-blocks.md` frames this as a head-on collision needing a
lookahead disambiguator on the model of `group_is_type` (`parser.rs:187-206`).
It is not, and the model does not apply. `group_is_type` exists because in
*type* position a leading `(` genuinely opens either reading — `(A -> B) -> C`
and `(a + b) + c = d` start identically — so the parser must scan for `->`
before committing. Nothing analogous holds for `{`: the record literal cannot
occur at a prefix position at all, because it is constructed only after an
expression has been parsed and only when that expression is a name. The right
precedent is `docs/surface-fin-indexing-design.md` §5.1's postfix `[`, which
made the same argument for the same reason and needed no lookahead and no
backtracking. §2.4 confirms the premise empirically: prefix `{` is
"expected an expression" in both the result position and the arm position.

Three collision checks, each done rather than asserted:

- **`match m { … }`.** The scrutinee is parsed with `no_record_lit` set
  (`:1433`); `m` is an `Ident` atom, the postfix loop (`:1103-1149`) does not
  consume `{`, and `match_expr` then expects it as the arm list (`:1448`).
  Unchanged. A block *as* a scrutinee (`match { let k = f(x); k } { … }`) now
  parses, and is unambiguous because the block consumes its own braces.
- **`D { x: 1 }` in an arm.** Still the postfix literal: `D` is parsed first,
  so the `{` is not prefix. The block form cannot reach it.
- **`fn f() -> T { … }`.** `decl()` calls `block()` directly (`:616`), not
  `expr()`. The result type is parsed with `no_record_lit` set, so the body
  brace is never a literal, and it is never a prefix position either.

One cosmetic consequence worth naming: this makes the block form **independent
of `no_record_lit`**, so if `docs/surface-records.md` §6.1's provisional braced
literal is ever retired in favour of `named-arguments`, nothing here has to be
revisited.

### 4.2 Reuse `Block`, do not mint a second node

**Decision: `ExprKind::Block(Box<Block>)` over the existing `ast.rs:155-166`
node.** The losing option is a new `ExprKind::Block { stmts, result }` without
the `ons` field.

- **The parser shares `block_body` verbatim**, so a declaration body and a
  block expression cannot drift in what statements they admit. This is the
  same argument `univ()` (`parser.rs:808`, "shared by `ty_atom` and `atom` so
  the two spellings cannot drift") and `expr_as_ty` (`:119-127`, "the one place
  the grammar decides…") already make.
- **The elaborator shares the alias loop**, which is the real win: §4.4.
- **A field that is parsed and then rejected is house style**, not a smell.
  `InductiveDecl::valparams` is exactly this (`parser.rs:388-390`: "Parsed,
  then rejected by the elaborator … a named rejection beats
  `expected `{`, found LParen`"), and the reason is the same — the rejection
  message can name the actual concept.
- **When `nested-goal-discharge` lands, the field is already there** and only
  the elaborator changes. A second node would have to grow one.

### 4.3 No `on` on a block expression, and why that is a decision rather than a deferral

An arm-level `on` would mean a **nested goal scope**, and every part of the
goal machinery is currently declaration-scoped:

- `goal_base = count_holes(decl)` is reserved once, before anything is
  elaborated (`lib.rs:593-597`), for the whole declaration.
- `frozen` is a single `Cell<bool>` on the elaborator (`lib.rs:409`), set once
  by `solve_goals` (`:924`) and cleared once per declaration (`:584`).
- `strengthen_global(&t, self.goal_base)` (`:952`, `:993`) strengthens a
  solution out of the *declaration's* goal world.

A nested `on` would have to discharge a subset of goals *while later goals are
still being created*, which is precisely the dependency-order discharge
`nested-goal-discharge` describes and this round does not build. So the
refusal is not "we ran out of time"; it is the same invariant, stated at a new
syntactic site, with a diagnostic that points at the issue.

**And nothing is lost by it.** A hole inside an arm-level block is an ordinary
goal in the declaration's goal list, with the arm's binders and the block's
aliases captured in its `Cx` — the same capture the `match`-arm case already
exercises (`issues/split-on-arms.md` says so about the existing arm path).
It is discharged by the declaration's own trailing `on`. That works the day
this lands, and it is worth a test (§8).

### 4.4 Elaboration: one refactor, two new arms

The `let` loop at `lib.rs:677-745` is lifted out of `elab_decl_inner` into

```rust
/// Push a block's statements onto a *clone* of `cx` as aliases, returning the
/// extended context. Shared by a declaration body and `ExprKind::Block`, so
/// the two cannot disagree about what a `let` means.
fn elab_stmts(&self, cx: &Cx, stmts: &[Stmt]) -> R<Cx>
```

`elab_decl_inner` calls it and continues unchanged. Two new elaborator arms
call it too:

- `elab_check_hinted` (`lib.rs:1246`): `ExprKind::Block(b)` ⇒
  `let cx2 = self.elab_stmts(cx, &b.stmts)?; self.elab_check(&cx2, &b.result, expected, lvl)`.
- `elab_infer` (`lib.rs:1515`): the same, ending in `elab_infer`.

**The block is checking- and inference-transparent**, which is the property
that makes it useful: a block in an arm under a dependent motive is checked at
the arm's type, not inferred and then converted. This matters and §8 tests it.

Three things fall out of `let` being an *alias* rather than a binder
(`lib.rs:719`, `:738`):

1. **No kernel binder is introduced**, so a block in an arm does not perturb
   the `Case`/`ElimNat` telescopes the arm builds, and no motive changes.
2. **Scoping is automatic** — the aliases live on a cloned `Cx` that dies with
   the block.
3. **`let code` stays meta-layer**, rejected by the same arm that rejects it
   today (`lib.rs:683-690`), now reachable from a block expression too. The
   `meta fn` body path (`elab_meta_decl`) is a separate walk; whether a block
   expression is admitted *inside* a `code { … }` payload is settled by §7.2.

**The exhaustive walks the new node must join**, found by grepping every
`match &e.kind` with no catch-all (this is the checklist, not a guess):

- `lib.rs:4117` `count_holes` — both `stmts` and `result`. **Load-bearing**: an
  under-count is `internal: more goals than the pre-count reserved`
  (`lib.rs:859`), not a wrong answer. §9 requires the test.
- `quote.rs:778` `scan_splices` — a `$x` inside a block inside a quote must
  hoist. Same "load-bearing, a missed arm is a silent non-hoist" note
  `docs/surface-fin-indexing-design.md` §6 item 10 made.
- `inductive.rs:1973` `expr_mentions` — conservative like `Match`/`J`
  (`:2004-2005`) is the safe answer.
- `certgen.rs:318`/`:154` have catch-alls (`_ =>`), so a block inside a
  certifying-generator fragment is an ordinary "not a fragment" rejection.
  Correct, and no work.

### 4.5 Interleaving is deliberately deferred, and the reason is not effort

`block_body`'s `while self.at_kw("let")` (`parser.rs:635`) forces every `let`
before the result. Interleaving would mean **expression statements**, and in a
language with no effects an expression statement is a no-op — there is nothing
for `f(x);` to do. The form becomes meaningful exactly when
`issues/effects-direction.md` lands and decides what a statement *is*; adding
it now would be adding a syntax whose semantics is "discard a pure value",
which is a lint, not a feature.

What is *not* deferred and already works: a chain of `let`s where each may use
the previous (`let a = …; let b = f(a); g(b)`), which is the only interleaving
anyone has wanted, and the shape `issues/match-arm-blocks.md` was actually
blocked on.

## 5. Decision 3: three rules over all six keyword-headed atoms

### 5.1 The audit

Every expression-position form keyed on an identifier, with what follows it
and whether the trap is loud:

| Form | `atom` | Always followed by | Failure of a binder by that name |
|---|---|---|---|
| `code` | `:1220` | `{` (and `:678`, an ident after `let`) | **none — already guarded** |
| `j` | `:1211` | `(` — the form is saturated | loud: `expected (, found Comma` |
| `calc` | `:1204` | `{` | loud: `expected {` |
| `match` | `:1201` | *an expression* | loud, but see below |
| `fun` | `:1214` | a binder — an ident, or `(` | loud: `a lambda needs at least one binder` |
| `refl` | `:1207` | **nothing** (nullary) | **silent**: the use becomes `ExprKind::Refl` |
| `Type` | `:1198` | nothing, or `<n>` | **silent**: the use becomes `Univ { level: 0 }` |

Type position adds `Ctx` (`:850`, already guarded by `!matches!(nth(1), Lt|LParen)`),
`TyCode`/`Code` (`:854`, `:861`, both guarded by `(`), and the name-keyed
`Nat`/`Fin` in `expr_as_ty` (`:141`, `:150`) — the latter two documented and
deliberate reservations (`docs/surface-fin-indexing-design.md` §2.2).
Statement heads `let`/`on` are safe by the argument in `parser.rs:51-53` and
tested at `:1936-1943`.

So the trap set is **six**, and `j` — the one that was filed — is a *loud*
member of it. The two silent ones are the dangerous ones.

### 5.2 The three rules

**Rule 1 (lookahead — the `code` precedent). A keyword-headed form that is
always introduced by a fixed token is recognized only when that token
follows.** Applies to `j` (`(`) and `calc` (`{`):

```rust
if self.at_kw("j") && matches!(self.nth(1), TokKind::LParen) { … }
if self.at_kw("calc") && matches!(self.nth(1), TokKind::LBrace) { … }
```

Both are exact: `j_expr` (`:1484-1512`) unconditionally expects `(`, and
`calc_expr` (`:1519`) unconditionally expects `{`. Nothing that parses today
parses differently, because today the same token is *required* one line later.
This is precisely the `code {` rule (`:1220`) and its pinned test
(`:2014-2025`).

**Rule 2 (shadowing — the `Succ`/`map`/`absurd` precedent). A nullary special
form, whose node carries no name to re-derive, consults `shadowed` in the
elaborator.** Applies to `refl`: the `ExprKind::Refl` arm checks
`self.shadowed(cx, "refl")` (`lib.rs:2599-2608`, which sees local binders,
`let` aliases, globals and the self-reference) and, when shadowed, elaborates
as `Var("refl")` instead. Three lines, and exactly the guard `Fin`
(`lib.rs:1604-1610` per `docs/surface-fin-indexing-design.md` §2.3), `absurd`
(`:1781`) and `inj` (`:1770`) already use.

**Rule 3 (binder rejection — the `self`-as-type-parameter precedent). A form
that is neither saturated by a fixed token nor nullary is a true keyword, and
a binder by its name is rejected at the binding site with a message naming the
collision.** Applies to `match`, `fun`, `if`, `Type`:

> `fun` is the lambda keyword, so it cannot be a binding name here; a use of
> it would parse as `fun x => …`. Pick another name.

Binding sites to cover: `let` (`parser.rs:686`), `let code` (`:679`), the
destructuring pattern's field names (`:663`), lambda binders (`:1339`,
`:1344`), `match`-arm pattern binders (`:1460`), declaration parameters
(`:548`), type parameters (`:490` — which already rejects `self` this way,
`:491-501`), value parameters (`:349`), and record/constructor field names
(`:403`, `:456`). One shared helper, one message.

Why the split rather than one rule for all six: **each rule is keyed on a
property the form actually has**, so the set stays classified rather than
enumerated when another form arrives. `match` and `if` cannot take rule 1
because what follows either is an arbitrary expression — `match (x) { … }`
and a call `match(a, b)` to a function named `match` begin identically, and
one token of lookahead cannot separate them. `refl` cannot take rule 1 because it has no
follow token at all. `Type` cannot take rule 2 because `Type` and `Type<0>`
produce the same `Univ { level: 0 }` node, so there is no name left in the
tree to check.

### 5.3 The residue, stated rather than hidden

After rule 1, a binder named `j` is an ordinary name at every use *except* one:
`j(x)`, a local of function type applied to arguments, still parses as the J
form and fails in `j_expr`'s arity check. This is left standing because (a)
`j` is an index name, and an index is not applied; (b) the failure is loud and
inside a form the user can see named in the error; (c) it dissolves entirely
under `special-forms-as-declarations`. `j_expr`'s existing error messages
should gain a clause naming the collision, which is the cheap half of the
issue's second proposal.

### 5.4 Stopgap or permanent?

`issues/special-forms-as-declarations.md` would make `j`, `refl`, `cong`,
`absurd` and `inj` ordinary declarations, which shadow like anything else and
dissolve this whole question for those five. So, per rule:

- **Rule 1 is not reverted, it is deleted with what it guards.** When `j`
  stops being a parser form, the guard goes with `j_expr`. Zero migration
  cost, and in the meantime it is a strict improvement.
- **Rule 2 is a down payment on that issue, not a stopgap.** "A declaration
  shadows like anything else" is exactly what rule 2 implements for `refl`,
  one form early. When `refl` becomes a declaration the special arm is deleted
  and the behaviour is unchanged for every program.
- **Rule 3 is permanent.** `match`, `fun`, `if` and `Type` are not on
  `special-forms-as-declarations`' list and never will be: they are keywords
  of the grammar, not elaborator conveniences. Rejecting them as binder names
  is a rule the language keeps.

There is therefore **nothing here that a later round must undo**, which was
the question worth asking before spending effort on a trap that a bigger issue
already promises to remove.

### 5.5 The `jx` rename

`crates/elab/tests/surface_fin.rs` renamed `FS(j)` to `FS(jx)` to work around
this (the issue's 2026-08-02 log). After rule 1 the rename can be reverted —
and reverting it *is the test* that rule 1 works, at the exact site that
motivated it. §9 requires it.

## 6. Issues this round does not fix, and what it commits or preserves

- **`nested-goal-discharge`** — answered, not folded in (§1.2). This round
  *preserves* it exactly: §4.3 refuses `on` on a block expression, so the
  declaration-scoped `frozen`/`goal_base`/`strengthen_global` invariants are
  untouched. When it lands, it lifts one parser rejection and adds an
  elaborator pass; `ast::Block::ons` is already the field it needs.
- **`split-on-arms`** — untouched and, importantly, not foreclosed. That issue
  needs "a distinguished `split`-terminated block shape or a rule that a block
  whose last statement is a `split` takes no result expression." §4 does not
  make `Block`'s single `result` any more load-bearing than it already is, and
  §4.5 explicitly leaves statement-position forms open. One caution to record:
  if `split` becomes a statement, a block *expression* containing one raises
  the nested-goal-scope question again — and the answer will be the same as
  §4.3's until `nested-goal-discharge` lands.
- **`effects-direction`** — §3 *protects* it. Keeping `=` as the `let` binder
  leaves `:=` free for the assignment glyph its 2026-07-24 log asked to pin
  early. §4.5 defers interleaved statements to it, on the grounds that an
  expression statement has no meaning without effects. Both are commitments in
  its favour, and the `annotated-let` issue's claim to the contrary should be
  logged as superseded.
- **`special-forms-as-declarations`** — §5.4. Rule 2 anticipates it; rule 1
  is deleted by it; rule 3 is orthogonal. Nothing here makes it harder, and
  the audit table in §5.1 is the inventory that issue will want.
- **`case-algebra-definitions`** — unaffected by §3 and §5. §4 helps its
  rung 1 slightly (a `fold` clause can now use a local binding) and changes
  nothing about its substrate, which is `nested-match-patterns`.
- **`comparison-operators`** (closed) — §3 closes its recorded loose end and
  falsifies its prediction that the fix would be `:=`. `docs/comparison-operators.md`
  :95-110 needs the correction §9 lists.
- **`surface-records`** §6.1 — §4.1 confirms the braced literal's flag is not
  an obstacle to blocks, which slightly *weakens* one argument for retiring it
  (the "standing hazard that every future block-preceding construct has to
  remember the flag" turns out not to bind here). Recorded so that section is
  not read as more pressing than it is.

## 7. Bigger than filed, and what could be split

### 7.1 Question 1 is bigger; question 2 is smaller

Stated plainly, because both are useful corrections:

- **Bigger.** `annotated-let-swallows-the-equals` reads as "one type former
  is greedy". It is "the annotation position inherits the whole expression
  grammar's loosest rung", and the affected set includes bare declared type
  names and function types (§1.1(1), §2.4). Three documents describe the cause
  incorrectly and need the correction in §9. The fix is still small; the
  *claim* was wrong.
- **Smaller.** `match-arm-blocks` reads as a head-on grammar collision needing
  a lookahead disambiguator. It is a pure prefix extension needing none
  (§1.1(4)). The real work is the four exhaustive walks in §4.4 and the
  `elab_stmts` refactor, neither of which the issue mentions.

### 7.2 One thing that should be split out

**A block expression inside a `code { … }` quote payload.** `atom`'s quote arm
(`parser.rs:1220-1235`) parses one expression and its comment says "quotes
have no statements". With §4, a block *would* become parseable there, and its
`let`s would elaborate as aliases at `Layer::Code` — plausibly fine, plausibly
interacting with `scan_splices`' letbox hoisting (`quote.rs:778`) and with
`box-synthesis-gap`'s meta-ANF invariant in ways this round has not
established.

**Recommendation: the implementing round rejects a block expression as a
quote payload's top level, with a named message**, and the question of `let`
inside quotation is filed as its own issue against
`issues/in-language-map.md`'s thread. It would be genuinely useful there —
`lib/lang/vec_code.hthr`'s templates are the client — but "useful" is not
"analysed", and a wrong answer here is a silently mis-hoisted splice, which
is the failure mode `docs/surface-fin-indexing-design.md` §6 already flagged as
the expensive one.

### 7.3 Predictions worth recording so they can be refuted

In the style of `docs/in-language-map-design.md` §7, two:

1. §3's migration of the six equality-annotated `let`s will be mechanical, and
   `lib/certgen/ir_v1.hthr` will re-check with no other change. If it does not, the
   likely cause is `no_eq` leaking through `ty()`'s arrow codomain
   (`parser.rs:792`) into a place the annotation did not intend, and the
   acceptance list's item 4 is the control.
2. §4's block form will need **no** change to `elab_match`
   (`lib.rs:1932`). If it does, the cause is that arm bodies are re-elaborated
   somewhere (motive synthesis, `lib.rs:2132`) in a way that duplicates alias
   pushes — and a hole inside an arm block would then be the visible symptom,
   which item 12 tests.

## 8. Test plan

`docs/testing-generated-terms.md`'s axes apply to §4 (an elaboration change
that emits terms) and only weakly to §3 and §5 (grammar). Applied per
decision. New file `crates/elab/tests/let_and_blocks.rs`; parser-shape
assertions go in `parser.rs`'s own suite beside the tests they replace.
Everything under `scripts/test`.

**§3, the annotation**

1. `let x: T = e;` at each of the previously-failing `T`s: `Nat`, a declared
   `record P`, an applied `Opt<Nat>`, `Nat -> Nat`, `(Nat)`, `Fin(Succ(n))`.
2. The three annotations that already worked are byte-identical:
   `Type<0>`, `[Nat; 3]`, `D<A>`.
3. `let p: (a = b) = pf;` and `let h: (n <= m) = pf;` parse and elaborate.
4. **Negative controls.** (a) `let p: a = b = pf;` is rejected, with the §3.2
   hint naming the parenthesised spelling. (b) `let x: Type<0> = a = b;` still
   parses and still binds the *proposition* — the `surface-universe`
   counterexample, and the control that `no_eq` is scoped to the annotation
   and not to the value. (c) `a = (b = c)` parses (finding 1.1(3)).
   (d) `a <= b = c` and `a = b = c` now get the `CHAIN` message.

**§4, the block** (axis 1 = literal *and* neutral scrutinee; axis 3 = a
checking position where nothing reduces; axis 4 = a negative control)

5. The motivating shape: `Succ(k) => { let y = f(x); g(y) }`, at a **literal**
   scrutinee, and the result *computes* (`conv` against the expected reduct,
   not merely `check`).
6. The same at a **neutral** scrutinee, inside an enclosing `match` arm — the
   axis-1 case, where the alias must survive without reducing.
7. **Axis 3**: a block in an arm under an explicit dependent motive, in a
   *checking* position (a `theorem`), where the block's value must convert
   with the goal rather than be reduced away. An **annotated** `let` inside it,
   so §3 and §4 are exercised together.
8. **Axis 2's analogue** — an *open* element type: a block whose `let` binds
   at `[A; n]` for a declaration type parameter `A`, so nothing about the
   binding is closed.
9. A block in three other positions, to pin that the form is general and not
   arm-local: a call argument, a `let` value, and a lambda body.
10. Equivalence control: the same program with and without the block (the
    `let` hoisted to the declaration body) elaborates to **convertible** terms
    at `Layer::Prog`, plus the vacuity guard `assert!(a != b)` where the two
    terms are expected to differ syntactically — the pattern
    `in_language_fold.rs:103-141` established.
11. **Negative controls.** (a) `on` inside a block expression is rejected with
    the §4.3 message naming `nested-goal-discharge`. (b) A `let` *after* the
    result expression is a parse error. (c) `let code x = …;` inside a block
    expression in a non-meta declaration gets the existing meta-layer message.
    (d) A block expression as a `code { … }` payload is rejected (§7.2).
    (e) An empty block `{ }` is a parse error.
12. **`count_holes`**: a hole inside an arm-level block, discharged by the
    declaration's trailing `on`. Without the `count_holes` arm this is
    `internal: more goals than the pre-count reserved`, so this test is the
    one that catches a missed walk. A second hole in a *nested* block, to
    catch a shallow walk.
13. **`scan_splices`**: `$x` inside a block inside a `code { … }` payload —
    which, given item 11(d), means the *rejection* is what is pinned, and the
    walk arm is written to `err` rather than silently succeed.

**§5, the traps**

14. Rule 1: `fn f(n: Nat) -> Nat { let j = n; lookup(j, n) }` parses; `j(p, m, c)`
    still parses as the J form; `calc` as an ordinary name parses, and
    `calc { … }` still works. The pattern of `code_is_still_an_ordinary_name`
    (`parser.rs:2014-2025`), one test per form.
15. Rule 2: `let refl = n; refl` elaborates as the binding; `refl` in a
    checking position at an equality type still elaborates as the form; a
    `theorem` that *shadows* `refl` and still needs it is a documented
    impossibility, not a test.
16. Rule 3: each of `match`, `fun`, `if`, `Type` as a `let` name, a lambda binder, a
    match-arm binder and a declaration parameter is rejected with a message
    containing the form's name. One negative control per binding site is
    excessive; one per *form* across three sites is enough.
17. **The revert**: `crates/elab/tests/surface_fin.rs`'s `jx` binders go back
    to `j` (§5.5), and the suite is green. This is the acceptance test of rule
    1 at the site that motivated it.

**Regressions**

18. `lib/certgen/ir_v1.hthr` re-checks after the six migrations; `goal_holes.rs`,
    `surface_fin.rs`, `in_language_{map,fold,nth,tabulate}.rs`, `records.rs`,
    `quotation.rs`, `function_types.rs` green.
19. `parser.rs`'s own suite: `let_binds_with_and_without_an_annotation`
    (`:1903`) is rewritten around the parenthesised spelling and gains the
    non-equality cases it could never have.

## 9. Acceptance list

Ordered so each phase is landable and testable alone. Phases A, B and C are
independent; within a phase, the order matters.

**Phase A — the `let` annotation (§3)**

1. `atom`'s `(` arm (`parser.rs:1311-1318`) and `ty_atom`'s
   (`:839-844`) clear `no_eq` via `with_eq(false, …)`, making the parenthesis
   escape hatch real. Checkable alone: `a = (b = c)` parses (§2.4's `w1`
   inverts), and `calc { (a = b) = c := p }` parses.
2. `let_stmt`'s annotation (`parser.rs:687-692`) is read inside
   `with_eq(true, …)`. Checkable: every row of test 1 in §8.
3. `comparison` (`parser.rs:1007-1013`) adds `TokKind::Eq` to the trailing-
   operator check, and its doc comment's trailing-`=` exemption
   (`:981-985`) is deleted. Checkable: `a = b = c` and `a <= b = c` get the
   `CHAIN` message; `theorem t(): a = b { refl }` and
   `let x: Type<0> = a = b;` still parse.
4. The six sites of §2.5 are migrated to `(a = b)`, and `lib/certgen/ir_v1.hthr`
   re-checks unchanged otherwise. Checkable independently of 5.
5. The elaborator's "not a type" path gains §3.2's hint for a `let`
   annotation that resolved to a term. Checkable: test 4(a).
6. Documentation corrections, each a specific edit:
   `docs/surface-function-types.md:507-513` (§10.3's account of the cause is
   wrong per §1.1(1), and the bug is fixed);
   `docs/surface-value-parameters.md:133-137` and
   `crates/elab/tests/value_parameters.rs:143-148` (same);
   `crates/elab/tests/surface_fin.rs:173-192` (the caveat is retired and the
   annotated-`let` checking position is added — the axis-3 test that suite
   said it was missing);
   `docs/comparison-operators.md:95-110` (the exception is gone, and it was
   not `:=` that removed it);
   `docs/surface-fin-indexing-design.md` §3.2 (its claim is now true).

**Phase B — the block expression (§4)**

7. `ExprKind::Block(Box<Block>)` in `ast.rs`, with a doc comment stating the
   prefix/postfix disambiguation (§4.1) and the no-`on` rule (§4.3).
8. `atom` gains the prefix-`{` arm before its final `match`, delegating to
   `block()` and rejecting a non-empty `ons` with the message naming
   `nested-goal-discharge`. Checkable: §8 items 5 and 11(a).
9. `elab_stmts` is extracted from `elab_decl_inner` (`lib.rs:677-745`) and
   `elab_decl_inner` calls it, with **no behaviour change** — checkable on its
   own by every existing suite staying green before any new arm is added.
10. `elab_check_hinted` (`lib.rs:1246`) and `elab_infer` (`lib.rs:1515`) gain
    their `Block` arms (§4.4). Checkable: §8 items 5–9.
11. The four exhaustive walks learn the node: `count_holes` (`lib.rs:4117`),
    `scan_splices` (`quote.rs:778`, as an `err` per item 13),
    `expr_mentions` (`inductive.rs:1973`, conservative). Checkable: §8 items
    12 and 13; the `count_holes` test fails loudly without its arm.
12. A block expression is rejected as a `code { … }` payload's top level
    (§7.2), and an issue is filed for `let` inside quotation. Checkable:
    §8 item 11(d), and the issue exists.
13. `crates/elab/tests/let_and_blocks.rs` carries §8 items 5–13, including the
    axis-3 checking-position test and the item-10 equivalence control with its
    vacuity guard.

**Phase C — the binder traps (§5)**

14. Rule 1: `j` (`parser.rs:1211`) and `calc` (`:1204`) gain their one-token
    lookahead guards. Checkable: §8 item 14.
15. Rule 2: the `ExprKind::Refl` elaborator arm consults
    `shadowed(cx, "refl")` (`lib.rs:2599`). Checkable: §8 item 15.
16. Rule 3: a shared binder-name check rejects `match`, `fun`, `if` and `Type` at
    the ten binding sites listed in §5.2, with a message naming the form.
    Checkable: §8 item 16.
17. `j_expr`'s arity errors gain a clause naming the local-`j` collision
    (§5.3). Checkable by message text.
18. `crates/elab/tests/surface_fin.rs`'s `jx` binders are reverted to `j`
    (§5.5, §8 item 17) — the acceptance test of rule 1 at its motivating site.
19. `issues/j-binder-parse-trap.md` is closed with the §5.1 audit table
    recorded in its log, and `issues/special-forms-as-declarations.md` gains a
    log entry pointing at §5.4 (rule 1 is deleted by it, rule 2 is a down
    payment, rule 3 is orthogonal).

**Cross-phase**

20. `issues/effects-direction.md` gains a log entry recording that `:=` was
    *not* spent on the `let` binder and remains available for assignment
    (§3.1), and that `annotated-let-swallows-the-equals`' claim to the
    contrary is superseded.
21. `issues/match-arm-blocks.md` is closed with §1.2's answer recorded — the
    block form does **not** subsume `nested-goal-discharge`, and §4.3 says
    why — so the speculation stops propagating.

---

## 10. Addendum: the implementing round, 2026-08-02

Written after the fact, so §7.3's predictions can be scored and the one thing
the round learned that no section above says is recorded where it will be
found.

### 10.1 The predictions

**Prediction 1 — the migration is mechanical, and `lib/certgen/ir_v1.hthr` re-checks
with no other change. CONFIRMED.** Four annotations parenthesised
(`:972`, `:975`, `:994`, `:997`), `git diff --stat` reports exactly
`4 insertions(+), 4 deletions(-)`, and a capped release check
(`ulimit -v 8388608 -t 300`) is `ok` in **70 s**. The named failure mode —
`no_eq` leaking through `ty()`'s arrow codomain (`parser.rs:792`) — did not
occur, and `let g: Nat -> Nat = fun x => x;` is a live test of the codomain.

**Prediction 2 — the block form needs no change to `elab_match`
(`lib.rs:1932`). CONFIRMED.** `elab_match` is untouched. The named symptom
(arm bodies re-elaborated somewhere, duplicating alias pushes, visible as a
hole inside an arm block) is the acceptance test for §9 item 11, and it
passes: two holes, one in an arm-level block and one in a block *nested*
inside another block's `let` value, both discharged by the declaration's
trailing `on`.

**Item 11's own prediction — the `count_holes` test "fails loudly without its
arm". CONFIRMED, and stronger than stated.** A *missing* arm is not a runtime
failure at all: `count_holes`'s inner `expr` walk has no catch-all, so
omitting the arm is a **compile error**, and the same is true of
`scan_splices` and `expr_mentions` — the three walks §4.4 listed were exactly
the three the compiler named, which is the checklist validating itself.
Deliberately weakening the arm to a *shallow* one (visiting `b.result` but not
`b.stmts`) reproduces the predicted failure verbatim:
`internal: more goals than the pre-count reserved`. So the loud failure is
available at both strengths, and the test earns its place against the shallow
one.

### 10.2 What the round learned that is not above

**Rule 3's binding-site list was undercounted.** §5.2 lists ten binding sites;
there are **twelve**, because `tyvar_list` (`parser.rs:369`, an `inductive`'s
and `record`'s type parameters) is a second type-parameter site distinct from
a declaration's own (`:490`), and `inductive`'s constructor names (`:403`) are
a binding position in their own right. All twelve go through one
`Parser::binder_ident`, so the count is a fact about the survey and not about
the fix.

**One `count_holes` shape changed, and it had to.** The declaration's own
statement walk and a block's were two copies of the same `match` over `Stmt`.
They are now one `stmts` helper called from both, for the same reason
`elab_stmts` exists: a nested block cannot be walked differently from a
top-level one if there is only one walk.
