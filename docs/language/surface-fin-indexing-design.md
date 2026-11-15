# The surface indexing layer: `Fin(n)`, its indices, `match` on `Fin`, and `xs[i]`

Design sketch for `issues/surface-fin-indexing.md`, filed off
`docs/metaprogramming/meta-def-registration-design.md` §4.4 when the registration round
validated its seam against `tabulate_code` and found the blocker was not
registration but syntax. Round pattern as usual: this document first, the
implementing round against §7's acceptance list.

**Status: no kernel change is required, and none is proposed.** The constraint
was that a kernel change would be a blocking finding at the top of this doc;
there is none to report. Everything below is `crates/syntax` and `crates/elab`.
The kernel already has `Type::Fin`, `Term::Inl`/`Inr`/`Case`/`ElimEmpty`, and a
`nth` schema (`term.rs:1118`); what is missing is the ability to *write* any of
them.

## 1. What this round unblocks, and what it deliberately does not do

`vec.tabulate` and `vec.nth` are the last two entries of `slots.rs`'s slot
vocabulary (`slots.rs:150-169`) with no template. Their payloads need `Fin` and
its indices, so the candidate order of
`issues/quotation-stage-artifacts.md` reads "fold (landed), *this layer*, then
tabulate and nth". This round lands the layer and **not** the two templates
(§9): the templates are `.hthr` text plus a cross-check suite once the surface
can express them, and keeping them separate is what makes each round's
acceptance legible.

Beyond the two ports, the layer is owed elsewhere. `docs/language/container-proofs.md`
§7 defers route A's `All` predicate explicitly to "the surface indexing layer
(`Fin`, `xs[i]`)", on the grounds that evidence no surface proof can eliminate
is worse than no evidence. `docs/language/container-fields.md` §7 deferred `Fin n` and
`xs[i]` out of phase 1 for the same reason and pointed at a later round. This
is that round.

### 1.1 Three findings that shrink it

Recorded first because each removes something the issue asked for.

1. **`elim_Empty` at the surface already exists, and already does the job.**
   The issue wants "an `elim_Empty` in the zero arm, term.rs' spelling"
   (`term.rs:1148`). `elab_match` (`lib.rs:1862-1877`) already turns a `match`
   with **zero arms** on a scrutinee whose whnf is `Type::Empty` into
   `Term::ElimEmpty`, with `scrut_level` read off the type and independent of
   the motive's level. `Fin(0) ⇝ Empty^0` is a whnf step (`reduce.rs:320-322`),
   so the moment `Fin(0)` is writable as a type, `match i { }` at `i : Fin(0)`
   *is* `elim_Empty`. No new form, no new diagnostic — the existing
   "this type has no constructors, so `match` takes no arms" already guards it.
2. **`Fin(n)` needs no parser change.** `expr_as_ty` (`parser.rs:128-156`) is
   "the one place the grammar decides what an expression means in type
   position", and it already claims the *name* `Nat` there
   (`parser.rs:141`). `Fin(n)` reaches it as
   `App { head: Var("Fin"), args: [n] }` — because `ty_atom`'s `D<A>` rule
   backtracks out when a `(` follows (`parser.rs:889-895`) and the fall-through
   parses an expression. One arm in each of the two `expr_as_ty` functions
   (parser and elaborator) is the whole type-position story. The only new
   grammar in this round is the postfix `[` of §5.
3. **The slot specs already exist.** `slots.rs:148-169` declares
   `vec.tabulate` and `vec.nth` with their ingredient types, including
   `ITy::Fin`, precisely so "the round which adds them adds a template and not
   a third dispatch pattern" (`slots.rs:120-122`). This round therefore wires
   the two *use sites* to `try_code_template` and leaves the templates for the
   port round; the port becomes a `.hthr` change.

### 1.2 One permanent limitation, stated as a rule rather than a TODO

**`Fin` has no eliminator of its own.** It is a former whose whnf is `Empty` or
`Unit⁰ + Fin(k)` (`reduce.rs:317-329`); elimination is the sum's `Case` after
unfolding, or `ElimEmpty` at zero. So a `match` on `Fin(n)` at a **neutral**
`n` is not an unimplemented case — it is unwritable, because there is no
canonical form to case on. The kernel's own `nth` shows the shape that works:
recurse on the *length* with `elim_Nat`, and the index becomes matchable inside
each arm (`term.rs:1126-1214`). §4.3 makes that a diagnostic that says so.

This is worth stating because it looks like a gap and is not one: `nth`
computes at a literal length **whatever the tuple is, including a neutral one**
(`term.rs:1113-1115`), and that property — not case analysis on an open index —
is what makes the `Fin`-indexed induction hypothesis usable.

## 2. The type: `Fin(n)`

### 2.1 Decision: a `TyKind` of its own, reached through `expr_as_ty`

```
TyKind::Fin(Box<Expr>)          // `Fin(n)`; the length is an expression at `Nat`
```

Modelled on `TyKind::Vec { elem, len }` (`ast.rs:267`) and for the same stated
reason: `Fin` is a **primitive** indexed type, a kernel former rather than a
user declaration, so it gets a node rather than an encoding
(`ast.rs:263-266`'s note about `[T; n]` applies verbatim).

The alternative — let `Fin(n)` fall all the way through to
`TyKind::OfExpr(App { Var("Fin"), [n] })` and give the elaborator a name-keyed
`Fin` arm returning `TmFin` — was rejected. It would produce
`Type::El { level: 0, tm: TmFin n }` rather than `Type::Fin { len: n }`.
Conversion sees through that (`reduce.rs:278`), so it would be *sound*, but
`unify_ty`'s `Fin`/`Fin` case (`lib.rs:3955-3957`) would stop firing, every
diagnostic would print `El(Fin(n))`, and the `Inl`/`Inr` annotations would no
longer read back folded — which is the property `wf.rs`'s `fin_index` was
written to preserve (`wf.rs:867-871`: "the folded form is what a goal reads
back as"). One `TyKind` variant buys all of that back.

### 2.2 Grammar: no parser rule, two `expr_as_ty` arms

In **type** position, `ty_atom`'s early cases (`univ`, `[T; n]`, `Ctx`/`Code`,
`D<A>`) all decline `Fin(n)` — the last one by explicit backtrack on `(` — and
the fall-through hands `expr()`'s result to `expr_as_ty`. So:

```rust
// parser.rs, in `expr_as_ty`, beside the `Nat` arm:
ExprKind::App { head, args, explicit: false }
    if matches!(&head.kind, ExprKind::Var(s) if s == "Fin") && args.len() == 1
    => TyKind::Fin(Box::new(args[0].clone())),
```

and the same arm in the elaborator's partial `expr_as_ty` (`lib.rs:287-309`),
which is what `elab_at_universe` (`lib.rs:1372-1394`) reads an expression
through when the expected type is a universe.

Two consequences, both intended:

- **`Fin` is a reserved type-former name**, exactly as `Nat` is and by exactly
  the same mechanism (a name-keyed arm in `expr_as_ty`). A user
  `fn Fin(n: Nat) -> Type` becomes unreachable *in type position*. This is the
  right side of the trade: the issue's own argument is that a user-supplied
  `Fin` is not a substitute, since it would not be `Type::Fin` and the
  cross-check against the Rust oracle would rightly fail.
- **Arity is checked in the parser arm, not later.** `Fin` with zero or two
  arguments falls through to `OfExpr` and gets the existing "this is not a
  type" message, which is unhelpful. Add the arity check to the elaborator's
  `Fin` inference arm (§2.3) so both spellings produce
  "`Fin` takes exactly one argument, a length at `Nat`".

Collision audit. `Fin(n)` in *expression* position still parses as an ordinary
`App`; nothing that parsed before parses differently, because no `Fin` exists
to have parsed. `Fin<A>` is not a spelling anyone can write (the type-argument
rule needs a declared inductive). `[Fin(n); k]` is an ordinary vector type.

### 2.3 Elaboration

- `elab_ty` gains one arm beside `TyKind::Vec` (`lib.rs:1139`):

  ```rust
  TyKind::Fin(len) => {
      let len_t = self.elab_check(cx, len, &Type::Nat, &Level::Zero)?;
      Ok((Type::Fin { len: Rc::new(len_t) }, Level::Zero))
  }
  ```

  The level is `Level::Zero` **unconditionally** — `Fin` is the one extension
  former that carries no level (`term.rs:153`, `typing.rs:569-573`), and it
  needed nothing from the level-indexing round (`reduce.rs:318-319`). There is
  no `Fin` at level 1 to write and no way to ask for one.

- `elab_infer`'s `App` arm gains a name-keyed `Fin` case beside `Succ`
  (`lib.rs:1604-1610`), returning the **code**:
  `(Term::TmFin { len }, Type::Ty(Level::Zero), Level::constant(1))`. This is
  what makes `fn Idx(n: Nat) -> Type { Fin(n) }` work, and it is what makes §8's
  coverage-table row honestly say "yes". Guarded by `!self.shadowed(cx, "Fin")`
  so a local binder or a global still wins in *expression* position — the
  asymmetry with type position is deliberate and follows `map`/`head`/`cons`
  (`lib.rs:1618-1641`).

- `code_of` needs no change: `Type::Fin → TmFin` is already there
  (`code.rs:70`). `unify_ty` needs no change (`lib.rs:3955-3957`).

## 3. The indices: `FZ` and `FS(i)`

### 3.1 Decision: `FZ` / `FS(i)`, both checking-only

Kernel-side there are no `Fin` constructors: an index is `Inl ⟨⟩⁰` or `Inr`
over the unfolded `Unit⁰ + Fin(k)`, with the `rhs` annotation written *folded*
as `Fin(k)` (`wf.rs:867-890`'s `fin_index`, the only smart constructor that
exists). The surface needs names for those two.

**Spelling: `FZ` and `FS(i)`.** Rationale, in force order:

1. **Constructors are capitalized in this surface** (`Zero`, `Succ`, every user
   constructor), and `head`/`tail`/`cons`/`map` are lowercase because they are
   *functions*. `FZ`/`FS` are constructors.
2. **Arm names and expression spellings must coincide.** Everywhere else in
   Heather a `match` arm is named by the constructor it matches
   (`lib.rs:1899-1905`). A scheme where the arm reads `Zero`/`Succ(j)` (which
   is unambiguous — arms are dispatched by scrutinee type) but the expression
   reads something else would be the first place they diverge.
3. **No collision with `Nat`.** `Succ` is hard-coded and unguarded in
   `elab_infer` (`lib.rs:1604`); reusing it for indices would make
   `Succ(0)` mean two things in inference position.
4. **The repo already uses these names**:
   `docs/inductives/inductive-indexed-lowering.md:123` writes "`Fin`'s `FZ` and `FS` are
   both `Succ`-class", and `:300` contrasts "`FZ` vs `FS`".

*Amendment recorded:* `docs/metaprogramming/meta-def-registration-design.md` §4.1's
`tabulate_code` sketch spells them `fin_zero` / `fin_succ`. That sketch was
written to exhibit a Π order, not to fix a name; this document supersedes it,
and the port round should write `FZ`/`FS`. Flagged rather than silently
changed, because it is the one decision here that is taste over argument.

**Both are checking-only**, mirroring `refl` (`lib.rs:1811`), a vector literal
(`lib.rs:1532`) and a quote (`lib.rs:1819`) — the house pattern for a form
whose type is not determined by its own syntax.

- `FZ` genuinely cannot infer: it inhabits `Fin(Succ k)` for *every* `k`, and
  nothing in the term names one.
- `FS(j)` *could* infer when `j` does (`j : Fin(k)` gives `Fin(Succ k)`), and
  that is the one nicety deliberately left out. Keeping both in one mode means
  one rule to remember, one diagnostic, and — the deciding reason — no
  name-collision question: the arms below fire on the **expected type**, never
  on the name, so a user inductive with a constructor named `FS` is untouched.
  Inference for `FS` is recorded as deferred (§10).

### 3.2 The checking arms, with the annotation-needed cases spelled out

New arms in `elab_check_hinted` (`lib.rs:1230-1355`), placed with the other
expected-type-directed forms and keyed on `whnf(expected)` being
`Type::Fin { len }`:

| Expression | `whnf(len)` | Result |
| --- | --- | --- |
| `FZ` | `Succ(k)` | `Inl { 0, 0, Unit⁰, Fin(k), Triv⁰ }` |
| `FZ` | `Zero` | error: "`Fin(0)` is empty, so it has no index" |
| `FZ` | neutral | error: "the length has to reduce to a successor here; `Fin(n)` at an open `n` has no canonical index" |
| `FS(j)` | `Succ(k)` | `Inr { 0, 0, Unit⁰, Fin(k), ⟦j⟧ }` with `j` **checked** at `Fin(k)` |
| `FS(j)` | `Zero` / neutral | as above |
| `Num(t)` | `Succ^{t+1}(m)` | `fin_index(t, t+1, m)` — §3.3 |
| `Num(t)` | anything shorter | error naming `t` and the length |

and the inference-position diagnostics, in `elab_infer`:

- `FZ` (an `ExprKind::Var`): "`FZ` needs an expected `Fin` type (checking
  position, or an annotated `let`)" — the wording of `refl`'s
  (`lib.rs:1811-1813`).
- `FS(…)` (an `ExprKind::App`): same message naming `FS`, and only when `FS`
  is not shadowed and not a constructor of a declared inductive
  (`ctor_here`, `lib.rs:2293`), so a user `FS` still resolves.

Every checking position a payload actually needs is available: an `xs[i]`
index (§5 checks it at `Fin(len)`), a function argument, an annotated `let`, a
`theorem` body, a `match` arm under a motive.

**Correction, 2026-08-02.** The annotated `let` in that list was *not*
available when this was written, and the implementing round recorded the
falsification on `issues/annotated-let-swallows-the-equals.md`:
`let i: Fin(Succ(n)) = FZ;` did not parse, and neither did `let x: Nat = 3;`.
`docs/language/let-and-blocks-design.md` §3 has since fixed it, so the claim is now
true as stated, and item 7 of §7's plan below — the axis-3 fixture — is live
in `crates/elab/tests/surface_fin.rs::an_index_in_checking_position`.

### 3.3 Numeral sugar at a `Fin` type

**Decision: a numeral checked against `Fin(m)` elaborates to the iterated
index.** `xs[2]` is the spelling anybody will reach for first, and without this
it means `xs[FS(FS(FZ))]`.

Implementation is a reuse, not new code: `wf.rs:867-890`'s
`fin_index(t, m, base)` already builds "index `t` of `Fin(Succ^m(base))`", with
the folded annotations. The checking arm peels `whnf(m)` for `t + 1`
`Succ`s, takes the residue as `base`, and calls it. Emitting *literally the
term `wf.rs` emits* is free adequacy: the surface numeral and the elaborator's
own container indices are the same syntax, so nothing can drift between them.

Inference of a numeral is unchanged (it is a `Nat`); only the checking arm at a
`Fin`-headed expected type is new.

## 4. Case on `Fin`

### 4.1 Decision: reuse `match`; no dedicated form

`elab_match` (`lib.rs:1834-1883`) already dispatches by scrutinee type —
indexed family, declared inductive, `Empty`, `Nat`, error. `Fin` becomes a
fifth case. A dedicated form would need its own motive syntax, its own arm
parser, and its own "in inference position you need a motive" rule, all of
which `match` has.

### 4.2 Where the arm goes, and what it builds

Insert a `Fin` case that tests the **raw** `scrut_ty` (after
`inductive::decoded`) rather than its whnf, for the same reason
`indexed_of_at` does (`lib.rs:1846-1849`): the whnf of `Fin(Succ k)` is a bare
`Type::Sum`, which carries no hint that its arms should be called `FZ`/`FS`.
Placed after the `tag_of` check so a declared inductive still wins, and *before*
the `Nat` fall-through.

Then dispatch on `whnf(len)`:

- **`Zero`** — fall through to the existing `Empty` case (`lib.rs:1862`).
  `head` is already `Type::Empty { level: 0 }`, so `match i { }` produces
  `ElimEmpty { level: mlvl, scrut_level: 0, motive, scrut }` and a non-empty
  arm list gets the existing error. Finding 1 of §1.1: nothing to write.
- **`Succ(k)`** — require exactly the arms `FZ` (no binders) and `FS(j)` (one
  binder), with the usual duplicate/unknown/missing diagnostics of
  `elab_match_nat` (`lib.rs:1896-1909`), and build

  ```
  Term::Case {
      lhs_level: Zero, rhs_level: Zero, motive_level: mlvl,
      lhs: Unit⁰,  rhs: Fin(k),  motive,
      case_l: ⟦FZ arm⟧   in Γ, #u : Unit⁰      at  motive[inl⟨⟩/z]
      case_r: ⟦FS arm⟧   in Γ, j  : Fin(k)     at  motive[inr j /z]
      scrut,
  }
  ```

  The `FZ` arm binds nothing at the surface but the kernel's `case_l` binds one
  local, so the elaborator pushes a `#`-prefixed dummy (the convention
  `build_absurd` already uses for `#y`/`#p`, `inductive.rs:2459-2469`) and the
  arm body is elaborated one binder deeper. Both arm types come from
  `motive.apply_local(… .extended(Inl/Inr …))`, as `elab_match_nat` does for
  its two arms.

  The `Case`'s summands are written **unfolded** (`Unit⁰`, `Fin(k)`) because
  that is what the kernel's typing rule wants and what `term.rs:1203-1213`
  writes; the scrutinee's *type* stays the folded `Fin(Succ k)` and conversion
  bridges them. Same asymmetry `nth` already lives with.
- **neutral** — error (§4.3).

Motive story: unchanged. Motive-less in checking position goes through
`synth_motive` (`lib.rs:2132`) and yields a constant motive, which is what
`nth`'s inner case wants. Explicit `match i as λ w => T` binds `w : Fin(Succ k)`
and is what a dependent use would need. Neither needs new syntax.

### 4.3 The neutral-length rejection, and its diagnostic

> `match` on a `Fin` needs its length to reduce to `0` or a successor; here it
> is `n`. Recurse on the length first (`match n as λ z => …`), which is how the
> index becomes matchable.

The second sentence is the point: it names the fix rather than the limitation,
and the fix is exactly the shape `nth_code` and `tabulate_code` will have.
Per §1.2 this is permanent, so the message must not read like a TODO.

## 5. `xs[i]`

### 5.1 Grammar: one arm in the postfix loop

`ExprKind::Index { recv: Box<Expr>, idx: Box<Expr> }`, produced by a third arm
in `postfix`'s loop (`parser.rs:1091-1120`, beside `Dot` and `LParen`):

```rust
TokKind::LBracket => {
    self.bump();
    let idx = self.expr()?;
    let end = self.expect(&TokKind::RBracket, "`]` (an index)")?;
    let span = e.span.join(end);
    e = Expr { kind: ExprKind::Index { recv: Box::new(e), idx: Box::new(idx) }, span };
}
```

**The bracket collision is empty, and the reason is positional.** `[` is
disambiguated by position, never by lookahead: in type position `ty_atom` reads
`[T; n]` (`parser.rs:863-874`), in expression position `atom` reads a `VecLit`
(`parser.rs:1257-1272`). Both are *prefix*. `xs[i]` is *postfix*, and today an
expression followed by `[` is a parse error in every production — the parser is
not newline-sensitive, statements terminate with `;`, blocks with `}`, vector
elements with `,` or `]`, and match arms with `,` or `}`. So this is a pure
extension in the sense of `docs/language/types-as-expressions.md` §3: no input that
parsed before parses differently, and no backtracking is needed. The
implementing round should re-run that audit as a grep over the productions
rather than trusting this paragraph.

Two pleasant consequences of living in the loop: `[1,2,3][0]` works (postfix on
a literal), and `xs[i].foo` / `xs.map(f)[0]` chain in the order written.

`Index` is a new `ExprKind`, which means the five exhaustive walks in §6 must
learn it. That checklist is the real cost of the node, and it is small.

### 5.2 What it desugars to

Straight to the kernel's `nth`, through the slot:

```
xs[i]   with  xs : Vec^l(A; k)     ⇝    nth^l(A; k; ⟦xs⟧; ⟦i⟧) : A
```

`elab_vec_nth`, modelled line for line on `elab_vec_fold` (`lib.rs:2633`):
infer the receiver; `inductive::decoded` it (a coded `Vec` field is one — the
comment at `lib.rs:2642`); require `Type::Vec { level, elem, len }`, else "an
index needs a vector receiver"; **check** the index at
`Type::Fin { len }` and `Level::Zero`; then

```rust
if let Some(t) = self.try_code_template(cx, Slot::VecNth, &[
    ("A", Ingredient::Type { level: &vl, ty: &elem }),
    ("k", Ingredient::Term((*len).clone())),
    ("v", Ingredient::Term(xs_t.clone())),
    ("i", Ingredient::Term(idx_t.clone())),
], span)? { return Ok((t, elem, vl)); }
Ok((heather_kernel::term::nth(&vl, &elem, &len, Rc::new(xs_t), Rc::new(idx_t)), elem, vl))
```

Inferring, not checking: the element type comes off the receiver.

**Decision: it targets the kernel `nth` today and routes through `nth_code`
the moment one registers.** Not "the future in-language `nth_code` only" —
that would make this round depend on the next one — and not "the kernel `nth`
only", which would make the port a second dispatch pattern. The Rust (here:
kernel) schema stays as the oracle and the fallback, exactly as `vec::map` and
`vec::fold` do (`docs/metaprogramming/in-language-map-design.md` §4's routing policy).

The same round wires `elab_container_ih` (`lib.rs:2795`) to
`try_code_template(Slot::VecTabulate, {B, k, f})` with the `vec::tabulate` call
as its fallback — the call `docs/metaprogramming/meta-def-registration-design.md` §9 says it
"gains … when §4.4's blocker clears". After this round both slots have live use
sites and no template, which is the *silent decline* path the seam was built
for; §7 tests exactly that.

### 5.3 A superseded sketch decision, recorded

`docs/archive/surface-v1.md:79-81` made `xs[i]` "sugar for `xs.get(i, ?_)` —
an implicit proof parameter … becomes an anonymous goal at the call site", and
`issues/goal-holes.md:25` still points at it. That sketch was written against a
`List` with a separate length; in the length-indexed world `i : Fin(n)` **is**
the proof, `nth` is total, and there is no obligation to defer. The auto-hole
idea does not die — it dies *here*, and the fact that it does is an argument
for the indexed encoding. Noted so the two documents do not silently disagree.

## 6. Elaboration: the entry points that change

Exhaustively, because most of them are one-liners and the risk is forgetting
one:

**`crates/syntax`**
1. `ast.rs` — `TyKind::Fin(Box<Expr>)`, `ExprKind::Index { recv, idx }`.
2. `parser.rs:128` `expr_as_ty` — the `Fin` arm (§2.2).
3. `parser.rs:1091` `postfix` — the `LBracket` arm (§5.1).

**`crates/elab`, the new behaviour**
4. `lib.rs:1097` `elab_ty` — `TyKind::Fin` (§2.3).
5. `lib.rs:287` `expr_as_ty` — the `Fin` arm.
6. `lib.rs:1470` `elab_infer` — `Fin(n)` as a code; `FZ`/`FS` inference
   diagnostics; `ExprKind::Index` → `elab_vec_nth`.
7. `lib.rs:1230` `elab_check_hinted` — `FZ`, `FS(j)`, `Num` at a `Fin`-headed
   expected type (§3.2); `ExprKind::Index` falls through to inference.
8. `lib.rs:1834` `elab_match` — the `Fin` dispatch case and `elab_match_fin`
   (§4.2).
9. `lib.rs` — `elab_vec_nth` (new, §5.2); `elab_container_ih` gains its
   `Slot::VecTabulate` call.

**`crates/elab`, the walks a new node must join** (found by grepping the
`VecLit`/`TyKind::Vec` sites — this is the checklist, not a guess)
10. `quote.rs:843` `scan_splices` (expr) and `quote.rs:791` (ty): a `$x` inside
    `xs[$i]` or inside `Fin($k)` must hoist. **Load-bearing for the port
    round** — a missed arm here is a splice that silently does not hoist.
11. `inductive.rs:1990` `expr_mentions`, `:2030` `occurs`, `:2064`
    `recursive_fn`.
12. `lib.rs:3777` / `lib.rs:3742` `count_holes`.

**No changes**: `code.rs` (`Type::Fin → TmFin` exists, `code.rs:70`),
`slots.rs` (specs exist), `vec.rs` (no `nth` there; the schema is kernel-side),
and the kernel.

### 6.1 How the oracle cross-check applies here

The fold/map suites' pattern is: elaborate the same fixture twice, once with
`lib/lang/vec_code.hthr` in scope and once without, and require the two declaration
bodies **convertible at `Layer::Prog`** — adequacy, not typing
(`in_language_fold.rs:103-141`). Plus the vacuity guard that suite added and
the map suite still owes: `assert!(ht != rt)`, so a hook that declined cannot
make `conv` trivially pass.

In *this* round there is no template, so there is nothing to cross-check: both
paths are the same path. What this round owes instead is the **oracle side**:
`xs[i]` must emit exactly `heather_kernel::term::nth`'s output (asserted by
equality against a directly-built term in one fixture, so a future
`nth_code` cross-check has a pinned left-hand side), and the numeral sugar must
emit exactly `wf.rs::fin_index`'s output (§3.3). Then the port round adds
`nth_code` and inherits the comparison for free.

## 7. Test plan

`docs/testing-generated-terms.md`'s axes — literal **and** neutral scrutinee,
an open element type, a **checking** position, a negative control — applied per
new form. New file `crates/elab/tests/surface_fin.rs`; everything under
`scripts/test`.

**`Fin(n)` as a type**
1. `fn f(n: Nat, i: Fin(n)) -> Nat` elaborates; the binder's kernel type is
   `Type::Fin`, not `El(TmFin)` (assert on the elaborated type — this is what
   §2.1's decision buys and the only way to see it).
2. `fn Idx(n: Nat) -> Type { Fin(n) }` checks — the expression spelling, and
   §8's coverage-table claim made true by a test.
3. Negative: `Fin` at arity 0 and 2 gives the arity diagnostic;
   `Fin(true_expr_at_the_wrong_type)` gives the `Nat` mismatch.

**`FZ` / `FS` / numerals** (axis 2 = an open *length*, the analogue of an open
element type here — a closed `Fin(3)` hides every shift)
4. Literal, computing: `theorem t(): [10,20,30][1] = 20 { refl }`.
5. Neutral: `fn at(n: Nat, xs: [Nat; Succ(n)]) -> Nat { xs[FZ] }` — the length
   is open, `FZ` still checks, nothing reduces, the annotations carry it.
6. Open element type: `fn at2(m: Nat, xs: [[Nat; Succ(m)]; 3]) -> [Nat; Succ(m)]
   { xs[2] }` — the axis-2 control the four `vec.rs` defects were hiding in.
7. Checking position, non-computing: an index at an annotated `let`
   (`let i: Fin(Succ(n)) = FZ;`) and as an argument to a function taking
   `Fin(k)`, where the annotation must convert with a goal rather than reduce.
8. Negative controls:
   (a) `FZ` and `FS(j)` in inference position give their annotation
   diagnostics, naming the form;
   (b) `FZ` at `Fin(0)` and at a neutral length give their two distinct
   messages;
   (c) `xs[i]` with `xs : [A; n]` and `i : Fin(m)`, `m` a *different* ambient
   variable, is rejected — the index's length must convert with the vector's,
   and this is the test that it is not silently coerced;
   (d) **axis 4** (a positive test cannot distinguish a type from a quotient of
   it): `theorem bad(): FZ = FS(FZ) { refl }` at `Fin(2)` must be **rejected**.
   Without it, an encoding that collapsed the two constructors passes
   everything above;
   (e) `xs[i]` on a non-vector receiver.

**`match` on `Fin`**
9. `Fin(0)`: `match i { }` in a checking position elaborates to `ElimEmpty`;
   `match i { FZ => … }` is rejected by the existing no-arms error.
10. `Fin(Succ k)` at a **literal** `k`: both arms, and the result *computes*
    (`conv` against the expected reduct, not merely `check`).
11. `Fin(Succ k)` at a **neutral** `k`, inside a `match k` arm — the shape
    `nth_code` will have. This is the axis-1 neutral case that matters: the
    index term is neutral while its type still reduces.
12. A **dependent** motive: `match i as λ w => …` where the body mentions `w`,
    in a checking position (a proof), so the arm types must convert with the
    goal rather than be reduced away (axis 3).
13. Negatives: a neutral *length* gives §4.3's message verbatim; unknown,
    duplicated and missing arms; `FS` with zero or two binders.

**The slots**
14. With no template registered, `xs[i]` and `elab_container_ih` take their
    Rust/kernel paths and every existing suite is byte-identical — the silent
    decline (`docs/metaprogramming/meta-def-registration-design.md` §2.4's use-row).
15. `template_registration.rs` gains nothing; but a `for vec.nth` template
    whose payload disagrees is already rejected by the registration check, and
    that path first becomes *reachable* in the port round — record the status
    in a comment there, as §8.7 of that doc does for the two unreachable
    guards.

**Regressions**
16. `container_proofs.rs`, `in_language_{map,fold}.rs`, `wf_*` suites green;
    in particular `elab_container_ih`'s output must be unchanged by the new
    slot call when no template is registered.

## 8. The `docs/language/types-as-expressions.md` correction

§2's table (`types-as-expressions.md:61`) reads

```
| `Fin` | `TmFin` | yes |
```

which is false about syntax and was true only of the code. Replace with

```
| `Fin` | `TmFin` | yes (`Fin(n)`) — **since the surface indexing layer**; before it, the code existed and no syntax did |
```

and add, immediately after the table:

> The right-hand column means *writable in source text*. The `Fin` row said
> "yes" for a phase on the strength of `code_of` covering `Type::Fin`, which is
> a fact about the middle column; no parse produced a `Type::Fin` until
> `docs/language/surface-fin-indexing-design.md` landed
> (`issues/surface-fin-indexing.md`, discovered in
> `docs/metaprogramming/meta-def-registration-design.md` §4.4). The distinction is worth
> keeping in view for the three `no` rows, which are `no` for the *opposite*
> reason — no code — and for `W`, whose "yes (tier 2, not yet lowered to)" is a
> third status again.

§2's headline finding — "every surface-writable type former has a code" — is
unaffected in either direction, and should not be edited.

## 9. Sequencing: this round versus the ports

**This round (`issues/surface-fin-indexing`)**: §6's twelve items, §7's tests,
§8's correction. The deliverable is that every payload line
`tabulate_code` and `nth_code` need can be written and elaborated, plus the two
use sites wired to their slots.

**The port round (`issues/quotation-stage-artifacts`)**: `tabulate_code` and
`nth_code` in `lib/lang/vec_code.hthr`, and their cross-check suites. Nothing in
`crates/` should need to change — that is the acceptance test of this round's
scope, and if it does not hold, the residue belongs back here.

`nth_code`, for the record, so this round knows what it must support:

```heather
meta fn nth_code(g: Ctx) for vec.nth -> Code(g |-
    (A: Type<0>) -> (k: Nat) -> (v: [A; k]) -> (i: Fin(k)) -> A
) {
    code {
        fun (A: Type<0>) => fun (k: Nat) =>
            match k as λ z => [A; z] -> Fin(z) -> A {
                Zero => fun (v: [A; 0]) => fun (i: Fin(0)) => match i { },
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) => fun (i: Fin(Succ(zk))) =>
                    match i {
                        FZ => head(v),
                        FS(j) => ih(tail(v), j),
                    },
            }
    }
}
```

Every form in it is §§2–4: `Fin(z)` in a motive body (type position, which the
motive already parses with `ty()`), `Fin(0)` and `Fin(Succ(zk))` as lambda
annotations, `match i { }` as `elim_Empty`, and `match i { FZ, FS(j) }` as the
`Case`. Notably it needs **no** `xs[i]` — `xs[i]` is what gives `nth_code` a use
site, not what it is written with. `tabulate_code` needs strictly less: `Fin`,
`FZ`, `FS`, and no case at all.

The parametric-rigidity heuristic (`docs/metaprogramming/in-language-map-design.md` §7) is
worth predicting for both, since the port round will have to decide how much
work the conversion cross-check does: `nth`'s result type is the bare `A`, so
it is **not** rigid in `map`'s sense — but its argument `i : Fin(k)` is the only
thing of that type in scope and the recursion is forced by the length, so the
step arm has no wrong inhabitant to pick; `tabulate`'s result *is* indexed
(`[B; k]`), which is `map`'s situation. Expect a writable mutated-arm control
for neither, and record it if that prediction is wrong — the last two rounds
each refuted one such prediction, and both refutations were the payoff.

*Outcome (2026-08-02, the port round): **both halves refuted.*** `tabulate`'s
`f : Fin(Succ(zk)) -> B` accepts `FZ` wherever it accepts `FS(i)`, so the
constant-head tabulate checks at the same signature; `nth`'s `FS` arm has
`head(v) : A` in scope beside the ih, so the constant-first-element projection
checks too. Only arms whose context offers no alternative are forced (`nth`'s
`FZ` arm, by absence). The refutations and the unifying reading live in the
`lib/lang/vec_code.hthr` template headers and in
`docs/metaprogramming/in-language-map-design.md` §7's addendum.

## 10. Deferred, recorded

- **Inference for `FS(j)`** (§3.1). Cheap; wanted the first time an index is
  built outside a checking position. Its cost is the name-collision rule that
  §3.1 currently avoids paying.
- **`Fin` arithmetic and comparison** — `i + 1`, `i < j`, weakening
  `Fin(n) → Fin(Succ n)`. Nothing needs them yet; they are ordinary library
  functions once bodied globals exist, not surface forms.
- **`xs[i] := v`** (functional update). A second schema, no client.
- **Route A's `All` predicate** over a vector (`docs/language/container-proofs.md` §7):
  now *unblocked* by this layer rather than deferred by it, and it belongs to
  the container-proofs thread, not here.
- **`match` on `Fin` at a neutral length** — not deferred: unwritable (§1.2).
  Recorded here so it is not re-filed as a gap.
- **A `Fin` at a level above 0** — not a thing. `Type::Fin` carries no level
  (`term.rs:153`); this is the one extension former for which the
  level-indexing round had nothing to do.
