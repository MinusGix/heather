# A bare operator symbol resolves from the expected domain's carrier

Status: **designed and implemented** (2026-08-11; §5 and §10 record what
implementing it corrected, and §16 of the operators design is the postscript).
Suite 1432 → 1439. Owner:
`issues/bare-symbol-checking-carrier.md`. Its input is
`docs/operators-onto-classes-design.md` — §4's three-rung ladder, §4.1's
carrier probe, and §12.3, which is the finding this round generalises.
Adjacent and deliberately untouched: `issues/binder-symbol-as-notation.md`
(§15 of that document), which adds a *position in the grammar* for installing
a rung-1 spelling and no resolution path at all.

---

## 1. The problem, in one line

A symbol that is *applied* reads its carrier off its left operand, so `xs ++ ys`
means `append(xs, ys)` at every `List<A>` — but a symbol *passed*
(`mconcat(++, xss)`) has no operand, so rung 2 cannot fire and the only rungs
left are a binder that named it and a fallback the doubled symbols do not have;
which is why `sum_all` may write `mconcat(+, xs)` and `concat`, whose monoid
sits at `List<A>` where no constraint slot can name a symbol, must write
`mconcat(append, xss)`.

## 2. The decision, in one sentence

> **A bare symbol in a checking position takes rung 2 from the first domain of
> its expected type**, because that domain is the carrier the position is asking
> about — the same fact the left operand supplies when the symbol is applied,
> arriving from the other side. The probe fires where the expected type is
> already meta-free, and the existing per-argument **deferral** machinery is
> what makes that the common case rather than the lucky one.

Everything below is that sentence's consequences, and §3 is the part the issue
asked to be pinned rather than assumed.

## 3. The crux: where the expected type actually is

The issue names order sensitivity as the risk, and it is the right risk. The
answer is better than the issue's sketch feared, and it costs one change the
sketch does not mention.

### 3.1 Checking mode already carries the expected type past the symbol

`Elaborator::op_rewrite` runs at the top of exactly three functions:
`elab_infer_at`, `elab_ty`'s `TyKind::OfExpr` arm, and — the one that matters —
`elab_check_skel`, whose signature already has `expected: &Type` in hand. So in
checking position the expected type is *there*, one line above the rewrite, and
has been since the operators round. Nothing has to be plumbed from a call site;
`op_rewrite` and `resolve_op_name` grow an `Option<&Type>` parameter, `None` at
the two inference sites and `Some(expected)` at the checking one.

That is the whole of the new resolution path. The engineering is elsewhere.

### 3.2 The engineering is: a bare symbol has to become checking-only

`elab_check_skel` having the expected type is worthless if the argument never
reaches it, and for the motivating call it would not. `apply_implicit`
elaborates each explicit argument at its parameter's domain, and takes one of
three roads (`crates/elab/src/lib.rs`, the `match zonked(&dom, n, &sols)` in
the parameter loop):

- the domain is already **meta-free** → `elab_check_skel` against it;
- the domain still mentions metas and the argument is
  `is_checking_only` → the argument is **deferred**: its spine position becomes
  a withheld stand-in meta, and the obligation is retried, to fixpoint, once
  later arguments and expected-type solving have filled things in;
- otherwise → `elab_infer`, whose result type *teaches* the metas.

`mconcat`'s parameter list after the linked constraint floats
(`traits.rs::float_linked`) is `A` (implicit), `op` (explicit), the
`Monoid<A>(op)` solver parameter, `xs` (explicit). The symbol is argument 0, and
at argument 0 the domain is `?A -> ?A -> ?A` with `?A` unsolved: the carrier is
not merely unknown, it does not exist yet. Only `xss : List<List<B>>`, argument
1, unifies `List<?A>` and pins `?A := List<B>`.

So the third road is the one a bare symbol takes today, and it is the wrong one:
inference is precisely the mode with no expected type. **The change is to make a
bare operator symbol `is_checking_only`**, under the guard of §4.3, so that it
takes the second road and the fixpoint loop hands it its carrier after the later
argument has produced one.

This is not a new mechanism, and that is the argument for it. It is the same
sentence the doc comment on `is_checking_only` already makes about a bare
reference to a global with a leading implicit prefix: *it can infer, but only at
a shape that mis-teaches, and checking position is where its instantiation is
decidable, so at a meta-bearing domain it waits for one.* A bare `+` infers to
`add` and would teach `?A := Nat` at a call whose carrier is `Bool`. Waiting is
the honest reading, not a concession.

### 3.3 The order, traced

For `fn concat<A>(xss: List<List<A>>) -> List<A> { mconcat(++, xss) }`:

1. `A` (implicit): a fresh meta `?A`, unsolved.
2. `op`: domain `?A -> ?A -> ?A` does not zonk; `++` is checking-only ⇒
   deferred at slot *s*, `Sol::Withheld`.
3. the `Monoid<?A>(op)` solver parameter: `Sol::Withheld`, one `ResolveOb`.
4. `xss`: domain `List<?A>` does not zonk and `xss` is not checking-only ⇒
   inferred, `unify_ty` solves `?A := List<A>`.
5. fixpoint, pass 1 — **resolutions first**: the goal `Monoid<List<A>>(?s)` does
   not zonk, because *s* is the deferred symbol. `fill_index_from_scope` and
   `fill_index_from_designation` both skip a `Withheld` slot by an explicit
   guard already in the code, so neither can pre-empt the symbol. Blocked.
6. fixpoint, pass 1 — deferred: `?A` is solved, so the domain zonks to
   `List<A> -> List<A> -> List<A>`. `elab_check_skel` runs, `op_rewrite` sees a
   bare symbol *and* an expected type, whnfs it to a `Π`, takes
   `type_namespace` of the domain — `List` — and the table answers `append`.
   Progressed, still blocked ⇒ another pass.
7. fixpoint, pass 2: the goal is now `Monoid<List<A>>(append)`, meta-free, and
   the registry answers through `instance<A> Monoid<List<A>>(append)`.

Two properties of that trace are load-bearing and neither is new code. The
`Withheld` guards in the two index fillers mean the symbol's slot cannot be
filled behind its back — the value-slot ladder's steps 2 and 3 are for a slot
*nobody wrote*, and here somebody wrote a symbol. And the rewritten name is
**checked**, not inferred, against the same domain — which is §12.2 of the
operators design getting its lesson honoured for free, since a generic
`append`'s element type is pinned by exactly that domain and by nothing else.

### 3.4 Where the probe cannot fire, and what happens then

Three cases, all decided rather than left to fall out:

- **The expected type is not a `Π`** (`let x: Nat = ++;`). No domain, no
  carrier, no rung 2; the ladder falls to rung 3 exactly as today.
- **The domain has no head** — a variable, a meta, `Type`. `type_namespace`
  already answers `None` for all of these, so this is one code path with the
  case above and needs no separate test for meta-freeness: a domain that still
  mentions metas cannot present a nominal head.
- **The deferral never unblocks** — no later argument pins the carrier, e.g.
  `mconcat(++, Nil)` under a nothing-else-to-go-on elaboration. Today such a
  call resolves `++`… by refusing (no fallback), or, for `+`, by inferring
  `add` and teaching `?A := Nat`. Under this design the obligation is still
  `Withheld` at the end of the loop and the existing "this argument was
  deferred" refusal fires, with the symbol-flavoured wording of §6.

  That last one is a real behaviour change for `+`/`*`/`<=`/`<` in a file that
  designates them, and it is why §4.3 has a gate. It is recorded as residue
  (§12), not hidden: the change trades an inference that could be wrong for a
  refusal that names what is missing, which is the trade `is_checking_only` was
  built to make everywhere else.

**Determinism.** The probe reads a solved meta or nothing; it never searches,
never backtracks, and never runs twice with two answers, because the fixpoint
loop only ever *adds* solutions and a slot is checked exactly once (the loop
skips a slot that is no longer `Withheld`). There is no position where the same
program elaborates two ways depending on iteration order.

## 4. The rung, exactly

### 4.1 Rung order is unchanged; rung 2 gains a second source

The ladder stays three rungs and rung 1 still fires before any type is looked
at. What changes is one clause inside rung 2:

> **(2) The designation at the operand's carrier — or, for a bare symbol in a
> checking position, at the carrier the expected type's first domain names.**

A binder wins over both. That is not a tie-break, it is the same reason rung 1
was first in the first place: inside `<A: Monoid(++)>` the symbol *is* the bound
index, at every carrier, and a designation that happened to cover the carrier
the call instantiates at would be a second meaning for a name the declaration
already bound. The discriminating control is in §10: a binder naming `||`,
instantiated at `Bool` with `and`, must still mean `and` even though `||`
designates `or` at `Bool`.

Rung 3 is unchanged and still last, and still runs when rung 2's new source
produces a carrier with no row — which is the sentence that keeps the
no-fallback refusals refusals.

### 4.2 The new source fires only for a *bare* symbol

An applied symbol in checking position has both an operand and an expected type,
and it reads the operand. Rejected alternative: prefer the expected type, or
consult it when the operand probe fails. Both are refused for the same reason —
every operator expression that elaborates today would have a second thing that
could change its meaning, and §4's growth invariant is a structural claim, not
an audited one. The operand is also the *more specific* evidence: it is the
value the operation will actually be applied to, where the expected type is only
what the surrounding position will accept. One inversion, in the one place where
there is nothing to invert away from.

### 4.3 The gate: checking-only only for a symbol that is designated somewhere

`is_checking_only` answers `true` for a bare `ExprKind::OpSymbol(s)` **iff**
rung 1 misses (`cx.op_locals` has no `s`) **and** the designation table has at
least one row for `s`.

The second conjunct is the growth invariant's guard, and it is the same guard
rung 2 already carries (`self.designations.keys().any(|(s, _)| s == sym)`, so
that a file declaring no designations pays one failed lookup in an empty map and
no inference). With it, a file that declares no designation for a symbol
produces byte-identical terms by running byte-identical code — including the
`fold(+, Nil)` shape whose meta the fallback `add` used to teach. Without it,
that shape would start refusing in files that predate this round, which §4 of
the operators design forbids in as many words.

The first conjunct is rung 1's precedence expressed at the deferral, and it
matters for cost as well as meaning: `sum_all`'s `mconcat(+, xs)` resolves at
rung 1 and is therefore never deferred, so the library's existing symbol fold
elaborates through exactly the code it does today.

## 5. Scope of "checking position"

**Every position where `elab_check_skel` runs with an expected type** — the
resolver takes no position test, it reads whatever expected type it is handed.

**Amended during implementation (2026-08-11).** This section was drafted arguing
that the elaborator rule is wider than the issue's "argument slot" framing, and
it is; what the draft missed is that the *grammar* is narrower than either.
`Parser::op_symbol_arg` — the only producer of a bare `ExprKind::OpSymbol` — is
called from `Parser::call_args` and nowhere else, so an operator token is read
as a bare symbol **only in argument-initial position**, directly after `(` or
`,` and followed by `,` or `)`. That is not an oversight to fix here: it is §4
of the operators design holding its reservation, keeping the position free for a
future prefix operator, and widening it is
`issues/notation-extensibility.md`'s axis with no customer.

So `let g: Bool -> Bool -> Bool = &&;` is a **parse error**, not a checking
position that declines — and the issue's framing and this section's describe the
same observable language. Two consequences worth stating rather than leaving
implicit:

- **The widening costs nothing and is still the right shape.** Threading a
  position flag to make the resolver refuse what the parser already refuses
  would be an exception with no case behind it, and the general rule pre-pays
  for any grammar position a later round opens. `a_bare_symbol_is_grammatical_-
  only_in_an_argument_slot` pins the two halves together so they cannot drift.
- **An argument slot always has an expected domain**, so with the gate of §4.3
  in place a bare symbol never reaches an inference position at all. §3.4's
  first two cases are still real (a domain with no nominal head — the caller's
  own type variable — is the writable one, and it is the negative control of
  §10 item 3), but the third, the deferral cliff, is the only *observable*
  boundary left.

What is **outside**, and stays outside:

What is **outside**, and stays outside:

- **Inference positions** — `elab_infer_at`, and the `TyKind::OfExpr` rewrite in
  `elab_ty`. There is no expected type there by definition, and per the
  amendment above no bare symbol can be *written* into one either.
  (`elab_infer_at`
  does take an `expected` for the congruence hook, and it is deliberately *not*
  passed to `op_rewrite`: it is the expected type of a call's *result*, reached
  only from `elab_check_skel`'s inference fallback, i.e. only after the rewrite
  at the top of `elab_check_skel` has already happened. A bare symbol reaches
  `elab_infer_at` unrewritten only in genuine inference.)
- **The index slot of a constraint** (`Monoid(+)`) — that is rung 1's
  *installation* site, handled in `traits.rs` by minting `#op+@0_0`, and it
  never calls `resolve_op_name`.
- **The qualified-name dictionary spelling** (`Bool::Monoid(+)`) — §12.3's
  second site, which reads the carrier out of the subject it was written with.
  It stays its own two-line loop; the expected type there would be less
  specific than the thing the user wrote.

## 6. Diagnostics

Three messages, one of them new.

**(a) The refusal names the carrier it tried.** Today's rung-0 refusal says "no
`designation {sym} at …` covers this carrier" with no carrier in it, because the
applied path drops the probed head into `uncovered_carrier` and only uses it for
a fallback note. Both sources now feed one field, and both name it:

> ``` `++` has no meaning here: no constraint binder named it
> (`<A: Monoid(++)>`), nothing designates `++` at `Nat` — the carrier this
> position expects — and `++` has no fallback name. `++` designates something at
> `List` (`list::append`). ```

with *the carrier of its left operand* in place of *the carrier this position
expects* for the applied case, and today's carrier-less wording preserved
verbatim when neither source produced a head. The applied case gaining a carrier
name is a small improvement the unification pays for; it is additive, so the
existing content-checked refusal tests keep passing and gain an assertion.

**(b) The fallback note gains the bare case.** `op_fallback_notes` already
records "`+` has no designation at `List`, so it used its fallback name `add`"
when an applied probe found an uncovered carrier, so that a subsequent kernel
failure retains the notation fact (§14 of the operators design). The bare case
produces the same note from the same field, with the same "the carrier this
position expects" clause.

**(c) The deferred-argument refusal learns that it is holding a symbol.** The
generic message ("this argument of `mconcat` was deferred — the type of its
parameter `op` still mentions an implicit that could not be inferred") is true
but says nothing about why a symbol needed the type. For a deferred bare
`OpSymbol`:

> ``` `++` is a bare operator symbol, so it needs the carrier this position
> expects — and the type of `mconcat`'s parameter `op` still mentions an
> implicit that could not be inferred here. Name the operation instead of the
> symbol, or give the type arguments (`mconcat<…>(…)`). ```

This is the message §3.4's third case reaches, and it is the reason that case is
acceptable: the user is told which of the two spellings works and why the one
they wrote could not.

## 7. Rejected alternatives

### 7.1 A fourth rung

Add "the expected type's carrier" as rung 4, after the fallback. Rejected: it
inverts the point. The fallback is the *legacy* rung, deliberately last so that
`True + False` cannot resolve to `Nat`'s addition; putting a carrier-directed
answer behind it would mean `mconcat(+, bs)` at `Bool` resolves to `add` and
dies in the kernel while a designation sat unread. The expected domain's carrier
is the same *kind* of evidence the operand is, so it belongs at the same rung.

### 7.2 Probe from the callee's parameter type at the call site

Resolve the symbol in `apply_implicit` by reading the parameter's declared type
before elaborating the argument. Rejected: the declared type is
`A -> A -> A` with `A` a binder, not a carrier — the whole difficulty is that
the carrier arrives from *another* argument — so this either reads a meta or
re-implements zonking beside the loop that already does it. It also puts the
symbol's meaning in the caller's application code rather than in the resolver,
which is exactly the two-mechanism shape §8.1 of the operators design rejected.

### 7.3 Solve the order problem by reordering arguments

Elaborate non-symbol arguments first so the carrier is known when the symbol's
turn comes. Rejected: argument order is user-visible (a later argument's type
may mention an earlier argument's *value*), and the deferral loop is the
existing, tested answer to exactly this question. Reordering would be a second
one.

### 7.4 Widen the probe to the expected *result* type

For `A -> A -> A` the result's head is the carrier too, and it would cover a
symbol whose first domain is not the carrier. Rejected: §4.1's closure
assumption is already recorded as residue with no customer, and reading the
result adds a second place a wrong answer can come from with no case that wants
it. The first domain matches "the left operand" exactly, which is the property
that makes the two sources of rung 2 one rule.

### 7.5 Restrict to argument slots as the issue frames it

Rejected in §5, with reasons.

## 8. Perf posture

Nothing new is computed for a program that does not use the feature. The
`is_checking_only` arm is one `op_locals` scan (rung 1's own scan, at most a
handful of entries) plus one `designations` key scan, both already paid by
`resolve_op_name`, and both reached only for an `ExprKind::OpSymbol` node —
which no file written before the operators round contains. The probe itself is a
`whnf` of a type that was about to be whnf'd anyway plus a `type_namespace`
lookup: no inference, unlike the applied probe, because there is no operand to
infer. The deferral costs one extra scratch slot per deferred symbol, which the
`n_defer` pre-count already over-approximates for every checking-only argument.

The measurement is `lib/std/algebra/algebra.hthr` (three call sites gained) and
`lib/lang/list_algos.hthr` / `lib/certgen/ir_v1.hthr` as the no-designation controls, per §9
of the operators design.

## 9. The library payoff

Three bodies and two comments.

```heather
fn concat<A>(xss: List<List<A>>) -> List<A> { mconcat(++, xss) }

fn any_of(bs: List<Bool>) -> Bool { mconcat(||, bs) }

fn all_of(bs: List<Bool>) -> Bool { mconcat(&&, bs) }
```

The comment above `any_of`/`all_of` currently argues that the positional
spelling is load-bearing — "`+` means nothing at `Bool`, so each names its
operation positionally, which costs one word and is legal forever". Its *last*
sentence is the one worth keeping, and it gets stronger rather than weaker:

> The `Bool` folds are still not `sum_all` — `+` means nothing at `Bool` — but
> each now writes its own symbol, and the bare symbol takes its meaning from the
> carrier the slot expects (`Bool`), not from any structure being preferred
> there. Side by side they are the sentence that nothing was nominated: two
> symbols, two structures, one carrier, both registered, both reachable, neither
> the default. The positional spelling stays legal forever, and
> `all_of_single`/`any_of_single` below still use it.

The header comment (algebra.hthr §"A `designation` says what an operator SYMBOL
means at a carrier") gains one clause: *applied, the symbol reads its carrier
off its operand; passed, off the carrier the position expects — one sentence,
two directions.* And the `designation<A> ++ at List<A>` comment notes that this
row is now what `concat`'s `mconcat(++, xss)` reads, which is the open-carrier
case of the new rung.

**What does not change**, and this is most of the claim: no `class`, no
`instance`, no `designation`, no constraint slot, no call site outside these
three bodies, and no proof. In particular `mconcat` keeps its linked slot and
its `op as ∙`; `mconcat_single` keeps its plain positional parameter; `sum_all`
still resolves at rung 1 and elaborates through untouched code; and
`concat_single`, `all_of_single`, `any_of_single` still prove themselves with
`mconcat_single(append, …)` / `(and, …)` / `(or, …)` — which is itself a free
acceptance pin, since those proofs only typecheck if `concat` and `all_of` are
*the same terms* they were before the respelling.

## 10. Acceptance

Per `docs/testing-generated-terms.md`'s four axes; the axes are named where they
are exercised, because three of them are the feature's own shape.

1. **The headline, at three carriers**, each pinned by `refl` against the
   positional spelling so that the sugar and the written form are one term:
   `mconcat(&&, bs)` and `mconcat(||, bs)` at the **concrete** carrier `Bool`
   (two symbols, one carrier — and the pair pins that neither designation
   answered for the other), and `mconcat(++, xss)` at an **open** element type
   (`concat<A>` itself), which is axis 2 and the only one that can see §12.2's
   check-don't-infer requirement on the generic `append`.
2. **Checking position is the feature** (axis 3), so the controls are the two
   ways it can fail to be one. **Amended during implementation** in line with
   §5: the "inference position" control is a *parse* error rather than a
   resolution one (`a_bare_symbol_is_grammatical_only_in_an_argument_slot`), and
   the writable control is a slot whose domain has **no nominal head** — the
   caller's own type variable, `fn g<A>(xs: List<A>) -> A { fold(&&, xs) }` —
   which declines the probe and falls to a fallback `&&` does not have, with the
   `List<A>` carrier beside it as the resolving contrast. The deferral cliff of
   §3.4 is pinned separately (`a_symbol_with_no_carrier_in_sight_says_so`),
   at a callee with **no solver parameter**: at `fold`/`mconcat` the blocked
   `Mon<?A>(?op)` goal reaches the older value-slot refusal first, which is the
   better message about the same situation and is left in front.
3. **Negative control: a carrier with no designation** — `fold(&&, ns)` at
   `List<Nat>` refuses, and the refusal names `Nat` as the carrier it tried,
   names `Bool` as where `&&` does mean something, and says `&&` has no fallback
   name; with `fold(++, bs)` at `Bool` as the second row, since `++` is
   designated only at `List`. This is the "no-fallback refusals stay refusals"
   clause, content-checked.
4. **Rung 1 shadows rung 2**, discriminatingly: `fn f<A: Mon(||)>(xs: List<A>)
   -> A { fold(||, xs) }` instantiated with `@f(and, Bool::Mon(and), bs)` is
   `fold(and, bs)` — at `Bool`, where the designation for `||` says `or`. The
   binder wins against a rung that would have answered differently, which the
   existing `Mon(++)`-at-`Nat` test cannot show because no designation covers
   `Nat` for `++`.
5. **A neutral scrutinee and a literal** (axis 1) at the Bool folds:
   `all_of(Cons(True, Cons(b, Nil)))` for the neutral, and a fully literal list
   that must compute to a value.
6. **The growth invariant**: a file with **no** designations still resolves
   `fold(+, xs)` by the fallback in inference position, byte-identically (the
   `bare()` harness of `crates/elab/tests/operators_onto_classes.rs`); `<=` and
   `<` are untouched; and `sum_all`'s `mconcat(+, xs)` still resolves at rung 1
   with no deferral.
7. **Two existing refusal tests flip, deliberately**, and their comments are
   rewritten rather than deleted — both live in
   `crates/elab/tests/operators_onto_classes.rs`:
   - `a_bare_symbol_between_delimiters_is_the_index`'s boundary case
     `fold(+, bs) = fold(or, bs)` at `List<Bool>` currently refuses (rung 3 gives
     `add`, the kernel rejects). It becomes **provable**: `+` designates `or` at
     `Bool` in that test prelude. The test's third stanza changes from "elsewhere
     a bare symbol has no operand and so no carrier" to "elsewhere a bare symbol
     takes the carrier the position expects, and the boundary is now *inference*
     position".
   - `a_doubled_symbol_has_no_fallback_rung`'s last stanza,
     `fold(&&, bs) = fold(and, bs)`, flips for the same reason. Its first two
     stanzas — the `Nat` refusal and the no-designations-anywhere refusal — must
     **stay refusals**, and the first one gains the carrier-naming assertion.
   Everything else in that file, and the whole of `binder_symbol_notation.rs`,
   stays green unchanged; that is the "does not disturb the rung architecture"
   claim, stated as a test outcome.
8. **The library** (`lib_algebra.rs`, `lib_list_algos.rs`): the three respelled
   bodies check, and `concat_single` / `all_of_single` / `any_of_single` prove
   unchanged — the term-identity pin of §9.
9. Full `scripts/test`, suite count recorded; `lib/std/algebra/algebra.hthr` timed
   against §12.7's numbers with the two no-designation files as controls.

## 11. What `docs/operators-onto-classes-design.md` should be amended to say

Three edits and a postscript, in the shape §5.1 was amended by the `as` round —
the sentence restated rather than deleted, with the reason it grew.

- **§4, rung 2.** The rung's text becomes the §4.1 sentence above: *the
  designation at the operand's carrier — or, for a bare symbol in a checking
  position, at the carrier the expected type's first domain names.* And the
  paragraph introducing the bare symbol ("A bare symbol between delimiters …
  is the same node unapplied") gains: *unapplied is not the same as
  carrier-less; §12.3 found one place a bare symbol has a carrier and the
  postscript below found the general one.*
- **§4.1.** Retitle the reasoning as *the carrier probe, both directions*, and
  add the inverted case beside the left-spine descent: the applied probe infers
  a leaf and reads its head; the bare probe whnfs the expected type and reads
  its first domain's head; both are **proposals**, both fall through to rung 3
  when they miss, and neither can produce a wrong term because the kernel gate
  is downstream of both. The closure assumption residue covers both.
- **§12.3.** This is the finding that must be *restated*, not just extended. Its
  claim is that §4's "a bare symbol has no carrier" is right for an ordinary
  argument and wrong for a qualified name. The first half is now wrong too, and
  what survives is sharper: **a bare symbol in an *inference* position has no
  carrier; everywhere else it has one, and there are two places it comes from —
  the subject of a qualified name, and the expected type of a checking
  position.** §12.3's `fold(+, bs)` example, currently offered as the boundary,
  moves to the other side of the line and is replaced by an inference-position
  example.
- **A §16 postscript** recording what landed: the checking-only gate (and why it
  is gated on the symbol being designated at all), the deferral trace of §3.3,
  the diagnostics of §6, the two flipped tests, and the library's three
  respellings — plus the residue of §12 below, whose owner is
  `issues/surface-operators.md`.

## 12. Residue, with owners

- **The deferral cliff** (§3.4). A designated symbol whose slot never unblocks
  now refuses where `+` would previously have inferred `add` and taught the
  carrier from it. The refusal is the better answer (the taught carrier could be
  wrong), but it is a change, and it applies only to files that declare a
  designation for that symbol. Owner: `issues/surface-operators.md`.
- **A bare symbol is grammatical only in an argument slot** (§5, amended).
  Rung 2 still cannot fire in an inference position, but no bare symbol can be
  written into one, so the two statements have no observable difference today.
  If a later round opens another position — `let g: T = ++;`, a record field —
  the resolver needs no change and the reservation question is
  `issues/notation-extensibility.md`'s. No customer.
- **§6(c) sits behind the value-slot refusal** at any callee with an indexed
  class's solver parameter, which is every fold in the library. The older
  message is the better one there (it names the class and lists the instances),
  so the ordering is kept; §6(c) is what a callee *without* a solver parameter
  says. Recorded so that a future reader does not mistake the ordering for an
  accident. Owner: `issues/surface-operators.md`.
- **The closure assumption** (§4.1) is unchanged and now covers two probes: the
  bare probe assumes the carrier is the *first domain*, as the applied probe
  assumes it is the left operand. Same failure mode (a fallback), same reason
  not to enforce it (the designation is keyed on a head, not a type).
- **`mconcat`'s name and any dedicated syntax** —
  `issues/mconcat-surface-story.md` — and **implicit operation parameters on
  lemmas** — `issues/mconcat-single-implicit-op.md` — both read differently
  after this lands, as the issue predicted: with `mconcat(++, xss)` legal, the
  argument that the operation must be spelled at every call site is weaker for
  computational functions and unchanged for lemmas. Neither is decided here.
