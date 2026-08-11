# Operators onto classes: design record — designations and `Monoid(+)`

Status: **designed and implemented** (2026-08-09; §12 records what implementing
it corrected). The last entry of the traits-line order agreed at session close
2026-08-07 (`issues/frontend-roadmap.md`). Its input is
`docs/operation-indexed-classes-design.md` §7 — the designation interface,
specified there and deferred to here — and it consumes §4.1's SYMBOL referent,
§5's ladder step 3, and §11's refusal polish. Constraints:
`docs/traits-layer2-design.md` (search order, trace-as-data),
`docs/traits-type-projection-design.md` (as round one amended it),
`issues/notation-extensibility.md` (the standing notation position, whose
closing sentence is this round's licence).

Owner: `issues/operation-indexed-classes.md` and `issues/surface-operators.md`.

---

## 1. The problem, in one line

`+` is a **parser desugaring to a bare global name** — `a + b` is literally the
AST for `add(a, b)`, and the elaborator has never heard of the symbol — so the
one thing a notation is for, *meaning something different at different
carriers*, is the one thing it cannot do; meanwhile round one gave the language
classes indexed by their operation and left their only spelling a written
identifier.

## 2. The decision, in one sentence

> **An operator symbol is a name in a namespace of its own, and a
> `designation` is what puts a meaning in it at a carrier.** Resolution of a
> symbol is a three-rung ladder — a constraint binder that named the symbol,
> then the designation at the operand's carrier, then the symbol's fixed
> fallback name — whose last rung *is* today's parser desugaring, so every
> operator expression that elaborates today elaborates to the same term.

Everything below is that sentence's consequences.

### 2.1 Why the symbol is a name and not a form

The alternative shape — keep `+` a desugaring and add a *second*, type-directed
path beside it — was drafted and lost (§8.1). Making the symbol a name buys
three things at once, and no other framing buys more than one:

- **`Monoid(+)` and `x + y` become one mechanism.** §7 of the input document
  asks for a designation *reference* in an index slot and a designation *use*
  in an expression. As a name, the first is the bare symbol and the second is
  the symbol applied — one `ExprKind`, one resolver, one table.
- **The growth invariant is structural, not audited.** The fallback rung is
  the current desugaring moved from the parser into the resolver's last stop;
  a file with no designations produces byte-identical terms because it runs
  byte-identical code.
- **It is what `issues/notation-extensibility.md` already decided.** That
  issue's closing boundary is *"parsing is context-free; only resolution
  (which trait, which instance) consults scope."* A symbol resolved by the
  elaborator is on the right side of that line; a symbol desugared by the
  parser to a fixed name was on neither side of it, because it never asked.

## 3. Designations

### 3.1 The declaration

```heather
designation + at Nat := add
designation + at Bool := or
designation * at Bool := and
designation<A> + at List<A> := append
```

Read: *the symbol `+`, at a carrier whose head is `Nat`, designates `add`.*
The form is deliberately shaped like `instance`: the generic binder list is in
`instance<A> Monoid<List<A>>(append)`'s position and does the same job (it
exists to *spell* the carrier), the carrier is a written type, and the
right-hand side is `:=` plus a name, which is what an instance's literal field
is.

Grammar: `"designation" tyvars? OP "at" ty ":=" expr`. `designation` is
contextual exactly as `class` and `instance` are — a declaration cannot begin
with it, since the next token would have to be an operator.

### 3.2 The key, and what the two halves admit

The key is **(symbol, carrier-head)** — one entry, a duplicate is a
declaration error naming the previous one. The carrier's head is computed by
`head_name`, the very function layer 1 keys instances on, so `List<A>` and
`List<Nat>` are one key for the same reason two instances at one head collide.

The right-hand side must be a **bare global name**. Not "spellable" in
`index_spelling`'s wider sense (which admits `f<A>`): a designated operation
is fetched at a use site whose type arguments are the *use site's*, so the
name is emitted bare and ordinary implicit inference instantiates it — which
is exactly how `mconcat(append, xss)` already reaches the generic instance.
Anything else is refused at declaration with the rule stated. The name is
resolved at declaration time, so a designation of something that does not
exist is caught where it is written and not where it is used.

**Non-symbol names are not designatable.** §7 of the input document raised and
set aside a designation for `op` itself; the argument there (it is default
instances wearing a smaller hat) is accepted verbatim and the grammar cannot
express it: the slot after `designation` is an operator token.

### 3.3 One table, not two

**One.** The question §7 defers — whether `+`-designations and "any operator
class the round wants" are one mechanism — is answered by not wanting an
operator class. A class that *owned* `+` would have to answer "which class owns
`+` at this carrier", which is the nomination question the whole round-one
design exists to delete, re-entering through the notation door. A designation
owns no laws and asserts no structure: it says what a symbol means, and the
classes go on being indexed by operations. That is why `+` at `Bool` can be
`or` while `*` at `Bool` is `and` with neither being "the" Bool monoid — the
symbols distinguish, and both `CommMonoid<Bool>(and)` and
`CommMonoid<Bool>(or)` stay registered as equals.

The table is global on the elaborator, beside `instances`, and is not
module-scoped for the same reason the instance registry is not.

## 4. Resolving a symbol

`+` is `ExprKind::OpSymbol("+")`. `a + b` is that symbol **applied**:
`App { head: OpSymbol("+"), args: [a, b] }`. A bare symbol between delimiters
— `Monoid(+)`, `A::CommMonoid(+)` — is the same node unapplied. The parsing
rule is §7's, decided there and implemented here without reopening: an
operator token in argument-initial position (directly after `(` or `,`) has
exactly one reading, because an infix operator can never *begin* an
expression; a lone operator token between delimiters is always the designation
reference, which reserves the position against a future prefix operator.

A symbol resolves to a **name**, and then everything downstream is the ordinary
application path — the same checking position, the same implicit insertion, the
same spilling, the same diagnostics. Three rungs, in order:

> **(1) A constraint binder that named the symbol.** `<A: Monoid(+)>` installs
> `+` as the local meaning of its index binder for the whole declaration —
> signature and body. Innermost declaration-level binding wins; this is the
> only rung that can fire inside generic code, and it fires without looking at
> any type.
>
> **(2) The designation at the operand's carrier.** The symbol is applied, the
> left operand's type has a head, and the table has an entry at (symbol,
> head): the designated global.
>
> **(3) The symbol's fallback name.** `+`→`add`, `*`→`mul`, `<=`→`Le`,
> `<`→`lt`, resolved by `Elaborator::resolve` exactly as the parser's
> `named_call` made it resolve before this round. This rung is the growth
> invariant.

Rung 3 is last rather than first for a reason worth stating: `add` is an
ambient global at `Nat`, so a name-first ladder would make `True + False`
resolve to Nat's addition and then fail in the kernel, which is precisely the
"fixed name-directed resolution" `issues/surface-operators.md` recorded as a
stopgap. It is *reachable*, though: it fires for every file that declares no
designation for the symbol, which is every file written before this round.

### 4.1 The carrier probe, and why it is a proposal

Rung 2 needs the left operand's type head before the head of the call is
known, which inverts the ordinary order (head first, arguments checked against
its domains). Two rules keep the cost linear and the risk nil:

- **Descend the left spine first.** `a + b + c` is `(a + b) + c`, and the
  probe walks down through operator applications to the leftmost
  *non-operator* leaf and infers that one. A chain of length *d* costs *d*
  leaf inferences, not 2^*d* — the naive "infer `args[0]`" is exponential in
  chain length, and the descent is exactly what makes it not.
- **A wrong head costs a fallback, never a wrong term.** If the leaf does not
  infer, or has no head, or the table has no entry there, rung 3 runs. The
  probe claims the same licence `scope_dict_index` claims: it is a proposal,
  the answer still passes the kernel gate.

The descent assumes an operator's result carrier is its left operand's, which
holds for every operation a designation can usefully hold (`A -> A -> A` is
what an indexed class's index is). It is not enforced, because enforcing it
means type-checking the designation against a carrier the declaration only
names the head of; the failure mode is a fallback, so the enforcement would
buy a better message and nothing else. Recorded as residue (§11).

## 5. The `Monoid(+)` constraint form

§4.1 of the input document gives the index slot three referents. The third is
built here:

```heather
fn sum_all<A: Monoid(+)>(xs: List<A>) -> A {
    match xs {
        Nil => A.unit,
        Cons(h, t) => h + sum_all(t),
    }
}

theorem op_unit_of_comm<A: CommMonoid(+)>(x: A): x + A.unit = x { … }
```

Desugaring: a SYMBOL slot behaves as the EMPTY slot does — an ordinary implicit
index binder, then the instance binder over it — with two additions.

- **(b) The symbol is installed as the binder's local meaning**, for the whole
  declaration, so `x + A.unit` in a *result type* is the bound index applied
  and not an ambient operator. This is what makes theory-in-notation work, and
  it is the difference between a notation and a global.
- **(a) At a call site, when unification leaves the index open, it is filled
  from the designation of the symbol at the caller's carrier** — the value-slot
  ladder's step 3, at last built. `sum_all(ns)` at `List<Nat>` pins `A := Nat`
  from the argument, the goal `Monoid<Nat>(?op)` is blocked on its index, the
  table says `+` at `Nat` is `add`, the goal grounds and the registry answers.

### 5.1 Each referent binds exactly one spelling

A rule the input document leaves implicit and this round has to state, because
`<A: Monoid(+)>` has two candidate names for one binder:

> The empty slot binds the index under the class's **declared** parameter name
> (`op`); the linked slot binds it under **your parameter's** name; the symbol
> slot binds it under **the symbol**.

So `<A: Monoid(+)>` does *not* also bind `op`. That is not a restriction, it is
§5.2's uniqueness rule holding its shape: `<A: CommMonoid(+) + CommMonoid(*)>`
must bind two distinct things, and it does — `+` and `*` — with no bare `op`
to be ambiguous about. A declaration that wants the identifier writes the empty
slot, which is what theory does anyway.

**Amended 2026-08-11** (`issues/binder-symbol-as-notation.md`). The rule above
is about a *slot*, and a slot has one job; a **declaring binder** has two, so
`op as ∙` deliberately gives one referent two spellings and the rule is
restated by role rather than weakened:

> The **identifier is the interface spelling** — what constraint slots link
> to, what call sites pass, what the registry keys on, what every diagnostic
> says — and the **symbol is the body spelling**, live only inside the
> declaration whose binder installed it. One spelling per role; the sentence
> above is the case where the roles coincide.

So `class Semigroup<A>(op as ∙: …)` is still a class whose index is named
`op`: the empty slot binds `op`, a linked slot binds the caller's own name, a
symbol slot binds the symbol, and none of them has heard of `∙`. And §5.2's
uniqueness check now runs over **both namespaces**: a declaration may not bind
`∙` twice, nor `op` twice, by any mix of constraint slots and `as`. Only the
symbol half needed new code — `as` mints no identifier, it gives a second role
to the one the binder already has — so the identifier half is the
parameter-list rules that were already there, unchanged
(`Elaborator::check_symbol_free` is the symbol half, and it is one loop over
the one table §5(b) already installs into).

The index binder's generated name carries its symbol (`#op+@0_0`), because the
call site has to recover "this slot was designated by `+`" from the callee's
parameter list and nothing else travels there. That is the same device round
one used for `#index{i}_{k}` and `#constraint{ix}`: a `#`-prefixed name is
unspellable, so it is free to be a record.

## 6. What the ladder does *not* do: the concrete-carrier regression stands

The round was asked whether designations recover the terseness round one lost
(§14.6 of the input: at a concrete carrier `Bool.unit` and `x.assoc(y, z)` are
refused, because an indexed class has no scope binder there). **They do not,
and they must not.**

The reasoning is short. A designation is keyed *per symbol*. The dot sugar
names no symbol — `Bool.unit` says nothing about `+` or `*`. To let a
designation fill that slot, the elaborator would have to choose which of the
symbols designated at `Bool` to consult, and at `Bool` there are two (`+` is
`or`, `*` is `and`). Any rule for choosing — one designation wins, the first
declared wins, the one whose designated operation has an instance of *this*
class wins — is a nomination mechanism, which is §9.2 of the input document
rejected and rebuilt under a new name. **So the regression stands**, and the
`Bool.unit` refusal is still a refusal.

What the round does instead is §11's polish, which is the whole of what can be
had honestly: **the refusal now names the designations that exist at the
carrier and spells the binder that would use them.** At `Bool` it reads
"`+` designates `or` and `*` designates `and` here: take the class as
`<A: Monoid(+)>`, or write the dictionary (`Bool::Monoid(or).unit`)". A reader
who wanted `Bool.unit` is told, in one line, both spellings that work and why
neither was guessed.

A third spelling — a dot sugar that names its symbol, `Bool.(+).unit` — was
considered and is **direction, not scheduled**: it is a new grammar for a case
with no library customer, and the dictionary spelling already says it.

## 7. Diagnostics

Trace-as-data throughout; one new refusal, three grown ones.

- **Duplicate designation** → names the symbol, the head, the previous
  right-hand side and where it was written.
- **A non-name right-hand side** → refused with the rule (§3.2) and the reason
  (the operation is emitted bare and instantiated at the use site).
- **An unknown right-hand side** → the ordinary name-miss, at the declaration.
- **A designation at a head that is not a type** → refused as an instance at
  such a head is.
- **The value-slot refusal** (input §5, §11) grows its ladder sentence to
  three rungs and, where the carrier's head has designations, lists them with
  the `<A: C(+)>` spelling (§6).
- **A symbol that resolves to nothing** — no binder, no designation, no
  fallback global — reports the *symbol as written* and the designations that
  do exist for it, rather than "unbound name `add`", which was the old answer
  and named something the user never typed.
- `render_expr` re-sugars an operator application (`a + b`, not `add(a, b)`),
  which is `issues/diagnostics-name-the-written-form.md`'s standing ask,
  arriving free because the written form now survives into the AST.

## 8. Rejected alternatives, with reasons

### 8.1 A second, type-directed path beside the desugaring

Keep `a + b` a `named_call("add", …)` and add an elaborator rule that, when
the name misses or the operand type has a designation, redirects. Rejected: it
is two mechanisms with a precedence question between them, the growth
invariant becomes an audit rather than a structure, and `Monoid(+)`'s index
slot still needs a symbol node — so the "smaller" option ships the new AST
node *and* keeps the old path.

### 8.2 A designation attached to an instance

`instance CommMonoid<Bool>(or) designates +`. Rejected: a designation is per
(symbol, carrier), an operation is the index of a *chain* of classes
(`Semigroup`, `Monoid`, `CommMonoid` all at `or`), so attaching it to an
instance either multiplies the entry by the chain's length or picks a class to
privilege. It also couples the notation choice to the structure declaration,
which is exactly the coupling §7 of the input document flagged as the cost of
`class Semigroup<A>(+)` — declined there, declined here for the same reason.

### 8.3 Designating non-symbol names

Covered by §3.2: the input document set it aside and the grammar cannot say
it.

### 8.4 An operator class (`class Add<A> { add: … }`)

The Rust/Haskell shape. Rejected as §3.3 argues: it re-poses the nomination
question at the notation layer, and it would make `+` at `Bool` demand a choice
between `and` and `or` that this design's whole point is not to have to make.

## 9. Perf posture

Rung 1 is a vector scan of the declaration's installed symbols. Rung 3 is the
existing name resolution. Rung 2 is the only new work, and it is one
`elab_infer` of the leftmost leaf of an operator spine, run only when the
symbol has designations at all and only when rung 1 missed — so a file with no
designations pays a failed lookup in a usually-empty map. The call-site index
fill (§5(a)) runs inside the blocked branch of `apply_implicit`'s existing
fixpoint, beside `fill_index_from_scope`, and adds no iteration of its own.

The measurement that matters is `lib/std/algebra.hthr`, which is where the
library's designations live and the only file that uses them; §12 records it.

## 10. Acceptance

Per `docs/testing-generated-terms.md`'s four axes, and the growth invariant is
its own row.

1. **The headline**: `fn sum_all<A: Monoid(+)>(xs: List<A>) -> A` with `h +
   sum_all(t)` in the body, called at **three** carriers — `Nat` (→ `add`),
   `Bool` (→ `or`), and an **open** element type `List<B>` (→ `append`, the
   generic designation and the generic instance together) — each pinned by
   `refl` against the positional spelling `mconcat(op, xs)`, so the sugar and
   the written form are one term.
2. **Theory in notation**: `theorem op_unit_of_comm<A: CommMonoid(+)>(x: A):
   x + A.unit = x`, and its corollaries at `add`, `and`, `or` still pinning
   their index by unification alone — the symbol in the *statement*, the index
   still recovered from the goal.
3. **The growth invariant**, three ways: (a) a file with no designation for
   `+` gets today's term (`add`, by fallback), including one that defines its
   *own* `add`; (b) with the library's designation loaded, `+` at `Nat` is
   still `nat::add`, pinned by `refl` against `add(x, y)`; (c) `<=` and `<`
   have no designations and are byte-identically the fallback path.
4. **Two symbols at one carrier**: `+` is `or` and `*` is `and` at `Bool`,
   both monoids still registered, `sum_all` at `Bool` giving `or` and a
   `<A: Monoid(*)>` fold giving `and` — the sentence that no nomination
   happened.
5. **Refusals as data**, content-checked: a duplicate designation; a
   non-name right-hand side; an unknown one; a designation at a non-type head;
   a symbol with no rung (`+` at a carrier with no designation and no
   fallback global in scope) naming the symbol as written; and the grown
   value-slot refusal at `Bool` naming both designations and the `<A: C(+)>`
   fix.
6. **Negative controls**: a designation at `Nat` does *not* answer at `Bool`;
   `<A: Monoid(+)>`'s `+` does not leak out of the declaration; a bare `op`
   under a symbol slot is unbound (§5.1); a different operator's designation
   is not consulted.
7. **Checking position and a neutral scrutinee** at the migrated library
   functions, per the testing doc.
8. **The concrete-carrier refusal still refuses** (§6), with its new
   designation clause — the regression pinned as a *decision*, positively.
9. Full `scripts/test`, suite count recorded.

## 11. Residue, with owners

- **The probe's closure assumption** (§4.1): a designation whose operation is
  not closed on its carrier mis-probes a nested operator chain and falls back.
  No customer; enforcing it needs the carrier and not just its head. Owner:
  `issues/surface-operators.md`.
- **The lexicon is still four tokens** (`+ * <= <`). Every new symbol is
  `issues/notation-extensibility.md`'s, and this round deliberately adds none
  — it makes the *existing* four resolvable, which is the half that was
  missing.
- **`Bool.(+).unit`** (§6): direction, not scheduled.
- **`class Semigroup<A>(+)`** and the algebraic-theory declaration form with
  auto-generated corollaries: still direction-not-scheduled, untouched here
  per the input document §7.
- **Declaration-level installation only** (§5): the symbol a constraint names
  is installed for the declaration, not per-scope, so a `let`-bound dictionary
  cannot install one. Same shape as round one's §14.8 residue, same reason
  (nothing needs it), same owner.

## 12. What implementing this corrected

Seven findings. None changes §2's sentence; four change how a section reads.

### 12.1 A symbol in *type* position needed its own rewrite site (§4)

The rewrite was designed as a pre-pass on `elab_infer_at` and
`elab_check_skel`, on the reasoning that everything is an expression. It is
not: `n <= m` reaches `elab_ty` as a `TyKind::OfExpr`, and that arm's readings
(an indexed family at its index, a **record at its value parameters** — which
is what `Le(n, m)` is) all key on an `App` with a `Var` head. With the head an
unresolved symbol, `n <= m` in an annotation stopped being `Le(n, m)` and
became a decoded code, which reported a `Le`-can't-infer-its-value-arguments
error a reader would have no way to connect to `<=`. Fixed by rewriting at the
head of the `OfExpr` arm too — three sites, not two — after which `x + A.unit`
as an equation's endpoint works for the same reason. §4 should be read as
"wherever an expression is *read*", not "wherever an expression is elaborated".

### 12.2 The designated operation has to be **checked**, not inferred (§3.2)

§3.2 argues the right-hand side is emitted bare so the use site instantiates
it. True, and the first implementation still got it wrong: it filled the index
slot with `elab_infer` of the bare name, which for a *generic* operation
(`append` at `List<B>`) leaves the element type an unsolved implicit and the
resolver then rejects every candidate with an unreadable trace. The fix is one
line and it is the honest one: the slot's own domain — the index binder's
declared type at the carrier this call solved — is available and meta-free
exactly when the carrier is, so the name is **checked** against it. The
concrete carriers passed either way, which is `docs/testing-generated-terms.md`
axis 2 for the seventh time: only the open element type could see it.

### 12.3 The qualified name is the one place a bare symbol has a carrier (§4)

§4 says a bare symbol has no operand and so no carrier, and rung 2 cannot
fire. That is right for an ordinary argument (`fold(+, bs)` is rung 1 or the
fallback, pinned as a boundary test) and **wrong** for `Bool::Mon(+)`, where
the qualified name wrote the carrier down. The operation-indexed design's §5.1
promised `A::CommMonoid(+)` as a dictionary spelling, and it costs one loop in
`class_at_type`: the subject *is* the head the table is keyed on. Ordinary
arguments are unchanged, so this is a second site rather than a widened rule.

### 12.4 The symbol slot's declared name needed the §5.2 device (§5.1)

§5.1 decides that a symbol slot binds under the symbol and not under the
class's declared name. Implemented, a bare `op` under `<A: Monoid(+)>` reported
`unbound name \`op\`` — technically correct and useless. Fixed by reusing round
one's own device verbatim: the declared name is recorded per declaration with
the refusal it owes, consulted at the one point where the answer would
otherwise be "unbound name". So §5.1's rule and §5.2's rule now share a
mechanism, which is the right relationship — both are "this name binds nothing
*here*, and here is what does".

### 12.5 The fallback rung fires more often than the refusal reads

`o + o` at a carrier with no designation resolves to the fallback `add` and
dies in the kernel as `NotConvertible`, because `add` **is** in scope; the
"`+` has no meaning here" refusal only fires when the fallback name is
nowhere. That is exactly today's behaviour (`o + o` was `add(o, o)` before this
round too) and it is what the growth invariant buys, so it is kept — but §7's
symbol refusal is narrower in practice than that section implies. Recorded
rather than fixed: making it wider means preferring a designation-shaped
failure over a name that resolves, which is rung 3 losing its guarantee.

### 12.6 The library keeps one fold, not two (§10, item 4)

The migration's temptation was a `prod_all<A: Monoid(*)>` beside
`sum_all<A: Monoid(+)>` so that both Bool structures have a notation-form
fold. Declined in the library (it is kept in the *tests*, where two symbols at
one carrier is the thing under test): a second declaration of one fold under a
second symbol is the duplication §1 opens by objecting to, and `all_of` staying
`mconcat(and, bs)` is the better sentence — the positional spelling is legal
forever, and its sitting beside `any_of` is the plainest statement that nothing
was nominated.

### 12.7 Measurements

`lib/std/algebra.hthr`, release, ulimit-wrapped, best of three:
**0.247 s → 0.251 s**. `lib/list_algos.hthr` 0.606 → 0.612; `lib/ir_v1.hthr`
40.40 → 40.66. All within run-to-run noise (<1.5%), and the last two use no
designation at all, which is the growth invariant showing up as a number.
Suite **1354 → 1375**.
</content>

## 13. Postscript (2026-08-09): the Boolean spellings `&&`/`||`

Filed the day this round closed and paid the same day
(issues/bool-operator-designations.md): the library's Bool designations
shipped as the semiring convention — `+` = or, `*` = and — and the review
replaced them with the doubled programming spellings. What changed, and what
it exercised in this design:

- **Two new tokens.** `&&` and `||` lex as two-byte tokens; the single `&`
  and `|` stay lex errors, deliberately — `|` in particular is reserved
  against a future or-pattern, and doubling is what keeps the singles
  unclaimed. This is a fixed-grammar lexicon addition
  (issues/notation-extensibility.md's axis 1 at its cheapest: new symbols,
  no new shapes, parsing still context-free).
- **Precedence: below `+`/`*`, above the comparison rung** — deliberately
  unlike C, where `&&` is looser than `<=`. The comparison level here is
  propositional (`=` is the identity type, `<=` is `Le`), so a Boolean
  operand never wants to contain one, and theorem statements want the
  arithmetic reading whole: `x && True = x` is `(x && True) = x`, exactly as
  §5's `x + A.unit = x` already relies on. `&&` binds tighter than `||`.
- **No fallback rung.** §4's third rung is the parser's old table and nothing
  else — that is the growth invariant's charter — and the doubles postdate
  the table, so `op_fallback` has no entry for them: away from a binder or a
  designation they refuse, the first symbols whose entire meaning is the
  designation table. The rung-3 refusal learned to say "has no fallback
  name" for this case instead of mislabeling the symbol as outside the
  grammar.
- **The library designates `&& at Bool := and`, `|| at Bool := or`** and the
  semiring rows are deleted. `sum_all` at `Bool` therefore refuses (`+` means
  nothing there), the two Bool folds (`any_of`/`all_of`) both name their
  operations positionally, and the corollaries `bool_and_true`/
  `bool_or_false` are stated in the new notation. The *mechanism* stays
  convention-agnostic: the tests keep the semiring rows in their own table
  (crates/elab/tests/operators_onto_classes.rs), where two symbols at one
  carrier is the thing under test.

Nothing else moved: both `CommMonoid<Bool>` instances stay registered as
equals, nothing nominates, and `op_unit_of_comm` is untouched — the review
was purely about what two symbols mean at one carrier, which is exactly the
small question §3 built the table to make small. Suite 1375 → 1383.

## 14. Postscript (2026-08-10): `++` for List append

The same curated-lexicon recipe now gives List concatenation its programming
spelling (`issues/list-append-symbol.md`): `++` is a two-byte token at `+`'s
precedence and associativity, has no fallback name, and is designated at the
open carrier by `designation<A> ++ at List<A> := append`. The old `+ at List`
row is gone; `concat` uses the positional `mconcat(append, xss)`, beside the
Bool folds for the same reason — a fold declaration is not duplicated merely
to follow every symbol.

The migration also sharpens §12.5's diagnostic without changing its semantic
decision. A symbol with a valid fallback still takes rung 3. If the resulting
declaration reaches the kernel and fails, the error now retains the known
notation fact: for example, old `xs + ys` at List reports that `+` had no List
designation and therefore used `add`. A user-defined `add` that genuinely
accepts lists remains legal; the note explains a failed fallback rather than
turning designation lookup into a refusal.

Suite 1400 → 1405.

## 15. Postscript (2026-08-11): `op as ∙` on declaring binders

`issues/binder-symbol-as-notation.md`, landed. §5.1 is amended above; this is
what the amendment cost and what it did not.

- **One installation, two places to write it.** `as` attaches to a
  **declaring** binder occurrence — a class head's index parameter, and a
  `fn`/`theorem` value parameter — and pushes onto `Cx::op_locals`, which is
  the table §5(b)'s constraint symbol slot already pushes onto and rung 1 of
  §4's ladder already reads. There is no second resolution path and no fourth
  rung: `as` adds a *position in the grammar*, not a way for a symbol to mean
  something. A reference never takes it — a linked constraint slot mentions a
  parameter declared elsewhere, and notation belongs where the name is born —
  so the three slots keep exactly the grammar this round gave them.
- **Scope is the binder's scope.** For a value parameter: the rest of the
  telescope, the result type, and the body — the result type being the
  load-bearing third, since a `theorem`'s statement *is* its result type. For
  a class head: the class body, installed where the field types are actually
  elaborated (`lower_ctor`, per instantiation) and cleared of the *use site's*
  spellings first, because a class's field types are the class's own source.
- **`∙`, one curated token.** `issues/notation-extensibility.md`'s reserved
  generic operator lands in the lexer: three bytes (U+2219), so it needed a
  three-byte window beside the two-byte one; multiplicative precedence, by
  that issue's precedence-by-class scheme; **no** designation row anywhere and
  **no** `op_fallback` entry, so rungs 2 and 3 can never fire for it and away
  from a binder it cannot mean anything. That is the reservation, enforced by
  absence rather than convention, and it is why `Semigroup`'s laws can be
  written in a symbol that will never whisper commutativity.
- **The library**: the three algebra classes and `mconcat` restate their
  bodies in `∙`, and not one instance, designation, caller or proof changed —
  which is the whole claim, since the identifier never moved.
- **A modifier prefixes one name** (the multi-binder round's sentence,
  `issues/multi-binder-function-types.md`): `g as ∙, h: A -> A -> A` would
  give one symbol to two binders, so it is refused by name beside `self`'s
  identical refusal. A `record`'s value parameter is refused too — it is a
  term the fields mention, not a binder with a body to spell.

What is deliberately *not* here: a class **advertising** a symbol to its
users' binders. `as` is strictly local, so `Monoid` writes `∙` in its own laws
while claiming no default (`issues/class-default-operators.md` owns that, and
the lean there is that `Monoid` advertises nothing).

Suite 1419 → 1432.
