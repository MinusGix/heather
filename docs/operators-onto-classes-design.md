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
designation prefix - at Int := neg
```

Read: *the symbol `+`, at a carrier whose head is `Nat`, designates `add`.*
The form is deliberately shaped like `instance`: the generic binder list is in
`instance<A> Monoid<List<A>>(append)`'s position and does the same job (it
exists to *spell* the carrier), the carrier is a written type, and the
right-hand side is `:=` plus a name, which is what an instance's literal field
is.

Grammar: `"designation" "prefix"? tyvars? OP "at" ty ":=" expr`. Omitting
`prefix` means infix, preserving every original declaration. `designation` is
contextual exactly as `class` and `instance` are — a declaration cannot begin
with it, since the next token would have to be an operator.

### 3.2 The key, and what the two halves admit

The key is **(fixity, symbol, carrier-head)** — one entry, a duplicate is a
declaration error naming the previous one. The carrier's head is computed by
`head_name`, the very function layer 1 keys instances on, so `List<A>` and
`List<Nat>` are one key for the same reason two instances at one head collide.

**Amended 2026-08-18** (`issues/designation-key-collides-across-modules.md`):
the head component is the head's **resolved declaration** and not its written
name — `list::List`, never `List` — which is
`docs/instance-resolved-key-design.md` §3's rule ("no component of a registry
key is a spelling") applied to this table. Two modules each declaring a `List`
and each designating `++` at their own are two entries; the same resolved
carrier twice is the declaration error it always was. `head_name` still
computes what the *diagnostics* print, and `DesignationInfo::carrier` keeps it
for them, because the key stopped being something a reader can be shown.

The lookup side is where this table differs from the instance registry, which
had one: a designation is looked up from an **operand's** carrier — a lowered
type's declaration — so `Elaborator::carrier_of_ty` reads the declaration's own
key (`qkey(module, name)`) off the type rather than re-resolving a spelling at
the use site. Re-resolving would answer "ambiguous" in a file importing two
`List`s, about a type nothing there is ambiguous about.

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

`+` is `ExprKind::OpSymbol { symbol: "+", fixity: Infix }`. `a + b` is that
symbol **applied**: `App { head: OpSymbol { ... }, args: [a, b] }`. A bare
infix symbol between delimiters
— `Monoid(+)`, `A::CommMonoid(+)` — is the same node unapplied. The parsing
rule is §7's, decided there and implemented here without reopening: an
operator token in argument-initial position (directly after `(` or `,`) has
exactly one reading, because an infix operator can never *begin* an
expression; a lone operator token between delimiters is always the designation
reference, which reserves the position against a future prefix operator.

**Amended 2026-08-11** (`docs/bare-symbol-checking-carrier-design.md`):
*unapplied* is not the same as *carrier-less*. §12.3 found one place a bare
symbol has a carrier — the qualified name, which wrote it down — and the
postscript §16 found the general one, the expected type of a checking position.
Rung 2 below is stated for both.

A symbol resolves to a **name**, and then everything downstream is the ordinary
application path — the same checking position, the same implicit insertion, the
same spilling, the same diagnostics. Three rungs, in order:

> **(1) A constraint binder that named the symbol.** `<A: Monoid(+)>` installs
> `+` as the local meaning of its index binder for the whole declaration —
> signature and body. Innermost declaration-level binding wins; this is the
> only rung that can fire inside generic code, and it fires without looking at
> any type.
>
> **(2) The designation at the carrier.** The symbol is applied and the left
> operand's type has a head; or the symbol is bare in a **checking** position
> and the expected type's first domain has one (amended 2026-08-11, §16). Where
> the table has an entry at (symbol, head): the designated global.
>
> **(2b) The designation at a class** (amended 2026-11-06,
> docs/division-design.md §6). When rung 2 found no head at all (the operand
> is at a section's type parameter), the designation at the class of a
> dictionary in scope, innermost first: `designation postfix ⁻¹ at
> OrderedField := OrderedField::inv` gives `x⁻¹` its meaning inside
> `section<K: OrderedField(…)>`. The designated operation is generic and
> emitted bare, so its own dictionary is found at the operand's carrier.
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

### 4.1 The carrier probe, both directions, and why it is a proposal

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

**Amended 2026-08-11.** The probe has a **second direction**, and the two are
one rule. Applied, it *infers a leaf* and reads the head off the result. Bare
in a checking position, it whnfs the **expected type** and reads the head off
its **first domain** — the slot where the left operand would have sat — which
costs no inference at all, there being no operand to infer. Both are
**proposals**: no head, or no entry at the head, and the ladder goes on to rung
3, so a mis-probe costs a rung and never a wrong term. The closure assumption
above covers both, the bare direction assuming the carrier is the first domain
exactly as the applied one assumes it is the left operand. Only a *bare* symbol
reads the expected type: an applied one has an operand, which is the more
specific evidence, and admitting a second source there would put something new
in the path of every operator expression that elaborates today.

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

The measurement that matters is `lib/std/algebra/algebra.hthr`, which is where the
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

**Restated 2026-08-11** (`docs/bare-symbol-checking-carrier-design.md`), because
the surviving half is now the smaller one. The parenthesis above is wrong too:
`fold(+, bs)` at `List<Bool>` resolves at `Bool`, because the slot's own type
says which carrier is being asked about. What is left of §4's sentence is
sharper than what it claimed:

> A bare symbol in an **inference** position has no carrier. Everywhere else it
> has one, and there are two places it comes from — the subject of a qualified
> name, and the first domain of the type a checking position expects.

And the grammar makes even that boundary unobservable today:
`Parser::op_symbol_arg` is called from `call_args` alone, so a bare symbol can
only be *written* in an argument slot, and an argument slot always has an
expected domain. The boundary test `fold(+, bs)` was flipped to a positive in
`crates/elab/tests/operators_onto_classes.rs`, and what replaced it is a slot
whose domain has no nominal head — the caller's own type variable — where the
probe declines and rung 3 is again the only rung left.

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

`lib/std/algebra/algebra.hthr`, release, ulimit-wrapped, best of three:
**0.247 s → 0.251 s**. `lib/lang/list_algos.hthr` 0.606 → 0.612; `lib/certgen/ir_v1.hthr`
40.40 → 40.66. All within run-to-run noise (<1.5%), and the last two use no
designation at all, which is the growth invariant showing up as a number.
Suite **1354 → 1375**.

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

  > **Amended 2026-08-16** (`issues/modifiers-in-shared-binder-runs.md`): the
  > refusal is lifted; the sentence is not. A modifier prefixes one name — the
  > one it is written on — so it is read *inside* the run, per name.
  > `g as ∙, h: A -> A -> A` is `g` carrying `∙` and `h` carrying nothing,
  > both at that type; a second name may carry its own symbol
  > (`g as ∙, h as +: …`), and two names at the *same* symbol still hit §5.2's
  > uniqueness rule, which is per spelling and not per group. The `record`
  > value parameter refusal is untouched — that one is about what a binder is,
  > not about where its modifier sits.

What is deliberately *not* here: a class **advertising** a symbol to its
users' binders. `as` is strictly local, so `Monoid` writes `∙` in its own laws
while claiming no default (`issues/class-default-operators.md` owns that, and
the lean there is that `Monoid` advertises nothing).

Suite 1419 → 1432.

## 16. Postscript (2026-08-11): a bare symbol in a checking position

`issues/bare-symbol-checking-carrier.md`, designed in
`docs/bare-symbol-checking-carrier-design.md` and landed. §4's rung 2, §4.1 and
§12.3 are amended above; this is what the amendment cost.

- **The resolver change is three lines.** `op_rewrite` runs at the top of
  `elab_check_skel`, whose signature has had `expected: &Type` in it since this
  round — so the expected type was always one line above the rewrite, and rung
  2's second source is an `Option<&Type>` threaded into `op_rewrite` and
  `resolve_op_name`, `Some` at that one site and `None` at the two inference
  ones. `Elaborator::expected_carrier_head` whnfs it, takes the first `Π`
  domain, and asks `type_namespace` — which answers `None` for a variable, a
  meta or anything else with no nominal head, so a domain that still mentions
  an implicit declines without a separate meta test.
- **The engineering is that a bare symbol became checking-only.** Handing
  `elab_check_skel` the expected type is worthless if the argument never gets
  there, and at `mconcat(++, xss)` it would not: `op` is argument 0 and its
  domain is `?A -> ?A -> ?A` with `?A` unsolved until `xss` pins it. So a bare
  symbol answers `is_checking_only` — gated on rung 1 missing **and** the symbol
  being designated somewhere — and `apply_implicit`'s existing per-argument
  **deferral** is what hands it the carrier a later argument produced. That is
  the same sentence the bare-implicit-prefix arm beside it already makes: it can
  infer, but only at a shape that mis-teaches (`+` infers to `add`, whose type
  would pin a `Bool` call's carrier to `Nat`), so at a meta-bearing domain it
  waits for one.
- **Nothing can fill the slot behind the symbol's back.** `fill_index_from_-
  scope` and `fill_index_from_designation` both skip a `Withheld` slot by a
  guard that was already there — the value-slot ladder's steps 2 and 3 are for
  a slot *nobody wrote*, and here somebody wrote a symbol — so the fixpoint
  discharges the argument first and the goal grounds on the round after.
- **The gate is the growth invariant.** "Designated somewhere" is rung 2's own
  guard, reused: without it a file that designates nothing would stop inferring
  `+` by the fallback, and the fallback's own type is sometimes what teaches the
  call its carrier, so a program written before this round could start refusing.
  With it such a file runs byte-identical code, and `sum_all`'s `mconcat(+, xs)`
  — rung 1 — is never deferred either.
- **Diagnostics.** The rung-0 refusal now **names the carrier it tried** and
  which source it came from ("nothing designates `++` at `Nat` — the carrier
  this position expects —"), which the applied direction gains too; the
  fallback note of §14 gains the same clause; and a deferred bare symbol is
  reported as a symbol rather than as a nameless deferred argument. That last
  one sits *behind* the value-slot refusal at any callee with an indexed class's
  solver parameter, deliberately: the older message names the class and lists
  the instances, and is the better answer about the same situation.
- **Two refusal tests flipped, deliberately**, with their comments rewritten
  rather than deleted: `fold(+, bs)` and `fold(&&, bs)` at `List<Bool>` now
  resolve at `Bool`. What must stay a refusal did: a carrier the table does not
  cover, and a file that designates nothing anywhere.
- **The library**: `concat`, `any_of` and `all_of` are respelled
  `mconcat(++, xss)`, `mconcat(||, bs)`, `mconcat(&&, bs)`, and not one class,
  instance, designation, constraint slot or proof changed —
  `concat_single`/`all_of_single`/`any_of_single` still prove themselves against
  the positional `mconcat_single(append, …)`, which only typechecks because the
  respelled folds are *the same terms*. `mconcat` keeps its linked slot and its
  `op as ∙`; `mconcat_single` keeps its plain positional parameter.
- **What the grammar still says.** `Parser::op_symbol_arg` is called from
  `call_args` alone, so a bare symbol is writable in an argument slot and
  nowhere else — `let g: Bool -> Bool -> Bool = &&;` is a parse error. The
  resolver takes no position test all the same, which is what keeps it one rule
  with no flag; the two halves are pinned together by a test so they cannot
  drift.

- **Measurements**, release, ulimit-wrapped, best of three. The same binary on
  the *old* and *new* `lib/std/algebra/algebra.hthr`: **0.291 s → 0.290 s**, so the
  respelling is free; `lib/lang/list_algos.hthr` 0.600 s, which uses no bare symbol
  in an argument slot at all and sits in §12.7's band, so the resolver change
  is free too.

Suite 1432 → 1439.

## 17. Postscript (2026-10-31): constraints sharing a symbol at one carrier

`<A: OrderedField(≈, <, <=, +, *) + CommRingOfInt(≈, +, *)>` used to be
refused by §5.1: each constraint installed `≈`, `+` and `*`, so each symbol
named two binders. The library answered with combined classes that added
nothing but the pairing (`OrderedFieldOfInt`), which is the pattern Minus
asked to retire (issues/constraints-sharing-indices.md).

**Linking alone is not enough.** Pointing the second constraint's slots at
the first's binders makes both dictionaries range over one `≈`, one `+`, one
`*`, and works while the two classes share no ancestor. These two do:
both reach `CommRing`, and two dictionaries are two locals, so
`OrderedField::zero_lt_one` speaks about `#constraint0.unit` and
`CommRingOfInt::of_int_one` about `#constraint1.multiplicative.unit`. No
choice of which dictionary a bare `A.unit` reads fixes that, because a
lemma mixing the two classes' laws is stated over both copies.

**So the constraints become one dictionary.** `merge_linked_constraints`
(crates/elab/src/traits.rs) runs before a declaration's attempts begin,
between items where Ψ may grow:

- Anonymous inline constraints whose every index slot is a symbol, at one
  carrier (the written type arguments agree), and sharing a symbol, form a
  group. A class written twice in a group is left to §5.2.
- The group becomes one constraint at a synthesized class named by its
  parents sorted, `CommRingOfInt+OrderedField`: its parameters are the first
  parent's, one value parameter per distinct symbol, `extends` every parent
  linked through those parameters, and no fields of its own. Class
  flattening dedups the shared ancestor, which is the diamond collapse class
  declarations already rely on, so `CommRing` occurs once and both parents
  are reached from the one dictionary by upcast.
- The class is made in the module that first asks for it and found by name
  after that; the sort means written order does not make a second class.
  A class of that name linked differently is refused by name.
- The merged binder stands where the earliest member was written, and
  `expand_constraints` then treats it as any one constraint: the symbols are
  installed once.

**At a concrete carrier the dictionary is assembled from the parents.** The
merged class has no instances. Resolution's step 2b (`join_parents`,
crates/elab/src/resolve.rs) reads each parent's type off the goal's own
arguments (its applied spelling, where unsolved operations are still goals
that the parents' searches solve by unification as a registry candidate
would), resolves it, and builds the record taking every field from the first
parent that has it. That checks at `Rat` and `CReal` because their canonical
instances already share the ancestor by reference (traits-design §4). At an
open carrier with no merged dictionary in scope the fields need not agree,
and the kernel gate refuses the assembly. A closed answer is queued for the
canonical table, so a carrier pays for its assembly once. That has to work
with goals in flight, because nearly every call is in a tactic's
certificate: `record_joined` reads the applied spelling out of the goal
world and the call's Γ before queueing it, and `joined_hit` looks entries up
at the spelling, shifted into the goal world. Without it every `linarith`
call rebuilt and re-gated the whole dictionary, and `creal`'s cold build
went past the suite's CPU rail.

**Index pinning reads the parents too.** A call's index slots are filled
from a dictionary in scope of the goal's class or a descendant
(`scope_dict_index`, crates/elab/src/dispatch/dictionary.rs). A merged
class has none in a scope holding its parents: `linarith` at a section's
class carrier `K: OrderedField(…)` puts `OrderedField::with_ints<K>()`, a
`CommRingOfInt`, beside the section's field. So for a merged class each slot
is read off the first parent dictionary in scope that fills it, and the
join then assembles the record from the same two.

`linarith`'s certificate section now writes the two constraints, and
`OrderedFieldOfInt` and its two instances are gone. Probes:
lib/_tests/std/algebra/ordered_field_tests.hthr.

**Left open** (issues/merged-constraint-class-identity.md). Two modules
that do not import each other can each synthesize the class, and a third
importing both sees two classes of one name; nothing in the library does
that yet. A *named* constraint (`requires m: …`) does not merge, since its
body reaches the dictionary by name.
