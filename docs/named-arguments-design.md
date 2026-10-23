# Named arguments at call sites, and defaults at binders

Design record for `issues/named-arguments.md`. Round pattern as usual: this
document first, the implementing round against §11's acceptance list.

**Status: no kernel change is required, and none is proposed.** Everything
below is `crates/syntax` (one two-token lookahead in one function, one new AST
field on two nodes) plus a purely additive pass in `crates/elab` that runs
*before* the two existing spine walkers and hands them the argument vector they
already take. The load-bearing property is stated once here and pinned by a
test in §11: **a call with no named argument takes byte-identically the path it
took before.**

The issue is the last item on the roadmap's "stop deciding this by position"
line ([[method-receiver-position]] was the one before it). It arrives carrying
a second half re-homed from [[true-prop-trivial-hypotheses]] — *default
argument values declared at the binder* — and §9 decides what happens to that
half.

## 1. What this round decides, and what it does not

Seven decisions, and one deliberate staging:

1. **§3 — the spelling is `f(x := e)`**, not `f(x: e)` and not `f(x = e)`.
2. **§4 — written order is free; elaboration order is declaration order.**
   Named arguments are normalized into the Π spine's order before anything is
   elaborated, exactly as a record literal's fields already are.
3. **§4.2 — positional first, then named.** A positional argument after a
   named one is a *parse* error, not an elaboration error.
4. **§5 — naming an implicit gives it.** That is the point of the feature:
   `sym(p, a := x)` pins `a` and leaves `b` inferred. Mechanically it is the
   existing `apply_implicit` mask with one bit flipped, and nothing else.
   Naming a **solver** parameter gives it by hand, finer-grained than `@f(…)`.
5. **§5.3 — type parameters are *not* nameable**; `f<…>` stays their spelling,
   and the reason is that their argument is a *type*, not an expression.
   Staged, with its shape pinned, at §10.1.
6. **§6 — constructors are nameable**, by field name, which is the
   record-construction payoff [[surface-records]] §6 asked for.
7. **§7 — a callee with no parameter *names* refuses named arguments**, with a
   message that says why rather than "unknown parameter". This is the
   two-tier rule the issue asked to have decided rather than discovered.

Staged, not implemented, shape pinned: **§9, defaults at binders.** The
grammar slot is settled and it is the one `:= infer` already occupies; what is
*not* settled is where a default's free names resolve, and that is the whole of
the remaining work. §9.4 says so and sizes it.

Not in scope, each with a home named in §10: patterns by name, retiring the
braced record literal, partial type application, and named arguments through a
trait/record *interface* (which is [[compile-typeclass-design]]'s question and
must be answered with it).

## 2. What is already true, and why that decides most of this

Three facts about the codebase, each of which removes a question rather than
answering it.

**2.1 Parameter names are already API, in writing.** `ParamMeta.name`
(`crates/elab/src/lib.rs`) exists so that a goal raised in argument position is
*named after the parameter*, and `on ?bound := …` discharges it by that name.
The doc comment says it: "The *name* is API: it is the default name of a goal
raised in that argument position, so callers discharge by it." So the objection
that has stalled named arguments in Rust for a decade — that making parameter
names callable retroactively turns every rename into a breaking change — does
not arise here. The names are load-bearing already; this round adds a second
consumer of a commitment already made.

**2.2 `:=` appears in no expression position and in no argument position.**
Eight grammar sites use `TokKind::ColonEq` (`designation … := op`, a minted
`datarepr`/`impl` body, a repr clause, an instance literal field, a binder's
`:= infer`, `on ?g := e`, a `calc` step proof) and every one of them is a
declaration head, a clause, a statement or a binder — never an operand.
Therefore `IDENT :=` inside call parentheses is *free syntactic real estate*:
today the parse dies at `expect(RParen)`. §3.2 is what makes the lookahead
total rather than speculative.

**2.3 By-name argument permutation already exists, once.** `record_lit_args`
(`crates/elab/src/lib.rs`) takes a record literal's fields, looks each name up
in `ind.ctors[0].fields`, refuses a duplicate and lists what is missing, and
returns the arguments *in declaration order*. §6 generalizes that function
rather than writing a second one; §4's "free order, normalized before
lowering" rule is that function's rule, promoted from records to calls.

## 3. The spelling: `f(x := e)`

### 3.1 Why not `:`

`f(a: e)` does not collide with anything in the grammar today (§2.2's
companion fact: `:` never *continues* an expression, so `call_args` simply
fails at the `)`). It is rejected anyway, for two reasons that are about
reading rather than about parsing.

**`:` introduces a type, everywhere else in this language, without exception in
binding position**: `fn f(x: T)`, `{a: T}`, `requires m: C<A>`, `let x: T = e`,
`on _: P := e`, `(x: A) -> B`, a class field, a record field *declaration*.
Heather also has `docs/types-as-expressions.md` — a type *is* an expression in
the positions where both are legal — so `f(A: Nat)` is not merely
unfamiliar, it has two readings that are both well-formed: "fill the parameter
`A` with the value `Nat`" and "the expression `A`, ascribed to `Nat`". A
grammar can pick one; a reader cannot.

**And the codebase has already made this call, in the same situation.** An
instance's literal field is `op := Rat::add`, and the parser's own error text
says why: "``:=`` (an instance's literal field is ``op := e``; ``:`` is the
record literal's spelling and would be ambiguous here). Choosing `:` for call
arguments now would be reversing that decision at the site *next door* to it.

The one place `:` does mean name-to-*value* is the braced record literal,
`Monoid { unit: 0 }`. That is a real inconsistency, and it is one of the
reasons [[surface-records]] §6 already marks the braced form **provisional**.
§10.2 says what happens to it.

### 3.2 Why not `=`, and why `:=` is positively right

`f(a = x)` is unavailable, not merely ugly: `=` is the identity *type* former,
the one `=` this surface deliberately merged binding and equality onto
([[surface-syntax]]), so `f(a = x)` is already a legal call with one argument,
the proposition `a = x`. Choosing it would silently change the meaning of
existing programs. That is disqualifying on its own.

`:=` is the language's existing operator for **filling a named slot**:

| written | fills |
|---|---|
| `on ?bound := proof;` | a named goal |
| `instance … { op := Rat::add }` | a named instance field |
| `datarepr … { abs := f }` | a named repr clause |
| `hx: P := infer` | a named parameter, at its binder |
| **`f(x := e)`** | **a named parameter, at a call** |

The last two lines are the point: the binder's own default and the caller's
override are the *same* operator on the two sides of one slot, which is what
makes §9 a continuation of this design and not a second one.

### 3.3 The grammar

Inside a call's parentheses, an argument is **named** iff the next two tokens
are `IDENT` `:=`:

```
call-args    ::= arg-list? ','?
arg-list     ::= positional (',' positional)* (',' named)*
               | named (',' named)*
positional   ::= expr | op-symbol
named        ::= IDENT ':=' expr
```

Two tokens of fixed lookahead, no backtracking and no speculation — unlike
`try_tyargs`, which has to be speculative because `<` is also `lt`. Nothing
here is ambiguous with anything, by §2.2.

It applies at **every** call's parentheses, because they are all one function
(`call_args`): a plain call `f(…)`, an `@`-call, a `f<T>(…)` call, a method
call `x.f(…)`, and a constructor application. It does *not* apply to `<…>`
(§5.3), to a record literal's braces (§10.2), or to a pattern's binders
(§10.3).

The lone-operator argument (`Monoid(+)`, a designation reference) is
unaffected: it is checked before the named lookahead and an operator token is
not an `IDENT`.

## 4. Order

### 4.1 Written order is free; elaboration order is declaration order

`map(f := g, xs := ys)` and `map(xs := ys, f := g)` are the same call. The
named arguments are permuted into declaration order *before* any of them is
elaborated.

This is not a convenience; it is forced, and the issue was right to say the
constraint should be stated rather than discovered. **A later parameter's type
mentions an earlier parameter's argument** — that is what a Π telescope is —
so the spine has to be walked in declaration order no matter what order the
call was written in. `apply_implicit` in particular *depends* on it: an
argument's domain is `zonked` against the solutions learned from the arguments
before it, and a checking-only argument (`refl`, a `?`-hole, a bare lambda, a
vector literal) is only in checking position because the arguments before it
already solved its domain's metas.

So the honest statement of the rule is: **written order is free, evaluation
order is irrelevant (the language is pure), and elaboration order is the
declaration's.** One user-visible consequence, recorded so it is not filed as a
bug later: when two named arguments are both ill-typed, the one reported is the
one that comes first *in the declaration*, not the one written first. Each
error still carries its own written span, so it points where the user typed.

This is exactly the record literal's rule ("Field order in the literal is
free; it is normalized to declaration order before lowering",
`docs/surface-records.md` §6), which is the precedent §2.3 named.

### 4.2 Positional first, then named

A positional argument after a named one is refused, **in the parser**, with a
message that names the rule:

```
f(1, x := 2, 3)
      ~~~~~~   ^ a positional argument cannot follow a named one
```

Reason: a positional argument means "the next parameter with no argument yet",
and once free-order named arguments have already claimed parameters, "the next
one" is a rule the writer has to *compute* rather than read. Every language
that has both (Python, C#, Swift, Kotlin, Dart) draws the line here, and they
draw it in the same place for the same reason.

Putting it in the parser rather than the elaborator is deliberate: it makes the
rule a property of the *grammar*, so the AST cannot represent an interleaving
(§8.1), so no elaborator path has to decide what an interleaving would mean.

### 4.3 No gaps

After resolution, every parameter in the range this call is filling must have
either an argument or a meta. A named argument that skips an explicit
parameter therefore leaves a hole in the spine, and there is nothing to put in
it:

```heather
fn zip<A, B>(xs: List<A>, ys: List<B>) -> List<Pair<A, B>>
zip(ys := bs)      // refused: `xs` has no argument
```

The refusal is the existing "applied to too few arguments" message, extended to
name the parameter that has none — which it can now do, because in this
situation it knows exactly which one is missing rather than only how many are.

Note what this does *not* forbid: partial application through
`apply_explicit` is untouched, because a call with **no** named argument is not
resolved at all and reaches the same code with the same vector (§1's
invariant). Named arguments and partial application simply do not compose, and
that is stated rather than diagnosed obscurely.

## 5. Which parameters are nameable

### 5.1 Explicit parameters: yes, and it is the boring case

`map(xs := ys, f := g)`. Positional arguments fill explicit parameters in
declaration order as they do today; named arguments then fill by name; a
parameter filled both ways is "given twice" (§8.3).

### 5.2 `{}`-implicits and solver parameters: yes — this is the feature

`sym(p, a := x)` gives `a` and leaves `b` inferred. This is the issue's open
question 3, and the answer is the one it predicted: the `apply_implicit` mask
is a `&[bool]` with one entry per parameter, `true` meaning "mint a meta",
`false` meaning "consume the next written argument", and a named implicit is
**that bit flipped to `false`**, with the named argument spliced into the
argument vector at that position.

What makes this cheap is that the flipped slot then travels the *ordinary*
explicit-argument path inside `apply_implicit`, which already does the right
thing at every sub-case: the domain is `zonked` against the solutions learned
so far, a checking-only argument at a still-metaful domain is deferred and
retried, and an inferable one drives `unify_arg_ty`. A named implicit therefore
gets exactly the same treatment a positional one gets under `@`, which is the
treatment `at-and-type-arguments` already built and tested.

**Solver parameters** (`requires m: C<A>`, `p: T := infer`) are implicit with
a `solver` marker; naming one flips the same bit, and the effect is that the
slot is *not* minted as a `ResolveOb` at all — it is filled by the written
argument, so no search runs. That is strictly finer than today's `@f(…)`,
which is all-or-nothing over every value implicit, and it is the natural
spelling for "resolution picked the wrong instance, here is the one I mean".

Three states of one mask, as the issue predicted: `inferred` / `positional` /
`given-by-name`.

### 5.3 Type parameters: no, and `f<…>` is why

`map<A, B>(…)`'s `A` and `B` are leading implicits with `is_type` set, and they
are **not** nameable. `map(A := Nat, …)` is refused, naming `f<…>`.

The reason is not squeamishness about a third knob; it is that **a type
parameter's argument is a type, and this surface keeps type syntax and
expression syntax separate on purpose.** A `<…>` argument is parsed by `ty()`
and lowered by `elab_ty`; a named argument's payload is parsed by `expr()`. The
overlap is large but proper: `Nat`, `List<Nat>`, `Type<0>` and `a = b` read
both ways (`expr_as_ty`), while `[Nat; 3]`, `Nat -> Nat` and `Code(Δ |- T)`
have no expression spelling at all. So naming a type parameter is not "the same
feature with a name" — it is a *second reading* of the payload, available for
some types and not others.

And that second reading is one this codebase deliberately deleted. The
`at-and-type-arguments` round retired the "expression read as a type at `Ty l`"
coercion — its log entry says so in as many words: "the coercion is now DEAD —
no position has that expected type any more — so it was retired to a
diagnostic; it had existed only to paper over this collision." Reinstating it,
in the same round that finishes the job that killed it, would be a poor trade
for a knob that already has a spelling.

There is a real gain being given up: `<…>` is all-or-nothing, so *partial*
type application has no spelling. §10.1 files it, with the observation that its
answer is probably not a named argument at all but `f<_, Nat>`.

### 5.4 The receiver: no

A parameter marked `self` is filled by the *receiver* of a method call, and
naming it is refused with a message that says so and offers `e.f(…)`. This is
the same rule the parser already applies to solver defaults — "`self` cannot
have a solver default: its argument is the receiver, which is never omitted" —
applied at the other end of the same slot.

Note this is a refusal only in the `x.f(…)` spelling's *own* parameter: in the
plain-call spelling `f(x, a)` the subject is an ordinary positional parameter
and naming it is fine. The refusal fires when the receiver has already been
consumed, which is exactly when the slot is taken.

## 6. Constructors

`Cons(head := x, tail := xs)` and `Monoid(unit := 0, op := f, unit_l := p)`.

Constructor applications never go through `apply_explicit`/`apply_implicit`;
they go through `infer_ctor`/`build_ctor`, which take a positional
`args: &[Expr]`. So the resolution pass runs *earlier* for them — the named
arguments are permuted into field order and handed on as an ordinary positional
vector, and nothing downstream of the permutation learns that names were
written.

The name table is `Ctor.fields[k].0` (`Option<String>`), which is where the
record literal already reads it. Consequences worth stating:

- An **unnamed** field is not nameable, and the message says the constructor
  has unnamed fields rather than "unknown field". Positional-only constructors
  (`inductive Pair { P(A, B) }`) therefore keep working and gain nothing, which
  is right.
- The refusals — unknown name, duplicate, missing — are **the record
  literal's**, word for word, because they are the same function. That is the
  point of generalizing `record_lit_args` rather than writing a second
  permutation: `Monoid(unit := 0)` and `Monoid { unit: 0 }` cannot drift into
  disagreeing about what is missing.
- A constructor's **type parameters** are still not nameable (§5.3);
  `Cons<Nat>(head := 1, tail := xs)` is the spelling, and it already works
  (`ctor_at`).

## 7. Callees with no parameter names

`Type::Pi` carries no names — `Pi { dom_level, cod_level, dom, cod }`, de
Bruijn, full stop. This is the structural gap
[[implicit-binders-in-function-types]] documents for implicitness, and the
issue was right that it makes named arguments a two-tier rule. The decision is
to make the tiers **visible**, not to pretend they are not there:

- A **global** callee has a `ParamMeta` table with real names
  (`params_of`). Named arguments work.
- A **value** callee — a local, a `let`-alias, a projected record field —
  has a table synthesized from its *written* skeleton (`skel_params`), whose
  names are the binder names the writer typed, with `#i` for a binder that had
  none.
- A callee with **no** table at all (an arbitrary expression in head position)
  refuses named arguments.

The two refusals say different things, and both name the escape:

```
`#1` is not a name you can write: this callee's type is `Nat -> Nat`,
which binds no parameter names, so its arguments are positional. Write the
argument positionally, or annotate the binder — `(x: Nat) -> Nat`.
```

```
named arguments need a callee whose parameters have names, and this call's
head is an expression rather than a name. Write the arguments positionally.
```

The `#i` placeholder is unspellable by construction (no identifier starts with
`#`), so a synthesized name can never be *matched* by accident — the only way
to reach it is the message above, which is the property that makes tier two
safe rather than merely restricted.

**Corrected while implementing: tier two is narrower than this section first
claimed.** The draft said "`let g: (x: Nat) -> Nat = …; g(x := 3)` works".
It does not, and the reason is not this feature's. `skel_of_ty`
(`crates/elab/src/lib.rs`) is deliberately **sparse** — it returns a skeleton
only when the written type carries an *implicit mark* somewhere, because
`docs/implicit-binders-design.md` §3.1's storage rule is "existing
declarations store nothing new". A markless `(x: Nat) -> Nat` therefore stores
no skeleton, so a value at that type has no parameter table and no names, and
falls into the first message above rather than the third bullet.

So the real boundary of tier two is: **a value head is nameable exactly when
its written type carries an implicit mark.** `f: {A: Type<0>} -> (x: A) -> A`
is nameable and `f: (x: Nat) -> Nat` is not, which is a strange line to have to
explain and is filed as residue ([[implicit-binders-in-function-types]]'s own
territory: the fix is for `skel_of_ty` to store names whenever a binder *has*
one, not only when a mark is present). Both halves are tests, so the line
cannot move by accident.

**Amended 2026-08-20:** [[skel-of-ty-drops-binder-names]] closed that residue.
Tier two's boundary is now the one this section originally designed: a value
head is nameable exactly where its written type names binders. Thus
`f: (x: Nat) -> Nat` accepts `f(x := n)`, while anonymous `Nat -> Nat` remains
skeleton-less and positional. The two halves remain one regression test.

## 8. Representation, and the audit it forces

### 8.1 The AST

```rust
pub struct NamedArg { pub name: String, pub name_span: Span, pub expr: Expr }

App { head: Box<Expr>, args: Vec<Expr>, named: Vec<NamedArg>, explicit: bool }
Dot { recv: Box<Expr>, name: String, args: Option<Vec<Expr>>, named: Vec<NamedArg> }
```

A **separate list**, not `args: Vec<Arg>` with an optional name per element.
Three reasons, in order of weight:

1. **It makes §4.2 unrepresentable.** Positional-then-named is the grammar, so
   the AST that mirrors the grammar cannot hold an interleaving, and no
   elaborator path has to decide what one would mean. A `Vec<Arg>` would have
   to re-check the ordering rule everywhere it is read, or trust that the
   parser checked it.
2. **`args` keeps its meaning at ~35 existing match sites.** `args.len()` is
   still the positional arity every fragment recognizer keys on
   (`reprgen`, `datarepr`, `certgen`, `forded`, `traits`, `quote`), and none of
   them has to change to stay *correct* — a call with named arguments has a
   different positional arity, so a recognizer expecting `n` positional
   arguments declines it, which is the safe direction.
3. Named arguments are a **small** minority of arguments in real code, and a
   `Vec<Option<String>>` parallel to `args` — the third option — is the one
   representation that can desync.

### 8.2 The audit the field forces, and the one it does not

Adding a field makes every **construction** site a compile error, so all of
those are audited by the compiler: the parser's call arm, `named_call`,
`op_call`, the `Dot` arm, and every synthetic `App` the elaborator builds
(`calc`'s `@trans`, the operator desugarings, the generators).

It does **not** force the ~35 `App { head, args, .. }` *reading* sites, and
that is the one real cost of this representation. Those are audited by hand in
the implementing round, and the finding is recorded in §12: each is a shape
recognizer that keys on positional arity, so a named argument makes the shape
not match and the recognizer declines. Two classes get an explicit
`named.is_empty()` conjunct anyway, because arity alone does not protect them:
a recognizer that matches on **zero** positional arguments
(`is_naive_call`-style, where `repr::naive(x := 1)` has zero positional
arguments and would be read as `repr::naive()`), and `Expr::as_named`, whose
whole job is to hand a callee's argument slice to a name-keyed special form.

`Expr::as_named` is the important one: it returns `(&str, &[Expr], bool)` and
is the accessor *every* builtin uses (`Succ`, `Fin`, `cong`, `inj`, `absurd`,
`map`/`fold`, …). Those builtins have no `ParamMeta` table — they are
elaborator arms, not declarations — so they have no names to be called by, and
a named argument at one must be refused rather than dropped. It is refused
centrally, at the top of the named-head application arm, with the §7 message.

### 8.3 The resolution pass

One function, run before both spine walkers and before the constructor path:

```
resolve_named(callee, value_head, params, param_offset, mask, args, named, span)
    -> R<Option<(Vec<Expr>, Vec<bool>)>>
```

Returns the full argument vector in declaration order and the adjusted mask —
and `None`, cloning nothing, when `named` is empty, which is §1's invariant
made mechanical rather than promised. (`Option` rather than an eager clone
because an `Expr` clone is *deep*, and this sits on the application path.)
`resolve_named_ctor` is the constructor twin, with the same `None` discipline
for the same reason plus one more: the permutation demands saturation, so
running it unconditionally would break partial constructor application.

Its refusals, each spanned at the *written name*:

| written | message names |
|---|---|
| a name no parameter has | the callee's nameable parameters, in declaration order |
| a type parameter | `f<…>` (§5.3) |
| the receiver | `e.f(…)` (§5.4) |
| a parameter already given positionally | "given twice", both spans |
| the same name twice | "given twice", both spans |
| a name past the parameters this call fills | that it is over-application, which has no names (§4.3) |
| a name at a callee with no names | §7's two messages |

Every one of them names the **written** form — the identifier the user typed
and `:=`, never "argument 3" and never the desugared spelling. That is
[[diagnostics-name-the-written-form]]'s standing rule, applied here at the
outset rather than paid for twice.

## 9. Defaults at binders — the shape, pinned, and staged

[[true-prop-trivial-hypotheses]] re-homed its half 2 here: default argument
values declared at the binder, ratified by the user 2026-08-16 as the mechanism
for discharging definitionally-trivial hypotheses, and wanted as a general tool
besides — "including defaults that run a tactic search over the surrounding
context, not just a stored term."

This round does **not** implement it. It does settle everything about it that
named arguments settle, which is most of the surface and none of the hard part.

### 9.1 The slot, and it is not a new one

```heather
fn refines(r: R, h0: True := trivial) -> …
```

`p: T := e` — the binder position that today accepts exactly one thing,
`:= infer`. The parser's own comment there says "Unambiguous here: nothing else
follows a parameter's type with `:=`", which is as true of an expression as it
is of `infer`. So the grammar change is: after `:=`, `infer` stays the solver
keyword and **anything else is an expression default**. `infer` is not
shadowable into meaning something else, which is the one wart, and it is the
wart `:= infer` already has.

### 9.2 A defaulted parameter has no positional slot

This is the decision that makes defaults compose with everything already built,
and it is taken straight from the solver parameter next door: `implicit = true`
(`crates/syntax/src/parser.rs`, "A solver parameter has no positional slot: it
is implicit, and `@f(…)` is how it is passed by hand").

A defaulted parameter is therefore **implicit, filled from its default** rather
than by unification (`{}`) or by search (`:= infer`) — a fourth state of the
same slot. Consequences, all of them good:

- **The partial-application ambiguity never arises.** If a defaulted parameter
  kept a positional slot, `f(1)` at `fn f(a: Nat, b: Nat := 0)` would be
  ambiguous between `f(1, 0) : Nat` and the function value `Nat -> Nat`, and
  every language that has both defaults and currying has had to pick. Here the
  question is not asked: the positional arity of `f` is 1, both before and
  after `b` gains a default.
- **Adding a default is backwards-compatible**, for the same reason: no call
  site's positional arity changes.
- **Named arguments are the override**, with no new syntax:
  `f(1, b := 7)`. That is why the two halves are one design — §3.2's table has
  the binder and the call site on the two sides of one `:=`.
- **`@f(…)` still passes it by hand positionally**, exactly as it does a
  solver parameter, so the escape hatch exists before the feature ships.
- **Generators keep passing explicitly.** The ratified uniform-registry shape
  from [[true-prop-trivial-hypotheses]] survives untouched: the binder is still
  in the signature, so every consumer still handles one shape, and omission is
  substitution rather than a change of statement.

### 9.3 Where it lands in the elaborator

`ParamMeta` gains `default: Option<Rc<Expr>>` beside `solver`. In
`apply_implicit`'s mask loop, a defaulted parameter mints its meta and marks
the slot `Sol::Withheld`, pushing a `DefaultOb { slot, dom, dom_level, param,
expr }` — structurally the `ResolveOb` next to it. The existing
retry-to-fixpoint loop discharges it: once `zonked(dom)` is `Some`, the default
is *checked* against that domain and the slot becomes `Sol::Solved`. Ordering
within the loop is defaults **after** resolutions and **before** deferred
arguments, because a default may mention a resolved dictionary and a deferred
argument's domain may mention a default's value.

A named argument at a defaulted parameter flips the mask bit (§5.2) before any
of that runs, so the `DefaultOb` is never created — the override costs nothing
and cannot race the default.

### 9.4 What is *not* settled, and why it is a round of its own

**Where a default's free names resolve.** A default is written in the
declaration's telescope and consumed at a call site, and those are two
different contexts:

```heather
fn f(n: Nat, k: Nat := n) -> …      // mentions an earlier parameter
fn g(h: True := trivial) -> …       // mentions only a global
```

Two mechanisms, and the choice between them is the work:

1. **Lower once, at the declaration, in the telescope prefix; instantiate at
   the call.** Correct for both examples, and the only mechanism that can ever
   support `:= n`. Cost: the default becomes a kernel term open in the
   declaration's first `i` locals, which has to be stored on the declaration
   and substituted with the arguments already applied at the call — the same
   shape a Π's codomain is instantiated with, but the elaborator has no path
   that does it for a *stored surface default* today.
2. **Splice the surface expression into the call and elaborate it there.**
   Trivial to build, and it is what `written_clauses`'s omission default
   already does one layer up. But it resolves the default's names in the
   *caller's* scope, so a caller with a local named `trivial` silently changes
   what `g`'s default means. That is dynamic scoping, and it is a lie of
   exactly the kind this codebase files as a defect rather than documents.

Mechanism 1 is the one to build. It is staged rather than rushed because it is
a genuine elaborator question — a stored open term and its instantiation —
rather than a permutation, and because the first customer (`h0: True :=
trivial`) does not need `:= n` and would tempt mechanism 2 into looking
sufficient. The user's further want, *defaults that run a tactic search over
the surrounding context*, is mechanism 1 with the stored term replaced by a
stored **goal**, which is another reason not to build the version that cannot
grow into it.

Also unsettled, and belonging to that round: whether a default may mention a
**later** parameter (no: the telescope is ordered), and whether a defaulted
parameter may also be `{}`-implicit (no: it is already implicit, and two
filling disciplines on one slot is the error `:= infer` already refuses).

### 9.5 As landed for record fields (2026-10-01)

Record **fields** came first, not parameters
(docs/automatic-author-surface-design.md §2.3): `name: T := e` on a record's
field. §9.2 holds as written. A defaulted field has no positional slot, so
the other fields fill positionally in order, and a named argument overrides
it; writing every field positionally also overrides it. §9.4 is answered for
fields as it says it must be:

- the default is stored on the constructor and checked at the field's type
  as each construction instantiates it (the stored goal);
- names resolve in the record's declaring scope, and none of the
  construction's locals are visible to it.

One restriction remained: a default ran only where the construction had no
local bindings (issues/field-defaults-under-locals.md). §9.6 lifted it.

### 9.6 As landed for parameters (2026-10-12)

```heather
fn second(a: Nat, b: Nat := seven()) -> Nat { b }
theorem divides(n: Nat, h: 0 < n := omega): 0 < n { h }

second(1)                 // second(1, b := seven())
second(1, b := 2)         // the override
divides(k)                // omega, over the caller's hypotheses about k
```

§9.1 and §9.2 hold as written: after `:=`, `infer` is the solver and any
other expression is a default, and a defaulted parameter is implicit with no
positional slot. A default is refused on a `{}`-implicit and on `self`.

**The mechanism is a named argument, not a `DefaultOb`.** §9.3 planned a
fourth obligation beside `ResolveOb`. What landed is smaller:
`resolve_named` fills each omitted defaulted parameter with an internal
marker (`application::PARAM_DEFAULT`, carrying the declaring global's key and
the parameter's index) and flips its mask bit. From there it is a named
argument the caller did not write. The spine walkers check it at the
parameter's domain with the earlier arguments substituted, in declaration
order, and defer it, since the marker is checking-only, until that domain has
no unsolved metas. The ordering §9.3 wanted (after resolutions, before
deferred arguments that depend on it) falls out of the existing
retry-to-fixpoint loop. A call that names nothing and leaves no default takes
the path it took before, cloning nothing.

**§9.4, answered.** Neither mechanism as described. A default is checked:

- against the call's instantiated domain, which is open in the caller's
  locals, so it is checked in the caller's context;
- with that context made **hygienic** (`Cx::hygienic`): each local and alias
  is renamed to a reserved `__caller_<name>` spelling, and the name-keyed
  scaffolding (dictionaries, operator symbols, the self-reference) is
  dropped;
- with names resolving in the declaration's scope, which `ParamMeta` stores
  beside the default.

So `h: True := trivial` means the declaring module's `trivial` even when the
caller has a local `trivial`, and `h: 0 < n := omega` or `:= positivity`
searches the caller's hypotheses, which a tactic reads by type. This is the
"default that runs a tactic search over the surrounding context" the user
asked for (2026-08-16), with no dynamic scoping. The renamed locals stay
*source* spellings, because `omega` reconstructs its certificate as source.
The `__` prefix is the same reserved spelling `omega`'s own renaming uses.

Record fields use the same check, so a field default now runs under local
bindings too.

**A default may mention the parameters before it** (`k: Nat := n`,
2026-10-12). In the hygienic context the caller's locals are out of reach,
so a parameter's name is bound to something else: the call's argument for
it, pushed as an alias (the `let` mechanism, a kernel term inlined at each
use) by `defaults::elab_param_default`. The default's term is therefore the
one it would be with the arguments written in, and `fn f(n: Nat, k: Nat :=
n)` makes `f(3)` the term `f(3, k := 3)`. A caller's own `n` is still
`__caller_n`, so it cannot be what the default reads.

The arguments come from the spine walkers, which keep the call's arguments
so far, with their instantiated domains, only when the call leaves a default
to fill (`application::EarlierArg`). In `apply_implicit` they are scratch-world
terms, so a default waits, as a deferred argument does, until the earlier
arguments it mentions are solved as well as its domain: an implicit learned
from a later argument or the expected type, or an earlier default not yet
filled. Which parameters a default mentions is read off its syntax at the
call (`defaults::mentioned_parameters`), so the module image is unchanged.

The declaration refuses a default that mentions its own parameter or a later
one (the telescope is ordered, §9.4), and one that mentions a type parameter,
which no alias can bind
(issues/parameter-defaults-mention-type-parameters.md).

**What a default cannot do yet**, each with an owner:

- **Mention a type parameter** (`xs: List<A> := Nil<A>`); see above.
- **Fail at the call when only the kernel sees it.** A `refl` default whose
  endpoints differ at some call is reported at the declaration
  (issues/default-kernel-failure-reported-at-declaration.md). An elaboration
  failure is reported at the call, naming the parameter and `name := …`.
  Since §9.7 a *value* default's kernel-only failure that holds at every call
  is the declaration's own error and is reported there, correctly; the issue
  keeps the discharges and the second-reading values whose fit fails at a
  call.

**A bare reference is the whole function.** `apply(second)` passes
`Nat -> Nat -> Nat`: a default fills at a call, as a solver parameter does,
and `λ a => second(a)` is the spelling that fills it.

### 9.7 Checked where it is written (2026-10-23)

§9.6 checks a default at each call that leaves it out, and nowhere else, so
a default no call uses was checked by nobody
(issues/parameter-default-unchecked-at-declaration.md, the sibling of
issues/unused-let-value-unchecked.md):

```heather
record P { a: Nat, h: a = 3 }
fn g(x: Nat := P(2, refl).a) -> Nat { x }   // was accepted; refused now
```

It cannot simply be checked at the declaration as a term of its parameter's
type, Lean's `optParam` rule, because two kinds of default are in use whose
meaning is per call:

- `h: 0 < n := omega` (and `:= positivity`) proves the call's goal from the
  *caller's* hypotheses. In the telescope alone `0 < n` does not hold.
- `nan: F.specials.has_nan().IsTrue() := trivial` (lib's `Float::div`) and
  `zero: IsZero(n) := Holds` fit the calls whose arguments make the goal
  compute to `True`/`Yes`, which is
  [[true-prop-trivial-hypotheses]]' reason for defaults: discharging a
  hypothesis that is definitionally trivial *at the call*.

So a default is checked at the declaration exactly as far as the
declaration decides it, and the rest stays the call's
(`Elaborator::check_default_at_declaration`, `crates/elab/src/defaults.rs`):

**A discharge is the call's.** A default whose head is a goal-reading form —
`omega`, `positivity`, `ring`, `bv_omega`, `decide`, `rel_cong`/`rel_derive`,
`rewrite`, `subst`, `by t`, `refl` — or that contains a goal `?` has no
meaning apart from the goal a call poses and the hypotheses it has, as
`:= infer` has none. It is not elaborated at the declaration.
(`defaults::is_discharge`; it reads the head only, so `mk(omega)` is a value.
`trivial` is a value: it has a type of its own, `True`.)

**A value is a term, and the kernel judges it at the declaration.** It is
elaborated in the declaration's telescope — the parameters before it bound
as binders, names resolving in the declaring scope, as at every call — and
the result goes to the kernel there, so `P(2, refl)`'s `refl` is refused at
`g`'s declaration with no call in sight. Two readings, in order:

1. **At the parameter's type.** The ordinary case: `NearestEven`, `seven()`,
   `n`, `λ y => y` at `A → A`. A default that checks here checks at every
   call, since a call substitutes arguments for binders.
2. **At a type of its own**, when the first reading fails. Accepted when the
   default checks at the type it synthesizes *and* a call could still change
   whether that type is the parameter's: when either type mentions an
   earlier parameter. `zero: IsZero(n) := Holds` is a well-typed `Yes`, and
   `IsZero(n)` is `Yes` at the calls with `n` zero, so it stays legal and a
   misfit stays the call's error (§9.6). `b: Bool := 5` is a `Nat` where
   every call wants a `Bool`, and is refused here. When the second reading
   elaborates but the kernel refuses it (`Holds(refl)` at a `Holds(p: 2 = 3)`),
   that refusal is the one reported: it is about the default itself, not its
   fit.

This answers the issue's open question — *a default that only typechecks at
some instantiations* — as: legal when its own term is well-typed and its fit
is the instantiations' business, refused when its own term is ill-typed or
its fit is decided and wrong.

The attempt leaves nothing behind: its goals, checking notes, warnings and
dependency edges roll back (`resolve::SearchMark`), because the default's
term belongs to each call's term and never to the declaration's. A tactic
inside a value (`need(3, omega)`) therefore runs twice, once in the
telescope and once at each call (its atom slots are reserved with the
declaration's, `surface::count_tactic_slots`). The call still re-elaborates
the default rather than instantiating the declaration's term — §9.4's
mechanism 1 — so the declaration check is a check, not a lowering; storing
the term would also let a value default mention a type parameter
(issues/parameter-defaults-mention-type-parameters.md).

Record field defaults (§9.5) are checked only at a construction still
(issues/field-default-unchecked-at-declaration.md).

## 10. Out of scope, with homes

### 10.1 Partial type application

`f<…>` is all-or-nothing: `psym<Nat>(n, m, p)` needs every type argument
written. §5.3 declines to fix this with names. The likelier answer is a **hole
in the type-argument list** — `zip<_, Nat>(xs)` — which stays inside type
syntax, needs no expression-as-type reading, and composes with `f<…>` as it
stands. Filed as residue.

### 10.2 The braced record literal is not retired here

[[surface-records]] §6 marks `Monoid { unit: 0 }` provisional and says named
arguments would make it redundant, deleting §6.1's whole ambiguity class (the
`no_record_lit` suppression flag, and the standing hazard that every future
block-preceding construct has to remember it). §6 of *this* document makes the
successor spelling real: `Monoid(unit := 0, op := f)`.

Retiring the braced form is nonetheless a separate decision and a separate
round, for a reason worth stating: it is a **migration**, not a feature. Every
braced literal in `lib/`, in the fixtures and in the tests has to move, the
`no_record_lit` flag and its ten set-sites have to come out, and §6.1's
parenthesis rule and its tests have to be deleted rather than adapted. Bundling
that into the round that *introduces* the successor would put a sweep on top of
a new feature and make a bisect over either of them useless.

The criterion for that round, stated so it is not re-argued: the braced form
goes when `Monoid(unit := 0, …)` has shipped, been used in `lib/`, and the
`⟨…⟩` anonymous literal question (also deferred in §6) has an answer — because
if `⟨…⟩` lands, `{ … }` loses its second customer too and the two retirements
are one edit.

### 10.3 Patterns by name

`Cons(head, tail)` as a *pattern* naming fields rather than binding them
positionally is the issue's open question 4, and [[surface-records]] owns the
matching half. It is out of scope here for a reason that is not scheduling: a
pattern's `Cons(x, y)` **binds** `x` and `y`, it does not fill them, so `:=`
would be pointing the wrong way and the spelling would have to be something
else (`Cons(head: h, tail: t)`, i.e. field-to-binder). That is a different
grammar with a different collision surface, and it should be decided with
records rather than inherited from calls.

### 10.4 Trait and record *interfaces*

The issue's Rust-obstacle 1: an `impl` may name its parameters differently from
the trait declaration, so which names a caller at a generic type may use is
genuinely ambiguous. Nothing here answers it, and nothing here needs to —
today's callees are declarations and records of concrete functions, and
`params_of`/`skel_params` name exactly one thing in each case. It becomes live
with [[compile-typeclass-design]] / [[operation-indexed-classes]], and the
answer should be decided **with** that round, which is what the issue already
says. Recorded here only so that round finds the constraint: §7's tiering means
a class member reached through a dictionary is a *projection*, so it takes the
skeleton path, so the names a caller may write are the ones on the **class
declaration's** member type — which is the answer Rust could not have, because
it has no such type to hang them on.

## 11. Acceptance list

Per `docs/testing-generated-terms.md`: positive **and** negative, an open type,
a checking position, and a control that would pass if the feature were
hardcoded.

**All met**, in `crates/elab/tests/named_arguments.rs` (21) and four grammar
tests in `crates/syntax/src/parser.rs`'s own module, plus `calc`'s two fold
tests re-spelled (§12.7). Item 14 was met by *refusing*
rather than by supporting — §5.3 — and item 17's positive twin moved to the
narrower boundary §7's correction paragraph records. One test the list did not
ask for was added while implementing and is the sharpest of the lot: a `?`-hole
inside a named argument, raised and discharged by `on ?q := …` (§12, finding
6).

1. **Explicit parameters, reordered.** `map(xs := ys, f := g)` and
   `map(f := g, xs := ys)` both check and produce the *same term* as
   `map(g, ys)`. The term equality is the assertion, not merely that both
   check — a permutation that got the order wrong would still typecheck at
   `map`'s two same-shaped parameters if the element types agreed, so the test
   uses parameters whose types differ.
2. **Mixed.** `f(a, b := e)` — positional prefix, named suffix.
3. **An implicit, given by name.** `sym(p, a := x)` at a polymorphic `sym`:
   `a` is pinned, `b` is still inferred, and the result type shows it.
4. **A solver parameter, given by name** — the written dictionary is used and
   no search runs (asserted by giving a *non-default* instance and checking the
   result).
5. **A checking-position argument, by name.** A named argument that is
   checking-only (`refl`, a `?`-hole, a bare lambda) at a parameter whose
   domain is solved by an *earlier* argument — the §4.1 rule under load. This
   is the axis-3 test and it is the one that would catch a permutation done
   after elaboration rather than before.
6. **An open element type.** Every one of the above at a parameter whose type
   mentions an ambient variable, not only at `Nat` (axis 2).
7. **Constructors.** `Cons(head := 1, tail := xs)` equals `Cons(1, xs)`; a
   record constructor `Monoid(unit := 0, op := f)` equals both `Monoid(0, f)`
   and `Monoid { unit: 0, op: f }`.
8. **Method calls.** `p.trans(c := z, q := r)`.
9. **`@` and `<…>` compose.** `@f<Nat>(a, b := e)`.
10. Negative: **unknown name**, and the message lists the real parameters.
11. Negative: **duplicate name**.
12. Negative: **given twice**, positionally and by name.
13. Negative: **positional after named** — a *parse* error (§4.2), asserted as
    such and not as an elaboration error.
14. Negative: **a type parameter by name**, and the message says `f<…>`.
15. Negative: **the receiver by name** in a method call, and the message says
    `e.f(…)`.
16. Negative: **a gap** — a named argument that skips an explicit parameter
    (§4.3), naming the parameter with no argument.
17. Negative: **a value callee with no binder names**, with §7's message; and
    the **positive** twin, a value callee whose skeleton *does* have names.
18. Negative: **a builtin by name** (`Succ(n := 1)`) — §8.2's central refusal.
19. **The control**: a call with no named arguments, at each of the shapes
    above, still elaborates to the term it did before. Without this, a
    permutation that silently reordered *positional* arguments would pass
    every test above.
20. **`lib/` still checks**, and the adoption sites of §12 check.

## 12. What implementing this corrected

Seven corrections, all found by doing it rather than by reading. Three change
the design above; four are findings about the codebase that the design had no
way to predict.

**1. Tier two is narrower than §7 claimed** — see §7's own correction
paragraph. A value head is nameable exactly when its written type carries an
implicit mark, because `skel_of_ty` is sparse by design. Residue filed.

**2. §5.4 named the wrong half of the method-call interaction.** The draft
worried about naming the receiver's parameter, which is a "given twice" and
takes care of itself. The real interaction is *positional*: `resolve_dot`
splices the receiver into the argument list at `subject_index(name)`, which is
an index among the **written** arguments. Naming an argument removes it from
that list, so a call that names a parameter *before* the subject would place
the receiver one slot early and silently mean a different call. It is refused,
with its own message naming the parameter number and offering the plain call.
Rare — `self` is only written where the subject is not first (`cong`) — but it
is a wrong-term bug, not a diagnostic wart, and nothing in the design had seen
it.

**3. Self-calls refuse named arguments, and the reason is the termination
guard.** Not scoping, not the parameter table (a `SelfRef` has names): the
guard analysis walks the body AST looking for which argument *position*
decreases. A named self-call would either have to be normalized before that
walk or make the walk name-aware, and both are a correctness surface on the
termination checker rather than an ergonomics change. Refused at both self-call
sites — the plain one and the `map<A, B>(…)` type-argument one — with a message
that says the position is what is being read.

**4. The over-application check has to run *after* the name lookups.** It ran
before, in the first draft, and that made every named argument at a callee with
no parameter table report an arity problem: with `params` empty the mask is
empty, so every positional argument is "past the end" vacuously, and §7's
message about names never fired. Moved, with the reason in a comment.

**5. `resolve_named_ctor` must be a no-op when nothing is named.** The
permutation demands saturation (it must, by §4.3), and running it
unconditionally broke *partial* constructor application — `Cons(1)`
η-expanded against an expected Π, `docs/constructor-function-values.md`. Both
constructor entry points now return `None` and clone nothing when no name was
written, which is §1's invariant made mechanical at a second site.

**6. The §8.2 audit found more than §8.2 predicted, and the two most
dangerous were not on its list.** The prediction was `is_naive_call`-style
zero-argument recognizers, and that one was real (`repr::naive(x := 1)` would
have read as `repr::naive()`). The two it missed are both *walkers*, where
dropping a subterm is silent by construction:

- the **goal pre-count** (`crates/elab/src/lib.rs`), whose own doc comment says
  it is the one thing the goal mechanism cannot survive under-counting — a
  `?hole` inside a named argument would have been uncounted;
- **`scan_splices`** (`crates/elab/src/quote.rs`) — a `$u` inside a named
  argument inside a quotation, which is the quotation-payload interaction §1
  listed and did not resolve.

Seven more traversals were threaded for the same reason and none of them was a
judgement call: `walk_expr` (self-call depth), `expr_mentions` in `inductive`
and in `traits`, `mentions_free` in `datarepr`, `walk` and
`vars_outside_self_calls` in `reprgen`, and `expr_size`/`expr_var_count` (the
Paterson measures over an applied carrier). The remaining ~20 reading sites are
fixed-arity shape recognizers and were left alone deliberately: a call carrying
names has a different positional arity, so they decline, which is the safe
direction and is what §8.2's second reason predicted correctly.

Two **renderers** also had to choose, and they chose oppositely, which is
right: `traits::render_expr` (a diagnostic display) now renders `x := e`
as written, per [[diagnostics-name-the-written-form]]; `datarepr::spell_expr`
(whose output is *re-parsed* as generated source) **declines**, because a
permutation that resolves at one callee need not resolve at another.

**7. `calc`'s `@trans` is retired, and a shipped test was changed on
purpose.** `calc { a = b := p1, = c := p2 }` now emits
`trans(p1, p2, a := a, b := b, c := c)`. `@` forced every value implicit
positionally, so a *parser* desugaring encoded how many implicits `trans` has
and in what order — a property of a library declaration. The issue records that
this desugaring "has now been fragile twice"; naming the endpoints makes it
depend only on what they are *called*, which `ParamMeta` already treats as API.
`calc_multi_step_nests_explicit_trans` became
`calc_multi_step_pins_the_endpoints_by_name`, and its doc comment says why the
old assertion was deliberately abandoned rather than broken.

### 12.1 Adoption in `lib/`, and what it did not find

Sparing, as intended, and the survey is the more interesting half: **there are
no `@`-spelled calls left in `lib/` at all** (the 2026-08-17
argument-type-reduction round removed the last of them) and **no braced record
literals** either. So the two payoffs the issue advertised for the library —
finer `@` overrides, and the record-literal ambiguity — have no library sites
to be paid at today; the `@` payoff was paid at `calc` instead (§12.7), and the
literal one is §10.2's future round.

What the library *did* have is the case neither the issue nor §6 named: a
record whose two fields have the **same type**, where a transposition
typechecks. Six sites, all `Iff` and `And` in `lib/std`:
`and_swap`, `iff_refl`, `iff_sym`, `iff_trans` (`logic.hthr`),
`lt_succ_iff_le`, `le_iff_exists_add` (`nat.hthr`), `mem_append_iff`
(`list.hthr`). `iff_refl`'s `Iff<P, P>` is the sharpest: both fields are
`P -> P`, so *no* type error could catch a swap, and until now nothing but
position said which lambda was `mp`.
