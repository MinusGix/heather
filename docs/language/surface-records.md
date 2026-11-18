# Records: named-field Σ sugar, and field access as a real operation

Status: **scheme**, written before the code per the discipline of
`docs/language/surface-polymorphism.md`, `docs/language/surface-function-types.md` and
`docs/kernel/wf-former-design.md`. §10 is the acceptance checklist; §11 is reserved
for what implementing this corrects.

Tracking issue: `issues/surface-records.md` (roadmap item 12).

The **encoding side is already done**. A record is a one-constructor tier-0
inductive, and `docs/inductives/inductive-tier0-lowering.md` already says so: §1 lists
records as tier-0 content, §3.2 notes that `n = 1` collapses to the field
spine with no tag spine ("which is the right answer for structs"), and §9's
acceptance item 6 already pins the `n = 1` case round-tripping. No new
generator, no kernel change, no ch. 07 obligation — the same risk class as the
last three rounds.

What is *not* already done, and is the real content of this round, is **field
access**. `.` is currently a parser desugaring that turns `p.f(a)` into a call
to a **global** `f` with the receiver appended last (`parser.rs:571–596`; the
receiver's position has since become the callee's business,
`issues/method-receiver-position.md`), and
`p.f` with no parentheses does not parse at all. A record of functions — which
is what a trait, an algebraic structure, a `Compile` instance and an
optimization-pass interface all are — needs `m.op(x, y)` to mean
`(m.op)(x, y)`. So this round moves `.` out of the parser and into the
elaborator, where it can be resolved against the receiver's type. That is a
change to landed behaviour (`surface-operators`), and it is the part to review
hardest.

---

## 1. What the surface gains

```
item    := … | record
record  := "record" name tyvars? valparams? "{" field ("," field)* ","? "}"
field   := name ":" type
valparams := "(" name ":" type ("," name ":" type)* ","? ")"   -- see §1.2

type    := … (a record with no value parameters is a `TyKind::Named`; one with
              them is written applied — `Converges(p, env, ir, vs)` — and
              reaches the elaborator as `TyKind::OfExpr`)

expr    := … | record_lit | expr "." name
record_lit := name tyargs? "{" (name ":" expr) ("," …)* ","? "}"

stmt    := … | "let" "{" name ("," name)* ","? "}" "=" expr ";"
```

```heather
record Monoid<A> {
  unit: A,
  op: A -> A -> A,
  unit_l: (x: A) -> op(unit, x) = x,
}

fn nat_add_monoid() -> Monoid<Nat> {
  Monoid { unit: 0, op: λ (x: Nat) => λ (y: Nat) => add(x, y), unit_l: … }
}

fn twice<A>(m: Monoid<A>, x: A) -> A { m.op(x, x) }
```

Three things to notice, each a section below:

- Fields are **named and in scope in the later fields' types** — `unit_l`
  mentions `unit` and `op`. This is not new: `FieldDecl` already carries a
  name and the Σ spine already makes it dependent (`ast.rs:63`,
  tier-0 §3.1). It is why the spine is a Σ and not a product.
- The literal is **braced and named**, not positional (§6).
- `m.op(x, x)` is a projection applied to arguments, *not* a call to a global
  `op` (§4).

### 1.2 Value parameters (added 2026-08-01)

`record R(p: T, …)`, after the `<…>` if there is one, adds **value**
parameters: terms the use site supplies, substituted into the field types at
lowering. That is what makes a record usable as a *predicate* —

```heather
record Converges(p: Prog, env: Val, ir: Ir, vs: Val) {
    n: Nat,
    h: eval(n, p)(env, ir) = Out(vs),
}
```

— i.e. the value-indexed Σ `issues/surface-existential.md` was filed for. The
grammar, the substitution rule, the checking-position-only construction
decision, and the parameters-vs-indices line are all in
**`docs/language/surface-value-parameters.md`**; nothing in the sections below changed to
accommodate it (projection, `let { }`, match arms and the level fold are all
indifferent to where a type in the spine came from).

### 1.3 A record in a type's namespace (added 2026-11-18)

A record whose value parameters start with the thing it is a claim about
can be declared in that thing's type's namespace, as a `fn Target::m` is
(`issues/record-in-type-namespace.md`):

```heather
record Target::Held(self t: Target, live: List<Nat>, env: Env) {
    words: List<Nat>,
    placed: t.Placed(env.with_words(words)),
}
```

- **Spellings.** `t.Held(live, env)` and `Target::Held(t, live, env)` are
  one type; `Held` alone is not in the ambient namespace. A construction
  names the record by its whole name, `Target::Held(words := …, placed :=
  …)`, or leaves it to the expected type; fields are read as on any record
  (`held.placed`).
- **The method spelling is always the type.** `t.Held(…)`'s arguments are
  the record's value parameters, so the call is the type former even where a
  bare `Target::Held(…)` would read as the constructor (an inference
  position). `Dot` resolution writes it as a type literal
  (`dispatch/member.rs`).
- **`self`** may mark the first value parameter and only that one: a method
  call puts its receiver in the first positional argument of a record's type,
  and a record keeps no parameter metadata for a later position to be read
  from. Unmarked, the first parameter is still the receiver, as at a `fn`.
- **The owner is checked**, as at a `fn` member: it must name a type or a
  type former in scope (`elab_inductive_members`). One qualifier only; an
  `inductive` or `enum` still declares no qualified name, since no use asked
  for one.
- **Images carry nothing new.** The receiver route needs the base name in
  the member table (`names::insert_current`), and it is read off the
  inductive's name when its name event is recorded or replayed.

### 1.1 Type parameters are monomorphized, like an `inductive`'s

`record Monoid<A>` follows `InductiveDecl`, not `Decl`: `A` is a surface
parameter substituted through the lowering per instantiation, not a kernel
`Π(A : Ty 0)` binder. `Monoid<Nat>` and `Monoid<Bool>` are unrelated kernel
types.

This is exactly the asymmetry `docs/language/surface-polymorphism.md` §3.1 settled, and
it is load-bearing here rather than incidental. The reason `record` waits on
polymorphism is that every interesting record is generic in its carrier — and
what makes that work is that an instantiation may be **open**: inside
`fn twice<A>(m: Monoid<A>, …)`, the parameter type `Monoid<A>` lowers to
`⟦Monoid<El A>⟧`, an ordinary kernel type with `A` free. That is the same
mechanism that let `map` return a `List<B>`, and it needs no generator change
here either.

## 2. `record` is a surface form over one internal path

**Decision.** `record` is its own keyword and its own parse, and desugars
immediately to the existing `InductiveDecl` with a single constructor, plus a
**field table**. The generator (`crates/elab/src/inductive.rs`) sees nothing
new.

The issue frames this as a fork — distinct declaration form *or* one-
constructor inductive with accessor sugar — but those answer different
questions. The lowering must be the inductive one: a second generator is the
thing that goes stale, and the tier-0 generator is the most-reviewed code in
the repo. The surface must be distinct, because three things a bare
one-constructor `inductive` cannot do:

1. **Reject recursion at the declaration, pointing at `inductive`.** Tier
   classification (tier-0 §2) already computes this; a `record` whose fields
   mention itself is a surface error with the occurrence located and the
   message naming `inductive`. A record is by construction tier 0.
2. **Expose the fields outside a `match` arm.** An inductive's field names are
   in scope only in later field types and in an arm's binders. A record's
   names become *accessors*, which is a name→offset table on the
   declaration — a property of the declaration, not of the encoding.
3. **Name the literal after the type.** `Monoid { … }` has no separate
   constructor name to write.

### 2.1 The generated constructor

The single constructor is named after the record. So `record Monoid<A> {…}`
desugars to

```
inductive Monoid<A> { Monoid(unit: A, op: A -> A -> A, unit_l: …) }
```

and everything an inductive gets comes free: `Monoid(…)` positional
construction, `match m { Monoid(u, o, l) => … }`, constructor-as-function-value
(`docs/language/constructor-function-values.md`), and the tier-0 derived lemmas.

**The nominal tag stays.** Tier-0 §3.3 prefixes every constructor's field
spine with `Tag_D`, and at `n = 1` that is the *only* thing distinguishing two
structurally identical records. `record Monoid<A>` and `record Semigroup<A>`
with the same fields must not share a kernel type; with the tag they do not,
and the kernel itself rejects the confusion. Field `j` therefore sits at
`fst(snd^j x)` — one `snd` more than the naive count, exactly as tier-0 §5.1
already documents.

### 2.2 What the field table holds

Per record declaration, per field: the surface name, its index `j`, and the
surface type. The index is all the projection needs (§4.3); the type is what
the ambiguity diagnostic and the literal's field-order normalization need.

Field names must be **distinct within a record**, which is a new check — an
`inductive`'s field names are positional and never looked up, so duplicates
were previously harmless. Diagnose the duplicate at its own span.

## 3. Levels: compute the join, do not hardcode zero

**Rule.**

```
level(⟦record D⟧) = level(⟦T₁⟧) ⊔ … ⊔ level(⟦T_k⟧) ⊔ 0
```

which is nothing but the Σ spine's own rule (tier-0 §3.1), and which
`inductive.rs` already computes correctly when building the spine
(`inductive.rs:511–517`: the accumulator folds `fst_level ⊔ snd_level` from a
`Unit^0` terminator, and `⊔` absorbs the terminator).

Today every record lands at level 0, and it is worth being precise about
*why*, because the issue's framing ("a record over `A : Ty 0` lives at level 1
as soon as it stores a type") describes a case the surface cannot currently
express: `TyKind` is `Nat | a = b | Named<args> | [T; n] | (x: A) -> B`
(`ast.rs:152`) — **there is no way to write `Type` in a field**. Combined with
monomorphized parameters, every field type is at level 0, so the join is 0.

So there is no level *decision* in this round, only a level *discipline*: the
generated code must read the join off the spine and must never write
`Level::Zero`. The one hardcoded site in the generator is the `n = 0` →
`Empty` case (`inductive.rs:409–416`, whose comment already flags itself as
"the site" that changes when a declaration lives above 0), and a record with
one constructor cannot reach it.

**Where the real level question arrives**, named here so nobody re-derives it:
the **bundled** record, `record Mon { carrier: Type, unit: carrier, … }`. That
is a `Type`-in-`TyKind` round; the record then lives at level 1, and
non-cumulativity bites for real — it has bitten twice already
(`issues/unit-level-and-vec-preservation.md`,
`docs/kernel/unit-empty-level-indexing.md`). It is wanted, and it is not this round.
Writing the join as a computation now is what makes that round a grammar
change rather than a generator rewrite.

> **Landed 2026-07-27** (`docs/language/surface-universe.md`). The prediction held: the
> generator needed **no** change — `lower_ctor`'s `Level::max` fold already
> computed the join, so a bundled `Mon` lands at level 1 by arithmetic that was
> written here and never exercised until now. What the round did have to add
> was on the *other* side: a field at a universe has to become a type name for
> the fields after it, and `m.carrier` has to be usable as a type at all.

## 4. Field access, and the move of `.` into the elaborator

This is the round's real work and its only regression risk.

### 4.1 What `.` does today

`parser.rs:571–596`: `.f(args)` is desugared **in the parser** to
`App { head: Var(f), args: [args…, receiver] }` — a call to a global named
`f` with the receiver appended **last**, so that stage-2 implicit endpoints
are inferred from it (`p.sym()` ⇒ `sym(p)`, `p.inj(1)` ⇒ `inj(1, p)`,
`x.cong(f)` ⇒ `cong(f, x)`). The `(` is mandatory: `p.f` is a parse error.

> Superseded after this round: the receiver now fills the callee's `self`
> parameter, defaulting to the *first* explicit one, so `p.inj(1)` is
> `inj(p, 1)` and `p.trans(q)` reads forward. The inference claim above was
> never the reason — implicit insertion is name-directed and indifferent to
> explicit-argument order. See `issues/method-receiver-position.md` and §11.3.

Both properties are wrong for records. `m.op(x, y)` must be `(m.op)(x, y)`,
and `m.unit` must parse.

### 4.2 The decision: type-directed resolution in the elaborator

`ExprKind` gains one node, and the parser stops desugaring:

```rust
/// `p.f` (`args: None`) or `p.f(a, b)` (`args: Some`). Resolved in the
/// elaborator against the receiver's inferred type, NOT in the parser:
/// a record field wins over a global of the same name (§4.4).
Dot { recv: Box<Expr>, name: String, args: Option<Vec<Expr>>, span: Span },
```

Elaboration of `Dot { recv, name, args }`:

1. **Infer** the receiver. `recv` must be in an inference position — it is the
   thing whose type decides the meaning, so there is nothing to check it
   against. (This is already true today in effect: the receiver becomes an
   argument, and implicit insertion infers from it.)
2. If the receiver's inferred type is a **record** `D<…>` with a field named
   `name`, this is a **projection** (§4.3). With `args: Some(a⃗)`, the
   projection is then applied: `(π_name recv)(a⃗)`, an ordinary
   `Type::Pi` application, which `surface-function-types` landed.
3. Otherwise, with `args: Some(a⃗)`, fall back to **today's desugaring**:
   `App { head: Var(name), args: [a⃗…, recv] }`. Every existing use —
   `p.sym()`, `p.trans(q)`, `p.inj(1)`, `p.absurd()`, `x.cong(f)`, and every
   `calc` chain — takes this path unchanged.
4. Otherwise (`args: None`, receiver not a record with that field) it is an
   error: "`no field `op` on `Nat`". A bare `p.f` is **never** a global call —
   a call needs parentheses.

**Fallback when the receiver's type cannot be inferred.** Rule 2 needs an
inferred type. If inference fails, take rule 3 rather than reporting the
inference failure: that is today's behaviour and it must not regress. If the
receiver is not inferrable *and* there is no such global, report the
inference failure, since that is the more informative of the two errors.

### 4.3 The projection itself

Given a receiver `r : ⟦D<…>⟧` and field index `j` (from §2.2's table),
projection is exactly tier-0 §5.1's `π_j`, with `q_0 = r`:

```
π_j = fst(f_j: A_j. B_j;  snd(…) ∘ … ∘ snd(…) (r))     -- j snds, then fst
```

with the `+1` for the nominal tag, and with each `A_j` carrying the earlier
fields' projections substituted in — which is precisely what makes
`m.unit_l : (x: A) -> m.op(m.unit, x) = x` come out right without any
special handling. The dependency is the Σ's, and the substitution is the one
the arm-binding path already performs. **No new machinery**: this is the same
code path tier 0 uses to bind arm binders, lifted out of the arm.

Annotations are fully determined by the spine, so `p.f` **synthesizes** — the
checking-descent invariant (`issues/front-end-sugar.md`) is preserved.

### 4.4 Ambiguity: a field named like a global

If `m`'s record has a field `sym` and a global `sym` exists, `m.sym()` is the
projection applied to no arguments. **The field wins**, unconditionally — it
is the more local and more specific reading, and the global remains reachable
as `sym(m)`. Emit no warning by default; a field shadowing a global is normal
and expected once the trait layer exists (that is the whole point of
`m.op`).

The one case worth a diagnostic is the *near miss*: field `name` exists but
the arity is wrong, or `name` is a field of a *different* record than the
receiver's. Both should say what the receiver's type actually is, since the
common mistake will be a receiver that is not the record you thought.

### 4.5 Regression surface

Moving `.` out of the parser touches every landed test that uses method
syntax. The tests to watch, all of which must pass unchanged:
`surface-operators`' method and `calc` tests, `p.inj(k, …)` / `p.absurd()`
in the tier-0 suite, and `.cong(Succ)` from
`docs/language/constructor-function-values.md` — the last one specifically, since it
reaches an *inference* position and was the harder half of that round.

## 5. Destructuring `let`

```heather
let { unit, op } = m;
```

binds each name to its projection, as an `Alias` (`lib.rs:1287`) —
substituted, not `let`-bound, since the kernel has no `let`. This is pure
sugar over §4.3 and shares its code.

It is also **nearly redundant**: `match m { Monoid(u, o, l) => … }` already
works today via tier 0, and with Σ-η the two are definitionally the same term.
So it is second in priority behind projection, which is what the trait layer
needs. Field order in the pattern is the declaration's; a partial pattern
(`let { op } = m;`) is allowed — the unmentioned fields are simply not bound.

**The test that earns its keep is not "the two spellings agree"** — they emit
the same projections, so that is true by construction. It is **η**:

```heather
theorem eta(m: Monoid<Nat>): Monoid { unit: m.unit, op: m.op, unit_l: m.unit_l } = m { refl }
```

This exercises Σ-η *and* `Unit`-η through the nominal tag simultaneously,
which is exactly the argument tier-0 §3.3 makes when it explains why the tag
cannot be `Id`. It should pass; if it does not, something is wrong somewhere
that would otherwise surface much later.

## 6. The literal

**Braced and named**, `Monoid { unit: 0, op: f, unit_l: p }`:

- Field order in the literal is **free**; it is normalized to declaration
  order before lowering. Missing field and unknown field are both errors, each
  at its own span, and the missing-field message lists what is missing.
- Elaboration is then tier 0's constructor path (§4 of that doc), unchanged.
- Type arguments come from the fields where inference can see them
  (tier-0 §2), with `Monoid<Nat> { … }` available when it cannot.

The positional form `Monoid(0, f, p)` also works, since §2.1 generates a real
constructor. That is not a second path — it *is* the path; the braced literal
is a permutation in front of it.

**The braced form is provisional** (decided 2026-07-27, after implementing).
Since a record's constructor is an ordinary constructor, the moment
[[named-arguments]] lands the same thing is sayable with no new syntax at all:

```heather
Monoid(0, f, p)                          -- works today, positional
Monoid(unit: 0, op: f, unit_l: p)        -- named arguments: an ordinary call
Monoid { unit: 0, op: f, unit_l: p }     -- this section's form
⟨0, f, p⟩                                -- anonymous, head inferred
```

The second line is a *call*, so it is in parentheses, so it carries none of
§6.1's ambiguity and needs none of its suppression flag — and it is consistent
with every other application in the language rather than being a special form.
That makes the braced literal plausibly **redundant with named arguments**
rather than with the anonymous form, and retiring it would delete §6.1
outright, along with the standing hazard that every future block-preceding
construct has to remember the flag.

So: no further investment in the braced form, and revisit it when named
arguments land. This is also a reason to pull that issue forward — it now pays
off in two places (there, `@`-calls and `calc`'s fragile desugaring; here, a
whole ambiguity class).

**Named arguments landed** (`docs/language/named-arguments-design.md`), so the second
line above is real — spelled `Monoid(unit := 0, op := f, unit_l := p)`, with
`:=` rather than `:` for the reasons that document's §3.1 gives, and permuted
by the *same function* this section's literal is permuted by, so the two
cannot drift into disagreeing about an unknown, duplicated or missing field.
`crates/elab/tests/named_arguments.rs` proves the three spellings equal by
`refl`.

**The braced form is not retired, and that is a decision rather than an
omission**: retiring it is a *migration* (every literal in `lib/`, the
fixtures and the tests, plus the `no_record_lit` flag and its ten set-sites,
plus this section's parenthesis rule and its tests), and bundling a sweep into
the round that introduces the successor would make a bisect over either
useless. The criterion for that round is in named-arguments-design.md §10.2.

Not chosen, and worth recording why: **going all-in on `⟨…⟩`** — dropping the
braced form now and spelling an explicit head as `Monoid ⟨unit: 0, …⟩` — is
coherent, and its rule is cleaner than what we have ("braces are for blocks,
angles are for structure", which would take `let ⟨x, y⟩ = p` with it). It is
not taken because `⟨⟩` has no good ASCII twin, and every unicode form here has
one (`λ`/`fun`). `<` is already both `lt` and the type-argument bracket, which
is why `try_tyargs` has to be speculative, so it cannot serve. Making the only
way to construct a record depend on editor support is a worse trade than one
pair of parentheses in a `theorem` statement — and named arguments remove the
need to make it at all.

### 6.1 The `match m { … }` ambiguity (added while implementing)

A braced literal makes `{` able to follow an expression, and there are three
places where a **block** already follows one:

```heather
match m { … }                     -- scrutinee, then the arm block
match m as x -> M { … }           -- motive type, then the arm block
theorem t(): a = b { refl }       -- statement type, then the proof block
```

Without a rule, `match m { T => … }` reads `m { T: … }` and dies at the `=>`.
This is Rust's problem exactly, and it takes Rust's fix: a parser flag that
**suppresses the literal** in those three positions and is **lifted inside any
bracket**. So `match f(D { x: 1 }) { … }` is fine — the literal is inside call
parentheses — and a literal that really is wanted in a suppressed position is
parenthesised:

```heather
theorem eta(p: P): (P { x: p.x, y: p.y }) = p { refl }
match (P { x: 1 }).x { Zero => …, Succ(k) => … }
```

The parenthesis requirement in a `theorem` statement is worth calling out,
because that is where it will actually be met: an η or equality statement
about a record is exactly a literal in a suppressed position. It is the only
ergonomic cost of the braced form, and it is what §10.6's tests are written
against.

Deferred, wanted: the **anonymous** literal, Lean's `⟨0, f, p⟩`. It is
positional and elaborates in checking position against the expected record
type — the same shape as an unsaturated constructor checking against an
expected `Π` (`docs/language/constructor-function-values.md`), so the machinery is
there. It is deferred only because `⟨⟩` needs lexer support and is awkward to
type; it should land as a small follow-up, not a round.

### 6.2 Update (added 2026-10-03)

`s with { f = v, … }` is the literal that writes the given fields and keeps
every other one as `s`'s projection (`issues/record-update-syntax.md`):

```heather
fn wc_step(s: WcState, b: BitVec(8)) → WcState {
    … s with { bytes = Succ(s.bytes), inside = False } …
}
```

- **Postfix, on any expression**, chaining left to right
  (`p with { x = 0 } with { y = 0 }`). `with` is a word only before a `{`, so
  it names nothing else and is no keyword elsewhere. Fields are written with
  `=`, as a program assigns them; the literal's `:` declares them.
- **Elaborated as the literal.** The elaborator infers the base's type, finds
  the record, and checks or infers `R { f1: …, f2: … }` with each unwritten
  field `base.f` (`Elaborator::record_update_expr`). A base that is not a
  local is bound once by a `let`, an alias, so the term is the constructor
  over projections in either case. That is the term every record reader
  already takes; the native frontend reads it as a record result like any
  other.
- **Refused:** a field the record does not have, a field written twice, a
  base that is not a record, an empty update (at parse), and a kept field
  whose type mentions a replaced one, below binders too (`unit_l` when `unit`
  or `op` is replaced). Its old value is about the old field, so the update
  must give it as well, and then it is accepted.

## 7. Equality of records

Two directions, and they are not the same problem.

**Destructing (`inj`) is inherited, restrictions and all.** A record
inherits tier-0 §6.2 verbatim: `inj(p, k)` from `Monoid(a⃗) = Monoid(b⃗)` is
derived at a **constant** motive, so a field whose type mentions an earlier
field is diagnosed, not derived (`issues/dependent-field-injectivity.md`).
For records this is the *normal* case rather than the exotic one — `unit_l`'s
type mentions `unit` and `op` — so the diagnostic will be hit. It is not new
work, it is not made worse here, and it should be tested rather than
rediscovered.

Disjointness (§6.1) is vacuous at one constructor.

**Constructing is the direction records actually want**, and it is out of
scope. "Two `Monoid`s with equal fields are equal" needs funext for the
function fields, and a record of functions is what the trait layer is made of.
Recorded here so the two do not get conflated later: this is *not* blocked on
the dependent-field restriction, and it is not permanently blocked on funext
either. The shape of the eventual answer, per the 2026-07-27 design
discussion:

- A record with **no function fields** gets full field-wise `inj` and
  construction once dependent-field injectivity lifts.
- A record **with** function fields needs a canonical setoid symbol
  quotienting functions — i.e. `issues/setoid-auto-lifting.md`, which is
  already filed for exactly this class of problem, and which is the reason
  this is a later round rather than a hole.

## 8. What is out of scope

- **Instance resolution / typeclass search** — `issues/compile-typeclass-design.md`.
  This round gives records of functions and `m.op`; passing `m` explicitly is
  the interface. Everything a trait needs is a record plus dispatch, and
  dispatch is the other issue.
- **Coercions** of any kind.
- **Bundled records** (a `Type`-valued field) — §3.
- **Record update**: landed later, as `m with { unit = 1, … }` (§6.2).
- **Recursive records** — that is an `inductive`, and §2's check says so.
- **Anonymous `⟨…⟩` literals** — §6, wanted, small, deferred.
- **Record equality construction** — §7.

## 9. What this does *not* touch

No kernel change. No metatheory obligation, no ch. 07 pass: `Σ`, `Pair`,
`Fst`, `Snd` are v0 formers with definitional η (`conv.rs:668`), and every
term this round emits is one the tier-0 generator already emits. The trusted
base is untouched, exactly as in items 8, 9 and 11.

## 10. Acceptance checklist

Each an acceptance test in `crates/elab/tests/records.rs` unless noted. Per
`docs/testing-generated-terms.md`, the suite must vary: an **open** field type
(inside a polymorphic `fn`), a **checking** position and not only computation,
a **neutral** receiver and not only a literal, and a **negative control**.

1. Every generated record type, its constructor, and every projection passes
   the real kernel check.
2. `record Monoid<A> { … }` with a **dependent** field (`unit_l` mentioning
   `unit` and `op`) declares, and `m.unit_l`'s type is the one with `m`'s own
   projections substituted in — checked by kernel conversion against the
   hand-written expected type.
3. `Monoid { unit: 0, op: f, unit_l: p }.unit` β-reduces to `0`, definitionally.
4. Field order in the literal is free: two permutations of the same literal
   are convertible.
5. Missing field, unknown field, and duplicate field name are each rejected at
   their own span.
6. **η**: §5's `Monoid { unit: m.unit, … } = m` by `refl`, at a **neutral**
   `m` (a parameter, not a literal). The load-bearing test.
7. `let { unit, op } = m;` and `match m { Monoid(u, o, l) => … }` produce
   convertible terms, at a neutral `m`.
8. **Open**: inside `fn twice<A>(m: Monoid<A>, x: A) -> A { m.op(x, x) }` —
   the record instantiated at an open type, projected, and applied. Checks
   and computes when instantiated at `Nat`.
9. **Checking position**: a record literal checked against an expected type
   supplied by a `fn`'s return type, with no annotation at the literal.
10. `m.op(x, y)` elaborates to `(π_op m)(x, y)` and **not** to `op(x, y, m)`,
    checked by kernel conversion against the hand-written expected term. The
    test that pins §4.2's decision.
11. **Field wins over global**: a record with a field `sym`, in a file where
    the polymorphic `sym` is in scope; `m.sym()` is the projection.
12. **Regression**: the full existing method-syntax suite — `p.sym()`,
    `p.trans(q)`, `p.inj(1)`, `p.absurd()`, `.cong(Succ)`, and the `calc`
    chains — passes unchanged after `.` moves to the elaborator.
13. `p.f` on a receiver with no such field is rejected, naming the receiver's
    actual type.
14. **Negative control**: a `record` whose field mentions itself is rejected
    with the occurrence located and the message naming `inductive`.
15. Two structurally identical records (`Monoid`/`Semigroup` with the same
    fields) are **not** interconvertible — the nominal tag at `n = 1`.
16. `inj` at a *non*-dependent field of a record fires; `inj` at `unit_l` is
    **diagnosed**, not derived, with the dependent-field message (§7).
17. Level: a record's computed level is the join of its field levels. Today
    that is 0 for every writable record, so this is asserted against the
    computation rather than against a literal `0` — the test that would catch
    a hardcoded `Level::Zero` when a `Type`-valued field arrives (§3).

## 11. What implementing this corrected

Per the house pattern — tier-0 §3.3 and §6.2, container-fields §10,
constructor-function-values §5.1 — where the code and this document disagree,
the code is right and this section records why.

Implemented 2026-07-27: `crates/elab/tests/records.rs` (33 tests), workspace
at 508. The §10 checklist passes in full.

### 11.1 A function field was rejected outright, and had to stop being

**The scheme missed this entirely, and it would have blocked the round on its
own line one.** `reject_function_fields` (`inductive.rs`) rejected *any* field
whose type contained a `->`, with the message "that is the infinitary tier".
So

```heather
record Monoid<A> { unit: A, op: A -> A -> A, … }
```

— the motivating example of `issues/surface-records.md`, and the shape of
every trait, `Compile` instance and pass interface this round exists to
enable — did not declare.

The check was keyed on the **shape** of the field type when the property it
wanted is a **self-occurrence**. A function field is infinitary because the
declaration appears in it (`Acc.intro`'s `h: (b: A) -> Acc<A>` has one child
per `b`); a function field that does not mention the declaration is an
ordinary payload — one `Type::Pi` component of the Σ spine, which every
downstream scheme already treats like any other payload. Nothing about the
tier-0 or tier-1 lowering had to change; the check was simply too coarse.

Corrected to reject a `Π` field **that mentions the declaration**, in the
domain or the codomain (the domain case being the negative occurrence, which
is a rejection for a second reason and must not slip past this one). `Acc`
stays rejected, with a message that now names why. The
`function_types::a_function_field_is_the_infinitary_tier` test asserted the
over-broad behaviour and was rewritten into two: the recursive case still
rejects, and `inductive Endo { Mk(f: Nat -> Nat) }` now declares, computes and
proves.

Worth noting *why* this hid: until records there was no reason to put a
function in a field, so the over-broad check had no counterexample. It is the
same shape as the container-field and dependent-field restrictions — a
limitation written down as if it were a property of the tier, when it was a
property of the check.

### 11.2 The literal collides with every block-preceding position

Anticipated in neither §2 nor §6 as written. Documented above as §6.1: a
braced literal needs Rust's suppression rule in the `match` scrutinee, the
`match` motive, and a declaration's result type, lifted inside brackets. The
practical consequence is that a record literal in a `theorem` **statement**
must be parenthesised, which is exactly where η statements live.

### 11.3 Two things found and deliberately not fixed

- **`.trans()` reads backwards.** The receiver-last convention (§4.1) is right
  for a one-premise lemma (`p.sym()`) and inverted for a two-premise one:
  `q.trans(p)` is `trans(p, q)`, so the receiver is trans's *second* premise.
  Pre-existing, unchanged by this round, and pinned as such in §10.12's test
  rather than quietly worked around. Promoted to its own issue and prototyped
  the same day: [[method-receiver-position]], which measured the flip as cheap
  for declarations and awkward only for the built-in special forms — and
  falsified the guess that it would also fix `.cong(Wrap)`.
  **Fixed 2026-07-27**, and not by a flip: the receiver's position became a
  declared property of the parameter (`self p: a = b`), defaulting to the
  first explicit one. §10.12's test now asserts `p.trans(q)` forward, and the
  backwards spelling is a rejection test in `method_receiver.rs`.
- **A numeral above ~40 overflows a 2 MB stack.** `fn f() -> Nat { 99 }` alone
  overflows a test thread's default stack — verified against a clean tree, so
  it predates this round entirely. It cost real debugging time here because a
  test used `99` as a "distinctive" value. Unrelated to records; filed
  separately.
