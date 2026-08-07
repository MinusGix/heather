---
title: Where do requires binders live? Sketch the call-signature syntax options
status: open
labels: [frontend,syntax,design,ergonomics]
created: 2026-08-07
updated: 2026-08-07
---

From the adoption round's reading (2026-08-07): `fn sum<A> requires m: Monoid<A> (xs: List<A>) -> A` reads oddly — the requires clause sits BETWEEN the type parameters and the value parameters, and with several dictionaries the head of the declaration becomes a wall before the first real argument. The position is semantically motivated (solver parameters are moved to the front because later parameter TYPES may mention them — rare but legal, e.g. `p: m.op(x, y) = z`) but the surface need not mirror the elaboration order.

Options to sketch against real library signatures before deciding:

- **(a) Status quo**: prefix clause. Honest about dependency order; heaviest to read.
- **(b) Trailing where-clause**: `fn sum<A>(xs: List<A>) -> A requires m: Monoid<A> { … }` (or `where`). Rust-familiar, keeps the argument list first; desugars to the front, so a later value parameter's type referencing `m` reads textually forward — acceptable if rare, worth a lint if confusing. Name could be optional (`requires Monoid<A>`) when the dictionary is only consumed by resolution/dispatch, never projected by name — auto-named binder.
- **(c) In-list bracketed binders**: `fn sum<A>([m: Monoid<A>], xs: List<A>)` Lean-style — interleaves freely, no reordering question, but adds a third bracket kind to parameter lists.
- **(d) Both (a) and (b)**, prefix for the dependent case, trailing for the common one — two spellings of one thing has cost (traits record §12's own warning about the instance forms).

Also from the same reading, separate but adjacent: **instance shorthand** — `instance Default<Nat> { default := 0 }` is already short, but a one-field instance may want `instance Default<Nat> := 0`-grade concision or a positional literal; sketch alongside since both are call-signature/declaration ergonomics over the same feature. Decide in one small design pass; no implementation until then.

## Syntax exploration (2026-08-07, brainstorm round)

Design only — no parser work was done and none is proposed here beyond the
recommendation. Every grammar claim below was **checked against
`crates/syntax/src/parser.rs`**, not guessed; the checks are collected in §D.

### A. The facts the choice has to respect

1. **A `requires` binder is not a new kind of thing.** It is a parameter with
   `implicit = true, solver = Some(Infer)` (`docs/traits-layer2-design.md` §1),
   i.e. *exactly* what `hx: P := infer` produces. The two spellings differ only
   in that `requires` also moves its binders to the front. Any syntax that puts
   class constraints somewhere a `:= infer` parameter cannot go is asserting a
   distinction the elaborator does not have (criterion (f) below).
2. **They are passed by hand under `@`**: `@sum(m, xs)` — solver parameters
   occupy argument slots in the `@` spelling, and *type* arguments never do
   (`issues/at-and-type-arguments.md`). So the declaration bracket a constraint
   is written in is also a claim about which bracket it is passed in.
3. **Their type is a class reference**, `name<args>` — not a general type
   (§9.4). The general goal (`x > 0`) has its own spelling, `:= infer`, and no
   syntax below should quietly extend class-reference position to arbitrary
   types without saying so.
4. **The `instance` head has a `requires` clause too**, with the same meaning,
   and an `instance` has **no parameter list** — only a tyvar list and a class
   reference. Any form that lives *inside* a parameter list therefore cannot
   serve the instance head, and leaves `requires` standing there. This is a
   criterion the original four options did not name; call it **(i) does it
   generalize to `instance`**.
5. **What the real library actually does with the binder** (counted, not
   assumed — `lib/std/algebra.hthr`): six constrained declarations, and
   **four of them project the dictionary by name** — `mconcat` (`m.unit`),
   `mconcat_single` (`m.unit_r`), `max_of_self` (`c.le_refl`),
   `plus_zero_of_comm` (`a.plus_comm`, `a.zero`). Only `max_of` and
   `max_of_true` never name it (receiver dispatch carries `x.le(y)`).
   The Lean intuition "the dictionary is rarely referenced by name" is a claim
   about *operation*-heavy code; this library is **law**-heavy, and a law or a
   unit has no receiver to dispatch from — `m.unit` cannot become `unit`, and
   `a.plus_comm(x, a.zero)` names the dictionary twice. **Anonymity must be
   free, but the named form is the common form here and must stay short.**
   That single fact does more to separate the candidates than any aesthetic
   argument below.

### B. The candidate space (11)

Recorded ones are marked ★.

- **(1) ★ Prefix clause (status quo).**
  `fn mconcat<A> requires m: Monoid<A> (xs: List<A>) -> A`
- **(2) ★ Trailing clause, after the return type.**
  `fn mconcat<A>(xs: List<A>) -> A requires m: Monoid<A> { … }`
- **(2b) Trailing clause, before the return type.**
  `fn mconcat<A>(xs: List<A>) requires m: Monoid<A> -> A { … }`
- **(3) ★ In-list bracketed.** `fn mconcat<A>([m: Monoid<A>], xs: List<A>) -> A`
- **(4) ★ Grouped generics (the user's).**
  `fn mconcat<A, m: Monoid<A>>(xs: List<A>) -> A`
- **(5) ★ Separate bracket group after the generics (disliked).**
  `fn mconcat<A>[m: Monoid<A>](xs: List<A>) -> A`
- **(6) Constraint on the binder, Rust/Scala-style.**
  `fn mconcat<A: Monoid>(xs: List<A>) -> A`
- **(7) In-list, marker keyword, name optional** — the `:= infer` mechanism with
  its marker moved to the front so the name can be dropped:
  `fn mconcat<A>(infer m: Monoid<A>, xs: List<A>) -> A`, anonymous
  `fn sum<A>(infer Monoid<A>, xs: List<A>) -> A`.
- **(8) In-list, bare class reference.** A class reference standing where a
  parameter name would go *is* an inferred dictionary:
  `fn sum<A>(Monoid<A>, xs: List<A>) -> A`; named case keeps today's
  `m: Monoid<A> := infer`.
- **(9) Haskell context arrow inside the list.**
  `fn mconcat<A>(Monoid<A> => xs: List<A>) -> A`
- **(10) Second parameter clause (Scala 3 `using`).**
  `fn mconcat<A>(xs: List<A>)(using Monoid<A>) -> A`
- **(11) Attribute / preceding line.**
  `#[requires(Monoid<A>)] fn mconcat<A>(xs: List<A>) -> A`, or a bare
  `requires Monoid<A>` line above the `fn`.

Prior art, and what transfers to a comma-and-braces language:

| Language | Spelling | Transfers? |
|---|---|---|
| Lean 4 | `[Monoid α]` in the binder telescope | Yes — (3). Anonymous by default, interleaves, one extra bracket kind. |
| Agda | `⦃ _ : Monoid A ⦄` instance arguments | Same shape as Lean; the brackets are worse to type. |
| Idris 2 | `Monoid a => …` context arrow, or `{auto _ : …}` | (9); `auto` is our `:= infer` exactly, and Idris spells it *inside* the binder — evidence for (7)/(8). |
| Haskell | `Monoid a => …` before everything | (9) at signature level; needs an arrow that is not our lambda arrow. |
| Scala 3 | `(using Monoid[A])` clause, anonymous by default, `given` for instances | (10)/(7). The strongest precedent that **anonymous by default with optional naming, in a parameter clause, next to ordinary parameters** is livable at scale. |
| Rust | `<T: Trait>` and `where` | (6)/(2). Both assume a constraint is *about one named type parameter*, which is false for `Monoid<List<A>>` and for multi-parameter classes. |
| C++20 | `template<…> requires C<T>` **and** trailing `requires` | Precedent for shipping two placements — and for the confusion tax that followed. Option (d) in the problem statement is this, and inherits it. |

### C. Evaluation

Criteria: (a) one vs three constraints; (b) multi-line behavior; (c) grouping
and name/class conflation; (d) anonymity and optional naming; (e) the dependent
case; (f) honesty about the `:= infer` unification; (g) parser reality;
(h) migration; (i) generalizes to `instance` (§A.4).

**(1) Prefix clause.** (a) One is fine, three is the wall the issue was filed
over: `fn f<A> requires c: Cmp<A>, m: Monoid<A>, d: Default<A> (xs: List<A>)`
— the reader reaches `(` after 60 characters and the arguments are last.
(b) No good multi-line shape: the clause is neither inside `<>` nor inside
`()`, so a formatter has to invent a rule. (c) Grouping is fine (each ref names
its carrier), no conflation. (d) Naming is mandatory today; anonymity would
need `requires Monoid<A>` with the name elided — easy. (e) Honest by
construction. (f) Poor: a class constraint gets a keyword and a position of its
own, while the identical `d: Default<A> := infer` sits in the parameter list —
`or_default` and `mconcat` in the same file look like two features. (g) Ships.
(h) Zero. (i) **Yes** — it is the instance-head form already.

**(2) Trailing after the return type.** (a) Best in the common case: name,
generics, arguments, result, then the small print. (b) The recorded objection
is real and is the deciding one: `-> A requires m: Monoid<A> {` pushes the brace
toward its own line as soon as there are two constraints, and Rust's `where`
experience says the formatter will do it always. (c) Fine. (d) Fine.
(e) **Lies about order** — a later parameter whose type mentions `m` reads
backwards. Rare (record §1 calls it rare), lint-able, not fatal. (f) Same cost
as (1), worse: the small print is now *after* the return type while `:= infer`
is *before* it. (g) Parseable — checked: type parsing stops at a bare
identifier (there is no juxtaposition application), and `no_record_lit` is
already set for the result type, so `-> A requires … {` has no brace ambiguity.
(h) Six declarations. (i) No (an instance has no return type either) — but it
could keep its clause where it is, since the instance form *is* trailing
relative to the class ref.

**(2b) Trailing before the return type.** Buys back the brace: `{` still
follows `-> A`. Costs the thing (2) was for — the return type is now behind the
small print, and `theorem`'s statement (`: max_of(x, y) = y`) is the part a
reader most wants adjacent to the name. Strictly worse than (2) for theorems,
which are half the constrained declarations in the library.

**(3) In-list bracketed.** (a) One constraint reads well; three is the noise
the user named: `([c: Cmp<A>], [m: Monoid<A>], [d: Default<A>], xs: …)` — six
brackets and three commas doing one job. (b) Best-in-class vertically: one
entry per line, `{` untouched, and the constraints are visibly a prefix of the
list. (c) Grouping fine, no conflation. (d) Anonymity free (`[Monoid<A>]`).
(e) Honest — interleaves. (f) **Good**: the constraint lives where the
parameter lives; the only dissonance left is bracket-vs-`:= infer`.
(g) Free — checked: no parameter can begin with `[` today (`[T; n]` is the
vector *type* and needs the `;`; `[e, …]` is a vector literal in *expression*
position). Cost: `[Monoid<A>]` reads as "a slice of `Monoid<A>`" to every Rust
reader, and the vector type is a live neighbour. (h) Six declarations. (i) No.

**(4) Grouped generics `<A, m: Monoid<A>>`.** (a) Very good at both counts:
`<A, c: Cmp<A>, Monoid<A>, Default<A>>` keeps the entire constraint story in
one bracket and the argument list clean. (b) Good — the tyvar list breaks
across lines like any comma list and `{` never moves. (c) The strongest form on
grouping, and it matches how mathematics quantifies ("for all `A` and a monoid
structure on it") and how Lean's `variable {α} [Monoid α]` reads. The recorded
cost — one bracket holding both binder names and class references — is real but
**parseable**: a tyvar is `ident` optionally followed by `:`, a class ref is
`ident<…>`, so one token of lookahead separates them. (d) Anonymity free; the
named form needs `<A, m: Monoid<A>>`, and **that colon is already taken**: the
tyvar list parses `<A: Type<1>>` as a universe annotation
(`parser.rs:579–588`). Disambiguating on `Type` vs anything-else is doable and
its error messages are writable, but it is a second meaning for one colon in
one bracket, and it is the *common* (named) case that pays it. (e) The
dependent case cannot be expressed at all here — a constraint whose type
mentions a **value** parameter has no home in the type bracket; it would fall
back to `:= infer` in the parameter list. Arguably principled ("the bracket you
live in is decided by what your goal mentions"), but it is a rule to learn.
(f) **Weakest on this criterion**: class constraints move as far from
`d: Default<A> := infer` as the grammar allows, into the bracket that otherwise
holds *types*. The one-mechanism claim becomes invisible in the very file that
demonstrates it. (g) Two checked problems, one of them sharp:
  - the colon overload above;
  - **explicit type application arity**. `elab_ty_app` computes
    `n_ty = params.iter().take_while(|p| p.is_type).count()` and errors unless
    `tyargs.len() == n_ty` (`crates/elab/src/lib.rs:5506–5524`). So a
    declaration written `<A, Monoid<A>>` is called `mconcat<Nat>(xs)` — two
    entries at the declaration, one at the call — and under `@` the dictionary
    is passed in the *value* parens (§A.2). The declaration bracket and the
    call bracket disagree, in both directions. Fixable by rule ("class
    references are skipped for explicit type application"), but it is exactly
    the kind of rule that is remembered wrong.
  - a class ref between two tyvars (`<A, Monoid<A>, B>`) also breaks the
    *leading* run `take_while(is_type)` expects, so lowering must reorder all
    tyvars ahead of all constraints — harmless, but it means the written order
    is not the elaborated order here either (the charge (2) is criticized for).
  (h) Six declarations, plus it would want the instance heads too. (i) **Yes,
  and uniquely** — `instance<A, Monoid<A>> Monoid<List<A>> { … }` works, and no
  other in-list form does. This is grouped generics' best argument and it is a
  good one.

**(5) `<A>[m: Monoid<A>]`.** Already disliked, and correctly: it pays for a
third bracket group *and* keeps the wall-before-the-arguments shape of (1),
buying only the ability to elide names. Nothing below rescues it.

**(6) `<A: Monoid>`.** Reads beautifully at one constraint on one parameter
and falls apart everywhere else. It cannot say `Monoid<List<A>>` (the
constrained type is not a parameter), it cannot say a two-parameter class
(`Coe<A, B>` — which side is the binder?), it stacks badly (`<A: Monoid + Cmp>`
needs a `+` this language does not have), and the colon is already the universe
annotation, so `<A: Monoid>` and `<A: Type<1>>` are the same production with
two meanings. Its one virtue — the constraint is adjacent to the thing
constrained — is what (4) delivers without the restrictions. **Not viable even
as sugar**, because a sugar that covers only the single-parameter,
carrier-is-a-tyvar case teaches a rule with an exception in the second example
(`Monoid<List<A>>` appears in `lib/std/algebra.hthr` today).

**(7) In-list `infer` marker, name optional.** `infer m: Monoid<A>` named,
`infer Monoid<A>` anonymous, and the general goal is the *same* form:
`theorem blah(x: Nat, infer hx: x > 0): …`. (a) One is unobtrusive; three is a
clean vertical block or a readable line. (b) Very good — parameter-list
formatting, `{` untouched. (c) Grouping by carrier is in the class ref itself;
no conflation of any kind (the marker keyword separates the name space from the
class space explicitly). (d) **Both, at the same length** — anonymity is
dropping one word, not switching forms; and the named form is *shorter* than
today's `m: Monoid<A> := infer`. Given §A.5 (four of six project by name) this
is the criterion that matters most. (e) Honest — interleaves, so the dependent
case is written in the order it elaborates. (f) **The honest maximum**: class
constraints and solver-default value parameters are literally one production,
one keyword, one position; the file shows one feature. (g) Checked and free:
today a parameter must begin with `{`, `self`, or `ident :`, so `infer` +
(ident-not-followed-by-`:` | class ref) is unambiguous with one token of
lookahead, and a parameter *named* `infer` (`infer: Nat`) still parses. The
anonymous general-goal case (`infer x > 0`) is the only delicate corner and can
simply be refused — anonymity restricted to class references, which is §9.4's
production and covers every real use. (h) Six declarations, plus a decision
about `:= infer`: keep it as the trailing alias (two spellings, the cost the
issue's option (d) warns about) or retire it and rewrite `or_default` and the
`:= infer` tests. **Retire it** — it landed the same day; this is the cheapest
this choice will ever be. (i) No — the instance head keeps `requires` (§A.4).

**(8) Bare class reference in the list.** All of (7)'s virtues for the
*anonymous* case with no keyword at all, and (7)'s exact failure for the named
one: naming falls back to `m: Monoid<A> := infer`, so the common case in this
library is the verbose case and the two cases do not look like each other.
Making `m: Monoid<A>` *itself* inferred is not available: it would silently
turn every honest dictionary-valued parameter (the thing `bool_or_monoid`
exists to be passed as) into an inferred one, breaking "an instance is an
ordinary value". Keep as the fallback if `infer` is judged too heavy a word.

**(9) `=>` context inside the list.** Attractive on paper — one separator, no
new bracket, constraints visibly a prefix — and rejected on lexical grounds:
`=>` is the lambda arrow and the match-arm arrow in this grammar, both of which
appear inside parentheses in ordinary code. Reusing it for a third,
unrelated purpose in *parameter* position is exactly the kind of overload the
house style refuses elsewhere. Also has (8)'s naming problem.

**(10) Second parameter clause `(xs: …)(using Monoid<A>)`.** Would import
Scala's ergonomics wholesale, but Heather has exactly one parameter list, and
the postfix expression grammar already reads `f(a)(b)` as curried application
(`Cons(1)(xs)` is re-associated in the elaborator). A second clause at the
declaration would be a shape whose call-site echo means something else. Reject.

**(11) Attribute or preceding line.** Moves the constraint out of the signature
entirely, which is the wrong direction: it *is* a parameter, it is passed under
`@`, and it is projected in the body. An attribute also has no natural place to
bind a name. Reject — but note it is the only form with zero effect on the
signature's reading order, so if constraints ever become numerous *and* purely
resolutional (never named), it comes back.

### D. Parser reality, checked

| Claim | Verdict | Evidence |
|---|---|---|
| `[` is free at parameter position | Yes | `param := name ":" type \| "{" name ":" type "}"`; `[T; e]` is a *type*, `[e, …]` an *expression* (`parser.rs` header, 1433/1872) |
| `<A: Monoid>` collides with an existing production | Yes | tyvar `:` already introduces a **universe** (`parser.rs:579–588`) |
| `<A, Monoid<A>>` is parseable | Yes | one-token lookahead: `<` after the ident means class ref, `:` or `,`/`>` means tyvar |
| grouped generics disturbs explicit type application | **Yes** | `n_ty = take_while(is_type)`, arity checked exactly (`crates/elab/src/lib.rs:5506–5524`) |
| trailing `requires` after `-> A` is parseable | Yes | no juxtaposition application, and `no_record_lit` is already set for the result type (`parser.rs:1032–1035`) |
| a leading `infer` marker in the list is free | Yes | a parameter starts with `{`, `self`, or `ident :`; `infer m:` / `infer C<A>` match none |
| `where` is unused | Yes | no occurrence in lexer or parser; every keyword here is contextual |
| `requires` binder types are class refs already | Yes | `requires_list` calls `class_ref` (`parser.rs:531–564`), §9.4's correction |

### E. Test drive — the real signatures

The three finalists: **(4)** grouped generics, **(7)** in-list `infer`,
**(3)** in-list brackets. Plus an invented three-constraint signature,
`merge`, of the shape a sorted merge would need.

**Today (1):**

```heather
fn mconcat<A> requires m: Monoid<A> (xs: List<A>) -> A { … }
theorem plus_zero_of_comm<G> requires a: AddCommMonoid<G> (x: G): a.plus(x, a.zero) = x { … }
fn or_default<A>(o: Option<A>, d: Default<A> := infer) -> A { … }
fn sum<A> requires m: Monoid<A> (xs: List<A>) -> A { … }
fn merge<A> requires c: Cmp<A>, m: Monoid<A>, d: Default<A> (xs: List<A>, ys: List<A>) -> List<A> { … }
```

**(7) in-list `infer`:**

```heather
fn mconcat<A>(infer m: Monoid<A>, xs: List<A>) -> A { … }
theorem plus_zero_of_comm<G>(infer a: AddCommMonoid<G>, x: G): a.plus(x, a.zero) = x { … }
fn or_default<A>(o: Option<A>, infer Default<A>) -> A { … }      // anonymous — but the body names `d.default`, so: infer d: Default<A>
fn sum<A>(infer Monoid<A>, xs: List<A>) -> A { … }               // never projected: anonymous
fn merge<A>(infer c: Cmp<A>, infer Monoid<A>, infer Default<A>, xs: List<A>, ys: List<A>) -> List<A> { … }

fn merge<A>(
    infer c: Cmp<A>,
    infer Monoid<A>,
    infer Default<A>,
    xs: List<A>,
    ys: List<A>,
) -> List<A> {
```

**(4) grouped generics:**

```heather
fn mconcat<A, m: Monoid<A>>(xs: List<A>) -> A { … }
theorem plus_zero_of_comm<G, a: AddCommMonoid<G>>(x: G): a.plus(x, a.zero) = x { … }
fn or_default<A, d: Default<A>>(o: Option<A>) -> A { … }
fn sum<A, Monoid<A>>(xs: List<A>) -> A { … }
fn merge<A, c: Cmp<A>, Monoid<A>, Default<A>>(xs: List<A>, ys: List<A>) -> List<A> { … }

fn merge<
    A,
    c: Cmp<A>,
    Monoid<A>,
    Default<A>,
>(xs: List<A>, ys: List<A>) -> List<A> {
```

**(3) in-list brackets:**

```heather
fn mconcat<A>([m: Monoid<A>], xs: List<A>) -> A { … }
theorem plus_zero_of_comm<G>([a: AddCommMonoid<G>], x: G): a.plus(x, a.zero) = x { … }
fn or_default<A>(o: Option<A>, [d: Default<A>]) -> A { … }
fn sum<A>([Monoid<A>], xs: List<A>) -> A { … }
fn merge<A>([c: Cmp<A>], [Monoid<A>], [Default<A>], xs: List<A>, ys: List<A>) -> List<A> { … }
```

What the drive shows, beyond the eyeball:

- **(4) wins the one-line contest** and only that contest: `fn sum<A, Monoid<A>>(xs: List<A>) -> A` is the shortest honest signature anyone has written for this. It also, alone, gives `instance<A, Monoid<A>> Monoid<List<A>>`.
- **(4) then has to explain `or_default`.** Under (4) the file's *two* solver
  parameters — `Default<A>` (a class) and a hypothetical `hx: x > 0` (not) —
  live in different brackets. Under (7) they are the same word in the same
  place. That is the whole of §A.1 made visible or made invisible.
- **(3) is unreadable at three** and unremarkable at one; its vertical form is
  genuinely nice, which is what the user reported, but (7)'s vertical form is
  the same shape with a word instead of two brackets.
- **`plus_zero_of_comm` is the honest test of anonymity** and it fails it in
  all three: the statement itself says `a.plus(x, a.zero)`, so the name is in
  the *type*, before the body exists. No placement helps; only a form where
  naming is cheap does. (7) is the only finalist whose named form is shorter
  than today's.

### F. Recommendation

**Primary: (7), the in-list `infer` marker with an optional name.**

```
param := "infer" (name ":")? classref     -- anonymous allowed
       | "infer" name ":" type            -- the general goal, named
       | … today's productions …
```

One keyword, one position, name optional, and — the reason it wins — it is the
*same* production for a class constraint and for `hx: x > 0`, which is the one
thing `docs/traits-design.md` §8 and `docs/traits-layer2-design.md` §1 both
insist is true and which no other candidate lets the source show. It fixes the
filed complaint (the arguments come first, the head is not a wall), it keeps
`{` on the signature line (the objection to (2)), it is quiet at one constraint
and tidy at three (the objection to (3)), it makes anonymity a word-drop rather
than a second form (the wanted feature), it interleaves so the dependent case
is written in elaboration order (the reason (1) existed), and it needs no new
bracket, no new arrow, and no second meaning for the colon (the objections to
(3), (9), (4), (6)). Costs, stated plainly: `requires` disappears from function
and theorem signatures while remaining the `instance` head's clause (§A.4) —
one word in two roles, which is better than one meaning in two brackets — and
`:= infer` should be **retired in favour of the prefix marker** rather than
kept as an alias, which costs `or_default` plus the `:= infer` tests. That is
the entire migration: six declarations in `lib/std/algebra.hthr`, ~21 signature
occurrences across `crates/elab/tests/*`, `crates/cache/tests/end_to_end.rs`
and the frontend bench fixtures, and the `instance` heads untouched.

**Secondary, composable, and vetoable: (4) as sugar for the anonymous
single-constraint case**, `fn sum<A, Monoid<A>>(…)` desugaring to a leading
`infer Monoid<A>` parameter, and `instance<A, Monoid<A>> Monoid<List<A>>`
desugaring to today's `requires`. It is genuinely the best reading for the
zero-projection case (`sum`, `all_of`, `concat`) and it is the only form that
also serves the instance head. **But it should not ship in the same round**: it
is a second spelling, its named form drags in the colon overload, and it owes
an answer to the explicit-type-application arity check (§D). Ship (7), write
`lib/std/algebra.hthr` in it, and let a later round decide whether the
grouped form earns its keep as sugar with a *no-name* restriction (class
reference only, never `<A, m: Monoid<A>>`) — which removes both of its costs
at once and leaves it doing exactly the one job it is best at.

**Rejected outright**: (5), (6), (9), (10), (11), and the two-spellings
option (d) of the problem statement.

## Syntax exploration round 2 (2026-08-07): unconstrained

Round 1 was too deferential — to today's grammar and to today's library. This
round throws both constraints away. **No candidate below is judged on whether
`crates/syntax/src/parser.rs` can parse it today**; where a collision exists it
is a one-line footnote in §R2-G, never an argument. Round 1's rejections of
`<A: Monoid>`, `=>` and `(using …)` on parser grounds are **void**.

The axis is re-weighted, per the review: **unobtrusiveness at scale is
primary**. A typeclass constraint is background information — "let `A` be a
monoid" — and background information should occupy the least space the reader
can still find it in. Round 1's finding (four of six declarations project by
name) is a fact about a library that is currently *all* core algebra; ordinary
downstream code skews anonymous, and the right response is not a syntax that
makes naming cheap but a syntax that makes naming **unnecessary** — see §R2-C,
which turns out to be where most of the leverage is.

### R2-A. `<A: Monoid>`, taken seriously

The reading the user names is the right one and is worth stating as the design
principle: **`A: Monoid` is the same sentence as `A: Type<1>`.** Both answer
"what is `A`?" — one says it is a type at a level, the other says it is a
monoid. Mathematics writes them identically ("let `A` be a set", "let `A` be a
monoid") and never feels the need for two punctuation marks. So the colon does
not acquire a second meaning; it acquires a second **noun**.

How the reader tells them apart: by what follows, and nothing subtler. `Type`
and `Type<n>` are the universe nouns; every other name after `:` is a class.
They are also *distinguishable in kind*, which is the honest version of the
claim: a universe annotation says **where `A` lives** (it is a sort), a class
annotation says **what `A` carries** (it is a structure). A binder can have
both, and the natural spelling makes them a list of facts:

```heather
fn mconcat<A: Monoid>(xs: List<A>) -> A
fn lift<A: Type<1> + Monoid>(xs: List<A>) -> A       -- level and structure
fn sort<A: Cmp + Monoid + Default>(xs: List<A>) -> List<A>
```

`+` reads "and", stacks without ceremony, and is one token — the objection
round 1 raised against it ("this language has no `+`") is exactly the kind of
objection this round is not allowed to make.

**The two cases the sugar cannot state, and the clause that states them.** The
inline form works when the constrained thing *is* the binder. It is not, for
`Monoid<List<A>>` (a constraint on a compound type) or for a class whose
carrier is not its only parameter. The answer is to notice that the inline form
is not the feature — the feature is a **constraint sentence**, `T: C`, and the
inline form is that sentence written at the binder because `T` happens to be the
binder. Everything else writes the same sentence in a clause:

```heather
fn flatten<A>(xss: List<List<A>>) -> List<A>
    given List<A>: Monoid                       -- carrier is compound
{ … }

fn convert<A, B>(x: A) -> B
    given A: Coe<B>                             -- extra parameters, carrier first
{ … }

fn back<A, B>(x: A) -> B
    given B: Coe<_, A>                          -- `_` IS the binder's slot
{ … }
```

Three rules and no exceptions: `A: C` means `C<A>`; `A: C<X, Y>` means
`C<A, X, Y>`; and `_` moves the carrier to whichever slot it is written in
(`B: Coe<_, A>` is `Coe<A, B>`). The inline sugar is then defined as literally
"the clause sentence, hoisted to the binder when its subject is that binder" —
one production, two placements, and the second placement is a *rewrite*, not a
second feature. That is what round 1's option (d) got wrong: two spellings of
one thing is a cost only when neither is defined in terms of the other.

**Recovering a name**, three levels, cheapest first:

1. **Don't.** §R2-C makes `A.unit`, `A.op(x, y)` and `x.op(y)` work without a
   dictionary name ever appearing. This is the case that should dominate.
2. **Canonical path.** `A::Monoid` is the dictionary, by the *existing*
   notation — `lib/std/algebra.hthr` already writes `Nat::AddCommMonoid.plus`
   for a registered instance, and extending that path to a constrained binder
   is not new syntax at all, just a new thing a path can name. `A::Monoid.unit`
   is available always, needs no declaration, and is unambiguous under two
   constraints.
3. **`as`, when a short name genuinely helps.** `<A: Monoid as m>`,
   `given List<A>: Monoid as ml`. Reads as English, costs five characters, and
   is *never required* — which is the point.

**Bracket arity is untouched**, and this is `<A: Monoid>`'s decisive advantage
over round 1's grouped generics `<A, Monoid<A>>`: the constraint is an
*annotation on an entry*, not an entry, so `mconcat<Nat>(xs)` still has exactly
one type argument and the declaration bracket and the call bracket keep saying
the same thing. Round 1's arity objection was to grouped generics specifically;
it does not touch this form.

**The remaining honest weirdness**, stated rather than argued away: an
autofilled *value* is being introduced by an annotation that looks purely
descriptive. `<A: Monoid>` adds a runtime argument to the function, and nothing
in the notation says so. Every language that has this feature has this problem
(Haskell's `=>`, Rust's `:`, Scala's `using`), and the two mitigations are
(i) §R2-C's projections, which make the added value visible at *use* sites
where it matters, and (ii) `@mconcat(m, xs)` continuing to pass it positionally,
which is where a writer learns it was there all along.

### R2-B. Eleven new candidates

Numbering continues from round 1.

- **(12) Section / context variables** — `given` declared once for a file
  region; signatures stop repeating it.
- **(13) Named constraint bundles** — `context Sortable<A> = Cmp + Monoid + Default;`
  then `<A: Sortable>`.
- **(14) Functor-flavored module parameters** — the whole file is inside the
  monoid: `module fold<A: Monoid> { … }`.
- **(15) Dictionary opening in bodies** — `open A::Monoid;` brings `unit`,
  `op`, `assoc` into scope as bare names.
- **(16) Constraint at the use site inside a type** — `xs: List<A: Monoid>`.
- **(17) Implicit generalization** — no binder bracket at all; an unbound
  capitalized name in a parameter type binds itself, and its constraint rides
  along: `fn mconcat(xs: List<A: Monoid>) -> A`.
- **(18) Constraints as a row on the arrow** — `fn sum(xs: List<A>) -> A ! Monoid<A>`,
  dictionary-passing treated as the reader effect it is.
- **(19) The footnote line** — the constraint clause committed to its own
  indented line under the signature, mathematician-style, brace after it.
- **(20) Constrained regions** — `for<A: Monoid> { fn mconcat … fn sum … }`,
  a bracketed section.
- **(21) Extension blocks** — generic consumers declared *inside* the class's
  own region: `extension<A: Monoid> { fn mconcat(xs: List<A>) -> A { … } }`,
  with receiver dispatch doing the calling.
- **(22) Constraint inference** — no syntax whatsoever; the elaborator infers
  the context from the body and *prints* it into the interface.
- **(23) Type-level dot projection** — not a placement at all but the thing
  that makes placements cheap: `G.zero`, `A.op(x, y)`, `A.unit`.

### R2-C. (23) first, because it changes the scoring

A constrained type variable **is** a structure, so let it be projected like
one. If `<G: AddCommMonoid>` is in scope, `G.zero` is that structure's zero and
`G.plus(x, y)` its addition — dot on a *type*, resolving through the
constraints that type carries.

```heather
theorem plus_zero_of_comm<G: AddCommMonoid>(x: G): G.plus(x, G.zero) = x {
    trans(G.plus_comm(x, G.zero), G.zero_plus(x))
}
```

Compare today's `a.plus(x, a.zero)`: identical length, and the dictionary name
is gone. Three things fall out:

- **It generalizes the notation the library already has.** `Nat::AddCommMonoid.plus`
  is what a concrete carrier writes today; `G.plus` is the same projection with
  the class inferred from the single constraint that provides that field. A
  concrete carrier can use it too — `Nat.plus`, `Bool.zero` — which is a
  readability win the library would take immediately.
- **Ambiguity is the existing rule, not a new one.** Two constraints providing
  the same field name is exactly receiver dispatch's ambiguity, already decided
  (`docs/traits-receiver-dispatch-design.md`: name both readings, never pick),
  and the escape is already spelled: `G::AddCommMonoid.plus`.
- **It retires the naming problem that dominated round 1's scoring.** All four
  of the library's name-projecting declarations become anonymous:
  `m.unit` → `A.unit`, `m.unit_r(x)` → `A.unit_r(x)`, `c.le_refl(x)` →
  `A.le_refl(x)`, `a.plus_comm` → `G.plus_comm`. **Zero** of the six then need
  a binder name. The round-1 empirical finding was not wrong; it was a finding
  about a language that could not project from the carrier.

This is orthogonal to placement and composes with every candidate below, which
is why it is written first: it is worth more than the placement decision.

### R2-D. The other ten, developed and judged

**(12) Section variables.** Lean's actual answer to signature noise, and the
one that scales sublinearly: declare once per region, every declaration in the
region that needs it gets it.

```heather
section {
    given A: Monoid;

    fn mconcat(xs: List<A>) -> A { match xs { Nil => A.unit, Cons(h, t) => h.op(mconcat(t)) } }
    theorem mconcat_single(x: A): mconcat(Cons(x, Nil)) = x { A.unit_r(x) }
}
```

The danger is Lean's, precisely: `variable` inclusion is folklore, the rules
changed across versions, and "which variables did this theorem actually get" is
answered by reading the elaborator. **The discipline that makes it shippable
here is a syntactic one**: a `given` binder is included **iff the declaration's
own signature mentions it**, never on the strength of the body. `A` is
mentioned by `List<A>`; `A: Monoid` rides along because `A` did. Body-driven
inclusion is refused outright — it makes a signature depend on a proof, which
this project's determinism and interface-stability doctrine cannot accept.
With that rule the elaborated signature is a function of the signature text,
printable and diffable. **This is the highest-leverage candidate after (23)**:
it is the only one whose cost per constraint *decreases* with library size, and
`lib/std/algebra.hthr`'s consumer section is exactly the shape it is for.

**(13) Named bundles.** `context Sortable<A> = Cmp + Monoid + Default;` and
then `<A: Sortable>` everywhere. Crucially **not a class**: no instance, no
coherence key, no registry entry — a macro over constraint sentences, expanded
at the binder. That distinction is the whole design, because a *class* with
three parents would drag in the flattening ambiguity the library already hit
(`Monoid` is declared flat for that reason), whereas a bundle introduces no
fields and therefore no member can be inherited twice. Cheap, obvious, and it
is the honest answer to the three-constraint `merge` signature. Cost: a second
namespace of things that can appear after `:` — mitigated by requiring bundles
to be declared, so a name after `:` is a class or a declared bundle, never a
guess.

**(14) Functor modules.** `module fold<A: Monoid> { … }`, instantiated
`fold<Nat>`. Genuinely the ML answer and genuinely more than this needs: it
makes the *module* the unit of parameterization, so every use site names the
instantiation, which is precisely the ceremony typeclasses exist to remove. It
also collides with `docs/modules-design.md`'s file-is-a-module design at the
root. **Reject as the mechanism**, but note what it gets right — that the
constraint belongs to a *region*, not to each declaration — which is (12) and
(20) with less machinery.

**(15) Opening dictionaries in bodies.** `open A::Monoid;` puts `unit`, `op`,
`assoc`, `unit_l`, `unit_r` in scope bare. The elegance is real and the
ambivalence is warranted, and this library has already paid the exact tax
twice, in writing: `Cmp`'s field is `le` and not `leb`, `AddSemigroup`'s is
`plus` and not `add`, both times because a field sharing a name with an ambient
global becomes unreachable — and the receiver-dispatch round's shadow test
caught a class field named `map` swallowing every list's `map`. `open` takes
that hazard, which today is a *naming* decision made once per class by the
library author, and hands it to every function body. Verdict: **allowed,
scoped, opt-in, and reported** — an `open` that shadows any name in scope is an
error naming both, not a silent win. With (23) in hand its value drops sharply
anyway: `A.unit` is one character longer than `unit` and cannot capture
anything. **Keep as a body-side convenience, never as the answer to placement.**

**(16) Use-site constraint in a type.** `fn mconcat(xs: List<A: Monoid>) -> A`.
Reads like set-builder notation and puts the constraint at the point of use,
which is where a reader first wonders about it. Two problems, one fatal on its
own: if `A` occurs twice the constraint has two homes and the reader must know
they are the same one; and the *return* type `-> A` now depends on a binder
introduced inside a parameter type, so scope flows leftward out of a bracket.
Fine as a **sugar for exactly one occurrence**, which is what (17) makes of it.

**(17) Implicit generalization.** The maximally unobtrusive candidate: an
unbound name in a signature binds itself, so the bracket disappears entirely.

```heather
fn mconcat(xs: List<A: Monoid>) -> A { … }
fn merge(xs: List<A: Cmp + Monoid + Default>, ys: List<A>) -> List<A> { … }
```

Haskell, Idris and Lean's `autoBound` all do this, and all three regret pieces
of it: a typo becomes a new type variable rather than an error, and the
declaration's arity stops being visible in its own text. The second is the one
that matters here, because `f<Nat>(…)` explicit type application is positional
against a list the reader can no longer see. **Reject as the default**; note
that if the project ever wants it, it wants it with the diagnostic that a
single-use unbound name is a warning naming the two spellings.

**(18) Effect row.** `fn sum(xs: List<A>) -> A ! Monoid<A>` — constraints as
the reader effect they mathematically are. Honest, and it is the only
placement whose *type* changes visibly at the arrow, which is the thing
`<A: Monoid>` was accused of hiding. But it introduces a third concept
(effects) into a language that has none, to spell a feature that already has a
home; and it puts the constraint after the return type, where round 1 already
found the brace problem. **Reject**, with the note that the day Heather has
effects, this is where instance constraints belong.

**(19) The footnote line.** Turn round 1's objection into the design: the
clause is *supposed* to be on its own line, and the brace after it.

```heather
theorem merge_sorted<A>(xs: List<A>, ys: List<A>): sorted(merge(xs, ys)) = True
    given A: Cmp + Monoid + Default
{ … }
```

This is how a paper prints a theorem — statement, then "where `A` is an ordered
monoid", then the proof — and it is the *general* clause from §R2-A given a
canonical layout. Strong as the fallback form; weak as the only form, because
one constraint should not cost a line.

**(20) Constrained regions.** `for<A: Monoid> { … }` — (12) with a bracket
instead of a keyword, and with the inclusion question answered by construction
(everything inside gets it, mentioned or not). That is its advantage over (12)
and its disadvantage: a declaration in the region that does not use `A` gets a
spurious parameter, so the region must be drawn tightly. **Keep as (12)'s
sibling**; if `given` inclusion rules prove hard to explain, this is the
retreat that needs no rules at all.

**(21) Extension blocks.** Declare generic consumers inside the class's region:

```heather
extension<A: Monoid> {
    fn mconcat(xs: List<A>) -> A { … }
    theorem mconcat_single(x: A): mconcat(Cons(x, Nil)) = x { … }
}
```

Which is (20) wearing a name that says what the region is *for*, plus an
implied home for receiver-dispatched members. It is the most Rust-shaped
answer, and its cost is that it wants to become the *only* way to write generic
code — at which point unconstrained helpers and constrained ones live in
different syntactic worlds for no semantic reason. **Merge into (20)/(12)**.

**(22) Constraint inference.** The wackiest and worth stating properly: the
elaborator already computes exactly which dictionaries a body needed; it could
simply *not require* the signature to say so, and print the inferred signature
as data (this project's diagnostics doctrine makes that a `heather sig`
command, not a mystery). Haskell shows the failure mode — inferred contexts
make a public API change silently when a body changes — and this project has a
certified cache whose keys are interfaces, so a body-driven signature is a
correctness-adjacent hazard, not merely a style one. **Reject for public
declarations. Note for local ones**: a nested `fn` inside a body, whose
interface nobody outside can depend on, is a legitimate place to infer, and it
is the same principle as (12)'s ban on body-driven inclusion applied to a scope
where there is no interface to destabilize.

### R2-E. Test drives

**(6′) `<A: Monoid>` + (23) alone:**

```heather
fn mconcat<A: Monoid>(xs: List<A>) -> A {
    match xs { Nil => A.unit, Cons(h, t) => h.op(mconcat(t)) }
}
fn sum<A: Monoid>(xs: List<A>) -> A { mconcat(xs) }
fn or_default<A: Default>(o: Option<A>) -> A { unwrap_or(o, A.default) }
theorem plus_zero_of_comm<G: AddCommMonoid>(x: G): G.plus(x, G.zero) = x { … }
fn merge<A: Cmp + Monoid + Default>(xs: List<A>, ys: List<A>) -> List<A> { … }
fn flatten<A>(xss: List<List<A>>) -> List<A> given List<A>: Monoid { … }
```

Two structures on one carrier, the case that forces names — the second monoid
is a *value*, exactly as the library's coherence policy says, and it stays an
ordinary parameter:

```heather
theorem xor_via<A: Monoid>(m2: Monoid<A>, x: A): A.op(x, A.unit) = m2.op(x, m2.unit) { … }
```

The asymmetry is the honest one: the registered structure is anonymous because
it is canonical; the second is named because a reader must be told which is
which.

**(12) section variables, whole-file sketch** — the consumer half of
`lib/std/algebra.hthr` as it would read:

```heather
section {
    given A: Monoid;

    fn mconcat(xs: List<A>) -> A { match xs { Nil => A.unit, Cons(h, t) => h.op(mconcat(t)) } }
    theorem mconcat_single(x: A): mconcat(Cons(x, Nil)) = x { A.unit_r(x) }
}

section {
    given A: Cmp;

    fn max_of(x: A, y: A) -> A { cmp_pick(x.le(y), x, y) }
    theorem max_of_true(x: A, y: A, p: x.le(y) = True): max_of(x, y) = y { … }
    theorem max_of_self(x: A): max_of(x, x) = x { max_of_true(x, x, A.le_refl(x)) }
}
```

Ten lines, and the word `Monoid` appears once for two declarations, `Cmp` once
for three. At `std`'s current size that is a small win; at a library with
twenty lemmas per class it is the difference between a file about algebra and a
file about dictionaries. Note `sum`, `all_of`, `concat` sit *outside* both
sections and are unaffected — the inclusion rule ("mentioned in the signature")
means a section costs nothing to the declarations that ignore it.

**(13) bundles, the three-constraint case:**

```heather
context Sortable<A> = Cmp + Monoid + Default;

fn merge<A: Sortable>(xs: List<A>, ys: List<A>) -> List<A> { … }
fn sort<A: Sortable>(xs: List<A>) -> List<A> { … }
theorem sort_idem<A: Sortable>(xs: List<A>): sort(sort(xs)) = sort(xs) { … }
```

**The combination, all three, formatted:**

```heather
context Sortable<A> = Cmp + Monoid + Default;

section {
    given A: Sortable;

    fn merge(xs: List<A>, ys: List<A>) -> List<A> { … }
    fn sort(xs: List<A>) -> List<A> { … }
    theorem sort_idem(xs: List<A>): sort(sort(xs)) = sort(xs) { … }
}

// and the one-off, outside any section, with a compound carrier:
fn flatten<A>(xss: List<List<A>>) -> List<A>
    given List<A>: Monoid
{ … }
```

Three constraints, three declarations, and the word "Cmp" is written once in
the file. That is what unobtrusiveness at scale looks like.

### R2-F. Recommendation (round 2)

**A combination, in this order of value:**

1. **(23) type-level dot projection — `A.unit`, `G.plus(x, y)`.** Ship this
   whichever placement wins. It removes the binder *name* from every real
   declaration in the library, which is what makes anonymous-by-default a
   default rather than an aspiration, and it is a generalization of a notation
   the library already writes (`Nat::AddCommMonoid.plus`) rather than a new
   idea. Its ambiguity rule is receiver dispatch's, already decided.
2. **(6′) `<A: Monoid>` as the constraint sentence, inline** — with `+`
   stacking, `as m` for the rare name, `A: C<X>` / `A: C<_, X>` for extra
   parameters, and the identical sentence available as a **`given` clause**
   (§R2-A, laid out per (19)) whenever the subject is not the binder. One
   production, two placements, the second defined as a hoist of the first. The
   colon keeps one meaning — "what `A` is" — with universes and classes as two
   nouns under it, and the type-argument bracket keeps its arity, which is the
   concrete advantage over grouped generics.
3. **(12) `given` section variables**, with the syntactic inclusion rule
   (mentioned in the *signature*, never inferred from the body), and (20)
   `for<…> { }` held in reserve if the rule proves hard to teach. This is the
   only mechanism whose cost per constraint falls as the library grows.
4. **(13) bundles** when the same triple recurs — a macro over sentences, never
   a class, so it can introduce no field and therefore no ambiguity.
5. **(15) `open`** as a body-side convenience only, opt-in and shadow-reporting,
   and honestly less needed once (23) exists.

Rationale in one sentence: **background information should be written once and
projected from, not carried** — (23) removes the name, `<A: Monoid>` removes
the clause, `given` removes the repetition, and each of the four is defined in
terms of the same constraint sentence, so the reader learns one idea and meets
it in four positions rather than learning four features.

Explicitly **not** recommended: round 1's `infer` marker (correctly judged too
obtrusive — it makes the background the foreground on every signature line);
grouped generics (bracket arity); implicit generalization (17) and inference
(22) as defaults (interface stability); effect rows (18) until there are
effects; functor modules (14) (use-site ceremony is the thing being removed).

**Staging, if it helps**: (23) and (6′) inline are one round and would let
`lib/std/algebra.hthr` be rewritten immediately; the `given` clause is the same
round's fallback form for `flatten`; sections and bundles are a second round
that needs no syntax the first did not already introduce.

### R2-G. Implementation footnotes (not evaluation criteria)

Recorded only so the eventual round is not surprised, in one line each:
`:` in the tyvar list currently means a universe (`parser.rs:579–588`) — the
disambiguation is "is the next token `Type`"; `+` is not a token today;
`given`/`context`/`section`/`for`/`open`/`as` are all unused words and every
keyword in this grammar is contextual anyway; type-level dot (23) needs `A.f`
where `A` is a type binder, which the receiver-dispatch path already has the
resolver call for; a `given` clause between the return type and the block is
the same `no_record_lit` situation round 1 already checked. None of these
changed a judgement above.

## Log

- 2026-08-07: 2026-08-07: User review: ANONYMOUS binders are wanted regardless of placement (Lean experience: the dictionary is rarely referenced by name). Trailing clause tempts but encourages brace-on-own-line; in-list bracketed `[Monoid<A>]` reads naturally in multi-line parameter lists but is visually noisy; NEW option from the user: grouping in the generics list — `fn sum<A, Monoid<A>>(xs: List<A>) -> A` — typeclasses beside the type they constrain (Lean-ish grouping), at the cost of conflating a binder name and a class reference in one bracket; `fn sum<A>[Monoid<A>](…)` considered and disliked. Instance shorthand SPLIT OUT to [[instance-shorthand-syntax]]. A brainstorm round is tasked with widening the option space and evaluating against real library signatures, writing its analysis into this issue; decision after that.
- 2026-08-07: Exploration landed above (11 candidates, parser claims checked, top three test-driven on the real `algebra.hthr` signatures). Recommends the **in-list `infer` marker with an optional name** — `fn mconcat<A>(infer m: Monoid<A>, xs: List<A>) -> A`, anonymous `infer Monoid<A>` — retiring `:= infer` into it, with the user's grouped generics offered as a later, name-free sugar; key finding: four of the library's six constrained declarations project the dictionary by name, so the *named* form is the common one and must be the short one.
- 2026-08-07: Round 2 (unconstrained — parser reality demoted to footnotes, unobtrusiveness-at-scale made the primary axis) landed above: eleven new candidates, `<A: Monoid>` rehabilitated and developed (constraint *sentences* `T: C`, `+` stacking, `C<X>`/`C<_, X>` for extra parameters, `given` clause when the subject is not the binder, `as m` for the rare name, bracket arity untouched). Recommends a **combination**: (23) type-level dot projection `A.unit` / `G.plus(x, y)` — which removes the binder name from all six library declarations and is a generalization of the existing `Nat::AddCommMonoid.plus` path — plus `<A: Monoid>` inline with the `given` clause as its general form, plus `given` section variables (syntactic inclusion rule only) and named bundles for repetition; `open` kept as a body-side convenience. Round 1's `infer` marker withdrawn as too obtrusive.
