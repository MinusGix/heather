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

## Log

- 2026-08-07: 2026-08-07: User review: ANONYMOUS binders are wanted regardless of placement (Lean experience: the dictionary is rarely referenced by name). Trailing clause tempts but encourages brace-on-own-line; in-list bracketed `[Monoid<A>]` reads naturally in multi-line parameter lists but is visually noisy; NEW option from the user: grouping in the generics list — `fn sum<A, Monoid<A>>(xs: List<A>) -> A` — typeclasses beside the type they constrain (Lean-ish grouping), at the cost of conflating a binder name and a class reference in one bracket; `fn sum<A>[Monoid<A>](…)` considered and disliked. Instance shorthand SPLIT OUT to [[instance-shorthand-syntax]]. A brainstorm round is tasked with widening the option space and evaluating against real library signatures, writing its analysis into this issue; decision after that.
- 2026-08-07: Exploration landed above (11 candidates, parser claims checked, top three test-driven on the real `algebra.hthr` signatures). Recommends the **in-list `infer` marker with an optional name** — `fn mconcat<A>(infer m: Monoid<A>, xs: List<A>) -> A`, anonymous `infer Monoid<A>` — retiring `:= infer` into it, with the user's grouped generics offered as a later, name-free sugar; key finding: four of the library's six constrained declarations project the dictionary by name, so the *named* form is the common one and must be the short one.
