# One sequencing surface: binding over a carrier, local state and loops

Status: **proposal, for Minus's decision.** Round R1 of
`docs/compiler-milestones-proposal.md` (§3, §7; milestone `lang-sequencing`),
issue `issues/sequencing-surface-design.md`. Written on master `3099a7d`.
Nothing here is built. §11 lists the decisions, §12 what R2 and R3 take from
this note.

Constraints from Minus's decisions on the proposal (2026-10-31), not
reopened here:

- Binding works for **any type with a `bind`**, not only named monads.
- Interface definitions are **opt-in** (`issues/proof-modularity-design.md`
  owns them; §7.4 says what this surface hands them).
- Ownership is the leaning second `runtime fn` setup, decided later. The
  surface stays setup-neutral (§8.3).
- The sugar covers `let x <- e;`, `let mut`, `:=`, `for`/`while` and early
  exit, and **lowers to folds**. The goal is less painful composition and
  imperative-style code.

Standing constraints from earlier rounds: `=` is equality and the `let`
binder, and `:=` is held for assignment (`docs/let-and-blocks-design.md`
§3.1, `issues/effects-direction.md` 2026-07-24). Interleaved statements were
deferred until a statement means something (`docs/let-and-blocks-design.md`
§4.5). Users never write or prove against a monadic elaboration target for
effects (`issues/effects-direction.md`, "Avoid").

**No kernel change and no trusted rule.** Every form lowers to a term that
can be written by hand today: a `bind` call, a `List::foldl`, a `decreases`
function. The elaborator checks that term like any other.

---

## 0. The proposal in one page

```heather
// Layer 1: binding over a carrier. The carrier is the owner of the block's
// expected type (`Tac`), and `let x <- e;` is `e.bind(λ x => …)`.
fn mono_run(…) → Tac<Mono> {
    let triv <- mono_global("mono_trivial");
    let truth <- infer(Global(triv)).or_fail("mono: ");
    Pure(Mono(le, lt, rf, weaken, laws, signs, pushes, given, truth, triv))
}

// Layer 2: local state and loops in a pure function. The loop's body
// becomes the named step `count_words::step`, the two locals its state, and
// the loop is `bytes.foldl(count_words::step, …)`.
fn count_words(bytes: List<BitVec(8)>) → Nat {
    let mut words = 0;
    let mut inside = False;
    for b in bytes {
        if b.is_space() { inside := False }
        else if !inside { inside := True; words := words + 1 }
    }
    words
}
```

1. **The carrier protocol is a pair of owner members, not a class**
   (§2). A carrier is a named type `M` with `M::bind(self m, k)`, and
   `M::pure(a)` where a form must inject a value. The block's carrier is the
   owner of its expected type, or else of its first bound expression. The
   lowered term is the hand-written `bind` tower exactly, so a port changes
   no kernel term. A class cannot be written: type constructors are not
   values in Heather (probe P1).
2. **The spelling is `let x <- e;`** (`←` too), with `e;` for a discarded
   result and `(<- e)` for a nested bind. A nested bind runs before the
   statement it is in, in written order, and never leaves a match arm, an
   `if` branch or a λ (§3).
3. **Layer 2 is one elaborator pass over a statement scope** (§4, §5).
   Mutable locals become SSA aliases. Each loop becomes a **named step
   function** over the locals it assigns. A `for` with no early exit is
   `Owner::foldl`, a `for` with one is `Owner::for_in`, `while … decreases`
   is a generated `decreases` function, and `while … fuel` a structural one.
4. **What proofs see** (§7): `f_unfold` (the function equals its lowered
   body, by `refl`), the step function by name, and a handful of **library**
   theorems about `foldl`/`for_in`, not per-loop generated ones. The
   `while` form's unfolding equation needs `unfolding-computed-scrutinee`
   first (probe P5).
5. **The effects case is layer 2, not layer 1** (§8). A capability is a
   `let mut` local, and a method with a `mut self` parameter reassigns it.
   That is the world-threading reading `effects-direction` decided, with no
   monadic type in the user's code.
6. **`?` becomes a special case of `return`** inside loops (§6.3), and
   `Option` gets `?` and a carrier (§3.5).

---

## 1. What the library writes today

Counted on `3099a7d`.

- **`lib/std/tactic`: 517 `.bind(λ` sites.** `cast` has 115, `norm_num`
  76, `mono` 71, `interval_tactic` 46 and `tactic` 45. **185 of them
  (36%) match on the bound value at once** (`bind(λ c => match c {`). Most
  of those split a `Checked<A>`. 34 turn `Refused(why)` into
  `fail(prefix ++ why, [])`, and 20 more turn it into a default
  (`Pure(None)`, `leaf`).
- **Towers are recursions over lists.** `mono_laws`, `mono_signs` and
  `mono_class_laws` walk a list and bind two lookups per element.
  `mono_pushes` binds four `Option`s and then matches all four by hand. That is
  a `Tac` chain and an `Option` chain in the same expression.
- **Pure algorithms are written against fuel.** `lib/std/text/decimal.hthr`'s
  `decimal_digits(fuel, n)` uses fuel because `decreases` over a
  `match n.leb(9)` gets no unfolding equation
  (`issues/unfolding-computed-scrutinee.md`, log of 2026-09-25).
- **Step functions are what the native proofs want.**
  `docs/native-programs-read-like-programs-design.md` §1.1 proves `wc`'s
  facts with one line per field of `wc_step`. The native loop compiler takes
  folds of a step (`fold_bytes`, `lib/native/function_ir/function_ir_loop.hthr`),
  and `decreases` word functions compile to verified loops against `f#rec`.

## 2. The carrier protocol

### 2.1 Owner members, and why not a class

A **carrier** is a type whose head is a name `M`, an inductive, record,
codata type or type-former `fn`, with:

```heather
fn M::bind<…>(self m: M<…A…>, k: A → M<…B…>) → M<…B…>   // required
fn M::pure<…>(a: A) → M<…A…>                            // where §5 needs it
```

Every other parameter is implicit. The protocol does not say where `A`
sits in `M`'s arguments: `Result<A, E>` puts it first, `Parser<T, A>` last,
and `ITree<A>(E)` has a value parameter after it. The elaborator never needs
to know, because it only builds the two calls and checks them.

**Why not a class `Monad<M>`.** It cannot be stated. Class parameters are
types, and a type constructor is not a value: `class Bind<M: Type → Type>`
does not parse, and passing `Option` where `Type → Type` is expected is
refused with "`Option` cannot be used here" (probe P1). Type parameters are
monomorphized (`docs/traits-layer2-design.md` §3.1), so making constructors
first-class would be a language round of its own. It would buy laws as class
fields. No customer here wants those: tactics and parsers are not proved
lawful, and where a proof wants a law, a theorem about `M::bind` states it.

**What owner members buy.**

- **The lowered term is the hand-written term.** `let x <- e; rest` becomes
  `M::bind(e, λ x => rest)`, which is what `e.bind(λ x => rest)` resolves to
  today. It has no dictionary and no projection to unfold. That matters for
  closed evaluation: `docs/native-programs-read-like-programs-design.md` §2
  found that an instance arrives as an unreduced projection. Porting `mono`
  therefore changes **no kernel term**, and R2 can prove that with
  `scripts/timings --diff`: identical count columns before and after.
- **It is Minus's "any type with a `bind`"**, read literally. No
  declaration has to opt in beyond having the member.
- **Resolution already exists.** Owner-by-head resolution
  (`docs/receiver-member-resolution-design.md` §1) finds `M` from a call's
  declared result type without inferring the receiver, which covers
  `fail(…)`, `Pure(x)` and `goal()`.

### 2.2 Which carrier a block uses

A **statement scope** is a declaration body or a block expression. The
bodies of the statement forms of §4 (`for`, `while`, a statement `if` or
`match`) belong to the scope around them. A block expression in value
position, and a λ body, open a new scope.

A scope is a **carrier scope** when it contains `let … <- e;`, a nested
`(<- e)`, or an expression statement `e;`, including inside its loop and
`if` bodies. A `mut self` call on a `let mut` local (§8.2) is not counted:
it is an assignment, so it discards nothing. Its carrier is, in order:

1. the owner of the scope's **expected type**, when the scope is checked
   (a `fn` body whose result is `Tac<Expr>` has carrier `Tac`);
2. otherwise the owner of the **first bound expression's type**, found by
   owner-by-head resolution, or by inference when that declines.

Every bind in the scope uses that one carrier. A statement whose
computation has another carrier is a type error at that statement, and the
note says so: "this computation is an `Option`, but the block's carrier is
`Tac`". Nothing is lifted automatically. To use another carrier, write a
block expression at its own type:

```heather
Pure({ let x <- ga; let y <- gb; Some(Pushes(x, y)) })   // an Option block inside a Tac block
```

A pure scope, with none of the three forms, is exactly today's block.

### 2.3 What the library adds

R2 adds the members its customers lack. Each is a one-liner:
`Tac::pure`, `Option::bind`, `Option::pure`, `Result::bind`, `Result::pure`
(beside `and_then`, which stays), and `Parser::pure` (today a free `pure` in
`parser_combinators`). `ITree::bind` takes its event signature explicitly,
so it gets a `self` form with `E` implicit. Also `Tac::or_fail(self t:
Tac<Checked<A>>, prefix: String) → Tac<A>`, which retires the 34
`Refused(why) => fail(…)` matches as a library function rather than a
syntax.

## 3. Layer 1: binding statements

### 3.1 Forms

```heather
let x <- e;              // M::bind(e, λ x => rest)
let x: A <- e;           // the binder annotated; e is checked at M<…A…>
let { a, b } <- e;       // bind, then destructure the record (docs/named-patterns-by-field-design.md §2)
let _ <- e;              // discard, explicitly
e;                       // discard: M::bind(e, λ _ => rest)
f(<- e, y)               // nested bind: let t <- e; f(t, y)
match <- e { … }         // the same, at a scrutinee
```

`←` is accepted for `<-`, as `→` is for `->`. The lexer makes `<-` one
token after `<->` (which is already one, `crates/elab/tests/logic.rs:327`).
No source in `lib/`, the showcase or the tests writes `a<-b` for `a < -b`
(grepped).

**A discarded result** whose type is not `True` gets a lint that names the
type and suggests `let _ <- e;`. `restore(m);`, which returns
`Tac<True>`, is silent.

**`let x = e;` stays pure** in a carrier scope. It binds `e` itself, so
`let t = goal();` binds the computation. That is the right reading, and the
lint for an unused `let` already catches the slip of forgetting the arrow.

### 3.2 Nested binds

`(<- e)` is the binding counterpart of `?`, and it reuses the same
expansion: `docs/result-propagation-design.md` lowers `K[e?]` to
`and_then(e, λ v => K[v])`, and `K[(<- e)]` lowers to `M::bind(e, λ v =>
K[v])`. The rules are the ones `?` already has, for the same reasons:

- **written order**: several nested binds in one statement run left to
  right, in reading order;
- **arm-local**: a nested bind inside a `match` arm or an `if` branch runs
  in that arm, only when the arm is taken. This is the point where Lean 4's
  `(← e)` is a known trap: Lean hoists out of an `if` branch, so the action
  runs whether or not the branch is taken. Here it does not hoist;
- **a λ is a boundary**: `(<- e)` inside a λ needs a carrier scope inside
  that λ.

The 185 bind-then-match sites become `match <- view(h) { … }`.

### 3.3 What a port looks like

Today's `mono_pushes` (`lib/std/tactic/mono.hthr`):

```heather
Some(n) => mono_try_global(n.le_l).bind(λ ga => mono_try_global(n.le_r).bind(λ gb => mono_try_global(n.lt_l).bind(λ gc => mono_try_global(n.lt_r).bind(λ gd =>
    Pure(match ga { None => None, Some(x) => match gb { None => None, Some(y) => match gc { None => None, Some(z) => match gd { None => None, Some(w) => Some(Pushes(x, y, z, w)) } } } }))))),
```

With binding statements:

```heather
Some(n) => {
    let ga <- mono_try_global(n.le_l);
    let gb <- mono_try_global(n.le_r);
    let gc <- mono_try_global(n.lt_l);
    let gd <- mono_try_global(n.lt_r);
    Pure({ let x <- ga; let y <- gb; let z <- gc; let w <- gd; Some(Pushes(x, y, z, w)) })
},
```

The outer block's carrier is `Tac`, from the arm's expected type
`Tac<Option<Pushes>>`. The inner block's carrier is `Option`, from `Pure`'s
argument type. `mono_split` loses its two-level `view(l).bind(λ vl =>
view(r).bind(λ vr => …))` the same way, and its inner
`mono_diffs(…).bind(λ diffs => match diffs {…})` becomes
`match <- mono_diffs(…) {…}`.

### 3.4 Elaboration

Binding statements are a new `Stmt` variant and a new expression form,
`ExprKind::Bind` for `(<- e)`, both parsed in `block_body`. The elaborator
lowers them in `elab_stmts`, the shared statement walk
(`docs/let-and-blocks-design.md` §4.4), because the carrier comes from the
expected type, which the parser cannot see. The diagnostic can then name
the carrier. The `?` lowering stays in the parser; §6.3 says how the two
meet inside loops.

The walks that must learn the new nodes are the ones the block-expression
round listed: `count_holes`, `scan_splices`, `expr_mentions`. The
tree-sitter grammar and `heather fmt` learn the statements as well
(`issues/tree-sitter-grammar-drift.md`: the grammar is not in CI and drifts).

### 3.5 `Option` and `?`

`?` gets `Option` beside `Result`, exiting the nearest `fn` or λ with
`None`, by the same parser expansion over `Option::and_then`. This was
proposal §3.1's plan, and it is the last open half of
`issues/prelude-option-and-friends.md` layer 2 (the `gather` shape). The
generic propagation protocol that `docs/result-propagation-design.md`
declined stays declined. `?` is propagation into the function's own
`Result`/`Option` type. `<-` is binding in any carrier.

## 4. Layer 2: statements

```heather
let mut x = e;                 // a local that := may reassign; `let mut x: T = e;` annotated
x := e;                        // reassign a `let mut` local
x.f.g := e;                    // x := x with { f = x.f with { g = e } }
for x in e { … }               // e's owner provides the iteration (§5.2)
for { a, b } in e { … }        // record destructuring at the binder
for i in a..b { … }            // a range, in a `for` header only
while c decreases m { … }      // a measure over the locals
while c fuel n { … } exhausted { … }
if c { … }                     // a statement `if`: `else` optional
match e { P => { … }, … }      // a statement `match`
break;  continue;  return e;
scan: for b in bytes { … }     // a label; `break scan;`, `continue scan;`
```

**Statement and result.** A block is now statements, then an optional result
expression, then `on`s. The parser keeps today's rule for the result: an
expression followed by `}` or `on` is the result. An expression followed by
`;` is an expression statement (§3.1), legal only in a carrier scope; in a
pure scope it is refused with the reason "a statement here discards a pure
value", unless it is a `mut self` call (§8.2). An expression followed by `:=` is an assignment. A block-like
statement (`for`, `while`, a statement `if`/`match`) needs no `;`, as in
Rust. One exception keeps existing code parsing: if the next token can
continue an expression (`.`, a binary operator), the `if`/`match` is an
expression and the parse continues. No program written today has two
expressions in a row in a block, so nothing that parses now changes
meaning.

**Labels** reuse the statement-head rule that `split` relies on: `name :`
cannot begin an expression, because `:` never continues one. So
`scan: for` is exact on two tokens. A label names the loop's generated
declarations (§5.4), and `break`/`continue` target it.

**Scope rules**, each a refusal with its reason (§10):

- `:=` only to a `let mut` local of the same scope, and never from inside a
  λ (the λ is a separate scope; it may read the local's current value).
- A `mut` local's type may not mention another `mut` local. Assignment
  checks `e` against the declared type, so the type never changes.
- `break`/`continue` only inside a loop. `return` only in the declaration's
  own statement scope, including its loop and `if` bodies. It is refused
  inside a block expression in value position, where it would exit from
  the middle of an expression.
- `while … decreases` is refused in a carrier scope (§6.2).

`return e` takes the **value**, in pure and carrier code alike: in a
carrier scope it is `M::pure(e)` and exits. The block's final expression
remains a computation, as today: `Pure(x)` or a tail call.

## 5. Layer 2: lowering in pure code

### 5.1 Straight-line code: SSA aliases

A `let mut x = e;` is a `let x = e;`, and each `x := e'` starts a new alias
`let x = e';` that shadows the previous one. Since a `let` is an alias, not a
binder (`docs/let-and-blocks-design.md` §4.4), the rest of the block sees
each local's current value spelled inline. `split_all`, `rewrite` and
`omega` work on it directly, and no binder or motive is introduced.

A statement `if`/`match` whose arms assign joins **per variable**: for each
local `x` the arms assign,

```heather
let x: T = match c { True => /* x after the then-branch */, False => /* x after the else-branch */ };
```

The annotation is required. Without it the `match` is in inference position,
and probe P2 shows that is refused ("`match` in inference position needs a
motive"). This is why layer 2 runs in the elaborator: the walk knows every
`mut` local's type. Joining per variable duplicates the condition once per
assigned local, which `split_all` handles consistently (it splits every
occurrence of a comparison, `docs/native-programs-read-like-programs-design.md`
§2). The alternative is a join tuple, which proofs would have to project.

### 5.2 Loops: a named step, then a fold

The **state** of a loop is the `mut` locals its body assigns. A loop that
assigns one local has that local's type as its state. A loop that assigns
several has a generated record, `f::State`, with one field per local, named
after it. The **step** is the body as a function of the locals it reads but
does not assign (its captures), the state and the element, returning the
state:

```heather
// generated from count_words (§0)
record count_words::State { words: Nat, inside: Bool }
fn count_words::step(s: count_words::State, b: BitVec(8)) → count_words::State { … the body, SSA-lowered … }
fn count_words(bytes: List<BitVec(8)>) → Nat {
    let s = bytes.foldl(count_words::step, count_words::State(0, False));
    s.words
}
```

The step function is always generated as a **named sibling declaration**,
never inlined as a λ. This answers the cost question R3's issue raised
("if it grows superlinearly, generate named step functions by default"): a
λ would put the whole body inside every term that mentions the loop, while
a global is elaborated and kernel-checked once. The step is also what
proofs state facts about (§7) and what the native compiler consumes (§9).
`decreases` sets the precedent of generated siblings (`f#body`, `f#rec`).

The **iteration protocol** uses owner members again. `for x in e` with
`e : O<…>` calls:

| body | member | type |
|---|---|---|
| no `break`, `continue` or `return` | `O::foldl` | `(self xs, f: S → A → S, z: S) → S` |
| any early exit | `O::for_in` | `(self xs, step: S → A → ForStep<S, R>, s: S) → ForStep<S, R>` |
| in a carrier scope (§6) | `O::foldr` | `(self xs, f: A → B → B, z: B) → B` |

`List` has `foldl` and `foldr` and gains `for_in`. R3 adds the members
to `[T; n]` and `BitVec` once a customer needs them. A range `a..b`
is `List::range_from(a, b - a)`, written only in a `for` header, so that no
`Range` type has to be designed now. `0..n` is `List::range(n)`, which
already has `len_range`.

`ForStep` is a library inductive in `list.hthr`:

```heather
inductive ForStep<S, R> { Next(s: S), Break(s: S), Return(r: R) }
fn List::for_in<A, S, R>(self xs: List<A>, step: S → A → ForStep<S, R>, s: S) → ForStep<S, R> {
    match xs {
        Nil => Next(s),
        Cons(a, rest) => match step(s, a) { Next(t) => rest.for_in(step, t), Break(t) => Break(t), Return(r) => Return(r) },
    }
}
```

`continue` ends the step with `Next(s)`, `break` with `Break(s)`, and
`return e` with `Return(e)`. After the loop, the rest of the block is the
`Next`/`Break` continuation, and `Return(r)` is the function's value
(probe P3: `find_index` computes by `refl` both ways). Choosing `foldl`
whenever no exit occurs keeps the common case on the lemmas the library and
the native counting proofs already have.

### 5.3 `while`: a generated recursive function

`while c decreases m { body }` becomes a sibling `f::run` with the
**state as separate parameters**, one per assigned local, not a record:

```heather
// let mut m = n; let mut out = []; while !m.same(0) decreases m { out := Cons(m, out); m := m - 1 }
fn f::run(m: Nat, out: List<Nat>) → List<Nat> /* the state, or a record of it */ decreases m {
    match h: !m.same(0) { False => …state…, True => f::run(m - 1, Cons(m, out)) }
}
```

Both choices come from probes. With a record state, the measure obligation
mentions a field of a constructed record, which `omega` cannot spell, and
which the unsolved-goal display prints as raw `fst@(snd@(pair@…` (probe P4).
Separate parameters make the obligation plain. The condition is matched with
an equation binder (`match h: c`), so the obligation sees `h : c = True`.
Without it, a computed scrutinee leaves the arm with no fact about the
condition, and the obligation is unprovable (probe P4). The obligation is discharged as
every `decreases` obligation is: `omega` by default, otherwise
`on decreasing <label> := …`
(`docs/stable-termination-labels-design.md`, with the loop's label as the
call's label).

`while c fuel n { body } exhausted { e }` becomes a sibling structural on
the fuel, returning `Fuelled<S> { Finished(s: S), Exhausted(s: S) }`. The
`exhausted` block runs on the state at exhaustion and may assign, `return`
or `break`. It is required, so running out of fuel is never silent. Proofs
after the loop get `¬c` only on the `Finished` path, which is honest.

`break`, `continue` and `return` inside a `while` thread the same `ForStep`
through `f::run`'s result.

### 5.4 Names

The generated declarations are `f::step`, `f::State` and `f::run` when `f`
has one loop. A labelled loop `scan:` gets `f::scan_step`, `f::scan_State`
and `f::scan_run`. Unlabelled loops in a function with several get ordinals
`loop1`, `loop2`, … in source order (`f::loop1_step`). That is the policy
`docs/stable-termination-labels-design.md` set for unlabelled `?decN`
sites: ordinal names work, and labels are recommended wherever a proof cites
the name, so an edit does not retarget it.

### 5.5 Early exit outside loops

`return e` in straight-line code splits the continuation, as `?` does
today: `if c { return e }; rest` is `match c { True => e, False => rest }`.
When a continuation is needed in more than one place, for example after an
`if` whose branches both fall through but one of them returns on an inner
path, it is bound once as a join point, `let k = λ (state) => rest;`, and
called from each place. That is Lean 4's join-point lowering, and it keeps
the size linear.

## 6. Layer 2 inside a carrier scope

### 6.1 Loops and `if`

The same statements work in a carrier scope. The state threads through
`bind`:

- a `for` is CPS over `O::foldr`:
  `xs.foldr(λ x k => λ s => step(s, x).bind(k), λ s => M::pure(s))(s0)`,
  with `step` returning `M<S>` (probe P3: `count_defeq` over `Tac`
  checks). With early exits, `step` returns `M<ForStep<S, R>>`, and the folded
  function stops at `Break`/`Return` by `M::pure`;
- a statement `if`/`match` whose arms bind joins through
  `(match c { … M::pure(state) … }).bind(λ state => rest)`.

These are the forms that need `M::pure`. When the carrier has none, the
refusal names the member: "`for` in a `Parser` block needs `Parser::pure`".

### 6.2 No `decreases` loops in a carrier scope

A measure cannot see a value a `bind` produces. In `step(s).bind(λ t =>
run(t))` the new state `t` is arbitrary, so `m(t) < m(s)` is unprovable
whatever the body does. A carrier `while` therefore takes `fuel`, and
`decreases` is refused with that reason. The tactics already work this
way: `mono_same(4096, …)` is a fuel budget.

### 6.3 `?` and `return` agree

`e?` inside a loop body must exit the **function**, not just the generated
step. So inside the statement forms of §4, `e?` is
`match e { Ok(v) => v, Err(x) => return Err(x) }`, through the loop's
`Return`. In straight-line code the parser's expansion stays. Both produce
the same term there, because `and_then` is that match. `?` is thereby
specified as a special case of `return`.

## 7. What proofs see

### 7.1 The function's equation

A function with any layer-2 statement gets `f_unfold : f(x̄) = <lowered
body>`, proved by `refl`. It is generated for a practical reason: tactics
treat `count_words(xs)` as an atom and do not unfold it. Probe P2's
`cw_bound` had to restate `count_words(xs) = xs.foldl(…).words` by `refl`
before `omega` could use the fold's bound. With `f_unfold` in hand, that
step is `rewrite(f_unfold)` or a fact passed to `omega`. The name matches
the `decreases` equations (`f_unfold`, `docs/decreases-unfolding-design.md`).

### 7.2 Step facts and fold theorems

A step fact is one line, as §1.1 of the native design found:
`theorem cw_words_step(s, b): count_words::step(s, b).words <= s.words + 1
{ split_all; all_goals { omega } }` checks (probe P2).

What a `for` contributes beyond its step is a **library** theorem, not a
generated one, because every lowered `for` is the same `foldl`/`for_in`
applied to a step:

- `List::foldl_invariant(inv, step, hstep)`: `inv(s) → inv(xs.foldl(step,
  s))` (probe P2 proves it in four lines);
- `List::for_in_invariant`, the same over `Next`/`Break`, with the
  exit's post-state;
- `foldl_append`, which exists, and `for_in_append`.

This is why `loop-invariant-rules` (P4) can be small: its invariant rule is
these theorems plus a tactic step that applies them, not a per-loop
generator. §11 asks Minus to confirm that boundary.

### 7.3 `while` needs `unfolding-computed-scrutinee`

A `decreases` function's `_unfold` is generated by walking its body. The
`while` lowering matches on the condition with an equation (§5.3), so its
obligation depends on the match equation, and the walk refuses: "no
unfolding equation for `cd_loop`: the lifted `cd_loop#obl_1` was refused"
(probe P5; the loop itself computes, `cd_loop(3, Nil) = [1, 2, 3]` by
`refl`). That is exactly `issues/unfolding-computed-scrutinee.md`. So the
`while … decreases` half of R3 depends on that issue, and its first route
(generalize the scrutinee into the convoy the lowering already writes) is
the one this lowering needs. `for` and `fuel` loops do not depend on it:
`foldl`, `for_in` and structural fuel compute on constructors.

### 7.4 Interface definitions

When a function is declared an interface definition
(`issues/proof-modularity-design.md`, opt-in), tactics stop unfolding it.
Then `f_unfold`, the named step and the fold theorems are the interface
it exports. The surface already produces the shape that design wants:
facts about a small named step, and one rule per loop. Nothing here waits
on P1.

## 8. The effects case

### 8.1 Effects use layer 2

`effects-direction` decided uniqueness threading that denotes interaction
trees, and that users never write monadic types. Layer 1 over an `ITree`
carrier would be exactly the monadic surface it rules out. So
**effectful code is layer 2**: a capability is a `let mut` local, and
an effectful operation is a method that updates it.

### 8.2 `mut self` parameters

```heather
fn Fd::read(mut self fd: Fd, n: Nat) → List<BitVec(8)> { … }
// kernel type: Fd → Nat → Pair<Fd, List<BitVec(8)>>

let mut out = stdout();
let mut inp = stdin();
let bytes = inp.read(4096);      // let p = Fd::read(inp, 4096); inp := p.first; let bytes = p.second;
out.write(bytes);                // a `mut self` method whose result is True: a statement
```

A `mut self` parameter is passed in and comes back out, like Swift's
`inout`. The kernel type returns the pair, and a call whose receiver is a
`let mut` local reassigns it. That is pure code: SSA (§5.1) handles it. It
is also useful outside effects (`out.push(byte)` on a `let mut` list).
Called on anything that is not a `mut` local, the method is refused, and
`@Fd::read(fd, n)` gives the pair. The expression statement `out.write(bytes);`
is legal in a pure scope because it reassigns `out`. It discards nothing.

### 8.3 What belongs to setups

**Uniqueness is not checked by the elaborator.** That a capability is
used linearly, never duplicated or dropped, is a judgment over the
function's code, and judgments over code are what `runtime fn` setups check
(proposal §4.1). The default setup checks capability linearity, and the
ownership setup, if adopted, reads `let mut` and `mut self` as Rust's
`let mut` and `&mut self`. The surface stays neutral: the same lowered term
goes to whichever setup boxes it.

`effects-uniqueness-surface` (R6) builds capabilities, the denotation
agreement (`ITree::run_state_bind`) and the I/O library over this. It owns
`mut self`'s effectful customers. §12 places `mut self` itself in R3, since
it is pure and uses the same SSA.

## 9. The native compiler's view

The lowered shapes are the ones the native compiler already verifies:

- `for` → `foldl` of a named step is the counting-fold shape
  (`counting(wc_step)`, `fold_bytes`). The one bridge R5 needs is
  `fold_bytes(step, xs, s) = xs.foldl(step, s)`, by induction.
- `while … decreases` → a `decreases` function compiles to a verified loop
  against `f#rec` (merged as PR #190).
- SSA lets and per-variable joins are FunctionIR's pure leaves and `Select`.

R4 (the setups design) takes these as its input shapes, so the pure
fragment of the default setup is "what this lowering emits".

## 10. Refusals

Each is a refusal that names its reason (`docs/test-value-audit.md` §5),
and R2 or R3 adds it as a negative control:

| form | reason |
|---|---|
| `let x <- e;` in a scope whose expected type's owner has no `bind` | "`Nat` has no `bind`: this block is not over a carrier" |
| `let x <- e;` with no expected type, where `e`'s owner has no `bind` | the same, naming `e`'s type |
| a bind whose computation's carrier is not the block's | "this computation is an `Option`, but the block's carrier is `Tac`" |
| `e;` in a pure scope | "a statement here discards a pure value" |
| `x = e;` as a statement (an equation, so a discarded proposition) | the same, plus "to assign, write `x := e`" (`issues/warn-bare-eq-no-effect.md`) |
| `for`/statement `if` with binds where `M::pure` is missing | "needs `M::pure`" |
| `x := e` where `x` is not `let mut` | "`x` is not mutable: declare it `let mut x`" |
| `:=` inside a λ | "a λ cannot assign the enclosing function's locals" |
| a `mut` local whose type mentions another `mut` local | "the type of a mutable local cannot depend on another" |
| `break`/`continue` outside a loop, or to an unknown label | named |
| `return` inside a block expression in value position | "`return` would leave an expression unfinished" |
| `while` with neither `decreases` nor `fuel` | "a `while` needs a measure (`decreases m`) or fuel (`fuel n`)" |
| `while … decreases` in a carrier scope | "a measure cannot see values a bind produces: use `fuel`" |
| `while … fuel` without `exhausted` | "say what happens when the fuel runs out" |
| a `mut self` method on a value that is not a `let mut` local | "call it on a `let mut` local, or write `@M::m(…)` for the pair" |

## 11. Decisions for Minus

1. **Carrier protocol: owner members `M::bind` / `M::pure`, not a class**
   (§2.1). A class is not expressible today. *Recommended.*
2. **Carrier scopes are implicit**: a block is over a carrier when it binds
   or sequences, with no `do` keyword (§2.2). The alternative is an
   explicit marker, which Lean needs because it is an expression language
   with an ambiguous `;`; Heather's block grammar is not. *Recommended:
   implicit.*
3. **Nested binds `(<- e)` arm-local, with no hoisting** (§3.2). *Recommended.*
4. **Step functions always named siblings, with state records for several
   locals and state parameters for `while`** (§5.2, §5.3). *Recommended.*
5. **The invariant rule is library theorems about `foldl`/`for_in`, not a
   per-loop generator** (§7.2). This narrows `loop-invariant-rules`.
   *Recommended.*
6. **Effects are layer 2 with `mut self`, and uniqueness is a setup
   judgment** (§8). `mut self` lands in R3, and its effectful customers in
   R6. *Recommended.*
7. **The other syntax issues**:
   - `pipeline-operator`: keep it open and independent. Binding statements
     remove carrier towers, not pure dataflow chains, and method calls
     already give value-first chaining for owners. Its customers come from
     `surface-proof-automation`, not from towers.
   - `function-composition-operator`: unaffected.
   - `prelude-option-and-friends`: layer 2 closes with R2 (`Option` carrier
     and `?`, §3.5).

## 12. What R2 and R3 take

**R2, `binding-statements`.** `let x <- e;` (and `←`, annotated,
destructuring, `_`), `e;`, nested `(<- e)` and `match <- e`, lowered in
`elab_stmts`. The carrier comes from the expected type, then owner-by-head.
`?` for `Option`. The library members of §2.3 (`Tac::pure`, `Tac::or_fail`,
`Option`/`Result` `bind`/`pure`, `Parser::pure`, `ITree::bind`'s `self`
form). Port `mono.hthr` and one parser chain, with `scripts/timings --diff`
showing identical count columns on `mono`'s probes (no kernel term changed).
Tree-sitter and `heather fmt`. Layer-1 refusals from §10. Unchanged done-when:
`mono.hthr` has no `bind` tower.

**R3, `pure-imperative-statements`**, in two slices so the second can wait
on its dependency:

- **R3a**: `let mut`, `:=` (with field paths), statement `if`/`match`, `for`
  over lists and ranges (`foldl`/`for_in`), `break`/`continue`/`return`,
  labels, `while … fuel … exhausted`, the carrier forms of §6, `?` as
  `return` in loops, `mut self` parameters, `f_unfold`, the generated step
  and state names, `List::for_in` and `ForStep`, the fold theorems of §7.2.
  Done when `wc`'s step is written imperatively and its facts are proved by
  the existing tactics with no hand unfolding.
- **R3b**: `while … decreases`, after `unfolding-computed-scrutinee`. Done
  when the decimal formatter is written as a `while` over `m` and
  `decimal_places` is proved against it.

**Cost, stated as shapes.** Lowering is linear in statements. Per-variable
joins cost one condition copy per assigned local per `if`. A chain of `k`
binds nests `k` binders, which is the hand-written tower's cost, quadratic
at worst by the representation's bound on a binder-per-link chain (the
`let/under` bench, PR #199), and never worse than the tower it replaces.
Each loop's body is elaborated once, as its step's declaration.

## Appendix: probes (run on `3099a7d`, `heather check -L lib`)

- **P1, a class over a type constructor.** `class Bind<M: Type → Type> {…}`
  fails to parse ("expected `>` to close the type parameters, found
  Colon"). `fn ap(M: Type → Type, x: M(Nat))` called as `ap(Option,
  Some(1))` is refused: "`Option` cannot be used here".
- **P2, `count_words` hand-lowered.** A generated record, a step with
  annotated SSA joins, and `xs.foldl(step, init)`. Closed `refl` gives 3 on
  an eight-byte input. The step fact needs `split_all; all_goals { omega }`.
  `List::foldl_invariant` takes four lines. The spec `count_words(xs) <=
  xs.len()` holds by structural induction over a generalized state, plus the
  `refl` restatement §7.1 automates. An unannotated join `let inside2 =
  match …` is refused for lack of a motive. While writing it, a separate
  bug: `omega` in a `Nil` arm whose goal mentions `xs.len()` fails because
  its generated certificate spells a bare `Nil`
  (`issues/omega-certificate-bare-nil.md`, filed by this round).
- **P3, early exit and a carrier loop.** `List::for_in` with `ForStep`;
  `find_index([4, 5, 6], 6) = Some(2)` and `… 7) = None` by `refl`.
  `count_defeq` over `Tac` as CPS `foldr` checks.
- **P4, `while` with a record state.** `decreases s.m` over a constructed
  `DecState(…)`: the obligation is displayed as raw `fst@(snd@(pair@…` and
  `omega` cannot spell it. Without `match h:`, the arm has no fact about the
  condition (`__dec_scrut : Bool` only). Hence §5.3's separate parameters
  and equation binder (`issues/decreases-measure-record-field-unspelled.md`).
- **P5, `while` with parameter state.** `cd_loop(m, out) decreases m` with
  `match h: m.leb(0)` and an `on ?dec1` discharge checks, and
  `cd_loop(3, Nil) = [1, 2, 3]` by `refl`. `cd_loop_unfold` is refused,
  because the lifted obligation depends on the match equation
  (`unfolding-computed-scrutinee`).
