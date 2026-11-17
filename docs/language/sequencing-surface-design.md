# One sequencing surface: binding over a carrier, local state and loops

Status: **decided (2026-10-31); layer 1 built (R2, 2026-11-01).** Round R1
of `docs/native/compiler-milestones-proposal.md` (§3, §7; milestone
`lang-sequencing`), issue `issues/sequencing-surface-design.md`. Written on
master `3099a7d`. §11 lists the decisions, §12 what R2 and R3 take from this
note, and §13 what building R2 changed. Layer 2 (R3) is not built yet.

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
binder, and `:=` is held for assignment (`docs/language/let-and-blocks-design.md`
§3.1, `issues/effects-direction.md` 2026-07-24). Interleaved statements were
deferred until a statement means something (`docs/language/let-and-blocks-design.md`
§4.5). Users never write or prove against a monadic elaboration target for
effects (`issues/effects-direction.md`, "Avoid").

**No kernel change and no trusted rule.** Every form lowers to a term that
can be written by hand today: a `bind` call, a `List::foldl`, a `decreases`
function. The elaborator checks that term like any other.

---

## 0. The proposal in one page

```heather
// Layer 1: binding over a carrier. The carrier is the constructor of the
// block's expected type (`Tac`), and `let x <- e;` is `Bind::bind(e, λ x => …)`
// at `Tac`'s instance.
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

1. **The carrier protocol is two classes over a type constructor,
   `Bind<M>` and `Pure<M>`** (§2). Heather can nearly state them already:
   a record over `M: Type → Type` works and computes (probe P1). Three
   pieces are missing and become R2's first slice: the unifier's
   `?M(A) =?= Option<A>`, a bare `Option` as a `Type → Type` value, and a
   class whose carrier is a constructor. The block's carrier is the
   constructor of its expected type, or else of its first bound expression.
   Owner members (`M::bind`) are the fallback if that slice proves large.
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
  `docs/archive/native-programs-read-like-programs-design.md` §1.1 proves `wc`'s
  facts with one line per field of `wc_step`. The native loop compiler takes
  folds of a step (`fold_bytes`, `lib/native/function_ir/function_ir_loop.hthr`),
  and `decreases` word functions compile to verified loops against `f#rec`.

## 2. The carrier protocol

### 2.1 A class over a type constructor

*Revised 2026-10-31, after Minus's comment on the PR that a `Monad` Heather
cannot express is something to fix in Heather. The first draft said a class
could not be written and chose owner members instead. Probe P1 was too
narrow: most of what a class needs works already, and the gaps are three
bounded pieces of work.*

**What works today** (probe P1, all on `3099a7d`):

- A value-parameter inductive is a type constructor:
  `inductive Box(A: Type) { … }` passes as `M: Type → Type`.
- So is a generic inductive under a λ: `λ (A: Type) => Option<A>`.
- A record over a constructor is a dictionary:
  `record Monad(M: Type → Type) { pure: …, bind: … }`, with a value at
  `Option`, and generic code `twice({M}, m: Monad(M), x: M(Nat))` computes:
  `twice(option_monad(), Some(3)) = Some(3)` by `refl`.

**What does not, and is the work** (proposed as R2's first slice, §12).
*Landed 2026-10-31 as R2a: `docs/language/classes/higher-kinded-classes-design.md`. Its §5
lists what R2 inherits: instances write their implicit binders
(`pure := λ {A} a => …`), a class named `Pure` collides with `Tac`'s
constructor `Pure`, and a `Result` instance waits on
`issues/class-instance-at-lambda-carrier.md`.*

1. **The unifier cannot solve `?M(Nat) =?= Option<Nat>`.**
   `pick({M: Type → Type}, x: M(Nat))` called at an `Option<Nat>` or a
   `Box(Nat)` gives "could not infer the implicit argument `M`". The fix is
   the first-order approximation that Lean and Haskell use: an applied
   unknown against a named type applied to arguments takes the head with the
   leading arguments, so `?M := λ A => Option<A>`. For `Result<A, E>` this
   picks the last argument, so a `Result` instance is over `λ A =>
   Result<A, E>` only if the approximation abstracts the right argument.
   Where it cannot, the instance names its constructor and the expected type
   pins `M`.
2. **A bare generic name is not a constructor value.** Passing `Option` where
   `Type → Type` is expected says "`Option` cannot be used here". The fix
   η-expands a generic name with one remaining parameter at a
   `Type → Type` position to `λ A => Option<A>`. This is elaboration only.
3. **A class's carrier must be a type.** `class Monad(M: Type → Type)` is
   refused ("a class is a record parameterized by its carrier"), and
   `class Bind<M: Type → Type>` does not parse. Both the carrier syntax and
   the registry key have to take a constructor. Instance keys are already
   resolved head references (`docs/elaborator/instance-resolved-key-design.md`), so the
   key of `instance Bind<Option>` is the head `option::Option`.

**The classes.** Two small classes rather than one `Monad`, so that "any type
with a `bind`" (Minus, 2026-10-31) holds literally:

```heather
class Bind<M: Type → Type> { bind: {A, B: Type} → M(A) → (A → M(B)) → M(B) }
class Pure<M: Type → Type> { pure: {A: Type} → A → M(A) }

instance Bind<Tac> { bind := Tac::bind }
instance Pure<Tac> { pure := λ a => Pure(a) }
```

`let x <- e; rest` lowers to `Bind::bind(e, λ x => rest)` at the carrier's
instance, and the forms of §5–§6 that inject a value use `Pure`. Laws are
not fields. A lawful-monad class can extend both later if a proof needs one.

**What the class buys over owner members**, which were the first draft's
protocol (each carrier `M` had members `M::bind` and `M::pure`, found by
owner-by-head resolution):

- **Carriers with no named head.** A state monad can be `λ A => S →
  Pair<A, S>`, with no wrapper record. Owner members need a name to own
  them.
- **Generic code in Heather.** `traverse`, `for_m` and `when` are written once
  over `Bind<M>`/`Pure<M>`. The member route has to generate them per loop
  (§6.1's CPS over `foldr`). With the class, §6.1's carrier `for` is a call
  to a library `List::for_m`.
- **The general fix.** A class over a constructor is useful beyond this
  round (functors, traversals, the effects library), which is the
  proposal's "generalizing features" direction.

**What it costs.**

- **The three pieces above**, before R2's sugar can land. Pieces 1 and 3
  are the substantial ones.
- **The lowered term is no longer the hand-written one.** It goes through the
  instance: `Bind::bind` at `Bind<Tac>`, which δ-reduces to `Tac::bind`.
  Instances are transparent, so closed evaluation still computes (the
  `Option` probe is `refl`). But a port of `mono` changes kernel terms, so
  the "identical count columns" check is replaced by "the timings do not
  move beyond noise", read with `scripts/perf ab`. A native setup that
  reflects code has to see through one instance projection. That is the
  unreduced-projection friction `docs/archive/native-programs-read-like-programs-design.md`
  §2 found with `Numeral`, and the setup (R4) owns it.

**The fallback**, if the class work proves larger than it looks: the
owner-member protocol, which needs none of the three pieces. The sugar is
written so that the carrier lookup is one function. Switching between the
two changes that function and §2.3's library additions, and nothing in §3–§10.

### 2.2 Which carrier a block uses

A **statement scope** is a declaration body or a block expression. The
bodies of the statement forms of §4 (`for`, `while`, a statement `if` or
`match`) belong to the scope around them. A block expression in value
position, and a λ body, open a new scope.

A scope is a **carrier scope** when it contains `let … <- e;`, a nested
`(<- e)`, or an expression statement `e;`, including inside its loop and
`if` bodies. A `mut self` call on a `let mut` local (§8.2) is not counted:
it is an assignment, so it discards nothing. Its carrier is, in order:

1. the constructor of the scope's **expected type**, when the scope is
   checked (a `fn` body whose result is `Tac<Expr>` has carrier `Tac`),
   with its `Bind` instance resolved as any instance is;
2. otherwise the constructor of the **first bound expression's type**,
   found by inference (or by owner-by-head resolution,
   `docs/language/classes/receiver-member-resolution-design.md` §1, when inference declines,
   which covers `fail(…)` and `Pure(x)`).

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

R2 adds the instances its customers need. Each is one line: `Bind`/`Pure`
at `Tac`, `Option`, `Result` (over `λ A => Result<A, E>`), `Parser` and
`ITree`. It adds the generic helpers `List::for_m`, `traverse` and `when`
over the classes. It also adds `Tac::or_fail(self t: Tac<Checked<A>>,
prefix: String) → Tac<A>`, which retires the 34
`Refused(why) => fail(…)` matches as a library function rather than a
syntax.

## 3. Layer 1: binding statements

### 3.1 Forms

```heather
let x <- e;              // Bind::bind(e, λ x => rest), at the carrier's instance
let x: A <- e;           // the binder annotated; e is checked at M<…A…>
let { a, b } <- e;       // bind, then destructure the record (docs/language/matching/named-patterns-by-field-design.md §2)
let _ <- e;              // discard, explicitly
e;                       // discard: Bind::bind(e, λ _ => rest)
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
expansion: `docs/language/result-propagation-design.md` lowers `K[e?]` to
`and_then(e, λ v => K[v])`, and `K[(<- e)]` lowers to `Bind::bind(e, λ v =>
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
(`docs/language/let-and-blocks-design.md` §4.4), because the carrier comes from the
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
generic propagation protocol that `docs/language/result-propagation-design.md`
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
  λ (the λ is a separate scope; it may read the local's current value). The
  arms of a branch that ends the local's block are of its scope (§19.1).
- A `mut` local's type may not mention another `mut` local. Assignment
  checks `e` against the declared type, so the type never changes.
- `break`/`continue` only inside a loop. `return` only in the declaration's
  own statement scope, including its loop and `if` bodies. It is refused
  inside a block expression in value position, where it would exit from
  the middle of an expression.
- `while … decreases` is refused in a carrier scope (§6.2).

`return e` takes the **value**, in pure and carrier code alike: in a
carrier scope it is `Pure::pure(e)` and exits. The block's final expression
remains a computation, as today: `Pure(x)` or a tail call.

## 5. Layer 2: lowering in pure code

### 5.1 Straight-line code: SSA aliases

A `let mut x = e;` is a `let x = e;`, and each `x := e'` starts a new alias
`let x = e';` that shadows the previous one. Since a `let` is an alias, not a
binder (`docs/language/let-and-blocks-design.md` §4.4), the rest of the block sees
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
occurrence of a comparison, `docs/archive/native-programs-read-like-programs-design.md`
§2). The alternative is a join tuple, which proofs would have to project.
*Amended (2026-11-12):* the join tuple is what is built now (§14 item 3):
per-variable joins copied each branch's calls along with the condition.

*Amended (2026-10-31):* probe P2's refusal is gone. A motive-less `match`
in inference position now takes its constant motive from any arm whose type
lives outside its binders (`docs/language/matching/dependent-match-compiler-design.md` §6.1).
The annotation is optional wherever some arm's type names `T`. The walk can
keep writing it, since it knows the type and the annotation costs nothing.

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

The **iteration protocol** uses owner members: a container's folds are its
own operations, and no class over containers is needed yet. A `Foldable`
class can replace the table once §2.1's constructor classes exist. `for x in e` with
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
(`docs/language/recursion/stable-termination-labels-design.md`, with the loop's label as the
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
`docs/language/recursion/stable-termination-labels-design.md` set for unlabelled `?decN`
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

- a `for` is a call to the library's `List::for_m(xs, s0, step)`, written
  once over `Bind<M>`/`Pure<M>` as CPS over `foldr`:
  `xs.foldr(λ x k => λ s => step(s, x).bind(k), λ s => pure(s))(s0)`,
  with `step` returning `M(S)` (probe P3: the same CPS over `Tac` checks).
  With early exits, `List::for_in_m` takes a step returning
  `M(ForStep<S, R>)` and stops at `Break`/`Return`. Under the owner-member
  fallback, the lowering writes this CPS inline instead;
- a statement `if`/`match` whose arms bind joins through
  `Bind::bind(match c { … pure(state) … }, λ state => rest)`.

These are the forms that need `Pure<M>`. When the carrier has no instance,
the refusal names it: "`for` in a `Parser` block needs `Pure<Parser>`".

### 6.2 No `decreases` loops in a carrier scope

A measure cannot see a value a `bind` produces. In `step(s).bind(λ t =>
run(t))` the new state `t` is arbitrary, so `m(t) < m(s)` is unprovable
whatever the body does. A carrier `while` therefore takes `fuel`, and
`decreases` is refused with that reason. The tactics already work this
way: `mono_same(4096, …)` is a fuel budget.

*2026-11-03: a carrier that can iterate (an `Iterate` instance: `Partial`,
`CoTree<_>(E)`) takes `while c { … }` with neither `decreases` nor `fuel`
(§18; decided by Minus with docs/language/effects-capabilities-design.md §4). The
`fuel` form for the other carriers is still not built.*

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
the `decreases` equations (`f_unfold`, `docs/language/recursion/decreases-unfolding-design.md`).

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
A body that ends in a branch, and a method's own call at its end, are §19.

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
| `let x <- e;` in a scope whose expected type has no `Bind` instance | "`Nat` has no `Bind` instance: this block is not over a carrier" |
| `let x <- e;` with no expected type, where `e`'s type has none | the same, naming `e`'s type |
| a bind whose computation's carrier is not the block's | "this computation is an `Option`, but the block's carrier is `Tac`" |
| `e;` in a pure scope | "a statement here discards a pure value" |
| `x = e;` as a statement (an equation, so a discarded proposition) | the same, plus "to assign, write `x := e`" (`issues/warn-bare-eq-no-effect.md`) |
| `for`/statement `if` with binds where `Pure<M>` is missing | "needs `Pure<M>`" |
| `x := e` where `x` is not `let mut` | "`x` is not mutable: declare it `let mut x`" |
| `:=` inside a λ | "a λ cannot assign the enclosing function's locals" |
| a `mut` local whose type mentions another `mut` local | "the type of a mutable local cannot depend on another" |
| `break`/`continue` outside a loop, or to an unknown label | named |
| `return` inside a block expression in value position | "`return` would leave an expression unfinished" |
| `while` with neither `decreases` nor `fuel` | "a `while` needs a measure (`decreases m`) or fuel (`fuel n`)" |
| `while … decreases` in a carrier scope | "a measure cannot see values a bind produces: use `fuel`" |
| `while … fuel` without `exhausted` | "say what happens when the fuel runs out" |
| a `mut self` method on a value that is not a `let mut` local | "nothing here keeps the update: call it on a `let mut` local …, or call `M::m(…)` by its qualified name for the `Mutated` record" (built; docs/language/effects-capabilities-design.md §2.2) |

## 11. Decisions for Minus

1. **Carrier protocol: classes `Bind<M>`/`Pure<M>` over a type
   constructor, with the three missing pieces built first as R2a** (§2.1).
   The alternative is owner members `M::bind`/`M::pure`, which need no
   language work but give no generic code and need a named head.
   *Recommended: the classes (revised after Minus's PR comment).*
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

**R2a, `higher-kinded-classes`** (new): §2.1's three pieces. They are the
unifier's first-order approximation for `?M(A) =?= Option<A>`, a bare
generic name η-expanded at a `Type → Type` position, and classes (and
instance keys) whose carrier is a constructor. Done when `class Bind<M:
Type → Type>` has instances at `Option` and `Tac`, and a generic
`twice({M}, x: M(Nat))` with `Bind<M> := infer` resolves at both and
computes by `refl`.

**R2, `binding-statements`.** `let x <- e;` (and `←`, annotated,
destructuring, `_`), `e;`, nested `(<- e)` and `match <- e`, lowered in
`elab_stmts` through `Bind<M>`. The carrier comes from the expected type,
then from the first bound expression. `?` for `Option`. The instances and
helpers of §2.3 (`Tac::or_fail`, `List::for_m`). Port `mono.hthr` and one
parser chain, and check with `scripts/perf ab` that `mono`'s probes do not
move beyond noise. Tree-sitter and `heather fmt`. Layer-1 refusals from §10.
Unchanged done-when: `mono.hthr` has no `bind` tower.

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
joins cost one condition copy per assigned local per `if` (*amended
2026-11-12*: one join per `if`, whatever it assigns, since a copy per local
copied each branch's calls too, issues/statement-form-join-copies-calls.md). A chain of `k`
binds nests `k` binders, which is the hand-written tower's cost, quadratic
at worst by the representation's bound on a binder-per-link chain (the
`let/under` bench, PR #199), and never worse than the tower it replaces.
Each loop's body is elaborated once, as its step's declaration.

## 13. R2 as built (2026-11-01)

Layer 1 landed for `issues/binding-statements.md`. Probes:
`lib/_tests/std/core/binding_statements_tests.hthr`; parse-level refusals:
`crates/syntax/tests/binding_statements.rs`. What building it changed from
§2–§3 and §12, each with its reason:

1. **The lowering is in the parser, not in `elab_stmts`.** §3.4 put it in
   the elaborator because the carrier comes from the expected type. It does
   not need to: the lowered term is an ordinary call of a prelude function,
   `Bind::seq(e, λ x => rest)`, and *application elaboration* finds the
   carrier (`M(B) ≟` the expected type, `M(A) ≟` `e`'s type) and resolves
   `Bind<M>` as any `:= infer` parameter. So the parser does it, in
   `crates/syntax/src/try_lower.rs`, which now runs one continuation-passing
   walk for two protocols: `?` (scoped to the function or λ body, blocks
   transparent) and binds (scoped to the **block**: every block is lowered
   when it closes, so an inner block in value position is a scope of its own
   with its own carrier, §2.2, and a λ body likewise). `let x <- e;` is the
   nested bind at a `let`'s right side, `let x = (<- e);`, and `e;` the same
   at a private `#seqN` name. Nothing downstream learns a new node, so the
   walks §3.4 listed (`count_holes`, `scan_splices`, `expr_mentions`) are
   untouched. The elaborator keeps two small pieces: it schedules the
   generated continuation after the expected type (a `#bind` λ is
   checking-only, `classify_application_argument`), so that the rest of a
   block checks at `M(B)` instead of being inferred from its first token; and
   on the failure path only, it restates a carrier-search error at the bound
   expression in the statement's terms (`crates/elab/src/binding.rs`).
2. **The second class is `Pointed<M>`, not `Pure<M>`.** Both classes live in
   the implicit prelude (as `CollectionLiteral` does for `[…]`, so the syntax
   has one protocol identity), which means every module sees them, and a
   class's record constructor is named after it: `Pure` would have taken
   `Tac::Pure` from every tactic module
   (`docs/language/classes/higher-kinded-classes-design.md` §5.2). The prelude also defines the
   two calls the lowering writes, `Bind::seq` and `Pointed::ret`.
3. **The carrier is the first bound expression's when that determines one,
   else the expected type's.** §2.2 ordered them the other way. The
   application walk unifies argument types before the expected result, so a
   block whose first computation is an `Option` and whose expected type is
   `List<…>` is refused at its *result* ("this has type `List<Nat>`, but
   `Option<Nat>` is expected here"), not at the computation with §10's
   "the block's carrier is `List`" wording. The two orders agree whenever
   the block is well typed; only that refusal's site differs. A computation
   that does not determine its constructor (`Pointed::ret(3)`) still takes
   the expected type's.
4. **A non-tail `match` whose arms bind is in inference position.** As for
   `?`, such a match is packaged (each arm ends in `Pointed::ret`) and bound
   once, which makes it `Bind::seq`'s first argument, where nothing gives it
   a motive: `let r = match c { True => (<- x) + 1, False => 0 };` is
   refused with the motive message. A tail match, a match whose scrutinee
   alone binds (`Pure(match <- e { … })`), and arms written as computations
   all work. §5.5's join point would retire it, and R3 needs it anyway.
5. **Instances at `Option` and `Tac` only.** `Result`, `Parser<T, ·>` and
   `ITree<E, ·>` vary in an argument that is not alone, so their instances
   are at a λ carrier, which `issues/class-instance-at-lambda-carrier.md`
   owns. The parser-combinator customer waits on it; `regex.hthr`'s
   generator chain is the second customer instead. *2026-11-02: Result's
   instances landed at `λ (A: Type) => Result<A, E>` with `inductive
   Result<A, E> varies A`, and `Parser<T>` is now a valid carrier as a
   partial application (`docs/language/classes/lambda-carrier-instances-design.md` §7). The
   CoTree/ITree carrier still waits on codata type constructors
   (`issues/codata-type-constructor-carrier.md`).*
6. **`?` for `Option` (§3.5) is not built.** The parser lowers `?` to
   `result::Result::and_then` before any type is known, and choosing
   `Option::and_then` instead is type-directed. It stays in the issue.
7. **The discarded-result lint (§3.1) is not built.** `e;` at a non-`True`
   result is accepted silently.

The helpers of §2.3 landed as `List::for_m`, `List::traverse` (both over the
classes, structural) and `Tac::or_fail`. `when` waited for a customer. `mono`
was ported: its 75 `.bind(` sites are now statements, `match <- e` and
nested binds, and `regex`'s ten-link tower is ten statements.

## Appendix: probes (run on `3099a7d`, `heather check -L lib`)

- **P1, a class over a type constructor.** Works:
  - `inductive Box(A: Type)` passed as `M: Type → Type`;
  - `λ (A: Type) => Option<A>` as a constructor;
  - `record Monad(M: Type → Type)` with a value at `Option`, and a generic
    `twice({M}, m: Monad(M), x: M(Nat))`, where
    `twice(option_monad(), Some(3)) = Some(3)` holds by `refl`.

  Fails:
  - `class Bind<M: Type → Type>` does not parse ("expected `>` to close the
    type parameters, found Colon");
  - `class Monad(M: Type → Type)` has no carrier ("`Monad` needs its
    arguments here");
  - a dummy carrier `class Monad<U>(M: …)` with `:= infer` leaves the index
    unpinned;
  - `ap(Option, Some(1))` gives "`Option` cannot be used here";
  - `pick({M: Type → Type}, x: M(Nat))` at `Box(Nat)` or `Option<Nat>`
    gives "could not infer the implicit argument `M`".
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
  Since fixed (`docs/tactics/omega-measure-reduction-design.md` §18): with `match h:`
  a record state's obligation spells and closes by the default `omega`, as
  P5's does without its `on`.
- **P5, `while` with parameter state.** `cd_loop(m, out) decreases m` with
  `match h: m.leb(0)` and an `on ?dec1` discharge checks, and
  `cd_loop(3, Nil) = [1, 2, 3]` by `refl`. `cd_loop_unfold` is refused,
  because the lifted obligation depends on the match equation
  (`unfolding-computed-scrutinee`).
8. **Over `Tac`, a bind costs more in the gate than the method call did.**
   `Bind::seq` is generic in `M`, and `Tac` (a tier-2 declaration) has no
   type code function, so `M := λ A. ⌜Tac<El A>⌝` and every `M(X)` in the
   call is a β-redex over `Tac`'s whole code, compared structurally against
   the inline `Tac<X>`. A ported tactic module's declarations roughly double
   their gate counters (shape: a constant per bind proportional to `Tac`'s
   lowering). `Option` has a code function and pays nothing.
   `issues/tier2-type-code-functions.md` owns the fix; the lowering itself
   need not change.

## 14. R3a's first slice as built (2026-11-02)

Local state, statement forms and `for` over lists. What departs from §4–§7:

1. **Straight-line code and statement forms lower in the parser**
   (`crates/syntax/src/imperative.rs`), when each block closes, before its
   binds (§13 item 1). `let mut x = e;` is `let x = e;`, `x := e` is
   `let x: TypeOf(x) = e;`, and a statement `if`/`match` is one annotated
   join per local it assigns. The annotation is `TypeOf(x)`, the type of the
   local's current value, so the parser needs no types; §5.1's "layer 2
   runs in the elaborator" holds only for loops (item 5).
2. **A statement body belongs to its enclosing scope.** An inner block
   cannot tell when it closes whether an assignment in it is an outer
   local's, so it leaves the assignment as a residual and the block that
   declared the local rewrites the statement holding it. An inner form that
   assigns an outer local becomes the residual `x := match c { … { body; x } }`.
   A residual left at the end of the declaration is the "not mutable"
   refusal, which also covers assignments through a λ or a block in value
   position.
3. **Joins of several locals are staged.** Each copy of the form reads the
   locals as they were before it, so each join lands in a private
   `#stageN` first and the locals are rebound after the last. Without this
   a later copy's condition would read an earlier join's result (found by
   `count_words`, whose `else if inside = False` reads a local the same `if`
   assigns). *Amended (2026-11-12):* there is one copy, not one per local.
   Each arm ends in the state `Mutated(v₁, Mutated(v₂, …))` the loop
   lowering threads, annotated `Mutated<TypeOf(v₁), …>`, bound once at
   `#stageN`, and the locals are read out of it with `.after`/`.value`. A
   copy per local copied each branch's calls too: a recursive call ran
   once per local per level, exponentially
   (issues/statement-form-join-copies-calls.md).
4. **`else` is optional only on a statement `if`, and `else if` chains.**
   `{}` is a statement body next to a real one (`None => {}`), while an
   `if`/`match` of `{}` alone stays the empty proof block.
5. **`for x in xs` lifts in the elaborator** (`crates/elab/src/loops.rs`), as
   `decreases` does: the parser threads the locals the body assigns through
   a `\0loop` marker, and before the declaration is elaborated the loop
   becomes `f::step` (and `f::State` for several locals) over
   `List::foldl`. Each part is an ordinary declaration checked the
   ordinary way. The step's telescope is the declaration's solver
   parameters, the captures (the locals the body mentions, at the types the
   `BinderTys` oracle recovers from the part of the scope they read), the
   state, then the element. With one local the state is that local, so
   `sum::step(n, x) = n + x` by `refl`. The names are minted `f#step` and
   designated `f::step` after `f` exists, as `f#body` is. A step with loops
   of its own is lowered the same way.
6. **`f::State`'s fields follow the locals' declaration order**, not the
   order the body assigns them, so `count_words::State(words, inside)` reads
   as the function was written.
7. **`f_unfold` is generated for functions with a loop**, not yet for every
   function with a layer-2 statement. It is always attempted and never a
   reason to refuse `f`.
8. **Not built yet:** `break`/`continue`/`return` (`ForStep`, `List::for_in`; built since, §15),
   ranges, labels, `while` (both kinds), loops in a carrier scope (§6),
   assignment to field paths (built since, §20), `mut self`, destructuring `for` binders, and
   loops under a `match` arm that binds. A `for` iterates a `List` only.
   A loop inside a statement `if` that assigns several locals was copied
   into each join, and so lifted once per copy (one join since
   2026-11-12, item 3).
9. **Step facts are `split_all; all_goals { omega }`** over the step's
   nested `if` (`count_words_step_at_most_one` in
   `lib/_tests/std/core/imperative_statements_tests.hthr`), and facts by
   `refl` at a neutral state work too. A condition on a Bool equation
   (`if s.inside = False`) was refused by the kernel until 2026-11-06
   (`issues/split-all-nested-if-omega-kernel-refusal.md`).

## 15. Early exit as built (2026-11-02)

`break`, `continue` and `return e` in a `for` body, over §5.2's `ForStep`
and `List::for_in` (both in `lib/std/data/list.hthr`). What departs from
§5.2:

1. **Exits lower in tail position, in the parser.** `break;`, `continue;`
   and `return e;` are statements only before `;` or `}`, so the words stay
   usable as names elsewhere. A loop body that holds an exit is lowered by
   `tail` (`crates/syntax/src/imperative.rs`): a statement form that exits
   takes the rest of the body into each of its arms, so the body becomes
   one expression whose leaves are `\0next(v̄)`, `\0brk(v̄)` and
   `\0ret(e)`. The elaborator turns the leaves into `ForStep::Next(s)`,
   `ForStep::Break(s)` and `ForStep::Return(e)`, and the loop into
   `xs.for_in(step, init)`. A body with no exit still uses `foldl`.
2. **After the loop the state is read once**, as `#forN#s =
   #forN.state(init)`, where `ForStep::state` keeps `Next`'s and `Break`'s
   state and gives `init` for `Return`. Every local the loop assigns is then
   read from `#forN#s`.
3. **A returning loop splits the function body.** The parser nests the rest
   of the body after such a loop in `\0after(#forN, rest)`, and the
   elaborator builds `match #forN { Return(r) => r, _ => rest }`, so
   `find_index` computes by `refl` both ways (P3). The step's `R` is the
   function's result type when the body may `return`, and otherwise the
   state's own type, which no leaf ever builds.
4. **A stateless search is a loop.** A `for` that assigns no local but may
   `return` has a state record with no fields, whose one value is the
   constructor itself.
5. **Refused, each at parse time:** an exit outside any loop, a statement
   after an exit in the same block ("nothing after `break` runs"), `return`
   outside a `for`, and a returning loop that is not a statement of the
   function's own body (nested in another loop or in a statement form). The
   last needs the enclosing step to carry the `Return` out, which is §6.3's
   agreement between `?` and `return` and not built yet. A nested loop's
   `break` and `continue` are its own.
6. **Not built yet:** labels, `return` from a nested or conditional loop,
   ranges, `while`, and the `List::for_in_invariant` theorem (§7.2).
7. **In a `mut self` method** (§8.2, built 2026-11-02 after the above),
   `return e` leaves with the receiver as the body has threaded it there:
   after the body is lowered, each `\0ret(e)` leaf of a returning loop is
   rewritten to `\0ret(Mutated(x, e))`, so the loop's `Return` is the
   method's whole result, as the body's own end `Mutated(x, value)` is. The
   leaf reads `x` where it stands, which is the loop state's alias when the
   body calls on the receiver or assigns it, and the receiver as it came in
   when the loop only searches. The refusals are pure code's (5).

## 16. `while` as built (2026-11-02)

`while c decreases m { body }`, following §5.3. What departs from it:

1. **The parser reuses the `for` marker.** A `while` is `\0for(\0while(
   decide_bit<c>(), m), λ #whileN => body)`, so its locals are threaded,
   read back and left as residuals exactly as a `for`'s are. The condition
   is decided as a plain `if` decides it. `while` is a statement only
   where a `while` statement can start, so it stays usable as a name.
2. **`f::run` takes the state as separate parameters and returns the
   state**, a single local's own type or `f::State`, so the loop reads back
   like a `for`. The body is **hoisted above the condition's match**:
   `fn f#run(c̄, v̄) → S decreases m { body′; match h: decide_bit<c>() {
   True => f#run(c̄, v̄′), False => v̄ } }`. The body is pure, so the `False`
   arm ignoring its `let`s changes nothing. Keeping the `let`s out of the
   arm keeps them out of the shapes the unfolding companions handle worst.
3. **The body is put in SSA form** (`crates/elab/src/alpha.rs`): each
   top-level `let` that rebinds a name gets a fresh `name__N`, along with
   every later occurrence of it, so the condition's match, placed after
   the hoisted `let`s, still reads the parameters. This also kept two
   `decreases` bugs away (the measure's `m` reading a shadowing `m`, and
   the unfolding companions declining shadowed binders); the `decreases`
   lowering now deshadows every body itself (`alpha::deshadow`,
   `issues/decreases-shadowed-let.md`), so hand-written functions no
   longer hit them either.
4. **`f::run_unfold` is generated** (§7.3's dependency, unfolding over a
   computed scrutinee, has landed). It needed one fix in `measure.rs`: a
   lifted obligation's telescope now includes an equation binder about a
   binder it needs. An argument passed through a `let` alias otherwise
   reached the goal as the alias, and the arm's `h` about the parameter
   behind it was dropped (`lib/_tests/std/core/decreases_unfolding_tests.hthr`).
5. **The obligation is `omega`'s.** It reads the condition from
   `h : decide_bit<c>() = True`, so a module with a `while` imports `omega`
   and `int`, as any `decreases` function does. A body that does not
   decrease the measure is refused at its obligation. The message still
   suggests `on ?dec1 := …`, which a `while` cannot yet name (no loop
   labels).
6. **Not built yet:** `break`/`continue`/`return` in a `while` (refused at
   parse time), the fuelled form, a `while` inside a `decreases` function
   or holding a `for` (the generated `f#run` is a `decreases` function, and
   loops in those are refused), and labels.

## 17. Ranges as built (2026-11-02)

`for i in a..b` is `List::range_from(a, b - a)` (new in `list.hthr`, with
`len_range_from`, built at the end as `range` is), and `for i in 0..n` is
`List::range(n)`, so the loop is an ordinary `for`. That keeps
`List::len_range` and the native counting lemmas in reach. `..` is not a
token. The parser reads two `.`s as a range only while parsing a `for`
header, and anywhere else it refuses them with a message pointing at
`range_from`. No `Range` type exists, as §5.2 planned.

## 18. `while` with no measure as built (2026-11-03)

`while c { body }` with no `decreases`, in a block over a carrier with an
`Iterate` instance (`lib/std/itree/itree.hthr`: `iter: (A → M(Step<A, B>))
→ A → M(B)`, an Elgot monad; instances at `CoTree<_>(E)` and so at
`Partial`). Probes: `lib/_tests/std/itree/partial_fn_tests.hthr`. What it
does, and what departs from §5.3 and §6:

1. **It lowers in the parser, whole.** The header is `\0while(decide_bit<c>())`
   with no measure, so `crate::imperative` threads the locals the body
   assigns exactly as a `for`'s, and then writes the loop itself instead of
   the `\0loop` marker the elaborator lifts. No named step is generated: the
   step is a λ in the block, so captures need no types.
2. **The step** is `λ (#s: TypeOf(v̄)) => { v̄ = #s; match decide_bit<c>() {
   True => { body; Pointed::ret(Step::Continue(v̄)) }, False =>
   Pointed::ret(Step::Break(v̄)) } }`. With several locals the state is
   nested in the prelude's pair, `Mutated(v₁, Mutated(v₂, v₃))`, read back
   by `.after`/`.value`; this needs no declaration the parser cannot write.
   The annotation is the locals' types before the loop, which `:=` keeps.
3. **The loop and the rest of the block are one call**,
   `Iterate::then(init, step, λ #bindN => rest)`. The parser binds the loop
   (`let #whileN = (<- \0iterate(step, init));`), and the bind lowering
   writes that bind as one call instead of `Bind::seq(Iterate::loop(…), …)`.
   That matters: `Bind::seq`'s first argument is inferred, and the step λ's
   `match` cannot be checked while `M` is unknown. As one call, both λs are
   checking-only arguments, scheduled after `M` is learned from the block's
   expected type.
4. **The body's binds wait.** A loop body's block closes before its
   enclosing statement knows which locals the loop threads, and lowering
   its binds at close would bury its assignments inside a continuation. So
   the body of a `while` with no measure keeps its `\0bind` markers when it
   closes (`Parser::defer_binds`) and they are lowered in the step's `True`
   arm, after the state is read.
5. **Refusals.** In a carrier with no `Iterate` instance, and in pure code,
   the loop is refused with its reason ("a `while` with no measure may go
   round forever, so it runs only in a block over a carrier that can
   iterate …"), restated by `Elaborator::restate_loop_error` from the
   instance search, the unbound `Iterate::then`, or the step's motive
   failure. A loop that assigns no local is refused at parse time: its
   condition can never change.
6. **Not built yet:** `break`/`continue`/`return` in it (as for a measured
   `while`), a `for` in a carrier block (`List::for_m`, §6.1), and a
   statement `if`/`match` whose arms bind inside the loop body (their binds
   are lowered when the arm closes, as anywhere in a carrier block). The
   tree-sitter grammar has the optional `decreases`; its `parser.c` is
   regenerated with the binding statements
   (`issues/tree-sitter-binding-statements.md`).

## 19. A branch that ends a block as built (2026-11-12)

`issues/mut-self-tail-branch-receiver.md`. A block's last expression is
the last thing it computes. Two rules had treated a branch there as a value
like any other, and both made a loop written as a method impossible: its
arms could not assign the block's locals (§4: an assignment reaches a
local of its own scope, and an arm that yields a value was a scope of its
own), and a `mut self` body bound its end to a name before returning the
receiver beside it (§8.2), so the branch stood in inference position and
its arms could not reach the receiver. Probes:
`lib/_tests/std/core/imperative_statements_tests.hthr`,
`decreases_unfolding_tests.hthr` (the recursions),
`lib/_tests/native/runtime/runtime_span_tests.hthr` (`List::fill_all`);
parse-level facts in `crates/syntax/tests/imperative_statements.rs`.

### 19.1 The arms of a tail branch update the block's locals

```heather
fn bump_if(n: Nat, b: Bool) → Nat {
    let mut acc = n;
    if b {
        acc := acc + 1;
        acc + acc
    } else {
        acc
    }
}
```

Nothing after the branch reads `acc`, so an assignment in an arm is a
shadowing `let` there and needs no join. When a block closes,
`imperative::lower_block` lowers each arm of its result again with the
block's mutable locals in scope (`claim_tail`), which claims the residual
assignments and method-call candidates the arm's own lowering left, and so
on through an arm's own tail. A name the arm's pattern or its equation
binds is the pattern's in that arm. A branch that does not end the block
that declared the local (`let y = if c { x := 2; x } else { x };`) is a
value as before, and its assignment is refused.

This is not §5.5's join point: a statement `if` in the middle of a block
still joins per variable. It is the case where no join is needed.

### 19.2 A `mut self` body that ends in a branch returns its receiver per arm

```heather
fn Counter::tick_some(mut self c: Counter, m: Nat) → Nat {
    match m {
        Zero => 0,
        Succ(k) => {
            c.tick(k);
            k
        },
    }
}
// match m { Zero => Mutated(c, 0), Succ(k) => { c.tick(k); Mutated(c, k) } }
```

The receiver after the branch is a different one per arm, so the parser
ends each arm as it ends a body (`Parser::receiver_end`), and §19.1 gives
the arm's statements the receiver. The branch is then checked at the
method's `Mutated<C, R>`, so it needs no motive.

- **Only where an arm updates the receiver.** A branch whose arms leave it
  alone keeps the lowering it had, `Mutated(c, match … )`: the receiver
  after the call is then known whichever arm runs, which a proof about
  `.after` at a neutral scrutinee relies on (`tick_pick_after`). "Updates"
  is read off the arm: an assignment to the receiver, or a method call on
  it as a statement, bound by a `let`, or ending the arm. The parser cannot
  know whether a called method is `mut self`, so a call that turns out not
  to update is still returned per arm; the term is the same function.
- **Not where an arm rebinds the receiver's name** (a `let`, a pattern
  variable): the name at that arm's end is not the receiver, so the branch
  stays a value and an update in another arm is refused as before.
- **Not under a written motive**: `match e as λ z => T { … }` states the
  branch's type, which is the value's.
- **The value stands in the record.** `Mutated(c, value)` is written with
  the value in place, no longer bound first, so it is checked at the
  result type: `0` at the end of a method returning `u64` is a word.

### 19.3 The method's own call that ends its body is the body's result

```heather
fn Counter::fill_all(mut self c: Counter, m: Nat) → Nat decreases m {
    match h: decide_bit<1 <= m>() {
        False => m,
        True => {
            c.tick(m);
            c.fill_all(m - 1)
        },
    }
}
```

`c.fill_all(m - 1)` returns the receiver and the value both, which is what
the arm returns. Bound and taken apart (`let w = …; Mutated(w.after,
w.value)`), the recursion would be a call in a `let`, which a `decreases`
function's companions do not follow and a `runtime fn`'s loop is not. So
the parser writes the method's own call on the receiver, where it ends the
body or a tail arm, as `\0mutated_whole(c.f(ā))`
(`imperative::MUTATED_WHOLE`), and the elaborator reads it as the call
itself; under `decreases` the self-call rewrite spells it `f(c, ā)` with
the others (`measure::MethodCalls::whole`). The equation `fill_all_unfold`
states is the hand-threaded function's, and a `runtime fn` written this
way has the program of the one written with `Mutated` by hand
(`fill_all_is_fill_from`, by `refl`).

"Its own" is the method's base name called on the receiver parameter.
Another method's call there is bound and taken apart as before: every
`mut self` method that ended in a call keeps its term, and the generator's
rule for how a span function ends (a `Mutated`, a branch of them, or its
own call) is unchanged.

### 19.4 Not built

- A tail call of another `mut self` method as the body's result (it would
  need the generator to accept a callee's end as the caller's).
- A branch in the middle of a body whose arms update the receiver and
  yield a value (`let got = if b { c.tick(1); 1 } else { 0 };`): the
  statement spelling with a `let mut` for the value works, at the cost
  `issues/statement-form-join-copies-calls.md` records.
- `return` outside a loop (§5.5), which this does not touch.
- An arm that binds (`let x <- e;`) before it updates: the arm's binds are
  lowered when it closes (§13), which puts what follows them under a λ, and
  the update is refused there as it was.

## 20. A field path as a place as built (2026-11-12)

`issues/field-path-places.md`. §4 planned `:=` "with field paths" and
built the local. A record that holds another could update the inner one
only by rebuilding itself by hand, which is what stood between methods on
a span of bytes and methods on a type that wraps the span
(`issues/sha256-context-type.md`).

A **place** is a mutable local followed by field names: `x`, `x.f`,
`x.f.g`. A call, an index or a method in the path makes it no place.

```heather
record Tally { left: Counter, right: Counter, total: Nat }

fn Tally::bump(mut self p: Tally, by: Nat) → Nat {
    p.total := p.total + by;
    let was = p.left.tick(by);
    p.right.tick(was);
    p.total
}
```

### 20.1 Assignment

`x.f := e` is `x := x with { f = e }`, written by the parser where the
assignment is read (`place_update`, `crates/syntax/src/imperative.rs`),
and `x.f.g := e` nests: `x := x with { f = x.f with { g = e } }`. From
there it is the assignment of §4 and §5.1: checked at the local's type,
threaded by the scopes that thread `x`, refused with "is not mutable"
where `x` is not. A field the record lacks is the record update's own
refusal, at the place.

### 20.2 A `mut self` method on a field

`x.f.m(a);` and `let p = x.f.m(a);` are candidates of the local `x`
(§8.2), claimed by the block that declared it exactly as `x.m(a)` is. The
elaborator decides, as it does there, by the method's type:

- `m` returns `Mutated`: `p` is the call's `value`, and `x` is rebound to
  `x with { f = call.after }`, built from the record update as written
  (`elaborate_mut_call`). Both read the one call.
- otherwise it is the ordinary call it was, and `x` is not touched. This is
  why the decision is the elaborator's and not a lowering: a parser that
  wrote the update for every call on a field would rewrite `x` to itself
  round every `x.items.len()`.

A `decreases` function's companions follow the receiver through a path
too: the walk that inlines a body's `let`s (`inline_lets`,
`crates/elab/src/measure.rs`) rebinds the local to the update with the
call's `after` in the field, and its substitution reads record updates and
literals, which it had left as written.

### 20.3 With §19

A tail arm that updates a field of the receiver is an arm that updates the
receiver, so the body returns it per arm (§19.2). An arm that is a bare
call on the receiver or on a field of it (`True => p.right.tick(2),`) is
bound first, as a block that ends in one is; before, only an arm written
as a block was. The method's own call is the body's result (§19.3) only on
the receiver itself, never on a field of it.

### 20.4 Not built

- A path through an index (`x.items[i] := e`) or through a constructor's
  argument of a type with several constructors.
- A place rooted at something other than a local (`f(x).g := e` has
  nothing to rebind).
- Any run-time meaning: a record has no runtime layout yet, so a
  `runtime fn` cannot hold one. The update is `C(…)` over projections,
  which is the identity on the other fields by the record's η; the layout
  work is what makes that a store into one field's bytes.

## 21. Ranges over words, and elements at a word, as built (2026-11-14)

SHA-256 as compiled methods (`lib/native/crypto/`) wrote its loops as
hand recursions, `decreases (48 - j).toNat()` with `if h: j < 48 { …;
s.expand(j + 1) } else { j }`, and its elements as `s.schedule.at(j + 14)`
and `s.schedule := s.schedule.put(j, x)`. The surface had `for i in a..b`
(§17) and `xs[i]` (docs/language/surface-fin-indexing-design.md §5), but a range
listed `Nat`s and an index was a `Fin`. Now:

```heather
runtime fn Sha256::expand(mut self s: Sha256) → u64 {
    for j in 0..48 {
        s.schedule[j + 16] := sha256_next(s.schedule[j + 14].zero_extend(32), …);
    }
    48
}
```

### 21.1 A range over words is a counted recursion

`for i in lo..hi` whose bounds are words (`u64`, `BitVec(w)`) is lifted
(`crates/elab/src/loops.rs`, `lift_counted`) to a `decreases` function
over `i` with the body under the test:

```heather
fn f#run(c̄, v̄, i: W) → S decreases (hi - i).toNat() {
    if i < hi { body; f#run(c̄, v̄′, i + 1) } else { v̄ }
}
```

and the loop to `f#run(c̄, v̄, lo)`. The test is written as an `if` whose
branches do not name its evidence (a match on the comparison's bit with
the bit's equation bound), so a proof the body leaves to a search (an
element's `inside`) reads `i < hi` from it, as it reads a hand-written
`if h:`. Not a fold over a list of words: a list has no word bound to
find a proof from, and a `runtime fn` compiles a counted recursion
already (`docs/native/layout-design.md` §9.3).

**At a `mut self` receiver it is a method.** Where the loop's state is
exactly the receiver of a `mut self` method `T::f`, the recursion is a
`mut self` method of `T`, `T::f_loop` (`T::f_loop2`, … with several
loops), `→ W` returning the count where it stopped, and the loop is the
receiver after `x.f_loop(c̄, lo)`. It is a member under a name of its
own, not a minted `f#run`, because a generator over it and a proof about
it name it as they name `T::f`. Under a prefix generator
(`runtime fn T::f`), the generator runs over each such method before
`T::f` (`HostMut::elab_prefixed`), so the loop compiles exactly as a
hand-written counted method does, and `T::f` calls it.

**A range of numerals** (`0..48`) lists `Nat`s as before, and counts
`u64` words where the declaration is refused at `Nat`
(`DeclarationsMut::elab_loop_decl`): a body that indexes an array at the
counter, or adds it to a word, needs it to be one. A refusal at both
reports the `Nat` reading with the word reading's reason beside it.

### 21.2 An element at a word

`xs[i]` whose index infers at a type that is not `Fin` is the
receiver's `at` method, `xs.at(i)` (`inference::index_by_method`): for
`[A; n]` that is `Vec::at`, which finds its proof that `i` is inside
(`stored_words.hthr`). A numeral, and an index that only checks (`FZ`),
keep the kernel's `nth` at `Fin(n)`.

`xs[i] := e` is a place (§20 extended): `p[i] := e` is `p := p.put(i,
e)`, written by the parser (`place_update`), so `x.f[i] := e` nests into
the record update. A `decreases` body's `xs[i]` has its found proof
lifted as `xs.at(i)`'s is (`measure::lift_found`).

### 21.3 Not built

- `break`, `continue` and `return` in a loop over words (refused by name).
- A loop over words whose state is the receiver and other locals: it is
  lifted as a plain `f#run` returning the state, which a `runtime fn`
  does not compile. (Built for one other local, §22.)
- A `mut self` method whose result is only its receiver (`→ ()`): each
  SHA-256 step returns its count. And the method a loop is lifted to is
  called by a one-call function, which the linked code keeps as a call
  (five per block in `sha256_compress`); inlining a function whose body
  is one call would remove it.
- `xs[i]` at a numeral on `[A; n]` in a `runtime fn` is the kernel's
  `nth`, which the reflector does not read; the SHA-256 round still
  writes `vector_index(s.working, 7, trivial)`.

## 22. Loops over a span in a `runtime fn`, as built (2026-11-17)

Minus asked that a compiled function over a byte span get what a laid
record's methods have: `for`, `while`, `let mut` locals, a loop in a
loop. Probes: `lib/_tests/native/runtime/runtime_lifted_loops_tests.hthr`.

### 22.1 The receiver and one other local: a method returning it

A `for` over words or a `while c decreases m` whose state is the receiver
`r` of a `mut self` method and **one** other local `o` lifts
(`crates/elab/src/loops.rs`, `Lift::receiver_in`) to a `mut self` method
of the receiver's type, named as §21.1 names one, `T::f_loop`:

```heather
fn T::f_loop(mut self r: T, c̄, o: O) → Mutated<T, O> decreases m {
    if c { body; r.f_loop(c̄, o′) } else { Mutated(r, o) }
}
```

(a `for` also takes its counter, and tests `i < hi`), and the loop is
the `Mutated` its call returns, read back by `.after` for `r` and
`.value` for `o` (`Shape::Mutated`). With the receiver alone the method
returns the counter, as §21.1 built. This is the shape a hand-written
span loop has (`sift` in examples/sort), so the generator compiles it as
one, and the function calls it.

Unlike §16's pure `while`, the body is **under** the test, not hoisted
above it: a store into the receiver may not run where the condition
fails, and the code would run it. Its claimed method calls on the
receiver are spelled as plain `let`s and put in SSA form first
(`measure::rebind_marked`, `alpha::ssa`): the test's equation reads the
receiver the method was called with, and a later rebinding of the same
name otherwise made the kernel compare it against the stored span
(a `∧` condition that reads the span, with a store in the body).

### 22.2 Loops nest

A `decreases` function's loops lift as any function's (`loops::lower` no
longer refuses one; its equation is the measure lowering's own
`f_unfold`, so §7.1's is not generated for it). A loop in a loop is a
loop in the method the outer one lifted to. An arm whose equation binder
is private (`__…`, the lifted test's own) may hold a loop: no source
names it.

### 22.3 A plain loop in a `runtime fn` is compiled

A loop whose state is not the receiver is still `f#run` (designed
`f::run`), but a prefix generator now runs over it as over the methods
(`Family::methods`), by its designed name, which a lookup resolves; its
measure companions (`body`, `rec`, `ext`, `irrel`) are designated under
that name too. The reflector finds a minted `f#run`'s code under
`f::run` (`rt_designed`). Its self-call is spelled by its base name, which
is how a member recurses (a qualified self-call is not in scope while the
member is checked).

### 22.4 A test of several conjuncts, and invariants

The insertion sort's inner loop is
`while 0 < j && key < s[j - 1] invariant j <= i ∧ i < s.len() decreases
j.toNat() { s[j] := s[j - 1]; j := j - 1; }`
(`docs/native/span-record-design.md`).

- **`&&` and `||` bind looser than the relations** (`<`, `<=`, `≈`, `≠`)
  and tighter than `=` (Minus, 2026-11-17): `0 < j && key < b` is a
  conjunction of two tests. A relation operand of `&&`/`||` is decided
  (`decide_bit<0 < j>()`), so it reads as the `Bool` it tests
  (`crates/syntax/src/parser.rs`, `bool_chain`).
- **A test is tested conjunct by conjunct** (`Lift::tested`): `c₁ && c₂`
  or `c₁ ∧ c₂` is a `match` on `c₁` whose `True` arm matches on `c₂`, each
  equation in scope for what follows, so `s[j - 1]` is elaborated where
  `0 < j` holds and `j - 1` does not wrap. An element read in a test is
  bound by a `let` just before its match: inside the proposition it would
  be part of a type, and every copy of that type would search for its
  found proof again.
- **`invariant P`** (after the test, before `decreases`): each conjunct of
  `P` is a squashed parameter `__invN_k: ∥Pₖ∥` of the lifted loop, found
  by `bv_omega` at the entry and, at the recursion, by a `have` at the end
  of the body over the state's latest names (`bitvec_omega::found_fact`),
  passed by name. Inside the body a search at a squashed goal reads the
  squashed facts in scope through the squash eliminator
  (`Checking::release_squashed_facts`). The facts stay squashed so that
  every proof of them is the same term, which the `#ext` companion needs.
- **Captured facts.** A lifted loop's obligations (`f#obl_N`) take the
  loop's fact parameters as evidence (`measure::lift_obligation`).
- **The invariant after the loop.** Each fact `Pₖ` is a theorem
  `T::f_loop#keepsK` over the loop's parameters, `∥Pₖ[r, o := the
  loop's result's .after, .value]∥`, proved by induction along the loop
  (`induct T::f_loop(…)`): where it stops, `bv_omega` from the fact it
  was given; where it recurs, the induction hypothesis (`Lift::keeps`).
  Right after the loop the caller binds `have __heldN_k: ∥Pₖ∥` at the
  loop's result by that theorem, so `s[j] := key` after the sort's inner
  loop finds `j < s.len()` from `j <= i` and `i < s.len()`. Each read
  of the result in a restated fact takes the span of the name it
  replaces (`at_result`): one span for every read made the dot-receiver
  cache answer a `.len()` with the wrong receiver.

### 22.5 Not built

- The negated test after the loop (`¬(0 < j && key < s[j - 1])`), and an
  invariant that is not about words (the stopping case is closed by
  `bv_omega`).
- `let key = s[i]` with no annotation before a loop that reads `key`:
  the loop lifter recovers a local's type by a query that does not run the
  read's found proof, and refuses (`annotate its let`).
- A loop's state of two locals besides the receiver, or of two locals in
  a plain loop: `f#State` is a record, which the generator has no layout
  for (refused with that reason).
- A byte (`u8`) local captured by a loop in a function that writes a
  span: such a function's code takes 64-bit words
  (`issues/runtime-repr-narrow-words.md`), so the probes carry the key
  as a `u64`.
