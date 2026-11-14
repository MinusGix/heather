# `When<T, P>`: a value that is there exactly when `P` holds

Design note, 2026-11-14. Minus's idea and rulings; the reading and the stages
are this note's. Tracked by `issues/when-proof-conditional-option.md`; this
note is corrected where the code disagrees, and each stage records what it
built under §11.

## 1. Rulings and where this comes from

Minus, 2026-11-14:

- A "proof conditional Option" for operations like `get`: inhabited if the
  condition holds. With the proof you take the value; without it you test,
  and the test puts you in the branch. The two cases are one type.
- The condition need not be decidable: it is data, so a value in hand shows
  the condition was computable in this case.
- **Exactly when `P`** (not only "`P` implies present").
- It wants a better name than `OptionP`. This note uses `When`; a rename is
  a search and replace, so nothing below depends on the name.
- It should have first-class support, "like how Rust does for Option/Result
  but even better", because it is a very valuable type for software.
- **No `checked` keyword prefix** (01:44Z): "either generalize `?` or think
  of another way of writing the same thing elegantly". §4 is that way.
- **Coercion is worth trying**, in its own PR with performance benchmarks:
  "It is valuable. Inference can be changed." §5.

It continues the 2026-11-13 ruling that a junk value is a sign of missing
automation and a partial operation takes a proof found implicitly (PR #607:
`Vec::at(v, i, inside: i.toNat() < n := bv_omega)`). What #607 left apart is
the other half: the runtime test is a hand-written `if h: i < n { v.at(i) }`
at each use, and `Option` forgets why a `None` was a `None`.

## 2. The type

```heather
inductive When<T, P> { Present(value: T, holds: P), Absent(fails: ¬P) }
```

- `When<Unit, P>` is a decision of `P`: the type is "a decision that carries
  a `T` on its yes side". Nobody supplies a decision procedure for `P` in
  general; whoever builds the value decided this case.
- Heather keeps proof relevance (`docs/decide-class-design.md` §1), so a
  `match` on a `When` eliminates into `Type` with no sort boundary, and
  `holds`/`fails` are ordinary fields.
- Module `lib/std/core/when.hthr`, methods on the type, probes in
  `lib/_tests/std/core/when_tests.hthr`.

Library surface (all ordinary functions by `match`, no kernel change):

| Member | Statement |
|---|---|
| `w.val(holds: P)` | the value; the `Absent` arm is `absurd(fails(holds))` |
| `w.decision()` | `P ∨ ¬P` |
| `w.option()` | `Option<T>`, forgetting why |
| `w.map(f)` | `When<U, P>` |
| `w.restate(to: Q → P, from: P → Q)` | `When<T, Q>`: the condition restated |
| `w.and_then(k: T → P → When<U, Q>, back: Q → P)` | `When<U, Q>` (§6) |
| `w.is_present()`, `w.unwrap_or(d)` | `Bool`, `T` |
| `When::of<P: Decide, T>(f: P → T)` | test, then build: the form §4 generates |
| `When::of_bit(f, bit, e)`, `When::of_cases(f, M, yes, no)` | `of` with its bit as a parameter, and the elimination a proof about a test goes through (§11) |
| `val_present`, `option_some_iff`, `map_val`, `of_val`, … | the laws a client cites |

`val` reduces whenever its subject reduces to a constructor, whatever the
proofs are. That is the property everything below leans on.

## 3. Two directions, and which function is the primitive

A partial operation is written in one of two ways, and each gets the other
form without a second definition.

**(a) The proof-taking function is the primitive** when the test is separate
from the work: `Vec::at`, checked addition, division at apartness, a list's
head. The function takes its condition as a parameter (found by a search
default, as in #607), and the `When` form is *derived* (§4): the same call,
where a `When` is wanted.

```heather
if let Present(x) = v.at(i) { … } else { … }   // v.at(i) : When<A, i.toNat() < n>
let x = v.at(i)?;                              // tested, absence propagated
```

This order is deliberate. The kernel and the compiler both want the
proof-taking function: its meaning is the total function, a record
function's pin stays `refl`, and its code has no compare to remove. A
hand-written `get` that tests and then a `val` on top of it is stuck on a
neutral index and compiles to a compare.

**(b) The `When`-returning function is the primitive** when the test *is*
the work, or is cheaper or dearer than building the value some other way: a
map lookup (`m.get(k): When<V, k ∈ m>`), a parse, a search. The caller with a
proof writes `m.get(k).val(h)` or lets it be found (§5).

## 4. The tested form: the same call, where a `When` is wanted

There is no keyword. A call of a proof-taking function has two readings
and its place picks one:

- **Where a `T` is wanted**, the condition is found by its search, as today.
- **Where a `When<T, P>` is wanted**, the call leaves the condition out and
  tests it. "Wanted" is the expected type: an annotation
  (`let w: When<_, _> = v.at(i);`), an argument or a result of that type,
  the scrutinee of a `match` or `if let` whose patterns are `Present`/`Absent`,
  and the operand of `?` (§6), which is how **`?` is generalized**:
  `v.at(i)?` tests and propagates absence, in one mark.

A condition the call writes (`inside := h`) is not tested; the call then
has only its first reading, and a `When` wanted there is a type error as
now.

- **Which parameters.** The first parameter of `f` whose default is a
  context search (`defaults::is_context_search`) and that the call does not
  give is tested; the call is `When<T, P>` of that one. A later such
  parameter is searched as usual, with the tested proof in scope: so a later
  condition may mention the earlier one, and one the search cannot find is
  refused with the usual default error, naming it (built 2026-11-14; this
  replaced "several give the conjunction", which could not express a later
  condition that depends on an earlier one).
- **What it elaborates to.** The same term as

  ```heather
  if h: P { Present(f(args, name := h), h) } else { Absent(h) }
  ```

  through the existing `if h: P` (`docs/decidable-if-expression-design.md`):
  the branch is on the decision's bit, so compiled code is the compare the
  programmer would have written, and a `Bool` or mixed condition is read the
  way `if` reads it.
- **The search is not run first.** Where a `When` is wanted the test is
  made even if the context could prove `P`; the law below is what removes a
  test that is known, and a caller who has the proof and wants no test
  writes the first reading. (Trying the search first would make the code's
  shape depend on what a tactic happened to find.)
- **No `Decide<P>`.** Refused, saying that `P` has no decision here and that
  a function whose own work decides it returns a `When` itself (§3b).
- **Unknown expected type.** `let w = v.at(i);` with nothing wanted is the
  first reading, and its error when the search fails says both ways out:
  prove it, or use it where a `When` is wanted (`match`, `if let`, `?`).
  An argument at a parameter whose type is a `When` still open in the
  call's implicits (`present_count(v.at(i))` with `present_count<T, P>`) is
  inferred, not checked, so it is the first reading too; giving the type
  arguments makes it a place a `When` is wanted.
- **The law**, proved once per `f` where it goes through by cases and
  `refl`: the tested form's `.val(h)` is `f(a, h)`. It is what lets a later
  stage drop the test when `h` is known (§8).

The elaborator knows the callee's signature and the expected type at the
call, so this is an elaboration of the call node and not a parser rewrite
(`crates/elab/src/tested.rs`). `P` is the parameter's domain as this call
instantiates it, which only the call's elaboration knows (an implicit length,
a method's receiver), so the call is first elaborated in a probe that stops
at the condition's default and records its goal; `P` is then bound, as a
`let` binds a type, to a name the rewritten call's binder is annotated with:
`When::of(λ (h: P) => f(args, name := h))`. The route is taken only where
the expected type's head is `When` (after a name lookup that a module which
cannot name `When` pays alone) or the call is a scrutinee under `Present`/
`Absent`; it costs one more elaboration of the call's arguments. It gives the proof by name, so the found-proof
lifting of #607 has nothing to lift here. This reads the expected type at
calls with a context-search default, so it re-elaborates the whole library
before it merges.

## 5. Use and flow: the facts a branch leaves

- **`match`** already gives `holds` and `fails` to the arms.
- **`if let Present(x) = w { … } else { … }`** puts the proof in scope of the
  success block and the refutation in scope of the `else` block, under
  private names tactics can read (the `__if_bitN` device of #607).
  `docs/positional-if-let-design.md` says the `else` block gets no negative
  evidence in general; a `When` is the case where the other constructor
  carries exactly that, so the rule is for this type (or for any
  two-constructor type whose other arm has only proofs, if that is as easy).
- **Early exit.** `let x = match w { Present(x, _) => x, Absent(_) => return e };`
  works today if `return` composes with `match` in that position; the sugar
  `let Present(x) = w else { return e };` leaves `P` known for the rest of
  the block. Build the sugar only if the long form reads badly in the probes.
- **Found proofs.** `w.val()` with the proof found. No single search fits
  every `P`, so `val`'s default is a small context search (working name
  `known`): a hypothesis in scope or a projection of one, then `omega`, then
  `bv_omega`. It is registered as a context search so the lifting applies in
  a `decreases` body. A failure names the missing fact and says: test it
  (`match`, `if let`) or prove it.
- **Coercion to `T`**, its own PR under the same issue (Minus: valuable,
  inference can be changed, bring benchmarks). A `When<T, P>` where a `T`
  is wanted takes the value with `P` found by the `known` search; it is §4
  read the other way, so the two together make "the call" and "the tested
  call" one expression everywhere. It adds a route at an expected-type
  mismatch, which is a hot path: measure with `scripts/perf ab`
  (`perf/CLAUDE.md`) on the library's elaboration with and without it, and
  re-elaborate the whole library. The route should be reached only after
  the ordinary check has failed and only when the found type's head is
  `When`, so code with no `When` pays one head comparison on a path that
  was already an error.

## 6. Propagation

`w?` in a function returning `When<U, Q>`, with `w: When<T, P>` (and `w`
may be a proof-taking call, tested because `?` wants a `When`, §4):

```heather
K[w?]   ≡   w.and_then(λ v h => K[v], back)      // back: Q → P
```

- `back` is why an absent `w` makes the whole result absent: `¬P` gives `¬Q`.
  It is found by the `known` search; with `Q` a conjunction that contains `P`
  it is a projection.
- The tail value is wrapped as `Present(value, holds)` with `holds: Q` found
  from the proofs the `?`s bound. Unlike `Result`, where the body writes
  `Ok(value)`, writing the proof by hand is the whole cost, so the wrap is
  implicit when the tail has type `U` and explicit `Present(…)` still works.
- **V1 states `Q`** in the signature. Inferring it (`→ When<U, _>` as the
  conjunction of what was tested) is the "better than Rust" end: the failure
  type is the function's exact precondition. It is a second step because a
  later condition mentions earlier values, so the inferred statement is a
  dependent conjunction and wants a readable spelling first.
- The existing walk (`crates/syntax/src/try_lower.rs`, one `Protocol` per
  propagation) lowers by syntax and cannot know the carrier, so either the
  marker's meaning is chosen by the elaborator from the scrutinee's type, or
  `When` takes the nested-bind protocol. Decide by reading that file; record
  which here.

A twin with an error value on the absent side (`Absent(error: E, fails: ¬P)`)
is `Result`'s counterpart. Not in V1; note what would be shared.

## 7. Two things to probe before building far

1. **Proofs inside values.** Two `Present(v, h1)` and `Present(v, h2)` are
   convertible only when the kernel sees `h1` and `h2` as one, which it does
   for conditions that are η-unit (`Le` by recursion, a word bound through
   `toNat`), and not in general. This is the hazard #607 met in `decreases`
   bodies (`issues/found-proof-differs-across-recursion-companions.md`,
   closed). The design avoids it by keeping `When` values transient (built,
   then consumed by `match`, `val` or `?`, all of which reduce without
   comparing proofs) and keeping specifications on the proof-taking
   function. Probe it anyway: a `decreases` function whose body uses
   a tested call, and a `When`-returning function called from two lowered
   companions. If it bites, the fix belongs to the type (an extensionality
   law used by the comparison), not to each client.
2. **Cost at the kernel.** a tested call under a neutral condition is a
   stuck `match` on a decision bit; a theorem about it goes by cases, not by
   `refl`. `docs/proof-patterns.md` has the rules (never `refl` between two
   computations, closed verdicts as `b = True`). The probes should include a
   literal index, a neutral index and an open element type
   (`docs/testing-generated-terms.md`: all four axes, with a negative
   control).

## 8. Native code (after V1, with the compilation work)

Not part of the first build; recorded so V1 does not close a door.

- **Representation.** With proofs erased a `When<T, P>` is an `Option<T>`;
  whichever layout `Option` gets (`docs/datarepr-design.md`), `When` shares.
- **A record function** (`docs/layout-design.md` §9.5) takes a tested `t.f.at(i)`
  as the accessor's compare with both arms written, which is the tested read
  it already has.
- **Dropping the test.** the tested call's `.val(h) = f(a, h)` is the same fact
  as the never-taken compare #607 left in the linked SHA-256. Both wait on
  the path-facts theory; they land together.
- `datarepr`'s partiality ladder (rung 1 silent discharge, rung 2 decide and
  bubble) is this type seen from the generator's side. When that work
  resumes it should bubble a `When`, not an outcome type of its own.

## 9. Stages and acceptance

Each stage is a PR that leaves the library green.

1. **The type and its library** (§2), with laws and probes. `Vec::at` and a
   checked `u64` addition (`a.toNat() + b.toNat() < 2^64`) written through
   `When::of` by hand, to see the shape before generating it.
2. **The tested call** (§4): the elaboration where a `When` is wanted, the
   refusals as `// expect-error:` probes (no decision; a dependent later
   condition; a written condition where a `When` is wanted), the law.
   Rewrite stage 1's two users with it. Run §7's probes here.
3. **Flow facts and `val`'s search** (§5).
4. **`?`** with a stated condition (§6), including on a proof-taking call.
5. **Coercion to `T`** (§5), with its benchmarks.

Later, each its own decision: inferred conditions, the error-carrying
twin, §8.

Rails for the build: new syntax and a new type do not change what the
elaborator infers for existing code, so `scripts/test --pr` is the final
lane for stages 1 and 2; stage 3's search and anything that touches
defaults or `if let` evidence re-elaborates the whole library before it
merges. Claims Heather can state are theorems in the module or probes in
`lib/_tests`, not Rust tests. File the work as an issue with `area:
language` and log rulings there.

## 10. Open, for Minus when it matters

- The name (`When` here).
- Whether `if let`'s negative evidence is for `When` alone or for every
  type of that shape.

## 11. What was built

**Stage 1** (`lib/std/core/when.hthr`, probes in
`lib/_tests/std/core/when_tests.hthr`).

- The members of §2, with `weaken` named `restate` (it takes both
  directions, so nothing is weakened), plus `is_present` and `unwrap_or`.
- `When::of<P: Decide, T>(f)` is written as the `if h: P` of §4. A proof
  about it cannot case that `if` today: its branch uses `h`, and motive
  synthesis abstracts the bit everywhere but inside `decide_true`'s type
  (`issues/if-evidence-proof-by-cases.md`, open). So `When::of_bit(f, bit,
  e)` takes the bit and its equation as parameters, `When::of_unfold` says
  `When::of(f)` is `of_bit` at `decide_bit<P>()` and `refl` (by `refl`: the
  `if` lowers to that term), and `When::of_cases` is the elimination every
  law about the test goes through. A tested call generated in stage 2 is the
  same term, so these laws cover it without one generated per use.
- The law `of_val` is `When::of(f).val(h) = f(h)` **given `same: (a, b: P)
  → f(a) = f(b)`**: in the `Present` arm the value is `f` at the proof the
  decision built, not at `h`. `same` is `refl` for `Vec::at` and a checked
  addition (they ignore the proof). For the Nat-indexed `vector_index`,
  which uses it, it is **not** `refl`: two proofs of `i < n` at an open `i`
  and `n` are two stuck terms. Stage 1 said otherwise without a probe at a
  neutral index; stage 2 corrected it, adding `vector_index_irrel` (by
  induction, in `vector.hthr`) and the probes `entry_val` and the refused
  `entry_val_refl`. A wrapper over such a function (`Vec::nth`) cites the
  same lemma, since the wrapper unfolds to it.
- The stage-1 users are in the tests: `word_at` over `Vec::at`,
  `checked_add` over `add_within(a, b, fits := bv_omega)`, `entry` over
  `vector_index` (open element type), and `both`, a chain of two reads by
  `and_then`. Literal indices compute by `refl`, neutral ones go through
  `of_val`/`of_option`/`of_option_none`, and two negative controls are
  `expect-error` declarations.
- `When` is not in the common prelude yet: a module imports `when`. Whether
  stage 2 needs it there (the elaborator names the type at the call) is
  decided there.

**Stage 2** (the tested call, `crates/elab/src/tested.rs`).

- Built as §4 says, with the first omitted condition tested and later ones
  searched. Places: a result or annotation of type `When`, an argument at a
  `When` parameter whose type is known, and the scrutinee of a `match` or
  `if let` whose arms name `Present`/`Absent`. The two stage-1 users are now
  `v.at(i)` and `add_within(a, b)` where a `When` is wanted.
- An arm's constructor is resolved, not read by its spelling: a type of the
  module's own (or another import's) with a constructor `Present` keeps
  its call's first reading, and so does an ambiguous bare name;
  `When::Present` is resolved through its type (`when_names_tests`).
- The test of an expected type runs on every checked call, so it reads
  structurally first: an inductive's tag names its declaration and module.
  Only a type with no tag in its shape is decoded, and only in a module
  that imports `when`. No table probe is on that path.
- Refusals, as `expect-error` probes: a written condition where a `When` is
  wanted (a mismatch: the call is not tested), a condition with no decision
  ("… has no decision (`Decide<…>`) here: give `name := …` and take the
  value, or call a function whose own work decides it and returns a
  `When`"), and a later condition the search cannot find. A failed search
  where `When` can be named now also says the call can be tested.
- The rewritten call's names are `__when_condition` and `__when_proof`,
  lexable like `__if_bitN`: a later default's tactic spells the proof back
  as source (`omega`'s certificate), and a `\0` name broke that.
- **§7.1, proofs in values across `decreases` companions.** A tested read
  as a `decreases` body's scrutinee checks, computes, and has its unfolding
  equation (`sum_from`, `count_from` in the tests). The unfolding needed one
  fix: its walk types a scrutinee alone (`Rewrite::scrut_ty`) and read the
  call as the first reading, so the arm's proof was untyped and the lifted
  obligation could not see it; it now types a call under `Present`/`Absent`
  as its test (`match_scrut_ty`, through a private marker the inference
  entry reads). The tested call names its proof, so there is no found proof
  for two companions to differ on.
- **§7.2, kernel cost at a neutral condition.** A theorem about a tested
  call at a neutral index goes by `When::of_cases`, a case split on the bit
  and one conversion per arm; its cost does not grow with the callee
  (`nth_or_inside`, `nth_or_outside`). Comparing a read at the decision's
  proof with a read at the caller's is where it can fail: that needs the
  callee's proof irrelevance (`same`), which is `refl` only for a callee that
  ignores its proof.
