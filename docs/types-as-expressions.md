# Types are expressions

Status: **landed**, 2026-08-01. Tracking issue: `issues/type-definitions.md`
(route 2, by explicit decision — a `type` declaration would have been route 1).

A type is an ordinary expression whose type is a universe. That sentence was
already half true — `Type<n>` is writable, `a = b` is an `ExprKind::Eq`, and
`El ⌜T⌝ ⇝ T` is a kernel reduction — and this round makes it true of the
**function type** as well. The consequence the round exists for is that a
type-valued `fn` is an ordinary `fn`, so a statement shape can have a name:

```heather
fn Refines(p1: Prog, i1: Ir, p2: Prog, i2: Ir) -> Type {
    (env: Val) -> (vs: Val) -> Converges(p1, env, i1, vs) -> Converges(p2, env, i2, vs)
}

theorem refines_refl_conv(prog: Prog, ir: Ir): Refines(prog, ir, prog, ir)
{ λ env vs c => c }
```

**No kernel change, no new declaration form, no new typing rule.** The whole
round is one grammar fall-through plus four structural readers in the
elaborator that had to learn to look through `El`.

---

## 1. Why route 2 rather than a `type` declaration

Route 1 (`type Refines(…) = …`, a parameterized synonym) is a new declaration
form with its own scoping, its own arity checking, its own δ story, and its
own answer to "where may it be used". Route 2 has none of those, because a
type-valued `fn` reuses the ones `fn` already has. The cost of route 2 is a
grammar decision with an ambiguity surface; §3 is the finding that the surface
is empty.

Route 2 also **subsumes** route 1: everything `type` could abbreviate, a `fn`
returning `Type` abbreviates, and a `fn` additionally computes — `fn F(n: Nat)
-> Type { … }` may `match` on `n`, which a synonym could not.

## 2. Code coverage: which formers can be abbreviated

A type-valued `fn`'s body is elaborated as a type and then **quoted into its
code** (`crates/elab/src/code.rs`'s `code_of`, the `Type → Term : Ty l`
direction of the Tarski universe). A former with no code returns `None` and
becomes a diagnostic. So the round's reach is exactly `code_of`'s domain.

The audit, against `crates/kernel/src/term.rs`'s `Type` variants:

| Former | Code | Reachable from the surface |
| --- | --- | --- |
| `Nat` | `TmNat` | yes |
| `Ty l` | `TmTy` | yes (`Type<n>`) |
| `El` | identity | yes |
| `Pi` | `TmPi` | yes — **this round's customer** |
| `Id` | `TmId` | yes (`a = b`) |
| `Sigma` | `TmSigma` | yes (records, tier-0 inductives) |
| `Unit` / `Empty` | `TmUnit` / `TmEmpty` | yes (terminators, tags) |
| `Sum` | `TmSum` | yes (multi-constructor inductives) |
| `W` | `TmW` | yes (tier 2, not yet lowered to) |
| `Vec` | `TmVec` | yes (`[T; n]`) |
| `Fin` | `TmFin` | yes |
| `Wf` | `TmWf` | yes (tier-1 inductives) |
| `UPi` | — | **no**: layer m, never writable (surface-universe §7) |
| `SEq` / `SEmpty` | — | no: `crates/elab` never builds one |
| `GlobalTy` | — | no: `crates/elab` never builds one |

**Finding: every surface-writable type former has a code.** The three
uncovered variants are unreachable from any source text — `UPi` by the
universe round's decision, `SEq`/`SEmpty`/`GlobalTy` because the elaborator
has no path that constructs them (`grep` over `crates/elab/src` finds no
occurrence of any of the three).

The consequence for testing is worth stating plainly, since the brief for this
round asked for the uncovered-former diagnostic to be pinned: **it cannot be**.
`lib.rs`'s "this type has no code, so it cannot be written where a term is
expected" is currently *unreachable* from the surface. It is not dead code to
delete — it is the guard that keeps `code_of`'s partiality from becoming an
`unwrap` the day a new former lands — but it has no test because it has no
input. Recorded here so the absence is a known fact rather than an oversight.

### 2.1 Levels

`code_of` does not cap the level; `Ty l` is a code for every `l` and
`TmTy(l) : Ty (1+l)`. What caps a *declaration* is that `Type<n>`'s level is
written, never inferred (surface-universe §5), and universes are
non-cumulative (§6). So:

- A type-valued `fn`'s result type states the level. `-> Type` (= `Type<0>`)
  means the body must land at level 0 **exactly**; `-> Type<1>` means 1.
- `Refines`'s body is a `Π` chain over `Val`, `Ir`, `Prog` and record
  formations, all of which are level-0 encodings, and `Level::max` of zeros is
  zero. So `Refines` lands at `Type<0>` and its quantifiers fit under the cap
  with room to spare. A `Nat -> Nat` parameter is likewise level 0.
- The failure mode when a body does not fit is the non-cumulativity message,
  naming both levels — `fn Bad() -> Type { Type }` is rejected because `Type<0>`
  is a value at level 1. That is the round's level negative control.

## 3. Grammar: the ambiguity surface is empty

`->` in expression position was **always a parse error before this round**.
The token appears in exactly four places in `crates/syntax/src/parser.rs`, and
none of them follows an expression:

1. `group_is_type`'s lookahead — a *predicate*, consumes nothing.
2. `ty()`'s binder group `(x: A) -> B` — follows `)`, after a `:` that the
   expression grammar does not have.
3. `ty()`'s arrow between `ty_atom`s.
4. A declaration's `fn f(…) -> T` — follows the parameter list's `)`, parsed
   by the parameter loop and never by `expr`.
5. The retired motive spelling `as z -> T`, diagnosed by a two-token lookahead
   *before* any expression is parsed.

So admitting `->` after an expression is a **pure extension**: no input that
parsed before parses differently, and no backtracking is needed. Likewise
`(x: A) ->` at the start of an expression — `:` is not in the expression
grammar at all, so the same three-token lookahead `ty()` already uses is
unambiguous.

The landing zone is therefore **not** conservative, which is the round's one
surprise: `->` and dependent binder groups are allowed in *every* expression
position, not a chosen subset. `Parser::expr` gains two things —

- a leading `at_binder_group()` check that hands off to `ty()`, and
- a trailing `Arrow` check that reads the left side as the domain and lets
  `ty()` take the (right-associative) codomain

— and both come back as `ExprKind::TyLit`, the node the motive-body round
introduced for exactly this purpose.

### 3.1 One parse, not two

The reading of an expression *as a type* is now a single total function,
`parser.rs`'s free `expr_as_ty`, shared by `ty_atom`'s fall-through and by the
arrow's domain. This is what keeps the two spellings from drifting, and it is
also what keeps the old type grammar's *output* identical: `ty_atom` now parses
`Nat -> Nat` through `expr`, gets back a `TyLit`, and **unwraps** it — so the
AST is the same `TyKind::Fn` it always was and not an `El` of its own code.
`ty()`'s own early cases (`Type<n>`, `[T; n]`, `D<A>`, the binder group) still
fire first, so nothing that used to take a fast path lost it.

### 3.2 Precedence

`=` binds tighter than `->`, in both positions, because there is one parse.
`a = b -> c = d` is `(a = b) -> (c = d)`. This matches what `ty()` already did
(its arrow's sides are `ty_atom`s, and `ty_atom` is where `=` is read), so the
change introduces no new precedence to remember.

### 3.3 What is *not* in the landing zone

- `{x: A} -> B` in expression position: still the implicit-binder diagnostic
  (`issues/implicit-binders-in-function-types.md`), untouched.
- `issues/annotated-let-swallows-the-equals.md` is **not made worse**: the
  annotation position still parses with `ty()`, which is unchanged, and the
  round adds no new top-level `=` to a `let`'s value that was not already
  possible.
- `List<Nat> -> Nat` written in *expression* position needs the domain
  parenthesised, because `atom` reads `<` as the `lt` operator there. Type
  position is unaffected (`ty_atom` handles `D<A>` before the fall-through).
  Not a regression — no such expression parsed before — and not worth a
  lookahead until something wants it.

## 4. Elaboration: lazy decode, and the four readers that had to learn it

A named abbreviation is elaborated in one place and consumed in another:

- **Declaration.** The body is checked against `Ty l`, which routes through
  `elab_at_universe` → `expr_as_ty` → `elab_ty` → `code_of`. The `fn`'s value
  is the *code*.
- **Use.** `Refines(a, b, c, d)` in type position is `TyKind::OfExpr`, the
  call is inferred at type `Ty 0`, and the type is `El` of it. Conversion sees
  a δ-stuck head (`conv.rs`'s `delta_head_ty` looks through `El`) and unfolds
  **lazily**, only when a comparison needs it.

The consequence that cost this round its debugging time: **`El ⌜T⌝ ⇝ T` is a
lazy decode.** `step_type` on `El(TmSigma{fst, snd})` produces
`Sigma { fst: El(fst), snd: El(snd) }` — the children stay wrapped. So a
lowered type that arrived through an abbreviation is `El`-headed at *every*
level below the first, and every reader that walks its structure sees a code
where it expects a `Σ`.

Readers that call `whnf` at each step were already fine — `build_fields` and
the `match` field walk both re-normalize as they descend. The ones that walked
*structurally*, and now go through a new `decoded` helper in
`crates/elab/src/inductive.rs`, are:

| Reader | What went wrong |
| --- | --- |
| `tag_of` | returned `None`; a constructor in checking position was rejected as "not the expected type here" |
| `read_tag` | same, one level down |
| `spine` | would have failed on a multi-constructor `+` |
| `tag_value` | **emitted `⟨⟩` where a pair was needed** |

The last one is the round's real defect, and it is worth reading twice. Tag 0's
tag type *is* `Unit`, so `tag_value` falling through to `Triv` is correct for
the first declaration in a file and wrong for every one after it. The symptom
was a kernel `NotConvertible` on a term the elaborator was happy with — the
"checked theorem about the wrong object" half of
`docs/testing-generated-terms.md`'s dichotomy, caught only because
`lib/ir_v1.hthr` has many declarations. A single-declaration test could not see
it, which is why `crates/elab/tests/types_as_expressions.rs` §5 varies the
declaration *order*.

**Two more joined the table on 2026-08-01** (`docs/record-type-values.md` §4),
from a shape this round could not produce: a type reached through a
`Val -> Type` *value* is `El` of a **β-redex**, which `decoded` declines by
design. `record_of` (behind `resolve_dot`) now falls back to one `whnf` when
the structural read fails, and `unify_ty` decodes its *subject* before the
congruence walk.

**And the list is now closed** (`docs/record-type-values.md` §6, the audit —
`issues/el-reader-decode-audit.md`). Six more readers were repaired and the
rest of the roster is classified there, with a reason per entry. Four of the
six were broken by *this* round rather than by the `Val -> Type` one, and the
route is the sentence above about laziness taken one step further: because the
children of a decoded code stay wrapped, a record's **field** types are
`El`-headed whenever the record itself arrived as a code. That is how a
vector literal and `map`/`fold`'s receivers were reached — with no function
value anywhere in the program.

| Reader | What went wrong | Fix |
| --- | --- | --- |
| `record_of` behind `Stmt::LetRecord` | `let { a } = p` declined a receiver `p.a` accepted | `record_of_at` |
| `indexed_of` (three call sites) | an indexed family reached through a name was not a family | `indexed_of_at`, step-and-retest |
| `elab_vec_lit` | a record's vector field is `El (TmVec …)` | `decoded` |
| `elab_vec_map` / `elab_vec_fold` receivers | the same, projected | `decoded` |
| the container-proof motive test (`wf.rs`) | **naming** a container induction's statement re-broke it | one `whnf`, in a rebuilt context |

The two `decoded`s and the step-and-retest are not `whnf` on purpose: `Vec`
reduces on its length and an indexed family on its index, so normalizing to
find them destroys them (§6.3 there). The audit found no reader of
`tag_value`'s kind — none fell through to a *default* rather than a
diagnostic — which is the property the negative controls in
`crates/elab/tests/el_reader_audit.rs` exist to hold.

`decoded` is deliberately **context-free**: it admits only an `El` whose code
is a canonical former, and those rules of `step_type` are pure rewrites that
never consult the local context or δ. An `El` of a *neutral* code — an
unapplied abbreviation, a variable at `Type<n>` — is left exactly as it is,
because unfolding that is conversion's job and doing it here would throw away
the laziness the whole design depends on.

## 5. Diagnostics: the honest verdict

The issue asked whether the name survives into diagnostics, on the grounds
that a `Refines(…)` which unfolds to its full spelling on first mismatch is
barely better than no name. The answer is **mixed, and the good half is the
half that matters**:

- **The name survives conversion.** δ is lazy, so a comparison that succeeds
  without unfolding never mentions the spelling. This is a property of
  `conv.rs`, not of this round, and it is why `Refines` is worth naming at all.
- **The name does not survive a type error**, because there is nothing for it
  to survive *into*: a kernel rejection is `TypeError::NotConvertible` with no
  types attached, rendered as "the kernel rejected `f`: NotConvertible" at the
  declaration's span. That is `issues/cli-check-diagnostics.md`'s standing
  complaint and predates this round entirely. Naming a statement shape makes
  it neither better nor worse.
- **One new bad message**, pinned as a test rather than fixed: a *partially
  applied* abbreviation (`P(n)` where `P` takes two parameters) is an ordinary
  value of type `Nat -> Type<0>`, which is not a universe, so the diagnostic is
  "this is not a type: only an expression whose type is a universe …" rather
  than an arity error. Correct and unhelpful. Fixing it means the type-position
  path checking for a partially-applied universe-valued function and saying so,
  which is a diagnostics change and not a typing one.

## 6. Cost

Naming `Refines` in `lib/ir_v1.hthr` and restating three theorems through it
**made the file faster**: 35.96s → 32.90s release (−8.5%), and 204 → 194 CPU-s
for the debug test binary. The δ-unfolding conversion now has to do is more
than paid for by elaborating the statement once instead of six times (three
theorems, one of them stating the shape three times).

So the `issues/schema-construction-caching` worry — that named abbreviations
buy readability with conversion time — is **not borne out at this scale**, and
the direction of the effect is the opposite of the one guessed. The mechanism
is worth remembering rather than the number: a δ-stuck head is *cheaper* to
compare than the shape it unfolds to, whenever the comparison succeeds by
pointer or by syntactic equality first.

## 7. Not in this round

- **Abbreviating an indexed family's formation** through the same road:
  `indexed.rs` has its own copy of the "is a constructor of" check
  (`indexed.rs:436`) and its own structural reader, neither of which was
  touched. Untested, so assume broken until someone tries it.
- **`type` as a keyword.** Route 1 is now redundant and the issue closes
  without it.
- **Level-polymorphic abbreviations.** `Refines` at `Type<0>` and `Type<1>`
  are two declarations, as non-cumulativity requires (surface-universe §6).
