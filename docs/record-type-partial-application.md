# A record type, partially applied

Status: **landed**, 2026-09-19. Tracking issue:
`issues/record-type-partial-application.md`. Two siblings, each holding one
half of this round's disambiguator: `docs/constructor-function-values.md`
(η-expand the *constructor* against an expected `Π`) and
`docs/record-type-values.md` (read the *type former* against an expected
universe). This round is their intersection, and it is deliberately small
because both halves already exist.

---

## 1. What was missing

A record's type could be written at a universe, and a constructor could be
η-expanded at a `Π`. Neither of those is what a client wants when it needs
"this record, as a relation":

```heather
record Grammar(level: Nat, value: Nat) { at_level: level = level }
fn takes_relation(rel: Nat -> Nat -> Type) -> Type { rel(0, 1) }

fn direct() -> Type { takes_relation(Grammar) }
// was: "`Grammar` is a constructor of `Grammar`, which is not the expected type here"
```

The expected type is a `Π` and the name reaches the constructor arms, which
read it as `Grammar`'s *constructor* and try to absorb its **fields** — so the
diagnostic names the constructor even though nothing about a constructor could
inhabit a spine that ends in `Type`.

The workaround is a `fn` that applies the record and does nothing else. Both
calculator showcases carry three of them, and `docs/showcase/calc_text.hthr`'s
is the shape that makes the case:

```heather
fn GrammarSpec(level: Nat, source: List<Char>, begin, end: Cursor<Char>(source),
    value: Expr) -> Type {
    Grammar(level, source, begin, end, value)
}
```

`GrammarSpec(level)` is then passed to `parser_contracts::Certified`, whose
`relation` slot is `(source: List<T>) -> Cursor<T>(source) -> Cursor<T>(source)
-> A -> Type`. A reader asks what the wrapper adds over the record and the
answer is nothing.

---

## 2. The scheme: one η-expansion, pointed at the type reading

```
D<ā>(v₁ … v_j)  ⇐  Π(x_{j+1} : A_{j+1}). … Π(x_m : A_m). Ty l
    ⇝  λ x_{j+1} … λ x_m. ⌜D<ā>(v₁ … v_j, x_{j+1} … x_m)⌝
```

`check_type_former_value` in `crates/elab/src/inductive.rs`, sitting in
`elab_check_skel_slots` immediately after the universe arm and before the
constructor arms. It is `build_ctor_value`'s loop with three differences, and
each one is the point:

- **The binders come off the expected spine, one at a time, under the ones
  before them.** A *dependent* domain is the showcase's actual shape
  (`Cursor<T>(source)` mentions the binder above it), so the walk pushes each
  peeled binder into the context before it reads the next domain. Reading the
  whole telescope in the ambient context would not see `Cursor<T>(source)` at
  all.
- **The saturated spelling is lowered by `try_valparam_ty`**, not by a new
  copy of the instance lowering. The synthetic arguments are *surface*
  variables under unspellable `#ta`-names, so `D(v̄, x̄)` is lowered exactly as
  the same text written in type position is — which is `docs/record-type-values.md`
  §2's lesson applied verbatim, and why monomorphized type parameters
  (`Boxed<A>(v)` with `A` open) come along for free.
- **The result is quoted, not returned as a type.** The body is a *term* at
  `Ty l`, so it goes through `ExprElab::quote_type_at` — the same level check
  and the same emission respelling the universe arm uses, rather than a second
  spelling of either.

### 2.1 The disambiguator, one arrow further in

`docs/record-type-values.md` §2.1 settled the two-reading question with **no
constructor inhabits a universe**. The same sentence settles this one, because
no record type is a `Π`: a constructor's η-expansion ends at `D(v̄)`, a Σ tower,
so an expected Π-spine whose *ultimate* codomain is `Ty l` can only want the
type former.

That is why the arm walks to the end of the spine before it commits to
anything, and why committing there is safe: it is the only place where no
constructor reading exists to steal. Everywhere else the arm returns `None` —
not an error — and the constructor arms below keep every reading they have
today, including the one they own outright (`Two(1)` at `Nat -> Two(n, m)` is
field `a` written and field `b` abstracted).

### 2.2 What the commitment buys

An arity diagnostic pointed at the right telescope. Once the spine is known to
end in a universe, a mismatch between the arrows it offers and the value
parameters left over is *this* round's error rather than a constructor's
field count:

| Written | Message |
|---|---|
| `Grammar` where `Nat -> Type` is expected | "`Grammar` needs 2 more value argument(s) to be a type, but the expected function type provides 1 before its `Type`" |
| `Grammar(0)` where `Nat -> Nat -> Nat -> Type` is expected | the same sentence, "needs 1 … provides 3" |
| `Grammar(0)` where `Nat -> Type<1>` is expected | the non-cumulativity message, unchanged — `quote_type_at`'s |
| `Grammar(0)` in inference position (`let r = Grammar(0);`) | unchanged; no expected type has selected a reading (`docs/constructor-function-values.md` §3) |
| a peeled domain that disagrees with the value parameter it fills | `valparam_args`' own check of that argument |

The last row is worth stating because it is where this arm deliberately does
**not** grow a check of its own: the synthetic variable is checked against the
declared value parameter's type by the machinery that checks every written
argument, so a `Bool` domain filling a `Nat` parameter is rejected there and
not by a conversion test bolted onto the η loop.

---

## 3. Cost

`check_type_former_value` (one function, one loop), the arm that calls it, and
`quote_type_at` made `pub(crate)`. No kernel change, no parser change, no new
AST node, and no change to `try_valparam_ty` or `build_ctor_value`.

The arm's guard runs on the checking path of every application that fell
through the special forms, so it is ordered for a fast miss: the name table
lookup (a hash) comes first and the shadowing test (a walk of the context)
only after the value-parameter arithmetic has already said the shape could
match.

---

## 4. Acceptance

`crates/elab/tests/record_type_partial_application.rs`, eight tests. Following
`docs/testing-generated-terms.md`, every positive test *inhabits* the type it
built rather than only elaborating it — a term that merely sits at `Type`
proves nothing about being the right type — and the wrapper spelling is kept
beside the record spelling so the two are shown to agree rather than only to
both check.

1. **The repro**, with the wrapper beside it: `takes_relation(Grammar)` and
   `takes_relation(GrammarSpec)` are each inhabited, and each inhabitant is
   accepted at the *other*'s type.
2. **A written prefix**, at a **literal** (`Grammar(0)`) and at a **neutral**
   (`Grammar(level)`), with the neutral one instantiated at the literal.
3. **The showcase shape**: a three-binder relation whose second domain
   `Slot(n)` depends on the first binder, with the wrapper beside it again.
4. **A record's own relation slot**, which is where the showcase actually
   writes it (`Certified(Grammar(level))` — the checking position is
   `valparam_args`, not a `fn` parameter), with the relation-typed field
   projected back out.
5. **An open element type**: `Boxed<A>(v)` with `A` the enclosing
   declaration's parameter, alongside a closed instantiation that computes.
6. **The negative control**: the constructor reading of the same record in the
   same file — `Two(1)` at `Nat -> Two(n, m)` is still field `a` written and
   field `b` η-expanded, and both its fields are read back.
7. **The diagnostics**, every row of §2.2's table.
8. **Shadowing**: a `Nat -> Nat -> Type` *parameter* named `Grammar` is passed
   along, not lowered, and the witness (`refl`) distinguishes the readings.

---

## 5. What this does *not* do

**The showcases still carry their wrappers.** The feature makes them
removable, and `issues/record-type-partial-application.md`'s log already
argued that the showcase half should land as its own piece of work; this round
adds a reason that is specific and measurable. `GrammarSpec(level)` needs no η-expansion at
all: a global's term is a reference, so the partial application is a **δ-stuck
neutral spine** whose head conversion compares before it unfolds. What this
round produces instead is a **λ over the inlined record lowering**, and two of
those compare structurally, Σ tower and all. That is the trade `docs/record-type-values.md` §5 noted from the other
side ("the δ-stuck `RefinesNat2` head compares before it unfolds"), and
`docs/showcase/calc_text.hthr` is the file whose semantic image is 483 M nodes
and whose cold check needs more than 8 GiB
(`issues/elaborator-canonical-type-spelling.md`). Removing three wrappers there
is a measurement, not an edit, and it belongs with the round that turns
`RunSpec` and `OpRun` into records.

**Nothing abstracts a type parameter.** `Monoid` as a `Type -> Type` value is
still not expressible, by `docs/record-type-values.md` §2.2's fence: parameters
are monomorphized, so `Monoid<Nat>` and `Monoid<Bool>` are unrelated kernel
types. `Boxed<A>(v)` with `A` open is the case that works, and it works here
for the same reason it works there.

**Nothing changes in inference position.** `let r = Grammar(0);` still has no
expected type to select a reading, which is `docs/constructor-function-values.md`
§3's boundary, unmoved.
