# Printing a kernel type back as surface

Design doc for `issues/le-diagnostics-print-raw-el.md` (2026-08-17). The claim
being designed: a diagnostic that has to show a type should show it the way the
declaration that produced it was *written*, and the fact that the elaborator's
representation of that type is a lowering or a code should not be the reader's
problem.

## 1. What is missing, precisely

[[goal-display-decodes]] gave the display sites a **reader**: δ-step a
`Type::El` until a non-`El` head appears, at most `DISPLAY_DECODE_STEPS = 32`
steps, then print `{head:?}`. That covers every type whose wrapper is
*removable*. It does nothing for the two shapes the library now produces
constantly:

1. **An irreducibly wrapped code.** `Le` is a `fn … -> Type`, so at open
   arguments `El(Le(n)(m))` δ-unfolds to a stuck `ElimNat` and never loses its
   `El`. The reader spends its budget and falls back — correctly, for a type
   nothing can say anything about, wrongly for one whose code is a readable
   application of a named global.
2. **A type that was never `El`-headed at all.** `Id[0](Nat; app(app(u1^…)))`
   is the ordinary unfilled-goal statement of an equation between two calls.
   The reader declines it in its first line (`if !matches!(ty, Type::El {..})`)
   and the whole `Id` prints raw, annotations included — which is where the
   several-hundred-column messages come from, since every `App` node carries
   its domain and codomain.

Both are the same missing capability, and it is the *other direction* from the
reader: not "unfold until the wrapper is gone" but **spell the term back as the
surface that would elaborate to it**.

## 2. Shape: a per-node spelling with a per-node fallback

A new module, `crates/elab/src/display.rs`, holding one `Speller` that walks a
kernel `Type`/`Term` and emits surface text. Three properties, each chosen
against a way this could go wrong:

**Display-only, and it never reduces.** The speller performs no δ, no β and no
whnf. It reads the term it is given. (The one exception is `unspell_here`, which
is a registry lookup rather than a reduction — see §4.) This is stronger than
the reader's discipline, which at least spends steps; the speller cannot affect
elaboration at all because it never asks the kernel anything.

**Every node either spells or falls back to that node's `{:?}`.** There is no
"the whole type is unspellable" cliff: `Ap(λ …, v)` with an unspellable
argument prints the argument raw and the call in surface. A fallback is
`format!("{node:?}")` — already budget-bounded (`crates/kernel/src/fmt.rs`) —
truncated to `RAW_NODE_CHARS` with `…`, so a bad subterm cannot reintroduce the
several-hundred-column message on its own.

**Too many fallbacks abandons the attempt.** The speller counts fallbacks and,
above `SPELL_FALLBACKS`, the top-level call returns `None` and the caller prints
the plain bounded `Debug` of the whole type. This is the issue's "a code that
does not respell still falls back rather than guessing": a half-spelled monster
is worse than the honest raw form, because it *looks* like surface syntax while
being neither. Node and depth budgets (`SPELL_NODES`, `SPELL_DEPTH`) bound the
walk itself; exceeding either is a fallback like any other, so an adversarial
term degrades to the current behaviour rather than hanging.

The tolerance is a *parameter*, and one caller sets it to zero.
`spell_type_clean` admits no raw node at all, and it exists because there are
two different jobs here: **displaying** a type the reader asked about, where a
partly-raw rendering is still the best available answer, and **claiming**
something about two types, where a rendering the reader cannot check is worse
than no claim. `issues/check-fallback-discards-expected-type.md`'s mismatch
report is the second kind, so it speaks only when both types spell entirely.

## 3. Ordering: reader first, speller second

`display_type` becomes:

1. the existing `El` δ-reader, unchanged, producing a decoded head when it can;
2. the speller, on the decoded head if there was one and on the original type
   otherwise;
3. the plain bounded `Debug`, if the speller declined.

The reader keeps precedence deliberately. Where a head *exists*, it is the more
informative answer — `fn N(v: Nat) -> Type { Nat }` at `N(v)` should print
`Nat`, which is what the type *is*, not `N(v)`, which is one alias for it; that
is [[goal-display-decodes]]' pin and it stays. Where no head exists the reader
declines and the speller is strictly better than raw. Step 2 also now runs for
non-`El` types, which is what fixes the `Id` statement: the reader's first-line
decline no longer means "print raw".

One consequence worth stating rather than discovering: the over-budget case
changes what it prints. A 40-link chain of `fn T{i}(v) -> Type { T{i-1}(v) }`
used to print `El[…]` after exhausting the reader; it now prints `T40(v)`,
because the speller does not care that the reader gave up. The pinned
exhaustion test moves to asserting that, and the "falls back rather than
guessing" control moves to a term the speller genuinely refuses.

## 4. What spells, and how each name is recovered

Types:

| kernel | surface | how |
|---|---|---|
| `Nat` | `Nat` | literal |
| `Unit l` / `Empty l` | `True` / `False` | literal (`dress_true`'s job, done structurally) |
| `Ty l` | `Type<l>` | `show_level` |
| `Id(ty; a; b)` | `a = b` | the parser's spelling; `ty` is not printed, as it is not written |
| `SEq(ty; a; b)` | `a ≡ b` | **no surface form exists**; the glyph is display-only and deliberately not `=` |
| `Pi(dom). cod` | `A -> B`, or `(x: A) -> B` when `cod` uses the binder | dependence by `strengthen_ty` |
| `Vec(t; n)` | `[t; n]` | literal |
| `Fin(n)` | `Fin(n)` | literal |
| `Wf`/`Sum`/`Sigma` | `D` or `D<…>` | `inductive::tag_of` → the declaration's nominal tag → `Inductive::name` |
| `El(tm)` | spelling of `tm` | §2 |
| `GlobalTy` | the binding's name | §5 |

Terms: numerals via `nat_value` (`3`, not `S(S(S(0)))`); `Var` via the binder
name from `Γ`; an `App` spine as a call, with the head's *implicit* parameters
dropped so `len<A>(xs)`'s spine prints `len(xs)`; `Lam` as
`λ (x: A) => body`; `Refl` as `refl`; `Triv` as `trivial`; `Pair` as `(a, b)`;
and the type-code formers (`TmNat`, `TmId`, `TmPi`, …) by delegating to the
corresponding type spelling, since a code and the type it encodes are written
identically. Everything else falls back.

**Constructor values**, because a `match` arm's motive is instantiated at one
and so every goal statement inside an arm shows one. The injection path names
the constructor and the payload fields come out of the label's Σ spine and the
children tuple — the canonical half of `read_ctor`, re-derived here rather than
called, because that method takes a constructor spine, can elaborate
projections, and can fail, none of which a display path may do. An arm's motive
is instantiated at the *neutral* summand value, whose fields are projections
rather than the arm's binders, so `Nil` prints in full and `Cons(…)` admits its
fields the way a parameterized instance admits its arguments.

**A dependence check needs the context's base.** Whether a `Π`'s codomain uses
its binder is decided by `strengthen_ty`'s technique — drop the binder to a
marker, shift back, compare — which needs no traversal that could drift out of
sync with the syntax. The one trap, met while building this: under a context
variable the substitution's tail must be `Wk`, since a variable cannot address a
context-variable base, and an `Empty` tail there is a kernel invariant violation
that the kernel reports by *panicking*. A display path that panics is worse than
any message it could have printed.

**Recovering monomorphized type arguments.** A tier-0/1 lowering records no
argument list, but an argument is recoverable where a constructor payload
field's written type is exactly that parameter (`Cons(head: A, …)`). The
speller reads the matching lowered Σ field type, strengthens it out of the
nominal-tag and preceding-field binders, and does not trust that read: it
re-lowers the whole declaration at the candidates and accepts them only when
the resulting constructor shape is structurally identical. The diagnostic
cost is capped at declarations with at most 64 constructors-plus-fields.
Indexed families, value-parameterized declarations, oversized declarations,
and parameters with no exact field witness retain the honest `<…>` fallback.
Thus ordinary context entries now say `List<A>`, while `Phantom<A>` still says
`Phantom<…>` ([[display-inductive-type-arguments]]).

**That strengthening has to count the walk's own binders**, and for a year it
counted none: the recovery was handed the `Cx` the walk started from, so a
declaration printed *under* a `Π` was strengthened against a context short by
the binder, the binder's variable addressed nothing, and the kernel aborted the
process on the very invariant the paragraph above calls out — the display path
panicking, which this design says is worse than any message
([[pi-codomain-record-mismatch-panics-kernel]]). The count is **not** the
walk's `d`: `d` is the node/depth *budget* and is incremented on every descent,
binder or not. It is `names.len() − cx.names.len()`, since `names` gains one
entry per binder the walk descends under and `cx.names` is parallel to
`cx.gamma.entries`. The recovered arguments are strengthened past those binders
as well as the Σ spine's, which puts them back in `cx` — where the re-lowering
check already scopes them — and are shifted forward again before they are
handed to a walk that is still standing under them. An argument that genuinely
mentions one of those binders does not strengthen and keeps the honest `<…>`;
one that does not is now recovered where before it could only crash or fall
back.

## 5. Recovering a global's name

`GlobalBinding` carries no name (`crates/kernel/src/term.rs`); the elaborator's
`globals: HashMap<String, GlobalInfo>` does, keyed by qualified name with the
absolute Ψ index inside. A `Term::GlobalTm { var, .. }` in a term being
displayed is a de Bruijn index counted from the innermost end of the *padded* Ψ,
so the inversion is the one `gen_def_of` already performs:

```
abs = psi.bindings.len() + goal_base + meta_pushed.len() − 1 − var.0
```

and `global_name_at(abs)` is the existing reverse lookup. Two guards:

- A `GlobalTm` whose `LocalSubst` carries **terms** is not spelled. A top-level
  declaration has a nil context, so its substitution is `·^k` with no terms; a
  substituted global is something else and the speller declines rather than
  printing a name at arguments it is not applied to.
- A generated definition (`List#tycode`, `D#proj3`) is not in `globals` at all.
  `unspell_here` collapses a `#tycode` reference to the registry's inline copy
  before spelling, which is the right answer since the inline copy is then
  recognized by `tag_of`. Recursive constructor values and `Wf` types use the
  parallel exact lookup for `D#shape`; other generated definitions fall back.

### 5.1 Type names the program wrote

A `def` at a universe and a width family are expanded where they are read
(`docs/fixed-width-integers-design.md` §2), so the type a diagnostic holds is
`BitVec(8)` whichever of `u8`, `Byte` or `BitVec(8)` the program wrote. The
expansion is a pure function of the definition, so the name is recovered by
a table, not by unfolding anything (`Memos::type_names`,
`issues/type-name-display-respelling.md`):

- **Filled where the name is expanded** (`lower_type_value`,
  `try_type_value_app`), and read off the definition's *body*, once per name:
  `D#tycode_fn` applied to closed value arguments (`def Byte: Type =
  BitVec(8)`), `D#tycode`, or `λ n. D#tycode_fn(n)` for a declaration with
  one value parameter and no type parameters (`def u: Nat → Type = BitVec`,
  a family), each possibly through another `def` that is one (`def Word: Type
  = u(16)`). Any other body is not recorded and its expansion keeps the
  honest spelling: the display matches the instance it already recovers
  (§4) against the entry's tag and arguments, and never reduces to do it.
- **Read at an instance**, the inline lowering (§4, with its recovered value
  arguments) or its code `D#tycode_fn(ā)` (a type argument): an exact entry
  is its name; a family is `u16` at a numeral width and `u(e)` at any other.
  `u16` is spelled only where it would read back as the family (no `def
  u16` of its own).
- **The most recently written name wins.** Inside a declaration that is the
  one the declaration wrote, which is the spelling a reader of that
  declaration expects; `fn f(x: Byte, y: u8)` shows `u8` for both, since a
  type carries no record of which binder wrote what.
- **Only where the name still means it**: resolving to the same `def`, and
  not hidden by a local or alias in scope at the node. Otherwise the next
  name, or the declaration's own.
- **Reader flavours only.** The source flavours (`qualified`,
  `annotations`) keep the declaration's name, so a generated annotation is
  what it was.

Probes: `lib/_tests/std/bitvec/type_names_tests.hthr`.

### 5.2 Operators the program would have written

Elaboration resolves `a + b` to `Nat::add(a, b)` through the designation
table (docs/operators-onto-classes-design.md §4), so a diagnostic holds the
call and nothing of the symbol. The display reads it back the way §5.1 reads
a type name back, by a lookup and never by reducing
(`Speller::op_form`, issues/diagnostic-operator-resugaring.md):

- **The table read backwards at the carrier.** The call's head key and the
  carrier of its first explicit operand select every `(fixity, symbol)` whose
  designation at that carrier is this operation
  (`Traits::symbols_designating`). The carrier is the operand's type as the
  callee declares it, read off the binding's telescope — a type parameter
  there is the type argument the call passed — so `pick(a, b)` is `a ⊔ b`
  at a carrier that designates `pick` and `pick(x, y)` at one that does not.
  The global's name is never consulted.
- **Only an exact inverse.** Exactly one symbol of the call's arity
  (two infix operands, one prefix or postfix); no parameter the named call
  would write by name (a defaulted one has no place in the notation); the
  call fully applied. A partial application,
  an over-application, two symbols for one operation, or an undesignated
  operation keeps the named call.
- **Rung 1 wins.** Inside `<A: Monoid(+)>` a written `+` is the constraint
  binder's operation at every carrier, so a `+` designation cannot spell
  anything there; the binder's own applications, `#op+@0_1(x, x)`, spell as
  `x + x` while that binder is the innermost for its symbol.
- **Parenthesized by the parser's table.** `heather_syntax::operator_form`
  exports the grammar's levels (`Parser::infix_op`'s binding powers, the
  comparison level, `^`, prefix and postfix), and an operand is wrapped
  exactly where the parser would read the unwrapped text differently: an
  infix left operand whose right power is not above the parent's left power,
  an infix right operand whose left power is below the parent's right power,
  a comparison inside another, anything but a postfix form under `^`'s base
  or a receiver. `a - (b - c)`, `(xs ++ ys) ++ zs`, `-(a + b)`, `(-x) ^ k`.
- **Reader flavours only**, as in §5.1: a source flavour's output is
  re-parsed and decided on (omega's atoms, generated annotations), so it
  keeps the named call. Nothing elaboration keys on reads this spelling.

Probes: `lib/_tests/std/num/operator_display_tests.hthr`.

## 6. Testing

The axes of `docs/testing-generated-terms.md` apply, and two of them are the
whole point here: an **open** argument (a closed `Le(3, 10)` reduces to `True`
and never reaches this code) and a **negative control** (a term the speller
refuses). Concretely:

- the `trivial` mismatch at `Le(n)(m)`, open `n`, `m`: pins `Le(n, m)`;
- the unfilled-goal statement of an equation between calls over a parameterized
  inductive: pins `len(append(xs, ys)) = add(len(xs), len(ys))` and pins the
  context entries as `List<A>` rather than the `Wf(Σ…)` lowering;
- a mismatch between two `And` instantiations states both complete types, while
  a phantom parameter retains `<…>` rather than being guessed;
- a recursive `Tree` congruence failure states its complete constructor-valued
  goal after resolving the generated `Tree#shape` annotation;
- the reader still wins where it can: `N(v)` prints `Nat` (existing pin, kept);
- a term the speller refuses falls back to `El[`/the raw form, as a direct unit
  test on a hand-built `Type` — the surface language makes it hard to *write* an
  unspellable type, which is itself evidence the coverage is not thin;
- the fallback cap: a type with more unspellable nodes than `SPELL_FALLBACKS`
  prints raw rather than half-spelled.

Diagnostics tests pin the rendered text, not merely that an error occurred.
