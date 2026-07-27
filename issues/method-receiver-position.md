---
title: "Method calls put the receiver last, which inverts every two-premise lemma"
status: closed
labels: [frontend, syntax, elaboration, design]
created: 2026-07-27
updated: 2026-07-27
---

`x.f(a, b)` desugars to `f(a, b, x)` — the receiver is the **last** argument.
For a one-premise lemma that reads correctly; for a two-premise one it
inverts:

```heather
theorem trans<A>({a: A}, {b: A}, {c: A}, p: a = b, q: b = c): a = c

// given p: a = b and q: b = c, proving a = c —
q.trans(p)    ⇒  trans(p, q)    ✓   the receiver is the SECOND premise
p.trans(q)    ⇒  trans(q, p)    ✗   NotConvertible
```

So you write the *later* step as the receiver, which reads backwards against
every intuition `p.sym()` builds. Rust and Lean both put the subject first.

**The stated justification does not distinguish the two.** `parser.rs` said
the receiver is last "so with stage-2 implicit endpoints the earlier implicit
parameters are inferred from it (`p.sym()` ⇒ `sym(p)`,
`add_succ(n, k).sym()` ⇒ `sym(add_succ(n, k))`)". Both examples are **unary**,
where first and last are the same position — and the reason given is true of
receiver-first too, since implicit insertion is name-directed and does not
care about explicit-argument order. The convention was chosen on cases that
cannot tell the two apart, and the case that can was never written until
[[surface-records]]' regression suite wrote one.

## Why "just flip it" is not the whole answer

`cong` is a counterexample to *both* orders:

```heather
theorem cong(f: Nat -> Nat, {a}, {b}, p: a = b): f(a) = f(b)

p.cong(Succ)   receiver-last  ⇒ cong(Succ, p)   ✓
p.cong(Succ)   receiver-first ⇒ cong(p, Succ)   ✗
```

`trans` wants first, `cong` wants last. Neither position is right, because the
real property is **which parameter is the subject**, and that is a fact about
the *declaration*. Rust says it structurally (`self`); Lean gets it by
convention (subject first).

So a flip is really two things: the mechanism (receiver-first) **and** a
convention that lemmas are declared subject-first, with `cong`'s function
argument moving last.

## What the prototype measured (2026-07-27)

Flipped `resolve_dot` to `args.insert(0, recv)` and ran the suite.

**Mechanism: 5 small edits.** The desugaring itself, plus the argument
patterns of the four built-in special forms keyed on position (`map`, `fold`,
container-`cong`, `inj`).

**Real declarations: 1 test.** Only `constructor_values::cong_at_succ_by_name`
broke, and only because it declares `cong` function-first; re-declaring it
subject-first fixed it. `trans` needed **no change at all** — the prelude
already declares it `(p, q)`, so `p.trans(q)` ⇒ `trans(p, q)` reads forward
immediately. `sym`, `cong_succ` and `absurd` are unary and indifferent.

**Special forms: 8 tests, and this is the actual obstacle.** Every failure was
`inj`, and all for one reason: `inj` has a *documented direct-call spelling*
whose order was chosen to suit receiver-last.

```heather
inj(1, p)    // the direct spelling (tier-0 §6.3), index first
p.inj(1)     // the method spelling
```

Under receiver-last both arrive as `[k, arg]`. Under receiver-first the method
spelling arrives as `[arg, k]` while the direct spelling still means
`[k, arg]`, and they can no longer share one handler. `map`, `fold` and
container-`cong` have the same shape but no direct-call tests, so they merely
would have gone quietly wrong.

Three ways out, none free:

- **Flip the direct spellings too** — `inj(p, 1)`, `map(xs, f)`,
  `fold(xs, z, f)`. `map`/`fold` genuinely read *better* this way. `inj(p, 1)`
  reads worse than `inj(1, p)`, and it is documented syntax in a scheme
  document.
- **Make the special forms order-tolerant** (find the numeral). Hacky, and the
  hack would outlive the reason for it.
- **Wait for them to stop being special forms.** `inj`, `map` and `fold` are
  Rust that emits kernel terms, and [[generators-in-the-language]] says they
  belong in the meta layer. Once they are ordinary declarations they follow
  whatever convention ordinary declarations follow, and this dissolves.

## A hypothesis, tested and falsified

Worth recording so nobody re-derives it. I expected receiver-first to *also*
fix [[surface-operators]]' deferred `.cong(Wrap)` — the case
`docs/constructor-function-values.md` §5 leaves open — on the reasoning that
arguments elaborate left to right, so putting the informative receiver first
would let the constructor argument *check* against a known type instead of
*infer* against an unsolved meta.

**It does not.** Under the flip:

```heather
inductive Box { Wrap(v: Nat) }
theorem cong<A, B>({a: A}, {b: A}, p: a = b, f: A -> B): f(a) = f(b)
theorem method(n: Nat, m: Nat, p: n = m): Wrap(n) = Wrap(m) { p.cong(Wrap) }
// ERR: `Wrap` takes 1 argument(s), found 0     — both spellings, both orders
```

The proof `p` determines `A`, `a` and `b`. It says **nothing about `B`**,
which only `f` itself determines — so `f`'s expected type is `El A -> El B`
with `B` still a meta whichever order they are elaborated in, and
`build_ctor_value` cannot read a field layout off it. The blocker is
postponement ([[elab-unifier-completeness]]), exactly as
`constructor-function-values` logged it. Argument order is **orthogonal**.

## Decision (2026-07-27): a `self` marker, not a convention

The prototype framed this as *mechanism + convention*, and priced three ways
past the special forms. Both halves are superseded: the receiver's position
becomes a **declared property of the parameter**, written `self`.

```heather
theorem trans<A>({a: A}, {b: A}, {c: A}, self p: a = b, q: b = c): a = c
theorem cong<A, B>(f: A -> B, {a: A}, {b: A}, self p: a = b): f(a) = f(b)

p.trans(q)    ⇒  trans(p, q)     // subject first, the common case
p.cong(f)     ⇒  cong(f, p)      // subject last, because `cong` says so
```

This is the end state the "either way" paragraph below predicted, reached
directly rather than via a convention that would then be relaxed. It settles
`cong`, which was a counterexample to *both* fixed orders, without asking the
declaration to read backwards: `f` stays where it belongs and `p` is marked.

**Why a marker and not a `self`-*named* parameter.** Rust's `self` doubles as
the parameter's name, which suits a record method and suits nothing else — a
proof wants to be called `p`, and the statement it appears in already says
`p`. So `self` prefixes a normally-named parameter. `self: T` (no name after
it) is accepted as the shorthand that both marks and names, so a record
method can still be written the Rust way; it is one branch in the parser and
it keeps a bare parameter *named* `self` from being a silent non-method.

### Rules

- **Default is the first explicit parameter.** A declaration with no `self`
  behaves as it does under plain receiver-first. This is what makes the
  migration nearly free (the prototype's 1 broken test) and keeps one-premise
  lemmas — `sym`, `absurd`, `cong_succ` — free of ceremony. The cost is two
  spellings for the common case and therefore some drift; accepted, because
  requiring `self` would tax every unary lemma to discipline the rare one.
- **At most one `self` per declaration.**
- **`self` may not be implicit** (`{self p: T}` is rejected): an implicit
  parameter has no argument slot, so there would be nowhere for the receiver
  to land.
- **`self` may not be a `<A, B>` type parameter**, for the same reason — type
  arguments are never passed at a call site ([[at-and-type-arguments]]).
- The **direct call is unchanged**: `self` is call-site sugar only, so
  `trans(p, q)` and `cong(f, p)` still mean exactly what their declaration
  order says. There is one order per callee, not two.

### What it costs, and where it does not reach

- **Not in `Type::Pi`.** `implicit` is a flag on `syntax::ast::Param`
  (`ast.rs:151`) and `ParamMeta` (`lib.rs:182`); `self` is a second flag in
  the same two places. That is why this is cheap, and why it does **not** hit
  the wall [[implicit-binders-in-function-types]] is stuck behind — that
  issue needs its marker *inside* the kernel's function type, for by-value
  functions. `self` never does, because a function value cannot be
  method-called.
- **Traits cannot impose an order on it.** `resolve_dot` tries field
  projection before the method desugaring (`lib.rs:1607–1620`), so a
  record-of-functions member call `m.op(x)(y)` is a projection applied, not a
  method call. Trait members never consult `self`, so the "wrapper if the
  typeclass wants another order" escape hatch exists but should not be
  needed.
- **`self` is lexically free**: it occurs as no keyword today, and the
  recursion machinery's `SelfRef.name` (`lib.rs:2635`) is the *declaration's*
  own name, not the string `self`.

### The special forms need no table

Under default-subject-first, three of the four just become receiver-first and
read better for it (the issue's own assessment of `map`/`fold`):

| form | was | becomes |
| --- | --- | --- |
| `xs.map(f)` | `map(f, xs)` | `map(xs, f)` |
| `xs.fold(z, f)` | `fold(z, f, xs)` | `fold(xs, z, f)` |
| `xs.cong(self)` | `cong(self, xs)` | `cong(xs, self)` |
| `p.inj(k)` | `inj(k, p)` | `inj(p, k)` |

Only `inj` had a documented direct spelling (tier-0 §6.3) whose order encoded
receiver-last, and that is the entire obstacle the prototype measured. **It
is resolved by flipping the direct spelling**, not by an order-tolerant
handler and not by a Rust-side subject table. The earlier objection that
`inj(p, 1)` "reads worse than `inj(1, p)`" was formed under receiver-last;
once subject-first is the language's stated rule, `inj(1, p)` is the spelling
swimming against it, and one paragraph of tier-0 §6.3 is the whole cost.

So no exemption survives for the built-ins, and nothing has to be unwound
when [[generators-in-the-language]] turns them into declarations that write
`self` like anything else.

### Relation to [[named-arguments]]

That issue is the general form of "stop deciding this by position". `self`
does not compete with it: it names *one* argument — the one whose call-site
position is inverted by the `.` — and leaves the rest positional. If named
arguments land, `self` is the marker that says which parameter the `.`
fills, which is a question named arguments do not answer.

## Related

- [[named-arguments]] — the general form of "stop deciding this by position".
- [[generators-in-the-language]] — what removes the special-form obstacle.
- [[elab-unifier-completeness]] — the `.cong(Wrap)` blocker this is *not*.
- [[surface-records]] — where the inversion was first written down
  (docs/surface-records.md §11.3).

## Log

- 2026-07-27: Filed after prototyping the flip against the full suite. The
  prototype is not committed; its measurements are above. The headline is that
  the convention change is cheap for declarations (1 test, and `trans` needed
  nothing) and awkward only for the four built-in special forms keyed on
  argument position — and that the inference bonus I expected does not exist.
- 2026-07-27: Scheme written, superseding the mechanism+convention framing: the receiver's position becomes a declared property of the parameter (`self p: a = b`, a marker on a normally-named parameter), defaulting to the first explicit parameter when unwritten. Three consequences worth the reader's time. (a) It settles `cong`, which was a counterexample to BOTH fixed orders, without making the declaration read backwards -- `f` stays first and `p` is marked. (b) It costs one bool on Param/ParamMeta and does NOT reach Type::Pi, which is why it sidesteps the wall [[implicit-binders-in-function-types]] is stuck behind; and trait members never consult it, since a record-of-functions call is a field PROJECTION before the method path (lib.rs:1607-1620). (c) No Rust-side subject table survives: under default-subject-first, map/fold/container-cong simply become receiver-first and read better, and `inj` -- the whole measured obstacle -- is resolved by flipping its documented direct spelling to inj(p, k), since the 'inj(p,1) reads worse' objection was formed under the old convention. Code round next.
- 2026-07-27: LANDED (crates/elab/tests/method_receiver.rs, 12 tests, workspace 520). `self p: T` parses, `self: T` marks-and-names, and resolve_dot inserts the receiver at subject_index() -- the marked parameter's position among the EXPLICIT non-tyvar ones, or 0. Three things the round taught, none of them predicted by the scheme.

(1) The prototype's cost estimate held exactly, and the marker made the one broken declaration into the round's demonstration rather than a migration: constructor_values::cong_at_succ_by_name declares cong function-first, and adding `self` to `p` keeps BOTH its spellings (p.cong(Succ) and cong(Succ, p)) working with no other edit. That is the case the issue said no fixed order could serve.

(2) The obstacle dissolved as the scheme claimed, and the sweep for it was the useful part: flipping inj's direct spelling touched 9 call sites across three test files plus two docs, and nothing else -- map/fold/container-cong had no direct-call sites at all, which is exactly why the prototype found they 'would have gone quietly wrong'. They now read receiver-first in both spellings.

(3) One test I wrote to be thorough found nothing, and is worth keeping for the reason it found nothing: a marked subject in the MIDDLE (`fn pick(a, self b, c)`) works because insertion is an insert rather than a prepend-or-append, so there was never an end-biased version to get wrong. The counting test (implicits on both sides of the self) is the one that could have failed -- subject_index filters to explicit params, and cong alone would not have caught an off-by-one that happened to cancel.

Corrected while here: issues/surface-operators.md's landing note stated receiver-last with the inference justification, which was never load-bearing; docs/surface-records.md 4.1 and 11.3, and tier-0 6.3.
