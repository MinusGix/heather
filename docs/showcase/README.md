# The showcase pair: one program, written twice

Two spellings of the same program — a shell calculator whose compiler to an
RPN stack machine is *proved correct*, the project's thesis in miniature:

- **`idealized.hthr`** — the language we want. It does not check, and its job
  is to be argued with: a concrete surface for design critique, ahead of the
  issues (which lag the head — several constructs here have no owner yet).
- **`calc.hthr`** — the same program at the limit of what checks today
  (2026-08-13). Verify with:

  ```
  (ulimit -v 8388608 -t 120; \
   target/release/heather check -L lib/std docs/showcase/calc.hthr)
  ```

The method: every diff between the two files is either a **gap** (a feature
that doesn't exist, mapped below to its owner) or a **friction** (it exists
but cost too much argument). When a line of the idealized file starts
checking, a brick landed; re-derive the realized file toward it and shrink
the table. The idealized file is *not* a commitment — it is the current best
guess, revised freely as taste and design rounds move.

## What already matches

Worth saying first, because half the idealized file **is** the realized file:
inductives with fields and shared annotations, structural `match` recursion
with self-call IHs, nested patterns and `_` default arms, `+`/`*`/`++` via
designations (all three from `std/algebra` since 2026-08-13 — `*` at `Nat` was
the showcase's own line until then), `calc` equational chains, the empty proof block `{}`, implicit `{a, b}` theorem
binders, receiver members (`e.eval()` and `args.nth(1)` — `fn Expr::eval(self e: Expr)` checks today), honest
`Option` failure in the machine, and the whole *shape* of the correctness
statement. The demo theorem computes `2 + 3 * 4 = 14` by kernel reduction.

## The gap table

| Idealized construct | What's missing | Owner |
| --- | --- | --- |
| `theorem compile_pushes_eval(e, rest, s)` with plain parameters | varying arguments force the returned-function statement + over-applied IHs | `issues/ih-generalization.md` |
| `fn run(toks, s)` uncurried | same mechanism at `fn` level — the stack varies, so `run` curries it | `issues/ih-generalization.md` |
| calc steps that reassociate `++` silently | monoid laws as an ambient simp set the chain applies where they obviously fire | `issues/grind-port.md`, `issues/lemma-selection-and-search.md` |
| `:= compile_pushes_eval(l)` (endpoints fill the arguments) | unification-driven instantiation of a calc-step justification | `issues/elab-unifier-completeness.md` (nearest) |
| no `cong_run` anywhere | congruence inferred from the goal's shape | `issues/congruence-by-anti-unification.md` |
| `heather disprove '…'` at the shell | counterexample search before anyone pays for a proof | `issues/heather-disprove.md` |
| `n :: s` cons notation | finite construction is now `[TPush(n)]`; infix open-tail cons remains absent | `issues/notation-extensibility.md` |
| `Result`, `?`-chaining, `.map` | prelude types and their chaining kit | `issues/prelude-option-and-friends.md` |
| `let b :: a :: s2 = s else { … }` | let-else (the one-non-absurd-branch match) | `issues/let-else-sugar.md` |
| `String`, `.chars()`, `[c, ..rest]`, `if c.is_digit()` guards | strings, slice patterns, match guards | no owner yet |
| `decreases ts.len()` on mutually recursive parsers | non-structural termination measures; mutual recursion; callee consumption postconditions | `issues/termination-measures.md` |
| `"{src} = {eval(e)}"` | string interpolation | no owner yet |
| `datarepr Nat = repr::BigNat` | runtime representation chosen per type, linked by certified refinement | `issues/datarepr-separation.md` |
| `derive instance Compile[Cpu] for eval` | **half landed 2026-08-14**: tier-1 source types are in the generator's fragment (`docs/certgen-tier1-source-types-design.md` — an `eval`-shaped recursion over an `Expr`-shaped type generates a kernel-checked `Compile` instance end to end). Still missing here: the `derive` surface and the `Compile` class (their own row), and `run` — blocked by four independent certgen declines even after hand-monomorphization (probed 2026-08-15: tier-1 constructor fields at a *third* inductive — the binding one; recursive tier-1 results; non-`Nat`-field results like `Option<List<Nat>>`; the curried result), not only the parameterized-instantiation name gap | `issues/compile-typeclass-design.md`; `run`: `issues/datarepr-separation.md` |
| `Compile[Cpu]` as a class | the Compile typeclass and certificate coupling | `issues/compile-typeclass-design.md` |
| `runtime_fn main`, `IO`, `println` | the effects story and the kerneltime/runtime rim | `issues/effects-direction.md` |

## Frictions found while writing the realized file

Recorded here because "it checks" hides them:

1. **A parameter named `code` cannot be matched on.** `match code {` parses
   as the quotation form `code { … }` and dies with ``expected `}` to close
   the quote`` — a baffling message for an ordinary variable name. The
   realized file renamed the parameter to `toks`. Filed:
   `issues/match-scrutinee-named-code.md`. **Resolved 2026-08-16**: the
   quotation now stands down wherever the `{` belongs to the enclosing form
   rather than to the payload — the condition `no_record_lit` already marked
   for record literals — and `match code as λ z => T { … }` was found to be
   the same gap one form up. `match code { … }` and `match code as …` are
   ordinary matches on an ordinary variable; a quotation that really is the
   scrutinee is parenthesised, as a record literal there already was.
2. **`++` is left-associative; `append`-based proofs are right-nested.**
   Swapping `append(a, append(b, c))` for `a ++ b ++ c` silently changed the
   term under an already-green proof to `(a ++ b) ++ c` and broke it — fixed
   by writing `a ++ (b ++ c)`. Nothing wrong, but nothing *said* anything
   either. **Resolved 2026-08-13**: `++` is right-associative now (the fixity
   table in `parser.rs` says why), and this file dropped the parens. The
   durable lesson stands: fixity is proof-relevant, so notation declarations
   should carry associativity visibly.
3. **The congruence tax.** One `cong_run` lemma is cheap, but it is the same
   `j(p, λ y q => …, refl)` shape every file writes per position
   (`list_algos` has five). This showcase's whole proof burden beyond the
   induction itself is congruence plumbing plus `append_assoc` shuffling —
   both rows in the table above.
4. **`calc` is already a big win.** The first draft used `trans` chains; the
   calc rewrite is the difference between a proof you re-derive and a proof
   you *read*. It landed with `surface-operators` and deserves to be the
   default idiom.

## Bookkeeping

The realized file is checked by hand (command above), not by the test suite —
so it can rot silently if the surface moves. If it earns keeping, wire it
into a test; until then, re-check it when showing it to anyone.

**`mul` moved to `std/nat` on 2026-08-13** (`issues/std-nat-multiplication.md`),
with the lemma kit and the `CommMonoid<Nat>(mul)` instance the library wanted
anyway; `calc.hthr` dropped its own `mul` and its `*` row and takes both from
`std/algebra`. The deferral paragraph that stood here was **wrong about the
mechanism**, and the correction is the better datapoint: a module-local `fn`
*shadows* an imported one rather than colliding with it, so the byte-pinned
`fn mul` fixture in `crates/elab/tests/certgen.rs` would have gone on working,
silently meaning something other than what it read as. That is the module-scope
argument this paragraph was reaching for — fixture programs and the library
share one namespace, and the sharing resolves without a word. The fixture was
renamed `viaadd` for exactly that reason; the pins moved by name only.

## Finite-set client exploration

[`finite-sets-idealized.hthr`](finite-sets-idealized.hthr) is a separate
client-first design sketch for relational abstraction, ahead of an implementation.
It deliberately does not check and has no realized counterpart yet.
[Its design analysis](../finite-set-client-design.md) works backward from the
client to certificates, dependent membership transport, and proof opportunities.

For a smaller introduction and syntax critique, see
[three small transfer experiences](../three-small-transfer-experiences.md):
one set function, one positive-natural function, and one rejected/repaired
cardinality implementation. These are proposed examples, not checked programs.

## Writing your own thing with laws

[Mergeable summaries](your-own-thing-with-laws.md) walks through defining a
relation-indexed class, supplying two implementations, proving a reusable
repeated-delivery law, and reporting unfinished proof fields. The snippets are
illustrative and unverified. Exact obligation display is the baseline;
bounded counterexample search is an optional improvement.

## Realized Mergeable foundation

[`mergeable.hthr`](mergeable.hthr) is the checked manual counterpart to
[the user-authored law interface](your-own-thing-with-laws.md). Its library
closure and every showcase declaration run in `lib_setoid_mergeable`:

```console
furnace run -- scripts/test -p heather-elab --test lib_setoid_mergeable
```

[The implementation record](../manual-mergeable-round.md) contains the gap table,
explicit compatibility proof, and acceptance boundaries. The broader idealized
finite-set and subtype examples are still design sketches.

## Composed relational contexts

[`relational-contexts.hthr`](relational-contexts.hthr) constructs a certificate
for `known ++ (incoming ++ incoming)`, applies a local law beneath that whole
context, and states the extra evidence required by a surrounding observer.
It runs in `lib_setoid_mergeable`; [the round notes](../relational-context-round.md)
explain the proof rules and remaining automation work.

## Bounded certificate-generation prototype

[`relational_generator_input.hthr`](relational_generator_input.hthr) is ordinary
client source for `scripts/relational-context-demo`. The driver can emit a checked
preservation definition, expose a missing observer contract, resume with supplied
evidence, or leave raw length unproved. [The generator round](../relational-generator-round.md)
documents the explicit request API and its source-level prototype boundary.

[`relational_generator_generated.hthr`](relational_generator_generated.hthr)
is the saved success output, including the generated `receive_generated`
certificate. It can be checked directly as an ordinary Heather module.

## One contextual rewrite

[`contextual_rewrite_input.hthr`](contextual_rewrite_input.hthr) contains a theorem
with a single goal hole. The source driver selects its proof parameter, recovers
the shared context, and fills the hole with a checked certificate application.
It is input to `scripts/relational-context-demo rewrite`, not a completed module
until the driver fills that hole. [The round notes](../contextual-rewrite-round.md)
cover partial occurrences, missing observer evidence, and the bounded fragment.

The [saved generated theorem](contextual_rewrite_generated.hthr) contains the
ordinary proof emitted by the driver and is independently checked.
