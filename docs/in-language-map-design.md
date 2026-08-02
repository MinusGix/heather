# The first in-language derived artifact: `map_code`

Design sketch for `issues/in-language-map.md` — the opening move of
`issues/generators-in-the-language.md`'s migration, scoped by the
2026-08-02 expressiveness verdict logged there. Round pattern as usual:
this document first, the implementing round against §7's acceptance list.

## 1. What this round proves

Today every derived artifact is Rust that emits kernel terms. The thesis
says generators belong *in the language*, as layer-m functions over code.
This round runs the whole pipeline once, at minimum size:

    surface `meta fn` → layer-m kernel term → evaluated on code arguments
    mid-elaboration → emitted code spliced into a declaration → kernel check

The client is `vec::map` — per the verdict the one generator family that
consults nothing: no whnf/conversion oracle, no declaration table, no code
equality, no code analysis at all. Pure template-with-splices, i.e. pure
quotation, needing none of the verdict's four blockers.

The payoff is discovering *cheaply* whether the letbox discipline or the
abstract-context indexing is miserable at the surface, before the analysis
story (match-on-code, 37 branches) commits to it. Secondary payoff, the
thesis' selling point at minimum size: the modal substitution calculus does
the de Bruijn arithmetic that `crates/elab/src/vec.rs` does by hand —
`map` there has fourteen `shift_local` sites, each a comment naming its
binder context; `map_code` has none, because a letbox-bound global `u`
weakens through local binders by the calculus, not by the author.

### 1.1 Why code, and not just a function?

The naive question deserves a written answer: `map` looks like an ordinary
generic function, so why does the in-language version *generate code* instead
of simply being `fn map<A, B>(…)` in a prelude?

Two layers to the answer, one about the family and one about `map` itself.

**The family cannot be functions.** What this migration moves is Rust whose
job is to *write kernel terms*, and its real clients — the recursors,
no-confusion lemmas, and tier lowerings of
`issues/generators-in-the-language.md` — are one generated definition **per
declaration**, produced from the declaration's shape. "The recursor of every
inductive you will ever declare" is not a value to define once and call; it
is a program that writes a different program for each input. That is a
function from syntax to syntax, and `Code` is the type of syntax. `map` is
the deliberately minimal exercise of that machinery (§1), not its
justification.

**`map` itself could be a function — and splicing is still right, today.**
Three reasons, in force order:

1. **The emitted program is self-contained.** The hook splices the
   eliminator, so a use site contains the same computing term the Rust
   schema emits, and a `refl` proof over a literal length computes on the
   spot. A prelude *call* instead makes every such proof depend on unfolding
   a bodied global during conversion — and bodied globals are exactly the
   metatheory still owed (`issues/metatheory-ch07-definitions`: glueing at
   p, neutral at c). Splicing does not depend on an unfinished story.
2. **The oracle cross-check needs like against like.** The adequacy net for
   a template is "its output is convertible with the Rust schema's output."
   That comparison exists because both paths emit the same kind of artifact;
   a function call and an inlined eliminator are not comparable that way.
3. **The trust seam stays visible.** `Code(g |- T)` types the generator
   without trusting it: the kernel re-checks every spliced term
   (untrusted-generator property). A direct implementation blurs the seam
   the certifying architecture is built around; code-as-data keeps it.

Reason 1 is a *contingency*, not a principle: if the ch. 07 bodied-globals
round lands and prog-layer conversion unfolds definitions, the closed-generic
templates (`map_code`, `fold_code`, and the vec family generally) lose their
reason to be templates, and their natural end state is mundane prelude
functions — with `.map` elaborating to an application, the vec slots
retiring, and the quotation machinery keeping only the clients that cannot
be functions. That is a smaller trusted surface, not a loss; the thesis was
always demonstrated by deletion, and it would end by deleting the templates
too.

## 2. Where the pieces stand (surveyed 2026-08-02)

- **Kernel: complete and unreachable.** Every modal former exists through
  typing, both reduction engines, and conversion — `CtxPi`/`CtxLam`/`CtxApp`
  (typing.rs:600/694/1558), `TyPi`/`TyLam`/`TyApp` (:607/705/1592),
  `CodeTy`/`CodeTm` (:620/:626), `BoxTy`/`BoxTm` checking-only (:644/:653,
  `NotInferable` at :1609), `LetBox*` (:1611/:1637), the code recursors.
  Letbox-on-box β fires in both engines (eval.rs:1220ff, reduce.rs:673ff).
  No elaborator path emits any of them today.
- **Ψ cannot hold a layer-m body.** `GlobalBinding::Tm` admits layers v/c
  only and a body only at `Layer::Code` (typing.rs:149,162), which is
  ch. 04 verbatim ("there is no way to introduce a term at layer p to
  global context" — a fortiori m). This settles §4's central decision.
- **Surface: greenfield, but designed.** The quotation slice is specified
  in docs/sketches/surface-v0.md §§4–6 with verdicts already taken:
  `code { … }` quote blocks, `$ident` auto-hoisting splices (verdict (c)),
  `${expr}` for compounds, `let code`, `Code(Δ |- T)` as an ordinary
  wrapper type. `match code` is designed there too and **stays out** of
  this round.
- **The Rust artifact to mirror:** `vec::map` (vec.rs:54–142) is an
  `elim_Nat` on the length with the forced Π-over-the-vector motive,
  applied to the vector. Its surface spelling exists: explicit-motive
  `match … as λ z => T` accepts a function-type motive body (lib.rs:288),
  so the payload needs no new elimination form.
- **Call site:** `elab_vec_map` (lib.rs:2332) already holds exactly the
  four ingredients the boxed signature wants — `al`/`A` and `len` from the
  receiver's Vec type, `bl`/`B` via `vec::strengthen` on the function's
  codomain — and returns an ordinary inferred term.

## 3. The artifact — **as landed, after two corrections**

The section as first sketched gave `map_code` the issue's signature —
`TyCode` binders `a`/`b`, code arguments `f` and `k`, a result type
`Code(g |- Vec($a; $k) -> Vec($b; $k))`. The implementing round refuted
that shape twice, and both refutations are calculus facts worth keeping
(they are exactly the "discover cheaply" payoff §1 promised):

1. **There are no meta-functions over terms.** The kernel (and ch. 04) has
   `CtxPi`/`TyPi`/`UPi` only. A code *argument* is therefore an ordinary
   Π-bound local — and a local's payload can never be mentioned by a later
   *type*. `Code(g |- Vec($a; $k))` with `k` an argument is unstatable:
   nothing but a global can index a code type. Consequence: the length
   moves inside the quote.
2. **A layer-p type can never appear inside layer-c code.** `TyPi` binds
   `U : Typ_p`, and the binding invariant `i' ≤ i` (typing.rs's
   `GlobalTy`/`GlobalTm` rules, ll. 593/754) refuses a p-binding at a
   c-judgment — including every `Lam`/`App` type *annotation* inside a
   payload, which is where an element type inevitably lands. So `TyCode`
   binders index signatures and nothing else, which makes them useless to
   pure quotation; they leave the slice (the syntax stays reserved — their
   real consumer is the analysis story's code recursors, which take
   `CodeTy` *locals* and letbox them). Consequence: genericity lives
   *inside* the code, as code-level Π over the universe — ordinary MLTT.

What lands (`lib/vec_code.hthr`):

```heather
meta fn map_code(g: Ctx) -> Code(g |-
    (A: Type<0>) -> (B: Type<0>) -> (A -> B) -> (k: Nat) -> [A; k] -> [B; k]
) {
    code {
        fun (A: Type<0>) => fun (B: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [B; z] {
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }
    }
}
```

— a **closed generic template**: kernel image `CtxLam g. box ⟨payload⟩`,
the hook applies the spliced payload to `⌜A⌝`, `⌜B⌝`, `f`, `len`, `xs` as
ordinary applications. Notes:

- The elim is the same Π-over-the-vector one vec.rs builds by hand; the
  explicit-motive `match … as λ z => [A; z] -> [B; z]` spells it (a motive
  body may be a function type). Where vec.rs has fourteen `shift_local`s,
  the payload has none.
- The template's level is 1, not 0 — it quantifies over `Type<0>`. "Level
  0 slice" means no level *variables*; a code type's level is whatever its
  payload type computes.
- **Term splices survive** as designed — `Code(g |- T)` locals at
  *monomorphic* indices, each `$x` hoisting one `LetBoxTm` above the quote
  with a constant motive, the payload referencing `u_x` under a `wk`
  substitution the kernel weakens through binders. `map_code` itself needs
  none (its parametricity is total — see the §7 note), so the quotation
  suite proves them separately (`wrap_succ`, `apply_code`, `const_fn`).
- Payload spellings this round added, generally useful: `head`/`tail`/
  `cons` on vectors whose length reduces to a successor (the `Σ`'s
  projections and pair, annotated from the element type), and
  universe-typed binders registering as type names in **lambdas and
  written function types**, not just declaration telescopes — the
  generalization docs/surface-universe.md §2 already implied.
- In a `meta fn` signature, `Ctx` binders precede `Code` parameters
  (global binders cannot sit under local ones). Enforced with a
  diagnostic, not reordered silently.

## 4. The evaluation hook

**Decision: meta definitions are elaborator-held, not Ψ-resident.** The
issue's "Ψ-resident layer-m function" cannot be literal: ch. 04 excludes
meta-layer terms from Ψ and our kernel enforces it (§2). Extending Ψ with
Meta-bodied globals would be a deliberate book deviation with its own
ch. 07 obligations (`issues/metatheory-ch07-definitions.md`'s grade) — a
real kernel round, not this one. And `issues/box-synthesis-gap.md`'s
closed decision already names the alternative: *all meta-level computation
is static; the elaborator normalizes the meta layer at emission time.* So:

- A `meta fn` elaborates to a closed layer-m term, is **kernel-checked at
  `Layer::Meta` against Ψ** (statement via `check_type`, body via
  `check_term` — same gate as ordinary declarations, different layer), and
  is registered in an elaborator-side table (`meta_defs`), *not* pushed to
  Ψ. Layer honesty falls out: nothing at layer c can reference it, because
  Ψ never hears of it.
- At a use site, the hook builds the application — for the closed template
  in ambient context Γ with the ingredients of `elab_vec_map`:

      CtxApp(map_code, Γ)   ⇝*   box ⟨payload⟩
      then  payload ⌜A⌝ ⌜B⌝ f_t len xs_t   (ordinary `App`s)

  `CtxApp` wants a concrete context and Γ is one; `⌜A⌝`/`⌜B⌝` are the
  Tarski codes the elaborator already produces (`code::code_of`), and the
  `App` annotations come from kernel-inferring the evaluated payload once
  and peeling its Π spine. An element type with no Tarski code, or at a
  level the template does not take, is an **honest decline** — the Rust
  path serves it.
- **Evaluation is iterated δ-transparent WHNF** (`whnf_term_delta`, the
  elaborator's existing oracle, elaborator fuel), driven until the head is
  `BoxTm`. No deep normalization is needed: every β/letbox step happens at
  the meta layer at the *head*, and the final box payload is a layer-c
  term assembled by the modal substitution calculus — there are no meta
  redexes inside it to normalize. Anything other than a `BoxTm` head
  within fuel is a loud diagnostic naming the stuck head (the
  fail-loudly caution from generators-in-the-language, 2026-07-27).
- The spliced payload is applied to `xs_t` and returned as the inferred
  term, exactly where `vec::map`'s output went. The transient meta-layer
  application never lands in a declaration, so the emission invariant
  ("elaborated terms are meta-layer β-normal; composition through letbox")
  holds for everything the kernel is asked to re-check per use — the
  box-synthesis-gap discipline, obeyed by construction.

**Routing policy:** `elab_vec_map` consults `meta_defs` for `map_code`;
if registered, the hook path produces the term, otherwise the Rust schema
does. The Rust `vec::map` stays, as the oracle the cross-check compares
against (and the fallback for every file that doesn't declare `map_code`).
No attribute system in this round — the name is the contract, documented
at the dispatch site.

## 5. Elaboration plumbing (the real work items)

1. **Abstract-base local contexts.** The payload elaborates at
   `Layer::Code` in a context whose *base* is the context variable `g` and
   whose entries are the payload's own binders. The elaborator's `LocalCtx`
   must represent that base (surface variables from `g` are unreachable —
   fine: in pure quotation every free reference is a splice or a payload
   binder). Kernel checking already supports it (`in_ctx` with a `Ctx`
   term).
2. **Quotes are checking-only**, mirroring the kernel (`BoxTm` is
   `NotInferable` by design). A `code {}` block in inference position is a
   diagnostic pointing at the annotation that would fix it. Splice
   hoisting happens at the quote boundary; `$x` for a `Code`-typed local
   hoists a letbox, `$a` for a `TyCode` binder becomes a `GlobalTy`
   reference, `${expr}` is the general form `$ident` degenerates from.
3. **Meta-layer expression grammar is minimal**: a `meta fn` body is
   `let code` bindings and a quote (plus, transitively, whatever checks at
   layer m without new forms). No `rec`/`match` at the meta layer, no
   `match code` — declined with a diagnostic naming this round's scope.
4. **Name/index bookkeeping**: the elaborator owns the name↔index map for
   payload binders and letbox-bound globals; kernel display names are
   cosmetic, per surface-v0 §5.

## 6. What can go wrong, named in advance

- **The stuck-head risk**: if evaluation goes neutral (a splice that isn't
  a box literal at evaluation time, fuel exhaustion), the hook must
  decline loudly, never emit a half-reduced term. Negative control
  required (§7 item 5).
- **Adequacy is not soundness**: the kernel re-checks every emitted term,
  so a wrong `map_code` yields checked theorems about the wrong function —
  the same posture as vec.rs (its header says so), which is why the
  cross-check is conversion against the Rust output, not just "it checks".
- **The `Debug`/OOM discipline applies**: evaluation happens under
  elaborator fuel; tests run only under `scripts/test`, and any new
  recursive display goes through the budget-bounded fmt.

## 7. Acceptance

1. `lib/vec_code.hthr` declares `map_code` in the surface slice; the
   declaration kernel-checks at `Layer::Meta`.
2. The hook evaluates it at a **literal** length and element type
   `Nat`: `.map` through the hook produces a term convertible with the
   Rust `vec::map` output, and the enclosing `refl` theorem
   (`bump([1,2]) = [2,3]`-style, the container_recursion fixture) checks.
3. Same at a **neutral** length in an ambient (n, xs) context, and at an
   **open element type** (`A = Vec(Nat; m)`, m ambient) — the two axes
   closed-type tests cannot see (docs/testing-generated-terms.md); the
   use sits in a **checking** position in at least one fixture.
4. Cross-check proper: for each fixture, `conv_term` of hook output vs
   Rust `vec::map` output at `Layer::Prog` — adequacy, not just typing.
5. Negative controls, **as landed** (crates/elab/tests/in_language_map.rs
   and quotation.rs): (a) a registered template whose Π spine is too short
   errors loudly at the use site — never a silent fallback, never a
   half-applied term; (b) the routing proof: a template with its element
   binders *swapped* still checks as a `meta fn`, and an `A ≠ B` instance
   then fails the kernel gate — while the same file elaborates fine
   without the template, so it is the hook that carried the wrong shape
   in; (c) `code {}` in inference position, a `Ctx` binder after a `Code`
   parameter, quotes outside `meta fn`s, goals inside them, `${…}`
   compounds, and both `TyCode` refusals produce their diagnostics.

   The originally planned control — "a mutated motive still checks but
   fails the conversion cross-check" — turned out **unwritable**, and the
   reason is a finding: at the generic type, the template is rigid.
   `f(head(v))` is the only `B` in scope, `ih(tail(v))` the only
   `[B; zk]`, the lengths pin every position — parametricity plus the
   length index force the well-typed template to *be* map. Adequacy at
   generic type is carried by the types; the conversion cross-check (item
   4) still guards the instances.
6. A file that never declares `map_code` elaborates exactly as before
   (Rust path; existing suites green).

## 8. Deferred, recorded

- **Ψ-resident meta definitions** (true kernel residency, layer-indexed
  transparency at m): a metatheory-grade kernel round, wanted when meta
  fns need to *reference each other* or persist across elaboration units;
  goes with `issues/metatheory-ch07-definitions.md`'s obligations.
- **`match code` / the analysis story**: next artifact per the migration
  order (the certifying generator's fragment transcriber), after this
  pipeline is proven.
- **Levels**: `map_code` at level 0 only; level-generic means
  generator-per-level until ULam surfaces
  (`issues/implicit-level-polymorphism.md`).
- **Delayed substitution `$body[x := $arg]`** (surface-v0 §5): not needed
  by `map_code`; enters with the first artifact over open code.
