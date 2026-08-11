# The registration seam: how the elaborator knows which `meta fn` elaborates what

Design sketch for `issues/meta-def-registration.md`, the first of the two
gates `issues/quotation-stage-artifacts.md` names before the template family
grows past a couple of members. Round pattern as usual: this document first,
the implementing round against §8's test plan and §9's sketch.

The question the issue frames: does a template **declare** what it elaborates,
or does the elaborator **ask** the meta layer? The answer below is *declare*,
and the interesting half of the answer is not the declaration — it is what the
declaration has to carry so that the use site stops knowing the template's
shape. That is the part `tabulate_code` breaks today, and §4 is the validation
against it.

## 1. What this round removes

Three pieces of per-template hard-coding, all at the use site
(`crates/elab/src/lib.rs`, `elab_vec_map` :2478 and `elab_vec_fold` :2638):

1. **The literal template name.** `"map_code"`, `"fold_code"` — "the name is
   the contract", documented at the dispatch site as a one-round expedient.
2. **The argument vector, in the template's Π order.** `vec![f_t, len, xs_t]`
   for map; `vec![z_t, f_t, len, xs_t]` for fold. The call site is where the
   template's binder order is written down, and nothing checks it.
3. **The two-code prefix.** `try_vec_code_hook` (quote.rs:486) takes `al, bl,
   a_ty, b_ty` and Tarski-codes exactly two leading type arguments, because
   both templates happen to open with `(A: Type<0>) -> (B: Type<0>)`. The
   fold-round log calls this out: it is baked into the *shared* hook, and it is
   exactly what `tabulate_code` (one type parameter, no receiver vector) and
   `nth_code` will break.

And one gap at the declaration site: nothing but the use-site loud error stops
a user `meta fn` named `map_code` of an incompatible shape from being routed.

What this round does **not** touch: the kernel gate (every emitted term is
re-checked, registration never affects soundness), the Rust schemas (they stay
as oracles and as the fallback), and the meta-slice restrictions of
`docs/in-language-map-design.md` §5.

## 2. Decision: templates declare a **slot**, and a slot is typed

A **slot** is an elaboration site the elaborator is willing to hand over: today
`vec.map`, `vec.fold`, and (§4) `vec.tabulate`, `vec.nth`. The vocabulary of
slots is fixed in the elaborator, one entry per Rust schema that has an
in-language mirror. A template declares which slot it fills; the elaborator
indexes templates by slot and checks, at registration time, that the template
*has the slot's type*.

Three facts make this the shape rather than a resolver query (§6 records the
rejection in full, this is the short form):

- A code type can only be indexed by **globals** — `Ctx`/`TyCode` binders —
  never by a Π-bound local (`docs/in-language-map-design.md` §3, correction 1;
  ch. 04's `\CAPP` rule wants a *concrete* `\lpjudge \proglevel \Delta`, l.
  1086). So a meta-level query's result type cannot mention the use site's
  element type, length, or function. A resolver could not *see* the instance it
  is resolving; it could only answer a question already answered statically.
- There is no `match`/`rec` at layer m in this slice (quote.rs's meta-body
  grammar), and `issues/generators-in-the-language.md`'s blockers (2)–(4) — no
  generation-time oracle, no code equality, no context computation — are
  exactly the machinery a resolver would need to compute an answer.
- What *is* expressible today, `resolve : CtxPi g. Sum(Unit, Code(g ⊢ T))` for
  a slot-fixed `T`, is isomorphic to a table lookup with extra steps.

So the seam is a table. The design's job is to make the table carry enough that
the call sites stop carrying it.

### 2.1 What a template author writes

One clause, after the parameter list:

```heather
meta fn map_code(g: Ctx) for vec.map -> Code(g |-
    (A: Type<0>) -> (B: Type<0>) -> (f: A -> B) -> (k: Nat) -> (v: [A; k]) -> [B; k]
) { code { … } }
```

Two things changed against the landed `lib/vec_code.hthr`: the `for vec.map`
clause, and **every payload binder is named**. The names are not decoration —
they are the argument protocol (§2.3). A dispatched template with an anonymous
binder (`A -> B` rather than `(f: A -> B)`) is a registration error pointing at
it.

`for` is a contextual keyword (the parser's keywords are all contextual
`Ident`s, parser.rs:252), the slot is `family "." name` using the existing
`Dot` token, and the clause sits before `->` so the parse point is
unambiguous. It is legal only on a `meta fn`.

A `meta fn` **without** a `for` clause is never dispatched, whatever it is
named. That is the point at which "the name is the contract" is retired.

### 2.2 What the elaborator does at registration time

`elab_meta_decl_inner` keeps everything it does today (elaborate the modal
signature and the quotation body, kernel-check statement and term at
`Layer::Meta`) and then, if there is a `for` clause:

1. **Resolve the slot.** Unknown slot → error listing the known ones. This is
   a closed vocabulary by decision; user-defined slots are deferred (§10).
   *(Amended by the implementing round:)* also require the template to take
   exactly one `Ctx` binder and no `Code` parameters — the hook applies
   `CtxApp` and then the payload's Π spine, so a `Code` parameter would have
   no argument position. Own diagnostic, own test.
2. **Read the Π order off the surface signature.** Walk the `TyKind::Fn` chain
   of the declaration's `Code(g |- …)` result type, collecting binder names in
   order. Each must be one of the slot's **ingredient names**, no duplicates,
   all of them present, and the chain must have exactly the slot's arity. The
   result is a permutation `order : Vec<Ingredient>`. The names come from the
   *surface AST*, never from kernel display names (which are cosmetic,
   surface-v0 §5).
3. **Check the type.** Build the slot's generic template type in Rust *from
   the slot spec and this order* and require the registered statement to be
   convertible with `CtxPi g. Code(g ⊢ that)` at `Layer::Meta`. Convertible,
   not syntactically equal: definitional variants of the same signature are
   the same signature, and conversion is the kernel's own answer to that.
4. **Claim the slot.** A second template claiming a slot already claimed in
   this elaborator is an error naming the first. No shadowing, no last-wins:
   two templates for one site is a program the author did not mean to write.

Every one of these is **loud, at the declaration span**. That is the design's
main safety move: the class of failures the issue worries about ("nothing stops
a user meta fn of incompatible shape") stops being a use-site surprise and
becomes a declaration-time diagnostic, before any use site exists.

Step 3 also transfers §7 of the map design doc — parametric rigidity — to user
templates for free. `map_code` is rigid *at its generic type*; a registered
template is required to have that type; so the rigidity argument covers every
registered template, not only the one in `lib/`. Where the type is not rigid
(`fold_code`, whose result carries no index — see the `lib/vec_code.hthr`
header) the conversion cross-check keeps doing the real work, unchanged.

**This is not a soundness gate**, and the doc should keep saying so where the
code does: the check fixes the template's *type*, never its body. A constant
fold has `fold_code`'s type exactly. Registration decides which functions get
the in-language path; the kernel decides what is true.

### 2.3 What a use site does

A slot spec is a static table entry:

```rust
struct SlotSpec {
    slot: Slot,
    /// Ingredient names, canonical order (documentation and diagnostics only),
    /// each with the kind that decides how it is materialized.
    ingredients: &'static [(&'static str, IngredientKind)],
}
enum IngredientKind { Type, Term }
```

and the use site hands over a **bag of named ingredients**, in whatever order
is convenient for the Rust code that computed them:

```rust
self.try_code_template(cx, Slot::VecMap, &[
    ("A", Ingredient::Type { level: al,  ty: a_ty  }),
    ("B", Ingredient::Type { level: &bl, ty: &b_ty }),
    ("f", Ingredient::Term(f_t.clone())),
    ("k", Ingredient::Term((**len).clone())),
    ("v", Ingredient::Term(xs_t.clone())),
], span)?
```

`try_code_template` then: looks up the slot (absent → `Ok(None)`, the Rust
path); permutes the bag into the registered template's `order`; materializes
each ingredient — a `Term` passes through, a `Type` becomes its Tarski code via
`code::code_of` and **declines** (`Ok(None)`) if the level is not 0 or the type
has no code; evaluates `CtxApp(template, Γ)` by iterated δ-transparent WHNF to
a `BoxTm` (anything else is loud, as today); infers the payload once and walks
its Π spine applying the materialized arguments, annotating each `App` from the
peeled domain (as today).

The two-code prefix is gone: "the leading two arguments are types" becomes "the
ingredients of kind `Type` are Tarski-coded, wherever the template's order puts
them, however many there are".

### 2.4 Failure modes, one line each

| When | What | Why |
| --- | --- | --- |
| decl: unknown slot | loud, lists known slots | typo, or a slot that does not exist yet |
| decl: unnamed / unknown / duplicated / missing binder | loud, points at the binder | the names *are* the protocol |
| decl: statement not convertible with the slot type | loud, prints both | a shape the use site could not feed |
| decl: slot already claimed | loud, names the first template | two templates, one site |
| use: no template registered for the slot | **decline**, Rust path, silent | the ordinary case for every file that never loads `lib/vec_code.hthr` |
| use: a `Type` ingredient at level ≠ 0, or with no Tarski code | **decline**, Rust path, silent | the level-0 template honestly cannot take this instance |
| use: evaluation does not reach a `box` within fuel | loud, names the stuck head | never emit a half-reduced term (§6 of the map design) |
| use: payload does not type at the use site | loud, "the template is wrong, not the caller" | as today |
| use: Π spine shorter than the order | loud | defensive; §2.2 step 3 makes it near-unreachable, keep it anyway |

The invariant behind the table: **declines are static properties of the
instance** (no template, or a type this level-0 slice cannot code), and
everything else is loud. A registered template never silently declines a
use site it typechecked for.

## 3. Where the Π-order knowledge lives — the crux

In the template's own signature, read once at registration, and nowhere else.

- The **use site** knows: which slot, and which ingredients it can name. It
  does not know the order, does not know which ingredients are types, does not
  know the arity.
- The **slot spec** knows: the ingredient vocabulary and each ingredient's
  kind. It is order-free — its `ingredients` list has a canonical order only so
  diagnostics can print something.
- The **template** knows: the order, because the order *is* its Π spine, and
  because a template's order is not free — it is forced by dependency (§4.3).

That is the whole answer to "how does the call site know what to pass in what
order": it doesn't, and it can't, and after this round it doesn't have to.

## 4. Validation: `tabulate_code`

`vec::tabulate` (vec.rs:266) is `tabulate(B; k; f) : Vec(B; k)` for
`f : Π(i : Fin k). B`: **one** type parameter, an index-function argument, no
receiver vector, and the `d + 1` codomain subtlety that needed its own
open-element regression test (`tabulate_at_an_open_element_type`, the comment
at vec.rs:277).

### 4.1 The template

```heather
meta fn tabulate_code(g: Ctx) for vec.tabulate -> Code(g |-
    (B: Type<0>) -> (k: Nat) -> (f: Fin(k) -> B) -> [B; k]
) {
    code {
        fun (B: Type<0>) => fun (k: Nat) =>
            match k as λ z => (Fin(z) -> B) -> [B; z] {
                Zero => fun (f: Fin(0) -> B) => [],
                Succ(zk, ih) => fun (f: Fin(Succ(zk)) -> B) =>
                    cons(f(fin_zero), ih(fun (j: Fin(zk)) => f(fin_succ(j)))),
            }
    }
}
```

The `d + 1` subtlety does not appear, as `issues/quotation-stage-artifacts.md`
predicted: `B` is a binder, `f`'s type is written under it, and the calculus
does the shifting. That is the thesis-by-deletion this family is for.

### 4.2 How dispatch reaches it

The slot spec is `vec.tabulate: [("B", Type), ("k", Term), ("f", Term)]`.

The use site is **not** a surface method — it is `elab_container_ih`
(lib.rs:2766), the self-call over a container binder, where the elaborator has
just built `h = λ(i : Fin len). ih (inr^m i)` by hand. It hands over
`{B: (c.mlvl, result), k: len_rc, f: h}` and reads the result back at
`Vec(result; len)`. Notice what it does not do: it does not know that `B` is
coded, that `B` comes first, or that there are three arguments.

The decline path is live here rather than theoretical: `c.mlvl` is the motive's
level and is not always 0, so a level-1 instance takes the Rust schema —
silently, correctly, and with the same output it has today.

### 4.3 Why the order cannot live at the call site

`tabulate_code`'s order is not `(B, k, f)` by taste. `f`'s type mentions `k`,
so `k` precedes `f` in **any** well-formed spelling; `B` precedes both. The
admissible orders are a strict subset of the permutations, determined by the
template's own dependency structure — and for a slot like `vec.fold`, whose
`z : B` and `f : A -> B -> B` are independent of `k`, there are several
admissible orders and no reason for the elaborator to prefer one. A call site
that hard-codes an order is asserting a fact about a program it did not write.
Under §2 it asserts nothing: it names ingredients, and the signature it was
checked against imposes the sequence.

This is also the positive test the implementation round must write (§8.4): a
legally *permuted* template must produce a term convertible with the Rust
oracle's, with no call-site change.

### 4.4 The blocker `tabulate_code` actually hits — and it is not registration

**`Fin` has no surface spelling.** `TyKind` (ast.rs:222) has `Nat`, `Eq`,
`Univ`, `OfExpr`, `Named`, `Vec`, `Fn`, `Ctx`, `TyCode`, `Code` — no `Fin`; and
`ExprKind` has no index constructors (`inl ⟨⟩` / `inr`), no `elim_Empty`, and
there is no `xs[i]` (brackets are vector types and literals only). `Type::Fin`
is constructed exclusively elaborator-side (wf.rs, `elab_container_ih`).
`docs/types-as-expressions.md`'s coverage table lists `Fin` as "reachable from
the surface", which is true of its *code* (`TmFin`) and not of its syntax; that
row is worth correcting when this lands.

A user-declared `Fin` inductive is not a substitute: it would lower to a `Wf`
type, not `Type::Fin`, and the cross-check against the Rust oracle would
rightly fail.

So the sequencing verdict from this validation:

- The registration seam **survives** `tabulate_code` — the design above is
  what it needs and is sufficient for it. That is what the validation was for
  and it passes.
- `tabulate_code` itself is blocked on a **surface indexing layer**: `Fin(n)`
  as a type, and its two index constructors as expressions. `nth_code` needs
  strictly more (a case on `Fin`, i.e. an `elim_Empty` in the zero arm —
  term.rs:1104's spelling). `docs/container-proofs.md` §7 already anticipates
  this layer ("it should land *with* the surface indexing layer (`Fin`,
  `xs[i]`)").
- Consequence for `issues/quotation-stage-artifacts.md`: the candidate order
  "fold, tabulate, nth" should be re-read as "fold (landed), *surface indexing
  layer*, then tabulate and nth". File the layer as its own issue
  (`issues/surface-fin-indexing.md`, labels `[frontend,elaboration]`) and add a
  log line to quotation-stage-artifacts pointing at it; do not let it ride
  inside a template port.

The registration round is therefore independently landable, and should land
first: it is validated against `tabulate_code` on paper, it removes the
hard-coding from the two templates that exist, and it means the indexing-layer
round adds a template rather than a third call-site pattern.

## 5. Declines and loud failures, per template

The policy of `docs/in-language-map-design.md` §6 generalizes without change
once the type-versus-term distinction moves into the slot spec:

- **Decline** is a property of the *instance*, decided before evaluation, and
  is exactly two conditions, both about materializing a `Type` ingredient: a
  non-zero level, or no Tarski code. Any number of type ingredients, in any
  position. Nothing after the first `CtxApp` can decline.
- **Loud** covers everything downstream, unchanged in kind and now shared:
  stuck evaluation, an untypable payload, a short spine. Because there is one
  entry point, a new template inherits all three diagnostics — including their
  wording — rather than re-deriving them.
- **Registration-time loud** is new (§2.2). It is where the honest-declines
  policy gets its counterpart: a template that *could not* serve a slot is
  rejected where it is written, so the use site's decline path never has to
  mean "maybe the template was wrong".

One thing deliberately not added: a **dynamic** decline ("this template only
handles literal lengths"). There is no mechanism for it (the meta layer cannot
inspect the instance, §2), and the loud-failure policy says a registered
template handles everything its type admits. Deferred, §10.

## 6. Rejected alternatives

**A resolver-style query — the elaborator asks the meta layer.** The issue's
other horn, and the strongest alternative because it is what
`issues/lsp-from-the-meta-layer.md` and `issues/generators-in-the-language.md`
eventually want. It loses on type theory, not on taste: a code type is indexed
by globals only, so the query's answer type cannot mention the instance
(`docs/in-language-map-design.md` §3, correction 1; ch. 04's `\CAPP` needs a
concrete `Δ`, l. 1086) — a resolver is blind to the very thing it would be
resolving. Computing an answer would additionally need `match` at layer m
(outside this slice) and, for anything interesting, blockers (2)–(4) of
generators-in-the-language. The degenerate query that *is* expressible today,
`CtxPi g. Sum(Unit, Code(g ⊢ T))` at a slot-fixed `T`, is a table lookup with a
kernel reduction in front of it. Recorded as deferred, not refuted: §7 says
what the chosen design leaves in place for it.

**A naming convention (`<slot>_code`), i.e. keeping today's rule and adding
only validation.** Zero parser change, and the incompatible-shape worry is
fixed by §2.2's checks regardless of how the slot is named — so this is the
cheapest thing that could work. It loses for three reasons: it makes a program
name semantically load-bearing, so renaming a template silently changes what
elaborates; it cannot express a meta fn that is *not* a dispatch template
(helpers arrive as soon as meta fns can reference each other); and it leaves
the seam invisible in the source, which is precisely the property the fragment
transcriber and the LSP want to read off. One contextual keyword buys all
three.

**Widening the shared prefix, or passing a full argument list.** The fold-round
log's own two options. Widening ("three codes and a rest") re-breaks at the
next template with a different arity — `tabulate` breaks it immediately. A full
positional argument list moves the Π-order knowledge from inside the hook to
the call site verbatim, which is where it already is and where it cannot be
checked. Both are the same bet — that call sites can know template shapes — and
§4.3 is the argument that they cannot.

**Matching arguments by kernel binder names, or inferring the order by
matching types.** Kernel display names are cosmetic (surface-v0 §5), so the
first is unsound in the ordinary sense of "the compiler believes a comment".
The second is ambiguous exactly where it matters: `A` and `B` are both
`Type<0>`, and any type-directed matcher would have to guess.

**Name-matching without the conversion check** (§2.2 step 3). Cheaper, and it
catches the shape errors that produce a wrong arity — but it lets a swapped
`(B: Type<0>) -> (A: Type<0>) -> …` register happily, deferring the failure to
whichever use site first has `A ≠ B`. Since the slot's type is already written
in Rust (it is the schema's type), checking it is a dozen lines and moves that
failure to the declaration.

**A general attribute system.** Out of scope by the issue's own instruction,
and there is nothing to generalize over: one clause with a closed vocabulary
serves five templates and gives the transcriber a place to land.

## 7. What this buys, and does not, for the two later consumers

**`issues/lsp-from-the-meta-layer.md`.** It buys the *table*: after this round
the elaborator holds `slot → (template name, declaration span, checked
statement)`, which answers "which elaborations in this file are in-language,
and where is the source" as a projection of elaborator data, in the
`GoalReport` shape that issue asks new diagnostics to keep to (data in `elab`,
rendering in the front end). It does **not** buy the interesting half — a
`Code(Γ ⊢ T) → Presentation` written in the language — which needs `match code`
and is gated behind the analysis story, unchanged by this round.

**`issues/generators-in-the-language.md`.** It buys one dispatch entry point
and one registration path: the fragment transcriber arrives as a new
`SlotSpec` plus one `try_code_template` call, not as a third hand-written call
site with its own argument-order knowledge. The `for` clause is also the
syntactic place a user-declared slot would attach, so the extension point is
named even though it is closed. It does **not** buy user-defined slots, meta
fns calling meta fns (that is Ψ-residency, `docs/in-language-map-design.md`
§8), or any dynamic dispatch — all of which stay behind the same four blockers
the 2026-08-02 verdict enumerated.

**`issues/meta-hook-evaluation-cost.md`** gets a landing spot for free: its
lever (1), "evaluate and infer once per registered template, cache `(payload,
ty)`", is a field on the registration entry, keyed by slot. Not scheduled here;
noted so the implementing round leaves room for it rather than designing it
away.

## 8. Test plan for the implementing round

`docs/testing-generated-terms.md`'s four axes (literal *and* neutral
scrutinee, an **open** element type, a checking position, a negative control)
apply to every newly-ported template and are already the shape of
`crates/elab/tests/in_language_{map,fold}.rs`. Below are the obligations the
**registration mechanism itself** adds. New file:
`crates/elab/tests/template_registration.rs`.

1. **Nothing changed for the existing families.** Both suites stay green after
   `lib/vec_code.hthr` gains its `for` clauses and its binder names, including
   the cross-checks and the "still elaborates without the lib" control. Also
   back-port the fold suite's `assert!(ht != rt)` vacuity guard to the map
   suite (already flagged in `issues/quotation-stage-artifacts.md`'s log) —
   this round touches both files anyway.
2. **The name stops being the contract.** A `meta fn map_code` with the right
   signature and **no** `for` clause registers as a meta definition and is
   *not* dispatched: a `.map` in the same file produces the Rust term. This is
   the regression that proves the old rule is gone.
3. **An incompatible user template is rejected at its declaration**, one test
   per §2.4 registration row: unknown slot; an anonymous binder; a binder named
   outside the vocabulary; a missing ingredient; a duplicated one; a shape the
   conversion check refutes. *(Amended by the implementing round — this item
   was wrong as first written, and the correction is the design working:)* a
   "swapped" `(B: Type<0>) -> (A: Type<0>) -> …` with the **names** attached
   is a legal *permutation* of the slot's signature and must be **accepted** —
   it is the positive control of item 4, not a rejection. What conversion
   rejects is a template whose ingredient *types* disagree once names resolve
   (e.g. a result of `[A; k]` where the slot returns `[B; k]`). The fold
   suite's `a_swapped_template_breaks_an_a_neq_b_instance` control therefore
   became `a_permuted_template_is_the_same_template`.
4. **A permuted-but-legal template still works** — the positive control for
   §3. Register `fold_code` at `(A) -> (B) -> (k: Nat) -> (f: A -> B -> B) ->
   (z: B) -> (v: [A; k]) -> B`, change no call site, and require the emitted
   term to be convertible with the Rust oracle's at a neutral length. If this
   passes, the Π-order knowledge is genuinely in the signature.
5. **Two templates, one slot**: a second `for vec.fold` in the same elaborator
   is an error naming the first. Also the negative: two templates for
   *different* slots in one file coexist (the `lib/` file itself is that test).
6. **The decline paths are still silent and still correct**: a `Type`
   ingredient at level 1 and one with no Tarski code each take the Rust path,
   the file elaborates, and the emitted term equals the no-lib one.
7. **The loud paths are still loud, once each, at the shared entry point**:
   the short-spine error and the stuck-evaluation error. *(Finding of the
   implementing round:)* both are now **unreachable from the surface** — the
   short spine because the payload's type was checked against the slot's at
   registration, the stuck head because §2.2's one-`Ctx`-binder rule leaves
   `CtxApp` of a `CtxLam`, which always fires. Both guards stay in place,
   untested, with a comment block in `template_registration.rs` recording the
   status (same standing as the uncovered-former diagnostic,
   `types-as-expressions.md` §2). Reachability returns exactly when a slot
   gains a code-typed ingredient — user-defined slots or the fragment
   transcriber — and that round re-acquires this test obligation.
8. **Body adequacy is still not typing.** Keep
   `a_mutated_arm_checks_but_fails_the_cross_check`: the constant fold has the
   slot's type exactly and must still be caught by conversion, which is the
   test that shows §2.2 step 3 is a typing gate and not a soundness one.

Everything runs under `scripts/test`.

## 9. Implementation sketch

**`crates/syntax`** — `ast::Decl` gains
`elaborates: Option<SlotPath>` where `struct SlotPath { family: String, name: String, span: Span }`;
`parser::decl` gains, between the parameter list and the `->`, roughly

```rust
let elaborates = if self.eat_kw("for") { Some(self.slot_path()?) } else { None };
```

with a diagnostic when it appears on a non-`meta` declaration.

**`crates/elab/src/slots.rs`** (new, small) —

```rust
pub(crate) enum Slot { VecMap, VecFold, VecTabulate, VecNth }
pub(crate) enum IngredientKind { Type, Term }
pub(crate) struct SlotSpec { slot: Slot, path: (&'static str, &'static str),
                             ingredients: &'static [(&'static str, IngredientKind)] }
pub(crate) static SLOTS: &[SlotSpec];
pub(crate) fn lookup(path: &SlotPath) -> Option<&'static SlotSpec>;
/// The slot's generic template type, in the order the template declares —
/// what §2.2 step 3 checks the registered statement against.
pub(crate) fn expected_code_ty(spec: &SlotSpec, order: &[usize]) -> Type;
```

`expected_code_ty` is per-slot Rust that builds a *type*, not a term. *(Amended
by the implementing round:)* not hand-written Π chains — §8.4's permuted
templates mean the same slot type must be buildable in *any* declared order,
and a hand-written chain hard-codes one. It became a tiny ingredient-type
vocabulary (`ITy` in slots.rs) plus one generic Π-chain builder that resolves
ingredient names to de Bruijn indices at the declared depth; each slot's spec
is a handful of readable lines and the index arithmetic is written once.

**`crates/elab/src/quote.rs`** —

```rust
fn register_slot(&mut self, decl: &Decl, stmt: &Type) -> R<(&'static SlotSpec, Vec<usize>)>;
fn payload_binder_names(result: &Ty) -> R<Vec<(String, Span)>>;   // surface AST walk

pub(crate) enum Ingredient<'a> { Type { level: &'a Level, ty: &'a Type }, Term(Term) }

/// Replaces `try_vec_code_hook`. Same body from the `CtxApp` down; everything
/// above it is the slot lookup and the permute-and-materialize step.
pub(crate) fn try_code_template(
    &self, cx: &Cx, slot: Slot, args: &[(&'static str, Ingredient<'_>)], span: Span,
) -> R<Option<Term>>;
```

`elab_meta_decl_inner` calls `register_slot` after its two `typing::check_*`
calls (registration is checked code only) and stores the result.

**`crates/elab/src/lib.rs`** — `MetaDef` gains `slot: Option<Slot>` and
`order: Vec<usize>`; `Elaborator` gains `meta_slots: HashMap<Slot, String>`
(and, when `issues/meta-hook-evaluation-cost.md` is scheduled, the cached
`(payload, ty)` beside it). `elab_vec_map` and `elab_vec_fold` shrink to the
named-bag call of §2.3 and lose their template names, argument vectors, and
prefix comments. `elab_container_ih` gains the same call for `vec.tabulate`
when §4.4's blocker clears — not in this round.

**`lib/vec_code.hthr`** — two `for` clauses, four binders named, and a header
note that the signature is now checked against the slot.

Net: one new small module, one new parser clause, one hook renamed and
generalized, two call sites shortened.

## 10. Deferred, recorded

- **User-defined slots** — a `for` path that names something the elaborator
  does not know. Wanted when a generator elaborates something the elaborator
  has no Rust schema for at all; it needs a story for what the *contract* is
  when there is no Rust type to check against. Goes with
  `issues/generators-in-the-language.md`, after the analysis story.
- **Resolver-style dispatch** (§6). Filed against
  `issues/meta-def-registration.md`'s own log as the deferred horn; unblocked
  only by `match code` plus blockers (2)–(4).
- **Dynamic declines** — a template that inspects the instance and hands it
  back. Same blocker as the resolver; the loud-failure policy says it is not
  wanted before then.
- **Multi-signature slots** (a curried or flipped `fold` at the same slot).
  No consumer; the slot-as-contract decision is what rules it out, and it
  would return as a list of admissible types rather than one.
- **The surface indexing layer** (`Fin(n)`, its index constructors, a case on
  `Fin`) — §4.4. Not deferred so much as *sequenced ahead of* `tabulate_code`
  and `nth_code`; file as `issues/surface-fin-indexing.md` and reference it
  from `issues/quotation-stage-artifacts.md`'s candidate list.
- **Per-template evaluation caching** — `issues/meta-hook-evaluation-cost.md`
  lever (1), whose natural home is the registration entry this round creates.

---

## 11. Extension, 2026-08-11: **analyzer slots**

*Landed by the fragment-transcriber round
(`docs/certgen-transcriber-in-language-design.md`); recorded here because the
seam is this document's, not that one's.*

This document's slots are **template** slots: a `meta fn` returning
`Code(g ⊢ T)`, applied to the use site's context and then to the slot's
ingredients down its *payload's* Π spine. The first analysis-stage artifact is
not that shape and cannot be. A transcriber consumes code and returns a
**value**, because its `match code` motive has to be context-free: a motive
`Code(g ⊢ T)` would give the `lam` and `elim_nat`-step branches recursive
results at *extended* contexts, and nothing brings a `Code((g, x) ⊢ T)` back
down to `g`. So the analysis stage's artifacts return data, take their
arguments as their own Π binders, and have no payload at all.

Left unextended, the seam had two ways to serve them, and both were wrong.
Routing by name is what §2 retired. Widening `ITy` until it can spell
`Code(g ⊢ Nat)` and a library inductive re-states the whole problem: an
inductive is *inlined*, not a Ψ global, so there is nothing for a Rust-built
type to reference.

**The extension.** A second kind of slot — an **analyzer slot** — with the same
`for family.name` clause, the same closed Rust vocabulary, the same
declaration-time loudness, the same one-template-per-slot rule, and the same
not-a-soundness-gate stance. Two things differ:

1. **Its contract is a whole signature, not a payload spine.** The spec carries
   a `meta fn` signature *written in Heather*, elaborated at registration time
   in the declaring file's scope (`slots::AnalyzerSpec::signature`,
   `Elaborator::register_analyzer`); registration requires the declared
   signature to be **convertible** with it. A name the file has not declared
   fails there, loudly, with the slot named.
2. **The caller builds the spine.** §3's crux is that the Π order must be
   enforced somewhere the caller can rely on. For a template that is the
   payload read-off, because a template's order is genuinely free. For an
   analyzer, whole-signature convertibility fixes the order *outright* — there
   is no permutation left to discover — so the invoking Rust applies the
   arguments in the slot's canonical order and consults nothing. That is §3's
   answer restated for a shape where the answer is stronger, not an exception
   to it.

The vocabulary gains exactly one entry, `certgen.transcribe`, and the round
that added it added one client. Generalizing further waits for a second
customer; **user-declared** analyzer slots are deferred with user-declared
slots generally (§10, first bullet) and for the same reason — there is no Rust
type to check the contract against.

Two smaller consequences worth having written down, both from the same round:

- A `meta fn` may now take ordinary program-layer parameters and return
  ordinary data (`quote.rs`'s `Sig::Local`). The kernel always allowed it —
  Π is layer-generic and a layer-c global is referenceable at m (`i' ≤ i`) —
  and only the surface said otherwise.
- **Elaborator-held definitions go stale, and now say so.** A `MetaDef` is not
  in Ψ, so nothing rescopes it when Ψ grows, while a `GlobalVar` counts from
  Ψ's end — so a definition that *references* a global means something
  different at every later use site. `MetaDef` records `|Ψ|` at registration
  and `MetaDef::at` shifts by the growth. A live bug when the first analyzer
  landed; invisible before, because a pure-quotation template references no
  globals.
- A `meta fn` body may now name an ordinary global, inside a quote payload or
  out of it. The obstacle was never the layer but the index arithmetic: a
  `meta fn`'s own Ψ-extending binders sit above Ψ, and a committed global has
  to be shifted past them (and past a `match code` branch telescope's globals,
  which the arm's elaboration pushes onto the same padding).
