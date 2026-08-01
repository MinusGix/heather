# Value-indexed Σ at the surface: feasibility

Status: **investigation round**, 2026-08-01. No product code changed, no
commits. Tracking issue: `issues/surface-existential.md`.

> **Implemented the same day.** Route 1 landed as specified here; the grammar,
> the substitution rule, the construction decision and the parameters-vs-indices
> line are recorded in `docs/surface-value-parameters.md`, the acceptance in
> `crates/elab/tests/value_parameters.rs`, and the consumers in
> `lib/ir_v1.hthr`. Two sizings came in *cheaper* than §C: the AST split (a
> separate `valparams` list left every existing `ind.params` zip untouched) and
> **construction, which needed no code at all** — `build_ctor` already reads its
> annotations off the expected type, so §C.5's "medium" was a decision, not an
> implementation. Everything else landed as sized, and no kernel change was
> needed, as §A and §H predicted. This document is kept as written: it is the
> pre-round record, not a status page.

The question the issue posed and could not cost: what does it take to state

```
Converges(p, env, ir, vs) := Σ (n : Nat). eval(n, p)(env, ir) = Out(vs)
```

at the surface, and which of the issue's two routes should the implementing
round take?

**Verdict up front.** Route 1 (value parameters on `record`) is feasible with
**no kernel change, no new former, no ch. 07 obligation, and none of
`issues/indexed-families.md`'s machinery**. Every part of the encoding already
type-checks against the real kernel, and everything except *writing the
parameters as parameters* already works at the surface — including the full
`Converges` over the real `lib/ir_v1.hthr` declarations at concrete arguments.
Route 2 (a general Σ over a type-family parameter) is blocked on a different,
larger thing (a `Ty` form denoting a family; monomorphized parameters) and
should be deferred. Details below, question by question.

---

## A. Kernel sufficiency — yes, with nothing new

The kernel already has a **fully dependent Σ**: `Type::Sigma { fst_level,
snd_level, fst, snd }` where `snd` binds one local of type `fst`
(`crates/kernel/src/term.rs:92-97`), formation at `l ⊔ l'`
(`crates/kernel/src/typing.rs:518-527`), `pair` intro
(`typing.rs:1080-1101`), `fst`/`snd` projections (`typing.rs:1103-1156`), β
(`crates/kernel/src/reduce.rs:410-419, 471-478`) and **definitional η**
(surjective pairing, `crates/kernel/src/conv.rs:1166-1177`). `Id` is a v0
extension at `typing.rs:495-501` with `refl`/`J` at `typing.rs:953-1014`.
`crates/kernel/DESIGN.md`'s second extension paragraph is the design record.

The three things that could have bitten, and did not:

1. **Second component depending on the first component's *value*.** That is
   what the `snd` binder *is*. Not a question.
2. **A computed term inside a type.** There is **no matchability or
   layer restriction on which term shapes may appear in a type.** A grep for
   `matchab` over the whole kernel returns zero hits. Three formers embed
   arbitrary terms in a type — `Type::El { tm }` (`term.rs:54`),
   `Type::Vec`/`Fin`'s length (`term.rs:145-153`), `Type::Wf`'s arity
   (`term.rs:167-171`) — and the checker's only premise on those terms is an
   ordinary `tm_check` at the ambient layer (`typing.rs:488-492, 560-583`).
   The `Vec` formation comment says so as a design intent: "the length is a
   term in Γ … which is what lets the tuple's arity be *computed* from a
   shape". So `Id(Res; eval(n, p)(env, ir); Out(vs))` with `eval` a global
   definition and `n` a bound variable is an ordinary well-formed type; a
   stuck computation inside it is handled as a **neutral**
   (`reduce.rs:2143, 2172`, `conv.rs:1266-1273`), not rejected.
3. **Layer restrictions from ch. 04–06.** The layer machinery is coarse and
   orthogonal (`crates/kernel/src/layer.rs:13-33`): `not_var_layer` (layer v
   admits only variables), `meta_layer` (`UPi`/`CtxPi`/`TyPi`/`□`/box/letbox/
   code recursors need m), and `i' ≤ i` on global bindings. None of them
   restrict *which term shapes* may sit inside a type at c/p/m. Crucially
   `Layer::type_layer()` maps `Var|Code|Prog → Prog` (`layer.rs:22-27`), so
   types are always compared at a computing layer and `Tc::whnf` is
   δ-transparent unconditionally (`typing.rs:369-372`) — a global `eval`
   unfolds inside a type even while the surrounding term is at layer c.
   Nothing in `docs/delam/04–06` bears on this: DeLaM has no Σ and no Id at
   all; both are ours (`DESIGN.md`, "Extension beyond the paper").

**Universe/level placement.** Σ's level is a real join,
`Level::max(fst_level, snd_level)`, non-cumulative (`typing.rs:455-458`
compares with `≈`, never `≤`). `Id`'s level is its type's, with no bump
(`typing.rs:495-501`). So `Σ(n : Nat). Id(Res; …; …)` lands at
`0 ⊔ 0 = 0`. See §G.

---

## B. The decisive prototype

Two prototypes, one at each end. Both **first-run green** apart from one
deliberate scoping bug (below).

### B.1 Hand-built kernel terms

`crates/elab/tests/surface_existential_probe.rs` — **9 tests, all passing**
(`scripts/test --test surface_existential_probe`). *Investigation
scaffolding: clearly marked in its module doc, uncommitted, not wired into
CI.* Precedent and idioms: `crates/elab/tests/indexed_route1.rs`.

The miniature is

```text
dbl t   := elim_Nat(_. Nat; 0; _ rec. S (S rec); t)      -- a real recursive fn
Halts(m) := Σ (n : Nat). Id⁰(Nat; dbl n; m)              -- m a FREE variable
```

which is faithful on all three counts that matter: the second component's
type mentions the bound witness, it mentions it *under a recursive
eliminator-defined function* (neutral at a neutral argument, exactly like
`eval(n, p)(env, ir)`), and the right-hand side is a **free value
parameter** — the thing route 1 would let the surface write.

| § | test | what it shows |
|---|---|---|
| 1 | `forms_at_an_open_value_parameter` | the type **forms** with the parameter open — question A, directly |
| 2 | `lands_at_level_zero_and_not_at_one` | level is the Σ join, `0`; checking it at `1` is rejected (non-cumulativity pinned) |
| 3 | `intro_at_a_closed_parameter_discharges_by_conversion` | `⟨2, refl⟩ : Halts(4)` — the *computed-bound discharge* of `ir-simulate-design` §6, closed by conversion running `dbl 2 ⇝ 4` |
| 4 | `intro_on_fully_open_data` | `⟨k, refl⟩ : Halts(dbl k)` — witness open, parameter a computed term over it |
| 5 | `elimination_uses_the_witness_and_the_equation` | the consumer shape: from `h : Halts(m)` and `f : Π k. Q(dbl k)` conclude `Q(m)`, by instantiating `f` at `fst h` and transporting along `snd h` with `J`. **`Q` is an open type family**, so nothing is discharged by computation |
| 6 | `projections_beta_reduce_and_eta_holds` | `fst ⟨k, _⟩ ≡ k` on open data; and **η at a neutral pair**, `h ≡ ⟨fst h, snd h⟩` |
| 7 | `a_witness_for_one_parameter_does_not_inhabit_another` | negative control: the `Halts(4)` witness is rejected at `Halts(5)` and at an open `Halts(m)`; the two *codes* are inconvertible |
| 8 | `iterated_sigma_forms_and_inhabits` | the inversion-lemma shape (§F): `Σ w. Σ(_ : r = S w). dbl w = m`, formed at open `r`, `m` and inhabited at concrete ones |
| 9 | `an_unshifted_parameter_captures_the_witness` | the **generator hazard**, pinned |

**What needed care, and it is the only thing that did.** The value parameter
lives in the ambient Γ and must be `shift_local(1)` under the Σ binder. Get
it wrong and you have written a *different, trivially inhabited*
proposition — `Σ n. dbl n = n`, inhabited by `⟨0, refl⟩` — and **the kernel
cannot see the mistake**, because both spellings are well-formed. §9 pins
this as a generator obligation rather than a kernel-gated one. The same
class of bug bit for real while writing §8: an iterated Σ's *inner* pair
annotations must be the outer `snd`'s **with the witness substituted**, and
writing them un-substituted gave `UnboundLocalVar(0)` — there the kernel
does catch it. Rule for the generator: the parameter substitution is by
`depth` + `shift_local`, exactly the device `TyVar` already uses
(`crates/elab/src/lib.rs:3225-3230`, `inductive.rs:504-514`).

**What failed:** nothing else. No former was missing, no level had to move,
no conversion behaviour had to be worked around.

### B.2 Full `Converges` over the real `lib/ir_v1.hthr` — at the surface

Scratch file (scratchpad `ir_converges.hthr` = `lib/ir_v1.hthr` plus an
appendix), run ulimit-wrapped, **`ok`**:

```heather
record Converges1 {
    n: Nat,
    h: eval(n, add_prog())(VCons(embed_nat(1), VCons(embed_nat(1), VNil)), add_body())
       = Out(VCons(embed_nat(2), VNil))
}

fn add_one_one_converges() -> Converges1 { Converges1(50, refl) }

theorem converges1_loosens(c: Converges1, m: Nat, hle: leb(c.n)(m) = True)
    : eval(m, add_prog())(…) = Out(…)
{ fuel_monotone(add_prog(), …, c.n, m, c.h, hle) }
```

This is the *real* `Converges` — real `eval`, real `Prog`/`Ir`/`Val`/`Res` —
with the four parameters substituted to concrete values. It declares, it is
introduced by a computed bound with the equation closed by conversion, and
both projections (`c.n`, `c.h`) feed the landed `fuel_monotone`. **That is
exactly what route 1's record elaborates to once its parameters are
substituted.** The only thing the surface cannot do is write the parameters
as parameters.

---

## C. Elaboration gap for route 1

Route 1 = `record Converges(p: Prog, env: Val, ir: Ir, vs: Val) { n: Nat,
h: eval(n, p)(env, ir) = Out(vs) }`. Item by item.

### C.1 Parser — **small**

- `record` is parsed by `crates/syntax/src/parser.rs:241-268`, taking
  `tyvar_list()` (`parser.rs:271-285`, `<A, B>` → `Vec<String>`) and then
  requiring `{`. `record Small(m: Nat) { … }` today is
  `parse error: expected `{` (field list), found LParen` (verified), so the
  position is **free and unambiguous** — a `(` after the record name (or
  after its `<…>`) can only be a parameter list.
- **No ambiguity with `fn`.** `fn`/`theorem` do *not* use `tyvar_list`; they
  have their own inline loop (`parser.rs:376-405`) and their own
  `TyParam { level }` type (`ast.rs:116-120`). `record`/`inductive` share
  `tyvar_list` only with each other. The value-parameter list should reuse
  the existing `ast::Param` struct (`ast.rs:174-190`) — the same node `fn`
  parameters already use — which gets `{implicit}` and `self` for free if
  ever wanted.
- Declaration-position `<` needs no backtracking (`parser.rs:372-374`: a decl
  name is always followed by `(` or `<`). Note the consequence: once a record
  may take `(`, `record R(…)` and `record R<A>(…)` must both be accepted, in
  that order.

### C.2 AST — **small**

`InductiveDecl.params: Vec<String>` (`crates/syntax/src/ast.rs:47`) becomes
two lists, or one list of a `Param`-like enum. Everything downstream that
zips `ind.params` with type arguments (`inductive.rs:519-534`, `672-682`,
`indexed.rs:205-218`) has to learn the split. Mechanical but wide-ish.

### C.3 Elaborator: substitution of parameters into field types — **small**

This is the load-bearing finding and it is a *good* one. `lower_ctor`
(`crates/elab/src/inductive.rs:657-720`) already builds the field spine in a
context `fcx` that carries the declaration's parameters as `TyVar { name,
ty, level, depth }` (`inductive.rs:672-682`), and uses at
`inductive.rs:504-514` are weakened by `cx.names.len() - p.depth`. A **value
parameter is the same mechanism with a `Term` instead of a `Type`**: a
`ValParam { name, tm: Term, ty: Type, level, depth }` list on `Cx`,
consulted by the *expression* elaborator's variable lookup rather than by
`lower_named`, shifted the identical way. The `Alias` struct
(`lib.rs:3236+`) is already exactly this shape — an elaborated term inlined
at each use with a `depth` — so there may be nothing to invent at all.

Two facts make this small rather than speculative: (a) field N is *already*
elaborated in a context containing fields 1..N-1 (`inductive.rs:688-691`,
pushed onto `fcx` before the next iteration) — see §D; (b) the open-parameter
case already works and is already load-bearing (`Monoid<A>` inside
`fn twice<A>`), so `depth`-shifting against an *ambient theorem context* is
exercised code, not new code. `issues/tyvar-scoping-in-lowered-fields.md` is
the scar tissue.

### C.4 Use-site formation — **small**, and the hook already exists

`Converges(prog, env, ir, vs)` in **type position** already parses and
already reaches the elaborator's family hook:

- `TyKind::OfExpr` (`ast.rs:222`) is `ty_atom`'s last resort — an arbitrary
  expression in type position.
- `crates/elab/src/lib.rs:1037-1040` calls `try_indexed_ty` *before* the
  generic decode path, with the comment "an indexed family applied to its
  index … delivered here by the parser's applied-type-is-never-called
  backtracking" (`parser.rs:717-741` does the rewind).
- `indexed.rs:188-221` `try_indexed_ty` then checks the argument against
  `Type::Nat` and calls `lower_indexed_instance`.

Generalizing that from *one* `Nat` index to *N* value parameters at declared
types is a handful of lines in the same function. Verified live that the
grammar is already there: `theorem use_p(n: Nat, h: P(n)): P(n) { h }` with
`fn P(n: Nat) -> Type { leb(n)(5) = True }` checks today.

### C.5 Construction — **medium**

`Converges(50, refl)` cannot recover `(p, env, ir, vs)` from its arguments in
general (they appear only inside the *type* of the second field). Options,
in the grain of what exists:

- **Checking position supplies them** — the record-literal path already does
  precisely this for type arguments (`lib.rs:1204-1210`: the braced literal
  is only taken when `tyargs` is empty and the expected type supplies the
  instantiation). Extend to value parameters and require a checking position.
- **Explicit spelling at the head** (`ctor_at`, `lib.rs:2690-2722`, and
  `inductive.rs:2170-2181` for indexed constructors, which reads the
  *declared* result index syntactically — not available here, since a
  parameter is not written per-constructor).

Recommend the first, with a diagnostic naming the second when inference has
nothing to go on. This is the one item with a real design decision in it.

### C.6 Destruction — **small**

Projection is `project_field` (`inductive.rs:1260-1305`), which walks the Σ
spine substituting each earlier projection into the tail (`:1301`) — the
mechanism that already makes `m.unit_l`'s dependent type come out right, and
that already works for a computed field type (§D). Match arm binders take
the same walk (`inductive.rs:1196-1245`). Both are indifferent to *where* the
type in the spine came from, so a substituted value parameter costs nothing
here. `let { n, h } = c;` (`lib.rs:623-656`) likewise.

### C.7 The classifier's parameters-vs-indices line — **small, but must be
drawn deliberately**

`inductive.rs:339-348` already rejects an indexed `record` with exactly the
right reason: *"an index varies per constructor result, and a record has one
constructor"*. And attempting the existential through the landed **indexed**
form is rejected too — verified:

```
inductive Small : (m: Nat) -> Type { Mk(m: Nat, n: Nat, h: leb(n)(m) = True) : Small(m) }
→ error: `Mk`'s result index `m` is not constructor-headed: a bare-variable index
  means the constructor targets *every* index … route 2b, not yet generated
```
(`inductive.rs:1511-1519`.)

That diagnostic is **the confirmation of the issue's feasibility claim**, and
it is worth stating sharply: a uniform result index that is a bare variable
in *every* constructor is not an index at all — it is a parameter, and it
lowers by substitution with **zero** of route 2b's machinery (no fording, no
stored equation, no `Wf` skeleton, no UIP, no `Id`-transport, no coherence
predicate). See §E of `issues/indexed-families.md`'s scope notes, which
already says so in one line ("a parameter is uniform across constructors and
lowers by substitution; an index varies per constructor result"). **Confirmed,
not refuted.** The one caveat: the *diagnostic above* currently pushes that
case toward fording, so the round should make sure a uniform bare-variable
index is recognized as a parameter (or, more simply, that the parameter form
is written as a parameter list and the diagnostic gains a "did you mean a
parameter?" arm).

### C.8 Effort summary

| item | site | effort |
|---|---|---|
| grammar `record R(p: T, …)` | `parser.rs:241-268`, `271-285`; reuse `ast::Param` (`ast.rs:174-190`) | small |
| AST split params/valparams | `ast.rs:44-62` + every `ind.params` zip | small (wide) |
| substitute values into field types | `inductive.rs:657-720`, `672-682`; mirror `TyVar`/`Alias` (`lib.rs:3225-3240`) | small |
| use-site `Converges(a,b,c,d)` in type position | `lib.rs:1037-1040` → `indexed.rs:188-221` | small |
| construction | `lib.rs:1204-1210`, `1345-1357`, `2690-2722` | **medium** (design decision) |
| projection / match / `let {}` | `inductive.rs:1260-1305`, `1196-1245`; `lib.rs:623-656` | small |
| classifier: parameter ≠ index | `inductive.rs:339-348`, `1511-1519` | small |
| kernel | — | **none** |

---

## D. Dependent fields at the surface today — **yes, including computed ones**

Verified with the release binary, ulimit-wrapped, scratchpad `dep_field.hthr`
→ `ok`:

```heather
inductive Bool { True, False }
fn leb(n: Nat) -> Nat -> Bool { … }          -- a real recursive fn
record Small { n: Nat, h: leb(n)(5) = True } -- field 2's type applies a fn to field 1
fn witness() -> Small { Small(3, refl) }
theorem use_it(s: Small): leb(s.n)(5) = True { s.h }
```

Declaration, construction (equation closed by conversion), and **projection
at a dependent field** all work. §B.2 repeats it with the real `eval`. So the
dependent-field gap is **not** part of route 1's bill: the mechanism is
`lower_ctor`'s push-before-next-field loop (`inductive.rs:688-691`) plus
`project_field`'s substitution of earlier projections (`inductive.rs:1301`),
both landed since the records round (`docs/surface-records.md` §4.3, §10.2).

Route 1 really is "just add value parameters".

One inherited restriction to name so it is not rediscovered: `inj` at a
dependent field is **diagnosed, not derived**
(`issues/dependent-field-injectivity.md`, `surface-records.md` §7). A
`Converges` record has a dependent field, so `inj` on it will hit that. No
consumer below needs it.

---

## E. Route 2 sizing — defer

A general `Sigma<A, B>` with `B : A -> Type<0>` needs a **type argument that
denotes a family**, and that is where it dies today. Measured:

- `record Sig<B> { w: Nat, h: B(w) }` **declares** — but only because
  `lower_ctor` runs at *instantiation*, so the declaration is never checked
  on its own. Instantiating it fails: `fn mk() -> Sig<P> { … }` →
  `error: unknown type `P``. Type arguments go through `elab_ty`
  (`inductive.rs:529-532`), and no `TyKind` denotes a function-valued family.
- `fn P(n: Nat) -> Type { leb(n)(5) = True }` **does** work now, and
  `P(n)` **does** work in type position (both verified). So the issue's line
  "a `fn` returning `Type<0>` cannot help" is **partly stale**: the *equation*
  body works; what still fails is `->` in an expression body
  (`fn Q(n: Nat) -> Type { Nat -> Nat }` → `parse error: expected `}`, found
  Arrow`), which is `issues/type-definitions`' scope. **Landed 2026-08-01**
  (`docs/types-as-expressions.md`): `->` and `(x: A) ->` are expressions, so
  that spelling now checks and the second half of this bullet is spent. Bill
  item (ii) below is paid; item (i) — passing a family as a *type argument* —
  is not.
- `theorem ex(F: Nat -> Type, n: Nat, h: F(n)): F(n) { h }` **works** — a
  family-valued *binder* in a statement is already fine.

So route 2's bill is: (i) a way to pass a family as a type argument (a `Ty`
form for it, or lifting `fn`-defined families into the type namespace), (ii)
`->` in expression position for `fn`-defined type families
(`issues/type-definitions`), and (iii) the deeper one — record/inductive
parameters are **monomorphized by substitution** by design
(`docs/surface-records.md` §1.1, `docs/surface-polymorphism.md` §3.1), so a
*genuinely* general Σ wants a parameter that is a kernel Π binder, not a
substitution. That is a different round and it overlaps
`issues/surface-polymorphism`. **Defer.** Route 1 subsumes every consumer
named today, and the ∃-closure relation between the two is the issue's own
observation (nothing re-proves when route 2 eventually lands).

---

## F. What the consumers would look like under route 1

### F.1 `converges` (`docs/ir-simulate-design.md` §6)

```heather
record Converges(p: Prog, env: Val, ir: Ir, vs: Val) {
    n: Nat,
    h: eval(n, p)(env, ir) = Out(vs),
}
```

Introduction, at a computed bound — the §6 discharge story verbatim, and
exactly `add_one_one_converges` in §B.2 with the parameters written:

```heather
fn add_one_one_conv() -> Converges(add_prog(), VCons(embed_nat(1), VCons(embed_nat(1), VNil)),
                                   add_body(), VCons(embed_nat(2), VNil))
{ Converges(50, refl) }
```

`fuel_monotone` becomes a *lemma about `Converges`* rather than about raw
fuel (`lib/ir_v1.hthr:780-788` is unchanged; this wraps it):

```heather
theorem conv_loosen(p: Prog, env: Val, ir: Ir, vs: Val, m: Nat,
                    c: Converges(p, env, ir, vs), hle: leb(c.n)(m) = True)
    : eval(m, p)(env, ir) = Out(vs)
{ fuel_monotone(p, env, ir, vs, c.n, m, c.h, hle) }
```

`refines` (`lib/ir_v1.hthr:789-805`) loses its fuel map:

```heather
theorem refines_trans(…): (env: Val) -> (vs: Val)
    -> Converges(p1, env, i1, vs) -> Converges(p3, env, i3, vs)
```

**Awkwardness, honestly:** `refines` still cannot be *named* — a `fn` body is
an expression and `->` is not one, so it stays a statement shape written out
at each use. That is `issues/type-definitions`, not this issue, and it does
not block anything. The good news is that the bound-carrying spelling
(`b1`, `b2` as `Nat -> Nat` parameters, and `refines_trans` as composition of
bounds) **disappears entirely**: composition becomes ordinary implication
chaining. The landed bounded proofs are the image of the ∃-form under the
∃-closure, so nothing there re-proves.

### F.2 The inversion lemma (`issues/match-with-equation.md`)

The wanted statement is
`k_bind(ev, env, rest, r) = Out(vs) -> exists ws. (r = Out(ws)) × …`
(`k_bind` at `lib/ir_v1.hthr:329-334`). Under route 1 that is an
**iterated** value-parameterized record — §B.1 test 8 is this shape,
prototyped and checked:

```heather
record BindInv(ev: Val -> Ir -> Res, env: Val, rest: Ir, r: Res, vs: Val) {
    ws: Val,
    hr: r = Out(ws),
    hk: ev(append(ws, env), rest) = Out(vs),
}

theorem k_bind_inv(ev: Val -> Ir -> Res, env: Val, rest: Ir, r: Res, vs: Val,
                   h: k_bind(ev, env, rest, r) = Out(vs))
    : BindInv(ev, env, rest, r, vs)
{ … }   -- proved once by the remember-idiom, then never again
```

Three notes, none of them blockers:

- **A record with more than two fields *is* the multi-witness Σ.** No nesting
  is needed at the surface — the Σ spine is right-nested internally
  (`inductive.rs:708-718`) and later fields' types mention earlier ones,
  which is the whole point. §B.1 test 8 checks the nested kernel shape;
  §D checks the surface shape.
- The second and third fields mention **both** the witness (`ws`) and outer
  parameters (`env`, `rest`, `vs`) — that is the `depth`/`shift` obligation
  of §B.1 test 9, and the only correctness-critical part of the generator.
- A **function-valued parameter** (`ev: Val -> Ir -> Res`) is fine as a
  parameter — `reject_function_fields` was corrected during the records round
  to key on self-occurrence rather than shape (`surface-records.md` §11.1) —
  but it *does* make the record's `inj` unusable and makes constructing a
  record equality need funext (`surface-records.md` §7). No consumer needs
  either.

Consuming it is a `let { ws, hr, hk } = k_bind_inv(…);` — the destructuring
`let` (`lib.rs:623-656`) at its best use yet, replacing four hand-rolled
convoy motives in `step_mono` and, per
`issues/ih-generalization`'s datum, the 18 s of the file's 27 s that those
motives cost.

---

## G. Levels

`Converges` lands at the Σ join of its field levels. `n: Nat` is level 0;
`h : eval(…) = Out(vs)` is `Id` at `Res`, level 0. Join = **0**, and the
generator already computes it rather than hardcoding it
(`inductive.rs:511-517` folds `fst_level ⊔ snd_level`;
`surface-records.md` §3 is the discipline, and `surface-universe.md`
confirmed the fold needed no change when a level-1 record arrived).
§B.1 test 2 pins both halves: the type checks at level 0 and is **rejected**
at level 1 (non-cumulativity).

Consequence for the consumers: the prelude's `sym`/`trans`
(`crates/elab/src/prelude.hthr:25-31`) are `theorem sym<A>(…)` with `A` a
`TyParam` defaulting to `Type<0>`, and `j` is used at level 0 throughout
`lib/ir_v1.hthr`. A level-0 `Converges` is therefore an ordinary `A` for all
of them, and §B.1 test 5 exercises `J` at exactly those levels
(`ty_level = motive_level = 0`) with an *open* motive family. No interaction.

The one level rule to keep: a value parameter contributes **no** level to the
record (it is a term, not a type) — the same asymmetry `Vec`/`Wf` have
(`DESIGN.md`: "the `Vec`/`Wf` branches bind one universe, not two — an arity
term contributes no level"). If a future value parameter were itself at a
universe (`p: Type`), that is the bundled-record case and the existing fold
handles it. Per `issues/indexed-families.md`'s 2026-07-30 lesson, the round's
suite must keep **one nonzero-level test** — a uniformly-level-0 suite cannot
see a dropped join.

---

## H. Risks and the fallback line

1. **No kernel change, therefore no metatheory round.** Stated loudly because
   the opposite would change the round's cost class: every term route 1 emits
   is a `Σ`/`Pair`/`Fst`/`Snd`/`Id`/`Refl`/`J` the tier-0 generator already
   emits, all v0 formers with landed rules. Same risk class as
   `docs/surface-records.md` §9. **No ch. 07 obligation.** If a design
   discussion starts reaching for a former, that is the signal that the round
   has drifted into route 2 or into indexed families, and it should stop.
2. **Indexed-families machinery must not sneak in.** The tell is any mention
   of a stored index equation, fording, `Wf` skeletons, UIP/Hedberg,
   `sEq`/`transp`, or `elim_Nat`-on-the-index. None of it is needed: a
   parameter is *substituted at lowering*, which is what `TyVar` already does.
   If a proposed design needs the family to be *recursive in* the parameter,
   it is an index and belongs to `issues/indexed-families.md`.
3. **The silent-capture hazard (§B.1 test 9) is the real correctness risk.**
   An un-shifted parameter under the Σ binder produces a well-formed but
   *wrong* — and typically trivially inhabited — proposition, and the kernel
   gate cannot catch it. Mitigation: the acceptance suite must include a test
   that the *open-parameter* record is **not** inhabited by a witness that
   inhabits the captured spelling, i.e. a negative control on the
   proposition, not only on the encoding. This is the single test most worth
   writing first.
4. **Construction inference (§C.5) is the one open design question.** It can
   be closed cheaply (checking position only) and the round should do so
   rather than build a unifier for parameters that appear only inside field
   types.
5. **Term size / conversion cost.** `Converges` at concrete IR arguments
   makes conversion run `eval` inside a *type*. §B.2 measured this as fine at
   the existing fixture scale, but the parameters are now duplicated into
   every field type at every use site. `issues/simulate-conversion-cost.md`
   and `docs/inductive-indexed-lowering.md` §10 (per-occurrence term size)
   are the places this would show up; worth one bench fixture, not worth
   blocking on.
6. **Fallback line.** If C.5 or C.3 turns out worse than sized, the
   computed-bound form already in `lib/ir_v1.hthr` keeps working unchanged
   and nothing regresses — the ∃-form is its image under the ∃-closure. The
   fallback is "do nothing", and it is cheap.

---

## Recommended plan for the implementing round

Scheme-before-prototype-before-generator, per the tier discipline. The
prototypes in §B are the "before" half and are already done.

1. **Doc** `docs/surface-value-parameters.md`: the grammar, the
   parameters-vs-indices rule (with `inductive.rs:1511-1519`'s diagnostic
   gaining a parameter arm), the substitution rule (`depth` + `shift_local`),
   and the construction decision from §C.5.
2. **Parser + AST** (§C.1, C.2) — `record R(p: T, …)` and `record R<A>(p: T)`,
   reusing `ast::Param`.
3. **Elaborator** (§C.3, C.4) — `ValParam` on `Cx` mirroring `TyVar`/`Alias`;
   generalize `try_indexed_ty`'s argument-checking loop to N declared
   parameter types.
4. **Construction + destruction** (§C.5, C.6) — checking-position only for
   the literal, with the diagnostic; projections and match need nothing.
5. **Acceptance** `crates/elab/tests/value_parameters.rs`, four-axis per
   `docs/testing-generated-terms.md`, plus the three tests this
   investigation says are load-bearing: the **capture** negative control
   (risk 3), one **nonzero-level** test (§G), and a **neutral-parameter**
   test (the parameter a theorem binder, not a literal).
6. **Consumers** — `Converges` in `lib/ir_v1.hthr` per §F.1, then
   `k_bind_inv` per §F.2, which is the payoff that retires four convoy
   motives in `step_mono`.
7. Then close `issues/surface-existential.md` for route 1 and leave route 2
   filed against `issues/surface-polymorphism` / `issues/type-definitions`.
