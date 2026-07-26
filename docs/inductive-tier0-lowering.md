# Tier-0 inductive lowering: the mechanical scheme

Status: implemented, 2026-07-24 — `crates/elab/src/inductive.rs` mechanizes
this document section by section, and `crates/elab/tests/inductive_tier0.rs`
is §9's checklist. Where the two disagree, the code is wrong; §3.3 and §6.2
below record the two places where writing the code corrected the scheme.
Tracking issue: `issues/inductive-compiler.md` (tier 0).

Tier 0 is the non-recursive tier: `Bool`, `Option`, records, and most IR
node shapes. Its lowering is plain sums-of-Σs, and it is entirely
mechanical — this document *is* the mechanism, written before the code
because of the tier's hazard class: a bug here does not produce a rejected
term, it produces a *checked proof about a type the user did not mean*.
The kernel cannot catch that. Review of this document is what catches it.

Conventions:

- `⟦T⟧` — lowering of a surface type to a kernel `Type`.
- `⌜T⌝` — the *code* of a kernel type: a `Term` with `El ⌜T⌝ ≡ T`.
- Kernel constructors are named as in `crates/kernel/src/term.rs`; field
  names are that file's field names.
- `Γ` is the ambient local context at the point of use.

---

## 1. What the kernel provides

Everything tier 0 needs already exists (`crates/kernel/src/term.rs`):

| Need | Kernel | Level |
|---|---|---|
| tags | `Type::Sum {lhs_level, rhs_level, lhs, rhs}`, `Term::Inl`/`Inr` | `l ⊔ l'` |
| fields | `Type::Sigma {fst_level, snd_level, fst, snd}`, `Term::Pair`/`Fst`/`Snd` | `l ⊔ l'` |
| nullary ctor | `Type::Unit`, `Term::Triv` | 0 |
| no ctors / absurdity | `Type::Empty`, `Term::ElimEmpty {level, motive, scrut}` | 0 |
| case analysis | `Term::Case {…, motive, motive_level, case_l, case_r, scrut}` | motive's |
| large elimination | `Case`'s `motive` is an arbitrary `Type`, so it may be `Type::Ty(l)` | |
| decoding | `Type::El {level, tm}` | |

Four kernel facts the scheme leans on, each verified in the source rather
than assumed:

1. **Σ has η** (`conv.rs:668`) — conversion at `Σ` compares `fst`/`snd`
   projections without inspecting either side. So a pair is definitionally
   its projections, and vice versa.
2. **`Unit` has η / proof irrelevance** (`conv.rs:696`) — any two terms of
   `Unit` are convertible. A `Unit` component costs nothing in equality.
3. **`+` is positive** — `Case` β-reduces on `Inl`/`Inr` and is neutral on
   a neutral scrutinee (`reduce.rs`), which is what makes `match` on an
   open scrutinee stuck rather than wrong.
4. **`El` decodes every extension code** (`reduce.rs:93–103`):
   `El ⌜Unit⌝ ⇝ Unit`, `El ⌜Empty⌝ ⇝ Empty`, likewise `Σ`, `+`, `Id`, `W`.
   This is what makes the large-elimination no-confusion argument fire
   *definitionally*.

Non-cumulativity is the one place the kernel constrains us; see §6.2, where
avoiding it turned out to be free.

---

## 2. Declaration form and well-formedness

```
inductive D<p₁, …, p_m> {
  c₁(f₁₁: T₁₁, …, f₁ₖ: T₁ₖ),
  …
  c_n(…),
}
```

Fields may depend on earlier fields of the *same* constructor and on the
parameters. Tier 0 admits `n ≥ 0` constructors and `k ≥ 0` fields.

**Parameters are monomorphized.** `p_i` are surface type parameters,
substituted through the scheme at each use site (the issue's "prenex,
substituted through"). There is no kernel-level abstraction over them:
`Option<Nat>` and `Option<Bool>` lower to two unrelated kernel types. This
is forced today — the surface has no first-class function values or types
(`issues/surface-operators.md` deferral), and it is consistent with the
`def`-is-inlined rule. When universe polymorphism lands (layer m only), a
`ΠΠ ℓ⃗`-abstracted encoding becomes possible; nothing here blocks it.

**Tier classification** runs before lowering:

- `D` does not occur in any `T_ij` → **tier 0** (this document).
- `D` occurs strictly positively and only finitarily → tier 1 (fording).
- `D` occurs under a `Π` (infinitary) or in an index → tier 2.
- `D` occurs negatively (left of a `→`) → **reject**, with the occurrence
  pointed at.

Tier 0's check is therefore just "no self-occurrence", but the *positivity*
check that decides between reject and tier 1/2 must be written now, since
misclassification is how a negative occurrence would sneak into a later
tier's generator. As implemented it is occurrence-only, which is complete
for today's surface: field types have no `→`, so no occurrence can be
negative, and every self-occurrence is reported as tier 1. The strict-
positivity refinement lands with function-typed fields.

**Type arguments** are inferred only from an argument whose field type *is*
a parameter (`Some(3)` gives `A := Nat`); anything deeper is unification,
which belongs to [[elab-unifier-completeness]]. A bare `None` is genuinely
ambiguous and asks for an annotation.

---

## 3. The type

Two spines: an outer sum over constructors, an inner Σ over fields.

### 3.1 Field spine

For constructor `c_i` with fields `(f₁: T₁, …, f_k: T_k)`:

```
⟦c_i⟧ = Σ(f₁ : ⟦T₁⟧). Σ(f₂ : ⟦T₂⟧). … Σ(f_k : ⟦T_k⟧). Unit
⟦c_i⟧ = Unit                                              when k = 0
```

**Unit-terminated, not bare-last.** The alternative (`… Σ(f_{k-1}). ⟦T_k⟧`,
no trailing `Unit`) saves one node per constructor but makes the field
offsets depend on the field count: the *last* field is reached by `snd`s
alone, every other by `snd`s then `fst`. Uniformity is worth more than a
node here — every downstream scheme (projection, no-confusion, tier-1
height computation, the future IR pretty-printer) indexes fields the same
way — and by kernel fact 2 the trailing `Unit` is invisible to conversion:
`pair a ⟨⟩` and `pair a' ⟨⟩` are convertible exactly when `a` and `a'` are.

Levels: `Σ` lives at `fst_level ⊔ snd_level`, so
`level(⟦c_i⟧) = level(T₁) ⊔ … ⊔ level(T_k) ⊔ 0`.

**Scoping, and the one place it is not free** (corrected 2026-07-26,
`issues/tyvar-scoping-in-lowered-fields.md`). The spine is built outside-in
and folded from the end, so entry `j`'s own type is already scoped in
`Γ` + entries `0..j` and needs no shifting — that is why a named field is in
scope in the types after it, and why the spine is a Σ at all.

The **type parameters** are the exception, and they are not entries. A
parameter's instantiation `⟦A⟧` is lowered in the ambient `Γ`, once, before
the spine exists; by the time it is *used* in field `j` the spine has pushed
the nominal tag (§3.3) and the `j` earlier fields on top of it. So every use
of a parameter is weakened by `1 + j`:

```
⟦A⟧ used in field j   ↦   ⟦A⟧ ↑^{1+j}
```

For a **closed** `⟦A⟧` — every instantiation the suite had for two years'
worth of tests: `Nat`, another monomorphic declaration — this is the
identity, which is exactly why a missing weakening was invisible. The
surface's one context-dependent type is `=`, whose endpoints are terms, and
at `Box2<A> { Mk(x : Nat, y : A) }` instantiated at `n = n` a missing
weakening re-points `n` at `x` and the encoding silently becomes `x = x`:
well-formed, checked, and not what was written. In the implementation this
is `Cx::tyvars` carrying a binding depth, the same device `Alias` uses.

### 3.2 Tag spine

Right-nested, with tails `R_i`:

```
R_n     = ⟦c_n⟧
R_i     = ⟦c_i⟧ +  R_{i+1}                (i < n)
⟦D⟧     = R₁
⟦D⟧     = Empty                            when n = 0
```

`n = 1` collapses to `⟦D⟧ = ⟦c₁⟧` — a single-constructor inductive is its
field record, no tag, which is the right answer for structs.

Levels: `level(⟦D⟧) = ⊔_i level(⟦c_i⟧)`.

### 3.3 The nominal tag (decided 2026-07-24)

Structurally identical declarations must not share a kernel type (§8.1), so
every constructor's field spine is prefixed with a per-declaration tag:

```
⟦c_i⟧ = Σ(_ : Tag_D). Σ(f₁ : ⟦T₁⟧). … Σ(f_k : ⟦T_k⟧). Unit
```

Field `j` therefore sits at `fst(snd^j x)` — one more `snd` than §5.1's
untagged count. `Bool` and a structurally identical `Direction` now have
distinct kernel types, and the kernel itself rejects `True = Left`.

**`Tag_D` must be proof-irrelevant, which rules out the obvious choice.**
The first attempt was `Id⁰(Nat; ⌜id_D⌝; ⌜id_D⌝)`, inhabited by `refl`. It
distinguishes declarations, and it typechecks every *non-dependent* use —
and then fails on the first dependent motive, which is exactly what tier 0
exists to support. In an arm for `c_i` the binder `x : ⟦c_i⟧` is neutral,
and the motive puts it back together as `inl x`; proving e.g.
`neg (neg b) = b` by `match b { True => refl, … }` requires `inl x` to be
convertible with the canonical `inl (pair tag ⟨⟩)`. Σ-η reduces that to
`fst x ≡ tag` — and `Id` has no η, so a neutral `fst x` is not convertible
with `refl`. The proof is rejected. (This is the same η obligation that
rules out a single tag at the top of the sum spine, one level up; the first
draft of this document caught it there and missed it here.)

So the tag is built from formers that *do* have η — `Unit` and `Σ`, both
proof-irrelevant in `conv.rs` — while still being structurally distinct per
declaration, since **type** conversion is structural and only **term**
conversion is η-driven. `Tag_D` is the binary representation of `id_D` as a
right-nested Σ: digit 0 is `Unit`, digit 1 is `Σ(Unit).Unit`, terminated by
`Unit`. Minimal binary representations are distinct as digit strings, so the
encoding is injective; the inhabitant is the matching nest of `⟨⟩`s, and
which inhabitant hardly matters, since any two are convertible.

Three consequences, all accepted:

- **Cost.** One Σ node per constructor plus `O(log id_D)` nodes for the tag
  itself, and one extra `snd` per field projection. Free in conversion: η
  means the tag component is never actually compared.
- **Placement is per-constructor, not per-type.** A single tag above the
  sum spine would make `match` case on `snd t`, whose motive obligation
  `t ≡ pair (fst t) (snd t)` is again η — fine for this `Tag_D`, but it
  buys nothing and complicates every motive, so the tag stays field 0.
- **Phantom parameters still collapse.** `Phantom<Nat>` and `Phantom<Bool>`
  for `inductive Phantom<A> { P }` share a kernel type, since no field
  mentions `A`. Tagging the *instantiation* as well as the declaration
  would fix it; not worth it until someone writes a phantom parameter.

`n = 0` is the exception: `⟦D⟧ = Empty` carries no tag (there is no
constructor to put it in), so two empty inductives do share a type. Nothing
observable follows — neither has an inhabitant to confuse.

Users never see any of this: the tag is not a field, has no surface name,
and is not bindable in a pattern.

---

## 4. Constructors

The injection path for constructor `i` of `n`:

```
ι_i(t) = inr(⟦c₁⟧; R₂; inr(⟦c₂⟧; R₃; … inl(⟦c_i⟧; R_{i+1}; t) …))     i < n
ι_n(t) = inr(⟦c₁⟧; R₂; … inr(⟦c_{n-1}⟧; R_n; t) …)                     i = n
ι_1(t) = t                                                             n = 1
```

i.e. `i-1` `Inr`s, then `Inl` unless this is the last constructor. Each
`Inr`/`Inl` at depth `j` carries `lhs = ⟦c_{j+1}⟧`, `rhs = R_{j+2}` and
their levels — the annotations are fully determined by the spine, so the
generator builds them in one downward pass.

The field tuple for `c_i(a₁, …, a_k)`, with `S_j` the Σ-tail after
substituting the arguments already consumed:

```
tup_k   = ⟨⟩
tup_{j} = pair(f_{j+1}: ⟦T_{j+1}⟧. S_{j+1}; a_{j+1}; tup_{j+1})
⟦c_i(a⃗)⟧ = ι_i(tup_0)
```

Both `Inl`/`Inr` and `Pair` are fully annotated in the kernel, so a
constructor application **synthesizes** — no checking-mode obligation is
introduced by the lowering, which preserves the elaborator's
checking-descent invariant (`issues/front-end-sugar.md`).

Constructors are *not* kernel functions. `Some` alone (unapplied) has no
lowering; it is a macro of arity `k`. Partial application is a surface-level
error until first-class functions exist. Same status as `Succ` today
(`crates/elab/src/lib.rs:759`).

---

## 5. Projection and `match`

### 5.1 Field projection

Inside the arm for `c_i`, the `Case` binder is `x : ⟦c_i⟧`. Define, with
`S_0 = ⟦c_i⟧` and each `S_{j-1} = Σ(f_j : A_j). B_j`:

```
q_0   = x
π_j   = fst(f_j: A_j. B_j; q_{j-1})
q_j   = snd(f_j: A_j. B_j; q_{j-1})
S_j   = B_j[π_j / f_j]
```

so `π_j = fst(snd^{j-1}(x))`, with every annotation determined by the
spine, and `π_j : A_j` where `A_j` already has the earlier fields' `π`s
substituted in. The arm body is elaborated in a context extended by `x`,
with the surface field names bound to `π_j` as *aliases* (the elaborator's
existing `Alias` mechanism, `crates/elab/src/lib.rs:1287`) — substituted,
not `let`-bound, since the kernel has no `let`.

**β check.** `case(inl(pair a₁ (pair a₂ ⟨⟩)))` reduces to
`body[π_j := fst(snd^{j-1}(pair a₁ (pair a₂ ⟨⟩)))]`, and each projection
β-reduces to `a_j`. So a `match` on a canonical constructor computes to the
arm body with the actual arguments, definitionally, with no η appeal
needed. On a neutral scrutinee the outer `Case` is neutral (kernel fact 3)
and nothing reduces. Both are the intended behaviour.

### 5.2 `match` as nested `Case`

Given scrutinee `t : ⟦D⟧`, motive `M` over `z : ⟦D⟧` at level `l''`, and
arm bodies `b_1 … b_n`:

```
case_at(j) =                                       -- scrutinee in R_j
  if j = n:  b_n[fields of x]                      -- no Case; x : ⟦c_n⟧ directly
  else:      Case {
               lhs: ⟦c_j⟧, rhs: R_{j+1},
               motive: M_j,  motive_level: l'',
               case_l: x. b_j[fields of x],
               case_r: y. case_at(j+1),
               scrut:  (the R_j-typed scrutinee),
             }
```

with the motives obtained by pushing injections into `M`:

```
M_1     = M                                        -- over z : R₁ = ⟦D⟧
M_{j+1} = M_j[ inr(⟦c_j⟧; R_{j+1}; z) / z ]        -- over z : R_{j+1}
```

The substitution is one binder deep over the same `Γ` in both directions,
so it is `embed(Γ, 1).extended(inr(…, Var 0))` with the elaborator's
existing helper (`crates/elab/src/lib.rs:1387`), not a general local
substitution.

`n = 0`: `match` on `Empty` is `ElimEmpty {level: l'', motive: M, scrut: t}`
with no arms — the absurd-pattern case, and the reason `Empty` is the
`n = 0` encoding rather than an error.

`n = 1`: no `Case` at all; the arm body with `x := t`.

**Exhaustiveness and order** are surface obligations, resolved before
lowering: arms are permuted into declaration order and a missing arm is a
surface error. The lowering itself is total on a complete arm list.

---

## 6. No-confusion

Two separate derived artifacts, because they have different side
conditions. Both are *generated terms checked by the kernel* — never
trusted, never primitive.

### 6.1 Disjointness (any levels)

For `i ≠ j`, from `e : Id(⟦D⟧; c_i(a⃗); c_j(b⃗))` derive anything.

The tag predicate ignores fields entirely, so it lands in `Ty 0`
regardless of the field levels:

```
tag_i = z. Case { motive: Ty 0, motive_level: 1,
                  … branches: TmUnit at constructor i, TmEmpty elsewhere … }
```

— a nested `Case` with the *same* spine as §5.2 and the constant motive
`Type::Ty(Level::Zero)` (this is the large elimination; the kernel permits
it because `Case`'s motive is an arbitrary `Type`). Then

```
absurd = J { ty: ⟦D⟧, lhs: c_i(a⃗),
             motive: (y p. El⁰ (tag_i y)), motive_level: 0,
             case: ⟨⟩,                       -- El⁰ (tag_i c_i(a⃗)) ⇝ Unit
             rhs: c_j(b⃗), proof: e }         -- : El⁰ (tag_i c_j(b⃗)) ⇝ Empty
```

and `ElimEmpty` from there to the user's goal. Both reductions are
definitional by kernel fact 4 composed with `Case` β, so the `case: ⟨⟩` is
accepted without any transport of our own.

### 6.2 Injectivity (non-dependent fields)

For `e : Id(⟦D⟧; c_i(a⃗); c_i(b⃗))`, derive `Id(⟦T_k⟧; a_k; b_k)` per field.

This needs a *total* function `⟦D⟧ → ⟦T_k⟧`, so the branches for the other
constructors need some inhabitant of `⟦T_k⟧`. The first version of this
document reached for `Unit` and a code-valued family; that works, but it
buys a large elimination and, with it, a level restriction (`⌜Unit⌝ : Ty 0`
against a field code at `Ty l`, under non-cumulative universes).

There is a cheaper default sitting right there: **`a_k` itself**. The lemma
is derived at a specific pair of terms, so the left-hand side's own field
value inhabits exactly the type the other branches need, and the motive
stays *constant*:

```
proj = z. Case { motive: ⟦T_k⟧; … : π_k(x) at constructor i, a_k elsewhere }
```

then `J` with motive `(y p. Id(⟦T_k⟧; a_k; proj y))` and `case : refl` gives
`Id(⟦T_k⟧; a_k; proj c_i(b⃗))`, which reduces to `Id(⟦T_k⟧; a_k; b_k)`. No
codes, no `El`, no large elimination — and so no level restriction at all.

**Side condition: `⟦T_k⟧` must not depend on the constructor's earlier
fields.** The constant motive is what makes this work, and a dependent field
type (`Mk(n: Nat, p: n = n)`, field 1) is not constant in `z`. The generator
checks it — by reading the field type off *both* sides' encodings and
comparing them with kernel conversion — and reports the limitation rather
than emitting an ill-typed term. Field 0 of such a constructor is still
injective; only the dependent field is out of reach. Recovering it wants
either the code-valued family above (with its level restriction) or a
transport along the earlier field's equation.

*Update 2026-07-26.* This restriction now has a second instance — a
**container field**'s type `[D; len]` depends on the length field before it
(`docs/container-fields.md` §9.2), and unlike a dependent payload field that
is the *normal* case rather than an unusual one. Tracked for a shared fix as
`issues/dependent-field-injectivity.md`, which also records why the transport
route raises a design question (`inj` would state a heterogeneous equation).

### 6.3 What is emitted, and when

Disjointness and injectivity are not pre-generated lemmas but two surface
forms, elaborated where they are used:

- `absurd(p)` — checking-only (the goal is what it eliminates into), from an
  equation between two *different* constructors.
- `inj(p)` / `inj(k, p)` — the `k`-th field equation (`k` a literal,
  defaulting to 0), from an equation between the *same* constructor.

Both elaborate to ordinary terms that the kernel re-checks, so nothing is
cached and nothing is trusted; and both give way to any user binding of the
name, so neither is a keyword. Method syntax comes free from the existing
desugaring: `p.absurd()`, `p.inj(1)`.

---

## 7. Worked examples

The nominal tag of §3.3 is **elided throughout this section** — every
`⟦c_i⟧` below really begins `Σ(_ : Tag_D).`, and every constructor really
begins `pair(tag, …)`. Everything else is verbatim.

**`inductive Bool { True, False }`**

```
⟦Bool⟧  = Unit + Unit
⟦True⟧  = inl(Unit; Unit; ⟨⟩)
⟦False⟧ = inr(Unit; Unit; ⟨⟩)
match b { True => u, False => v }
        = case(z. M; Unit; Unit; x. u; y. v; ⟦b⟧)
```

Note `x`, `y` unused — nullary constructors bind a `Unit` the arm ignores.

**`inductive Option<A> { None, Some(A) }` at `A = Nat`**

```
⟦Option<Nat>⟧ = Unit + Σ(a : Nat). Unit
⟦None⟧        = inl(Unit; Σ(a:Nat).Unit; ⟨⟩)
⟦Some(t)⟧     = inr(Unit; Σ(a:Nat).Unit; pair(a:Nat. Unit; t; ⟨⟩))
match o { None => u, Some(a) => v(a) }
              = case(z. M; Unit; Σ(a:Nat).Unit;
                     x. u;
                     y. v[fst(a:Nat. Unit; y) / a];
                     ⟦o⟧)
```

and `match Some(3) { … } ⇝ v[fst(pair 3 ⟨⟩)/a] ⇝ v[3/a]`.

Disjointness `Some(t) = None → C`: `tag_Some = z. case(z; Unit; Σ…; _. TmEmpty; _. TmUnit)`,
`J` at `El⁰(tag_Some ·)` with `case = ⟨⟩`, then `ElimEmpty`.

**`inductive Three { A, B, C }`** — the right-nesting and the last-arm
special case:

```
⟦Three⟧ = Unit + (Unit + Unit)
⟦A⟧ = inl(…; ⟨⟩)      ⟦B⟧ = inr(…; inl(…; ⟨⟩))      ⟦C⟧ = inr(…; inr(…; ⟨⟩))
match t { A => a, B => b, C => c }
  = case(z. M; Unit; Unit+Unit; x. a;
         y. case(z. M[inr(Unit; Unit+Unit; z)/z]; Unit; Unit; x. b; y. c; y);
         ⟦t⟧)
```

The inner motive is where a lowering bug would hide: it must be `M`
*composed with the injection*, not `M` itself, or the arm bodies would be
checked against the wrong family. This is the first thing the tests pin.

---

## 8. Open decisions

1. **Nominal collapse — DECIDED 2026-07-24: tag (option b), see §3.3.**
   Structurally
   identical declarations lower to the *same* kernel type: `Bool` and
   `inductive Direction { Left, Right }` are both `Unit + Unit`, and `True`
   and `Left` are the same term. The elaborator compares kernel types
   (checking is ultimately the kernel's structural conversion), so
   `theorem t: True = Left { refl }` would be **accepted**. That is exactly
   the tier's hazard class — a checked theorem about a type the user did
   not mean — even though it is not a soundness problem.
   Options: (a) accept it and document Heather's inductives as structural;
   (b) §3.3's per-declaration `Id⁰(Nat; ⌜id_D⌝; ⌜id_D⌝)` tag, which makes
   the kernel itself reject the confusion, at one extra Σ node per
   constructor, one `refl` per construction, and one `snd` per projection;
   (c) a nominal surface-type layer in the elaborator, parallel to the
   kernel types — the principled fix, and much the largest.
   Chosen: **(b)**, the per-constructor tag — cheap, mechanical,
   kernel-enforced, invisible to users, and revisitable, since it is a
   single prefix in one scheme. Written up as §3.3; §5.1's projection index
   shifts by one accordingly.
2. **Dependent-field injectivity** (§6.2) — a field whose type mentions an
   earlier field of the same constructor is diagnosed, not derived. (This
   replaces the level-0 restriction the first draft carried: the constant
   motive removed it entirely.)
3. **Interaction with tier 1.** The tag/field spine here is meant to be
   reused verbatim under tier 1's exact-height fording — the height is
   computed per constructor from the field spine. Tier 1 should not need to
   restructure §3; if it does, that is a signal to revisit before writing
   the tier-1 generator.

---

## 9. Acceptance checklist

The properties the implementation must exhibit, each a test in
`crates/elab/tests/inductive_tier0.rs`. All pass as of 2026-07-24, with the
two documented exclusions (dependent-field injectivity, §6.2; tier-1
declarations, §2).

1. Every generated declaration's type, each constructor, and each derived
   lemma passes the real kernel check (the elaborator's
   soundness-by-construction property).
2. `match` on each canonical constructor β-reduces to the corresponding arm
   body with the actual field arguments — checked by kernel conversion
   against the hand-written expected term, per constructor arity 0/1/2.
3. `match` on a variable scrutinee is neutral and the whole `match` still
   typechecks against a dependent motive (the nested-motive composition
   from §5.2 — the `Three` example, with a motive that genuinely varies per
   constructor).
4. Disjointness fires: `Some(t) = None → C` is provable for every ordered
   pair `i ≠ j`, including the last-constructor path.
5. Injectivity fires: `Some(a) = Some(b) → a = b`, and for a 2-field
   constructor, per field, including a field whose type depends on an
   earlier field.
6. `n = 0` (`Empty`) and `n = 1` (record) special cases both round-trip.
7. Negative test: a negative occurrence is rejected with the occurrence
   located; a tier-1 shape is *classified* as tier 1, not silently lowered.
8. Under decision 8.1(b): `True = Left` across two structurally identical
   declarations is rejected.
