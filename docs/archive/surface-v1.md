# Surface syntax sketches, round 1

Revisions after review of round 0 (docs/sketches/surface-v0.md@4acf2fe). Decisions
taken this round are marked ✔; still-open choices ❓. The big movements:
real operator/method syntax everywhere; match/induction/rec unified via
recursive theorems; `where` replaced by in-block `on` discharge; implicit
quotation ("contaminate style") explored against explicit `code {}`.

## 1. Real syntax, unified match, `:=` calc

✔ Operators and method calls are used freely (`+`, `<`, `xs.len()`,
`p.sym()`); they ride the trait mechanism (§6). Note: because type
application is parenthesized (`List(Nat)`, not `List<Nat>`), `<` is
unambiguously comparison — `bound: i < xs.len()` parses without braces;
`{…}` grouping stays available but is not required.

✔ **match is the only eliminator form.** The unification: a theorem proved
by induction is just a *structurally recursive function* — the induction
hypothesis is a recursive self-call. `induction`, `rec`, and `match`
collapse into one construct; the elaborator compiles structurally-guarded
self-calls into the kernel recursor (the same termination analysis
recursive `fn`s need anyway). Proof mode and function mode become
*literally* the same language:

```heather
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),        // self-call, not ih
    }
}

theorem add_zero(n: Nat): n + 0 == n {
    match n {
        Zero => refl,
        Succ(k) => add_zero(k).cong(Succ), // IH = recursive call to the theorem
    }
}

theorem add_comm(m: Nat, n: Nat): m + n == n + m {
    match m {
        Zero => add_zero(n).sym(),
        Succ(k) => calc {
            Succ(k) + n
                == Succ(k + n) := refl,
                == Succ(n + k) := add_comm(k, n).cong(Succ),
                == n + Succ(k) := add_succ(n, k).sym(),
        },
    }
}
```

- ✔ calc steps discharge with `:= expr` (round-0 `by` dropped — there is
  no proof "mode"; every proof position is an ordinary expression
  position, `refl` is just a value).
- Explicit ih-binding (`Succ(k, ih) =>`) survives only as a low-level
  fallback (elaborator stage 1, before the termination checker exists;
  and for non-structural recursor tricks). Expected to disappear from
  normal code.
- The lowering is identical either way: kernel `elim_Nat`/`case`/`elim_W`
  chosen by whether (and how) the ih is used. Weak unification at the
  kernel, strong unification at the surface.

## 2. Goal-oriented blocks: `on`, not `where`

✔ Obligations are discharged *inside* the same block — they are part of
the same thing. Named, order-free:

```heather
fn third_plus_first(xs: List(Nat), long: 2 < xs.len()) -> Nat {
    let a = xs.get(0, ?first);
    let b = xs.get(2, ?third);
    a + b
    on ?third := long;
    on ?first := lt_0_2.trans(long);
}
```

- ✔ Auto-holes: `xs[i]` is sugar for `xs.get(i, ?_)` — an implicit proof
  parameter marked auto-defer becomes an anonymous goal at the call site
  (Lean-autoparam-shaped, but the goal is a first-class Ψ-meta, listed by
  the checker like any other).
- ❓ Positional discharge (bare `return long;` filling "the next goal") is
  **recommended against**: order-dependent filling is exactly the
  goal-stack brittleness the tactic critique was about. Names (or
  constructor names, below) keep discharge structural. Anonymous `?_`
  goals get checker-assigned names you can still refer to.
- `return` vs last-expression: ❓ lean Rust (last expression; `return` for
  early exit), nothing deep here.

Case-splitting as a *statement*, per the review sketch — with a scoping
caveat:

```heather
fn add(m: Nat, n: Nat) -> Nat {
    split m;
    on Zero    := n;
    on Succ(k) := Succ(add(k, n));
}
```

- `split m` replaces the current goal with one named goal per constructor;
  `on Ctor(fields) := expr` discharges by name. This is tactic `cases`
  with structurally named, order-free goals — the good version.
- Caveat (why expression-`match` stays primary): `on` arms are *leaves*.
  If computation must continue after the split (a join point), the
  continuation is the motive, and that is what expression-`match` already
  is. `split`/`on` is for when the split is the last act of the block —
  common in proofs, occasional in code.
- Speculative (recorded, not designed): goal *merging* — e.g. several
  `Result(_, E)` obligations collapsing into one `E`-handler goal —
  "goal-oriented error handling". Interesting emergent direction; needs
  its own sketch round once holes exist.

## 3. Fields, impls, namespacing

✔ Named constructor fields are Just a Thing (they are projection sugar
over the same Σ-encodings — tuple-ish and struct-ish declarations are the
same Sort of Thing). ✔ `impl` blocks Rust-style, plus out-of-block
namespaced definitions (`fn List(T).sum(xs: List(T)) -> …`) — method-call
syntax resolves through the type's namespace either way. Uncontroversial;
adopted for all sketches.

## 4. Implicit quotation ("contaminate style") vs `code {}`

The principled observation: kernel `box` is *checking-only* — the expected
type already announces code-ness. So quotation can be implicit exactly
where the kernel itself needs no annotation: **in checking position
against a `Code(Δ |- T)` type, a bare expression is a quote; splices mark
the meta-level parts.** `code {}` remains required in inference position
(same place the kernel demands letbox-or-annotation), and as an
explicitness escape hatch.

Round-0 sketch 4, both spellings:

```heather
// explicit blocks (round 0)
fn pow_code(g: Ctx, n: Nat, x: Code(g |- Nat)) -> Code(g |- Nat) {
    match n {
        Zero => code { 1 },
        Succ(k) => code { $x * ${pow_code(g, k, x)} },
    }
}

// implicit: arm bodies check against Code(g |- Nat), so they ARE quotes
fn pow_code(g: Ctx, n: Nat, x: Code(g |- Nat)) -> Code(g |- Nat) {
    match n {
        Zero => 1,
        Succ(k) => $x * ${pow_code(g, k, x)},
    }
}
```

- What it buys: staged code reads as *actual code*, not macro output —
  the review's point about lingering macro mentality. `let_inline`'s body
  becomes bare `$body[x := $arg]`.
- What it costs: stage boundaries become invisible when a quote contains
  no splices (`Zero => 1` — is `1` a Nat or code-of-1? only the type
  says). Scope errors (using a meta variable unspliced inside a quote,
  or a Δ-name outside one) are still *errors* either way — implicitness
  moves where they're reported, not whether they're caught. The
  contextual typing is the guardrail.
- ❓ The genuine test is **nested staging** (code-producing-code,
  `Code(g |- Code(...))`-adjacent patterns and quotes inside `match code`
  arms): if implicit quotes stay readable there, adopt implicit-by-
  checking as default; if not, implicit only at "depth 1". Needs a round-2
  sketch with a two-stage example before deciding.
- Non-negotiable either way: `$` stays explicit. Splices are the semantic
  events (letbox hoisting, delayed substitution); hiding *them* would hide
  meaning, not ceremony.

## 5. "Runtime code" for lower layers — deep embeddings at the boundary

Round-0 §6 asked how non-meta code can work with syntax if `match code` is
layer-m. The answer needs no kernel additions, because it is the
certifying compiler's own pattern: the "runtime version" of code is an
ordinary **tier-0/1 inductive AST** — a deep embedding — which any layer
matches on freely. Genuine `Code` (□) appears only at the reify/reflect
boundary, which is where layer m genuinely is:

```heather
inductive NatExpr {                      // ordinary data; layer p matches freely
    Lit(n: Nat),
    Add(l: NatExpr, r: NatExpr),
}

fn eval(e: NatExpr) -> Nat { … }         // ordinary recursion

fn reify(e: NatExpr) -> Code(· |- Nat) { // meta: build real code from data
    match e {
        Lit(n)    => ${nat_literal(n)},
        Add(l, r) => ${reify(l)} + ${reify(r)},
    }
}

fn reflect(e: Code(· |- Nat)) -> Option(NatExpr) {  // meta: match code at the boundary
    match code e { … }
}
```

The Church/visitor-callback variant from the review is exactly the Church
encoding of `NatExpr` — real inductives make it unnecessary. The IR is
precisely such a datatype, so this pattern is not an extra feature: it is
issues/ir-simulate-design.md's architecture stated small. Caveat worth
recording: `reflect` on *higher-order* fragments (code with binders →
data) needs a binder representation in the AST (de Bruijn as data);
first-order fragments — the IR case — are untouched by this.

## 6. Traits/typeclasses (direction note, not a design)

For operator syntax the mechanism barely matters; the real question is
resolution policy, and the key structural fact is that in this language
**dictionaries are first-class ordinary values** (records over Σ) — trait
vs typeclass is purely a question of *implicit resolution policy*, not
semantics. Leaning: **coherent by default** (Rust-style uniqueness per
(type, trait)) because certifying compilation wants canonical instances —
[[compile-typeclass-design]] already keys `Compile` instances
intensionally and wants determinism — with explicit dictionary values as
the escape hatch where mathematics wants multiple structures on one
carrier (`Nat` under `+` vs under `max`: named instances passed
explicitly, no incoherence). To be designed properly in
issues/compile-typeclass-design.md; recorded here so operator sugar
doesn't accidentally pre-commit the policy.

## Findings

1. ✔ Strong surface unification of match/rec/induction via **recursive
   theorems** — the IH is a self-call; proof mode and function mode are
   the same language, which was the design's stated ideal all along.
2. ✔ `:=` for calc steps and `on ?name := expr` discharge; no `by`, no
   proof mode, no `where` block — obligations live in the block they
   belong to.
3. ✔ `split`/`on Ctor := …` gives structurally-named multiple goals;
   expression-`match` remains primary because `on` arms are leaves (join
   points are motives).
4. Implicit quotation by checking type is principled (it is exactly where
   kernel `box` needs no annotation) and reads beautifully; decision
   deferred to a nested-staging sketch round. `$` never becomes implicit.
5. "Runtime code" = deep-embedding ASTs + reify/reflect meta-functions at
   the layer boundary; zero kernel additions; it is the IR pattern in
   miniature.
6. Traits: coherent-by-default + first-class dictionaries as escape;
   full design deferred to compile-typeclass-design.
