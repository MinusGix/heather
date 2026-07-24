# Surface syntax sketches, round 0

Purpose: concrete programs in the proposed surface (issues/surface-syntax.md)
to judge style and practicality before committing. Nothing here parses;
every sketch is elaboration-honest (each form has a known lowering into the
kernel core). `❓` marks a genuinely open choice; commentary follows each
sketch.

Conventions used throughout: `fn` for computing definitions (inlined at
elaboration), `theorem` for opaque Ψ-global proofs; `==` for `Id` with the
type inferred; numeral literals for `Nat`; `Type` with levels inferred;
last expression of a block is its value.

## 1. Warm-up: Nat, induction, calc

```heather
fn add(m: Nat, n: Nat) -> Nat {
    rec m {
        Zero => n,
        Succ(_, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) == n {
    induction n {
        Zero => refl,
        Succ(m, ih) => cong(Succ, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) == Succ(add(m, n)) {
    induction m {
        Zero => refl,
        Succ(m2, ih) => cong(Succ, ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) == add(n, m) {
    induction m {
        Zero => sym(add_zero(n)),
        Succ(m2, ih) => calc {
            add(Succ(m2), n)
                == Succ(add(m2, n))  by refl,
                == Succ(add(n, m2))  by cong(Succ, ih),
                == add(n, Succ(m2))  by sym(add_succ(n, m2)),
        },
    }
}
```

Notes:

- `rec m { … }` with the motive omitted (constant motive inferred from the
  checking type) covers the common case; the full `rec m as z -> M { … }`
  stays available. `induction` is the same form with a propositional
  motive — it reads as intended.
- `Succ(_, ih)` in `rec`: the predecessor is bound (here ignored) and the
  ih rides in the pattern. Reads well; no goal state to imagine.
- ❓ `calc` step syntax: `by proof` trailing each step, continuation lines
  starting with `==`. Alternative: Lean's `_ == rhs := proof`. The `by`
  spelling reads better but overloads a keyword that tactics might want
  later.
- Verdict: this tier is unproblematic. Rust-flavor survives contact with
  induction.

## 2. Holes and deferred obligations (multiple goals, for code too)

```heather
fn lookup(xs: List(Nat), i: Nat, bound: lt(i, len(xs))) -> Nat { … }

fn third_plus_first(xs: List(Nat), long: lt(2, len(xs))) -> Nat {
    let a = lookup(xs, 0, ?first_ok);
    let b = lookup(xs, 2, ?third_ok);
    add(a, b)
} where {
    ?third_ok => long,
    ?first_ok => lt_trans(lt_0_2, long),
}
```

Notes:

- `?name` is a named hole; the `where { … }` block discharges them after
  the main flow. This is the Lean multiple-goal idea, but for *programs*:
  proof arguments stop interrupting the code path.
- The deep alignment: a named hole is **literally the elaborator's own
  metavariable** — a fresh Ψ-global `u : Trm(Γ ⊢ T @ l)` capturing the
  local context at the hole (issues/elaborator-design.md). The `where`
  block just solves it. Multiple goals aren't a tactic-framework feature
  here; they're the substitution calculus. The hole's context capture is
  what makes `long` visible inside the `?third_ok` discharge.
- Same mechanism inside proofs: `have h: P = ?later;` postpones a lemma.
- ❓ Should an *unnamed* `?` be allowed (auto-named, listed by the checker
  like Lean's goals)? Probably yes, but names keep the where-block
  readable.
- Verdict: strong keep. This is the multiple-goal setup done structurally
  — obligations are named and discharged in one visible place, not left in
  a mutable goal stack.

## 3. Inductives

```heather
inductive Option(A: Type) {          // tier 0: sums-of-Σs
    None,
    Some(value: A),
}

inductive List(A: Type) {            // tier 1: exact-height fording
    Nil,
    Cons(head: A, tail: List(A)),
}

fn sum(xs: List(Nat)) -> Nat {
    rec xs {
        Nil => 0,
        Cons(x, _, ih) => add(x, ih),
    }
}
```

Notes:

- Named fields in declarations (Rust struct-ish), positional in patterns.
  ❓ Allow `Cons { head, tail: ih }`-style field patterns too?
- `Cons(x, _, ih)`: fields then ih, mirroring `Succ(_, ih)`. With multiple
  recursive fields there is one ih per recursive field, in field order.
- Verdict: fine. The interesting part is the lowering
  (issues/inductive-compiler.md), which the surface deliberately hides.

## 4. Staged code: the `$` family under load

The classic staged power function, three spellings of the same body.

```heather
// (a) fully explicit: letbox discipline visible
fn pow_code(g: Ctx, n: Nat, x: Code(g |- Nat)) -> Code(g |- Nat) {
    rec n {
        Zero => code { 1 },
        Succ(_, ih) => {
            let code xi = x;
            let code r  = ih;
            code { mul($xi, $r) }
        },
    }
}

// (b) ${expr} ANF-hoisting sugar
        Succ(_, ih) => code { mul(${x}, ${ih}) },

// (c) proposed collapse: $ident auto-hoists any Code-typed variable
        Succ(_, ih) => code { mul($x, $ih) },
```

Notes:

- (a) is what the kernel sees (meta-ANF, letbox); nobody wants to write it.
- (b) works but `${x}` for a *plain variable* is ceremony; in practice
  nearly every splice is a variable.
- (c) is the ergonomic sweet spot: `$ident` where `ident` is any
  Code-typed variable in scope means "hoist a letbox for it above this
  quote". `${expr}` stays for genuine compound expressions
  (`${pow_code(g, k, x)}`), which are rare once you name things.
  Under (c), `$u` for an already-letbox-bound code variable and `$x` for a
  meta-level `Code` variable *look identical* — deliberately: the
  distinction is elaboration bookkeeping, not meaning.
- Verdict: adopt (c); keep (b) as the general case it degenerates from.
  The "weirdness" of `${…}` mostly evaporates because it becomes rare.

## 5. Open code and the "function call" question

Code with a free variable, and instantiating it — the `Code(Δ |- T)`
application question.

```heather
// body is code over an extended context: x free in it
fn let_inline(
    g: Ctx,
    body: Code(g, x: Nat |- Nat),
    arg:  Code(g |- Nat),
) -> Code(g |- Nat) {
    code { $body[x := $arg] }
}
```

Notes:

- `$body[x := $arg]` is the surface form of the kernel's delayed
  substitution `u^(id, t/x)` — the "special function calling". It **must**
  be special syntax: it is substitution, not β — there is no function
  object, and no `Code`-typed term can provide this operation as a method,
  because it changes the *context index* of the type
  (`Code(g, x:Nat |- Nat)` → `Code(g |- Nat)`).
- ❓ Positional shorthand `$body($arg)`? It's closer to the kernel's
  positional δ, but it *looks like a call*, and the whole point of
  intensionality is that code application ≠ function application. Lean/2LTT
  precedent aside, recommendation: named `[x := …]` only, at least until
  the sketches say otherwise. Cost: surface names for Δ-entries must be
  stable (they're display-only in the kernel — the elaborator owns the
  name↔index map).
- On the Box-wrapper instinct (user, 2026-07-23): endorsed, and it's
  exactly the Rust `Box` precedent — `Code(Δ |- T)` is an ordinary-looking
  type that ordinary code passes around, stores in structs, returns; the
  *magic* is confined to three intros/elims (`code {}`, `$`, `let code`),
  the way Rust once confined `box x`. Everything else about `Code` values
  is non-magic: they're just terms of a (contextual) type at universe 0.
  Practical consequence: library functions over `Code` (like `let_inline`,
  `pow_code`) are ordinary `fn`s — the wrapper framing is already true.

## 6. `match code`: intensional analysis, and the default-arm question

A weak-head constant test over closed Nat code:

```heather
fn is_zero_code(e: Code(· |- Nat)) -> Bool {
    match code e {
        Zero => true,
        _    => false,
    }
}
```

A transformation — replace variable 0, i.e. capture-aware substitution done
intensionally (toy; the real recursor telescope is wider):

```heather
fn count_succs(e: Code(· |- Nat)) -> Nat {
    match code e {
        Zero          => 0,
        Succ($n, ih)  => add(1, ih),
        _(other)      => 0,        // ❓ see note
    }
}
```

Notes:

- The kernel recursor has **no default arm** — 37 fixed branches,
  exhaustiveness structural. A surface `_` arm is sugar that mechanically
  fills every unlisted branch. Two flavors needed:
  - `_ => expr` for constant motives (fill all branches with `expr`,
    binding nothing) — cheap, shown above;
  - `_(rebuild) => …` for transformation passes, where `rebuild` is the
    identity-reconstruction of that node with recursive results plugged
    in. This is exactly the kernel's `identity_branches` machinery
    (already implemented and tested, twice) surfaced as sugar — a
    transformation pass then writes only the arms it cares about.
- `Succ($n, ih)`: `$n` binds the sub-*code*, `ih` the recursive result.
  Splice-patterns in binding position mirror splice-expressions in quote
  position; pleasingly symmetric.
- Layer honesty: `match code` is layer-m machinery; `fn`s that use it are
  meta-functions. ❓ Is the layer inferred from use (a fn touching
  `Ctx`/`match code` is layer m) or declared (`meta fn`)? Sketches lean
  inferred; an explicit `meta fn` might be worth it purely as
  documentation.
- Verdict: the flagship holds up. The default-arm sugar is the difference
  between usable and punishing (37 arms), and its lowering is *already
  built* in the kernel test infrastructure.

## 7. Teaser: where this is all headed

```heather
inductive Instr { Push(n: Nat), Add }              // tier 0 + tier 1 List

fn simulate(prog: List(Instr), stack: List(Nat)) -> Option(Nat) { … }

instance Compile[Cpu] for add {
    fn ir() -> List(Instr) { … }
    theorem equiv(m: Nat, n: Nat):
        simulate(ir(), [m, n]) == Some(add(m, n)) { … }
}
```

Not designed here (issues/ir-simulate-design.md, compile-typeclass-design)
— included only to check the register: the certifying-compilation
deliverable reads as ordinary Rust-flavored code with one theorem in the
instance. It does.

## Findings

1. **Adopt `$ident` auto-hoist** (sketch 4c); `${expr}` for compounds only.
   The `$`-family stops feeling weird the moment plain variables don't
   need braces.
2. **Delayed substitution is `$u[x := t]`, not `$u(t)`** — it must be
   special (it re-indexes the context; no method can do that), and it must
   not *look like* a call, because it isn't one (sketch 5).
3. **`Code` as an ordinary type with three magic forms** — the Rust-Box
   framing is accurate, not just an analogy (sketch 5).
4. **Holes + `where`-discharge give Lean-style multiple goals for free**,
   because holes are the elaborator's Ψ-metas; obligations become named
   and structurally discharged, in programs and proofs alike (sketch 2).
5. **`match code` needs the two default-arm forms**, and their lowering
   already exists as `identity_branches` (sketch 6).
6. Open: `calc` step spelling, positional-substitution shorthand, unnamed
   holes, field patterns, layer inference vs `meta fn` (❓ marks above).
