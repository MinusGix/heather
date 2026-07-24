# Surface syntax sketches, round 3

From round-2 review: context-specific compilation, goal-seeing programs,
and the pow/specialize_pow distinction sharpened. The headline: threads 1
and 3 converge — context-specific compilation *is* certified
specialization applied at instance level.

## 1. Context-specific function compilation as a feature

Two candidate mechanisms from the review — smart *resolution* (inference
picks a different instance based on context) vs smart *instance* (the
instance itself consumes context). ✔ Recommend the latter, keeping
resolution dumb and coherent (rounds 1–2): one instance, parametric over
a context descriptor.

```heather
instance Compile[Cpu] for lookup {
    fn ir(ctx: CallCtx) -> FunctionIR {
        match ctx.fact_about(arg(1)) {      // e.g. "index is the literal 0"
            Some(KnownConst(i)) => unrolled_ir(i),
            None                => generic_ir(),
        }
    }
    theorem equiv(ctx: CallCtx, args: …):   // ∀ ctx — proven ONCE
        simulate(ir(ctx), args) == lookup(args) { … }
}
```

Why this factoring wins:

- **Prove the generator, not the copies.** `equiv` quantifies over `ctx`,
  so every specialized emission is certified by the one theorem — no
  per-copy proof obligations. This is [[certifying-generator]]'s
  prove-once shape appearing at instance granularity.
- **Deduplication is keying, not cleverness.** Compiled artifacts are
  keyed on `(function syntax, ctx descriptor)` — instances are already
  intensionally keyed, this extends the key. Three dozen call sites with
  the same descriptor share one compilation. The design lever is keeping
  `CallCtx` *coarse*: a small lattice of facts (known-constant args,
  range/alignment facts), so keys collide often. Descriptor design is an
  ir-simulate-design-adjacent question, recorded there.
- **Context facts can be *proofs*.** The caller's in-scope evidence
  (`long: 2 < xs.len()`) can ride the descriptor, so `ir(ctx)` may e.g.
  elide a bounds check *justified by a theorem in ctx*, not a heuristic.
  Optimization guards become propositions. This is the thesis —
  compilation and optimization as user-level, provable logic — in its
  most concrete form yet.

Resolution-from-main composes: the walk from `main` resolves the
instance *and* computes each site's descriptor; `let instance` overrides
still apply lexically.

## 2. Programs that see the goal

The enabling fact (from elaborator-design): a goal *is already code* —
a hole is `u : Trm(Γ ⊢ P)`, and its statement is contextual type code,
`□(Γ ⊢ Ty l)` — DeLaM's `Typ`-bindings. So "programs that see the goal"
need no new machinery: a solver is an ordinary meta-function over code,

```
solver : (g: Ctx, P: TyCode(g)) -> Option(Code(g |- El(P)))
```

and it is **untrusted by construction** — its output lands in a hole the
kernel checks. Casual goal-massaging is safe for exactly the reason
tactics usually aren't.

Surface: keep everything expressions, with `goal` as the reified
statement in an `on` right-hand side:

```heather
fn sum_three(xs: List(Nat), long: 2 < xs.len()) -> Nat {
    xs[0] + xs[1] + xs[2]
    on _: _ := lt_auto(goal, long);   // applied to each remaining goal; may fail
}
```

- `on _: _ := expr` runs `expr` per remaining goal (`goal` bound to that
  goal's statement); a `None`/failure leaves the goal outstanding and
  *listed* — no silent gaps.
- **Goal merging/subsumption needs no feature at all** — it is just
  programming with holes: introduce the strong goal, discharge the weak
  ones from it:

```heather
    let strongest = ?strong;                       // : 2 < xs.len()
    on _: 0 < xs.len() := lt_0_2.trans(strongest);
    on _: 1 < xs.len() := lt_1_2.trans(strongest);
    on ?strong := long;
```

  and a `subsume_lt`-style meta-function can *generate* that pattern.
  ❓ Whether set-level transformers (rewrite the goal list wholesale)
  deserve first-class syntax, or stay meta-library idioms like this —
  lean library-first; revisit if a real proof grinds without it.
- Guardrail, per the standing taste constraint: transformers declare
  their output goals (the `on`-discipline is preserved); no imperative
  goal-stack mutation. Structural, always.

## 3. pow vs specialize_pow, sharpened (review was right)

Round 2 called `specialize_pow` "pow moved across the boundary by hand"
— too glib. Correct account: they are **different functions related by a
binding-time split**. `pow.code : Code(· |- Nat -> Nat -> Nat)` is one
fixed closed term — the recursor, unapplied. `specialize_pow` takes `n`
*statically* (meta-level) and `x` *dynamically* (as code) and runs the
recursion at the meta level, emitting unrolled residual code. No local
syntactic move gets you from one to the other — unrolling means
*executing* the static part. That is the book setup (MetaML's power, ch.
04's motivating staged programs), and it is `specialize_pow`, not `pow`.

Three routes between them, in ascending ambition:

1. **Hand-staging** (status quo, the literature's answer): write
   `specialize_pow` yourself. Fine; it's short.
2. **Mechanical binding-time analysis in the elaborator** (round-2
   earmark): derive the staged version syntactically from `pow` + a
   static/dynamic annotation. Classic BTA; untrusted output, kernel
   checks. Plausible later.
3. **A certified partial evaluator** — the in-thesis route:

   ```
   pe : (g: Ctx, e: Code(g |- A -> B), static: Code(g |- A))
          -> Code(g |- B)
   theorem pe_correct: … eval(pe(e, s)) == eval(e)(eval(s)) …
   ```

   an ordinary meta-function over code (`match code` symbolic
   reduction), written and certified **once**, giving every function
   specialization-with-proof for free: `pe(pow.code, lit(3))`. Two facts
   make this genuinely tractable here rather than a research fantasy:
   (a) the object language is **total** (everything is
   eliminator-based), so a PE by structural recursion on code
   terminates — no widening/fuel heuristics in the correctness story;
   (b) stuckness is *honest* — recursors block on neutral scrutinees, so
   "can't specialize further" is a syntactic condition the PE handles by
   residualizing, conservatively and correctly.

**And this is where threads 1 and 3 meet**: a smart instance's
`ir(ctx)` for a known-constant argument is exactly
`lower(pe(f.code, ctx.const))` — context-specific compilation *is* the
certified specializer applied at instance level, with `pe_correct`
composing into the instance's `equiv`. The feature from §1 and the
staging story from §3 are one mechanism seen from two ends, which is a
good sign the design is carving reality at a joint.

## Findings

1. ✔ Smart *instances* over smart resolution: ctx-parametric `ir` with a
   ∀-ctx equiv proven once; dedup = coarse-descriptor keying; context
   facts may carry proofs (optimization guards become propositions).
2. ✔ Goals are code, so goal-solvers are ordinary meta-functions —
   untrusted by construction; `on _: _ := solver(goal, …)` surface form;
   merging is expressible as plain hole-programming today, set-level
   transformer syntax deferred until a real proof demands it.
3. ✔ pow ≠ specialize_pow: a binding-time split, not a boundary move.
   Routes: hand-staging now, BTA later, certified PE as the in-thesis
   endgame (tractable because the object language is total and stuckness
   is syntactic). Context-specific compilation = certified PE at
   instance level — threads 1 and 3 are one mechanism.
