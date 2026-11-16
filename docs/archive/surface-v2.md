# Surface syntax sketches, round 2

Continuing from round 1 review: local instance override, goal naming,
and the staging narrative ("code should feel like code, not macros").
✔ = decided this round, ❓ = open.

## 1. Local instance binding — safe specialization

The review sketch, polished:

```heather
instance custom_blah: Compile[Cpu] for blah {
    fn ir() -> … { … }                  // hand-tuned for this use site
    theorem equiv(…): … { … }           // same contract as any instance
}

runtime_fn do_thing(x: Nat) -> Nat {
    let instance Compile[Cpu] for blah = custom_blah;
    blah(x)                              // compiles via custom_blah here
}
```

The insight worth recording (goes beyond ordinary scoped-instances): in a
certifying compiler, **instance override is *safe* in a way it is nowhere
else**, because every `Compile` instance carries an equiv certificate —
the *semantics* of `blah` is pinned by the proof, so instance choice is a
purely *operational* decision (which correct IR runs), never a semantic
one. "I wish I could special-case this function's implementation, but
nobody can let me because they can't check equivalence" — here the
language checks equivalence, so it can let you. Coherence-by-default
(round 1) is therefore about *predictability*, not soundness, and local
`let instance` is its principled escape: explicit, lexically scoped,
certificate-carrying.

✔ Adopt: `let instance C for T = value;` as scoped resolution override;
default resolution stays coherent. (Logged to compile-typeclass-design —
resolution-from-`main`-inward composes with this naturally: the compiler
walks the call graph resolving instances in scope at each site.)

## 2. Goal naming — names are API

The round-1 worry: `on ?name := …` needs good names, but auto-holes
(`xs[i]`) have no user-written name, and repeats pile up. Three-part
answer, no positional filling anywhere:

1. ✔ **Default names come from the callee's parameter name.** `xs.get(0,
   ?)` creates goal `?bound` because `get`'s proof parameter is named
   `bound`; collisions get ordinals (`?bound.1`, `?bound.2`), and the
   checker lists them with provenance (which call site). Consequence,
   recorded as a design principle: **proof-parameter names are API** —
   libraries name them the way they name methods, because call sites
   discharge goals by them.
2. ✔ **Discharge-by-statement** for the no-natural-name case:
   `on _: 2 < xs.len() := long;` discharges the goal(s) whose statement
   matches — order-free, name-free, and it handles the "whole bunch of
   repeats" case by discharging *all* matching goals at once (the common
   pattern: one bound proof feeding many index sites).
3. Explicit site names (`?first`) always available and always win.

```heather
fn sum_three(xs: List(Nat), long: 2 < xs.len()) -> Nat {
    xs[0] + xs[1] + xs[2]
    on _: 0 < xs.len() := lt_0_2.trans(long);
    on _: 1 < xs.len() := lt_1_2.trans(long);
    on _: 2 < xs.len() := long;
}
```

❓ Whether `on _: P` should also accept a *weaker* statement it can
strengthen from (`on _: _ < xs.len() := …` with the index abstracted) —
attractive for arithmetic-heavy indexing, but it edges toward proof
search; defer.

## 3. The staging narrative

### The load-bearing fact: staging is exactly two-level

DeLaM's global bindings quantify code of layers v/c, and `□`/recursors
live only at layer m — **there is no code-of-code**. `Code(g |- Code(…))`
is not a type. So the MetaML-style multi-level tower, and all its
readability pathologies (which quotes am I under?), is structurally
impossible. There is "running code" and "code as data", one boundary,
never a stack of them. This settles round 1's deferred question:

✔ **Adopt implicit quotation** (checking position against `Code(Δ |- T)`
quotes the expression; `code {}` required in inference position and
available for explicitness). The two-level fact plus the rule below is
why it stays readable.

### The boundary is variables, not functions

Inside a quote, references to top-level `fn`s are just object code —
defs are inlined at elaboration, so `pow` inside a quote *is* its term.
`$` marks exactly the **meta-level variables** crossing the boundary.
This is the precise sense in which staged code "is just code": the whole
lexicon (functions, operators, literals, inductives) is shared between
stages; only variable references are staged. A reader scans for `$` and
knows everything else means what it always means.

### Writing once and extracting: `.code`

The review's wish — "write `fn foo` normally, later extract the Code for
it" — is elaborator-level, no kernel magic: the elaborator has `foo`'s
elaborated core term and can quote it.

```heather
fn pow(n: Nat, x: Nat) -> Nat {
    match n { Zero => 1, Succ(k) => x * pow(k, x) }
}

fn analyze() -> Nat {
    count_muls(pow.code)          // pow.code : Code(· |- Nat -> Nat -> Nat)
}
```

Two honest caveats, both features:

- **Intensionality**: `pow.code` is the *elaborated* term — its syntactic
  identity depends on elaboration (sugar choices included). That is
  exactly the contract compile-typeclass-design already accepted by
  keying instances on syntax; `.code` is where that contract surfaces.
  Elaboration determinism becomes a documented guarantee (❓ version it?).
- **Specialization is a library, not a kernel feature**: there is no
  kernel "normalize under box". A partial evaluator is an ordinary
  meta-function the ecosystem writes once:

```heather
fn specialize_pow(g: Ctx, n: Nat, x: Code(g |- Nat)) -> Code(g |- Nat) {
    match n {
        Zero => 1,                        // implicit quote
        Succ(k) => $x * ${specialize_pow(g, k, x)},
    }
}
```

  — which is round 0's `pow_code`, now recognizable as "`pow`, moved
  across the boundary by hand". ❓ Whether a `stage`-style annotation can
  *derive* `specialize_pow` from `pow` mechanically (binding-time
  analysis as an elaborator pass emitting an ordinary meta-function,
  checked by the kernel like everything else) — genuinely attractive,
  genuinely later. Recorded as the natural far end of the "write once"
  narrative.

### One narrative, end to end

The moves now compose into the story the language is *for*:

```heather
fn blah(x: Nat) -> Nat { … }             // 1. write ordinary code

fn blah_ir() -> List(Instr) {
    lower(blah.code)                     // 2. cross the boundary: syntax as data
}                                        //    (lower: match code -> deep-embedded IR)

instance Compile[Cpu] for blah {
    fn ir() -> List(Instr) { blah_ir() }
    theorem equiv(x: Nat):               // 3. certify: proofs are the same language
        simulate(ir(), [x]) == Some(blah(x)) { … }
}

runtime_fn main() { blah(7) }            // 4. run it, via any in-scope certificate
```

No macros, no second language at any step: step 2 is `match code`
(sketch round 0 §6) into a tier-0/1 inductive (round 1 §5), step 3 is
recursive theorems (round 1 §1), step 4 is scoped instances (§1 above).

## Findings

1. ✔ `let instance` scoped override; safe *because* instances are
   certificate-carrying — coherence is about predictability here, not
   soundness. Certifying compilation turns "special-case my function"
   from forbidden to checked.
2. ✔ Goal names: callee-parameter defaults + discharge-by-statement +
   explicit names; "proof-parameter names are API" adopted as a design
   principle; still no positional filling.
3. ✔ Implicit quotation adopted — justified by the two-level fact (no
   code-of-code in DeLaM) and the boundary-is-variables rule ($ marks
   meta variables, everything else is shared lexicon).
4. ✔ `.code` on top-level fns as the write-once/extract-later move;
   intensionality of the elaborated term is the (accepted) contract;
   specialization/PE is library territory, with mechanical
   binding-time-analysis derivation earmarked as a far-future elaborator
   pass.
