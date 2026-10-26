---
title: A constructor value of an n-constructor type costs Θ(n²) to elaborate and Θ(k·n) to gate
status: closed
labels: [elaboration,kernel,inductives,performance,x86]
area: language
milestone: [hih-passes]
code: crates/elab/src/gendefs.rs:2755 @ 9a80b41
created: 2026-10-26
updated: 2026-10-26
---

Found by the intricate-inductive bench families
([[intricate-inductive-bench-families]], `inductive/isa-constructor-use`).
An instruction-shaped declaration — `n` forms, each with a couple of operand
fields — is cheap to declare (`inductive/isa-declaration`, slope ~0.9), but
every **mention** of one of its constructors is not, and the cost grows with
the number of constructors the type has, not with anything at the mention.

`heather check --timings`, release, width one, cloud box (`fn mk(a: Reg, b:
Reg) -> Instr { Iₖ(a, b) }` beside the `n`-form declaration):

| n | `I₀(a, b)` total / gate | `Iₖ(a, b)`, k ≈ n total / gate | gate eval steps at k ≈ n |
|---|---|---|---|
| 64 | 5.3 / 0.1 ms | 7.2 / 1.5 ms | 4,661 |
| 128 | 32.6 / 0.1 ms | 29.5 / 7.1 ms | 18,059 |
| 256 | 152.8 / 0.1 ms | 181.9 / 36.5 ms | 67,829 |
| 512 | 363.0 / 0.1 ms | 625.0 / 96.0 ms | 268,811 |

Two costs, in two layers:

1. **Elaboration, Θ(n²) per mention, whichever constructor.** `I₀(a, b)` at
   n = 512 is 339 ms of `decl_body`, with almost no counted events. gdb
   stack samples (six of six) sit in `<Type as PartialEq>::eq` under
   `respell_spine` → `spine_refs_by_position`
   (`crates/elab/src/gendefs.rs:2755`), from `prepare_ctor` /
   `build_ctor`. The positional path compares *every* component of the
   freshly built spine against the registered inline spine by deep
   structural equality, to guard that the references may stand
   ([[inductive-spelling-codes-nonrecursive]]'s guard). `tails[k]` is the
   suffix sum of the n − k later payloads, so the tails alone are Θ(n²)
   nodes, and none of them share an `Rc` with the registered copy (the spine
   is rebuilt from a whnf), so `Arc<Type: Eq>`'s pointer shortcut never
   fires.
2. **Gate, Θ(k·n) for the k-th constructor.** The `inr`-chain to the k-th
   payload unfolds a suffix code per level (`eval_delta_steps` 134,400 and
   `sel_evals` 133,894 at k = 510, n = 512, ≈ k·n/2). Constructor 0 is 41
   steps.

So an x86-sized instruction type (on the order of a thousand forms) pays
about a second per constructor value, and a `match` that rebuilds values
(`inductive/isa-roundtrip`, slope ~2.4 to ~2.8 from 128 to 256 forms) pays it
per arm.

## What a fix looks like

- The guard is a statement about the *spine*, which is the same for every
  mention of the type: check it once per declaration (or memo it on the
  decoded type's identity) instead of once per component per mention. Or
  compare by the tag and the registered spine's identity where the spine
  came from the registration in the first place.
- The gate side is the encoding: a right-nested sum puts the k-th
  constructor k injections deep, and each level's annotation is a suffix code
  that is unfolded. A balanced sum, or annotations the kernel does not need to
  unfold per level, would make it Θ(log n) or Θ(k).

Acceptance: `inductive/isa-constructor-use` drops to about 1 (the
declaration) and `inductive/isa-roundtrip` to about 1 to 1.5, re-recorded
from below.

## What it assumes from elsewhere

- **[[inductive-spelling-codes-nonrecursive]]** owns the positional
  references and their guard. Assumed here: only that the guard is a
  structural comparison per component.
- **[[emit-ty-rewalks-normalized-type]]** owns the deep `emit_ty` walk under
  the same `respell_spine` call on large *field* types. This is the other
  half of that call: the component count, not the component size.

## Log

- 2026-10-26: fixed in three places; `inductive/isa-constructor-use` 1.71 →
  0.96 (met), `isa-opcode-match` 1.62 → 1.34, `isa-roundtrip` 2.15 → 1.96
  (cloud box, three runs each).
  1. **The positional guard** (`spine_agreement`, `gendefs.rs`) compares
     the payloads deeply and each tail as its `+` node only: `tails[k]` is
     `ctors[k+1] + tails[k+1]` by pointer on both sides (`spine` reads them
     off without copying), so with the right neighbour's answer in hand
     it is two level comparisons. Θ(n) per mention instead of Θ(n²).
  2. **Sharing with the registered lowering**
     (`Elaborator::share_registered_lowering`, called from `lower_named`):
     a bare named type equal to its `D#tycode` guard copy is returned as
     that copy's nodes, so every later guard (`closed_type_ref`, the spine
     guard) stops at `Rc` identity. At 1024 forms the body of
     `fn mk(a, b) → Instr { I0(a, b) }` is ~2.5 ms; what remains per `fn`
     is lowering `Instr` in the signature, which a declaring module does
     per mention ([[named-type-lowering-per-mention]]'s "Left").
  3. **The gate** was Θ(k²), not Θ(k·n): layer `j` of an unannotated
     `inr@` chain was checked against a selection `j` deep and every view
     replayed it from the root. `Tc::injection_at_spine` views a contiguous
     chain's layers in one arena (`conv::injection_heads_cached`, the
     intro twin of `projection_at_spine`), and checks only the innermost
     value against the full description. `I₁₀₂₀(a, b)` at 1024 forms: 1.06 M
     eval steps → 16 K, gate 473 → 7 ms. Golden test
     `typing::an_injection_chain_checks_every_layer`; the typing
     differential already generates mixed chains.
- Left, not this issue's: the roundtrip's identity theorem, whose gate
  grows faster than its counters because every conversion query builds
  Γ's identity environment ([[conv-query-identity-env-per-gamma]]), and the
  encoding itself — the `k`-th value is still `k` injections deep, so an
  `n`-arm rebuild is Σk nodes. A balanced sum would make that Θ(n log n);
  not attempted, as it changes every reader of the spine.
