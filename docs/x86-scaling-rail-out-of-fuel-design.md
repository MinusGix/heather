# The 20-node x86 scaling rail: attribution and the boundary it found

Owner issue: `issues/x86-scaling-rail-out-of-fuel.md`. Written after the
measurement, as §13 of `docs/per-instantiation-type-codes-design.md` was.

## 1. Attribution: the two sides

The rail's refusal is one item, `mixed_binary_alu_x86_artifact`, and the
hypothesis on the issue was a *spelling twin* rather than a genuine
compute-through. It is the twin, and both halves are now on record.

Method: `HEATHER_CONV_MISS_TRACE=mixed_binary_alu_x86_artifact` (the
per-item miss trace, `crates/kernel/src/typing.rs`, behind `value-metrics`)
together with a throwaway `HEATHER_PROJ_TRACE` decline/mint listing in
`project_field` keyed by receiver shape — §13.1's method, run as a listing
because a silent decline looks exactly like a device that fired and lost.
Dev profile, 20 nodes, committed budgets, one furnace box.

**The expected side carries the projection reference.** From the trace of
the item's largest miss (`Id`/`Id`, 930.3 ms, site
`App < Pair×10 < Lam×5`, first difference at byte 17 — the left-hand side's
head):

```text
expected: Id[0](El[0](x7); app(app(u714^{·^8}; …; x7); … ) …
inferred: Id[0](El[0](x7); fst[0,0](El[0](x7). Unit 0; snd[0,0]( … )) …
```

`u714` is `MachineState#projⱼ`. The second `Id`/`Id` (3.5 ms, site
`App < Pair×8 < Lam×7` — `registers_preserved`, inside its two λs) is the
same pair one field over (`u717`), differing at byte 1237 where
`after.gprs` sits. Expected lengths 673 and 1892; inferred 1150 and 2116.

**Why each side is spelled the way it is.**

- The *expected* side is `BlockArtifact`'s own field type
  (`lib/std/arch/x86_64/x86_64_block.hthr`: `result_correct`, `memory_preserved`,
  `rip_correct`, `registers_preserved` — the four `Id`-typed fields, and the
  four misses), elaborated once at the declaration where `after` is a
  **local binder**. `receiver_is_neutral` says yes, so §13.4's telescoped
  device mints `MachineState#projⱼ(M, after)`. The constructor application
  then substitutes `after := mixed_binary_alu_x86_after(before)`, and the
  reference is left standing over a **computed** receiver.
- The *inferred* side is the generated theorem's own statement
  (`crates/elab/src/function_ir_x86_lower.rs`, the
  `_refines_function_ir` / `_preserves_memory` / `_advances_rip` /
  `_preserves_protected` emissions), where the receiver is written
  `mixed_binary_alu_x86_after(before)` — a global-headed application.
  `receiver_is_neutral` recurses `App → fun` to a `GlobalTm` and says no, so
  §13.6's second boundary declines and the **inline walk** is written.

The decline listing confirms it directly; the whole 20-node module has
1,526 field reads, and the `MachineState` rows are

```text
 112  decl=MachineState field=0 gate=true  args=true  recv=Var
  38  decl=MachineState field=2 gate=true  args=true  recv=Var
  14  decl=MachineState field=3 gate=true  args=true  recv=Var
   5  decl=MachineState field=1 gate=true  args=true  recv=Var
   5  decl=MachineState field=1 gate=false args=true  recv=App<App<App<Global(GlobalVar(24))
```

— `args=true` on the declining rows: the instantiation arguments are
recoverable and `rec_proj_ref_at` would have fired. **Only the receiver-shape
gate declines**, and it declines on exactly the five generated theorem
statements that read a field of `…_after(before)`.

**So §13.6's second boundary is not stable under substitution.** A reference
minted at a local receiver *becomes* a reference over a computed receiver the
moment the local is instantiated, and the boundary then disagrees with itself:
the record's substituted field type says "reference", every use site written
against the same computed state says "inline walk". Where the two meet, the
shortcut cannot fire and the kernel converts by computation — which here means
symbolically executing the whole 22-instruction block over an open machine
state, once per field.

**What grows 89× when the block grows 3×.** Not the misses — the item's four
`Id`/`Id` rows are `BlockArtifact`'s four `Id`-typed fields, a count fixed by
the *record*, not by the block. What grows is what each of them has to
evaluate. Each is decided by conversion rather than by the shortcut, and
deciding it means reducing `…_after(before)`: a 22-deep
`execute_normal(decoded_canonical(…), …)` chain at twenty nodes against a
7-deep one at five, over an **open** machine state, so the symbolic value at
each step carries the ones before it. That is why the evaluator's work is
superlinear in the block where the miss count is flat: 11,864 steps at five
nodes, 1,058,158 at twenty, for the same four fields.

*(Numbers restated once: the issue carries the budgets, the bisect and the
five-versus-twenty item costs; they are not repeated here.)*

## 2. What the shortcut needs, and what that rules out

One constraint runs through every candidate below and is worth stating first,
because it eliminates three of them on its own.

**The shortcut is all-or-nothing per type.** `conv_ty`'s syntactic shortcut
compares the two whole types; a single sub-term spelled two ways sends the
*entire* `Id` to conversion, where both sides are evaluated. So "spelled
alike" is not a matter of degree: `registers_preserved`'s type reads *two*
machine states (`after.gprs` and `before.gprs`), and a fix that aligns one and
misaligns the other buys nothing at all.

**And the elaborator cannot respell its way out.** A record is a Σ-tuple
(§3.3), so the artifact is nested `Pair`s and the expected type of field *j*
is the declaration's own field type with the earlier components substituted
**by the kernel**, out of the `Pair`'s `snd_ty` annotation. Respelling the
annotation does not help: the annotation must still convert against the
record's reference-spelled type, so the miss moves rather than goes. The
spelling that decides this is the one `project_field` wrote **into the record
declaration**, and the only lever on it is the boundary itself.

### 2.1 Rejected: widen the boundary (mint at every receiver)

The symmetric fix — the record declaration mints, so let the use site mint too
— and the first thing measured, because §13.10's rejection of it was dated
against the 2026-09-10 kernel and three spelling rounds have landed since
(most recently `code_of(emit_ty(template))`, 2026-09-13, which halved the
certificates). Hand-run on the current tree rather than inherited:

| | 20-node rail | 50-node rail | `native_summary` |
| --- | --- | --- | --- |
| boundary as committed | **OutOfFuel**, 19.3 s | — | ok, 48.7 s |
| minting at every receiver | **ok, 4.6 s** | **ok, 8.5 s** | **`caller_native_memory_same_27`: OutOfFuel**, 20.5 s |

So the rejection has *not* expired: it fixes this rail outright and
reintroduces §13.10's refusal one item earlier than before. Widening is out on
its own measurement, not on the old note. (`native_summary` reuses
`target/native-test-images`; the refusal is in the *generated* certificate,
which is elaborated fresh either way, and §2.4's arm — which cleared the
store — refuses the same theorem.)

### 2.2 Rejected: decline inside a record declaration's field types

The mirror image — never mint where the receiver is a binder that exists to be
substituted. It fails the all-or-nothing constraint above:
`registers_preserved` reads `before.gprs` as well, `before` is instantiated
with a **local**, and the use site mints there. Aligning `after` misaligns
`before`, the whole `Id` misses, and the block is symbolically executed
exactly as before. (It also leaves every ordinary `Π` domain — the same shape
one layer out — untouched.)

### 2.3 Rejected: a generator-side spelling

`function_ir_x86_lower.rs` could state the after/final facts once and reuse
them. It is the wrong layer twice over: `BlockArtifact` is a *library* record and any other client that
constructs one at a computed state pays the same 89×, and the generator cannot
change what spelling `project_field` writes into `lib/std`'s declaration —
only which sites hit it.

### 2.4 Measured and rejected: bound the computation at one layer

§13.6's argument is a cost, not a correctness claim — "a projection reference
is cheap to **compare** and dear to **compute through**" — and what it is dear
by looked like δ + β *per level of the receiver's own computation*. So the
next candidate bounded that at one: mint where the receiver is neutral, **or**
where it is a single global-headed spine over neutral arguments. That admits
`…_after(before)` and, it was hoped, not `reused_callee`'s chain.

It does not separate them. `reused_callee`'s own statements are
`{prefix}_state_{i}(gprs, flags, stack).memory = {prefix}_computed_{i}(gprs,
flags, stack).memory` (`crates/cli/src/native/calls.rs`): the *term* is one
global over three neutrals, and the twenty-eight levels are inside the
definitions, not in the receiver. `caller_native_memory_same_28` is refused
again. **No predicate on the receiver's syntax can tell the two apart** — they
are the same shape, and both unfold into a deep chain. What differs is whether
the conversion is decided syntactically or by computation, which the
elaborator cannot know.

### 2.5 Taken: decline at the **bare binder**, keep the chain

The two candidates above both tried to make the *use* site agree with the
declaration. The remaining move is to make the declaration agree with the use
site — and §2.2's objection to that was only that it left `before.gprs`
misaligned, because a bare local receiver mints on both sides. Decline there
too and everything lines up:

> mint the reference where the receiver is neutral **and is not the bare local
> itself** — a `Fst`/`Snd`/`App` chain over a local, not the binder.

Read against the fields of the artifact:

| read | record's field type | the statement written against it |
| --- | --- | --- |
| `after.gprs` / `.memory` / `.rip` | bare field binder → **walk** | `…_after(before).x`, computed → **walk** |
| `before.gprs` | bare parameter binder → **walk** | `before.gprs`, bare local → **walk** |

Both sides of every read agree, the shortcut fires, and nothing is evaluated.
`reused_callee` is untouched: its receivers were computed before and are
computed now.

**The item, measured** (dev, `--features value-metrics`, committed budgets):

| `mixed_binary_alu_x86_artifact` | 5 nodes | 20 nodes |
| --- | --- | --- |
| kernel gate | 7.32 ms | 7.57 ms |
| conversion misses | 279 | 279 |
| evaluator steps | 4,263 | **4,263** |

The item is now **independent of the block** — same steps, same misses, at
three times the instructions — which is what "the shortcut fires" means, and
is the sharpest possible form of the round's bar (20-node steps within 5× the
five-node count: they are equal). Before, under budgets lifted far enough to
finish at all, it was 1,058,158 steps and 3.94 s.

The argument is not "it happens to line up". A reference minted at a **bare
binder** is the one shape that cannot survive its own use: a binder exists to
be replaced, and what replaces it decides a *different* spelling. A chain
(`Sndᵏ v`, an applied local) is §13.1's measured payer — the shape whose
`Fst`/`Snd` nodes each make the kernel reconstitute `Σ(fst_ty). snd_ty` and
convert it against the receiver's reference — and a bare binder's read is a
*single* such node, which is what the walk costs anyway. So the boundary now
names what the device was measured to buy rather than the largest set that
looked safe.

**Where the decision actually lands.** Worth recording, because it was a
surprise and it is what makes the rule work: the spelling that decides this is
the one `project_field` wrote into `lib/std/arch/x86_64/x86_64_block.hthr`'s
**declaration**, not the one at any use. A record is a Σ-tuple, so the kernel
substitutes the constructor's earlier components into the declaration's own
field type, and the elaborator's annotations get no vote. The measurement
shows it directly: a run whose semantic image store was written under one
boundary and replayed under another behaves like the boundary that wrote the
*image*. §4 has the consequence for A/B protocol.

### 2.6 What it costs

`reused_callee`'s whole-workload gate, both arms on **one** furnace box from
**one** build (the boundary behind an env switch, each arm with its own fresh
`--cache-dir`), release, `--features value-metrics`, `HEATHER_KERNEL_WORKERS=1`,
cold:

| | boundary as committed | with §2.5 | Δ |
| --- | --- | --- | --- |
| items | 4,997 | 4,997 | — |
| item total | 88.06 s | 90.99 s | **+3.3 %** |
| `kernel_gate` | 60.98 s | 62.77 s | **+2.9 %** |
| evaluator steps | 46,617,036 | 46,744,997 | +0.3 % |
| conversion misses | 361,641 | 381,625 | **+5.5 %** |
| `call_run_checked` | 21.84 s / 8,100 misses | 22.36 s / 10,041 | +2.4 % |
| `caller_native_leaf_source_artifact` | 0.45 s / 8,519 | 0.67 s / 13,369 | +50 % |
| `stack_word_agrees` | 0.24 s / 8 | 0.44 s / 1,560 | — |

The steps and misses of the committed arm reproduce the round's before column
exactly (46,617,036 and 361,641), which is what makes the two columns
comparable; the wall differs from that column by box state alone.

**The extra misses are the price, and they are named.** Every bare-local field
read that used to be one syntactic comparison is now the inline walk, whose
`Fst`/`Snd` nodes each reconstitute `Σ(fst_ty). snd_ty` against the receiver's
named type — the `Sigma`/`El(?)` row §13.9 measured. 19,984 of them, at about
90 µs each: +1.8 s of kernel gate. `stack_word_agrees` is the clearest single
case and was already named as a residual payer in §13.9's boundary list.

**Against the bar, honestly:** `kernel_gate` is inside ±3 % (+2.9 %); the item
total is **marginally outside** (+3.3 %); the miss count rose by 5.5 % and the
sentence above is the explanation the changed count needs. What is bought is a
20-node certificate that goes from *unbuildable* to 4.6 s under the committed
budgets, and a 50-node one that builds at all. A follow-up that would recover
most of the 3 % — keep the reference at a bare local in *term* position, where
nothing can substitute it, and decline only inside a declaration's stated type
— is filed on [[per-instantiation-projection-boundaries]] rather than guessed
at here.

## 3. What implementing corrected

Three things the plan had wrong, each found by a measurement rather than by
reading:

1. **The rejection had not expired.** The round opened by hand-running §13.6's
   rejected widening on the current tree, because a perf rejection is dated
   against the kernel of the day it was taken. It fixes this rail outright —
   and
   `caller_native_memory_same_27` is refused again (§2.1). The dated rejection
   survived three spelling rounds.
2. **No receiver-shape predicate separates the two workloads** (§2.4). The
   obvious candidate — "do not mint where the receiver is a *computed* state"
   — is what shipped *already*, and it is the half of the boundary that causes
   the refusal. The useful move was on the other half, in the opposite
   direction.
3. **The elaborator's annotations are not the lever** (§2's preamble, §2.5).
   An emission-site respelling cannot reach this: a record is a Σ-tuple, so
   the expected type of a field is the *declaration's* field type with the
   earlier components substituted by the kernel. The A/B runs
   made this visible by accident — a boundary that wrote the semantic image
   store decided the outcome of a run made under a different one.

Consequence for protocol, worth keeping: **an A/B on a spelling boundary must
clear `target/semantic-test-images` and any `--cache-dir` between arms**, or
the arm that built the image is the arm being measured. (Image keys cover the
compiler build, so a source change invalidates them; an env-var A/B does not.)

## 4. The rail, promoted

`generated_20_node_mixed_binary_alu_dag_checks` is no longer `#[ignore]`d. It
is now `slow_acceptance_generated_20_node_mixed_binary_alu_dag_checks` —
`scripts/test`'s own documented opt-in, so the fast lane filters it by prefix
and the full lane runs it. It is the regression pin this round needed and
needs no metrics to be one: the item is refused `OutOfFuel` under the
committed budgets the moment the two sides of a field read stop agreeing, so
the gate is a *refusal*, not a threshold. 50 nodes stays explicit
(`generated_50_node_mixed_binary_alu_dag_checks`, `#[ignore]`d).

Cost, measured on the furnace box (dev profile): ~16 s when the rail's
semantic image prefix is cold and ~5 s when it is warm — against the per-child
`ulimit -t 300` rail, and against `native_summary`'s ~230 s
(`issues/native-summary-test-cpu-margin.md`), it is not close to a margin.
