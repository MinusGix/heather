---
title: call_run_checked is one library theorem worth a third of the reused_callee workload's kernel gate
status: closed
labels: [stdlib,x86,kernel,performance,proofs]
created: 2026-09-13
updated: 2026-09-14
---

From the 2026-09-13 checkpoint table (release, value-metrics, W=1, `build-x86 examples/x86-native/reused_callee.hthr caller --callee leaf`, cold, one furnace E5 box): whole workload 4,997 items, item total 92.4 s, kernel gate 64.1 s, 46.6 M steps, 361,641 misses. The top row is a single item:

| item | total s | kernel s | misses | steps | shortcut hits |
| --- | --- | --- | --- | --- | --- |
| `call_run_checked` (lib/std/arch/x86_64/x86_64_call_summary.hthr) | 28.7 | 23.4 | 8,100 | 15.6 M | 1.09 M |
| `caller_native_byte` (36 items) | 4.8 | 4.0 | 34,515 | 2.6 M | |
| `call_trace_append` | 3.8 | 2.9 | 850 | 1.8 M | |

One theorem is 37 % of the gate and a third of all evaluator steps; the next family is six times smaller. It sat unremarked in the round-4 table (docs/bitvector-literal-entry-design.md §10.6: 23.68 → 23.29 s across that round, i.e. not bitvector-shaped). It is library time — paid per cold library build and replayed from the image otherwise — so it does not tax a compiled program the way the certificate families do, but 15.6 M steps for a structural induction over `List<CallInstruction>` with an `Exists`/`∧` premise chain is a pathology: the theorem is a `match` with one recursive call and a handful of projections, `j`, `trans`, `cong_fn`. Attribute before touching it (`--timings` plus the conv-miss sampler on `heather check lib/std/arch/x86_64/x86_64_call_summary.hthr`): the likely shapes are the premise record's projections `premises.proof.right.right.right` computed through per-instantiation references ([[per-instantiation-projection-boundaries]]), or `call_next`/`call_run` unfolding under the motive.

Trigger: any round that measures cold library time, or the next x86 spelling round. Related: [[x86-64-machine-model]], [[x86-calls-stack-frames]], [[function-ir-x86-proof-scaling]].


## Log

### 2026-09-14 — reproduced and narrowed, no production change

Measured at `7ec67b2`, release with `value-metrics`, cold (no `--cache`),
`HEATHER_KERNEL_WORKERS=1`, on the local investigation host. These are
single-run diagnostic times, not a cross-host comparison with the checkpoint.
The standalone module closure reproduces the theorem's 15.6 M steps:

| variant | item s | kernel s | misses | evaluator steps | shortcut hits |
| --- | ---: | ---: | ---: | ---: | ---: |
| unchanged source | 27.950 | 24.070 | 10,041 | 15,607,876 | 1,107,762 |
| explicit lambda binder for `tail` | 31.704 | 26.943 | 8,292 | 12,905,690 | 909,102 |

The unchanged `call_trace_append` control is 2.858 s kernel / 1,782,181
steps / 850 misses. The updated baseline's 10,041 misses agrees with the
post-narrowing row in `docs/x86-scaling-rail-out-of-fuel-design.md`; the
original issue table predates that projection-boundary change.

**Conversion attribution.** The baseline sampler charges 19.228 s to this
item's conversion misses (nested within item accounting, not an extra phase):

| expected / inferred | count | seconds |
| --- | ---: | ---: |
| `Vec` / `Vec` | 762 | 10.757 |
| `Sigma` / `El(?)` | 2,113 | 2.531 |
| `Sigma` / `Vec` | 836 | 1.584 |
| `El(?)` / `Wf` | 115 | 1.094 |

A separate `HEATHER_CONV_MISS_TRACE=call_run_checked` run records all 10,041
misses. Of its 762 `Vec`/`Vec` misses, 592 share this innermost-first site:

```text
Var < App < App < App < App < ElimWf < ElimWf < Lam < App < App < App < App < App < App < TmSigma < TmSigma
```

Those 592 comparisons total 10.378 s in the trace run. A repeated pair has
exact rendered lengths 123,978 versus 944 UTF-8 bytes (first difference at
274); the excerpt shows an expanded Sigma tree meeting an `El` reference.
This is evidence of a large representation mismatch inside checked type-code
terms, not merely a small number of slow equality transports. `Vec` here
must not automatically be read as bitvector arithmetic: the recursive
lowering uses child vectors in its `ElimWf` telescope
(`docs/inductive-tier1-wf-lowering.md` §§6.1–6.3). The bounded trace does not
identify the precise source function/type behind this pair yet.

**Controlled source probe.** Replace the `let tail = recursive_call; body`
with `(λ (tail: FetchedCallTrace(fetch, access, rest, premises.witness, after)
∧ after = call_run(access, rest, premises.witness)) => body)(recursive_call)`.
Use `And(...)` for the body's outer pair so the applied lambda can infer its
result; anonymous `⟨...⟩` there fails with “checking-only”. Everything else,
including the theorem statement and recursive call, stays the same. The
complete temporary module checks successfully.

This tests a real distinction: `crates/elab/src/statements.rs:1` documents
that surface `let` is an elaborator alias, not a kernel binder; the original
two tail projections contain the aliased recursive application. The binder
reduces steps by 17.3% and misses by 17.4%, but leaves 628 `Vec`/`Vec` misses
and gives no wall-time improvement in this run. It is not a sufficient fix,
and neither the probe nor any compiler/library edit was retained.

**Next attribution step.** Capture the full telescope identity and emission
origin of the repeated `Vec` pair, focusing on `build_elim_wf` /
`apply_cs_ih` in `crates/elab/src/wf.rs` and type-code arguments carried by
premise/result projections. The current evidence does not distinguish a
projection-triggered expansion of `CallPremises` from other motive/type-code
expansion, so do not widen projection eligibility on this evidence alone.
The existing boundary issue remains relevant, but its `Sigma`/`El(?)` bucket
is not the dominant measured cost here. Leave this issue open for the fix.

**Reproduction correction.** The suggested direct `heather check` command
cannot resolve `x86_64`: the generic loader uses file stems while native builds
assign architecture aliases. Stage unchanged copies using the native build's
mapping, then check the staged root (from the repository root):

```sh
cargo build --release -p heather-cli --features value-metrics
python3 - <<'PY_STAGE'
from pathlib import Path
import re
source = Path('crates/cli/src/native.rs')
staged = Path('/tmp/call-run-investigation/modules')
staged.mkdir(parents=True, exist_ok=True)
for name, path in re.findall(
    r'\("([^"]+)", include_str!\("([^"]+)"\)\)', source.read_text()
):
    (staged / (name + '.hthr')).write_text(
        (source.parent / path).resolve().read_text()
    )
PY_STAGE
(ulimit -v 8388608 -t 240
 HEATHER_VALUE_METRICS=1 HEATHER_KERNEL_WORKERS=1 target/release/heather check \
   -L /tmp/call-run-investigation/modules \
   --timings /tmp/call-run-investigation/baseline.tsv \
   /tmp/call-run-investigation/modules/x86_64_call_summary.hthr \
   > /tmp/call-run-investigation/baseline.log 2>&1)
```

For the separate trace run, add `HEATHER_CONV_MISS_TRACE=call_run_checked`
and use separate output paths; allow 300 CPU seconds for diagnostic rendering.
Raw baseline, trace, and successful `tail_binder` source/TSV/log artifacts
were left under `/tmp/call-run-investigation/` in the investigation workspace.
Validation was the successful capped module checks; no Rust or library files
changed, so no compiler test suite was run for this documentation-only round.


### 2026-09-14 — emission origin isolated; telescope spelling fix

The follow-up captured one full, bounded `Vec`/`Vec` pair with temporary
instrumentation (removed afterward). Both sides are child vectors of a
list-shaped `Wf`, with arities 0/1. The expensive side's `Wf` shape carries
the expanded instruction payload (including its 64- and 32-bit fields);
the small side carries the closed payload code reference. The earlier
123,978/944 sizes are UTF-8 **bytes**, as reported by the sampler, rather
than character counts.

The emission origin is `build_elim_wf`, `crates/elab/src/wf.rs`: `d_emit`
used only `ty_type_ref`, which recognizes closed `TyCode` registrations.
Parameterized recursive types such as `List<CallInstruction>` have a
`TyCodeFn` instead, so this lookup declined and the complete structural
`Wf` became the element type in `wf_step_telescope_at`'s `Vec` and `nth`
annotations. Meanwhile the emitted eliminator slots already used component
references, and the kernel reconstructed a smaller telescope from them.
`apply_cs_ih` repeatedly compared these two representations. This was a
missing emission fallback, not a reason to change kernel conversion or
projection eligibility.

**Change:** use `emit_ty(cx, scrut_ty, 0)` when the closed lookup declines,
matching the existing constructor path in the same file. Structural readers
still receive `scrut_ty`; only emitted annotations take the reference. No
Heather proof or theorem statement changes.

Same cold staged-module protocol, release / value-metrics / W=1, unchanged
library source:

| item / scope | baseline kernel s | fixed kernel s | baseline steps | fixed steps |
| --- | ---: | ---: | ---: | ---: |
| `call_run_checked` | 24.070 | 3.899 | 15,607,876 | 3,130,456 |
| `call_trace_append` | 2.858 | 0.167 | 1,782,181 | 13,987 |
| all 1,099 items in this import closure | 36.831 | 13.273 | 26,998,966 | 12,337,552 |

These closure totals are not the full `reused_callee` workload. The theorem's
item total falls 27.950 → 4.638 s, kernel time 83.8%, and steps 79.9%.
The strongest attribution control is the **same 762 `Vec`/`Vec` misses**:
10.757 → 0.071 s. Total misses barely move (10,041 → 9,960), demonstrating
that the fix makes each comparison cheap rather than bypassing checking.
The 836 `Sigma`/`Vec` misses likewise fall 1.584 → 0.050 s. The prior
`tail`-binder experiment is not part of the fix.

The new unit test checks the actual children-vector element emitted by a
match on `Box<Flat>`: it must reference `Box#tycode_fn`. It also checks
recursive copying with an open element type, neutral and literal inputs,
checked equalities, and rejection of a false equality. This specifically
catches the representation regression that semantic acceptance alone misses.

Remaining conversion costs are small compared with the original pathology:
`El⌜⌝`/`El(?)` 0.868 s and `Sigma`/`El(?)` 0.736 s. General projection
boundary work stays with [[per-instantiation-projection-boundaries]]; this
fix does not widen that boundary. Raw follow-up measurement artifacts are
`fallback.tsv` / `fallback.log` and `vec-pair.txt` under the same temporary
directory as the first investigation.

Validation: the focused regression passes (`scripts/test -p heather-elab --lib
a_parameterized_match_names_its_children_element_type`: 1 passed). Full
`scripts/test`: **2,624 passed, 0 failed, 5 ignored** (174 s wall), including
the native summary test and the x86 scaling rail. `scripts/issue check` and
`git diff --check` pass. Temporary kernel diagnostics were removed before
the suite. Closed: the dominant cost is fixed; the general projection
boundary work remains with its existing owner above.


### 2026-09-14 — annotation API follow-up

Added the total `annotation_type` API and renamed the closed-only lookup to
`closed_type_ref`; audited and migrated its three production emission callers.
The API contract, caller audit and child-projection finding are recorded in
`docs/annotation-component-respell-design.md` §2.6. The focused recursive
lowering tests pass (60 passed). Full `scripts/test`: **2,626 passed, 0
failed, 5 ignored** (189 s wall), including native summary and x86 scaling.
`scripts/issue check` and `git diff --check` pass.


### 2026-09-14 — typed telescope boundary

Added separate structural/emitted wrappers to the shared recursive telescope;
see `docs/annotation-component-respell-design.md` §2.7 for the guarantee,
explicit raw-Type boundaries and the indexed-family audit. A temporary
structural-for-emitted substitution at the actual telescope call is rejected
by Rust (E0308), and was reverted. Focused `scripts/test -p heather-elab
--lib wf::`: 61 passed. Full `scripts/test`: **2,627 passed, 0 failed,
5 ignored** (245 s wall), including the indexed-family, native summary and
x86 scaling tests. `scripts/issue check` and `git diff --check` pass.


### 2026-09-14 — independent guards and remaining-site probes

Added independent registry-identity assertions across payload widths, a
persistent positive/negative compilation test of the private telescope
wrappers, and serial evaluator-count regression fixtures. Their contracts
and limits are in `docs/annotation-component-respell-design.md` §2.8.

The named `Box<Payload>` match takes **46/46/46** evaluator steps at payload
widths **2/8/32**, excluding setup. The guard allows a 2× ratio.
A temporary mutation making `StructuralWf::annotation` return its inline
structural type changed the counts to **67/91/187**, failing that guard
while all three declarations still kernel-checked. The mutation was reverted
before final validation.

The indexed audit used a three-constructor recursive index (`Shape`) and
`Family<A> : Shape -> Type`, with zero/one/two recursive children. Checking
the family declaration alone took **39/51/99** steps; its constant motive
hides the induction-hypothesis child term. A dependent recursive `copy`
took **57,768/77,568/156,768**. Temporarily naming the child annotations in
`wf_ih_at` and `wf_branch_env`, while keeping pattern aliases structural,
reduced this to **56,302/75,622/152,902**: roughly 2.5%, with the same linear
payload trend. Reverted the experiment; this does not establish another
instance of the dominant bug fixed here. The test retains a generous 4×
endpoint bound and semantic controls, including an open element type.

Projection substitution tests cover chains of 1/2/3 fields, a bare receiver,
and 0/1/2/4/8 rebuilding steps. The `make` declaration's evaluator counts are:

| Chain depth | Bare | 0 | 1 | 2 | 4 | 8 |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 54 | 63 | 75 | 81 | 93 | 117 |
| 2 | 54 | 69 | 92 | 103 | 125 | 169 |
| 3 | 108 | 127 | 163 | 176 | 202 | 254 |

Open field-use proofs and literal equations check; false equations are
refused. No projection policy change is justified by these cases. The
existing broader boundary issue remains open. All counts use one kernel
worker; raw logs are under `/tmp/call-run-investigation/` (`three-checks.log`,
`indexed-consumer-before.log`, and `telescope-cost-mutant.log`).


Validation: the final plain `scripts/test` completed with **2,632 passed,
0 failed, 5 ignored** (205 s wall), including all five new checks, the native
summary test and x86 scaling rail. `scripts/issue check` and
`git diff --check` pass. The first full run caught a test-only mistake using
an application lookup on a bare payload reference; the corrected registry
assertion uses `is_gen_ref`, and the full suite was rerun. Final log:
`/tmp/call-run-investigation/all-three-final.log`.
