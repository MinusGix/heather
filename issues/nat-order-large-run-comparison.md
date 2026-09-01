---
title: Make closed Nat order cancel large shared run prefixes
status: open
labels: [kernel,frontend,performance,nat,representation]
created: 2026-08-31
updated: 2026-08-31
---

The compact FunctionIR hardening round found that compact numeral storage is
not yet compact computation.  A tiny mixed-width graph with three identifiers
at `u64::MAX - 10`, `u64::MAX - 9`, and `u64::MAX - 8` generated a small
certificate, but checking its closed directory-bound facts grew to 23.88 GiB
anonymous RSS before the Linux OOM killer terminated `function_ir_cert`.
Moving only those identifiers to the same relative positions around 10,000
leaves the graph and proof shape unchanged but already overflows the checker
thread's stack.  A second follow-up with a maximum identifier of 1,000 did the
same.  The ordinary regression therefore keeps every identifier below 100.

The first investigation separated two costs that the original failure had
conflated. Surface numeral elaboration still built `Succ` syntax in a loop, so
the near-maximum case could consume memory before `Lt` ever ran; the succinct
value representation had no ordinary producer. After compact literal syntax
removed that cost, the same certificate fails quickly by stack overflow under
a 4 GiB address-space limit. Closed reduction of `Lt`/`Le` inside
`DirectoryWithin` is therefore still a real, independent problem: recursive
order normalization peels the enormous common prefix instead of cancelling
run counts.

## Reproducer discipline

Do not restore the near-`u64::MAX` case to the unbounded ordinary suite.  Probe
the same `generated_v2_sparse_dag_checks` shape under an address-space limit,
varying only its `top` value, and record time and peak RSS.  The original
failure was:

```text
Out of memory: Killed process (function_ir_cer)
total-vm:23967212kB anon-rss:23881172kB
```

Uncapped follow-ups with maximum identifiers of 10,000 and 1,000 terminated
with Rust stack overflows rather than out-of-memory kills.  This makes linear
structural recursion a stronger hypothesis and shows the problem is not
confined to saturated counts.

Compare reduction of nearby values, values with unequal run counts, and a
small control.  Determine whether the growth belongs to frontend reduction,
kernel conversion/checking, or both before selecting the optimization layer.

## Likely direction

Teach operations over run-compressed constructor spines to consume matching
run counts arithmetically and retain a shared residual run, rather than
materializing or visiting one constructor per represented step.  The solution
should apply to generic Nat-shaped inductives represented by runs, not be a
FunctionIR special case.

## Acceptance

- Closed `<`/`<=` between nearby values close to `u64::MAX` stays within a
  small fixed memory bound.
- Scaling is by the number of run fragments (or logarithmic in their counts),
  not by the represented unary depth.
- The original sparse FunctionIR certificate checks under a documented memory
  cap.
- Controls cover unequal prefixes and nested saturated runs, so the fix does
  not merely recognize one numeral spelling.

## Log

- 2026-08-31: Landed the producer half. `Term::NatLit(u64)` keeps closed
  surface numerals constant-size and evaluates a nonzero literal directly to
  one generic `ContextProgram::Run`; substitution, typing, conversion views,
  reflection, module images, cache identity, `Vec`/`Fin`, and literal-length
  inspection preserve its ordinary `Zero`/`Succ` semantics. A maximum-u64
  declaration plus literal reflexivity checks in effectively zero time under
  a 256 MiB address-space limit. The original maximum-ID FunctionIR probe no
  longer grows toward the OOM killer: under a 4 GiB limit it reaches the
  remaining recursive-order stack overflow in about three seconds. Thus the
  23.88 GiB observation belonged primarily to unary *syntax production*, while
  the earlier 1,000/10,000 stack failures correctly identified the consumer
  problem. The issue remains open for generic synchronous-run cancellation;
  neither `Le` nor FunctionIR received a name-based rule.

## What it assumes from elsewhere

- **[[succinct-inductive-values]]** owns the run representation itself.  This
  issue owns making a basic recursive consumer preserve that representation's
  asymptotic promise.
