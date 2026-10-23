# Projecting out of a global — design

Deliberate perf round on `issues/elaborator-canonical-type-spelling.md`'s
2026-09-12 charter, design pass. Workload: the generated call certificate
`heather build-x86 examples/x86-native/reused_callee.hthr caller --callee leaf
--arg 21 --arg 1`, release, `--features value-metrics`, furnace,
`--kernel-workers 1`, item timings with the conversion-miss sidecar beside the
table.

The charter's diagnosis survives the fresh measurement: `Sigma`/`El(?)` is the
certificate's second-largest conversion-miss bucket, **14 682 misses / 9.157 s
of a 37.128 s kernel gate**, and it is exactly what the charter said it is — the
kernel's `Fst`/`Snd` rule reconstituting an inline `Σ` and converting it against
the reference `El (app(D#tycode_fn^δ; ā))` that a parameterized record's value
carries. What the trace adds is *which receivers pay it*, and the answer is one
predicate: `project_field`'s `telescoped` guard asks
`receiver_is_neutral(&value)`, that predicate accepts a spine headed by a **local
variable** and nothing else, and every receiver in an x86 certificate is headed
by a **global** — `caller_native_state_28(gprs, flags, stack)`,
`call_stack_access()`, `caller_native_call_20_callee_contract(…)`. So the
certificate takes the fallback walk at every field read of every state, of every
access record, and of every contract, and the library takes the reference route
at the same reads because its receivers are binders.

The fix is one match arm. Measured on the probe at the certificate's own types,
it is **9.2× on the kernel and 46× on evaluator steps** per read in a checking
position, and **1.6×/2.3×** in a computing one; and it reproduces the
variable-receiver route to within 7 % on every counter, which is the
cross-check that it is not buying something new but simply letting the
certificate onto the road the library is already on.

## 1. The before column

Release build with `--features value-metrics`, one kernel worker, furnace
instance of 2026-09-12, warm declaration cache (`--cache-dir
target/native-probe-images`); every number in this document is from that
instance and an implementer's after column must come from one too. Two warm
runs an hour apart agreed to 0.8 % on both headline numbers (47.190/36.934 and
47.477/37.128); the second is the column below.

Whole run: **wall 53.37 s**, RSS 0.94 GB, 3 476 item rows in the
`caller_native_certificate` module. Summed over those rows:

| | before |
| --- | --- |
| item total | **47.477 s** |
| `kernel_gate` | **37.128 s** |
| evaluator steps | **35.43 M** |
| conversion misses | **237 888** |
| conversion shortcut hits | 6 648 742 |
| conversion **memo** hits | **88** |

The sidecar's per-item accounting says conversion misses are **28.103 s of the
37.128 s kernel gate**, spread over 3 358 items, and that *every* miss in the
run is attributed to a certificate item — with the cache warm the library
arrives from its images and elaborates nothing. So "which head pairs miss" and
"where the kernel gate goes" are the same question here, and the bucket table is
the whole story:

| expected / inferred | misses | seconds |
| --- | --- | --- |
| `Id` / `Id` | 2 632 | 11.816 |
| **`Sigma` / `El(?)`** | **14 682** | **9.157** |
| `El^δ` / `Sigma` | 41 639 | 2.072 |
| `Sigma` / `Sigma` | 1 284 | 1.788 |
| `El(?)` / `El(?)` | 4 296 | 0.855 |
| `Vec` / `Sigma` | 23 124 | 0.655 |
| `El(?)` / `Wf` | 9 560 | 0.496 |
| `El(?)` / `Sigma` | 382 | 0.336 |
| `El^δ` / `Sum` | 120 069 | 0.326 |
| `El(?)` / `Sum` | 4 872 | 0.165 |
| `Sigma` / `El^δ` | 559 | 0.139 |
| `El(?)` / `Id` | 59 | 0.082 |

`Sigma`/`El(?)` is **0.62 ms a miss** and **24.7 % of the kernel gate**. It is
not concentrated: **521 items have it as their heaviest bucket, carrying
8.488 s** of the 9.157 s between them — the largest single item's share is
0.098 s. This is a per-site tax, not a hot spot, which is why a structural
change to the route is the only thing that can collect it.

Every family above half a second of item total (`n`, total, kernel, evaluator
steps M, conversion misses):

| family | n | total s | kernel s | steps M | misses |
| --- | --- | --- | --- | --- | --- |
| `byte` | 36 | 4.767 | 3.899 | 2.55 | 34 515 |
| `store_equal` | 54 | 3.621 | 3.057 | 4.86 | 20 986 |
| `successor` | 35 | 2.517 | 2.155 | 2.36 | 9 338 |
| `step` | 19 | 2.507 | 1.605 | 1.15 | 13 811 |
| `byte_page` | 167 | 2.348 | 2.192 | 1.46 | 835 |
| `byte_wrap` | 131 | 2.155 | 2.050 | 1.35 | 393 |
| `stack_allowed` | 36 | 1.664 | 1.582 | 1.22 | 1 316 |
| `return_read` | 32 | 1.477 | 1.268 | 1.94 | 1 664 |
| `store_address` | 48 | 1.061 | 0.893 | 1.20 | 5 808 |
| `byte_present` | 167 | 1.026 | 0.686 | 0.14 | 9 018 |
| `store_offset` | 48 | 0.983 | 0.938 | 0.77 | 48 |
| `leaf_fetch` | 16 | 0.974 | 0.714 | 0.57 | 5 074 |
| `read_literal` | 32 | 0.962 | 0.844 | 0.91 | 816 |
| `write_permission` | 48 | 0.900 | 0.695 | 1.05 | 1 632 |
| `rsp` | 35 | 0.817 | 0.724 | 1.11 | 5 436 |
| `byte_found` | 167 | 0.751 | 0.393 | 0.02 | 501 |
| `write_literal` | 48 | 0.748 | 0.680 | 0.55 | 240 |
| `stack_permissions` | 10 | 0.676 | 0.518 | 0.60 | 3 752 |
| `code_drop` | 168 | 0.653 | 0.367 | 0.03 | 335 |
| `call_20_callee_applied` | 1 | 0.651 | 0.228 | 0.18 | 2 034 |
| `trace` | 36 | 0.646 | 0.065 | 0.04 | 675 |
| `literal_permissions` | 6 | 0.624 | 0.538 | 0.69 | 1 890 |
| `call_10_callee_applied` | 1 | 0.578 | 0.167 | 0.10 | 1 833 |
| `leaf_summary_suffix` | 9 | 0.573 | 0.191 | 0.30 | 1 277 |
| `store_byte` | 48 | 0.562 | 0.445 | 0.60 | 4 624 |
| `read_address` | 32 | 0.557 | 0.532 | 0.45 | 28 |
| `return_value` | 4 | 0.539 | 0.446 | 0.63 | 880 |
| `return_reads` | 4 | 0.518 | 0.462 | 0.74 | 608 |
| `call_20_callee_local_outside` | 8 | 0.513 | 0.481 | 0.38 | 568 |
| `call_10_callee_local_outside` | 8 | 0.502 | 0.471 | 0.38 | 568 |

and the ones below it that this round names:

| family | n | total s | kernel s | steps M | misses |
| --- | --- | --- | --- | --- | --- |
| `call_20_callee_ready` | 9 | 0.476 | 0.311 | 0.15 | 6 002 |
| `call_10_callee_ready` | 9 | 0.475 | 0.310 | 0.15 | 6 002 |
| `target_arithmetic` | 28 | 0.423 | 0.331 | 0.25 | 756 |
| `leaf_source_artifact` | 1 | 0.378 | 0.291 | 0.12 | 8 519 |
| `rsp_step` | 35 | 0.371 | 0.268 | 0.33 | 4 742 |
| `file_correct` | 1 | 0.336 | 0.334 | 0.14 | 1 |
| `execution` | 22 | 0.327 | 0.182 | 0.05 | 4 987 |
| `leaf_access` | 16 | 0.311 | 0.179 | 0.20 | 1 244 |
| `leaf_summary` | 1 | 0.304 | 0.202 | 0.13 | 6 865 |
| `memory_same` | 10 | 0.280 | 0.221 | 0.28 | 1 445 |
| `state` | 36 | 0.270 | 0.159 | 0.24 | 738 |
| `stack_bound` | 6 | 0.241 | 0.222 | 0.21 | 798 |
| `rsp_rhs` | 35 | 0.237 | 0.187 | 0.24 | 1 155 |
| `dead_frame_byte` | 1 | 0.236 | 0.231 | 0.05 | 4 |
| `byte_offset` | 167 | 0.236 | 0.173 | 0.20 | 501 |

The comparable column in `docs/call-memory-read-spelling-design.md` §1 was
49.06 s / 39.10 s on a cold cache before that round landed; this one is
47.48 s / 37.13 s warm after it. The families moved as that document predicted
(`read_literal` 4.724 → 0.962) and the certificate's total did not, because the
`Sigma`/`El(?)` tax is charged per *site* and the sites did not go away.

## 2. The unit: a projection out of a global

### 2.1 What the kernel is asked

`typing.rs` (~1630–1700) types a projection by rebuilding the pair's type from
the node's own annotations and checking the receiver against it:

    Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } =>
        … let sigma = Type::Sigma { fst: fst_ty, snd: snd_ty, … };
          self.tm_check(env, pair, &sigma, …)

When the receiver's inferred type is the instantiation's **reference**, that
`tm_check` ends in `conv_ty(expected = Σ(…). …, inferred = El (app(D#tycode_fn^δ; ā)))`
— a cross-head query, so neither the syntactic shortcut nor (see §5) the memo
answers it, and the kernel δ-unfolds the type-code function, β-reduces it at
`ā`, decodes, and compares component-wise.

### 2.2 Where the elaborator chooses

`crates/elab/src/inductive.rs` ~2549–2573:

    let telescoped = !ind.params.is_empty() || !ind.valparams.is_empty();
    if (!telescoped || receiver_is_neutral(&value))
        && let Some(args) = self.instance_args(cx, ind, record_ty)
        && let Some(t) = self.rec_proj_ref_at(cx, ind.tag, idx, &args, &value)
    { return Ok(t); }

and `receiver_is_neutral` (`inductive.rs:4849`):

    Term::Var(_) => true,
    Term::Fst { pair, .. } | Term::Snd { pair, .. } => receiver_is_neutral(pair),
    Term::App { fun, .. } => receiver_is_neutral(fun),
    _ => false,

`Term::GlobalTm` is not an arm, so an `App` spine bottoming out at a global is
**not** neutral, and neither is a bare nullary global. That is every receiver
the generator writes: `crates/cli/src/native/calls.rs:463` spells each state as
`{prefix}_state_{i}(gprs, flags, stack)`, and the access and contract records
arrive as `call_stack_access()`, `call_fetch_access()`,
`{instance}_callee_contract(gprs, flags, stack)`. The generator builds **no**
kernel terms directly for these: every one of them is surface `recv.field`
text, elaborated by `project_field`. There is nothing to change in
`crates/cli/src/native/*` and nothing to change in `lib/`.

The three record families that pay are exactly the telescoped, non-dependent
ones `docs/per-instantiation-type-codes-design.md` §13.6 already named as the
measured payers — `MachineState<M>` (`lib/std/arch/x86_64/x86_64.hthr:91`),
`StackAccess<M>` (`calls.hthr:12`), `NativeIntegerCallContract<M, A>`
(`call_frame.hthr:67`) — and they are the ones for which `register_rec_projs`
*did* register the simple device. The definitions exist. The certificate is
just not allowed to use them.

`CallMemory` (`lib/std/os/linux/elf64_calls.hthr:30`) is closed and non-dependent, so
`register_rec_projs` declines it by design (§13.3: a non-dependent closed spine
is linear already), and `memory.file` / `memory.stack` land in the
`El^δ`/`Sigma` bucket — 41 639 misses for 2.072 s, 0.05 ms each. Out of scope,
§6.

### 2.3 The trace

`HEATHER_CONV_MISS_TRACE=caller_native_return_reads_28` (152 misses, 0.091 s
untraced; traced item time is ~2× and families must be compared from the
untraced TSV only), reduced by (head pair, site, term[:120], expected length)
and summed by ms:

| ms | n | site | term | lengths |
| --- | --- | --- | --- | --- |
| 5.19 | 8 | `App < Snd⁸ < Fst < Fst < App⁴ < Pair` | `app(app(app(u124^{·^3}; …` | exp 291, inf 59 |
| 5.18 | 8 | `App < Snd⁸ < Fst < Fst < App⁵` | `app(app(app(u124^{·^4}; …` | exp 291, inf 59 |
| 5.16 | 8 | `App < Snd⁸ < Fst < Fst < App⁵` | `app(app(app(u124^{·^6}; …` | exp 292, inf 59 |
| 3.51 | 8 | `GlobalTm < Snd < Snd < Fst < Fst < App¹⁰ < Pair` | `u3053^{·^6}` | exp 805, inf 59 |
| 3.49 | 8 | `GlobalTm < Snd < Snd < Fst < Fst < App⁸ < Pair³` | `u3053^{·^5}` | exp 802, inf 59 |
| 3.37 | 6 | `GlobalTm < Snd < Snd < Fst < Fst < App⁴ < Pair⁷` | `u3053^{·^3}` | exp 800, inf 59 |

(remaining rows are the same two shapes at other depths; the same reduction on
`caller_native_call_20_callee_memory_effects` gives one shape only, `App < Snd <
Snd < Fst < Fst < App…`, exp 291–295 / inf 59, 0.63 ms a miss.)

Two receiver kinds, and nothing else:

- **`App`-headed** (`u124^{·^k}` applied to three arguments): a generated state
  function. The `Σ` it is checked against is 291–295 characters — `MachineState`'s
  four fields at `CallMemory`. 0.63 ms a miss.
- **`GlobalTm`** with no arguments (`u3053^{·^k}`): `call_stack_access()`. Its
  `Σ` is **800–805** characters — `StackAccess<CallMemory>`'s four *function*
  fields — and it is 0.44 ms a miss even though the receiver is a single node,
  because what costs is stating and comparing the record type, not the
  receiver.

The inferred side is 59 characters in every row: the reference. The expected
side is 291 or 800: a whole record spelled out. **What is closed and repeated
is the record type, and it is re-spelled once per projection node.** The `·^k`
suffixes say the same closed pair recurs at binder depths 3 through 16 within a
single item, which is why §5's memo cannot collect it.

### 2.4 The probe

`probes/t_real_*.hthr` rebuild the certificate's own shape at the certificate's
own types: a 24-link chain of `MachineState<CallMemory>` states, each built by a
named global function out of the previous link's `gprs`, `flags` and `memory`,
over `probes/arch` (the `lib/std/arch/x86_64/*.hthr` files renamed to the module
names `crates/cli/src/native.rs`'s `SUPPORT` table bundles them under, so that
`heather check` can resolve `import x86_64;`), plus `-L lib/std -L lib`. Twenty
four theorems, one per link. `t_*_named` is the proposed spelling emulated in
surface syntax — `fn p_gprs(s: MachineState<CallMemory>) → Gprs { s.gprs }` and
a use site that applies it — which is exactly the term `rec_proj_ref_at` emits,
`app(D#projⱼ^δ; ā, v)`, including its δ+β at evaluation.

| probe | route | total s | kernel s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| `t_real_app` | today: inline `.gprs` off a global-app receiver | 0.0867 | **0.0563** | 105 480 | 504 |
| `t_real_named` | proposed: the projection behind a name | 0.0184 | **0.0061** | 2 304 | 432 |
| `t_real_var` | control: a *variable* receiver (already the reference route) | 0.0269 | **0.0057** | 2 304 | 432 |
| `t_real_compute` | today, computing position (read a stack byte through `.memory`) | 0.1210 | 0.0831 | 119 532 | 120 |
| `t_real_named_compute` | proposed, computing position | 0.0818 | 0.0515 | 52 248 | 72 |

**9.2× on the kernel and 46× on evaluator steps** in a checking position;
**1.6× and 2.3×** in a computing one. And `t_real_named` reproduces
`t_real_var` to the counter — identical steps, identical misses, kernel within
7 % — which is the cross-check that the mechanism is not a new trick but the
route the library already takes.

The miss *count* barely moves (504 → 432) while the miss *cost* collapses:
what goes away is the handful of 0.6 ms `Sigma`/`El(?)` queries, and what stays
is the cheap `El^δ`/`Sum`-class residue. A round that reports only miss counts
would call this change a 14 % win. It is not; read the seconds.

The same comparison on a synthetic four-field record with trivial field types
(`probes/t_proj_app.hthr` / `t_proj_named.hthr` / `t_proj_var.hthr`, 12
theorems) gives 0.0008 / 0.0002 / 0.0002 s of kernel and 36 / 0 / 0 misses: the
route difference is the same, the *unit* is ~36× smaller, and that is the whole
reason the probe had to be rebuilt at `MachineState<CallMemory>` before any
projection was believed.

## 3. The mechanism

### 3.1 What to change

`crates/elab/src/inductive.rs:4849`, one arm, and the predicate's name and
doc comment with it:

    fn receiver_is_opaque(value: &Term) -> bool {
        match value {
            Term::Var(_) => true,
            Term::GlobalTm { .. } => true,
            Term::Fst { pair, .. } | Term::Snd { pair, .. } => receiver_is_opaque(pair),
            Term::App { fun, .. } => receiver_is_opaque(fun),
            _ => false,
        }
    }

The predicate the `telescoped` guard wants is not "this receiver is stuck" but
"**the kernel cannot see a pair here without a δ-step**", and a global is as
opaque to the `Fst`/`Snd` rule as a variable is. The comment at
`project_field` says the telescoped device is asked first because "the
definitions buy a syntactic comparison and charge δ + β for a computation"; the
δ + β is charged against the *body*, and a receiver whose head is a global
already sits behind one. §4 measures the one case where the body is in fact
visible — a literal — and that case keeps the fallback.

Nothing else moves. `instance_args` already has both routes (the receiver's own
reference spine, or §4.1's hole match) and already runs on this path for
unparameterized records; `rec_proj_ref_at` already reads the Π back out of Ψ
and rescopes it. No new definitions are registered, no library theorem changes,
no generator string changes.

### 3.2 Projected saving

The `Sigma`/`El(?)` bucket is 9.157 s, of which 8.488 s sits in the 521 items
that have it as their heaviest bucket. The probe removes the bucket entirely
rather than shrinking it, and removes elaborator time with it (`t_real_app`
0.0867 s total against 0.0563 s kernel — the fallback walk pays ~0.030 s of
elaboration to build the annotations it then makes the kernel check; the named
route pays 0.012 s).

Scaling the certificate by the probe's split, and discounting for the misses
that belong to records the change does not reach:

| | before | projected |
| --- | --- | --- |
| `kernel_gate` | 37.128 s | **28.5 – 30.0 s** (−19 % to −23 %) |
| item total | 47.477 s | **36.5 – 39.0 s** |
| `Sigma`/`El(?)` misses | 14 682 | under 1 500 |
| `Sigma`/`El(?)` seconds | 9.157 | under 1.0 |
| evaluator steps | 35.43 M | 26 – 31 M |

The families that should move are the 521 items' families — `step`,
`return_reads`, `return_value`, `literal_permissions`, `call_*_callee_*`,
`memory_same`, `state`, `rsp*`, `leaf_access`. The families whose heaviest
bucket is `El^δ`/`Sigma` or `Id`/`Id` (`byte`, `store_equal`, `byte_page`,
`byte_wrap`, `file_correct`, `dead_frame_byte`) should **not** move, and a run
in which they do is a run worth reading before shipping.

### 3.3 What else meets this type

A spelling change here changes two things a reader can be looking at: the shape
of a projection **term**, and the route by which a record's **reference** is
consumed. The rule from the bar is that every reader of either is listed and
checked. All of these already see the reference form for variable receivers;
what is new is seeing it for global-headed ones.

Readers that match on a `Fst`/`Snd` chain and will now find
`app(D#projⱼ^δ; ā, v)` at sites that used to be a chain:

- `crates/elab/src/matching.rs:616` (`stuck_scrutinees`) and `:659`
  (`field_rewrap`) — the match-motive synthesis, which abstracts a projection of
  a scrutinee and rewraps the receiver as a pair. This is the one with real
  exposure: a `case` on `foo().field` is exactly the shape that changes.
- `crates/elab/src/oracle.rs:260` — the omega oracle's scrutinee unwrap.
- `crates/elab/src/certgen.rs:2284` — `Term::Fst { pair, .. } if wfarm.is_some()`.
- `crates/elab/src/wf.rs:2413` and `:2451` — the `Wf` link reader and builder.
- `crates/elab/src/forded.rs:151` — forded-index reading.
- `crates/elab/src/lgg.rs:643–657` — anti-unification; two projections
  generalize only if both are chains or both are references.
- `crates/elab/src/emission_walk.rs:255` — the `Fst`/`Snd` annotation slots.
  Its finding count should *fall*: a reference carries no component annotation
  to respell. A rise is a defect.

Readers of the record's reference, all of which this change routes *more*
traffic through and none of which it changes:

- `gendefs.rs:1616 instance_args` (spine route and `instance_match` route),
  `:1574 rec_proj_ref_at`, `:2318 unspell_here`, `:2015 emit_ty`,
  `:1769 respell_ty`.
- `inductive.rs:1693 tag_of` and `dispatch/member.rs:60 record_of_at`.
- Every `project_field` caller, which is where a regression would surface as a
  changed elaboration rather than a changed proof: `lib.rs:904`, `:5979`,
  `:6060`, `:6085`; `dispatch/receiver.rs:187`; `dispatch/projection.rs:156`,
  `:278`; `dispatch/member.rs:68`; `relational_context/proof.rs:224`;
  `wf.rs:3080`, `:3103`, `:3203`.

## 4. Refuted: dropping the literal-receiver exception

The obvious simplification of §3.1 is to delete the guard rather than widen it
— always take the reference when one is registered. `project_field`'s comment
says the telescoped device is *not* asked for a literal receiver on purpose.
Measured, both ways, on the synthetic record in a computing position
(`probes/t_proj_lit.hthr` and `probes/t_proj_lit_named.hthr`, 12 theorems each,
`St(i, 0, i, Mem(1, stack)).rip = i` by `refl`):

| probe | route | total s | kernel s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| `t_proj_lit` | today: the fallback walk on a literal receiver | 0.0019 | **0.0008** | 288 | 36 |
| `t_proj_lit_named` | the reference at a literal receiver | 0.0019 | **0.0012** | **732** | 60 |

**1.5× worse on the kernel and 2.5× worse on evaluator steps.** With the pair
in front of it the `Fst` rule's reconstituted `Σ` is met by the literal's own
annotations and β-reduces in one step; behind `D#projⱼ` the kernel must δ-unfold
the projection and *then* β, and the annotation it has to check is the whole
record either way. The comment is right and the guard stays. Widen the
predicate; do not delete it.

This is also why the arm to add is `Term::GlobalTm`, not a general "anything
that is not a `Pair`": a `Term::Pair` is the case measured above, and the other
non-neutral heads (`Case`, `ElimNat`, `J`, …) are not receivers a record field
read reaches in any workload here and should not be given a route on a guess.

## 5. Not taken: one shared `Rc` for the repeated annotation

The charter asks whether emitting a single shared `Rc` for a repeated closed
annotation would make the kernel's existing conversion memo hit, with no kernel
change. The memo's bucket key (`typing.rs:684–700`, `type_anchor` at `:2456`)
is the two head discriminants plus an **`Rc` pointer identity** of each side's
principal child — the `Σ`'s `fst`, the `El`'s `tm` — plus the `Ψ`/`Γ`
identities, the layer and the level. Two structurally equal but separately
allocated annotations land in different buckets and never meet.

The premise reproduces. `probes/t_proj_repeat.hthr` puts **four identical
closed projections at one binder depth in one item**, twelve times:

| probe | items | misses | memo hits |
| --- | --- | --- | --- |
| `t_proj_repeat` | 12 | 108 | **0** |

and the certificate agrees: **88 memo hits against 237 888 misses.** The trace
of §2.3 shows the same key recurring `n = 8` times inside one item, so the
repeats are real and a shared `Rc` would plausibly convert seven of every eight
into hits.

It is still not this round's mechanism, for two reasons and one measurement.
First, the repeats that share a `Γ` are a minority: §2.3's keys span binder
depths `·^3` to `·^16` within a single item, and the memo requires
`entry.gamma == env.gamma`, so a shared annotation cannot bridge them. Second
and decisive: §3 **removes** these queries rather than memoizing them —
`t_real_named` does not issue the 0.6 ms query at all — and a mechanism that
makes a removed cost cheaper is worth nothing on top of it. Hash-consing the
emission chokepoint's output is a real idea with its own reach (it would touch
every bucket, not this one), and it belongs to
[[emission-spelling-chokepoint]] with its own before column. It is not in this
round, and §3 must not be blocked on it.

## 6. Out of scope

- **`Id`/`Id`, 11.816 s, the largest bucket.** Two items carry 0.56 s of it
  (`file_correct`, `dead_frame_byte`) and the rest is spread over the `byte`
  and `step` families: endpoint conversion of large closed equalities, which is
  the evaluator's problem and not a spelling one. Its own round.
- **`El^δ`/`Sigma`, 41 639 misses / 2.072 s.** `CallMemory`'s two fields, at
  0.05 ms a miss. Registering the closed non-dependent device would collect it,
  against `docs/per-instantiation-type-codes-design.md` §13.3's explicit
  reasoning that such a spine is linear already. 2 s is not enough to reopen
  that decision; file it if it survives §3.
- **The quote layer's closed boxed literal**
  ([[emission-walker-residual-sites]]). The charter admits it only if the trace
  attributes the bucket to it. It does not: every `Sigma`/`El(?)` row in §2.3
  has a 59-character reference on the inferred side and a spelled-out record on
  the expected one, which is the `Fst`/`Snd` rule, not a quote.
- **The kernel-side sibling**, `issues/conversion-typed-eliminator-congruence.md`
  — a `Fst`/`Snd` rule that did not have to reconstitute the `Σ` at all would
  make this bucket structurally impossible. Not designed here and not needed:
  the elaborator can keep the query from being asked.
- **`byte_page`, `byte_wrap`** (4.24 s of kernel over 298 items): closed 48- and
  64-bit compares by `refl`, [[kernel-native-bitvector-values]]'s shape.

## 7. The bar

Measured on one furnace instance, before and after, release,
`--features value-metrics`, `--kernel-workers 1`, warm `--cache-dir`, the same
`--timings` invocation as §1.

1. **Whole certificate: item total at or below 47.477 s and `kernel_gate` at or
   below 37.128 s**, with §3.2's projection being ~37 s and ~29 s. A result
   within a second of the before column means the change did not land; re-read
   §2.2 before shipping it.
2. **Every family row of §1 recorded again**, not only the ones that moved. The
   point of the table is that a rise elsewhere is visible, and §3.3 lists nine
   readers that could produce one.
3. **The `Sigma`/`El(?)` bucket's misses and seconds, before and after**:
   14 682 / 9.157 s → under 1 500 / under 1.0 s. Report the whole bucket table
   both times; a bucket that grew while this one shrank is the interesting
   result.
4. **Full plain `scripts/test`, green** — not `--fast`. Nothing here touches
   `lib/` or the generators, but the elaborator's projection route is what the
   semantic images were written by, so the images must be rebuilt and
   `crates/cli/tests/native*.rs` and the perturbed-library mutation controls
   must pass.
5. **The refusal controls in `crates/cli/src/native/calls.rs` still refuse**:
   `stale_summary`, `wrong_summary_interface`, `missing_summary_fetch`,
   `invented_successor`, `overlapping_word`, `live_slot_cannot_change`,
   `return_slot_cannot_change`. A projection route that lets any of these
   through is the failure mode this change can have.

**If the bar fails, STOP and report; do not land.**

## 8. Verification items

For the implementing pass's first hour. **If one of these refutes the design,
STOP and report before working around it.**

1. Reproduce §2.4's split before writing any Rust:
   `heather check -L probes/arch -L lib/std -L lib --kernel-workers 1 --timings`
   on `probes/t_real_app.hthr` and `probes/t_real_named.hthr`, wrapped
   (`ulimit -v 8388608 -t 600`). The 0.0563 s / 0.0061 s gap is the whole basis
   of §3.2. If it is not there on the implementer's instance, the box changed
   and every projection needs redoing. `probes/arch` is rebuilt by
   `probes/run_probes4.sh`'s first lines.
2. Confirm the guard is what decides, in the compiler rather than in a probe:
   instrument or log `project_field`'s two exits on the certificate and check
   that the fallback branch is taken for `MachineState`, `StackAccess` and
   `NativeIntegerCallContract` and the reference branch for the same records in
   `lib/`. If the certificate is already taking the reference branch somewhere,
   §2.2 is incomplete and the remaining payer has to be found first.
3. `crates/elab/tests/record_projection_size.rs` — the eleven-field
   cross-referencing record whose fallback walk is a 4 GiB abort
   (`docs/per-instantiation-type-codes-design.md` §13.10). It is *dependent* and
   so has no registered projections; the widened predicate must not change what
   it does. Run it first, alone, before the full suite.
4. `crates/elab/src/wf.rs:3155`'s `Cell` self-check already exercises
   `instance_args` + `rec_proj_ref_at` directly; it should be untouched. If it
   moves, the predicate change reached further than §3.1 claims.
5. Run the emission walker on the five-node x86 module before and after
   ([[emission-walker-residual-sites]]'s top table). The finding count must
   **fall** — a reference carries no component annotation — and a rise means the
   new route is writing a spelling some slot then respells.
6. Check `matching.rs`'s `field_rewrap` against a `match` on a projection of a
   *global-headed* receiver (a `case foo().field of …` in a probe). It is the
   one reader in §3.3 whose input shape genuinely changes; if it silently stops
   rewrapping, the failure is a worse goal, not an error.

## 9. Result — **refuted; not landed**

Implemented and measured 2026-09-12 on the furnace instance live that
afternoon (age 1 h 38 m at launch; §1's before column reproduced on it to
0.8 %, so the box did not drift). §3.1 was applied exactly as written and
nothing else. **The change makes the certificate stop checking**: the
generated proof `caller_native_memory_same_28` exhausts the kernel's fuel, so
the workload aborts at item 2 991 of 3 476 and there is no after column to
compare. Bar item 1 fails on correctness, not on time. The tree is left dirty
with the edit in place for review; it must not land in this shape.

    BEFORE  wall 53.01 s  rss 0.93 GB  rows 3476  total 47.088 s  kernel_gate 36.842 s
            35.43 M steps  237 888 misses  6 648 742 shortcut hits  88 memo hits
    AFTER   wall 96.72 s  rss 0.84 GB  rows 2991  ABORTED
            error: 18212:1: the kernel rejected `caller_native_memory_same_28`: OutOfFuel
            (partial: total 30.659 s  kernel_gate 22.791 s  13.13 M steps  195 656 misses  424 memo hits)

### 9.1 What refutes §3.1

The predicate's own doc comment — the one §3.1 rewrites — already named this
item and this failure: *"a certificate that chains twenty-eight machine states
through `state.memory` pays that once per read per level: `reused_callee`'s
`caller_native_memory_same_28` needs between 8× and 64× `DEFAULT_FUEL` with the
reference and checks inside it without."* §3.1 read that as an argument about
the *body* — "the δ + β is charged against the body, and a receiver whose head
is a global already sits behind one" — and that reading is wrong in the one
place it matters. The δ-step a global-headed receiver already sits behind is
**one** step, taken once; the reference route adds a **further** δ + β *per
field read per level of the chain*, and `memory_same_28` is twenty-eight levels
of `state.memory` inside one item. The certificate's global-headed receivers
are not merely opaque, they are the deep chain the old comment was written
about, and §2.4's probe did not reproduce that: `t_real_compute` reads one
stack byte through `.memory` at each of 24 *separate* theorems, so no single
item carries the nested chain that exhausts fuel.

`t_real_app`'s 9.2× is real and reproduced on this instance (§9.2), and the
`Sigma`/`El(?)` bucket does collapse as projected (§9.4). The mechanism is
right about the bucket and wrong about the workload: the tax it removes is
paid back, with interest, in evaluation of the chained reads — and past a
point, in fuel.

### 9.2 Verification items

1. **§2.4's split reproduces.** `t_real_app` kernel 0.0589 s, `t_real_named`
   0.0064 s, `t_real_var` 0.0058 s (design: 0.0563 / 0.0061 / 0.0057) — 9.2×,
   and the named route again matches the variable control to the counter.
   `t_real_compute` 0.0842 / `t_real_named_compute` 0.0509. Basis intact.
2. **The guard is what decides, confirmed in the compiler.** A temporary
   `HEATHER_PROJ_LOG` on `project_field`'s two exits, aggregated by
   (branch, record, receiver head), on the warm certificate:
   `fallback MachineState head=GlobalTm` 1 346, `fallback StackAccess
   head=GlobalTm` 370, `fallback CallMemory head=GlobalTm` 95, against
   `reference MachineState head=Var` 489 and `reference StackAccess head=Var`
   214. The same build on the library (`x86_64_call_frame`, cold) is the
   mirror image: `reference MachineState head=Var` 193, `reference StackAccess
   head=Var` 126, with only 22 global-headed `MachineState` fallbacks. §2.2 is
   exact. (The instrumentation was reverted before any measurement.)
3. **`record_projection_size` unaffected**: `== suite: 11 passed, 0 failed, 0
   ignored ==`. The dependent eleven-field record has no registered
   projections and the widened predicate does not reach it.
4. **`wf.rs`'s `Cell` self-checks unaffected**: `scripts/test -p heather-elab
   --lib wf::` → `== suite: 55 passed, 0 failed, 0 ignored ==`.
5. **Emission walker unchanged, not fallen**: the five-node FunctionIR/x86
   module lists **260 findings before and 260 after**, slot for slot
   (`Pair.fst_ty` 120, `Pair.snd_ty` 120, `App.cod` 14, `App.dom` 3,
   `ElimNat.motive` 3). §3.3 predicted a fall; there is none, because the
   module's residue is the quote layer's closed boxed literal and carries no
   `Fst`/`Snd` slots to begin with. Not a rise, so not a defect — but not the
   predicted evidence either, and `WALK_RESIDUE` in
   `crates/elab/tests/ir_v1.rs` is therefore **unchanged**.
6. **`field_rewrap` survives the new input shape.** `probes/t_case_global.hthr`
   — `match b0().tag { … }`, `match b1(n).tag { … }` and a variable-receiver
   control, five theorems — checks with the change applied (c0–c4 ok, 8–12
   evaluator steps each). The one reader with real exposure is fine.

### 9.3 Every family of §1, before and after

The after column is **over a truncated run**: items after
`caller_native_memory_same_28` were never elaborated, so a family whose `n`
fell did not get faster, it got cut off, and families present only in the after
column are rows that fell outside the before listing's top sixty. The table is
recorded for bar item 2 and is not a like-for-like comparison.

| family | n before / after | before s | after s | before kernel s | after kernel s | after misses |
| --- | --- | --- | --- | --- | --- | --- |
| `byte` | 36 / 28 | 4.768 | 3.797 | 3.909 | 3.154 | 26759 |
| `store_equal` | 54 / 54 | 3.589 | 1.173 | 3.029 | 0.733 | 17668 |
| `successor` | 35 / 28 | 2.502 | 1.809 | 2.147 | 1.557 | 7209 |
| `step` | 19 / 12 | 2.462 | 1.450 | 1.577 | 0.820 | 9683 |
| `byte_page` | 167 / 131 | 2.292 | 1.846 | 2.141 | 1.725 | 655 |
| `byte_wrap` | 131 / 103 | 2.119 | 1.708 | 2.019 | 1.625 | 309 |
| `stack_allowed` | 36 / 18 | 1.598 | 0.805 | 1.518 | 0.765 | 658 |
| `return_read` | 32 / 16 | 1.487 | 0.139 | 1.279 | 0.080 | 32 |
| `store_address` | 48 / 48 | 1.058 | 0.362 | 0.893 | 0.216 | 4992 |
| `byte_present` | 167 / 131 | 1.026 | 0.817 | 0.688 | 0.557 | 7074 |
| `leaf_fetch` | 16 / 16 | 0.967 | 0.688 | 0.712 | 0.475 | 4738 |
| `read_literal` | 32 / 16 | 0.949 | 0.217 | 0.834 | 0.190 | 16 |
| `store_offset` | 48 / 48 | 0.949 | 0.995 | 0.907 | 0.950 | 48 |
| `write_permission` | 48 / 48 | 0.903 | 0.162 | 0.697 | 0.074 | 576 |
| `rsp` | 35 / 28 | 0.821 | 0.153 | 0.728 | 0.093 | 3744 |
| `byte_found` | 167 / 131 | 0.750 | 0.591 | 0.393 | 0.320 | 393 |
| `write_literal` | 48 / 48 | 0.742 | 0.650 | 0.676 | 0.612 | 144 |
| `stack_permissions` | 10 / 8 | 0.682 | 0.254 | 0.524 | 0.146 | 3192 |
| `call_20_callee_applied` | 1 / 1 | 0.669 | 0.853 | 0.237 | 0.396 | 1958 |
| `trace` | 36 / — | 0.653 | — | 0.066 | — | — |
| `code_drop` | 168 / 168 | 0.649 | 0.771 | 0.365 | 0.455 | 335 |
| `literal_permissions` | 6 / 6 | 0.627 | 0.211 | 0.543 | 0.165 | 1290 |
| `leaf_summary_suffix` | 9 / 9 | 0.568 | 0.884 | 0.193 | 0.235 | 1277 |
| `store_byte` | 48 / 48 | 0.561 | 0.220 | 0.445 | 0.114 | 4216 |
| `return_value` | 4 / 2 | 0.556 | 0.072 | 0.463 | 0.039 | 208 |
| `call_10_callee_applied` | 1 / 1 | 0.555 | 0.561 | 0.165 | 0.121 | 1784 |
| `read_address` | 32 / 16 | 0.548 | 0.262 | 0.522 | 0.250 | 14 |
| `return_reads` | 4 / — | 0.514 | — | 0.461 | — | — |
| `call_20_callee_local_outside` | 8 / 8 | 0.498 | 0.443 | 0.468 | 0.414 | 488 |
| `call_10_callee_local_outside` | 8 / 8 | 0.493 | 0.429 | 0.462 | 0.401 | 488 |
| `call_20_callee_ready` | 9 / 9 | 0.482 | 0.376 | 0.311 | 0.237 | 5922 |
| `call_10_callee_ready` | 9 / 9 | 0.475 | 0.374 | 0.311 | 0.235 | 5922 |
| `target_arithmetic` | 28 / 23 | 0.418 | 0.321 | 0.326 | 0.259 | 638 |
| `leaf_source_artifact` | 1 / 1 | 0.381 | 0.569 | 0.293 | 0.484 | 8519 |
| `rsp_step` | 35 / 28 | 0.371 | 0.129 | 0.268 | 0.080 | 3491 |
| `execution` | 22 / — | 0.331 | — | 0.187 | — | — |
| `file_correct` | 1 / 1 | 0.329 | 0.354 | 0.326 | 0.351 | 1 |
| `leaf_access` | 16 / 16 | 0.303 | 0.181 | 0.178 | 0.059 | 1100 |
| `leaf_summary` | 1 / 1 | 0.291 | 0.337 | 0.197 | 0.233 | 6856 |
| `memory_same` | 10 / 9 | 0.277 | 0.860 | 0.219 | 0.813 | 1252 |
| `state` | 36 / 29 | 0.270 | 0.098 | 0.160 | 0.040 | 478 |
| `stack_bound` | 6 / 5 | 0.240 | 0.126 | 0.221 | 0.111 | 580 |
| `rsp_rhs` | 35 / 28 | 0.237 | 0.075 | 0.187 | 0.042 | 771 |
| `dead_frame_byte` | 1 / — | 0.237 | — | 0.233 | — | — |
| `byte_offset` | 167 / 131 | 0.232 | 0.194 | 0.169 | 0.142 | 393 |
| `word` | 98 / 98 | 0.231 | 0.198 | 0.116 | 0.129 | 18914 |
| `target` | 10 / — | 0.197 | — | 0.164 | — | — |
| `store_byte_literal` | 48 / 48 | 0.194 | 0.205 | 0.167 | 0.175 | 48 |
| `store_value` | 6 / 6 | 0.186 | 0.179 | 0.174 | 0.169 | 100 |
| `call_20_callee_return_outside` | 1 / 1 | 0.176 | 0.149 | 0.169 | 0.143 | 151 |
| `call_10_callee_return_outside` | 1 / 1 | 0.175 | 0.142 | 0.168 | 0.136 | 151 |
| `byte_next` | 131 / 103 | 0.167 | 0.142 | 0.116 | 0.103 | 103 |
| `result_at` | 7 / — | 0.165 | — | 0.145 | — | — |
| `call_20_callee_memory_effects` | 1 / — | 0.158 | — | 0.145 | — | — |
| `call_10_callee_memory_effects` | 1 / — | 0.155 | — | 0.141 | — | — |
| `return_outside_protected_offset` | 8 / 8 | 0.138 | 0.158 | 0.132 | 0.149 | 8 |
| `return_outside_written_offset` | 8 / 8 | 0.137 | 0.155 | 0.132 | 0.146 | 8 |
| `local_outside_written_offset` | 8 / 8 | 0.136 | 0.155 | 0.129 | 0.145 | 8 |
| `local_outside_protected_offset` | 8 / 8 | 0.136 | 0.158 | 0.129 | 0.148 | 8 |
| `local_outside_excluded` | 72 / 72 | 0.120 | 0.128 | 0.067 | 0.074 | 456 |
| `store_memory` | — / 54 | — | 0.097 | — | 0.046 | 96 |
| `leaf_instructions` | — / 3 | — | 0.119 | — | 0.024 | 36 |
| `leaf_summary_code` | — / 1 | — | 0.150 | — | 0.042 | 303 |
| `rsp_arithmetic` | — / 3 | — | 0.088 | — | 0.083 | 3 |
| `header_from` | — / 233 | — | 0.092 | — | 0.042 | 699 |
| `code_from` | — / 168 | — | 0.068 | — | 0.031 | 504 |
| `store_sub` | — / 3 | — | 0.072 | — | 0.068 | 3 |
| `return_outside_excluded` | — / 72 | — | 0.122 | — | 0.070 | 456 |

The one family to read closely is **`memory_same`: 10 items / 0.277 s before,
9 items / 0.860 s after** — 3.7× the kernel time on *fewer* items, and then the
tenth (`_28`) runs out of fuel. That is the refutation in the table.
`leaf_source_artifact` (0.293 → 0.484 kernel), `call_20_callee_applied`
(0.237 → 0.396) and `leaf_summary_suffix` (0.193 → 0.235) rise the same way:
they are the items that read deep chains. The families §3.2 predicted would
not move (`byte`, `byte_page`, `byte_wrap`, `file_correct`) indeed did not.

### 9.4 The bucket table, before and after

Both listings are the report's top twenty, so a `—` in one column may mean
"below the cut" rather than "absent"; the after listing is over the truncated
run.

| expected / inferred | before misses | before s | after misses | after s |
| --- | --- | --- | --- | --- |
| `Vec` / `Vec` | 13 | 0.007 | 2812 | 11.817 |
| `Id` / `Id` | 2632 | 11.567 | 3286 | 11.393 |
| `Sigma` / `El(?)` | 14682 | 9.163 | 1657 | 2.570 |
| `Sigma` / `Sigma` | 1284 | 1.778 | 6622 | 5.375 |
| `Sigma` / `El^δ` | 559 | 0.139 | 6048 | 4.312 |
| `El(?)` / `Wf` | 9560 | 0.498 | 19555 | 2.806 |
| `Sigma` / `Vec` | — | — | 5934 | 2.588 |
| `El^δ` / `Sigma` | 41639 | 2.073 | 46045 | 2.266 |
| `El(?)` / `Sigma` | 382 | 0.335 | 8506 | 1.686 |
| `El^δ` / `Sum` | 120069 | 0.326 | 132194 | 1.453 |
| `El⌜⌝` / `El(?)` | 612 | 0.046 | 3346 | 1.236 |
| `El(?)` / `El(?)` | 4296 | 0.842 | 4776 | 1.138 |
| `Vec` / `Sigma` | 23124 | 0.659 | 29709 | 0.995 |
| `Pi` / `Pi` | — | — | 1886 | 0.765 |
| `Fin` / `Sum` | — | — | 2189 | 0.620 |
| `Ty` / `Ty` | — | — | 2553 | 0.578 |
| `El(?)` / `El⌜⌝` | — | — | 428 | 0.302 |
| `El(?)` / `Sum` | 4872 | 0.165 | 5208 | 0.280 |
| `Empty` / `Fin` | — | — | 2380 | 0.224 |
| `El(?)` / `Id` | 59 | 0.079 | 202 | 0.117 |
| `Pi` / `El^δ` | 1179 | 0.051 | — | — |
| `Wf` / `El(?)` | 306 | 0.020 | — | — |
| `Vec` / `Unit` | 10864 | 0.015 | — | — |
| `El^δ` / `Wf` | 137 | 0.012 | — | — |
| `El(?)` / `Unit` | 26 | 0.012 | — | — |
| `Sum` / `El⌜⌝` | 124 | 0.011 | — | — |

`Sigma`/`El(?)` does what §3.2 projected — **14 682 / 9.163 s → 1 657 /
2.570 s**, and the items whose heaviest bucket it is fall from 521 (8.510 s) to
2 (0.007 s) — but the cost did not leave the run, it moved: `Vec`/`Vec`
0.007 → **11.817 s**, `Sigma`/`Sigma` 1.778 → 5.375 s, `Sigma`/`El^δ`
0.139 → 4.312 s, `El(?)`/`Wf` 0.498 → 2.806 s, and a new `Sigma`/`Vec` at
2.588 s. Bar item 3's own words — "a bucket that grew while this one shrank is
the interesting result" — are the finding: **9.157 s of `Sigma`/`El(?)` was
exchanged for well over 20 s elsewhere, in two thirds of a run.** The reference
route does not remove the record comparison; it defers it to a place where the
kernel meets it under evaluation instead of under the `Fst`/`Snd` rule, and
there the chain depth multiplies it.

### 9.5 Deviation from §3.1, and the suite

**No deviation.** The source change is exactly §3.1: `Term::GlobalTm { .. } =>
true` added, `receiver_is_neutral` → `receiver_is_opaque` (three recursive call
sites and the one caller), the predicate's doc comment and `project_field`'s
`telescoped` guard comment amended. No other file's behaviour is touched.

**The full `scripts/test` was not run.** The bar's rule is stop-and-report on
failure, and the failure is that the workload the suite's
`crates/cli/tests/native*.rs` gates check does not build: a suite run would
spend ~20 min re-deriving the `OutOfFuel` already in hand. Bar item 5's refusal
controls are therefore **unverified**. The targeted items that were run are
green: `record_projection_size` `== suite: 11 passed, 0 failed, 0 ignored ==`,
`wf::` `== suite: 55 passed, 0 failed, 0 ignored ==`, and the walker's own
target `test result: ok. 1 passed; 0 failed`.

### 9.6 Files touched

- `crates/elab/src/inductive.rs` — §3.1, the whole change (left in the working
  tree, **not to be landed**).
- `docs/record-projection-reference-design.md` — this section.
- `probes/` — `run_impl_before.sh`, `run_impl_item2.sh`, `run_impl_after.sh`,
  `run_impl_item6.sh` and `t_case_global.hthr` (§9.2 items 2 and 6) added to
  the design pass's set.
- `crates/elab/tests/ir_v1.rs` — **unchanged**: the walker's count did not
  move, so `WALK_RESIDUE` has nothing to remove.

### 9.7 Where this leaves the issue

The measured facts that survive, for whoever picks this up:

- The bucket's attribution (§2) is confirmed in the compiler, not just in a
  probe (§9.2 item 2). `Sigma`/`El(?)` really is every global-headed field read
  of `MachineState`, `StackAccess` and `CallMemory`, and it really is 9.157 s.
- Routing those reads to the reference really does remove the bucket, and
  really does cost more than it removes on this certificate, because the
  certificate's global-headed receivers are **chained** — the receiver is the
  previous link, twenty-eight deep — and each link's reference must be computed
  through by δ + β at every level. A predicate that distinguished a *chained*
  global receiver from a flat one (`call_stack_access()`, the 0.44 ms /
  800-character rows of §2.3, which are not chained at all) is the obvious next
  hypothesis; §2.3's own trace already separates the two shapes, and the flat
  `GlobalTm` half is about a third of the bucket's misses.
- The kernel-side sibling §6 names
  (`issues/conversion-typed-eliminator-congruence.md`) is now the more
  attractive route, not the less: a `Fst`/`Snd` rule that does not reconstitute
  the `Σ` removes the 9.157 s without moving any read off the walk, and so
  cannot pay it back in evaluation.

### 9.8 Addendum (2026-09-13): the owner was the quote, not the rule

§9.7's third bullet — a `Fst`/`Snd` *typing* rule that reads Σ off the
receiver and does not reconstitute — is **not available**. The certificate's
proof terms are checked at layer c (`crates/elab/src/lib.rs`, the kernel
gate's `check_term` call), and at layer c the annotations are load-bearing: the
code recursor's `tm_fst`/`tm_snd` branches (`crates/kernel/src/reduce.rs`,
`crates/kernel/src/rec.rs`) bind `u_p : □(g ⊢ Σ U_S U_T)` with the real pair
substituted in, so a rule that accepted `fst^{S,T}(p)` with `p : Σ S' T'`
unchecked would let the recursor's reduct fail to type. Conversion may ignore
the annotations because it presupposes well-typedness; the typing rule is
where that is established. The query stays.

What the query *costs* is the other half of the datum, which §2.3's trace
could not show because the sampler sees only the root pair: after the kernel
unfolds the reference to a `Σ`, every component meets a differently spelled
twin. The type-code function's body quoted the raw inline lowering
(`register_ty_code_fn`, `code_of(template)`), while the walk's annotation is
the emission chokepoint's respelling of the same components; each component
compare then paid its own δ. Quoting the respelled template instead —
`code_of(emit_ty(template))`, the `docs/per-instantiation-type-codes-design.md`
§5 sentence "quote the type you would emit" applied to the one quote it had
not reached — makes the components syntactically equal after the one unfold.

Measured on one furnace instance (2026-09-13), same recipe as §1, warm
cache, both columns from that box:

| | before | after |
| --- | --- | --- |
| item total | 45.117 s | **35.179 s** |
| `kernel_gate` | 35.296 s | **25.468 s** |
| evaluator steps | 35.43 M | **16.07 M** |
| conversion misses | 237 888 | 237 888 |
| `Sigma` / `El(?)` | 14 682 / 8.622 s | 14 682 / **0.618 s** |
| every other bucket | — | unchanged or slightly cheaper |

The miss *count* is identical to the row: no read moved, no query was
removed, and no bucket grew — the opposite of §9's table. The elaborator's
predicate (`receiver_is_neutral`, §2.2) and the reference route are untouched;
the certificate's global-headed receivers keep the walk, and the walk's query
is now cheap. The 0.6 s that remains is the single δ + β + decode per read.
