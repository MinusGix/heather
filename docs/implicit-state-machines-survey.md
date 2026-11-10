# Implicit state machines in the kernel and the elaborator — survey

Survey of 2026-11-02 over master `53ee29a`. Scope: places in `crates/kernel`
and `crates/elab` where a phase or mode is carried by flags, `Option` fields,
the order of calls, or invariants of the form "X is set only after Y", rather
than by an explicit state type. For each: where it is, the states and
transitions as they exist, the invariants it leans on, what has gone or could
go wrong because it is implicit, and whether an enum or typestate would pay.

**Second pass (2026-11-08):** `docs/kernel-implicit-state-review.md` reads the
kernel alone, re-checks §3 and §6, and adds five kernel findings.

A sibling survey looks at the same code from the data-oriented-design side.
The two meet wherever a struct's *fields* are regrouped: §1 (the Elaborator's
field lifetimes) and §10's memo tables are the overlap. This survey only asks
which state is reachable and who is allowed to move it; layout and access
patterns are the other survey's.

## Ranking

| # | Finding | Where | Evidence it bites | Make explicit? | Issue |
|---|---------|-------|-------------------|----------------|-------|
| 1 | Elaborator field lifetimes | `crates/elab/src/lib.rs` `Elaborator` | a real defect (`restore_from_clone` dropped the live pool) | **yes** | [[elab-field-lifetimes-explicit]] |
| 2 | Module pass: parallel → discard → serial replay | `lib.rs` `elab_module_source`, `check_module_source_inner`, `pool.rs` | a real defect (a nested join took the pass's outcomes) | **yes** | [[module-pass-state-machine]] |
| 3 | Ψ-bound `GlobalCache` | kernel `typing.rs`/`conv.rs` `Env`, `reduce.rs` `Defs` | none found; soundness-relevant, in the TCB, reachable from a `pub` API | **yes**, cheap | [[kernel-psi-bound-cache]] |
| 4 | Declaration attempt lifecycle and `delta_psi` | `attempt.rs`, `goals.rs` `GoalArena`, `refresh_delta_psi` | none found; protocol copied by hand at five sites | **yes** | [[decl-attempt-lifecycle]] |
| 5 | Goal slot state | `goals.rs` `Goal` | none found; 8 field combinations, 4 meaningful | **yes**, cheap | [[goal-slot-state-enum]] |
| 6 | Kernel checker mode | `typing.rs` `Tc` | none found; 16 combinations, 4 modes | yes, modest | [[kernel-checker-mode-enum]] |
| 7 | "Under a quotation" held in three places | kernel `Env::under_box`, `Cx::quoted`, `Elaborator::quote_depth` (+ `Cx::meta`/`meta_pushed`) | the second copy exists because a fresh `Cx` lost the first | fold into #1 | — |
| 8 | Hand-restored dynamic scopes | ~15 `Elaborator` fields | none today; three reset instead of restoring | fold into #1 | — |
| 9 | Small latches and pairs | see §9 | none | no | — |
| 10 | Already explicit, or deliberately not | see §10 | — | — | — |

Ranking weighs: a defect already happened > soundness/TCB > number of hand-kept
sites > size of the change.

## 1. The Elaborator's field lifetimes

**Where.** `Elaborator` (`crates/elab/src/lib.rs` ~610–815) carries ~60
fields. Read by lifetime, they fall into six classes that the type does not
name:

| Class | Fields (examples) | Clone rule | Rollback rule |
|-------|-------------------|------------|---------------|
| Committed world | `committed: Rc<CommittedWorld>` (Ψ, δΨ, names, types, traits, …) | shared, COW | `SessionCheckpoint::restore` |
| Module pass | `kernel_pool`, `kernel_replay`, `module_journal`, `slice_plan`, `container_decls`, `container_at`, `warnings`, `omega_reports`, `omega_failure_reports`, `pending_derived` | pool: *inline, empty* (custom `Clone`); replay: *empty* (custom `Clone`); journal: *lengths only* (custom `Clone`); rest: deep copy | `restore_module_pass` enumerates them; `restore_from_clone` enumerates the three it must *not* restore |
| Declaration attempt | `attempt: DeclAttempt`, `misplaced_recursion`, `member_owner`, `instance_scope`, `impl_provenance` | deep copy | `DeclAttempt::{prepare, finish}` enumerate fields (§4) |
| Dynamic scope | `positivity`, `by_quoting`, `host_leaves`, `rule_citation`, `meta_pushed`, `quote_depth`, `generated_depth`, `expr_depth`, `resolve_depth`, `omega_depth`, `ring_depth`, `omega_settled_guards` | copied (a clone inherits the depth, deliberately for `expr_depth`) | hand save/restore at each site (§8) |
| Policy/config | `lint_profile`, `review_lints`, `gate`, `fuel`, `value_metrics`, `emission_findings`, `owed_checks_forgotten`, `native_tactics` | copied/shared | never rolled back |
| Memos | `result_only_memo`, `named_type_memo`, `iwf_part_memo` (the three `guard_*` rescope memos went with `issues/identity-rescopes-after-constants.md`) | copied | two are cleared on restore (`session.rs:76`, `module_delta.rs:1009`); the rest validate by `Rc::ptr_eq` and need no clear |

**How the classes are enforced today.** By convention spread over: three
custom `Clone` impls (`KernelPool`, `ReplaySlot`, `JournalSlot`), the exception
list in `restore_from_clone` (`lib.rs:1983`), the reset list in
`restore_module_pass` (`session.rs:122`), the memo clears in
`SessionCheckpoint::restore` and again in the slice replay
(`module_delta.rs:1009`), and `fork`/`fork_over`/`SemanticImage::elaborator`.

**What went wrong.** `pool.rs:596`: whole-elaborator undo (`*self =
snapshot`) assigned a clone's inline, empty pool over the live one. Every
queued verdict was dropped, the join saw nothing, a recorded rejection was
never reported and the gate went silently inline for the rest of the module —
"invisible except under load". It is now caught only by a `debug_assert!` in
`KernelPool::drop`, and avoided by every caller remembering to use
`restore_from_clone` (`traits.rs:2791` carries a comment saying so).

**Fragility left.** A new module-pass field gets the deep-copy clone rule and
is clobbered by `restore_from_clone` unless someone adds it to the exception
list; a new Ψ-position-keyed memo is not cleared on rollback unless someone
adds it to two clear lists. Nothing fails to compile either way.

**Make explicit?** Yes. Group the fields into sub-structs named by lifetime —
`ModulePass`, `DynamicScope`, `Policy`, `Memos` beside the existing
`CommittedWorld` and `DeclAttempt` — and give each group exactly one clone
rule and one rollback rule. `restore_from_clone` becomes "restore everything
but `ModulePass`", which no new field can fall outside of. This is a
mechanical move of field declarations and accesses (`self.kernel_pool` →
`self.pass.kernel_pool`) with no behaviour change; the win is that the next
field has to pick a class. Overlaps the data-oriented survey's regrouping.

**Done (2026-11-02).** `crates/elab/src/lifetimes.rs` holds the groups and
the table of their rules; §7's duplicate and §8's helper landed with it
([[elab-field-lifetimes-explicit]]'s log). The line numbers above are as
surveyed.

## 2. The module pass: parallel → join → discard → serial replay

**Where.** `elab_module_source` and `check_module_source_inner`
(`lib.rs:2490`, `lib.rs:3221`), `serially` (`lib.rs:2508`),
`join_kernel_gate` (`lib.rs:2018`), `pool.rs` `Replay`/`ReplaySlot`/`KernelPool`.

**States and transitions (as the code walks them).**

```
Inline ──────────────────────────────────────────────► (one pass, done)
Parallel: replay.clear(); mark = checkpoint(); pass(&mut deferred_failed)
   ├─ !deferred_failed ─────────────────────────────► done
   └─ deferred_failed: join recorded Replay ─► restore_module_pass(mark)
        ─► Serial: set_workers(1); replay.arm(); pass(&mut false);
                   replay.finish(); set_workers(width) ─► done
```

The state is carried by: the pool's width, a `deferred_failed: &mut bool`
out-parameter set at two places in the pass, the `ReplaySlot`'s `Option`, and
`Replay { armed, live }`. Of `(armed, live)`'s four values three are reachable
(recorded, replaying, dead); `stop()` is only reached when armed. The whole
sequence is written out twice, once per entry point.

**Invariants.** The pool is quiescent at both ends of the serial pass; the
replay is armed only during the serial pass; a join takes every outstanding
outcome, so only the pass that owns the queue may join it.

**What went wrong.** `module_delta.rs:1302`: a slice replay running inside a
module pass joined the pool and took *the pass's* outcomes — a rejected proof
queued before the slice became the slice's failure, and the pass's own join
found nothing to refuse the module with. Fixed by not joining when the slice
queued nothing, i.e. by every nested caller knowing whether it owns the queue.

**Make explicit?** Yes. One driver, `run_module_pass(kind, |me| pass)`, owning
the checkpoint/discard/replay sequence for both entry points; `Replay` as an
enum (`Recorded`, `Replaying { at }`, `Dead`) with the folds riding along; and
pool submissions that return a ticket (or an epoch), so a join drains only
what its caller submitted. The ticket is what retires the nested-join class of
bug rather than the one instance. Relates to [[deferred-gate-transitive-rollback]],
which would replace the serial replay; the driver is the seam it would plug into.

## 3. The kernel's Ψ-bound `GlobalCache`

**Where.** `typing::Env` (`typing.rs:973`), `conv::Env` (`conv.rs:535`),
`reduce::Defs` (`reduce.rs:112`), `reduce::GlobalCache` (`reduce.rs:138`).

**State.** A `GlobalCache` memoizes rescoped bodies and signatures by
`GlobalVar` and is sound *for one Ψ only*: "an entry surviving a push would
answer about the wrong binding: a soundness bug, not a slowdown"
(`reduce.rs:135`). The pair `(psi, cache)` therefore has an invariant —
`cache` was built for exactly `psi` — kept by:

- `push_tele` rebuilding the cache in both `Env`s;
- twelve `typing::Env { psi: psi.clone(), cache: Rc::new(GlobalCache::new()), … }`
  literals in `typing.rs`, each pairing them by hand;
- the `pub(crate)` `conv_*_cached` entries taking `psi` and `cache` as two
  arguments (`conv.rs:205` note: "the caller is the one that knows its Ψ is
  the same");
- `pub fn Defs::transparent_cached(psi, cache)` and `pub struct GlobalCache`,
  used from the elaborator (`host.rs:92`, `function_ir_source/program.rs:1079`)
  as a `Reader { psi, cache }` pair.

No mismatch exists today. But it is a TCB soundness invariant that the type
system does not see, and two of its constructors are public.

**Make explicit?** Yes, and cheaply: a `ScopedGlobals { psi, cache }` (name
open) constructed only from a Ψ, whose only Ψ-changing operation is the
telescope push that rebuilds the cache. `Defs::transparent_cached` and the
`*_cached` entries take it instead of the two halves; the twelve `Env`
literals shrink to one constructor. Kernel change, so it belongs to a kernel
round with `scripts/bench --check`.

## 4. The declaration attempt lifecycle (and `delta_psi`)

**Where.** `DeclAttempt` (`attempt.rs`), `GoalArena` (`goals.rs:84`),
`elab_decl_one` (`lib.rs:3739`), `refresh_delta_psi` (`lib.rs:10156`).

**States and transitions.**

```
Idle ─enable_restarts─► Restartable
  ─prepare; configure(written, reserved); refresh_delta_psi─► Elaborating
     ─(promotion over capacity: requested_base > reserved)─► clear_goals ─► Elaborating (again)
     ─solve_goals: freeze─► Frozen (on-clauses; allocate refuses)
  ─finish; refresh_delta_psi─► Idle ─commit_decl (pushes Ψ, refresh)─►
```

Carried by `restart_enabled: Cell<bool>`, `frozen: Cell<bool>`, `base`,
`written_base`, `requested_base`, `promoted_seen`, and call order.

**Hand-kept parts.**

- `prepare()` and `finish()` each enumerate the fields to clear, and the
  lists differ: `prepare` clears `op_fallback_uses` and `direct_dependencies`,
  `finish` does not, because `elab_decl_one` reads the former *after*
  `finish` and `check_decl` reads the latter before it. Correct, and invisible
  in the type: the next field added to `DeclAttempt` must be added to one,
  both or neither list by reading the callers.
- The "mini-attempt" protocol — `prepare; configure; refresh_delta_psi; …;
  finish; refresh_delta_psi` — is copied at `check_measure_is_nat`
  (`lib.rs:4024`), `group_universe` (`mutual_rec.rs:567`) and the two measure
  queries (`measure_context.rs:20,62`).
- The measure queries clone the elaborator, then `prepare` and `configure(0,
  0)`. `GoalArena::prepare` resets two counters and keeps the goal entries, so
  this is a fresh attempt only because the queries run between attempts, when
  `finish` has already emptied the arena. Called mid-attempt, the clone would
  keep the outer declaration's goals over a base of 0.
- `delta_psi` (Ψ plus `base` placeholders) is stored in `CommittedWorld`
  although it is a function of Ψ and the attempt's goal base, and is
  refreshed by hand at 15 sites "wherever Ψ or `goal_base` moves". Every Ψ
  push I found is followed by a refresh; nothing enforces it.

**Make explicit?** Yes. A scoped `with_attempt(written, reserved, |me| …)`
for the mini-attempt; a debug assertion (or a phase enum) that `prepare` runs
only from `Idle`; reset by assigning a fresh value for the cleared fields
rather than enumerating them, with the fields read after `finish` moved into
the attempt's *result*. `delta_psi` becomes either a lazily built view keyed
on (Ψ identity, base) or something only the Ψ-push and configure methods
write.

## 5. The goal slot

**Where.** `goals::Goal` (`goals.rs:29`).

**State.** `solution: Option<Rc<Term>>`, `proved: bool`, `transparent:
Option<Transparent>`. Eight combinations; four mean something:

| State | solution | proved | transparent | Made by |
|-------|----------|--------|-------------|---------|
| Open | None | false | None | `allocate` |
| Solved | Some | false | None | `solve`, `solve_named` (`on` clauses) |
| Proved (lifted lemma) | Some | true | None | `allocate_proved` |
| Transparent (lifted definition) | Some | false | Some | `allocate_transparent` |

Readers re-derive the state: `lifted()` filters `proved ||
transparent.is_some()` and then `expect("a lifted slot is solved")`;
`outstanding()` and `reports()` filter `solution.is_none()`; `delta_world`
matches `transparent: Some(..)`.

**Make explicit?** Yes — a `GoalState` enum. The unifier made exactly this
move for its metas (`unification.rs:98`, `Sol { Unsolved, Withheld, Solved }`),
replacing a planted `Term::Zero` that made a withheld slot look solved; the
goal slot is the same shape one module over. Small and local.

**Landed** (2026-11-02): `goals::GoalState { Open, Solved, Proved,
Transparent }` replaced the triple; `lifted()` matches on it.

## 6. The kernel checker's mode

**Where.** `typing::Tc` (`typing.rs:1080`).

**State.** `materialize_eagerly: bool`, `spellings: Option<…>`, `spell_all:
bool`, `refused: Option<…>`. Sixteen combinations; four modes are built:

| Mode | eager | spellings | spell_all | refused | Built by |
|------|-------|-----------|-----------|---------|----------|
| Gate | false | None | (true, unread) | None | `Tc::new` |
| Oracle | true | None | (true, unread) | None | `Tc::eager` |
| Spell | true | Some | all/export | None | `Tc::eager` then two field writes (`typing.rs:723`, `:797`) |
| Locate | false | None | (true, unread) | Some | `Tc::new` then a field write (`:564`, `:587`) |

Arms test the combination directly (`!self.materialize_eagerly &&
self.spellings.is_none()` at `:3342`; the memo is skipped when `spellings` is
`Some`, `:2661`). "Spell implies eager" holds because both spell paths happen
to start from `Tc::eager`.

**Make explicit?** Yes, modestly: `enum TcMode { Gate, Oracle, Spell { all,
record }, Locate { slot } }` with `fn eager(&self)`, `fn memo_allowed(&self)`
predicates, so the arms ask a named question. The differential tests already
cover the behaviour, so the risk is low and so is the urgency; worth doing in
a kernel round that touches `Tc` anyway.

## 7. "Under a quotation", three times

The kernel's `Env::under_box` (`typing.rs:998`), the elaborator's
`Cx::quoted` (`context.rs:91`) and `Elaborator::quote_depth` (`lib.rs:764`)
all say "inside a `box` payload". The elaborator keeps two because "a helper
inside it that starts from a fresh `Cx` does not inherit the bit"
(`lib.rs:760`), so `emits_at_forms` reads both. The meta layer has the same
split: `Cx::meta` and `Elaborator::meta_pushed`, the latter cleared (not
restored) at the end of `elab_meta_decl`. The kernel copy is a typing rule's
side condition and stays. On the elaborator side the duplication is a symptom
of mode living in `Cx` while some helpers build a fresh one; either fresh-`Cx`
construction inherits dynamic mode from the elaborator, or the mode lives only
in the elaborator's dynamic scope (§8). Folded into
[[elab-field-lifetimes-explicit]].

## 8. Hand-restored dynamic scopes

Fifteen `Elaborator` fields are set for a dynamic extent and put back by hand
(`replace`/`set` before, assignment after): `member_owner` (`lib.rs:3590`),
`misplaced_recursion` (`:3640`), `positivity` (`resolve.rs:832,850,890`),
`rule_citation` (`resolve.rs:767`), `by_quoting` (`host.rs:1501,1579`),
`host_leaves` (`host.rs:3230,3586`), `meta_pushed` (`quote.rs:137,481`),
`impl_provenance` (`datarepr.rs:2557`), `quote_depth` (`quote.rs:824`),
`generated_depth` (`access.rs:184,194`), `resolve_depth`, `container_at`;
`omega_depth` and `ring_depth` already use guards.

I checked every site: each restores on the error path too (the result is
bound before the restore and returned after), and since nothing on the
elaborator's thread catches a panic (`catch_unwind` appears only in the pool's
workers), unwinding cannot leak one. Three *reset* rather than restore —
`impl_provenance = None`, `misplaced_recursion = None`, `meta_pushed.clear()` —
which is wrong only if the extent nests; I found no nesting path today.

**Make explicit?** One small `scoped(&cell, value, |me| …)` helper (the
`generated_mode` shape at `access.rs:180`) would make "restore the outer
value" the default instead of a per-site choice. Low on its own; folded into
[[elab-field-lifetimes-explicit]] as the `DynamicScope` group's rule.

## 9. Small latches and pairs — leave them

- `Eval::transparent` (`eval.rs:278`): saved and restored around the two
  `delta_whnf` loops, errors included. Local and correct.
- `Conv::depth`/`Eval::depth`: paired by hand ("a guard would borrow `self`
  across the comparison nodes", `conv.rs:862`), with the closure pattern so
  every `?` lands before the decrement. Fine.
- `reduce::Frames { depth, exhausted }`: a one-way latch read once at the end.
- `SlicePlan::exact` (`module_delta.rs:118`): a one-way exact → diverged latch.
- `JournalSlot { live, mark }`: `mark` is `Some` exactly on a clone; could be
  an enum, but it has two methods and one reader.
- `SealedProof { term: OnceLock, source: Option }`: "has a term or a source"
  is checked by one `expect`; the `OnceLock` is the right tool.
- `ArgumentClass { checking_only, fallback_infer }`: `(false, true)` is
  constructible and means the same as `(false, false)`. Harmless.
- `fmt.rs`'s `REMAINING = -1` "no format in progress" sentinel: thread-local
  and two functions wide.

## 10. Already explicit, or deliberately not

- **Already explicit, and good precedents:** `unification::Sol` (§5);
  `NativeTactic::{start, resume}` returning a `Step` (`host.rs:466`) — the host
  protocol is a real state machine with a real type; `MatchRollback`
  (`matching.rs:97`), a drop guard that rolls back unless committed;
  `ResolutionScope`, `omega_cert::CertificateScope`, `ring.rs`'s `Depth` guard;
  `unseal::Recording`, a guard that closes its frame on drop.
- **Deliberately implicit:** `bounds.rs`'s two-stage memo (`Cache` with
  parallel `terms`/`term_marks` vectors: each slot is Empty, Marked(address)
  or Computed). The answer is a pure function either way, the layout is
  perf-critical, and an enum per slot would cost the memory the design avoided.
  Data-oriented survey territory.
