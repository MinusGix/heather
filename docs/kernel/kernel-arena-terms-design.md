# Arena-indexed kernel terms: what it costs, what it buys, and what to do first

Design pass on `issues/kernel-arena-terms-frozen-prefix.md`, 2026-09-13.
The issue's Acceptance asks items 2–6 answered against the code, a sized diff
per kernel file, a named prototype slice, and a decision. This note does that
and recommends **not** rewriting `Term`/`Type` now: the measured payoff the
issue was chartered on has moved to the value domain, which is already
arena-borrowed, and the slice that collects it is two orders of magnitude
smaller than the rewrite.

Everything measured here was run on one furnace instance (see §0); the
committed `crates/kernel/benches/baseline.tsv` is desktop-recorded and not
comparable, so the before column was retaken with `--save` on the same
instance in the same job.

## 0. What changed under the issue since it was written

The issue named two walls. One of them is gone.

**Parallelism is no longer a motivation.** `issues/parallel-kernel-gate.md`
and `docs/kernel/parallel-kernel-gate-design.md` landed `use std::sync::Arc as Rc`
across 117 workspace files plus a deferred gate, default eight workers. Total
CPU and summed `kernel_gate` are flat to ±5% across W ∈ {1,2,4,8}; wall goes
2.88× at W=8 and then meets Amdahl's other half (the serial elaborator), not
contention. The issue's claim that "sharing a prefix across threads is a data
race on the refcounts" was true of `Rc` and is simply false of `Arc`: Ψ is
persistent, terms have no interior mutability, and a worker's snapshot is an
`Arc` clone the elaborator's next append copies away from. **The arena is not
the road to parallel checking; that road is already open and already flat.**

What survives as motivation:

- (a) **The allocation constant.** ~1.94 M `Rc<VTy>`/`Rc<Val>` memo
  allocations against ~60 k arena chunks per five-node x86 module — 33:1,
  the ~30% allocator share
  (`docs/kernel/conversion-query-arena-pooling-design.md` §1–§2,
  `issues/value-cache-memo-in-arena.md`). §2 re-measures the same quantity on
  the certificate and gets **~22.9 M**.
- (b) **The `Arc` serial tax** on refcount-dense paths: 1.20–1.28× on the
  four nat micro-families, 1.02–1.06× everywhere conversion does the work,
  +2% at module scale. `issues/subst-rebuild-then-discard.md` names where it
  lands.
- (c) **Ordering against K1** (`issues/kernel-native-bitvector-values.md`),
  which the user queued behind this issue on 2026-09-12.

§1 answers (c) first, because it is the cheapest finding in the note and it
unblocks another round.

## 1. Finding: K1 does not depend on the term representation

K1 adds a **`Val` constructor** holding a closed ≤64-bit word, with the
primitive fold computing natively on it. `Val<'v>` and `VTy<'v>` live in
`crates/kernel/src/value.rs` and already borrow the query region `'v`; their
syntactic sub-structures are reached through `TmClo`/`TyClo`, which hold
`Rc<Term>` today and would hold a `TermId` after the rewrite — one field, in
two enums, in one file. Nothing in K1's adequacy argument, its native fold, or
its differential oracle mentions how a `Term` child is spelled.

So the ordering K1's own text asks about has the easy answer: **K1 is not
blocked by this issue and never was.** The one real interaction is the
opposite of the one assumed — the prototype slice this note recommends (§5)
rewrites the `Val`/`VTy` ownership discipline, and a K1 variant written before
that slice would be rewritten by it. *K1 should land after the slice in §5 and
before any term rewrite.* That is a coordinator decision; this note does not
reorder anything.

Sizing K1 from the certificate, as its own 2026-09-13 log records it: the
closed-refl families are 8.4 s of a 27.8 s kernel gate, 630 items at
13–44 ms, each one closed machine-word operation. That is a bigger,
better-attributed number than anything in this note, and it is available
behind a diff in one region of the value domain.

## 2. The before column

`furnace-bb0218be4a` (AMD EPYC 9J14), tree `af00689`, release, one instance,
one job per table. The committed `baseline.tsv` is desktop-recorded, so the
bench column below was taken with `scripts/bench --save` on this instance
minutes before the certificate run.

**Certificate** — `heather build-x86 examples/x86-native/reused_callee.hthr
caller --callee leaf --arg 21 --arg 1 --cache-dir target/native-test-images
--kernel-workers 1 --timings …`, release with `--features value-metrics`,
warm (the run before it was warm too; wall 42.65 s vs 42.66 s, so no library
rebuild is in either):

| row | value |
|---|---|
| wall / user / peak RSS | 42.66 s / 42.17 s / 928.4 MB |
| `run` scope total | 42.14 s |
| certificate module `total` / `kernel_gate` | 36.89 s / 26.66 s |
| certificate items | 3 476 |
| `eval_steps` (run / certificate) | 22 767 621 / 16 069 722 |
| `conv_misses` (run / certificate) | 254 259 / 237 888 |
| `conv_shortcut_hits` (run / certificate) | 7 282 750 / 6 618 790 |
| `term_cache_lookups` / `hits` | 11 728 592 / 1 374 944 (11.7%) |
| `type_cache_lookups` / `hits` | 12 748 766 / 163 309 (**1.3%**) |

**The number this round was looking for is the last two rows.** A cache
lookup that misses is a value that then gets forced and `Rc::new`d:
`(11 728 592 − 1 374 944) + (12 748 766 − 163 309) = 22 938 105` heap
allocations of `Rc<Val>`/`Rc<VTy>` for one certificate build, on top of
whatever `VNeutral` costs beside them (§5.1). The five-node module's
1.94 M from `docs/kernel/conversion-query-arena-pooling-design.md` §1 was the same
quantity one workload down; on the certificate it is **~23 M**, against a
36.9 s module.

**Surprise, filed rather than exploited:** the *type* memo's hit rate is
1.3%. 12.7 M lookups buy 163 k hits, and every one of the other 12.6 M pays
an allocation and a table write. That is not what a memo is for, and it is
not this round's to fix
(`issues/type-value-memo-hit-rate.md`).

**Kernel bench**, `scripts/bench --save` on the same instance — medians, and
the four families the `Arc` tax flagged:

| family | cases (median) | slope |
|---|---|---|
| `nat/step-once` | 64:158 ns, 128:157, 256:157, 512:159, 1024:157 | −0.00 |
| `nat/step-into-closed-body` | 64:175 ns, …, 1024:175 | −0.00 |
| `nat/add-normalize` | 64:15.06 µs, 128:30.11, 256:60.15, 512:120.67, 1024:240.94 | 1.00 |
| `nat/mul-normalize` | 8:14.75 µs, 12:31.96, 16:55.74, 24:123.24, 32:216.80, 48:483.45 | 1.95 |
| `subst/shift-local` | 71:2.15 µs, 135:4.68, 263:9.55, 519:19.55, 1031:40.02 | 1.09 |
| `nat/check-numeral` | 64:1.83 µs, 128:3.53, 256:8.13, 512:16.84 | 1.07 |
| `conv/computed-numeral` | 32:26.05 µs, 64:51.08, 128:99.71, 256:201.62, 512:403.37 | 0.99 |
| `conv/perturbed-pairs` | 25:70.81 µs, 50:152.22, 100:315.38, 200:632.82 | 1.05 |
| `conv/simulate-payload` / `-depth` | — | 0.00 / 1.00 |
| `wf/check-tree` / `wf/mirror-involution` | — | 0.99 / 1.01 |
| `code/check-identity-recursor` | 3:353.50 µs, 5:356.24, 9:362.72, 17:364.12, 33:370.89 | 0.06 |
| `check/generated-terms` | 25:636.25 µs, 50:696.05, 100:1.91 ms, 200:5.12 ms | 1.05 |
| `stack/check-numeral` | 1 530 levels, 2.7 KiB/level | — |

Every slope is inside its declared band. This is the column any slice in §5
must be re-`--check`ed against **on this instance**, because the committed
baseline is not.

## 3. Item 2 — everything that relies on `Rc` identity or uniqueness

Audited by grep over `crates/` and read at each site. The inventory is smaller
than the issue assumed in one place and larger in another.

### 3.1 `Rc::ptr_eq` fast paths

| site | what it decides | id-based equivalent |
|---|---|---|
| `eval.rs:508`, `571` | δ-fixpoint: `delta_whnf`/`delta_whnf_ty` stop when a step returned the same **value** | value-domain; unaffected by term ids. Becomes `std::ptr::eq` on `&'v Val` under §5. |
| `eval.rs:537`, `545`, `553` | `delta_step_ty` — same, per stuck former | same |
| `conv/dom.rs:1667` `ty_eq_fast` | syntactic-domain reflexivity on `Rc<Type>` | `TypeId` equality — *stronger and cheaper*, see §4 |
| `conv/dom.rs:1677` `tm_identity_fast` | ditto for terms | `TermId` equality |
| `conv/dom/values.rs:1258,1273,1300` | closure-body identity `Rc::ptr_eq(b1,b2) \|\| b1 == b2` beside `Env::ptr_eq` | `TermId` equality; the `\|\| b1 == b2` structural fallback disappears under hash-consing (§4) and must be **kept** under copying |
| `bounds.rs:167,186,211,224` | the bounds memo's key validity | §3.3 |
| `term.rs:1104`, `1118` | `CtxEntriesIdentity` — `Eq`+`Hash` of a Γ spine by pointer, a conversion-memo bucket key | node id of the spine head |
| `term.rs:1326` | `CtxEntries::eq` shortcut on a shared tail | node id |
| `term.rs:1549` | `GlobalBindings::same_identity` — Ψ generation token | unchanged: it is an `Rc<()>` token, not a term |
| `typing.rs:557`, `565` | `RcIdentity<T>` `Eq`/`Hash`, the Ψ half of the conversion memo bucket | unchanged (same token) |
| `value/program.rs:82`, `255`, `360`, `369` | `ContextProgram` DAG identity: memo keys and `equivalent_fast` | value-domain run programs; unaffected by term ids |
| `value/algebra.rs:188`, `236`, `243` | fold-class memo keyed by `Rc::as_ptr(program)` | same |

Two comments about this table that matter more than the table.

First, **every pointer-keyed cache in the kernel already documents why its key
cannot be freed and reused** (`program.rs:78-81`, `algebra.rs:185-187`,
`bounds.rs:101-106`, `value.rs:253-258`). Under arena ids that comment becomes
a property of the representation rather than a retention argument at each
site: an append-only arena never reuses an id. This is the one place the
rewrite makes the *trusted* base simpler rather than more complicated, and it
is worth saying in DESIGN.md (§7).

Second, the sites that would actually get *faster* are the two `*_eq_fast`
hooks and `CtxEntries` — and their payoff depends entirely on §4.

### 3.2 `make_mut` / `get_mut` / `try_unwrap` — the issue's guess was wrong

The issue lists "`make_mut`/`get_mut` in `subst.rs`". There is none.
`subst.rs` has no `make_mut`, no `get_mut`, no `try_unwrap` and no
`strong_count`. What it has is `shared_ty`/`shared_tm` (`subst.rs:271`, `282`):
`map_*` builds a replacement node, the mapper reports no change, the node is
`drop`ped and `Rc::clone(orig)` returned. That is the rebuild-then-discard pair
`issues/subst-rebuild-then-discard.md` owns, and it is a *refcount* cost, not a
uniqueness cost.

`make_mut` in the kernel is exactly two live sites, both on Ψ's spine —
`term.rs:1556` (`GlobalBindings::push`) and `term.rs:1566` (`seal_tail`) —
plus one in a test (`eval.rs:2192-2193`). Ψ's copy-on-write append is the
frozen-prefix discipline the issue wants, already implemented; an arena would
replace the `Vec` copy with an append, which is a strict simplification of
those two functions and nothing else. The elaborator's 18 `make_mut` sites are
all on its own persistent layers (`types.rs`, `names.rs`, `gendefs.rs`,
`provenance.rs`), not on kernel terms.

**So item 2's uniqueness half is essentially empty.** The identity half (§3.1)
is real but almost all of it is either value-domain or a token, and the term
half is 8 sites.

### 3.3 The bounds memo

`bounds.rs` is the one structure whose *design* is an `Rc` argument.
`Cache::term_use`/`term_query` (`bounds.rs:148-235`) is a direct-mapped table
of `2^16` slots per sort where the slot's keep-alive `Rc` **is** the key
(`Rc::as_ptr` + `Rc::ptr_eq`), with a two-stage marker so one-shot terms pay
nothing. Under ids: the key is a `TermId`, the keep-alive disappears (the arena
retains), the two-stage marker stays (it is about one-shot cost, not about
liveness), and the "how many dead subtrees the keep-alives can pin" clause in
the doc comment is deleted. The slot shrinks from the documented 24 bytes to
about half that.

This is the clearest single argument *for* the rewrite in the whole note and
it is worth about 3 MiB of table and a handful of refcount ops; it does not
move a measured number.

### 3.4 `BodyCache`, the value caches, `Env` cells

`reduce.rs:105` `BodyCache(RefCell<Vec<Option<Rc<Term>>>>)` — a slot per
`GlobalVar` holding the rescoped body. Becomes `Vec<Option<TermId>>`; the
per-gate lifetime landed in `docs/kernel/conversion-query-arena-pooling-design.md`
§3 and is unaffected.

The value caches (`value.rs:252-253`) are already keyed by `*const TmClo` /
`*const TyClo` — **arena** pointers, not `Rc` — and their soundness argument
is already "closures live as long as the arena, so a key is never reused". The
same is true of `fold_classes` (`value.rs:259`). These need no id-based
equivalent; they are the id discipline, one region earlier. What they store is
the problem (§5).

`Env`/`EnvNode` (`value.rs:78-85`) are `&'v`-linked already.

### 3.5 `fmt.rs` — the item 2 entry that is not mechanical

`Debug` on `Term`/`Type` is budget-bounded by CLAUDE.md's rule, and
`fmt::write_exact` (`fmt.rs:115`) is used as a **content identity**: the
elaborator's determinism tests hash Ψ through it
(`crates/elab/tests/support/mod.rs:248-255`, `determinism.rs:109`) and
`typing.rs:2421` uses it for a capped render.

`Debug::fmt` takes no context. An arena-indexed `Term` is a `u32`; it cannot
print itself. There are exactly three ways out, and the note picks one so the
implementing pass does not have to:

1. A thread-local "current arena" the impls read. **Rejected**: it puts
   ambient mutable state into the trusted base's printing path, and a wrong
   arena prints a wrong term — silently, in a hash used as an identity.
2. Wrapper `struct Printed<'a>(&'a Arena, TermId)` with `Debug` on the
   wrapper, and every `{:?}` site updated. Honest, and the `write_exact`
   callers already have the arena in hand. **This is the choice.**
3. Keep a `Debug` on the arena and print by id only from there. Same as 2
   with a worse spelling.

Cost: `fmt.rs` is rewritten whole (646 lines) because every impl gains the
arena parameter; `crates/cache` and the three elab test-support sites follow.
`fmt.rs`'s totality discipline (destructure with no `..`, `deny(unused_variables)`)
survives unchanged. Nothing here is hard, but it is the item where "mechanical"
stops being true, and it is in the path of the determinism hashes.

## 4. Item 3 — hash-consing or copying

The question is whether an arena node is interned (structurally equal subterms
get one id) or freely copied.

**What hash-consing would buy — and the premise that turned out false.**
`typing.rs:678` is the kernel's hottest conversion decision:

```rust
if self.fuel > 0 && expected == inferred {
    crate::stats::conv_shortcut_hits(1);
```

The obvious argument is that each of those 2.78 M hits per omega module walks
two whole trees, and hash-consing would make it one `u32` compare. **It does
not.** `std`'s `Arc` carries an `ArcEqIdent` specialization
(`library/alloc/src/sync.rs:3549-3553`): for `T: Eq` — which `Type` and `Term`
both derive — `Arc::eq` is `ptr::eq(…) || **self == **other`. So the pointer
test is already there, at the root *and at every child*, and a comparison of
two trees that share a subtree stops at the shared node. The structural walk
only happens over the genuinely unshared spine, which is the part hash-consing
would have to intern node-by-node anyway.

So the conversion shortcut is not an argument for interning. Hash-consing's
remaining prize is the case where two structurally equal trees were built
*independently* (no shared node), which under interning become the same id.
That case is real — `rec.rs`'s telescopes and `certgen`'s generated statements
rebuild the same annotations repeatedly — but it is unmeasured, and it is the
same case whose per-node cost `bounds.rs`'s doc comment records.

**What hash-consing would cost.** Every construction becomes a hash lookup
over the node's own bytes plus its children's ids. Kernel-side that is 316
`Rc::new(Term::/Type::)` sites plus `rec.rs`'s 730 `Rc::new` (the code
recursors build a term per branch per traversal); elaborator-side ~1 200
(§5.2). The workload that decides it is `rec.rs` and `certgen`: fresh
telescopes, built once, checked once, dropped — exactly the shape
`bounds.rs`'s own doc comment records as having cost 1.5–2× on
`code/check-identity-recursor` when it was given eager metadata per node. A
hash-cons table is strictly more per-node work than that was.

**Decision: copy, do not hash-cons** — and take the shortcut payoff a
different way. The DAG-sharing arguments the issue points at
(`succinct-inductive-values`, `generated-source-semantic-term-sharing`) are
about *values* and *generated source*, not about the checker's own
construction traffic, and the checker's construction traffic is what would pay
the interning bill. `issues/open-payload-shift-copies.md` returning is the
accepted cost; `bounds.rs`'s skip hooks already make a shift over a closed
subtree O(1), which is the case that copying would otherwise blow up.

The copying cost the issue worries about —
`issues/open-payload-shift-copies.md` returning — is bounded by the same
`bounds.rs` skip hooks that make a shift over a closed subtree O(1) today,
and those hooks survive the rewrite unchanged (§3.3).

## 5. The prototype slice: the issue's guess, confirmed and sized

The issue guesses "arena-index the value domain's `Rc` memos first, since they
are already beside an arena". That is right, and it is *more* right than the
issue realized: the slice is self-contained, it does not touch `Term` at all,
and it collects essentially the whole measured allocation constant.

### 5.1 The slice

**Landed 2026-10-30** (`issues/value-cache-memo-in-arena.md`, closed), with
the value-domain `Elim` cells in the same arena as well; the paragraphs below
are the plan as written, and the issue log has the measurement. One
difference from the plan: an elimination a frame of the evaluator's
continuation stack makes for itself rides in the frame by value, not in a
region cell, because the frame is popped long before the query ends.

`ValueArena` (`value.rs:250`) owns five `typed_arena::Arena`s for
`EnvNode`/`Level`/`ElimNode`/`TmClo`/`TyClo`. The **forced values** —
`Val<'v>` and `VTy<'v>` — are not among them: `Eval::force` and friends
`Rc::new` them, the bounded FIFO caches store `Rc<Val>`/`Rc<VTy>` keyed by the
closure's arena address, and `Rc::clone` moves them around the δ loops.

The change: three more arenas (`vals: Arena<Val<'v>>`, `vtys: Arena<VTy<'v>>`,
`neutrals: Arena<VNeutral<'v>>`), and `Rc<Val<'v>>` → `&'v Val<'v>`,
`Rc<VTy<'v>>` → `&'v VTy<'v>`, `Rc<VNeutral<'v>>` → `&'v VNeutral<'v>`
throughout. Values become `Copy`; `Rc::clone` on a value becomes a pointer
copy; the δ fixpoint tests become `std::ptr::eq`; the caches store references.

`VNeutral` is worth calling out: `eval.rs:80-81` is
`Rc::new(Val::Neutral(Rc::new(VNeutral { … })))` — **two** heap allocations
per neutral, on the path every stuck elimination takes. Six occurrences, all
in `eval.rs`.

Sizing, counted:

| file | `Rc<Val>`/`Rc<VTy>` occurrences | `Rc::new(Val/VTy)` (non-test / total) |
|---|---|---|
| `value.rs` | 14 | 2 / 12 |
| `eval.rs` | 35 | 9 / 34 |
| `conv/dom/values.rs` | 34 | 1 / 30 |
| `eval/runs.rs` | 5 | 6 / 6 |
| `eval/probe.rs` | 4 | 3 / 3 |
| `value/shift.rs` | 2 | 0 / 0 |

**21 non-test construction sites, 94 type occurrences, six files, all inside
`crates/kernel`.** Every one of them already has an arena handle in scope
(`Eval::arena`, `env.arena`, `Conv`'s region), which is why the count is this
small. Estimated diff: 350–550 lines changed, no new module, no new
dependency (the kernel stays at zero).

Outside the kernel it touches exactly two elaborator files, neither of them a
term-construction API: `certgen.rs:3039` (`fn force(&self, c: &'v TmClo<'v>)
-> Result<Rc<Val<'v>>, String>` — one signature) and `oracle.rs:89-107`
(matches `Ok(VTy::…)`, needs `Ok(&VTy::…)` or a deref). Perhaps 15 lines.

### 5.2 Why not the alternatives

- **Memo cache only** (keep `Rc<Val>` but store `&'v Val` in the cache):
  incoherent — the value must already be arena-resident to be stored by
  reference, and if it is, there is no `Rc` left to keep.
- **`subst.rs` rebuild-then-discard** (`issues/subst-rebuild-then-discard.md`):
  an `Option`-returning rewrite of every arm of `map_type`/`map_term`/
  `map_motives`/`map_branches` — ~600–900 lines in the trusted base's widest
  traversal, behind the 300-seed law suite. Its acceptance number is the four
  nat micro-families at 1.2×; at module scale substitution is not what the
  certificate spends its 27.8 s on. **Worse payoff per diff, and higher risk.**
- **The full term rewrite** (§6): ~2 800 kernel sites, ~1 200 elaborator
  construction sites, `fmt.rs` whole, the determinism hashes in the path.

The slice in §5.1 is the one with the best measured-payoff-per-diff by a wide
margin: it addresses the **~22.9 M** `Rc<Val>`/`Rc<VTy>` allocations §2
counted on the certificate (and ~1.94 M of the five-node module's ~2.0 M), it is
~500 lines, and it is entirely inside the kernel.

### 5.3 What could go wrong with the slice, and the falsifiers

1. **Monotone memory.** An arena value is never freed before the query ends;
   an `Rc` value dies when its last holder drops. The FIFO caches
   (`VALUE_CACHE_CAPACITY = 64 * 1024`) currently reclaim on eviction. The
   module's recorded `evictions: 0` and `type_cache_peak: 6911` say this is
   not where the memory is, but the honest check is peak RSS on both the
   certificate and cold Omega, reported beside the time. §2's 928.4 MB on the
   certificate at W=1 is the before number; note that the deferred gate's RSS
   already grows with worker width (one value arena per worker in flight), so
   this slice's memory effect must be read at W=1 and then re-read at the
   default eight before it is called neutral.
2. **Eviction semantics.** `value-cache-memo-in-arena` names this: an
   arena-resident memo must not change *what is memoized*, only where it
   lives. Eviction remains eviction (the entry leaves the table); the value
   stays reachable from the arena, which is a memory statement, not a
   semantic one. The `value-metrics` counters keep their meaning
   (`inserts`/`evictions` count table events, not allocations) — and that
   should be stated in the counter's doc comment, because after this change
   `type_cache_inserts` is no longer a count of heap allocations, which is
   exactly how the number in `docs/kernel/conversion-query-arena-pooling-design.md`
   §1 and §2 of this note were read. Record
   `issues/type-value-memo-hit-rate.md`'s four rates **before** the slice
   lands, for the same reason.
3. **A thunk never memoizes a failure** (`value.rs`'s `TmClo` doc): the memo
   is written only on `Ok`. Unchanged — the arena allocation happens on the
   success path where `Rc::new` did.
4. **Negative control.** A test that a query's verdict is identical with the
   caches forced to capacity 1 (already the shape `conversion-query-arena-pooling`
   used) and one that a `Val` obtained before an eviction still answers
   `ptr_eq` against its re-forced twin **false**, so nothing accidentally
   starts depending on address stability across evictions.

## 6. Items 4, 5, 6 — sized, for the rewrite that is being deferred

### 6.1 Item 4: publication cost

A worker returns nodes the parent must append to the frozen prefix with ids
rebased. That is exactly `issues/relocatable-semantic-module-images.md`'s
problem: its 2026-09-04 log already proposes **per-dependency range
relocation** (old Ψ range → new range, valid when interface hashes are
unchanged) as the cheaper first slice, and an in-memory publication is the
same operation with a range that is always "append at the end", i.e. add a
constant to every id at or above the split. It should be the same code, and
the issue should own it.

But notice item 4 only exists because of parallelism, and §0 retired that
motivation. **In a serial kernel there is no publication step at all** — the
worker *is* the parent, and a term built during a check is already in the one
arena. Item 4 is therefore not a cost of the rewrite as now motivated; it is a
cost of a parallel scheme we no longer need.

### 6.2 Item 5: the elaborator boundary

Counted over `crates/elab/src`:

- 1 704 `Rc::new(` sites in 48 files that mention `kernel::`.
- 461 of them are literally `Rc::new(Term::…)` / `Rc::new(Type::…)`.
- Of the rest, the largest wrappers are `Rc::new(self…)` (129),
  `Rc::new(get_term(…))` (87), `Rc::new(get_type(…))` (71),
  `Rc::new(fam…)` (48), `Rc::new(term…)` (30), `Rc::new(motive…)` (22) —
  overwhelmingly kernel terms under a local name. Call it **~1 200
  kernel-term construction sites**.
- 297 `Rc<Term>` / `Rc<Type>` occurrences in elaborator signatures.
- Concentration: `vec.rs` 282, `forded.rs` 231, `lgg.rs` 134,
  `inductive.rs` 130, `wf.rs` 114, `indexed.rs` 111, `gendefs.rs` 106,
  `module_image.rs` 84.

Each site needs an arena handle threaded to it. That is the same chokepoint
`issues/elaborator-canonical-type-spelling.md` wants for "one spelling", which
is the only argument that makes this boundary work worth doing for its own
sake — but it is a ~1 200-site, 48-file, whole-crate refactor, and it must be
one commit (the type changes, so there is no incremental lane).

### 6.3 Item 6: adequacy, drafted for DESIGN.md

Draft section, to be moved into `crates/kernel/DESIGN.md` under
**Representation** *if and when the rewrite is taken*:

> **Arena-indexed terms.** A `Term`/`Type` is a `u32` index into an
> append-only arena. The arena is a prefix of sealed regions plus a growing
> tail; an index, once issued, denotes the same node for the arena's lifetime,
> and no index is ever reused or rewritten. The adequacy statement is
> therefore *the term is the tree the arena denotes*: `denote(A, i)` is the
> total function unfolding node `i` of arena `A` into the `Rc`-tree
> representation this kernel had before, defined because a node's children are
> strictly smaller indices — the arena is topologically ordered by
> construction, so `denote` terminates without an occurs check and cycles are
> unrepresentable. Every judgement is stated on `denote(A, ·)` and implemented
> on indices; the two agree because each rule's implementation matches on the
> node at `i`, which is `denote`'s head by definition.
>
> Two properties carry the weight, and both are properties of the *arena
> type*, not of any call site. **Append-only**: the only mutation is pushing a
> node, so a judgement derived against arena `A` is still derivable against
> any `A'` extending `A` (indices below `|A|` denote the same trees). This is
> what makes the frozen prefix sound and what replaces the old "terms have no
> interior mutability" clause. **No reuse**: an index is never recycled, so
> every pointer-keyed cache in the kernel — the bounds memo, the fold-class
> memo, `ContextProgram`'s equivalence memo, the conversion memo's context
> tokens — keys on an identity that is stable by construction rather than by a
> per-site retention argument. Those retention comments are deleted, not
> restated.
>
> What the argument does **not** give: index equality is sound but not
> complete for structural equality, because nodes are copied rather than
> interned (see the design note's §4). Every place that today falls back from
> `Rc::ptr_eq` to a structural compare must keep that fallback.

Approximate diff for the rewrite itself, by file, counted from the
`Rc<Term>`/`Rc<Type>`/`Rc<Motives>`/`Rc<Branches>` occurrences and the
`Rc::clone`/`Rc::new` traffic each file carries:

| file | lines | Rc-type occ. | `Rc::clone` | `Rc::new` | estimated diff |
|---|---|---|---|---|---|
| `term.rs` | 1 910 | 219 | 10 | 62 | ~900 (the enums, Ψ, `CtxEntries`, every constructor) |
| `rec.rs` | 4 800 | 8 | 8 | 730 | ~800 (construction-only: one arena parameter, 730 call sites) |
| `reduce.rs` | 2 427 | 15 | 415 | 172 | ~600 |
| `conv/dom.rs` | 1 972 | 173 | 151 | 54 | ~500 (the syntactic `Dom` impl *is* `Rc<Term>`) |
| `eval.rs` | 2 455 | 11 | 66 | 145 | ~350 |
| `typing.rs` | 2 604 | 1 | 111 | 77 | ~300 |
| `subst.rs` | 1 794 | 25 | 9 | 14 | ~300 (and `shared_*` collapses to an id compare) |
| `conv/dom/values.rs` | 1 846 | 14 | 38 | 50 | ~200 |
| `value.rs` + `value/shift.rs` | 2 509 | 21 | 12 | 24 | ~200 |
| `fmt.rs` | 646 | — | — | — | ~650 (rewritten whole, §3.5) |
| `bounds.rs` | 761 | 14 | 2 | 6 | ~150 (and it gets simpler) |
| `conv.rs`, `level.rs`, `checks.rs` | — | 4 | 23 | 9 | ~100 |
| **kernel total** | | | | | **~5 000 lines** |
| `crates/elab` (§6.2) | | 297 | — | ~1 200 | **~2 500 lines, 48 files** |
| `crates/cache`, `crates/cli`, tests | | | | | ~300 |

Plus the arena module itself (~400 lines with its tests) and the
`crates/kernel/tests` suites, which spell terms constantly.

**~8 000 lines, one commit, in the trusted base**, against a motivation that
§0 reduced to one constant factor and §5 shows is collectible for ~500.

## 7. Decision

**Rewrite later, behind a named trigger. Take §5.1 now.**

The recommendation in three lines:

1. **Now:** the value-arena slice (§5.1) — `issues/value-cache-memo-in-arena.md`'s
   lever, ~500 lines inside `crates/kernel`, gated by `scripts/bench --check`
   and RSS on the certificate and cold Omega. That issue's stated workloads
   are the five-node module and cold Omega; **add the `reused_callee`
   certificate**, because §2 shows the quantity it is chasing is an order of
   magnitude larger there (~22.9 M against 1.94 M) and the five-node module
   no longer bounds it.
2. **Next, and unblocked:** K1 (§1), which never depended on this issue.
3. **The term rewrite: deferred**, with the trigger written down.

The trigger, stated so it can be checked rather than argued:

> Take the arena-indexed term rewrite when, after the value-arena slice and
> K1 have landed, a profile of the certificate or a library check attributes
> **≥15% of kernel wall to `malloc`/`free`/refcount traffic over `Term`/`Type`
> nodes specifically** (not values, not closures), or when a workload needs
> intra-module parallel checking at a width where `Arc` contention is
> measurably non-flat (today it is flat to ±5% at W=8).

Two things that would *not* be reasons, recorded so they are not re-argued:
parallel checking (§0: already open, already flat) and hash-consing's
conversion shortcut (§4: `std`'s `Arc` already tests pointers first, so there
is no prize there to win).

**Why the slice was not implemented in this round.** Two reasons, both
deliberate. It changes a *kernel public type* the elaborator consumes —
`Eval::force` returns `Rc<Val<'v>>` and `certgen.rs:3039` mirrors that
signature — so it is outside this round's charter ("a bounded diff inside
`crates/kernel`, no elaborator API change"). And it has an owner already:
`issues/value-cache-memo-in-arena.md`, whose stated trigger is "a round whose
issue names kernel constant factors as the point", with its own workloads
(five-node module, cold Omega) and the falsifiers in §5.3 as its acceptance.
Those falsifiers are the work, not the type substitution. Handing it over
sized is the better trade than starting it in the corner of an evaluation
round — which is the same argument `issues/subst-rebuild-then-discard.md`
makes for itself, and it was right.

And one honest caveat about the recommendation: the §5.1 slice is *not* a step
toward the rewrite. It is the alternative to it. Taking it does not build an
arena for terms, does not thread an arena handle anywhere new, and does not
make the 8 000-line commit smaller. If the user's 2026-09-11 decision was that
the rewrite happens regardless, then the right first slice is instead `term.rs`
plus an arena module behind a type alias, and §5.1 is redundant work — that is
the one question this note cannot answer from the code, and it is the
coordinator's.

## 8. Raised in passing

- **The kernel's syntactic equality already short-circuits on pointers, and
  nothing says so.** `std`'s `ArcEqIdent` specialization makes
  `Arc<T>: PartialEq` test `ptr::eq` first whenever `T: Eq`
  (`library/alloc/src/sync.rs:3549`), which `Type`/`Term` derive. Every cost
  argument about `expected == inferred` in `typing.rs:678` and about
  `tm_eq_fast` depends on that specialization — including this note's §4 —
  and the kernel relies on it nowhere in writing. It is also a silent
  dependency on an unstable-internals detail of one `std` type: swapping
  `Rc`/`Arc` for any other handle (an arena id wrapper included) loses it
  without a compile error. Worth one comment in `term.rs` beside the
  `derive`, and worth knowing before anyone "cleans up" the alias.
- **`ty_eq_fast` is `Rc::ptr_eq`, `tm_eq_fast` is `==`**
  (`conv/dom.rs:1666-1673`). Given the specialization, `tm_eq_fast` is
  strictly stronger *and* pointer-first, so the asymmetry means types
  deliberately refuse the structural fallback and terms take it. That may
  well be a measured choice; it carries no comment saying so.
- **`value-metrics`' `type_cache_inserts` will stop being an allocation
  count** after §5.1 (see §5.3).
