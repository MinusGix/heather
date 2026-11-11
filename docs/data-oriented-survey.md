# Data-oriented design in the kernel and the elaborator — survey

Survey of 2026-11-02 over master `53ee29a` (plus a one-line local fix so that
tree compiles; see §0). Scope: places in `crates/kernel` and `crates/elab` where
memory layout, allocation, copying or lookup structure costs time, and where a
data-oriented rewrite (smaller nodes, shared or interned data, index-based
references, persistent structures, reused buffers, checkpoints instead of
copies) would pay. For each: where it is, what would change, the expected
benefit, and the cost or risk.

A sibling survey, `docs/implicit-state-machines-survey.md` (PR #352), reads the
same code for implicit state. The two meet at the `Elaborator` struct: that
survey groups its ~60 fields by lifetime ([[elab-field-lifetimes-explicit]],
[[decl-attempt-lifecycle]]); this one asks what cloning those groups costs.
§1's fix is phrased in its lifetime classes.

## 0. Method, and what was already known

**Profiles.** No hardware counters or `perf` on the cloud box, so the numbers
below come from a gdb sampler: one gdb session runs `heather check` and a timer
thread interrupts it every 30–100 ms and records every thread's stack
(`thread apply all bt`). That is time-fair sampling without symbol reloads.
Binary: the dev profile, whose `heather-kernel-lib`/`heather-elab-lib` are
opt-level 3 (`Cargo.toml`), at `HEATHER_KERNEL_WORKERS=1`, cold (no cache), so
every imported module is elaborated too. Two workloads:

- `docs/showcase/calc_parser.hthr`: 234 busy stacks over 7 s.
- `lib/std/num` and `lib/std/tactic`: 9 151 busy stacks over ~15 min under
  the sampler.

"x% of samples" below means the share of busy stacks with a matching frame
anywhere in the stack. That is an inclusive share, so rows overlap. The
sampler slows the program evenly; it does not move shares.

**Master did not compile.** `crates/elab/src/loops.rs:152` (from #351) builds
`measure::Binder` without the `value` field that #348 added. Every
measurement here ran with `value: None` added there; that line is not part of
this survey's change.

**Already owned, and not re-proposed here.** The kernel's value domain has
had the most data-oriented work: forced values in the query arena
([[value-cache-memo-in-arena]], closed), 16-byte environment handles and
32-byte closures ([[value-domain-allocation-constant]], whose list of
remaining items still stands), and the decision on arena-indexed kernel terms
([[kernel-arena-terms-frozen-prefix]]: later, behind a named trigger). Also
owned: the substitution's rebuild-then-drop pair ([[subst-rebuild-then-discard]]),
DAG-shared module images and the merkle walk ([[image-tree-walks-let-shared-terms]]),
one glued evaluator for the elaborator ([[elaborator-glued-evaluation]]),
interned module names in name resolution ([[resolver-lookup-constant]]), and
the bounds memo's accepted one-shot tax ([[bounds-metadata-taxes-one-shot-checking]]).

## Ranking

| # | Finding | Where | Measured share | Cost | Issue |
|---|---------|-------|----------------|------|-------|
| 1 | Speculative probes deep-copy the declaration attempt | `dispatch/operator.rs` ~282, `attempt.rs` `CheckNote` | ~20% of samples (clone + drop); a 3-line `Rc<Cx>` patch: cold wall **−20%** calc_parser, −3% rat, counters identical | low now, medium for the structural fix | [[elab-probe-clone-copies-attempt]] |
| 2 | The elaborator's `Cx` is a set of `Vec<String>` columns copied whole | `context.rs` `Cx` | 12–14% in a `Cx` clone or drop; 9–12% in `String::clone` | medium | [[elab-cx-persistent-binders]] |
| 3 | The `Level` inside every node is 24 bytes with `Arc` children; `Term` is 128 B and `Type` 72 B | `level.rs`, `term.rs` | 3–5% in `Level` code alone; it also sizes every node | medium–high (trusted base) | [[kernel-compact-level]] |
| 4 | The bounds memo is a 3 MiB direct-mapped side table | `bounds.rs` | 14% of samples on both workloads | high if taken (node header) | datum logged on [[bounds-metadata-taxes-one-shot-checking]] |
| 5 | Each substitution allocates fresh `Var` nodes for `id(Γ)` and a fresh memo table | `subst.rs` ~2263, `NodeMemo` | `id(Γ)` 1–4%, memo inserts 3–7% | low | [[subst-per-call-allocations]] |
| 6 | Layered registries scan every module's layer on a miss, hashing a `String` each time | `names.rs`, `types.rs`, `provenance.rs`, `gendefs.rs` | 3.5–4.7% in `names.rs` | low–medium | [[layered-registry-lookups]] |
| 7 | Smaller items | §7 | under 2% each | low | — |

Ranking weighs measured share, then the size and risk of the change. §1 and
§2 share a cause: the probe clones a `Vec<CheckNote>`, and each note holds a
whole `Cx`. The patch measured for §1 cuts that link; §2 would make every
other `Cx` copy cheap as well.

## 1. Speculative probes deep-copy the declaration attempt

**Where.** `op_carrier_head` (`crates/elab/src/dispatch/operator.rs` ~282, ~305)
probes each operator leaf on `self.clone()`, so that goals and diagnostics from a
failed candidate cannot leak. About a dozen other probes do the same (`lib.rs`
~1959, ~5191, ~5211, ~5259; `binding.rs` ~64; `host.rs` ~1569, ~2993, ~3183;
`traits.rs` ~2788). `Elaborator: Clone` is derived, so a probe copies every
field. The committed world is behind one `Rc`; the declaration attempt
(`attempt.rs` `DeclAttempt`) is not. Its `RefCell<Vec<…>>` logs are deep-copied,
and one of them, `check_notes`, holds a `CheckNote` per checking site met so
far, **each carrying a full clone of that site's `Cx`**: names as
`Vec<String>`, skeletons, aliases, type variables.

So a probe costs O(sites met so far × context depth) string and vector
allocations, and an operator chain probes once per leaf. Its drop pays the
same again.

**Measured.** On both workloads about a fifth of all samples are this clone
or its drop. calc_parser: 15.8% clone and 6.4% drop. num + tactic: 12.8% clone
and 7.4% drop. 8.8–11.5% are inside `CheckNote`'s `Cx` alone. It is also most
of why 32–42% of samples have an allocator function as the top frame.

A/B (`scripts/perf ab --before/--after`, 3 interleaved cold samples, dev
profile with optimized libraries): changing `CheckNote::cx` from `Cx` to
`Rc<Cx>` (three lines: the field, its constructor, one reader) moved
`docs/showcase/calc_parser.hthr` **7.59 / 7.51 / 7.68 s → 5.98 / 6.24 / 6.10 s
wall (−20%, separate)**. The kernel gate was unchanged, peak RSS was unchanged,
and 34 counter columns were identical in every sample. The counters that
varied are the address-keyed memo columns, which vary run to run within one
binary as well. `lib/std/num/rat.hthr`, which has few operator chains:
37.91 / 37.61 / 40.00 s → 35.72 / 36.64 / 36.71 s (−3.3%, separate). The win
scales with how many operator leaves a file probes.

**What would change.**

1. *Now:* `CheckNote { cx: Rc<Cx> }` (the measured patch); `ReflNote`'s `cx`
   likewise.
2. *Next:* a probe should not copy the attempt at all. Every log in
   `DeclAttempt` is append-only during an attempt, and the goal arena grows
   by allocation, so a probe can take a **mark** (the length of each log and
   the arena) and truncate back to it on discard: `O(fields)` instead of
   `O(contents)`. That is the transactional shape `module_delta::JournalSlot`
   already uses (a clone keeps lengths only). The per-attempt memos
   (`instance_matches`, `emitted_entries`) are pure caches; a discarded
   probe's entries can stay or be truncated, whichever their keys make sound.
3. In [[elab-field-lifetimes-explicit]]'s terms: a probe is a clone rule. It
   should *share* the committed world and policy, *share* the module pass
   (it must never get a pool of its own: §1 there), *mark* the attempt, and
   *copy* only the dynamic scope. The groups are being introduced on the
   lifetime-regrouping branch (`crates/elab/src/lifetimes.rs`: `pass`,
   `attempt`, `scope`, `policy`, `memos`). Once they land, `Elaborator::probe()`
   can say that once, and the dozen `self.clone()` probes stop each choosing
   by accident.

**Cost and risk.** Step 1 is three lines with no behaviour change; the
counters prove it. Step 2 changes what a discarded probe leaves behind, so it
needs [[decl-attempt-lifecycle]]'s structural reset first, or at least a
debug assertion that a probe's truncation restores the logs to their marked
lengths.

## 2. The elaborator's `Cx` is a set of `Vec<String>` columns

**Where.** `crates/elab/src/context.rs` `Cx`: `names: Vec<String>`,
`skels: Vec<Option<Rc<Skel>>>`, `aliases: Vec<Rc<Alias>>`, `tyvars: Vec<TyVar>`
(with `String` names), `dicts`, `index_ambiguity: Vec<(String, String)>`,
`op_locals: Vec<(String, String)>`, beside a `gamma: LocalCtx` whose entries
are already a persistent snoc list. There are 143 `cx.clone()` sites
(`inductive.rs` 15, `lib.rs` 15, `iwf_w.rs` 12, …), and every one copies each
column, allocating a fresh `String` per local name. Local lookup is
`cx.names.iter().rposition(|n| n == name)`, a string compare per binder
(`lib.rs` ~9914, `application/callable.rs` ~71, `dispatch/member.rs` ~477,
`statements.rs` ~460).

The kernel had this exact shape and fixed it ([[context-representation-clones]],
closed): Ψ and Γ became persistent spines. The elaborator's half never followed.

**Measured.** A `Cx` clone or drop is in 12–14% of samples. `String::clone`
is in 9–12%; most of it is `Cx::names`, and most of that arrives through §1.

**What would change.** Give `Cx` one persistent binder spine parallel to
`gamma.entries`, one node per binder: `{ name: Rc<str>, skel }`. Aliases,
type variables and dictionaries become persistent lists of `Rc` entries too,
so a clone is a handful of refcount bumps. Names should be `Rc<str>` at least,
or symbols interned per elaborator if [[resolver-lookup-constant]]'s interner
lands; then `rposition` compares words. `Cx::prefix(n)` becomes a walk to the
n-th node, which `CtxEntries::prefix` already does.

**Benefit.** Removes the O(depth) copy at all 143 sites and in every
`CheckNote` (making §1 step 1 unnecessary as a special case), and turns local
lookup into word compares.

**Cost and risk.** 192 `cx.names` uses, most of them `push`, `len` or
`rposition`. Behind accessors (`cx.lookup(name)`, `cx.name_at(i)`) it is
mechanical. `Cx::hygienic` renames every binder; on a persistent list it
rebuilds the spine once, the same cost as today. No kernel change.

## 3. `Level` sizes every node

**Where.** `crates/kernel/src/level.rs`: `enum Level { Var(UnivVar), Zero,
Succ(Rc<Level>), Max(Rc<Level>, Rc<Level>), Omega }`, which is 24 bytes.
Every annotated former stores one to three of them inline: `App` has two,
`Case` three, `Pi` two. `term.rs`'s size test pins `Term` at 128 bytes and
`Type` at 72, so each `Arc<Term>` allocation is 144 bytes. A `Var(LocalVar)`
leaf carries 4 bytes of payload in it. `Level::succ` allocates per `1+`,
`Level::constant(n)` allocates n nodes, and `shift`/`subst_at`/`inst_at`
rebuild the whole tree (one `Arc::new` per `Succ` and `Max`) even when
nothing moves. [[level-normalization-allocation]] closed with: "the level
cost that remains is drop glue on Level clones inside term construction,
which is a term-representation question". This is that question.

**Measured.** `Level` frames are in 3–5% of samples. Most of the cost is
indirect: every node is larger, and every rebuilt annotated node performs one
or two atomic refcount pairs per non-trivial level, which is part of what
[[subst-rebuild-then-discard]] measures.

**What would change.** A 64-bit `Level`: the common forms are encoded
inline, `Zero + k`, `Var(v) + k` and `Omega`, and a `⊔` tree is an `Arc` to
an out-of-line node. The form can be canonical: a sorted `(var, offset)` list
plus a constant, which is `LevelNf` already. Keep `Level::Zero` and
`Level::Var(v)` spelt as today (associated constants and constructors; only
~20 sites match on `Succ`/`Max` structurally), and give the rest a
`view()` enum.

With 8-byte levels, the largest `Term` variants (`Case`, `ElimCodeTm`) come
to ~80 bytes and `Type` to ~56 (its largest is then `GlobalTy`'s
`LocalSubst`). That is roughly a third less memory per node, more nodes per
cache line, and checker frames that hold `Term`/`Type` by value shrink with
them (the size test's own reason).

If levels are canonical by construction, `equiv` becomes `==`, and
[[fn-statement-level-trees]]' blocker goes away: that round measured that
canonicalizing at one emitter made formerly equal annotations differ in
spelling (misses doubled). That happens only because canonicity is per
emitter instead of per representation.

**Benefit.** Removes level drop glue and allocation outright, shrinks every
node, makes level substitution allocation-free in the common case.

**Cost and risk.** Trusted base. `Level` is part of the syntax, so its
printing (`write_exact` is the elaborator's determinism hash and the module
image's content identity) and image encoding change: a format bump. If it is
canonical-by-construction, terms that differed only in level spelling become
equal, which is sound (`equiv` is the judgement) but moves every interface
hash once. The kernel has no `unsafe`; a bit-packed level is possible without
it (an enum of `Small(u32 offset, u32 var-or-tag)` and `Big(Arc<…>)` is 16
bytes; 8 needs a packed `NonZeroU64` with manual decoding, still safe code).
Take the 16-byte version first: `Term` ~104, `Type` ~56.

**Status (2026-11-02).** Done as the 16-byte, canonical-by-construction
version: `Term` 104, `Type` 56, `Val` 72. perf ab, calc_parser cold: max
RSS −10%, kernel gate −7%, wall −4%, all separating. The 8-byte step needs
an interned join table: [[kernel-level-eight-bytes]].

## 4. The bounds memo is a side table

**Where.** `crates/kernel/src/bounds.rs`: per-node free-variable bounds,
memoized by `Arc` address in two thread-local direct-mapped tables of 2^16
slots each (~3 MiB), with keep-alive `Arc`s. Every `sub_tm`/`sub_ty` entry asks
`skip_term`/`skip_type`. Each ask is a thread-local `RefCell` borrow plus a
probe at a random slot of a table larger than L2, and an eviction can drop
the last reference to a dead subtree, so cascading frees get charged to
whoever evicted (`bounds.rs` ~180 shows up under `drop`).

**Measured.** 14.0% (num + tactic) and 14.5% (calc_parser) of samples.
[[bounds-metadata-taxes-one-shot-checking]] accepted ~1.17× in July and lists
cheaper-probe levers. This is a larger share on ordinary cold library checks
than that issue's last datum, so it is logged there.

**What would change, if taken.** The data-oriented answer is the one
`bounds.rs`'s own docs decline ("why a memo table and not a field on the
node"): a per-node header computed at construction from the children's
headers, O(arity) with no walk, carrying `bound`, `has_tail`, `uses`, and
optionally a structural hash and has-universe-variable / has-global flags
(Lean 4's `Expr.Data`). Every skip test then reads the node it is already
visiting. The construction invariant that the docs reject is real: ~1 200
elaborator construction sites build `Term`s directly. So the header only
makes sense together with a single construction API, which is also the
precondition [[kernel-arena-terms-frozen-prefix]] item 5 names and the chokepoint
[[elaborator-canonical-type-spelling]] wants. It is filed as a lever on the
bounds issue and as a consideration for the arena decision, not as its own
round.

**Status (2026-11-02).** Half of the 14% was not the side table's probe but
its keep-alive: an eviction dropped the last strong reference to a dead
subtree and paid its free on cold memory. Keys are now `Weak` and the
marker shares the slot's cache line; perf ab, calc_parser cold: wall −18%,
kernel gate −12%, max RSS −20%, all separating. The node header remains the
lever for what is left ([[bounds-metadata-taxes-one-shot-checking]]).

**Status (2026-11-10).** The header is taken, without the construction API
this section thought it needed ([[free-variable-bounds-in-the-node]]). It
is not computed at construction: the kernel's shared pointer keeps an empty
head beside the value, `bounds.rs` fills it on first demand with the same
pure function the table memoized, and the pointer empties it before it
hands the value out mutably. No construction site maintains anything, so
the 1,200 sites stay as they are. The tables, their weak keys and the
two-stage fill are deleted; what the change measured is in the issue.

## 5. Per-call allocations in substitution

**Where.** `crates/kernel/src/subst.rs`.

- `LocalSubst::id(ctx)` (~2263) builds `|Γ|` fresh `Arc::new(Term::Var(..))`
  leaves, 144 bytes each, every time a β-substitution is formed
  (`LocalSubst::id(&cx.gamma).extended(arg)`, e.g. `elab/src/application.rs`
  ~796 per explicit argument). There are 200 `LocalSubst::id(` call sites and
  276 literal `Rc::new(Term::Var(` sites.
- Every pure `Mapper` call builds a fresh `NodeMemo` (two `HashMap`s, `subst.rs`
  ~2000–2016, ~1412), which grows from empty by rehashing and is dropped with
  its keep-alives.

**Measured.** `id(Γ)` is in 1.3–3.7% of samples; memo inserts (`subst.rs`
~406, ~511, mostly allocation and rehash) in 3–7%.

**What would change.**

- Shared leaves: one interned `Arc<Term::Var(i)>` per index below a bound
  (say 4 096), handed out by `Term::var(i)`, plus the closed nullary leaves
  (`Zero`, `TmNat`, `Nat`). `id(Γ)` becomes `|Γ|` refcount increments. More
  sharing only helps the identity-keyed memos (`syntax_eq`'s pair memo, the
  typing memo); leaves are answered before any memo is consulted.
- Reused memo tables: a thread-local pool of `NodeMemo`s, cleared (capacity
  kept) when a call ends.

**Cost and risk.** Small and local to `subst.rs`/`term.rs`. One trap:
interned leaves are shared across the eight kernel workers, so their atomic
refcount is contended cache-line traffic. A per-thread intern table avoids
that, and the leaves stay `Send` either way. Measure with `scripts/perf ab`
at width 8 as well as 1. A lazy identity prefix in `LocalSubst` (the identity
part represented by its length, not materialized) is the larger version. It
departs from the paper's fully expanded `id_Γ`, so it is not proposed here.

## 6. Layered registries scan every layer on a miss

**Where.** `Names` (`crates/elab/src/names.rs` ~160), `Types` (`types.rs` ~65),
`Provenance` (`provenance.rs` ~58), `GenDefs` (`gendefs.rs` ~1203) are
`sealed: Rc<Vec<Rc<Layer>>>` plus a current layer, one sealed layer per module
in the world (282 `.hthr` files under `lib/`). Lookups walk the layers:
`entries(name)` chains *every* layer's `HashMap<String, Vec<NameEntry>>`, and
`global`, `inductive`, `constructor`, `member` and `has_record_field` do
`find_map` over them, so a miss (the common answer for
`has_record_field`, `declares_any_as`, `constructor` on a non-constructor) costs
one SipHash of the key per module. `global_name_at(abs)` does the same for a
dense `u32` coordinate that could index a `Vec`. `qkey` allocates a
`format!("{m}::{n}")` per lookup, and `note(name)` allocates a `String` per new
name while recording.

**Measured.** `names.rs` is in 3.5–4.7% of samples on these workloads. That
is smaller than §1–§5, but it grows with the world, and a native check's world
is the whole library.

**What would change.** Sealed layers never change. So a world can carry one
**merged index** of its sealed layers, built once when the world is loaded
(or merged LSM-style, so the layer count stays logarithmic) and kept beside
the `Rc<Vec<Rc<Layer>>>` it summarizes; lookups probe the merged index and
the small current layer. Hash the key once per lookup (or intern it,
[[resolver-lookup-constant]]), and make `by_abs` a `Vec<Option<Sym>>`.

**Cost and risk.** Module images serialize layers, and the merged index is
derived, so it needs no image format change. It must be rebuilt (or extended)
when a snapshot seals a new layer; `semantic_snapshot` is the one place.
Ambiguity semantics depend on seeing every entry for a name across layers;
the merged index keeps that by holding the concatenated entry list per name.

**Done (2026-11-02).** Built as log-many shared runs rather than one merged
index per world, so retained module states share them
(`crates/elab/src/layered.rs`; the measurement is in the issue's log).

## 7. Smaller items (under 2% each here; recorded, not filed)

- **Readback materializes the whole environment.** `readback.rs` ~523
  `subst` calls `Env::to_vec` (all entries) and fills unused positions with a
  placeholder, O(|env|) per closure read back even when `used` is 1. Iterate
  the innermost `used` entries instead. 0.3–2.1% of samples.
- **`GlobalBindings::push`** (`term.rs` ~2088) allocates a fresh identity
  token (`Rc::new(())`) per push and `make_mut`s the tail chunk, which copies
  up to 64 bindings whenever the tail is shared (after any clone of Ψ). A
  counter would serve as the identity; 0.9–1.9%.
- **Re-boxing elaborator terms.** 534 elaborator functions return `Term`/`Type`
  by value against 56 returning `Rc`, and 154 sites do
  `Rc::new(x.clone())`/`Rc::new((*x).clone())`. Each copies a 128/72-byte node
  and mints a new identity for an existing node, so the root of every
  re-boxed term misses the pointer-first equality and the address-keyed memos
  ([[kernel-syntactic-eq-relies-on-arc-specialization]]). Returning `Rc`
  where a caller re-boxes is a slow, local cleanup; the single construction
  API of §4 is where it would be enforced.
- **AST clones.** `syntax::ast::Expr` is an owned tree of `Box`es and `String`s.
  It was under 2% here, the largest being `loops.rs` ~74 `has_loop`, which is
  new with #351. If the elaborator's need to clone AST grows,
  `Rc`-shared subtrees or an arena-indexed AST would be the lever.

## 8. What the kernel trigger now says

[[kernel-arena-terms-frozen-prefix]]'s trigger for the term rewrite is "a
profile attributing ≥15% of kernel wall to malloc/free/refcount traffic over
`Term`/`Type` nodes specifically". These profiles have 32–42% of samples with
an allocator frame on top. Most of it is §1 and §2, elaborator-side copies of
non-term data, so the trigger has **not** fired, and it should be re-read
after §1 and §2 land, when the remaining allocator share is much more likely
to be terms. §3 and §5 are the representation-preserving steps that would
shrink that share without the rewrite.
