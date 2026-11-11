# The declaration cache, v1 — design

First concrete slice of `issues/parallel-checking-and-caching.md`, designed and
implemented 2026-08-06. That issue owns the architecture — the interface-split
invariant, the Merkle-DAG scheme, the trust ladder, the daemon, the command
split, merge. This document owns only what v1 makes *concrete*: the hash
function, the exact rendering hashed, what a "declaration" is at today's CLI
granularity, the on-disk format, the command surface, and what "skip" actually
skips. Every section names the assumption it rests on, because most of them are
the kind that fails silently.

The one-line summary: `heather check --cache` keys each declaration by a
content hash of its elaborated form with global references replaced by the
hashes of their referents, and skips the kernel gate — and only the kernel gate
— for keys a previous run recorded as accepted. On `lib/certgen/ir_v1.hthr` the kernel
gate is 94% of the run (`crates/elab/benches/baseline.tsv`), so this is most of
the wall clock.

Measured on that file, paired min-of-3 through the release CLI, 2026-08-06:

| run | time | |
|---|---|---|
| `heather check` (unflagged, unchanged) | **46.3 s** | the baseline |
| `heather check --cache`, cold | **53.3 s** | +15%: one hash of every declaration |
| `heather check --cache`, warm | **7.5 s** | **sheds 84%**, 6.2× |

The warm number is the round's headline and the cold one is its price: v1 buys
a 6× inner loop by making the first run 15% slower. §10 says where that 15%
goes and what would remove it.

**Since 2026-08-06 the table above is history.** The structural hash walker of
§12 replaced the rendering these numbers were taken over: the warm run is now
**2.2 s** and the cold overhead is single-digit percent and near the noise
floor, measured paired against this same binary. §12.4 has the current figures,
and §3 is marked superseded.

## 1. What is cached, and what a cache hit still pays

The unit is the **kernel gate**: the `typing::check_type` + `typing::check_term`
pair that every finished declaration passes before it is committed. There are
exactly three such sites in the tree, and they have the same shape — gate a
finished `(ctx = ·, ty, level, body)`:

- `crates/elab/src/lib.rs`, `elab_decl_inner` — user `fn` and `theorem`.
- `crates/elab/src/gendefs.rs`, `push_gen_def` — the elaborator-generated
  definitions (`μ_D`, tag predicates, child projections, `D#code`).
- `crates/elab/src/quote.rs`, `elab_meta_decl_inner` — a `meta fn`, checked at
  `Layer::Meta`. *(Added 2026-08-13,
  `issues/elaborator-snapshot-across-test-binaries.md`: measurement found the
  `match code` shells' meta checks dominating warm elaborations of
  `lib/certgen/certgen_code.hthr` — the seam's original "two sites" left the file's
  single most expensive gate uncovered.)* Two things distinguish the site, and
  `GateItem` carries both: the **layer** is part of the item's identity (the
  same `(ty, body)` at two layers is two kernel questions; the hashed binding's
  layer byte is what keeps the keys apart), and the checked item **never lands
  in Ψ** (`lands_in_psi: false`) — it registers in the meta-def table, so the
  cache must neither leave a pending interface hash for the next Ψ binding to
  absorb nor let its `admits`/`accepted` memo, which is keyed on Ψ length,
  answer for a neighbour at the same length. Both hazards are wrong-vouch
  class; both are guarded in `crates/cache/src/lib.rs` and pinned by
  `crates/cache/tests/end_to_end.rs`'s meta group.

A hit skips both calls. It does **not** skip:

- parsing,
- elaboration, including every trip the *elaborator* makes into the kernel
  (`whnf`, `conv_type`, unification). Those are elaboration deciding
  something, not the kernel re-checking a result — the same line
  `docs/frontend-benchmarking.md` draws for the phase split.

So the honest claim is "a warm run pays parse, elaborate, and its own hashing,
and nothing else". It is not a no-op re-check and must never be described as
one. On `lib/certgen/ir_v1.hthr` that is 7.5 s against a 46.3 s check, of which
elaboration is about 1 s and the hashing is the rest — the cache's own cost is
the larger half of a warm run, which is where the next round of work on this
went (§10, spent in §12: 2.2 s, still ~57% hashing). A cache that also skipped
elaboration would be a different, larger design (it would have to serialize Ψ),
and it is not this round.

*Assumption named*: that the elaborator's own kernel calls are not themselves
worth caching. True today at a 94/6 split; the issue's own caveat says that
ratio is not permanent.

## 2. Hash function: first-party SHA-256

**Decision: a first-party SHA-256** (`crates/cache/src/sha256.rs`, ~130 lines),
not a dependency, and not the determinism test's FNV-1a.

FNV-1a is out on its own terms: 64 bits and non-cryptographic. It is right for
a golden regression constant, where a collision means a test does not fire.
Here a collision means a *wrongly accepted proof* — the cache says "the kernel
accepted this" about a declaration the kernel never saw. That is the one
failure mode this whole design exists to not have.

Dependency or first-party is the real question, and
`issues/dependency-policy.md` does not decide it by itself. Its rule is "the
kernel stays at zero; everything above it has no trust story to protect and
should spend freely". The cache is the first thing above the kernel that
*does* have a trust story: at rung 1, believing a cache entry is believing the
hash. So the kernel's argument — a bug here is in the soundness set, and the
primitive is first-party by nature — applies to this one module even though it
does not apply to `crates/elab` or `crates/cli`.

And SHA-256 is exactly the shape of thing the kernel argument says to write
yourself: a fixed, frozen specification (FIPS 180-4) with published test
vectors, no design decisions, ~130 lines of `u32` arithmetic, and a
correctness criterion that is checkable rather than arguable. The
implementation is pinned against the NIST vectors plus a long-message vector
(`crates/cache/tests/sha256.rs`), which is a stronger guarantee than "we
depend on a crate that is probably right".

*Strengthened 2026-08-06.* "Pinned against the published vectors" was the weak
form of that claim — four short messages and one long one leave every length
that is not 0, 3, 56, 112 or a million untested, and most of SHA-256's
interesting behaviour is in the padding. The same file now runs `sha2` as a
**differential oracle**: a dev-dependency of this crate alone, never linked
into anything shipped, asserting byte-identical digests over every length
0..=300 with two contents each, multi-block inputs to 1 MiB, and six
adversarial chunkings including byte-at-a-time around empty updates. No
divergence was found. The dependency does not weaken the argument above — it
is adopted precisely *because* the implementation is ours, and
`issues/dependency-policy.md`'s log records it as the general rule that a
first-party implementation of a frozen specification should be differentially
tested against a mainstream one.

*Assumption named*: SHA-256's collision resistance. If that falls, so does
every content-addressed build system; we are not distinguished here.

*Not adopted*: this does not create a project policy against hash crates. It
decides one module, for the reason that the module is trust-bearing. A later
consumer above the kernel with no trust story should still spend freely.

## 3. The rendering hashed, and the Merkle substitution

> **Superseded 2026-08-06 by §12.** This section records what v1 decided and
> why, and the reasoning is left standing because §12 is best read as the
> answer to it. But the code it describes is gone: the rewriting sink was
> deleted with the structural walker, and neither the printed-form assumption
> below nor the three canaries that pinned it exist any more. Read §3 as
> history; read §12 for what the cache does.

**Decision: `heather_kernel::fmt::write_exact` streamed through a rewriting
sink**, not a hand-written serializer.

`write_exact` (landed 2026-08-06) is the kernel's budget-bounded `Debug` with
the elision disarmed: total, deterministic, streaming, and already the thing
`issues/elaboration-determinism.md`'s golden hash is taken over. Reusing it
means the cache's notion of "same term" and the determinism guarantee's notion
of "same term" are the same notion, by construction rather than by two
implementations agreeing. Writing a second exhaustive renderer in the cache
crate was considered and rejected: it would be ~500 lines tracking ~80 kernel
variants, and its only advantage — an exhaustive `match` breaking the build on
a new kernel variant — is bought more cheaply by §3.2's canaries.

### 3.1 Why a rewriting sink

The issue's decision 2 is that references are replaced by the *hash of the
referent's interface*, so that keys are position-independent (the kernel
telescope is positional; any key that keeps a Ψ index dies on the first merge
that renumbers a suffix). The kernel prints a global reference as `u12^{…}`
(term), `U12^{…}` (type), or `g12` (a context-variable base), where the number
is a de Bruijn *level-from-the-end*: for a binding stored at absolute index
`i`, its subterms were built when Ψ had length `i`, so `abs = i − 1 − var`.

The sink is a small state machine over the character stream `write_exact`
produces. It recognizes `u`/`U`/`g` immediately followed by ASCII digits and
not preceded by an ASCII alphanumeric, resolves the index to an absolute Ψ
position, and emits the 64 hex characters of that binding's **interface hash**
in place of the digits. Everything else passes through byte-for-byte, and
nothing is buffered beyond the digit run.

The sink is **fail-closed**: if an index resolves outside the known prefix, the
whole hash computation returns `None` and the declaration is simply not
cacheable. A malformed reference can never produce a key.

*Assumption named, loudly*: that `u<digits>` / `U<digits>` / `g<digits>` are
the only spellings of a global reference `write_exact` can emit, and that no
other production of `crates/kernel/src/fmt.rs` matches that pattern. Both
halves were verified by reading every format string in that file on
2026-08-06. Both halves are *the* fragility of this design: a kernel change to
the printed form of `GlobalTm` would silently reintroduce positional keys, and
positional keys can collide across contexts.

### 3.2 What keeps that assumption honest

Three tests, and they are the reason a hand-written renderer was not needed:

- **The rewriter fires** (`rewrites_every_global_spelling`): terms containing
  `GlobalTm`, `GlobalTy` and a `CtxBase::Var` base render with no surviving
  `u<d>`/`U<d>`/`g<d>` and with the referent's hash present. If the kernel
  renames the form, this fails.
- **Position independence** (`the_same_declaration_at_two_positions_agrees`):
  the same declaration over prefixes of different lengths hashes the same.
  This is the property the rewriter exists for, tested end-to-end rather than
  by inspecting the rewriter.
- **The rewriter does not over-fire** (`unrelated_text_is_not_rewritten`): a
  term whose rendering contains `sup`, `Unit`, `⟨⟩0`, `wk^2_g0` shapes is
  unchanged where it should be.

*Not claimed*: injectivity of `write_exact` itself. The cache inherits exactly
the assumption the golden-hash test already makes ("injective enough for
hashing", `crates/kernel/src/fmt.rs`). Substituting hashes for indices does not
weaken it: two references print alike after rewriting iff they denote the same
binding.

## 4. What a "declaration" is, and how the DAG is built

At today's CLI granularity a declaration is **one `GlobalBinding`**. That is a
smaller unit than a source `fn`/`theorem`/`inductive` item, and it is the right
one, because it is the unit the kernel gate operates on and the unit Ψ stores.

Three consequences fall out for free, which is the sign the unit is right:

**Theorem interfaces are already interface-shaped.** The issue's rule — a
theorem's downstream interface is its statement, a `fn`'s includes its body —
is *already* the shape of `GlobalBinding::Tm`: a theorem is pushed with
`body: None` (proofs are opaque, so conversion never sees them), a `fn` with
`body: Some(_)`. So "interface = the binding as stored in Ψ" implements decision
1 with no extra rule, and the statement-vs-proof sensitivity of §5 is not a
feature that had to be built.

**Generated definitions hash independently.** `gendefs` pushes `μ_D`, the tag
predicates, the child projections and `D#code` as ordinary bodied `Tm`
bindings through the same gate. They therefore get their own keys and their own
cache entries, rather than riding their parent inductive. This is the cheaper
choice (no notion of "parent" is needed anywhere) and the more useful one: two
inductives that generate an identical `μ` share one entry, and an inductive
whose declaration changes only in a way that leaves some generated defs
identical re-uses those. The issue's "generated defs derive deterministically
from the declaration" is preserved either way — deriving deterministically is
exactly what makes their independent hashes stable.

**Imports and the prelude need no special case.** The CLI already flattens the
import closure into one Ψ in topological order (`docs/modules-design.md` §3.2),
so an imported declaration is a Ψ binding like any other and its dependents
reference it by hash like any other. The prelude is the same (it is "the
degenerate module"), with one wrinkle: it is elaborated inside
`Elaborator::with_prelude()`, before the CLI can install a gate, so prelude
declarations are never *cached* — they are only *hashed*, by the same
sync-the-prefix path that absorbs any binding pushed outside a gate site. The
prelude is milliseconds; paying it every run is not worth an API to avoid.

**Inductives** push nothing to Ψ themselves — they register elaborator tables,
and their kernel content is exactly the generated definitions above. So
"inductive = the whole declaration" needs no separate treatment either: the
declaration's kernel-visible content *is* its gendefs.

*Assumption named*: that Ψ grows only by `push`, in declaration order, and that
a binding's subterms are scoped over its own prefix. Both are stated invariants
of `GlobalCtx` (`crates/kernel/src/term.rs`).

## 5. The two hashes, and red-green

Each binding gets an **interface hash**; each gate call gets a **check key**.

```
interface(i) = SHA-256( "heather/iface/2\0" ++ walk(bindings[i]) )

check_key    = SHA-256( "heather/check/2\0" ++ interface ++ 0x1c )
                                                        -- a transparent decl
check_key    = SHA-256( "heather/check/2\0" ++ interface ++ 0x1d
                                            ++ walk(proof term) )
                                                        -- a theorem
```

where `walk` is §12's framed byte encoding, substituting referent interface
hashes for global references against the already-computed prefix, and the
domain-separating prefixes keep the two hash families from ever being confused
for one another. (In v1 `walk` was `rewrite(render(…))`, the domains ended
`/1`, and the two check-key shapes were spelled `"|def"` and `"|proof:"`; the
*structure* of this section is unchanged, which is the point — §12 replaced
the encoding and nothing else.)

A transparent declaration's key is its interface hash and nothing more,
because a `fn`'s body is *in* its interface — so only a theorem is rendered
twice, and the total rendering a declaration costs is its own content exactly
once. That is not a micro-optimization: rendering is the whole of the warm
run's cost, and the first cut of this hashed everything twice and made the
cold run 29% slower instead of 15%.

The proof term appears in the check key and *not* in a theorem's interface
hash. That split is the whole design:

- Editing a **proof body** under an unchanged statement changes the check key
  (so that theorem is re-checked, correctly — the kernel has never seen this
  proof) and changes **no** interface hash (so no dependent's key moves, and
  nothing downstream is invalidated). Red-green, obtained structurally rather
  than by comparing outputs after the fact.
- Editing a **statement** changes that theorem's interface hash, hence the
  rewritten rendering of every declaration that references it, hence their
  check keys — and only theirs. A declaration that never mentions it is
  untouched however far down the file it sits.

For a `fn`, the body is in both, because a `fn` body is δ-relevant: a dependent
whose conversion could unfold it must be re-checked. That is decision 1, and it
is the only asymmetry.

Fuel is deliberately **not** in the key. Success is monotone in fuel (fuel
exhaustion is a failure, so a check that succeeded under some budget succeeded),
so including it would cause misses without buying soundness.

## 6. Trust: rung 1, and what that honestly means

v1 is rung 1: an entry says "some run of this kernel accepted a declaration
with this key", and a hit believes it. Two things follow, and both are stated
here rather than discovered later.

**The kernel-semantics fingerprint.** An entry is meaningful only against the
kernel that produced it. v1's fingerprint is a SHA-256 over the *source text of
`crates/kernel/src`*, computed by `crates/cache/build.rs` at build time and
compiled in. It is deliberately conservative: a comment change in the kernel
invalidates the cache. That is the right direction to err, and it makes
"a changed kernel invalidates loudly" a property of the build rather than of
someone remembering to bump a constant — which is the failure mode a
hand-maintained epoch number has. A reader believes only the entries its own
kernel recorded and says so when there are none; since
`issues/verdict-store-one-kernel.md` other kernels' entries stay in the file,
in sections of their own (§8), rather than being discarded.

What it should become: a fingerprint of the kernel's *semantics* rather than
its text — the conversion rules, the strip discipline, the layer table — so
that a pure performance round does not invalidate a corpus of traces. That is
the same distinction the issue's trace-format rule draws ("decisions, not
steps"), and it is the same fingerprint; when rung 2 lands, both should read
one value. Recorded, not built.

**What is and is not detectable.** At rung 1:

- *Detectable*: a stale kernel (fingerprint), a bad format version, a
  truncated or bit-flipped file (a body checksum line), a malformed entry
  (field count, hex shape). Any of these leaves the reader with no verdicts
  and forces a full re-check, loudly (a stale kernel's section, and a damaged
  section of another kernel, are not this reader's to believe or to keep
  reading; §8).
- *Not detectable*: a **forged** entry. Anyone who can write the cache file
  can compute the key of a declaration with a bogus proof and insert it, and
  can recompute the checksum while they are there. The checksum is integrity
  against accident, not against an adversary. Rung 1's trusted base is
  literally "the OS gave us a file nobody tampered with", exactly as `.olean`'s
  is, and the honest statement is that `--cache` is for inner loops and the
  unflagged `heather check` remains the gate.

The negative-control test asserts the detectable half and *documents* the
undetectable half rather than pretending to test it.

## 7. Command surface

**Decision: an opt-in flag on `heather check`, not a new subcommand.**

`heather check [--cache] [--cache-dir <dir>] <file>…`

- Without `--cache`: byte-identical to today. No reads, no writes, no output
  change. This matters beyond conservatism — the merge/CI gate and
  `scripts/bench-frontend` both drive plain `heather check`, and a cache that
  changed their meaning would have changed what the benchmark measures.
- With `--cache`: read and write `.heather/cache` (or `--cache-dir`). Hits skip
  the gate; misses run it and are recorded.

No `quickcheck` yet. The issue's eventual split is
`quickcheck` / `check` / `build`, where `check` **re-earns** entries and only
`quickcheck` trusts them. Shipping v1's trusting behavior *as* `heather check`
would have to be renamed away the moment that split lands; shipping it as a
flag means `heather check` keeps the meaning the split gives it, and `--cache`
becomes `quickcheck`'s implementation rather than its rival. The flag is the
smaller promise.

**Trust is visible.** The Coq `vos` scar is the reason the output line changes
whenever `--cache` is on, whether or not anything was cached:

```
lib/certgen/ir_v1.hthr: ok (cache) — 4 declarations kernel-checked, 130 accepted from cache
```

The bare `path: ok` is reserved for a full check and is unreachable under
`--cache`, so no green line can be mistaken for a green *full* line, and a
gate can grep for the absence of `(cache)`. A discarded cache says why:

```
cache: kernel semantics changed since these 134 entries were written — discarding
```

## 8. On-disk format

`.heather/cache/entries-v1.tsv`, one repo-local directory, tab-separated,
inspectable with `cat`, and versioned. Since format 4 the file holds one
section per kernel that has written to it, most recently used first
(`issues/verdict-store-one-kernel.md`):

```
heather-cache	4
kernel	<64 hex fingerprint>	<last used, unix seconds>	<64 hex checksum>
ok	<64 hex check key>	<64 hex interface hash>	<name>
…
kernel	<another kernel>	<last used>	<checksum>
…
```

Format 1–3 had one `kernel-semantics` and one `checksum` line for the whole
file, so a reader with another kernel discarded every entry and its save
overwrote them. That was free with one checkout; with several sharing a store
through `HEATHER_CACHE_DIR` it made the store ping-pong between kernels. Now a
reader believes only its own kernel's section and carries the others through
its save verbatim; a section leaves when it is unused for
`store::MAX_AGE_SECS` or falls outside the `store::MAX_KERNELS` most recently
used, never because another kernel saved last. A run that only hit renews its
section's stamp once a day (`store::REFRESH_SECS`) so a fully warm kernel does
not age out. Trust is unchanged: a verdict is accepted only under the kernel
that recorded it. A format-3 file is still read, as one unstamped section: its
keys mean what they meant, and the bump changed only the shape.

Four decisions in that shape:

- **Text, not binary.** The file is small (one line per declaration) and the
  first question anyone asks of a cache is "what does it think it knows".
  `grep` answering that is worth more than the bytes.
- **A verdict column** (`ok`), not an implied one, so failures could be
  recorded later without a format break.
- **The name is trailing metadata**, per Unison: it is there for the human
  reading the file and is never consulted. Two declarations with one key are
  one entry whatever they are called.
- **Extra fields are ignored by the reader.** That is the room rung 2 needs: a
  trace lands as a fifth column (`ok <key> <iface> <name> trace:<path>`) read
  by a version that understands it and skipped by one that does not. The
  format does not have to change to make room; it already has the room.

Each section's checksum covers its entry lines and is checked when that
section is read, so another kernel's damaged section is that kernel's miss and
is dropped by the next save, never this reader's. Writing is whole-file, at
the end of a successful run.

## 9. One invariant the implementation added

The cache holds a vector of interface hashes describing **one** Ψ, and the CLI
builds a fresh elaborator — hence a fresh Ψ — per root file, while sharing one
cache across all of them (so that a declaration two roots have in common is
checked once). `Cache::begin_run` is what reconciles those: it clears the
prefix and keeps the entries, which is exactly right, because entries are
content-addressed and belong to no particular Ψ while the prefix is nothing
but a view of one. `Inner::sync` additionally discards the prefix whenever Ψ is
*shorter* than it, so a caller who forgets recomputes rather than hashes
against referents that are not there.

## 10. Where the remaining cost is *(as of v1; §12 spent it)*

The cache's own work is one `write_exact` rendering of every declaration, fed
through the rewriting sink into SHA-256. On `lib/certgen/ir_v1.hthr` that is ~7 s: 15%
on top of a cold check, and ~90% of a warm one. Two things it is *not*: it is
not double work (§5 removed that) and it is not the hash (SHA-256 at these
sizes is a fraction of it) — it is `std::fmt`, formatting tens of megabytes of
tree through `Formatter` machinery to produce bytes nobody reads.

The fix, when it is worth it, is a structural hash walker over `Term`/`Type`/
`Level` that feeds the hasher without formatting. It was considered and
declined for v1 (§3), and the reason to revisit is now a number rather than a
preference: it would make the cold run's overhead approximately free and the
warm run approximately elaboration-bound. It also brings the compiler-enforced
totality an exhaustive `match` gives, which would retire §3.1's assumption
outright. Recorded on the owning issue rather than done here.

## 11. What v1 deliberately does not do

Each of these is the issue's, not this document's, and none is started here:
the daemon and the shared telescope, anything multi-session, merge semantics,
`quickcheck`/`build` as commands, certificate replay and traces (format
headroom only, §8), and any kernel change at all. The elaborator's only new
surface is one trait and one setter (`crates/elab/src/gate.rs`), which is what
"a minimal hook to expose per-declaration boundaries" was allowed to cost.

## 12. The structural hash walker (2026-08-06), and what it retired

§10 named the successor slice and it landed the same day. `crates/cache/src/
merkle.rs` is now an exhaustive walk over `Term`/`Type`/`Level`/`LocalCtx`/
`LocalSubst`/`Motives`/`Branches`/`GlobalBinding`, feeding tags and fields
straight into SHA-256. The rewriting sink, `rewritten_text`, and the three
canaries that pinned §3.1's printed-form assumption are **deleted**: two
definitions of cache identity is the disagreement risk v1 avoided by reusing
`write_exact` in the first place, so the choice is one or the other, not both.
`heather_kernel::fmt::write_exact` stays — `issues/elaboration-determinism.md`'s
golden hash is taken over it and nothing in this round touches elaboration.

### 12.1 Framing, and the injectivity argument

Four kinds of piece: a one-byte **tag** unique across *all* node kinds of all
sorts (the value space is partitioned — `0x01–0x1F` the structural sorts,
`0x20–0x3F` `Type`, `0x40–0x7F` `Term` — not reused per sort); a fixed-width
**`u32`** little-endian for indices, binder counts and sequence lengths; a
32-byte **referent hash**; and a **sub-encoding**, recursively. Sequences are
length-prefixed. Nothing else is variable-length.

The encoding is prefix-free, hence injective, by induction on the tree: the
leading tag determines the node kind, the node kind determines exactly what
follows (how many fixed-width integers, how many sub-encodings of which sorts,
with any repetition count read from a length field that precedes it), so a
decoder can be written that consumes exactly the bytes one node occupies. A
function with a left inverse is injective.

That is strictly **stronger than what v1 claimed**. §3.2 explicitly did *not*
claim `write_exact` was injective; it inherited "injective enough for hashing"
from the golden-hash test. The gap was real and this round found it:
`fmt`'s `Debug` for `Branches` prints **37 of the struct's 52 fields**. Every
`Vec`/`Fin`/`Wf` branch and every strict-equality branch is absent, so under v1
two code recursors differing only in (say) `tm_elim_wf` had **the same cache
identity** — a hash collision by construction, not by luck. Nothing in `lib/`
exercises it today, which is exactly the point: a stated assumption pinned by
canaries was the wrong instrument for a totality property, and an exhaustive
`match` is the right one. `tests/merkle.rs::every_recursor_branch_is_hashed`
now walks all 52 fields one at a time and demands 52 distinct hashes.

*The exhaustiveness is the deliverable.* Every `match` in the walker has no
`_` arm and every struct is destructured with no `..`, so a new kernel
constructor or a new `Branches` field is a **compile error** in the cache, not
a silently unhashed field. §3.1's assumption is not weakened, restated or
better tested — it no longer exists.

### 12.2 The substitution sites

The Merkle substitution is now keyed on constructors rather than on spellings.
`GlobalVar` occurs at exactly five places in `crates/kernel/src/term.rs`, and
the walker replaces the index with the referent's 32-byte interface hash at
each: `Term::GlobalTm`, `Type::GlobalTy`, `CtxBase::Var` (a context's base),
`SubstTail::Wk`, and `SubstTail::Empty`'s `base` (through `CtxBase`). The last
two were reached in v1 only because they happened to print `g<digits>`.

The replacement is fixed-width, so framing is untouched, and it drops the
*position*, which is the property the scheme exists for. Fail-closed is
unchanged and still needed: an unresolvable or **poisoned** reference (a
binding whose own hash failed) discards the whole computation, and the
declaration is re-checked rather than mis-keyed.

### 12.3 The format bump, and why the domain strings bumped too

`store::FORMAT` is **2**. `store::FILE` deliberately is *not* renamed: a new
filename would leave a v1 file unread and the run would look like a first run,
whereas keeping the path routes the stale file through `parse` and produces
`cache: the cache file is format 1, this build writes 2 — discarding`. Loud
beats tidy; the version lives in the header and the `v1` in the filename is a
fossil.

The domain strings bumped with it (`heather/iface/2\0`, `heather/check/2\0`)
even though the format version already invalidates every stored entry. The
reason is that the domain string names the **scheme**, not just the family:
v1's preimage was a rewritten rendering and v2's is a framed byte stream, and a
domain that did not move would leave "a v1 key equals a v2 key" as an
arithmetic accident rather than an impossibility. The two costs nothing and
the argument for content addressing is that identity is decided by
construction.

### 12.4 Numbers

Interleaved A/B through the two release binaries, min-of-3 alternating so
machine drift hits both equally, 2026-08-06 — *under a concurrent Coq build*,
so the absolute numbers run ~10% above §0's and only the paired ratios mean
anything:

| run | v1 (rendering) | v2 (walker) |
|---|---|---|
| `heather check`, unflagged | 49.2 s | 48.1 s |
| `heather check --cache`, cold | 57.2 s (**+16.3%**) | 51.4 s (**+6.8%**) |
| `heather check --cache`, warm | 7.9 s | **2.2 s** |

The warm run is **3.6× faster** and the cold overhead is more than halved. The
warm figure is the one to read: against the frontend baseline's 0.93 s of
parse + elaboration for this file (`crates/elab/benches/baseline.tsv`), the
cache's own work fell from ~7.0 s to ~1.25 s — a **5.6×** on the thing §10
said was `std::fmt` rather than SHA-256, which is now confirmed rather than
inferred.

**What the warm run is bound by now**: roughly 0.93 s elaboration (43%) and
~1.25 s walking-and-hashing (57%). So "approximately elaboration-bound" is the
right order of magnitude but not yet true — the walk is still the larger half,
where it was ~90% before. The remaining walk cost is real work (it visits
every node of every declaration and feeds SHA-256 tens of megabytes), so the
next lever is not a faster encoder but *not walking unchanged declarations*:
memoizing per-`Rc` subtree hashes, or a cache that skips elaboration too,
which §1 already notes is a larger design.

**Hash once per declaration (2026-09-17).** The `admits`/`accepted` pair asks
one question, and answering it twice doubles the hashing: the first
instrumented reading of a cold check (`issues/merkle-walk-cold-share.md`)
found the interface walked twice per declaration at the inline gate and the
whole identity computed twice at the deferred join, where `accepted` arrives
with the Ψ snapshot its item was queued under. The cache now keeps an exact
map of *open questions* keyed by Ψ position (opened by `admits`, closed by
the answer, killed by `KernelGate::abandon` when a declaration fails — the
elaborator keeps going after a refusal and the next declaration lands at the
same position), and the hasher compresses with the CPU's SHA extensions
where it has them (`src/sha256.rs`, `compress_blocks_sha`: Intel's reference
schedule over `std::arch`, selected per hasher, the portable rounds kept as
the same function for every other target and checked against it by the
oracle tests). That is the one `unsafe` in the workspace; the cache crate
carries `deny` where the workspace says `forbid`, for exactly those two
functions. `sha2`'s hardware path measured the same rate, so the crate stays
at zero shipped dependencies. What remains of the walk is its content: the
walker visits shared structure about twice over on a large module, so a
per-`Rc` memo is a 2× ceiling, not the lever it was once assumed to be.

**The replay asks the same question (2026-09-17).** A module replayed from
its semantic image used to be kernel-rechecked in full — every stored
definition's body — while the same store vouched for those declarations on
the source path, so a warm check of an unchanged file cost more than a check
after an edit. A stored definition is the binding `GateItem::binding`
produced at the cold gate, over the same Ψ prefix, and the key is content
with the name as metadata (§3); so `Elaborator::recheck_extension` now asks
`admits` over each stored definition, checks only the misses and records
them with `accepted`, and abandons its questions if the replay is rejected.
A stored theorem has no proof to ask about and keeps its statement check.
The trust is unchanged: rung 1 either way, and a body the store never saw
still faces the kernel.

**Statement verdicts (2026-10-29).** That kept statement check was, by
2026-10-29, the whole of a warm native world's `image_recheck`: every
theorem and opaque declaration of every replayed module re-checked on every
load, with every verdict stored
(`issues/native-process-fixed-cost.md`). Replay now asks
`KernelGate::admits_statement` about a declaration without a body, and
records a passed statement with `statement_accepted`. The key is a third
family,

```
statement_key = SHA-256( "heather/statement/1\0" ++ interface )
```

which is enough because the interface renders the statement itself and
every referent as its own interface: a statement check is type formation
over those referents' types and the δ-visible bodies their interfaces carry,
and nothing else. A statement check that opened a sealed proof keeps no
verdict, by the rule `accepted` follows.

**What the build checked, its first replay finds (2026-11-11).** Two kinds
of binding still faced the kernel on the first replay of an image, though
the build that wrote it had checked both
(`issues/first-replay-rechecks-what-the-build-checked.md`). A theorem's
build-time verdict was kept under its check key only, and a replay asks
under the statement key: `accepted` now writes both when the theorem lands
in Ψ with an empty context and nothing withheld, which is when the gate's
statement check is the replay's. The statement was the first half of what
the gate checked, and its key is one hash of the interface hash in hand. A
check that opened a sealed proof keeps neither, as before. And the
resolver's minted derivations (`#open`, `#derived`) were checked without
the oracle being asked or told, so no build kept a verdict about one; they
are gate items now (`resolve.rs`, `mint_passes`). A mint's refusal is
routine (a derivation that reached into a scope is not shared), so
`abandon` also forgets the interface hash its question left pending for
`sync`: before, that hash waited for whatever landed next at its index.

**One gate, several Ψs (2026-10-29).** An elaborator and its forks share
one gate, and `write-elf` asks it about the parent's Ψ and each fork's in
turn. The prefix of interface hashes was reset whenever a shorter Ψ asked
and trusted unread for a longer one, so each switch re-hashed the whole
world, and a Ψ that diverged from the last one but was already longer than
the hashed prefix would have inherited its hashes. The cache now keeps a
`GlobalMark` of the Ψ its prefix was built along and keeps exactly the
bindings the asking Ψ has in common with it (`GlobalBindings::common_prefix`:
sealed chunks shared by pointer are common without a look, anything else is
compared by `==`).

The cold overhead deserves one honest caveat: 6.8% is an upper bound taken
while the machine was busiest. A tighter paired loop later the same session
(v2 only, `plain`/`cold` alternating, five iterations, load falling) gave
**44.07 s plain vs 46.14 s cold — +4.7%**, with individual pairs ranging from
+0.3% to a run where the cold one came in *faster* than the plain. That is
consistent with the ~1.25 s the warm run implies (~2.8%) sitting inside the
measurement noise of a 45-second workload. So: cold overhead is now
**single-digit percent and near the noise floor**, against v1's reproducible
+16%. "Approximately free" is the right description; a number with two
significant figures is not available on this machine today.

### 12.5 Node digests (2026-11-06)

The walk of §12.1 was a tree walk, and the elaborator shares terms as a
DAG: a let chain, or a tier-2 type's `W` encoding repeated through a
tactic's monadic code, made a declaration's stream as large as its tree
(`issues/image-tree-walks-let-shared-terms.md`). A fifth piece now joins
the four of §12.1: a **node digest**, the tag `0x1f` followed by the
SHA-256 of `heather/node/1\0` and a term's or type's encoding. A node whose
encoding reaches 512 bytes is written into its parent's as its digest, and
the walk memoizes each digest by the node's address, so a node shared in
memory is walked once per declaration.

Whether a node is a digest is a function of its content (the length of its
own encoding, digests below it included), never of how it was shared, so
equal declarations still hash alike however they were built
(`tests/merkle.rs::a_shared_term_is_walked_once_and_hashes_as_its_tree`).
The framing stays prefix-free: the tag fixes the 32 bytes that follow, and
a digest stands for its preimage up to collision resistance, as a referent
hash already does. The domains bumped (`iface/4`, `check/4`,
`axiom-iface/3`, `statement/3`) because the scheme changed; every stored
verdict and module identity is new once.

Bytes of an open node stay in the staging buffer until the node closes,
because they may yet become its digest; the buffer is flushed only between
top-level pieces. Hashing cost is the shared size of the declaration, at
most 33 bytes more per digest.
