# Declaration-slice replay: the edit path skips unchanged declarations

Status: both rounds landed 2026-09-17 — `ModuleDelta` slices and
`Elaborator::check_module_delta_from` with the differential suite
`crates/elab/tests/slice_replay.rs`; the slice table in the image format
(`HTHMOD` 7), the store's newest-image pointer and `load_previous`, and the
session's source-miss path with the `(cache)` line's "declarations replayed
after an edit" count. Owner:
`issues/declaration-slice-replay.md` (split from
`issues/warm-path-rewalks-unchanged-declarations.md`'s second candidate).

Two things the implementation settled that §3–4 below did not say:

- **Spans.** A registration event carries the declaration's surface syntax
  with byte spans, and a slice's text may sit elsewhere after an edit
  above it. A replayed slice's events are *relocated*: encoded and decoded
  through the image codec with an offset added at `get_span`, the one place
  every span in every payload passes; its warnings shift the same way.
- **"The same contribution"** is the interface projection of the slice's
  events (spans zeroed, theorem proofs and proof dependency edges dropped),
  compared as encoded bytes, plus the Ψ bindings compared structurally. That
  is what a dependent observes, so it is what decides whether the prefix
  after a re-elaborated item is still exact.

## 1. The number this is about

After the merkle-walk round and the replay-verdict round, the cold check of
a file is the kernel gate (61% of the corpus) and the warm check of an
unchanged file is its image decode. The check a person sits through most is
neither: it is the check after an *edit*, and that one is the elaborator.
`scripts/perf`'s `edit` mode appends one trivial declaration to the file and
checks it again at width one (snapshot `2026-09-17T211854Z-local`):

| file | edit wall | body elab | type | emit | whnf | publish | walk | decode | other |
|---|---|---|---|---|---|---|---|---|---|
| showcase (144 decls) | 8.27 s | 2.32 | 0.07 | 1.10 | 0.18 | 1.12 | 0.59 | 0.51 | 1.36 |
| omega (623) | 2.86 s | 0.84 | 0.50 | 0.36 | — | — | 0.15 | 0.03 | 0.20 + omega_check 0.61 |
| x86 model (987) | 2.52 s | 0.75 | 0.21 | 0.30 | 0.54 | 0.11 | 0.11 | 0.05 | 0.16 |

The kernel gate is 0.01 s in every row: the declaration-verdict store admits
every unchanged declaration. What the run pays for is *re-elaborating* every
unchanged declaration to reach the term it then does not check — 4 s of the
showcase's 8.3 — plus re-encoding and re-hashing the whole module image
(publish 1.1 s) and re-walking every declaration for its verdict key (0.6 s).
The one declaration that actually changed costs milliseconds.

## 2. The identity is the one images already use

`docs/semantic-module-images-design.md` §4 fixes two identities for a module
and keeps them apart on purpose:

> The source digest selects a reusable elaboration result. The resulting
> interface hash controls downstream invalidation.

This design applies exactly that pair one level down. A declaration's
*source text* selects a reusable elaboration result for that declaration;
the *semantic prefix* it was elaborated over — the dependency world plus
the effects of every earlier declaration of the same module — is the
identity that decides whether the result is still the right one. Text never
carries trust and never stands in for the elaborated identity: a replayed
declaration's kernel bindings go through the same gate a replayed module's
do (`recheck_extension`: the verdict store vouches or the kernel runs), and
its registry events go through the same `preflight_module_event` checks.
That is why this is not the "two notions" the cache design refused
(`issues/warm-path-rewalks-unchanged-declarations.md`): the text-level key
only chooses *which stored elaboration to try*, and the stored elaboration
is accepted on the semantic identity alone, as a module image is.

## 3. Slices

A `ModuleDelta` today is one flat suffix: the Ψ bindings the module pushed
(`extension`), the journal of registry events (`events`), the scope, and the
module's warnings ride beside it in the image. The elaborator already
produces both in item order — `elab_module_pass` runs `elab_item_at` per
item and every `record_module_event` lands in the journal as it happens —
so item boundaries exist at elaboration time and are simply not recorded.

A **slice** is one item's contribution, recorded as ranges into the flat
data the delta already has:

```
ItemSlice {
    source: String,        // the item's exact source span (in process; the
                           // persistent half stores its SHA-256 instead)
    start: usize,          // its byte offset, the base its spans are relative to
    psi:      a..b,        // bindings this item pushed (extension indices)
    events:   e..f,        // journal events it recorded
    warnings: w..x,        // warnings it raised (re-raised on replay)
}
```

The granularity is the elaborator's own unit of atomicity: an
`Item::Decl` that belongs to a measure group (`ItemPlan::in_group`) is
elaborated with its group in one `session_transaction`, so a mutual group
is one slice keyed by the concatenation of its members' spans. Imports are
items with empty ranges. Derived instances are minted *between* items
(`mint_pending`) and journal as `Derived` events; they belong to the slice of
the item that preceded them, which is where the loop already places them.

The delta gains `items: Vec<ItemSlice>`. The flat vectors stay as they are;
the image format gains one table of five integers per item and bumps its
format version. Nothing about the encoded terms changes.

## 4. Replay after an edit

Today a changed source is a `ModuleCacheKey` miss and the module is
elaborated from scratch. With slices, the session on a source miss also
looks for the *previous* image of the same module over the same
dependencies (the key is source-keyed, so this needs a second index in the
image store: newest image per `(module, dependency identity)`; see §7). If
one exists, the pass is:

```
parse the new source; plan groups
for each new item (or group) in order:
    if the next unconsumed old slice has the same source digest
       and the prefix is still exact:
        replay the slice          (extend Ψ through recheck_extension;
                                   preflight + apply its events, spans
                                   relocated; re-raise its warnings, which
                                   already hold its source lints' findings)
    else:
        elaborate the item from source, journaling as today
        if the slice it produced is structurally equal to the old slice
           at this position (same bindings, same events):
            the prefix is still exact          (a proof-body edit, a comment)
        else:
            the prefix is broken from here      (every later old slice is dead)
```

"The prefix is still exact" is a running fact, not a hash: it holds while
every item so far either replayed its old slice or re-elaborated to a slice
structurally equal to the old one. Once it breaks, the rest of the module
elaborates from source, exactly as today. Insertions and deletions fall out
of "the next unconsumed old slice": an inserted item elaborates from source
and breaks the prefix (its bindings sit where the old slice's did); a
deleted item leaves an old slice unconsumed whose digest no longer matches,
also breaking it. Reordering breaks it at the first moved item. All of
these are the correct answer, not a limitation: a later declaration may
have unfolded the moved binding, and its Ψ indices are positional.

The structural-equality test on a re-elaborated slice is what makes the
common edit cheap. Editing a theorem's proof re-elaborates that theorem;
its Ψ binding is opaque and identical, its events identical, so every
declaration after it replays. Editing a `fn`'s body changes its binding and
every later declaration re-elaborates — which is necessary, since any of
them may unfold it, and is what the module-level interface split already
does for downstream modules.

What a replayed slice must reproduce, and where it comes from:

| state an item touches | on replay |
|---|---|
| Ψ bindings | slice's extension range, through `recheck_extension` (gate or kernel) |
| names, registries, gendefs, instances, designations, reprs, meta | slice's events, through `preflight_module_event` + `apply_module_event` |
| derived instances minted after it | `Derived` events in the same slice |
| warnings | stored per slice, re-raised at the relocated spans |
| source lints | their findings are among the stored warnings; not re-run |
| omega reports, timing rows | not reproduced; the CLI drains reports and the row for a replayed item is a replay row |
| `container_decls`, goal/mint arenas, `pending_derived` | transient per item; empty at every boundary today |

The last row is the one to verify with a test rather than assert: the loop
already relies on those being empty between items (a failed item clears
them), so a replayed item leaving them empty is the existing contract.

## 5. Trust

Unchanged. A slice is acceleration data with the same standing as a module
image: its bindings face the gate — the verdict store vouches for a
definition it has seen (rung 1, as on every other path since 2026-09-17) and
the kernel checks anything else — and its events face the preflight checks
a replayed module's do. The source digest picks a candidate and nothing
more. A forged or stale slice fails the same way a forged image does: at the
kernel or at preflight, before anything is published. `ImageFreshness`
applies to the previous image as to any other; under `Exact` a previous
image from another build is not consulted.

## 6. What it should buy, and what it does not

Measured in process on 2026-09-17 (release, width one, the desktop, the
verdict store installed as the CLI installs it): re-checking the showcase's
own module with one declaration appended went from 4.7 s fresh to 0.72 s
sliced, all 96 items replayed and one elaborated. Through the CLI the same
edit went from 8.3 s to 5.5 s, and the profile of what remains corrected
the projection below: the module's *previous* image has to be decoded (and
dropped) to replay from, which for the showcase's 29 M-node image is about
2 s of allocation and freeing — the imports' decode of 0.5 s was the only
decode the projection counted — then publish 1.0 s, the verdict walk
0.5 s, the encode-and-decode relocation of the replayed events. The
replayed declarations themselves are nearly free. So the next levers on
this path are the ones the design already named plus one: publish
incrementally, walk incrementally, and decode the previous image lazily or
drop it off the critical path. The rest of this section is the projection
made before the datum.

Showcase edit, from the table in §1: the 4 s of re-elaboration goes to the
edited declaration's own cost; decode (0.5 s), the verdict walk (0.6 s) and
publish (1.1 s) stay, and "other" (1.4 s: parse, module setup, name
registration) mostly stays. So roughly 8.3 s → 3.5 s in the first round.
The publish is the next slice of the same design: unchanged slices' encoded
bytes are position-stable while the prefix is exact, so a later round can
carry them into the new image verbatim and re-encode only from the break,
taking publish to a fraction. The verdict walk is
`issues/warm-path-rewalks-unchanged-declarations.md`'s first candidate and is
not touched here.

Omega is different: its edit cost is `omega_check` 0.61 s and type/body
elaboration of the appended declaration's *neighbours*, and 0.5 s of
`decl_type` across 623 small items. Slices help omega too but the fraction
is smaller, and the x86 model's 0.54 s of whnf is elaboration of the model
itself. Cold checks gain nothing from this design.

What it does **not** address is the other edit shape, measured on
`issues/relocatable-semantic-module-images.md` (2026-09-04): editing an
*upstream* module (nat, algebra, int — where edits actually land) invalidates
every downstream image because their Ψ positions are exact-prefix. Slices
keyed on the exact prefix have the same property. The refinement that would
cover it — key a slice on the interface hashes of the globals it actually
referenced (`direct_dependencies` is already journaled per `Global` event)
and relocate its Ψ references by range — is the relocation project, and this
design keeps the door open by keeping slices positional and self-describing
rather than by attempting it.

## 7. Cost against the code

- `crates/elab/src/module_delta.rs`: `ItemSlice`, `ModuleDelta.items`; the
  journal records a boundary per item (Ψ length, event count, warning count
  at item start and end) from the loop in `elab_module_pass`, at the same
  two points the loop already marks warnings and omega reports.
  `replay_module_delta` grows a sibling, `replay_module_slices(old, src)`,
  that runs the pass of §4 and returns a fresh `ModuleDelta` (the new
  image is published from it as today). ~250 lines.
- `crates/elab/src/lib.rs`: the item loop factors its per-item body so the
  sliced pass can call "elaborate this item and journal it" for one item;
  the structural comparison of a fresh slice against an old one. ~100 lines.
- `crates/elab/src/module_image.rs`, `crates/cache/src/module_image.rs`:
  the slice table in the format, version bump; the store's second index,
  newest image per `(module, dependencies)`, kept as one small file beside
  `modules-v1`; `load_previous(module, dependencies, freshness)`. ~200 lines.
- `crates/cli/src/semantic.rs`: on a source miss, try the previous image's
  slices before `check_module_delta`. ~40 lines.
- `scripts/perf`: nothing; `edit` mode measures this directly.

Tests, in the order they gate the work:

1. `module_delta.rs`: slices partition the delta (ranges are contiguous,
   cover everything, one per item or group).
2. Differential, in-process: for each edit shape — append, proof-body edit,
   `fn`-body edit, insert in the middle, delete, reorder, rename, an edit
   inside a mutual group, an edit that changes a minted derived instance —
   the sliced replay yields a delta equal to fresh elaboration's (Ψ, events,
   scope, warnings), and reports which items replayed. The negative controls
   are the ones where nothing may replay after the edit.
3. `cache/tests/module_images.rs`: the slice table round-trips; a previous
   image from another build is ignored under `Exact` and used under
   `AcceptStale`; a forged slice binding is refused through the kernel.
4. `cli/tests/check.rs`: the `(cache)` line reports replayed declarations;
   the perf `edit` mode before/after.

Two rounds: the in-process half (items 1–2, the delta and the pass) and the
persistent half (3–4, the format, the index, the CLI). The first is
testable and measurable on its own through `elab_module_delta` followed by
`replay_module_slices` on edited source.

## 8. Open questions for the owner

1. **Granularity of the prefix test.** §4 breaks the prefix at the first
   item whose re-elaborated slice differs. A finer rule — break only for
   later items whose `direct_dependencies` include the changed global —
   is the relocation refinement in disguise and needs Ψ index relocation
   to be sound; this design says no to it in the first two rounds.
2. **How many previous images to keep.** One per `(module, dependencies)`
   is enough for the inner loop; the store's lifecycle issue owns eviction.
3. **The output line.** `N declarations kernel-checked, M accepted from
   cache, K semantic modules replayed` gains `and J declarations replayed`
   or folds them into M; the count should say what was not re-elaborated.
