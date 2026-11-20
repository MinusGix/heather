# Composable layout rewrites (Isomer): what it means for Heather

Status: **survey**, 2026-11-20. Source: Gyurgyik, Root, Driscoll, Radanne,
Kjolstad, Pit-Claudel, *Composable Rewrites for Layouts of Algebraic Data
Types*, arXiv:2611.19113v2 (18 Nov 2026). The PDF was attached to the
project thread (arxiv.org is blocked from the cloud); it is not committed
here because its licence is not stated in the copy. Section, figure and
theorem numbers below are the paper's. Read against master at `c2a9d0ce`.

The paper is about one thing Heather is about to need: how an inductive
type with fields becomes bytes, and how to change that choice without
changing the program or re-proving the whole layout. Its bearing is on
rung 3 of the dogfooding ladder ("an enum with fields as a tagged cell in a
span, `match` as a read of the tag, lists and trees",
`/mnt/project-files/dogfooding-review/dogfooding-plan.md` §4), on the
`nh-heap` milestone, and on the layout library's open questions
(`docs/native/layout-design.md` §10). It has nothing for the kernel, the
elaborator or tactics.

---

## 0. The answer in brief

1. **Its central idea fits Heather and is cheaper here than in the
   paper.** A layout starts as the *canonical* one read off the type
   declaration and is changed by small rewrites (pad, commute, box, tag,
   split a field, give a value shape its own arm, cache a computed value).
   Each rewrite is proved once, locally, by a *reconstruction function*
   from the new representation back to the old one (§6.1). In Heather
   terms a reconstruction function is the `abs` of one step, and a layout
   reached by several steps is a stack of reprs whose `abs` is the
   composition. Heather's `abs` is a function, so the paper's "absolute
   injectivity" holds by construction and only the existence of
   constructor images (totality) is left to show (§2 below).
2. **The library theorem this asks for is one Heather already planned
   and has not proved**: refinement composes (CoqEAL's `\o`,
   `docs/native/datarepr-design.md` §7.1, "Adopt (2)"). The paper adds the two
   lifting lemmas that make it useful for layouts: a step under a context
   (inside a field, an arm, a pointee) and a step at a recursive type's
   body, which changes every child at once (Theorem 5, Lemma 6).
3. **Where it lands first: the representation of an enum with fields.**
   Today an enum is its tag word (`EnumInfo`, `lib/native/runtime/rt.hthr`,
   PRs #818 to #821) and a list is an arena cell written by hand
   (`lib/native/native_arena.hthr`). Both are "the canonical layout plus a
   few rewrites" in the paper's sense, and the design for rung 3 should be
   built that way rather than as one codec proved whole per type (§3.1).
4. **Two small things Heather can do now, without new machinery**: a
   cached value in a cell as a repr whose `inv` says the field equals a
   function of `abs` (the arena's line length already is one, §3.4), and
   field reordering as a permutation step with nothing to prove
   (`issues/laid-field-order-chosen.md` already says so, §3.2).
5. **What not to take**: the paper's compiler is unverified (only its
   model is mechanized, in Lean); its relational representation semantics
   is not needed when `abs` is a function; its producer/consumer
   specialization rejects valid programs by budget; high-bit pointer
   stealing rests on an address-space default (§4).

---

## 1. What the paper does

**A layout language** (Figure 1): empty, padding `padn`, zeros `zeron`,
an `n`-bit scalar `un`, a cached expression `⟨e⟩`, a pointer `&n(ℓ)` of
`n` address bits, a reference `ref T` to a type's layout, ordered products,
*ordinary* sums whose arms are chosen by a guard on the value, and
*disjoint* sums whose arm is chosen by a stored scalar with a code per arm.
A guard ("provenance") is a set of values, written as constructor tests at
paths (`l.r ↦ Leaf`) or scalar tests (`k ↦ c`), so an arm can be for
`Node(Leaf, Leaf)` or for keys below 2^32. A type declaration induces a
canonical layout environment: one ordinary sum per type, one arm per
constructor, the fields as a product in declared order (§4.3).

**Rewrites** (Figure 2, premises in Appendix C): `pad`, `zero`, `ptr` then
`box` (move fields behind a pointer), `unbox`, `commute`, `assoc`, `unit`,
`split_k` (cut a scalar into two), `memoize_e` (store `e` of the value),
`tag` (turn an ordinary sum into a disjoint one keyed by a new tag field,
which later rewrites move like any field), `distribute`/`factor`,
`refine_φ` (add an arm for values in `φ`), `prune`, `flatten`, `collapse`,
`unfold` (inline a referenced type's body). A rewrite applies to one focus
inside a context `C[□]`, or replaces a type's body, which changes every
`ref T`, recursive ones included.

**Correctness, locally** (§5, §6). The meaning of a layout is a relation
`W(v)`: the set of structural representations of value `v` (a set, to
allow unconstrained padding and addresses and overlapping arms). A layout
is *faithful* when every value has a representation (totality) and no
representation belongs to two values (absolute injectivity). A rewrite is
correct when it *locally refines*: on the values reaching the focus, two
values that share a new representation shared an old one. Each rule proves
this by a reconstruction function `f : S' ⇀ S` (padding drops the
component, commute swaps the pair, `split_k` joins `b0 + 2^k b1`, the
Scion interval rule `lo, hi ↦ lo, hi - lo` reconstructs `b, b + d`).
Theorem 5 lifts local refinement through a context; Lemma 6 through a
replaced recursive body (induction on the representation under the new
environment); Theorem 7 composes them; Theorem 9 gives program
preservation for terminating first-order programs (results compared at
scalars). A new rule needs only its reconstruction function.

**Bytes are a separate guarantee** (§7, Appendix F). Faithfulness of the
structural representation does not make the bit encoding decodable: with
variable-width arms and a tag after its payload, `(A(1), B(1))` and
`(B(2), A(1))` encode to the same bits (§7.2). A sufficient condition for
a left-to-right decoder is syntactic: every tag stored whole in its scope
and before the payload it selects (`∅ ⊢ ℓ disc→`).

**Isomer** (§8), a first-order, monomorphized pure language over these
layouts. The compiler follows the rewrites from the canonical layout,
updating a decoder (by the reconstruction functions) and a storage plan
(offsets, widths) at each step. Matches and constructions are
*specialized* to the layout, so that an unfolded list (two elements per
cell) does not rebuild its tail at every step (Appendix E, with budgets
that can reject valid programs). Pointer tags fold into field offsets
(`d - t`). The reference count is itself a layout field (`rc_n`) that
other rewrites can narrow or move; omitting it (`rc-0`) is accepted only
where an ownership analysis proves a single owner, and counts saturate
(sticky). A `coerce` directive converts a value between two layouts at a
chosen binding, as the catamorphism built from the target's constructors
and the source's match. A cached expression is stored at construction and
reused by CSE at reads.

**Results** (§9), for the record and not for Heather: 1.42x over Morphic
and 1.53x over MLton with default layouts; the fastest layout per
benchmark is 1.27x over the default and the smallest 23% less peak memory;
the 2-3 tree with `coerce` between building and scanning is 2.29x the best
fixed layout; the interval tree's cached maximum by rewrite matches the
hand-augmented source. Their decision-tree arm-order control "saw little
runtime benefit" (footnote 2).

## 2. How it lines up with what Heather has

| Paper | Heather | Note |
|---|---|---|
| layout of a value, `W(v)` a set of representations | a repr: carrier `R`, `abs : R → S`, `inv` (`docs/native/datarepr-design.md` §1.1) | the paper's arrow points from value to representations, Heather's from representation to value |
| faithful = total + absolutely injective | `abs` total on `inv`, constructor images | injectivity is free: a function cannot send one representation to two values. Totality is the images' existence, which FINDING 1 (§1.3) lets be guarded |
| reconstruction function `f : S' ⇀ S` of a rule | the `abs` of one step, `R' → R`, partial on `inv'` | a layout reached by steps is a repr of a repr; its `abs` is the composite |
| Theorem 7 (sequences of rewrites) | refinement composition, "proved once" (`datarepr-design.md` §7.1, Adopt (2)) | planned, not built |
| Theorem 5 (a rewrite under a context) | `Part`'s `frames` law and `Part::then` (`lib/std/machine/part.hthr`) for products; nothing yet for arms or pointees | arms and pointees arrive with sums in `Shape` |
| Lemma 6 (a replaced recursive body) | the fold anchor (`fold_law`) | a step at `T`'s body is a repr of `T` whose `abs` folds the step's `abs` at every child; one theorem per step kind, or one generic one over `Shape` |
| canonical layout `Δcan` | the naive repr (`repr::naive()`) and `laid record`'s written order | Heather's canonical layout for a sum does not exist yet |
| disjoint sum with codes `c_j` | `EnumInfo` (tag word, `pick`, `of`) | Minus 2026-11-20: a C enum is another repr with a discriminant table, which is exactly a disjoint sum with chosen codes |
| `&n(ℓ)`, pointer compression | an arena cell's name: a 4-byte offset into the arena (`native_arena.hthr`) | already compressed, and bounded by a limit Heather owns |
| `⟨e⟩`, a cached expression | a carrier field with `inv` saying it equals `e(abs r)` | the arena cell's payload length is one (§3.4) |
| `refine_φ` arm, checked at construction | a guarded constructor image (`issues/datarepr-guarded-images.md`) | same shape: construction pays a test, consumption is total |
| storage plan + decoder per step | `Shape::layout` and `Shape::stored` (`layout-design.md` §10.3, prototype in `layout-prototype/`) | `Shape` has products, arrays and words; no sums, no pointers |
| `coerce` at a binding | multi-repr conversion, "never compiler-inserted" (`datarepr-design.md` §5.3) | the paper keeps it an explicit directive too |
| `rc_n` field, `rc-0` by ownership | rung 3's "who frees: an arena dropped whole, or counts"; `nh-ownership` | nothing built for counts |
| storage recovery (§7) | `Stored`'s `round : read(write(a)) = a` | a hand codec cannot skip it; a codec derived from a `Shape` with sums needs the paper's syntactic check to be sure `round` will prove |

The reading that matters: **the paper and `datarepr` agree on the shape of
the obligation, and differ on what is trusted.** Isomer's model is
mechanized in Lean, but its compiler is not (§1, "It does not establish
end-to-end correctness of the Isomer compiler"; Appendix G, "implementing
them as generated code requires a separate proof"). Heather's generated
code carries its certificate. So what Heather takes is the decomposition
(canonical layout, small steps, a local proof per step, lifting lemmas),
not the proofs.

## 3. Ideas that fit, with where they land and what they cost

### 3.1 Rung 3's cells as a canonical layout plus proved steps (the main one)

**What.** When an enum with fields gets a runtime layout (rung 3,
`nh-heap`), build it as: the canonical layout read off the declaration (a
tag, then each constructor's fields in order, children by name into the
arena), plus a list of steps chosen per type, each step a value with its
reconstruction (`abs`) and its local law. The codec and the repr of the
final layout are the canonical ones composed with the steps'
reconstructions; no codec is proved whole per type.

**Why it fits Heather in particular.**
- It is the "layout is DATA" reading of `datarepr-design.md` §5.2 with
  the proof decomposed: a layout choice never touches the proof language
  because each step brings its own law.
- It is how Minus asked for field order to work (`laid` decides,
  "magical"), generalised from products to sums.
- It gives the C-compatible enum Minus named on 2026-11-20 as one step
  (`tag` with an explicit code table) on the same canonical layout as the
  default, rather than a second hand-written repr.
- The generator stays untrusted: a step it chooses is checked by its law.

**Where.** `Shape` (`issues/layout-first-order-description.md`, prototype
in `layout-prototype/shape.hthr`) gains a sum (tag and arms) and a name
into an arena; the canonical shape of a declaration; a `Step` type with
`apply : Shape → Option<Shape>` and a reconstruction with its law, proved
once per step kind; the lifting lemmas (a step under a path, a step at a
recursive body); and the composition lemma `datarepr-design.md` §7.1
already asks for. The arena's list cell
(`native_arena.hthr`) and `native-arena-cell-codecs`'s binary tree cell
are then the first two derived layouts and should come out equal to the
hand ones.

**Cost.** Large as a whole, but it is the cost of rung 3's representation
anyway; the paper's contribution is the order of work. A first slice that
proves the idea: a `Shape` sum with a tag word, the canonical shape of a
two-constructor type, three steps (commute, pad, tag with a code table),
and the arena list cell derived from the canonical shape of
`List<List<BitVec(8)>>`, equal by `refl` to the hand one. Lemma 6 is the
hard part; in Heather it is an induction over the arena's fuel (the name),
the same induction `ArenaRef::abs` already does.

### 3.2 Field order as a permutation step

`issues/laid-field-order-chosen.md` notes that reordering has "nothing to
prove" because a part's laws do not mention where it lies. The paper's
`commute` and `assoc` are the same claim made general: a permutation's
reconstruction is the inverse permutation. Nothing to do now beyond a log
line; when §3.1 exists, the reorder rule is a sequence of `commute` steps
and the issue closes into it.

### 3.3 Arms for value shapes and small values (`refine_φ`)

An arm for `Node(Leaf, Leaf)` (a node with no children stores only its
key), or for a key below 2^32 (stored in the name's place, no cell at all),
or for a short byte string inline. Each pays a test at construction and
nothing at a read. That is precisely a guarded constructor image, so it is
a second customer for `issues/datarepr-guarded-images.md` besides the
arena's capacity, and a reason to design the guard there as a decidable
test the construction runs, not only as a hypothesis. It also needs `match`
specialised to the layout when an arm unfolds a child (§4), so it is later
than §3.1.

### 3.4 Cached values in the cell (`memoize`), which Heather can do now

A repr whose carrier holds an extra field and whose `inv` says the field
equals `e(abs r)`; the `Impl` of `e` reads the field, certified by `inv`;
the constructor images compute it. Nothing new is needed: v1 `datarepr`
takes total images, and the cached field's law is an image law.

The arena already does this without saying so: a line cell stores its
payload's length `L` (`native-heap-arena-design.md` §4), which is a
cached `len` of the payload. Stating it gives `List::len` of a line a
certified constant-time `Impl`, which `sort` and `tac` would use. A
larger showcase is the paper's interval tree (§9.2.2): the subtree maximum
cached in each node turns a linear query logarithmic, and in Heather the
augmentation is a repr of the plain tree with no change to the program or
its proofs. That is a good example for the showcase push: the program is
proved over the plain tree, and the data structure the paper calls
"augmented" is a certified representation of it.

### 3.5 Tag bits inside a name

The paper's red-black tree moves a child's tag and colour into low bits of
its pointer, so a match on a child needs no load (§2). In Heather a child
is an arena name, an offset into an arena whose cells Heather places. If
cells are aligned to 8 bytes, a name's low 3 bits are free by a fact the
arena proves, not by an assumption about the operating system or the
allocator. A list's `Nil`/`Cons` (and an enum's tag up to 8 constructors)
fits there. This is a `split_k` plus `commute` on the canonical layout, so
it comes free with §3.1; the matching optimizer rule (fold the untagging
into the field's offset, `d - t`) is a rule about address words for the
rules-as-theorems optimizer when tagged names exist.

### 3.6 Conversion between layouts (`coerce`)

The paper's evidence (2.29x on the 2-3 tree, one conversion between
building and scanning) is the first measured case for
`datarepr-design.md` §5.3's multi-repr trigger. The conversion is the
identity on the spec type transferred from one repr to the other, which
reprgen's derived route already produces (a fold over the source repr
using the target's images, certified from `fold_law` and the image laws).
Nothing to build until a program wants two layouts; the paper confirms the
§5.3 guardrail (an explicit directive at a binding, not compiler
insertion) is workable in practice.

### 3.7 The count as a field of the layout

If rung 3 chooses reference counts for some programs, the paper's version
is the one that fits Heather's style: the count is a field of the layout
(so it can be narrowed, moved, or removed by the same steps), removal is
accepted only where uniqueness is proved (Heather's
`effects-uniqueness-surface`), counts are sticky at saturation, and arms
padded to one cell size let a dying cell be reused by another constructor.
The last is how Koka's FIP programs get reuse by editing the source (Pad
fields); here it is a `pad` step. Note for `nh-ownership`, nothing now.

### 3.8 A decodability check for derived codecs

§7.2's example is worth keeping as a negative control: once `Shape` has
sums with arms of different widths, a derived layout can be faithful and
still undecodable. Appendix F's condition (each tag stored whole, before
the payload it selects, in its scope) is a closed check over a `Shape`, a
`Bool` decided by evaluation like `Layout::fits_bit`, which a generator can
ask before it tries to prove `round`. It lands with §3.1, as the refusal a
step that moves a tag after its payload gets.

## 4. What does not apply

- **The proofs themselves.** They are about a big-step model with
  abstract construction and destruction policies (Appendix G), with
  results compared only at scalars. Heather proves each compiled program
  against its source, so the model's Theorem 9 has no place; what is reused
  is the decomposition into local laws.
- **The relational semantics.** Sets of representations exist in the
  paper to allow padding, addresses and overlapping arms, and to state
  injectivity. With `abs` a function from bytes, padding is bytes `abs`
  does not read, an address is a name `abs` follows, and an overlap is two
  arms whose `abs` agree; none needs a relation.
- **Producer and consumer specialisation as compiler work** (Appendix E).
  To avoid quadratic rebuilds under an unfolded layout, Isomer inlines and
  re-splits matches and constructions up to a budget, and rejects valid
  programs when the budget runs out. In Heather, a function specialised to
  a layout is a custom `Impl` certified against the derived one
  (via-derived), so the specialisation can be as clever as it likes and
  still be checked; and the fusion half is `issues/iterators-as-list-repr.md`.
  Unfolded layouts (two elements per cell) wait for that, not for a
  budgeted rewriter.
- **High-bit pointer stealing** (Layout 3, 44-bit pointers because Linux
  places user allocations below 2^47 by default). Heather's operating-system
  model relies only on what Linux guarantees in writing, and in any case a
  Heather child is an arena name, not an address, so the question does not
  arise: the name's width is bounded by the arena's limit.
- **Layout search by language-model proposals and measurement** (§9.4).
  It needs a measured search loop, which is perf work in the sense of
  `perf/CLAUDE.md`; with §3.1, every candidate layout is correct by
  construction, so such a search could be added later without trust cost,
  but there is no customer.
- **Programmer control of match decision-tree order.** The authors found
  little benefit; Heather should not build it.
- **Monomorphisation and defunctionalisation** are assumed by the paper
  and by Heather's rung 4 alike; nothing to adopt.

## 5. Follow-up

Nothing here is urgent, and nothing is filed as a new issue: the ideas
attach to issues that exist.

- `issues/layout-first-order-description.md`: §3.1 is the case for `Shape`
  with sums and names, built as canonical shape plus steps.
- `issues/datarepr-guarded-images.md`: §3.3, a second customer (arms for
  value shapes), and a reason for the guard to be a decidable test.
- `issues/native-arena-cell-codecs.md`: §3.1's first slice derives the
  list cell and the tree cell from canonical shapes; §3.4, the cached
  length as a stated law.
- `issues/laid-field-order-chosen.md`: §3.2.
- `issues/datarepr-separation.md`: §3.6 (measured evidence for the
  multi-repr trigger) and §3.7 (counts as a layout field).

The one decision for Minus: whether rung 3's representation of an enum
with fields is designed as §3.1 (canonical layout plus proved steps) or as
one codec per type proved whole. The recommendation is §3.1, because it is
what makes "the layout is chosen by the `laid` setup" and "a C enum is
another repr with a discriminant table" the same mechanism, and because it
keeps every layout choice out of the proof of the program.
