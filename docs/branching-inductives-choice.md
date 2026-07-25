# Branching finitary inductives: the choice

Status: **decision support, no decision taken** (2026-07-24). Written to be
thought over, not to be implemented from. Tracking issue:
`issues/tier1-branching-constructors.md`. Evidence base:
`docs/inductive-tier1-lowering.md` §8.1 and the validated linear-fragment
prototype `crates/elab/tests/tier1_fording.rs`.

The question: a constructor with **two or more recursive fields**
(`Node(Tree, Tree)`) has no lowering into the current kernel with the
definitional behaviour we get for the linear fragment. Where do we pay?

---

## 1. Why this decision exists at all

`issues/kernel-v1-extensions.md` promoted W-types with an explicit
reassurance:

> Note the classic "W-encodings of *first-order* inductives need funext"
> complaint is irrelevant here: first-order data stays on the finitary
> encodings; W is for the infinitely-branching tier only.

**That premise is false, and this week's work is what showed it.** The
finitary encodings reach the *linear* fragment — at most one recursive field
per constructor — and provably not past it. So the classic complaint is not
irrelevant; it is exactly the thing standing in front of `Tree`, and
therefore in front of any first-order data with a branching constructor.

The reason, stated as sharply as I can:

> `elim_Nat` recurses on a *predecessor*, so a family defined by it can refer
> to itself at one smaller index. A constructor with one recursive field needs
> exactly that: the parent's payload type is *literally a container of* the
> child's, so assembly is free and the constructor is in constructor form
> whatever the child is. A constructor with two recursive fields needs the
> family at two indices, neither of which is the predecessor. Every way to
> get there routes the child through a **function of a measure**, and a
> function of a *neutral* measure is stuck — so the constructor is a stuck
> case-split rather than a constructor form, and `match` on it stops
> reducing.

Fording buys a linear fixed point because `Nat` *is* the linear inductive
type. Branching data needs a branching fixed point, and the kernel has
exactly one: `W`. The literature agrees in the sharpest available form —
containers (Abbott–Altenkirch–Ghani) show `W` + funext interprets every
strictly positive finitary inductive, **with** funext, and that "with" is
load-bearing, because `W`'s children are *functions* rather than tuples.

§9 records the encodings that were tried and why each hits the same wall, so
that this is not relitigated.

---

## 2. The four places to pay

Every route below is a choice of *where* the cost lands, not whether there is
one:

| | Where the cost lands |
|---|---|
| **A** | An **axiom** — funext, extending its blast radius from infinitary types to all branching first-order data |
| **B** | The **conversion checker** — η rules for finite function types, so `W`'s children behave like tuples |
| **C** | The **former set** — a new positive former whose children *are* tuples |
| **D** | The **elaborator** — canonicalize the stuck embeddings in the cases where they can be computed |
| **E** | The **surface language** — no branching inductives yet; defer the decision |

---

## 3. What the datarepr separation removes from the ledger

Decided in discussion, 2026-07-24: **the representation the kernel checks is
not the representation that runs.** Inductive types are specification objects;
runtime data structures are chosen separately (unary Peano `Nat` for
reasoning, GMP-style `Nat` at runtime, linked by a certified refinement —
the same discipline as Isabelle's `code_datatype` + refinement lemmas or
CakeML's translator, and the sound version of what Coq's
`Extract Inductive nat => int` does by fiat).

Consequences for *this* decision, and they are large:

- **Every efficiency objection is void.** Unary heights, the `elim_Nat`
  family inlined at each type occurrence, the Σ-of-Units nominal tag, O(n)
  numerals — none of that is what runs. Term size and reduction cost of the
  encoding are not currency here.
- **The IR's shape is not an escape hatch.** "Make the IR flat (ANF/SSA) so
  its expression type is linear" was on the table and is now off it: a flat
  IR is a fine *IR* decision but it does not settle this, because the IR
  datatype is a spec object chosen for provability, and branching data is
  needed regardless (surface syntax, types, evidence structures). The IR was
  an instance of the problem, not the problem.
- **The only remaining currency is definitional behaviour and the cost of the
  mechanism.** That is the axis the table in §8 scores.

The axes that matter, then:

1. `match`/eliminator **β on open subterms** (proofs about open terms).
2. **Unique canonical forms** up to conversion.
3. **Axiom-freeness** (canonicity for closed terms).
4. **One regime** vs. a visible seam between linear and branching data.
5. **Trusted-base size** — kernel rules, and the ch. 07 metatheory bill.
6. **Meta-layer cost** — every former needs code-recursor telescopes
   (`crates/kernel/src/rec.rs`), which is the expensive part in DeLaM and the
   thing Heather is *about*.
7. **Elaborator complexity** (transport insertion, motive plumbing).

---

## 4. Route A — `W` + funext, i.e. branching goes to tier 2

Encode `D` as a container: shapes `S` = the sum over constructors of their
non-recursive fields, positions `P s` = the arity as a finite type, values
`sup(s, f)` with `f : P s → W`.

**What works, and better than first feared:**

- Constructor `cong` needs **no** funext. From `p : l = l'`, ordinary `cong`
  on a subterm of `λpos. case pos of 0 => l | 1 => r` gives the children
  functions equal, hence `Node l r = Node l' r'`.
- `match` on a constructor **does** β-reduce, even with open children:
  `elim_W` fires on `sup` (`crates/kernel/DESIGN.md`, W section).
- Canonical forms of *generated* data are unique: the generator always emits
  the same shape of children function.
- **Non-dependent** motives need no transport at all, so ordinary functions
  (`simulate`, evaluators, pretty-printers) compute definitionally on closed
  data.
- The ch. 07 funext-leak audit already establishes that funext cannot
  contaminate `□`-level equality (`docs/metatheory-ch07-extensions.md`,
  "Funext leak audit"): code conversion is syntactic and no rule derives
  `□`-equality from term-level `Id`. So the axiom is *contained* with respect
  to the meta layer. This is a real point in A's favour and corrects a
  worry I raised in discussion.

**What it costs:**

- The **dependent** eliminator's arms are typed at `sup(a, f)` for an
  abstract `f`, while the user's arm proves `M (Node e₁ e₂)`. Bridging needs
  `f = λpos. case pos of …`, i.e. one funext application per branching
  constructor. It is mechanical, so the *generated* recursor can absorb it
  and the user-facing arm interface stays clean.
- But absorbing it means the generated dependent recursor's **β is
  propositional only**: a transport sits in the middle and does not reduce.
  Dependent recursion therefore does not compute — acceptable for proofs,
  and a leak wherever *data* is produced by dependent recursion.
- funext arrives as an axiom anyway for tier 2 (`Acc`), so A does not
  introduce it; **A extends its blast radius** from "infinitary things that
  never computed anyway" to "all branching first-order data, including the
  IR". That is the honest framing of A's cost, and it is precisely what the
  §1 quote promised would not happen.
- Boxed code may contain stuck axiom applications. Not a soundness problem
  (per the audit) but a metaprogramming ergonomics one, and it interacts with
  `issues/setoid-auto-lifting.md`'s boxed-code introspection.
- **A seam.** The linear fragment stays on fording, where everything is
  definitional. So induction on `List` behaves better than induction on
  `Tree`, visibly, forever. Putting `List` on `W` too removes the seam by
  making the good case worse.

**Cost to build:** lowest of all routes. `W` is in the kernel, the ch. 07
pass covers it, the generator work is the tier-2 path that was planned
anyway. Realistically days, not weeks.

---

## 5. Route B — extend conversion so `W`'s children behave like tuples

`W`'s only defect is that its children are functions and the kernel has no η
for functions out of finite types. Two rules would fix it *in place*:

- **`Empty`-η**: any two terms of `Π(x : Empty). A` are convertible. Cheap,
  clearly sound (the same shape of argument as `Unit`'s proof irrelevance,
  already in `conv.rs:696`), and it fixes nullary constructors — the leaf
  case — outright.
- **Coproduct η / case commutation**: for `pos : A + B` neutral,
  `f pos ≡ case pos of inl x => f (inl x) | inr y => f (inr y)`. This is what
  the *n*-ary arms need.

**Benefits:** no new former, no axiom, no seam; `W` becomes the single
branching fixed point and everything is definitional. The most parsimonious
outcome if it works.

**Drawbacks:** η for coproducts is a research-grade conversion problem.
Decidability is known but the algorithms are awkward (type-directed partial
evaluation / extensional normalisation territory), no mainstream checker
implements it, and it makes conversion non-local in a way that would touch
every arm of `conv.rs` — the one component whose simplicity we most rely on,
and whose ch. 06 "verbatim" status (`DESIGN.md`) is a stated invariant. Also
the ch. 07 logical relations would need the η-closure at sums, which is a
genuinely new obligation rather than a variation on an existing one.

`Empty`-η alone is cheap and worth having regardless; it is *not* sufficient.

---

## 6. Route C — a kernel former whose children are tuples

Replace `W`'s position *type* with an arity *Nat*, and its children function
with a Σ-tuple:

```
Wf^l(x : S). n          S : Type @ l,   n : Nat with x : S free      lives at l
sup_f(a; cs)            a : S,  cs : the n[a/x]-fold Σ-tuple of Wf, Unit-terminated
elim_Wf(z. M; a cs ih. s; t) : M[t/z]
```

**Why the defects vanish rather than being patched:**

- Children compare **componentwise by Σ-η**, which is already in the kernel.
- Arity 0 is `Unit`, hence **proof-irrelevant** — leaf uniqueness is
  definitional, the same way the tier-1 base case already works.
- The arm obligation is `M (sup_f(a; cs))` with `cs` a *tuple*, and Σ-η makes
  it convertible with the canonical constructor form. No transport, no
  funext, β on open subterms.
- **One regime.** It subsumes tier 0, tier 1 and branching: the height
  classes, the two no-confusion regimes, and the tier-1 generator that does
  not exist yet all collapse into one mechanism. Given that this tier's
  hazard class is "checked proof about the wrong type", shrinking the
  mechanism may be worth more than shrinking the kernel.
- This week's fording work becomes the substrate rather than being retired:
  the tuple type is stated with the `vec` formula, which is why the
  telescope can stay fixed-arity.

**Wrinkles that need settling before this is a design** (each is real, none
looks fatal):

1. **Stating the children's type in the rule.** `Tup(k)` is
   `El (elim_Nat(_. Ty l; ⌜Unit⌝; (_, r. ⌜Σ(_ : Wf…). El r⌝); k))`, which
   needs the *code* `⌜Wf…⌝` and hence a code-expressible shape `S`. Either
   accept that side condition (all generated shapes are `Σ`/`+`/`Unit`/`Nat`,
   so it binds nothing in practice) or add a small **`Vec` former** —
   `Type::Vec {level, elem, len}` with `Vec(T,0) ⇝ Unit`,
   `Vec(T, S k) ⇝ Σ(_ : T). Vec(T,k)` — which states the rule cleanly and is
   independently useful.
2. **The ih's type.** The step needs "a tuple of `M(cᵢ)`", a *dependent*
   vector over `cs`, which `Vec` cannot state. Three ways out: state the ih
   as a function `Π(i : Fin (n a)). M(nth i cs)` — note this is harmless,
   since the η-deficiency of functions only hurts where the function is
   *stored in the data*, and the ih is transient; or add a dependent-vector
   former; or use the **mutual tree/forest presentation** (a second motive
   over vectors, with nil/cons cases), which is how rose trees are usually
   given and needs only `Vec`.
3. **Neutral arity.** If `n a` is neutral the children's type is stuck and
   `elim_Wf` must be neutral too. That is the right behaviour (an unknown
   shape has an unknown arity), and generated code cases on the tag first, so
   it never bites — but it wants to be stated deliberately.
4. **Two branching formers.** `W` stays for the infinitary tier (`Acc`'s
   positions are a type, not a `Nat`), so the kernel would carry both. Is one
   more former acceptable for the whole first-order story, when the existing
   one only serves the tier that never computes anyway? That is the crux of
   C, and it is an aesthetic-plus-trust judgment, not a technical one.

**Cost to build, grounded in the `W` landing** (`DESIGN.md`, `rec.rs` log):
`W` added 4 code-recursor branches (`ty_w`/`tm_w`/`tm_sup`/`tm_elim_w`, 37
total), with `tm_elim_w`'s telescope the deepest yet (3 univs, 6 globals, 5
recursive calls), and required five parallel transcriptions to stay in sync
(`rec.rs`, subst depths, reduce β, `BRANCH_DIMS`, `identity_branches` ×2,
`gen_branches`), plus a ch. 07 logical-relations obligation. `Wf` is a
comparable landing — plus `Vec` if wrinkle 1 goes that way — and its LR
obligation is *easier* than `W`'s (finitary, tuple-shaped, no quantification
over subtree functions). Call it the same order of work as the `W` round:
weeks, not days, and it touches the trusted base.

### C3, and why not to copy the mainstream

A full native inductive schema (Coq/Lean/Agda-style: arbitrary constructor
count, arbitrary field telescopes, a schematic recursor) is the obvious
alternative and the wrong one *here*: variable-arity, variable-constructor
schemas are exactly what DeLaM's fixed-telescope code recursors are bad at,
and the extra generality mostly buys representation flexibility that datarepr
now provides from outside. If a former lands, it should be the smallest one
with correct definitional behaviour.

---

## 7. Route D — canonicalize the embedding in the elaborator

Keep the `D_below` course-of-values scheme from
`docs/inductive-tier1-lowering.md` §8.1 and have the elaborator emit the
concrete injection when the children's heights are literals, postponing
otherwise.

**Benefits:** no kernel change, no axiom, and computation is restored in the
closed case, which is most *evaluation*.

**Drawbacks:** proofs about open terms — the majority of what the stress
suite and the compiler certificates do — get no help at all; the encoding is
the most complex of any route (course-of-values tables *plus* an embedding
function *plus* elaborator special-casing); the behaviour is
condition-dependent in a way that is hard to explain to a user ("it computes
when the sizes are known"); and it is the one route with no clean story to
tell about *why* it is right. It is a mitigation, not a design.

---

## 8. Route E — defer: no branching inductives at the surface yet

Ship the tier-1 linear generator, reject branching declarations with a
pointer to the issue, and revisit.

**Benefits:** costs nothing, blocks nothing currently on the roadmap — the
stress suite's three items are Nat/Id, `List`, and `Acc` (which is tier 2 and
needs `W` + funext regardless). Buys time to prototype C properly.

**Drawbacks:** a language for programming *and mathematics* that cannot
define a binary tree is not shippable, so this is a schedule choice, not an
answer; and the longer it waits, the more frontend machinery gets written
against the fording scheme that a route-C landing would retire.

---

## 9. Scoring

`✓` good, `~` partial, `✗` bad, for the axes of §3.

| Axis | A: W+funext | B: conv η | C: `Wf` former | D: elab | E: defer |
|---|---|---|---|---|---|
| β on open subterms (dependent) | ✗ | ✓ | ✓ | ✗ | — |
| unique canonical forms | ~ (generated only) | ✓ | ✓ | ✓ | — |
| axiom-free | ✗ (blast radius) | ✓ | ✓ | ✓ | ✓ |
| one regime | ✗ seam | ✓ | ✓ | ✗ seam | — |
| trusted base unchanged | ✓ | ✗ conv | ✗ former | ✓ | ✓ |
| meta-layer cost | none | LR at sums | 4 recursor branches | none | none |
| elaborator complexity | transports | none | none | highest | none |
| build cost | days | research | weeks | weeks | zero |

---

## 10. Encodings tried and rejected (do not relitigate)

All hit the §1 wall, each in its own dialect:

- **`D_below` sums** (simultaneous exact/below families) — well-defined and
  canonical, but the constructor must inject the shorter child at a depth
  equal to its own height, so it is a stuck case-split on a comparison.
- **Total size with a split point** — needs a convolution over a table of all
  smaller families; the split is stuck.
- **Code tables + `Fin` index** — the child's index becomes a data field
  (good!) but the child's type is then `El (nth k tbl)`, stuck at neutral
  `k`, and does not convert with the child's actual payload type.
- **Preorder token vectors + decidable well-formedness** — constructors
  concatenate, which is stuck on open children; and the eliminator would
  require a verified parser per declaration.
- **Gödel-coded shapes** — pairing arithmetic, stuck at the index.
- **Shape-indexed fording** (my recommendation on 2026-07-24, withdrawn the
  same day) — index the family by a shape so the parent's payload is
  literally the children's. The index type is then the tree shape itself, the
  very branching inductive we lack; stratifying it statically degenerates
  into either the code tables above or route C. Not a route; route C wearing
  a disguise.

---

## 11. What other systems choose

| System | Choice | What it pays |
|---|---|---|
| Coq, Agda, Idris | native inductive families in the kernel | a large trusted component (positivity + eliminator schema); nobody ships W-encodings for real data |
| Lean 4 | native inductives; funext *derived* from quotients | quotients primitive instead of funext axiomatic |
| cubical Agda | funext is a theorem, so W-encodings are livable | cubical machinery; still uses native data in practice |
| Isabelle/HOL, HOL4 | `datatype` encodes into a fixed universal labelled-tree type, carves a subset by a predicate, `typedef`s an isomorphic copy | works only because HOL is classical/extensional with *no* computation to lose — the mirror image of our trade |
| Cedille, impredicative encodings | Church/Parigot encodings with derived induction; constructors definitional | needs impredicativity, which predicative DeLaM will not give |
| Dybjer–Setzer descriptions | a universe of codes + interpretation — our Tarski `El` already *is* this | still needs a primitive μ; the description type is itself branching |
| container theory (AAG) | `W` + funext interprets all strictly positive finitary inductives | the funext; the statement is propositional, not definitional |

The pattern worth taking from the table: **every system with a computational
interest in first-order data puts a fixed point in the kernel.** The only
ones that encode datatypes into a universal type are the ones that had
already given up on definitional computation. We are the first kind of
system.

---

## 12. Recommendation, and what would change it

**C** (`Wf`, the tuple-children former), with **E** as the sequencing while it
is prototyped, and **A** as the considered fallback.

The argument in one line: with representation cost off the ledger (§3), the
only currency left is definitional behaviour, and A pays for a *presentation*
artifact of one former by weakening the whole theory's computation —
canonicity is not a reasonable thing to spend on a datatype encoding, and the
seam between `List` and `Tree` is a permanent user-visible wart.

What would move me to A:

- If wrinkle 6.2 (the ih's type) turns out to need a dependent-vector former
  *and* the mutual forest presentation is unpleasant, C's rule set stops
  being "one more former like `W`" and starts being C3 in disguise.
- If the ch. 07 obligation for `Wf` turns out *not* to be a variation on
  `W`'s — i.e. if the tuple-shaped LR case needs a new idea rather than a
  restriction of the existing one.
- If a survey of what we actually prove shows dependent recursion on
  branching data is rare, and non-dependent recursion (which computes fine
  under A) is the whole story.

What would move me to B: a convincing decision procedure for coproduct η that
stays local to `conv.rs`'s type-directed structure. I do not expect one.

---

## 13. If C: how to de-risk before touching the kernel

The prototype-first discipline cannot apply directly — you cannot build terms
in a former that does not exist. The substitute uses the kernel's global
context:

1. **Postulate the interface in Ψ.** `Tree`, `sup_f`, `elim_Wf` as layer-p
   type/term bindings with the intended types. The kernel checks everything
   built against them.
2. **Build the derived artifacts against the postulates**: constructors,
   `match`, no-confusion both ways, and a real proof by induction over a
   branching type (`Tree` mirror-mirror, say, matching the `flip flip` test
   in `tier1_fording.rs`). This validates the *typing* interface and the
   generator's shape completely.
3. **Then the kernel change**, with the β rules, and conversion tests pinning
   what step 2 could not: β on open subterms, canonical-form uniqueness,
   neutral behaviour at neutral arity.
4. **Then the ch. 07 pass** for the new former, as its own round.

Step 2 is where the wrinkles of §6 get settled honestly, and it is cheap.

---

## 14. Open questions either way

- Does `Wf` (if it lands) *replace* the fording scheme for linear types, or
  do both stay? Fording gives strictly better term size and is already
  validated; `Wf` gives one regime. Term size no longer matters (§3), so this
  is about how much frontend machinery we want to maintain.
- Does `Empty`-η go in regardless? It is cheap, plainly sound, and useful for
  any `W`-encoded data (route A's leaf case, tier 2's `Acc`).
- Mutual and nested recursion (`Rose { Node(List<Rose>) }`) is deferred in
  every route; C makes it nearly free (the forest presentation *is* mutual),
  which is a point for C that this document has not scored.
- Indexed families still want fording by `Id`, which has no η — unchanged by
  this decision, and tracked separately.
