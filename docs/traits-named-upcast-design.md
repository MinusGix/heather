# The upcast that is never built: a dispatched projection reads through it

Status: **round slice**, retiring
`issues/upcast-assembly-cost-at-open-carriers.md`. Amends
`docs/traits-owner-dispatch-design.md` §3 and §7.1, which own the upcast rule;
constrained by `docs/traits-layer1-design.md` (flattening, per-field `owner`,
canonical parents) and `docs/traits-layer2-design.md` (search order, the
kernel gate on every proposal, trace-as-data).

**No kernel change, no metatheory obligation, no new registry, no change to
the search order, no new Ψ artifact.** Step 1b is still step 1b and still
proposes the same term to the same gate. What changes is what the *one*
consumer that is not a value does with the answer.

The round set out to mint a named Ψ definition per (child, ancestor) pair, and
that was built first. It is measured, kept in §5, and **withdrawn**: it buys
2.2× where the device below buys 38×, and it costs conversion fuel the corpus
cannot spare. The filing's own log rejected two levers on measurements; this
is a third.

---

## 1. The price this pays off

Owner-keyed dispatch builds a member's goal at the class that **declares** it,
so a field inherited from an ancestor is reached, at an open carrier, through
the resolver's upcast. Owner-dispatch §7.1 built that upcast as a record
literal — the ancestor's record over the child dictionary's own projections —
written out afresh **per occurrence**.

`lib/std/algebra.hthr`'s `plus_zero_of_comm` is four such occurrences in one
three-line proof, and it measured (2026-08-08, release, whole-file check):

| spelling | file |
| --- | --- |
| `requires a: AddCommMonoid<G>`, `a.plus(x, a.zero)` | 0.67 s |
| `<G: AddCommMonoid>`, `G.plus(x, G.zero)` | 35.9 s |

The diagnosis placed 90% of it in the kernel gate, growing **linearly** at
~0.78 s per occurrence, with ~100% of the constant in the *law* fields. And
the tax escaped the declaring theorem, because the assemblies are baked into
its **statement**: `nat_plus_zero` and `bool_plus_zero` paid 2.9 s and 7.9 s
to consume it at their concrete carriers.

## 2. The decision: dispatch reads **through** the upcast

The upcast has exactly two kinds of consumer.

- A **value**: a dictionary passed where an ancestor dictionary is wanted — a
  lemma stated at `AddMonoid<G>` discharged from an `AddCommMonoid<G>` binder.
  There the parent record is what is asked for, and it is built, exactly as
  §7.1 says.
- A **projection**: dispatch, which resolved a dictionary in order to take one
  field out of it. `x.plus(y)`, `G.zero`, `A.unit_r(x)`. This is the case the
  library is made of, and it is four out of four in the motivating proof.

For the second, the parent record is built and thrown away, because

> the assembled parent's `f` slot **is** `d.f`.

So the projection is taken from the **child** dictionary, at the **child's**
own flattened index (layer 1 §3 guarantees it has one), and the assembled
ancestor never enters the term.

Three things this deliberately is not:

- **Not a change to the goal.** Dispatch still builds its goal at the field's
  owner, so the candidate set is still computed from declarations alone
  (owner-dispatch §2.1), two unrelated owners are still ambiguous, and the
  ambiguity diagnostic is untouched. Nothing about *which* class answers moves.
- **Not a change to the value.** The two terms are equal by β and projection.
  The proposal is still built, still passes `checks_at` at the goal (layer 2
  §4.4) before anything here runs, and the projection that replaces it faces
  the ordinary declaration gate like every other term. A resolution that fails
  still fails, in the same place, with the same trace.
- **Not a peephole on terms.** It does not pattern-match a record literal and
  guess. The resolver *reports* where its answer came from
  (`resolve_goal_from`'s `up`), so the rewrite fires exactly when step 1b
  answered and never otherwise.

### 2.1 The provenance channel

`resolve_goal` grows a sibling, `resolve_goal_from`, taking one out-parameter:
the **child dictionary and its class type**, set when and only when step 1b
answers. `resolve_goal` is that call with `&mut None`, which is what every
other consumer takes — including the recursive one, since backchaining
recurses through `elab_check` into the plain entry point and so cannot leak a
nested search's provenance into an outer one.

Both dispatch sites — receiver dispatch (owner-dispatch §2) and type
projection (`docs/traits-type-projection-design.md`) — reach `project_field`
through one shared step, so the rewrite is one function called twice.

### 2.2 What makes the rewrite total

Three facts, all already relied on elsewhere:

- **The child has the field.** `extends` flattens, so the ancestor's field list
  is a sublist of the child's (layer 1 §3). A miss is impossible; it is
  *reported* by declining the rewrite rather than asserted, because a library
  must not panic to say two of its tables disagree.
- **The field is the same one.** The assembled parent's slot for `f` is
  literally `d.f` (owner-dispatch §7.1), and at a concrete carrier layer 1's
  synthesized parent is built the same way — so the diamond still collapses by
  construction and `refl` still relates the paths.
- **An override does not change it.** The rewrite reads the *child's* field. If
  the child instance overrode it, that is what the writer's dictionary holds,
  and layer 1 §4.5's agreement certificate is what makes it convertible with
  the ancestor's — which is exactly the argument owner-dispatch §2.2 already
  makes for owner-keying. The rewrite is on the same side of that argument, not
  a new customer of it.

## 3. What it measures

`lib/std/algebra.hthr`, release, whole-file check, with `plus_zero_of_comm`
migrated to `<G: AddCommMonoid>` and `G.plus(x, G.zero)`:

| | before | after |
| --- | --- | --- |
| the file | 35.9 s | **0.94 s** |
| the file with the call sites removed | 25.1 s | 0.85 s |
| `nat_plus_zero`, its own delta | 2.9 s | 0.035 s |
| `bool_plus_zero`, its own delta | 7.9 s | 0.075 s |
| the file, still spelled `requires` | 0.67 s | 0.62 s |

(Both `requires` figures are the same code path; the second is the same
machine later in the day, and is the like-for-like baseline the 0.94 s should
be read against.)

On a three-class reproducer the two spellings become indistinguishable —
0.342 s anonymous against 0.339 s named-dictionary, and 1.13M conversion steps
against 1.12M — because after the rewrite they are the **same term**. The
migrated theorem is not "fast enough": it is the exact-dictionary spelling,
written differently.

The library's remaining 0.94 s against the 0.62 s baseline is **not** in the
emitted terms — they are the same terms, which is what §4's `refl` pins say.
It is the resolver's own trial cost: the parent record is still assembled and
gated once per upcast occurrence, only to be read through. `plus_zero_of_comm`
alone accounts for +0.22 s of it across its four upcasts. Layer 2 §10 owns that
line already; §6 files what would recover it.

### 3.1 The asymmetry the diagnosis left open

The diagnosis noted `bool_plus_zero` at 7.0–7.9 s against `nat_plus_zero`'s
2.8–2.9 s and asked whether the fix erases it. It does not: at 0.075 s against
0.035 s the **ratio survives**, which says the asymmetry was never the upcast.
The likely owner is layer 1's synthesis *direction* — `Nat` is declared
parent-first, so `Nat::AddCommMonoid` fills `plus` by reference from
`Nat::AddSemigroup`, while `Bool` is declared child-first, so
`Bool::AddSemigroup` and `Bool::AddMonoid` are synthesized record literals and
relating the two spellings of Bool's `plus` unfolds a global Nat's route does
not have. Two orders of magnitude smaller than it was, and filed rather than
chased.

## 4. Acceptance

Per `docs/testing-generated-terms.md`:

1. **Open carrier, checking position**: `plus_zero_of_comm` at
   `<G: AddCommMonoid>`, whose statement and body between them reach two
   ancestors; and `refl` between it and the named-dictionary spelling, which is
   the pin that they are one term.
2. **Neutral and literal**: the theorem at an open `G`, and its two concrete
   uses at `Nat` and `Bool`, which compute.
3. **The value form**, unrewritten and unchanged: a lemma stated at an ancestor
   discharged from a child binder, and a grandparent two hops up.
4. **Overrides**: an instance that overrides an inherited field, dispatched at
   the owner and answered by upcast from the child — the field it reaches is
   the child's, and the certificate says that is the ancestor's.
5. **Negative controls**: upcast still refuses two unrelated classes; two
   unrelated owners of one name are still ambiguous; a failed goal still
   reports its trace, and the trace still names the binder that answered by
   upcast, in the same words.

## 5. The named definition, built and withdrawn

The fix the issue's log picked was a machine-named Ψ global per (child,
ancestor) pair, minted at class-declaration time:

```
fn C#upP<p⃗>(#d: C<p⃗>) -> P<a⃗> { P<a⃗> { f: #d.f, … } }
```

with step 1b proposing `C#upP(#dict)`. It was implemented and measured, and it
is not what shipped. Three findings, in order of weight:

1. **It fixes a third of the problem.** The library went 35.9 s → 11.4 s: a
   uniform 2.2×, where §2's rewrite goes to 0.94 s. The record literal was
   never the whole cost. Replacing it with an application leaves the ancestor
   dictionary *in the term*, so the field's type is still written in
   projections of something that has to be reduced again at every later
   comparison — 43.9M conversion steps against 1.1M for the named-dictionary
   spelling, with only 670 δ-unfoldings, so the unfolding was not the cost
   either.
2. **It costs conversion fuel.** A dictionary *value* built as `C#upP(d)` is
   2.3× faster in wall time than the assembled record, but concentrates its
   work into single comparisons: the owner-dispatch suite's
   `a_parent_lemma_resolves_from_a_child_binder_at_an_open_carrier` needs
   2²¹ fuel where the assembly needs under 2²⁰, and `DEFAULT_FUEL` is a trust
   knob, not a tuning one.
3. **It is not free at declaration.** Four mints for this file's two chains, at
   ~25–30 ms each: +0.12 s on every check, paid by files that upcast nothing.

Once §2's rewrite exists, the named definition's remaining customer is the
*value* form, where finding 2 says it must not be used. So it has no customer.

The one thing it did buy — a nominal recognizer, so the rewrite could key on a
Ψ index rather than a term's shape — the provenance channel of §2.1 buys for
nothing, and more honestly: it reports what the resolver *did*, not what a term
*looks like*.

## 6. Residue, with owners

- **The trial cost is what is left.** The parent record is still assembled and
  gated once per upcast occurrence, and then read through — ~0.32 s on this
  file, of which +0.22 s is one theorem. Skipping the build for a projection
  consumer needs a carrier check that is not a `build_ctor` — the class type is
  monomorphized, so the carrier cannot be read back off it — and that is a
  layer-2 §10 question rather than this slice's. `issues/traits.md`.
- **The Bool/Nat asymmetry** of §3.1 — layer 1's two synthesis directions do
  not cost the same downstream. `issues/traits.md`.
- **The rewrite is dispatch-only.** A dictionary that is a value stays a value,
  which is right; but a *chain* of them — an upcast passed to a function that
  projects — is not rewritten, because the provenance does not travel with the
  term. Nothing in the corpus does it. `issues/traits.md`.
