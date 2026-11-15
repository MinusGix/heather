---
title: Branching finitary inductives: how tier 1 handles 2+ recursive fields
status: closed
labels: [frontend,elaboration,inductives,design]
created: 2026-07-24
updated: 2026-07-26
---

Split out of [[inductive-compiler]] tier 1 on 2026-07-24, when the
exact-height scheme was written down and prototyped: it covers the **linear
fragment** (≤ 1 recursive field per constructor — `List`, `Bits`, snoc
lists) and provably does not extend to a constructor with two or more
recursive fields. That includes `Node(Tree, Tree)` and therefore the IR
expression knot, so this decision gates [[ir-simulate-design]].

Full argument: `docs/archive/inductive-tier1-lowering.md` §8.1. In brief:

- Exact height *is* computable for a branching constructor (`S (max h_l
  h_r)`), so the issue's original plan was right about the measure.
- What breaks is the **payload**. At height `m+1` the children's heights are
  `≤ m` with `max = m`, so the branch type is a disjunction of shapes, and
  the natural fix (simultaneous recursion producing both the exact family and
  `D_below h = D_ex 0 + … + D_ex (h-1)`, well-defined and canonical) forces
  the *constructor* to inject the shorter child into `D_below` at a depth
  that is the difference of the two heights.
- So `node l r` is a case-split on a height comparison, not a constructor
  form: with an open child it is stuck, and `match (node l r) { … }` stops
  reducing. That is precisely the property the linear fragment buys
  (`cons a l` β-reduces with `a`, `l` both variables — pinned in
  `crates/elab/tests/tier1_fording.rs`).
- Every other single-`Nat` measure hits the same wall for the same reason
  (total size needs the split point; preorder tokens need concatenation;
  Gödel-coded shapes need pairing arithmetic). The invariant: unless the
  parent's payload type is *literally* a container of the children's payload
  types, assembly takes computation on measures, and that computation gets
  stuck on open terms.

**Decision-support doc: `docs/branching-inductives-choice.md`** (2026-07-24)
— the routes below in full, scored against the axes that survive the
datarepr separation, plus the encodings already tried and rejected, what
other systems choose, and a de-risking plan. Read that before deciding; the
summary below is kept only as an index.

## Routes

- **(a) Branching goes to tier 2** — `W` + `Id` + funext-as-axiom, as
  [[kernel-v1-extensions]] already argues for infinitary types. Cheapest to
  build; loses definitional `match` β on branching data, so the IR's
  equational reasoning becomes propositional.
- **(b) Multi-index fording** — index the family by a *shape* (a pair of
  heights for a binary node) so the parent's payload type is literally the
  children's. Preserves β; the index type wants to be a branching inductive,
  which is circular unless stratified statically. Needs real design work,
  and it is the one route that keeps first-order data definitionally clean.
- **(c) Keep `D_below`, canonicalize the embedding** — emit the concrete
  injection when heights are literals, postpone otherwise. Restores
  computation in the closed case only; cheap, partial, hard to explain.

Recommendation as written up: **(b)**, with **(a)** as the fallback that
unblocks the IR immediately (W is already in the kernel and already argued
sound in [[metatheory-ch07-pass]]'s pass). Needs a decision before the
tier-1 generator grows a branching path.

Related and deferred alongside it: mutual/nested recursion
(`Rose { Node(List<Rose>) }`, §8.2 — same simultaneous-family device, but
the part that works) and indexed families (§8.4 — fording an index means an
`Id` field, and `Id` has no η).

## Log

- 2026-07-24: Opened. Scheme + prototype for the linear fragment landed; the
  branching defect is diagnosed (β on open children), routes (a)/(b)/(c)
  written up, recommendation (b) with (a) as the IR's fallback.
- 2026-07-24: Choice written up for deliberation: docs/branching-inductives-choice.md. Reframed around WHERE the cost lands rather than which encoding trick: (A) an axiom -- W + funext, which extends funext's blast radius from infinitary types to all branching first-order data; (B) the conversion checker -- Empty-eta plus coproduct eta, which would make W's children behave like tuples in place (research-grade for the coproduct half); (C) the former set -- a Wf former with arity-Nat and Sigma-tuple children, so Sigma-eta and Unit-eta do the work funext was doing; (D) the elaborator -- canonicalize the stuck embedding when heights are literal; (E) the surface -- defer branching declarations. Two things the discussion settled that change the analysis: the datarepr separation (kernel-side inductives are spec objects, runtime representation is chosen separately and certified) voids every efficiency objection and takes the flat-IR escape hatch off the table, leaving definitional behaviour as the only currency; and the ch. 07 funext-leak audit means route A's axiom is contained w.r.t. the meta layer, which is a point in A's favour I had overstated against. Also recorded: A does not INTRODUCE funext (tier 2 needs it for Acc anyway), it widens it; route A leaves a permanent seam where induction on List behaves definitionally and induction on Tree does not; and route C's real crux is not difficulty but carrying two branching formers, since W stays for the infinitary tier. Recommendation stands at C with E as sequencing and A as fallback, with three named falsifiers. Note for the record: this decision exists because kernel-v1-extensions' promise that 'first-order data stays on the finitary encodings' is false -- the finitary encodings reach the linear fragment and provably no further.
- 2026-07-24: 2026-07-24: Ran the §13-style side-by-side comparison (Fable): crates/elab/tests/branching_route_a.rs (Tree as W + funext postulates, 10 tests) and branching_route_c.rs (postulated Wf-style interface + propositional beta laws, 4 tests), same theorem mirror (mirror t) = t on both. Results: (A) confirmed the doc's §4 claims against the real checker — sup constructors on open children check, match beta fires on open subterms (mirror (node l r) ≡ node (mirror r) (mirror l) definitionally, no funext), non-dependent recursion computes on closed data; the dependent induction goes through with exactly one funext per constructor ARM including Leaf's (pinned by a negative test: refl in the leaf arm is rejected — Empty-eta would erase that one), and the instantiated proof at closed leaf is stuck (not conv with refl) — dependent recursion does not compute, pinned by test. (B) route C interface validates: motive polymorphism through Ty-0 codes works (wrinkle 1 exercised — Tree = El treeCode), the arm structure after deleting the beta-markers is refl for Leaf and cong+cong+trans for Node — strictly smaller than A's arms, no funext, no eta. Also: the A-side generator would need one funext INSTANCE per position type (Empty, 2) unless the axiom is schematic — a generator cost the doc didn't note. Wrinkle 6.2 (ih type) not yet exercised: this test's eliminator uses the binary-constructor telescope directly, not the n-ary Fin-indexed ih; that is the remaining step-2 item.
- 2026-07-24: 2026-07-24 (later): Wrinkle 6.2 round complete: crates/elab/tests/branching_route_c_nary.rs (6 tests, all passing). Postulated the GENERIC n-ary Wf interface (supf + eliminator whose ih is Pi(i : fin (arity a)). M (nth (arity a) cs i)) with arity/tup/fin/nth all DEFINED via elim_Nat so the real kernel computes them, and ONE generic beta postulate for mirror (per-constructor facts derived by kernel computation, matching the real former's rule shape). Findings, all in C's favor: (1) wrinkle 6.2 RESOLVED as predicted — the Fin-indexed ih is fine because it is transient: nth at literal arity + neutral tuple reduces to the projections (pinned by test), so ih applications have the per-child types definitionally and nobody ever compares two ihs; no dependent-vector former needed, no forest presentation needed. (2) The central route-C claim validated against TODAY'S conversion: for a NEUTRAL tuple cs, supf (inr u) cs is convertible with node (fst cs) (fst (snd cs)) — Sigma-eta + Unit-eta discharge exactly the equation route A postulates funext for; the arity-0 case (any cs' : Unit gives the same leaf) also holds, so leaf uniqueness is definitional proof irrelevance as claimed. (3) The same mirror-mirror theorem goes through the generic single-step interface with the identical surviving proof content as the per-constructor round (leaf refl-shaped, node cong+cong+trans). Remaining C risk is now confined to the kernel-former round itself (step 3: reduction rules, rec.rs telescopes, ch. 07 LR) — the interface and the eta-bridging are validated. The doc's move-to-A trigger 1 (6.2 needs a dep-vector former or unpleasant mutual presentation) did NOT fire.
- 2026-07-25: 2026-07-25: DECISION TAKEN — route C, as The method (not a workaround). Evidence and reasoning recorded in docs/branching-inductives-choice.md §15; rules sketch in docs/wf-former-design.md; kernel work tracked in wf-former. Both §12 falsifiers resolved in C's favor short of implementation: 6.2 did not fire (Fin-ih transient, validated), and the eta-bridging C needs is already a theorem of today's conv.rs. Remaining falsifier: the ch. 07 LR case, carried by the wf-former issue.
- 2026-07-26: CLOSED by the phase-5 generator round of [[wf-former]]. `Tree { Leaf, Node(Tree, Tree) }` is declared at the SURFACE, and `mirror (mirror t) = t` is proved by an ordinary recursive `theorem` through the generated recursor — crates/elab/tests/inductive_tier1.rs::mirror_of_mirror, which is what crates/kernel/tests/wf.rs proves by hand. Scheme: docs/inductive-tier1-wf-lowering.md (written before the code, then corrected in one place by it); mechanization: crates/elab/src/wf.rs. The branching defect this issue was opened for is gone at the root rather than worked around: there is no height, no D_below, and no stuck embedding, so `Node(l, r)` is a constructor form with l and r open and `match` beta fires on it (pinned by beta_fires_on_open_children). Route (a)/(b)/(c) of the original write-up are all moot — the answer was route C of docs/branching-inductives-choice.md §15, i.e. change the former set. What did NOT come with it, and is split off rather than silently dropped: nested recursion (Rose). The former types it — arity-as-a-term makes the child count data — but lowering a declaration whose field type is a user-declared List would make the generator identify that List with the kernel's Vec, and the round trip fromVec(toVec xs) is convertible with xs only for canonical xs. So it would cost beta on OPEN subterms, which is the one property this tier exists for. What unblocks it is surface support for a children-container field type, i.e. a surface-language round, not a generator tweak; docs/inductive-tier1-wf-lowering.md §8.1 has the argument. Also still open and unrelated to branching: indexed families (ford by Id), mutual declarations, and polymorphic containers (a surface gap — the type grammar has no inhabitant above level 0 to instantiate a parameter with; the lowering itself takes its level from the shape and assumes nothing).
