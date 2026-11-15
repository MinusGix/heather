---
title: Stress-proof acceptance suite for the frontend
status: closed
labels: [frontend,testing,milestone]
blocked-by: [elaborator-design, inductive-compiler]
created: 2026-07-23
updated: 2026-07-26
---

The acceptance gate for [[elaborator-design]]: the stress proofs are not an
alternative to the frontend, they are how we know it works — and they are
barely feasible without it. When this suite passes, defining the IR is just
another `inductive` and simulate another `def`, and
[[ir-simulate-design]] reopens in-language.

The three items (agreed 2026-07-23):

1. **Nat arithmetic + Id lemmas.** comm/assoc via `elim_Nat`;
   `sym`/`trans`/`cong` via J. Exercises Id and the elaborator's
   annotation synthesis. Gates elaborator stage 1 (explicit levels, no
   metas) and again stage 2 (annotations dropped).
2. **List via tier-1 fording.** The forcing function for
   [[inductive-compiler]] tier 1: exact-height encoding, derived recursor,
   constructor injectivity/disjointness (no-confusion via large elim),
   plus a real proof or two (e.g. append associativity). Hand-prototyped
   first, then reproduced by the generator.
3. **Acc via W** (tier 2, hand-built). Exercises the synthesized-ih β rule
   — the newest, least-battle-tested kernel machinery — and the
   W + Id + funext indexed-containers story from
   [[kernel-v1-extensions]].

Each item's elaborated output goes through the real kernel check (the
frontend soundness-by-construction property from [[elaborator-design]]).

## Log

- 2026-07-23: Opened; items agreed in the frontend-first route discussion.
- 2026-07-23: Item 1 PASSING at elaborator stage 1 (explicit-annotation form): add_zero/add_succ/add_comm/add_assoc via elim_Nat with explicit motives + ih patterns, sym/trans/cong_succ via J, all elaborated from surface syntax and checked by the real kernel (crates/elab/tests/nat_suite.rs). Also: 2+2==4 by bare refl (computation check), and negative tests confirming the kernel gate rejects wrong proofs/lemma uses. Item 1 re-gates at stage 2 when the annotations drop.
- 2026-07-24: Item 2 half done, 2026-07-24: List via tier-1 exact-height fording is hand-prototyped and kernel-checked (crates/elab/tests/tier1_fording.rs) -- derived recursor, append, append_nil and append_assoc by induction, disjointness and per-field injectivity incl. the recursive field, plus negative controls. Remaining for the item: reproduce it from a surface 'inductive' declaration once the tier-1 generator exists. Note the prototype adds a second type (Bits) beyond the item's text, because List's height classes hold one constructor each and so never exercise the sum spine or same-height disjointness.
- 2026-07-26: Item 2 is now reachable and half-done. 'List via tier-1 fording' is misnamed as of 2026-07-26: there is no fording — List, Bits and every branching declaration lower onto the Wf former through one path (docs/inductives/inductive-tier1-wf-lowering.md, closing [[tier1-branching-constructors]]). What the generator now produces for a tier-1 declaration: the type, constructors, the recursor via a guarded self-call, and no-confusion (disjointness by large elimination over Wf, injectivity at both payload and recursive fields) — crates/elab/tests/inductive_tier1.rs, 13 tests. What item 2 still wants on top of that is the PROOF content: a real theorem or two about a linear type, e.g. append associativity over List, written at the surface. mirror(mirror t) = t over Tree is the branching analogue and is done.
- 2026-07-26: Item 2 DONE: proof content over a *generated* tier-1 List is written at the surface and kernel-checked — crates/elab/tests/tier1_list_proofs.rs (6 tests). append_nil and append_assoc by induction (the ih is the guarded self-call, with two constant parameters carried along in assoc — a shape mirror() never exercised), plus rev_append, which is the first proof in the suite to *compose* two earlier inductive results (cong_append_l on the ih, then append_assoc, chained by trans_list) rather than closing an arm with refl and one congruence. Also pinned: the Cons equation holds with all three variables open (append(Cons(h,t),ys) = Cons(h,append(t,ys)) by refl), which is the beta-on-open-children property route C was chosen for, now observed from a generated declaration rather than the hand-built encoding. Four negative controls assert the *kernel* rejected them with NotConvertible, so none of the positives is vacuous: append(xs,Nil)=xs is not refl, a false closed equation, Cons(h,t)=Nil, and the same induction skeleton applied to commutativity. Nothing in the generator needed changing — every proof went through on the first run, which is the real result. Item 2's original text ('List via tier-1 fording') is now fully superseded: no fording, one Wf path. Remaining for the issue: item 3, Acc via W.
- 2026-07-26: Item 3 DONE, and with it the suite: Acc via W is hand-built and kernel-checked -- docs/inductives/acc-via-w.md, crates/kernel/tests/acc.rs (13 tests, workspace at 434). The indexed-container fording as specified: W0 = W(a:A). Sigma(b:A). R(b,a), root and coh (a code, by elim_W at the large motive Ty 0) cut it down to Acc(a) = Sigma(t:W0). Id(A; root t; a) x El(coh t). Headline is the equation the item exists for -- wfrec(a; intro(a;h)) == st a (lam b r. wfrec(b; h b r)) DEFINITIONALLY with a, h AND the step st all open variables -- so elim_W's synthesized-under-a-lambda ih fires at an abstract position, which is the machinery no other recursor exercises (Wf's ih is Fin-indexed and transient). Instance is the omega+1 order (A = Unit + Nat, every numeral below omega, nothing below a numeral): one node of genuinely infinite arity, which is what puts Acc in tier 2, and no arithmetic. Closed computation goes through that node (wfrec(omega; acc_omega) == 1). Three negative controls: mis-indexed children are rejected (so the fording is not vacuous), the computed value is not 0 or 2, and at a VARIABLE accessibility proof the same call is stuck -- beta is not blind. Two findings beyond the item: (1) Psi is EMPTY throughout, so tier 2's recursion direction needs no funext -- the standing 'W + funext' claim covers proving Acc a proposition, not defining or computing with wfrec; (2) Unit-eta is load-bearing in the case arms (inl u == omega), while Empty-eta -- which [[empty-eta-conversion]] names Acc as its customer for -- is not involved at all, because leaf arms BUILD children with elim_Empty rather than comparing them.
- 2026-07-26: CLOSED. All three items met: item 1 at stage 1 (nat_suite.rs) and re-gated annotation-free at stage 2 (implicit_args.rs, per [[elab-stage2-metas]]), item 2 over a generator-produced tier-1 List (tier1_list_proofs.rs), item 3 here. Its own acceptance clause -- 'when this suite passes, defining the IR is just another inductive and simulate another def' -- is now the live question, so [[ir-simulate-design]] reopens in-language. What the suite does NOT cover, tracked where it belongs rather than held open here: Acc at the SURFACE (needs tier-2 generator support and a function-typed inductive field, which reject_function_fields rules out today) stays under [[inductive-compiler]].
