---
title: The elaborator emits the normal form of a type argument it normalized to decide a match: 3.5× per combinator layer, written down
status: open
labels: [elaboration,representation,performance,design]
created: 2026-09-16
updated: 2026-09-22
---

docs/conversion-query-traversal-design.md (2026-09-16). To check anything against `Post(source,begin,relation,REPLY)` — a `→ Type` body that matches on `REPLY` — the elaborator drives `REPLY` to a constructor; each parser combinator layer (`bind_at`, `map_at`, `rebase`) is itself a two-branch match over a record-shaped `Reply`, so the normal form is ≈3.5ⁿ in the nesting, and **the elaborator emits that normal form** into the obligation instead of the application it started from. The kernel then pays a flat ~2 µs per node of it (96.5 % of `complete_post`'s 3.68 M conversion queries are the `App` rule's two checks: `Ty/Ty` at type-argument slots and the `Π` rebuilt from annotations against the inferred one) and its own evaluator is idle. Measured with the component byte-identical and only the reply varied: 6 495 / 390 503 / 2 395 753 / 7 928 179 / 29 447 197 queries (`probes/t_qt2`, `t_qt1`, `t_cp9`, `t_qt3`, `t_qt5`), `elab_whnf_ns`, `decl_emit_ns`, kernel gate and maxrss (1.4 → 2.8 → 9.5 GB) all tracking the same curve; naming the reply in the library is a measured zero (`t_qt4`). `complete_post` (10.9 s), `close_body` (6.6 s), `expr_body`/`factor_body` are this family.

The fix is the elaborator's, at the boundary between normalizing to decide and emitting to record: keep the pre-normalization application as the spelling the annotation carries and let the kernel's lazy δ unfold the head on demand (design §5). Open questions for the implementer (design §8 item 2, coordinator's addendum): which emitter writes the normal form — most likely the dependent-match motive built by abstracting the scrutinee out of the *whnf'd* expected type — and what the motive becomes when the scrutinee occurs only after unfolding; and whether the kernel then reproduces the cost in its own evaluator per branch (the bar therefore includes evaluator steps and kernel gate, not queries alone). Rejected on measurement: naming the reply, hash-consing (the term is already shared and still exponential in RSS), a kernel memo (no repeated syntax at a repeated Γ), the typed-`App` constant factor (real, 36 %, its own issue). Related: [[quoted-component-traversal-remainder]] (closed into this), [[conversion-typed-eliminator-congruence]], [[parser-certified-composition-cost]], [[elaborator-canonical-type-spelling]].

## Log

- 2026-09-16: Implementation pass ran the design's §8 spike and **stopped** on item 2 (docs/conversion-query-traversal-design.md §10). Item 1 re-confirmed the exponent on d53ec73 to the unit (2 395 753 / 7 928 179 / 29 447 197 queries, emission and elab-whnf clocks tracking). Item 2: the exponent is two calls per item, the same two in complete_post as in the probes — 'whnf' at build_ctor (crates/elab/src/inductive.rs:1966; 5.4 / 492.6 / 2 213.5 ms across the curve) and 'emit_ty' at respell_spine under it (1.1 / 525.9 / 2 989.1 ms), both under wf_branch < build_elim_wf < elab_match_wf < elab_convoy. The motive is NOT the carrier: matching::expose's whnf is 113.7 → 140.9 ms across a layer that multiplies everything else by 3.5, so the coordinator's motive hypothesis is refused and the second one holds one step further in — what is written is the constructor value's Inl/Inr and Pair annotations, not a lambda domain. The pre-whnf type is in hand one line above the call and is still not a usable spelling: what is emitted are the **components** of the reduct (a Sum's summands, a Σ's fst/snd), and the pre-normalization term El(case(…)) has no sub-terms that correspond to them — the kernel's Inl/Pair rules take a former's components, not a term that reduces to the former. The mass inside those components is the terms the reply computed, substituted into a type-code application; their folded spelling exists only as projections of the un-reduced reply, which means the reducer telling its caller which output sub-term came from destructuring which input sub-term. That is reduction provenance in crates/kernel, so §5 is not one elaborator site and this needs its own design pass. Nothing under crates/ changed; the spike instrument is probes/nf_spike.patch, the scripts probes/nf_*.sh.
- 2026-09-16: Spun out of the same spike: [[emit-ty-rewalks-normalized-type]] — the emission chokepoint's own traversal of the reduct, a constant factor downstream of this exponent and not to be banked against it.
- 2026-09-16: Coordinator: mechanism sharpened by docs/projected-tuple-tower-design.md. The coordinator's reading (un-fired projections of tuple towers) is refuted by a node counter at `build_ctor`: firing every proj-of-pair/β/case-of-ctor to a fixed point leaves the reduct growing ×3.6–3.9 per layer (pre ×4.0–4.5); node count ≈ query count. The normal form is exponential **as a tree** (each layer's three fields mention the three below) and linear **as a DAG**; `Term` has no `let`, so the linear spelling needs names: a sharing-preserving, elaborator-owned readback of the machine's whnf value, memoized on closure identity, minting a generated Ψ declaration under the constructor telescope for every sub-value spelled twice (design §6; argued against docs/nbe-conversion-design.md §7 in §5). Candidate D (the δ-free simplifier) measured: −25–44 % queries on the curve, −42 % RSS at `t_qt5`, `complete_post` 11.2 → 8.8 s, **but** it reaches no other showcase item and regresses ten (case-of-ctor firing changes a spelling the kernel hit on) — declined, kept as `probes/tt_D.patch`. Reach of the chosen mechanism on the showcase: `complete_post` only; `close_body`/`expr_body`/`factor_body` do not go through a `build_ctor` reduct and need their own attribution before this round is chartered against the family.
- 2026-09-16: Coordinator: the readback round's spike confirms the design and prices it (docs/projected-tuple-tower-design.md §11). Value-graph counter (`crates/elab/src/rbcount.rs`, `HEATHER_RB=count`): naive readback = the normal form (0.67–0.85× the reduct, same ×3.8–3.95 curve); the graph is linear (+~19 k nodes per layer; tree/graph 196× at `t_qt5`). Unit of sharing: name shared sub-values saving ≥ 64 nodes → 30–42 names per reduct, `complete_post` 1.96 M emitted nodes → 80 k, `qt_deep`/`qt_pure` ×3.0 against ×18.5; Ψ growth over the whole showcase 152 bindings (31 in `complete_post`, 0 in ~900 items); a codes-only naming fails (1.44 M) — mints name terms at arbitrary types, typed by position. Stage one (`rbemit.rs`, `HEATHER_RB=fire`, inert by default): the readback spelled but not named lands behind its flag — misses −90 %, steps −4×, RSS −45 % on the curve, but the exponent stays (×2.8/×3.4) and 14 `list::*` rows regress, so it is not the default path. Blocker for the naming, now designed (§11.4): mints enter Ψ mid-declaration through the goal arena's reserve/allocate/realize shape with a body, then image/`ModuleDelta`/cache identity for a binding not keyed by a declaration tag. Next round.
- 2026-09-16: Coordinator: the naming spike STOPped (docs/projected-tuple-tower-design.md §12). Mints in a scratch Ψ block, keyed as `rbemit.rs` keys its memo — on (closure, depth), with Δ = every binder above the node — name 8–12 sub-values per reduct and buy a 2–6× constant (`complete_post` 2.63 M → 0.71 M emitted nodes) while the per-layer ratio stays ×2.5–2.6; naming every shared node emits the same count, so *that* device is at its ceiling. §12.5 attributes the gap to "a closure reached under binder chains of different length, which no Δ serves", and concludes the 80 k price is a sharing the term language cannot express. **Coordinator's reading, to verify first, not a claim:** a value that is one pointer under two binder chains cannot depend on either chain's binders (a closure under a binder is a different object), only on the ambient Γ and on whichever fresh neutrals it mentions; so a Ψ definition abstracted over **exactly its free variables** (closure conversion, not the innermost-k suffix §12.5 tried) is one name per *value*, referenced under any chain with a substitution of those variables at their current indices — depth-independent by construction, and the `HEATHER_RB_MERGE` negative measured an emitter that merged without re-indexing, i.e. unsound syntax rather than the mechanism. If that reading holds, §11.2's price is reachable; if the shared values do mention chain-specific neutrals, §12's sentence stands. Next: a design pass whose first instrument computes the exact free-variable set per shared value and checks it is the same under every chain that reaches it.
- 2026-09-16: Coordinator: the reading holds (docs/name-per-value-design.md). Free-variable instrument on `rbcount.rs`: of the 344 threshold-clearing shared values across the showcase's 8 092 reducts, **zero** are reached under a chain missing one of their free variables; a mint over exactly Δ = fv (mean |Δ| 2.4–2.7, max 5), referenced `u^δ` per occurrence, emits `qt_pure`/`cp_andt`/`qt_deep`/`complete_post` at 35 651 / 88 053 / 115 125 / **89 132** nodes (§12.3's best: 73 236 / 217 492 / 574 472 / 708 206; the rewriter's reduct for `complete_post`: 2 634 824, i.e. 29.6×), per-layer ratio ×2.47 / ×1.31 — the value graph's curve. §12.5's "a sharing the term language cannot express" is withdrawn: its negatives were a per-depth-keyed context shrink (6 %) and a merge without re-indexing. §11.2's 80 477 was priced over a memo that merges an out-of-line forced value on its address alone; the honest ceiling is 89 132. Showcase: 336 mints in 16 items. Next: implement — Δ = fv mints through the goal arena's reserve/allocate/realize shape (§11.4/§12.7 arithmetic), on the default path gated on the reduct/graph ratio.
- 2026-09-16: Coordinator: the mint round STOPped at step 0 on scope, not mechanism (docs/name-per-value-design.md §8). The 89 k column counted shared **types** as nameable; a Ψ binding names a term. Term-only mints: `complete_post` 103 197, `qt_deep` 133 050 emitted (25×/30× under the reduct), per-layer ×1.64/×1.30 — the shape bar met; naming the shared types through their codes (`⌜T⌝` as a term mint, `El(u^δ)` at use; formers `+` 196, `Π` 14, `El` 10, `Σ` 9 over the showcase) recovers §2's column at +0.1 %. Decision: both halves in one round, term mints first and measured alone, the type-code half second and measured on top; sub-bars 103 k / 89 k respectively. `TM0` within 0.5 % of `TM64` (the threshold is not the lever); charging sharing by tree multiplicity is not a device (740–5 353 mints per reduct).
- 2026-09-16: Coordinator: the mint is built (`crates/elab/src/mint.rs`, docs/name-per-value-design.md §9) and ships **opt-in** (`HEATHER_RB_MINT=1`, threshold 1 024; default path byte-identical, the five Ψ-renumbering sites now take `global_padding()`). At T = 64 it lands on §8.2's column (`complete_post` 90 844 emitted nodes, +1.8 %; 40 term / 40 type mints; |Δ| ≤ 5; typing refusals **0**, not 7 of 19; `code_of` refuses none of the 229 shared types) and the kernel columns follow: `complete_post` queries 3.70 M → 0.78 M, gate 6.58 → 1.65 s, `decl_emit` 626 → 174 ms; `qt_pure` gate 553 → 124 ms. Two findings the design lacked: the counter had two memos the emitter did not (out-of-line forced values by address+depth; 0-binder closures merged across depths), so the device carries a provenance map and mints one name per value; and the choice must be top-down over multiplicity (80 names, not 196). **Not landed**, on the readers audit: (1) a name hides a record from `record_of_at` (T = 64, `relation.hthr`); (2) at T = 256 the calculator stops converting `leb(2,2)` against `leb(2,len_append(…))`; (3) a **kernel** `NotConvertible` on `x86_64`'s `fetched_executes` — a well-typed mint whose occurrence carries the statement `infer_term` chose where the site wants another; the whole-answer `infer_type` gate that fixes (3) also declines `complete_post`/`qt_pure`. Cost: the readback runs at every `build_ctor` to learn there is nothing to name (`elab_whnf_ns` ×3.5–4 on fired items; a pre-gate on the value graph is the first fix). Next: attribute (3) with a conv-miss trace on `fetched_executes` with the device on, then (1) and (2); the question is what a name may hide from a structural reader and from conversion.
- 2026-09-16: Coordinator: the readers-audit pass was **stopped mid-way** at the user's request (time versus gain; the device line has become intricate). Its partial, untested edits are parked on branch `wip/mint-readers-audit` (commit 10aee3b: mint.rs/lib.rs/gendefs.rs edits toward attributing the `fetched_executes` kernel rejection, plus the reproducer `probes/fe1.hthr`; the brief is in `probes/brief-mint-readers-audit.md` on the untracked scratch dir). Master stays at 4359f2e with the mint opt-in. Decision: no further slices on this line; the next step is a **structural design pass in a fresh session** — why sharing does not survive in the kernel term language (no let; Rc-sharing dies under de Bruijn shifting) and whether one kernel-side change (a sharing-preserving representation with typing memoized on node identity per context, or a let form costed against the Coq formalization) dissolves the mint, the see-through arms and the quote slices together. The refl-theorem evaluator cost ([[refl-theorem-step-cost]]) belongs in the same pass.
- 2026-09-17: Re-measured on the current tree through `heather check --only parser_primitives::complete_post` (release, width one, desktop; 13.5 s per probe against 48 s for the whole file): the item is 9.6–9.8 s, 3,681,039 conversion queries, 14,346 misses (0.45 s summed — a remainder), 246,634 steps. The query trace (every 64th, 57,517 samples) reproduces docs/conversion-query-traversal-design.md §2 on this tree: heads Ty 54 %, Pi 36 %, El(?) 9 %; 92 % of compared types under 100 characters; 98 % of site stacks at the 40-frame cap, `Pair×12 < Snd < Snd < Fst < Fst < App×20` — the record tower's constructor annotations. The opt-in mint (`HEATHER_RB_MINT=1`) does not move the kernel's count here: 3,723,257 queries, 298,380 steps, 12.8 s — so the naming device is not a lever on this item, consistent with §10.3's "exponential, not exponentially repeated". Nothing landed: what is left is the structural pass (a sharing-preserving kernel representation with typing memoized on node identity, or a let form) or the reducer-provenance change §10.3 names, and the constant-factor typed-App rule on [[conversion-typed-eliminator-congruence]] (the Pi/Pi 36 % plus both ty_checks per App node) — a kernel typing-rule change, since the stored annotations are load-bearing for typed conversion, and not a slice.
- 2026-09-18: The 09-16 entry's "the refl-theorem evaluator cost belongs in the same pass" is withdrawn: [[refl-theorem-step-cost]] is attributed (2026-09-18) to per-gate-call global rescoping in `Defs::body`, a value-machine constant with no relation to term sharing or a `let`; it has its own fix candidate there.
- 2026-09-18: Traced, and the 27× record axis is **this family**, not a new defect — which
  means the round it implies is the one the user paused on 2026-09-16, and it is
  not chartered here.

  `HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=char_run` on the controlled pair
  (`probes/str/p10.hthr`, width one, release + value-metrics, 1,527,742 records =
  the whole miss count):

  | head pair | misses | share | summed ms |
  |---|---:|---:|---:|
  | `Nat/El⌜⌝` | 1,470,824 | **96.3 %** | 2,089 |
  | `El(?)/Sigma` | 15,757 | 1.0 % | 3,001 |
  | `Pi/Pi` | 14,820 | 1.0 % | 438 |
  | `Wf/El(?)` | 12,600 | 0.8 % | 1,101 |
  | `El⌜⌝/Sigma` | 6,655 | 0.4 % | 131 |
  | `Sigma/Sigma` | 3,233 | 0.2 % | 1,274 |

  The dominant row is one structural shape repeated: **1,470,784 of its 1,470,824
  records have exactly six `TmSigma` on the site stack**, at
  `Var < App < App < TmSigma×6 < App…`, comparing the primitive `Nat` against the
  quote `El⌜Nat⌝` at ~1.4 µs each. Six is the Σ tower a
  `Certified<Char, List<Char>>` over a `Cursor<Char>(source)` builds. So a record
  token type does not introduce a new disagreement; it adds Σ layers to the tower
  whose every type-argument slot already pays the `Ty/Ty` check that
  docs/conversion-query-traversal-design.md §2 measured at 54 % of
  `complete_post`'s queries. `Char` multiplies an already-exponential term — the
  27× is a **multiplier on this family's base**, with combinator nesting held
  identical between the two sides of the control pair.

  Consequences for scheduling, which the coordinator should decide and this entry
  does not:

  - The standing decision on this family (2026-09-16, user) is *no further
    slices*; the next step is a structural kernel-side design pass in a fresh
    session — whether one change (a sharing-preserving representation with typing
    memoized on node identity, or a `let` costed against the Coq formalization)
    dissolves the mint, the see-through arms and the quote slices together. That
    decision covers this axis too, now that the axis is this family.
  - One candidate *is* newly attractive on this datum and is small: the
    `Nat/El⌜⌝` pair is the **bounded** quote arm
    ([[quote-see-through-bounded-arm]], closed) applied on the *conversion*
    side rather than the matcher's. 96 % of the misses are a primitive against
    its own quote at a type-argument slot, uniform in shape; one bounded head
    step of `decoded` in `Tc::conv_ty` turns them into hits. It is a kernel
    conversion rule, so it needs this area's protocol (design pass, fresh before
    table, bench gate) and it is exactly the kind of cleverness
    [[kernel-acceleration-policy]] says to weigh — not something to slip in.
  - `probes/str/p10.hthr` is the cheapest reproduction this family has: 90 lines,
    both sides in one process, no showcase. Where the prior rounds needed
    `complete_post` inside a 500-line file, the axis is now one declaration
    duplicated at two token types.
- 2026-09-20: Coordinator: the structural design pass the 09-16 entry asked for is written — docs/intro-by-type-design.md (2026-09-20, after discussion with the user). The route is neither a `let` nor a resumed mint: five **checked spellings** of the existing formers at the computing layers only (`pair@`/`inl@`/`inr@`/`fst@`/`snd@`, one annotation = the un-reduced type the elaborator had at `build_ctor`/`projection`), conservative by a typing-preserving translation to the component forms (§2.4), refused at layer c so the code grammar and all 56 recursor branches are untouched (§2.2–2.3: `tm_pair`'s telescope types `u_a` by `U_S`, which is why the existing forms cannot change in place). Forced consequence: `fst@`'s inferred type has no syntax, so `typing.rs` becomes `Tc<D: Dom>` over the boundary `conv.rs` already has, `Values` in production and `Syn` as the differential oracle (§3) — the stage docs/nbe-conversion-design.md §7 deferred as cold. Conversion's arms do not move (no arm reads an intro's or projection's annotation, confirmed on this tree). The mint, readback and counter are superseded and deleted in stage 2. Stage 3 (the elaborator's own transient reduct) is deferred with candidates (§5). Gates, kill criteria and the corpus are in §8–9; day-one work is [[check-only-no-stored-image]]. Per the user: implement, then analyse — no falsifier up front.
- 2026-09-20: Implementer, §9.0 (six first-hour verification items), on 5cf63f2. Two design
  adjustments follow from them; both are *simplifications* and both are stated
  here before any code was edited.

  **1. No conversion arm reads an intro's or a projection's annotation —
  confirmed, and stronger than §3.4 claims.** `TmView` has **no `Pair`
  variant at all**: `Term::Pair`/`Val::Pair` both view as `TmView::Opaque`
  (`conv/dom.rs` ~1294, `conv/dom/values.rs` ~809) and the Σ-η arm
  (`conv.rs` ~1586) does the work at the *ambient* type — every `fst_ty`/`snd_ty`
  in `conv.rs`/`dom.rs`/`values.rs` comes from a `TyView::Sigma`, never from a
  `Val::Pair`. `TmView::Inl { val } / Inr { val }` carry only the injected value
  (`conv.rs` ~1659). `TmView::Fst/Snd { fst_level, snd_level, pair }` carry the
  two **levels** and the pair; the neutral arms (`conv.rs` ~2184/2204) `lev_eq`
  those two levels and then take the Σ from `tm_nee_c(p1,p2)` — the comment there
  already says the stored annotations are never related. So §2.4's conversion
  paragraph stands, with one qualification the design missed: the stored
  **levels** are compared. See item 3 for what that costs.

  **2. `tm_pair`'s telescope types `u_a` by `U_S` — confirmed** (`rec.rs`
  ~1705–1800). `locals` = `(x_S, x_T, x_a, x_b)` where `x_a = inst_tm_motive(…,
  gty(3, g_ctx(4)), …)` — global 3 is `U_S` — and `x_b`'s type is
  `Type::GlobalTy { var: 1, subst: id.extended(gtm(0)) }` = `U_T[u_a/x]`. A
  branch handed one `U_Σ` could not state either. §2.2's argument is exact.

  **4. `Tc::whnf` is δ-transparent unconditionally — confirmed**, `typing.rs`
  ~882, with the rationale already in its doc comment ("a *type* lives at
  `typeof(i)`, which is always a computing layer"). The premise `T ⇝* former`
  is safe inside a boxed type.

  **3. §3.5 decided: no new value variants, and no new `TmView` variants
  either.** The grep (`Val::Pair|Val::Inl|Val::Inr|Elim::Fst|Elim::Snd` across
  `crates/kernel/src`) returns 80 sites. Every *destructuring reader* of the
  annotation slots is a re-builder, not a reader of a pair's annotation:
  `value/shift.rs` ~217/605 (shifting, structural), `eval/bits.rs` ~69,
  `eval/runs.rs` ~187, `eval/transduce.rs` ~855 all read `fst_ty`/`snd_ty` off a
  **`VTy::Sigma`** to construct an `Elim::Fst`. The readers of a `Val::Pair`
  itself (`eval/bits.rs` 194/220/228/381, `eval/probe.rs` 125,
  `eval/transduce.rs` 221/823/995/1471, `eval.rs` 1702/1707) take `fst`/`snd`
  only; the readers of `Val::Inl`/`Inr` (`eval/bits.rs` 176, `eval.rs` 1712/1717,
  `transduce.rs` 984/2101) take `val` only. The readback devices do not appear.

  So neither option (a) nor (b) of §3.5: **the evaluator maps the five `@`
  forms onto the five existing value forms.** `eval(PairAt { ty, fst, snd })`
  forces `eval_ty(ty)` to its `VTy::Sigma` view and builds the existing
  `Val::Pair` from that view's levels and component closures; `InlAt`/`InrAt`
  likewise through `VTy::Sum`; `FstAt`/`SndAt` push the existing
  `Elim::Fst`/`Elim::Snd`. Consequences: `value.rs`, `value/shift.rs`,
  `eval/bits.rs`, `eval/transduce.rs`, `eval/runs.rs`, `eval/probe.rs` and
  `conv/dom/values.rs` are **untouched**; the native fast paths keep firing; and
  `pair@(T;a;b)` is convertible with `pair(x:S.U;a;b)` by construction rather
  than by a new arm. The one whnf of `T` this costs is the head-exposure the
  design already pays for at the typing rule, memoized on the glued neutral.

  Corollary for the **syntax** side (`Syn`, the oracle, and `reduce.rs`):
  `Term::PairAt` views as `TmView::Opaque` exactly as `Term::Pair` does;
  `InlAt`/`InrAt` as `TmView::Inl`/`Inr`; and `FstAt`/`SndAt` as
  `TmView::Fst`/`Snd` — which is where item 1's qualification bites, because an
  `@` projection has **no stored levels**. `Dom::view_tm` is documented total
  ("views inspect a form that is already whnf and reduce nothing"), so it may
  not whnf `T` to find them. Decision: `TmView::Fst`/`Snd`'s two level fields
  become `Option<&Level>` (`None` for the `@` spelling), and the two neutral
  arms skip `lev_eq` when either side is `None`, falling through to the
  inferred Σ they already use for the result. This is the *only* edit to a
  `conv.rs` arm in stage 1a, it is a weakening of a check the arm's own comment
  calls redundant on well-typed inputs, and it is what makes `fst@(T;p)`
  convertible with `fst(x:S.U;p)` — which §2.4's translation requires.

  **5. `Dom` needs no new operation, but three structural obstacles the design
  does not name.** The operations typing wants are all present: `whnf_ty_root`
  + `view_ty` (the nine `self.whnf` sites at `typing.rs` 1183/1192/1202/1218/
  1233/1245/2159/2186/2221 match `CodeTy`, `CodeTm`, `Pi`, `UPi`, `CtxPi`,
  `TyPi` — all six are `TyView` variants), `inst_ty`/`inst_tm` for the 29
  `apply_local`s, `weaken_ty`/`weaken_tm` for the 21 `shift_local`s,
  `push_entry`, `var_type`, `embed_ty`, and the former constructors. §3.2's
  "nothing structural" is right about the *operations*. What it is missing:

    (a) `trait Dom` is `pub(super)` inside `crate::conv` (`conv/dom.rs` ~334)
        and `TyView`/`TmView` are `pub(super)` with `pub(super)` methods.
        `crate::typing` cannot see any of it; the visibility must widen to
        `pub(crate)`. Mechanical, but it moves the boundary out of `conv`.
    (b) **Every `Dom` method takes `cv: &mut Conv<'v, Self>` as its receiver.**
        `Tc<D>` cannot call `Dom` without holding a `Conv<'v, D>`, so the
        migration is `Tc` *owning* a conversion checker for the gate call's
        duration, not `Tc` and `Conv` side by side.
    (c) `Env<'v>` is conversion's (arena, ρ, vtys, vbase, ψ, γ, layer, cache)
        and `typing::Env` is typing's (ψ, γ, layer, univs, cache); they must
        become one type. Coupled to §3.6: `conv_type_cached` (`conv.rs` ~209)
        builds `ValueArena::new()` **per query** and `Env::new_with(&arena, …)`
        borrows it, so `Tc<'v, D>` acquires the arena's lifetime and the arena
        must be created once per gate call. That is the §3.6 change and the
        `Env` merge is how it is spelled; they are one edit, not two.

  None of (a)–(c) contradicts the design; they are the shape of stage 1b and
  are recorded so the estimate is honest. No operation is missing from `Dom`.

  **6. Before-side binary recorded.** Worktree clean at 5cf63f2;
  `cargo build --release -p heather-cli` is a no-op against the shared
  `target/` (`Finished in 0.02s`), so the release `heather` on this tree is
  5cf63f2's. Per `before-after-binary-provenance` the stage-2 comparison will
  go through `scripts/perf ab --source-patch`/`--patch` rather than a
  hand-rolled pair; stage 1's gate is "not regressed", which needs the before
  seconds and peak RSS only. Corpus copied into this worktree's `probes/`
  (untracked in the main checkout, so copied rather than referenced):
  `t_qt2.hthr`, `t_qt1.hthr`, `t_cp9.hthr`, `t_qt3.hthr`, `t_qt5.hthr`,
  `str/p10.hthr`.
- 2026-09-20: Implementer, **stage 0 + stage 1a**. Stage 1a is in and green on its own
  targets; the full `scripts/test` and `scripts/bench --check` are the gate and
  are reported in the next entry.

  ### Stage 0 — instrument and bar

  - **`intro_at_nodes`** (`crates/kernel/src/stats.rs`, +12): one bump per
    checked-spelling typing rule fired. Zero on the current tree by
    construction, so it is the `scripts/perf ab --marker` column §8 asks for.
    It rides `Snapshot::NAMES`, so `--timings` gains the column with no other
    edit.
  - **Corpus** copied from the main checkout's untracked `probes/` into this
    worktree's `probes/` and *tracked* (`.gitignore` does not cover it — the
    coordinator should decide whether it wants these six files in the tree or
    in `.gitignore`): `t_qt2.hthr`, `t_qt1.hthr`, `t_cp9.hthr`, `t_qt3.hthr`,
    `t_qt5.hthr`, `str/p10.hthr`.
  - **Before side**: worktree clean at 5cf63f2, `target/release/heather` is
    5cf63f2's (the build was a no-op). Stage 2's comparison goes through
    `scripts/perf ab`, per `before-after-binary-provenance`.
  - Disk: 125 GiB free on `/home`, so `CARGO_TARGET_DIR` is left alone.

  ### Stage 1a — the five forms

  `Term::{PairAt, InlAt, InrAt, FstAt, SndAt}`, each `{ ty, …}` with **one**
  annotation and **no binder in it**. Files, with the substance rather than the
  line counts where they differ:

  | file | + | what |
  |---|---:|---|
  | `term.rs` | 59 | the five variants and the design's rationale in their doc comments |
  | `subst.rs` | 22 | the walker; every site loses the `dep(0,0,1)` its component sibling needs |
  | `bounds.rs` | 9 | free-local bounds, `under(1)` likewise gone |
  | `fmt.rs` | 10 | budget-bounded `Debug`, printing `pair@(T; a; b)` |
  | `reduce.rs` | 48 | β, neutrality, whnf grammar |
  | `eval.rs` | 95 | evaluation, and `Eval::ty_to_former` |
  | `conv.rs` + `conv/dom.rs` + `conv/dom/values.rs` | 62 | the views; see below |
  | `typing.rs` | 94 | the five rules on syntax, and `Tc::computing_layer` |
  | `merkle.rs` | 32 | five tags, `0x76`–`0x7a` |
  | `elab/module_image.rs` | 15 | five image tags, `54`–`58` |
  | `elab/emission_walk.rs` | 25 | five slots, each `ty @ d` |
  | `elab/rbcount.rs`, `rbname.rs` | 32 | kept compiling; superseded and deleted in stage 2 |

  **`rec.rs`: zero lines.** The layer guard held.

  **Three deviations from the design, all simplifications, all consequences of
  §9.0's answers:**

  1. **No new value forms and no new `TmView` variants** (§3.5, decided by
     §9.0 item 3's grep). The evaluator exposes the annotation's head former
     and builds the *existing* `Val::Pair` / `Val::Inl` / `Val::Inr` /
     `Elim::Fst` / `Elim::Snd` from that former's component closures. So
     `value.rs`, `value/shift.rs`, `eval/bits.rs`, `eval/transduce.rs`,
     `eval/runs.rs`, `eval/probe.rs` and `conv/dom/values.rs`'s `view_tm` are
     **untouched**; the native bitvector and transducer fast paths keep firing
     on a `pair@`-built value without knowing the spelling exists; and
     `pair@(T;a;b)` is *the same value* as `pair(x:S.U;a;b)`, so the two
     convert with no new arm. The new helper is `Eval::ty_to_former`, the
     evaluator-side `delta_to_head_ty`. An annotation whose head is not the
     expected former is ill-typed and eval returns `OutOfFuel` — its only
     failure, and "no answer" rather than a verdict; the rejection belongs to
     the typing rule, which reports `HeadMismatch`.

  2. **One `conv.rs` arm did change, and §2.4's conversion paragraph needs a
     sentence.** `TmView::Fst`/`Snd` carried `fst_level`/`snd_level`, and the
     neutral projection arms `lev_eq` them before taking the real Σ from the
     head's inferred type. A checked projection stores no levels, and
     `Dom::view_tm` is documented **total** ("inspect a form that is already
     whnf and reduce nothing"), so it may not whnf `T` to find them. The two
     fields became `levels: Option<(&Level, &Level)>`, `None` for the `@`
     spelling, and the arms skip the `lev_eq` when either side is `None`. This
     is a weakening of a check the arm's own comment calls redundant on
     well-typed inputs — and it is *required*, not merely tolerated: without it
     `fst@(T;p)` would not convert with `fst(x:S.U;p)`, which `⌊·⌋` demands.
     §3.4's "conv.rs untouched in its arms" is therefore not quite true and the
     doc should say so.

  3. **`reduce.rs` gets no layer guard.** The design (§3.4) asked for "the same
     layer guard" there. `reduce.rs`'s `step_*` take no layer — reduction is
     untyped, and every other layer restriction in the kernel lives in
     `typing.rs` (`not_var_layer`) and nowhere else. The guard is
     `Tc::computing_layer`, which is `layer.computes()` and therefore *stronger*
     than `not_var_layer`: layer **c** refuses these forms and admits the
     component ones, which is the asymmetry §2.3 is about. The golden test
     pins both directions.

  Two smaller notes: the projection's step arm does **not** step its annotation
  (there is no β to find inside `T`, and a projection on a neutral pair is
  neutral whatever shape `T` is in — exposing `T`'s former is the typing rule's
  business), which keeps `is_neutral_term` honest; and the **image version bump**
  §4.2 asks for happens by construction, because `SemanticsIdentity` is derived
  from the kernel's sources by `crates/cache/build.rs` and `term.rs` changed.
  Merkle takes five *distinct* tags rather than folding onto the component ones:
  a Merkle hash names syntax, and two spellings that convert are still two terms.

  ### Tests

  - **`wt.rs` +103**: generators for all five, plus `gen_at_sigma`. They
    generate the annotation as **`El ⌜Σ(x:El A). El B⌝`**, not as the former —
    so the premise `T ⇝* former` is exercised in its *non-reflexive* case, and
    `fst@`'s pair is generated at the decoded Σ so checking it against `T` is a
    real `Sigma`-against-`El⌜Sigma⌝` query: the head pair the issue's
    2026-09-18 trace found at 96 % of a record tower's misses. A literal former
    as the annotation would make every `@` form a rename of its sibling.
    Dispatch widened from `r.below(27)` to `r.below(32)`, guarded on
    `env.layer.computes()` (`gen_letbox_tm` generates under `Layer::Code`).
    **Every existing seed stream therefore sees a different schedule**, which is
    the point of `ch05_06_lemmas`'s "several independent streams" argument, and
    all of them stayed green.
  - **`ch05_06_lemmas.rs` +16**: a coverage assertion on `intro_at_nodes` in
    `the_generator_oracle_holds_across_seed_streams` — a generator that stops
    producing the spellings makes every property test in the crate silently
    vacuous on them. Measured: **3 160 checked spellings met by the checker
    across 3 200 cases.**
  - **`eval_differential.rs` +71**: the `⊩` arms. The three streams failed
    first (`term head constructor`, seeds 0 / 5 / 13) and the failure was the
    *harness's* adequacy relation, not the kernel: `⊩` relates a value to the
    whnf of the term's **translation**, so the harness now reduces `T` and
    relates the value's annotation closures to *its* components. That is the
    statement of §2.4 for these arms, not a weakening of it. Green after.
  - **`typing.rs` +134**: `checked_spellings_infer_their_annotation`, over
    `El ⌜Σ(A : Ty 0). El A⌝` — inference returns the annotation un-reduced,
    `fst@`/`snd@` infer the components of its whnf, `snd@`'s substituted
    projection is the `@` spelling again, both spellings check against each
    other's type in both directions, a non-Σ annotation is `HeadMismatch`, and
    layers **v and c** refuse all five while c admits the component form.
  - **`reduce.rs` +67**: β on all four spelling combinations (`fst` over
    `pair@`, `fst@` over `pair`, …), with *deliberately wrong* annotations
    (`Empty` where a Σ belongs) to pin "reads nothing from the annotations";
    plus the whnf/neutrality lines.

  Green on the targets that could break: `ch05_06_lemmas` 12, `conv` 35,
  `conv_differential` 7, `eval_differential` 10, `reduce` 53, `typing` 33,
  `subst_laws`, `heather-cache` 9 + 17, `heather-cli` `check` 28.
- 2026-09-20: Implementer, **correction to the §9.0 item-5 entry above, and stage 1b's real
  shape**. The earlier entry concluded "no operation is missing from `Dom`"; that
  was checked against the nine `self.whnf` sites and the 29 `apply_local`s — the
  *checking* side — and it is **wrong about the inference side**. §3.2's "What
  `Dom` lacks that typing needs, and must gain: nothing structural" does not
  hold, and per §9.0 item 5 this is the log entry it asked for.

  `tm_infer_inner` **constructs** 18 distinct type formers as synthesized types:

      El 6  Id 3  SEq 2  Squash 4  SEmpty 1  Sigma 6  Sum 4  Unit 1
      Empty 1  W 3  Pi 5  Wf 2  Vec 1  UPi 2  CtxPi 2  TyPi 2  CodeTy 2  CodeTm 2

  `Dom` has constructors for twelve of them (`nat`, `univ`, `empty`, `sempty`,
  `squash`, `code_ty`, `code_tm`, `el`, `pi`, `sum`, `w`, `wf`, `vec`, `id`).
  It has **none** for the six conversion never has to synthesize because it only
  ever *views* them:

      sigma   seq   unit   upi   ctx_pi   ty_pi

  So stage 1b adds **six `Dom` methods, twelve implementations**. Each is one
  `VTy` constructor on the `Values` side and one `Type` constructor on `Syn`'s,
  so they are mechanical in the way the trait's existing formers are — but
  "nothing structural" is not the right sentence and §3.2 should be corrected to
  "six synthesized formers, mechanical, because conversion views these and never
  builds them".

  Three further obstacles, already logged above and restated because together
  they are the estimate: (a) `Dom`, `TyView`, `TmView`, `Conv` and `Env` are all
  `pub(super)` inside `crate::conv` and must widen to `pub(crate)`; (b) every
  `Dom` method takes `&mut Conv<'v, Self>`, so `Tc` must *hold* a conversion
  checker rather than sit beside one; (c) `conv::Env<'v>` and `typing::Env` must
  become one type — which is better news than it looked: conv's `Env` is a strict
  superset of typing's except for **one** field (`univs: u32`), so the merge is
  "add `univs` to `conv::Env` and delete `typing::Env`", and it carries the §3.6
  arena change with it because `Env::new_with(&arena, …)` is what borrows the
  arena and `conv_type_cached` (`conv.rs` ~209) currently calls `ValueArena::new()`
  **per query**.

  Scope, stated plainly for the coordinator rather than discovered halfway: 1b is
  six new trait methods, an `Env` merge across two trusted files, a visibility
  widening of the `Dom` boundary out of `conv`, an arm-by-arm rewrite of
  `tm_infer_inner` (1 150 lines, 39 arms) plus `tm_check_inner` and `rec_ga`,
  a `typing::oracle` module, and `tests/typing_differential.rs`. That is the
  1.5-definitions-round core the design sizes it at, and its failure mode is
  soundness rather than a mismatch. This entry is the point at which the round's
  remaining budget is the coordinator's call and not the implementer's.
- 2026-09-20: Implementer, **stage 1b: STOPPED before the first line, on a design gap, not on
  a disagreement.** Stage 1a stays (it is correct, tested, and inert without an
  emitter). What follows is the thing the coordinator has to decide.

  **The design does not say what `Tc::conv_ty`'s two shortcuts become.** §3.2
  prices exactly one thing about the seam — "compares two `D::Ty` in one arena
  instead of re-entering the value domain from syntax per query with a fresh
  arena" — and the arena is real. But `Tc::conv_ty` (`typing.rs` ~758) does not
  reach `Conv` on most queries at all. Ahead of it sit two devices, **both keyed
  on `Type` syntax**, and neither has a counterpart at `D::TyC`:

  1. **The syntactic reflexivity shortcut**, `expected == inferred` — plain
     α-equality under de Bruijn, at zero arena and one fuel unit. This is the
     `conv_shortcut_hits` column, and per `CLAUDE.md` it is most of what
     `queries` counts ("shortcut hits = term size"). At `Values` the
     corresponding operation is `Dom::ty_eq_fast` (`conv/dom/values.rs` ~1266),
     which requires `home`/`sat` to agree **and** either the same closure pointer
     or the *same environment pointer* with α-equal bodies. And `conv.rs`'s own
     comment on `ty_root` says what the seam hands it: "the typing seam's
     expected-vs-inferred query overwhelmingly hands this function two
     **separately built** copies of one type". Separately built means different
     environments, which `ty_eq_fast` rejects. So the migration plausibly trades
     a syntactic test that fires on α-equality for a scoped-identity test that
     fires on provenance, on the hottest path in the gate, and the design has no
     sentence about it.

  2. **The cross-head memo** (`ConvMemoBucket` / `ConvMemo`, ~772–880): bucketed
     on `discriminant(expected)`, `type_anchor(expected)` and matched by
     `entry.expected == *expected`, i.e. structural `Type` equality against a
     stored `Type`. On closures there is nothing to store and nothing to compare
     — two closures over the same syntax in two environments are distinct
     pointers. `docs/conversion-query-arena-pooling-design.md` §3 is cited in
     §3.2 for the arena; this memo is a separate measured device with its own
     rationale in the code, and it is also the round's own instrument.

  A third, smaller: keeping `expected` as syntax and letting only `inferred`
  become a domain object is the obvious dodge and it is **the hybrid §6 item 6
  refuses**, one level down — `Conv` enters from syntax roots
  (`Dom::whnf_ty_root`) or compares domain objects, and a mixed judgment is a new
  entry point into the trusted comparison.

  **Why this is a stop rather than a deviation to log and push through.** §9.0's
  instruction is to log a contradiction and adjust the plan, not to deviate
  silently; but this one is not a local adjustment. It decides what the gate's
  hottest path *is*, it is the thing `scripts/bench --check` and the round's own
  counters would measure, and getting it wrong is not a failed test — it is a
  correct checker that is slower than the one it replaced, discovered after a
  2 770-line trusted file has been rewritten. The design's stage-1 gate already
  says "expect movement: the per-query arena is gone"; the arena is not the only
  thing that moves, and the round should know which direction before it starts.

  Two further corrections to §3.2, both above in this log: six `Dom` methods are
  missing (`sigma`, `seq`, `unit`, `upi`, `ctx_pi`, `ty_pi`), and the `Dom`
  boundary is `pub(super)` inside `crate::conv` with every method receiving
  `&mut Conv<'v, Self>`, so `Tc` must own a conversion checker and `conv::Env`
  must absorb `typing::Env`'s one extra field (`univs`).

  **What the coordinator has to decide, in the order it matters:**

  1. What `Tc::conv_ty`'s reflexivity shortcut becomes. Candidates, unpriced:
     keep a syntactic pre-test by having `tm_check` carry the *syntax* of an
     expected type alongside its domain object (cheap, but it is the hybrid in
     another guise); strengthen `ty_eq_fast` to compare `TyClo::Syn` bodies by
     `==` across *different* environments when both are closed in the relevant
     prefix; or accept the loss and measure it. A **fresh before-table on the
     current tree** (`fresh-before-table-in-briefs`) of the shortcut/memo/miss
     split per corpus file would settle it before a line is written.
  2. Whether the cross-head memo survives, moves, or is deleted with a recorded
     verdict.
  3. Whether 1b is still one round after (1)–(2), six new `Dom` methods, the
     `Env` merge and the visibility widening — or two.

  Stage 1a's gate follows in the next entry.
- 2026-09-20: Implementer, **stage 1a's gate**. Green, with one honest gap: the bench is
  **no result on this box**, and the reason is recorded rather than papered over.

  **Full `scripts/test`:** `== suite: 2827 passed, 0 failed, 5 ignored ==`,
  including the `calc_text` showcase gate. (A second full run followed two later
  edits — a `ty_infer`-before-`whnf` ordering fix in all five rules, and a
  strengthened negative control in the golden test — and is reported in the
  implementer's handover.)

  **`scripts/bench --check`: no result.** Not "regressed", not "clean" — the
  measurement did not happen, and here is why, because the raw output says
  "27 regression(s)" and a reader could be forgiven for believing it.

  1. The **committed baseline is stale against this tree**: `conv/vec-literal:*`
     comes back `untracked — no baseline entry`, and `nat/check-numeral` shows a
     *5× improvement* on a change that cannot reach it. Per
     `furnace-bench-check-needs-save` / `desktop-bench-gate-for-constants` the
     first move is a control, so: `git stash` → `scripts/bench --save` on the
     clean tree → `stash pop` → `--check`.
  2. Against that fresh control, **27 regressions became 8**, and the 8 were
     confined to `conv/perturbed-pairs:*` and `check/generated-terms:*` — the
     two families whose fixtures are built from `gen_wt_term`, which this round
     changed. Everything else was clean.
  3. But repeating the *same* comparison minutes later gave **30**, this time
     including `level/equiv-shared:4` at **5 ns → 7 ns (1.37×)** — a
     pure-arithmetic microbenchmark nothing in this round touches — and a
     uniform 1.25–1.5× across `subst/`, `nat/`, `code/` and `wf/`. Load average
     was 9.3 → 12.8 (a desktop with browsers, an Electron app and Steam). This
     is `before-after-binary-provenance`'s invented regression, verbatim.

  So: the noise floor on this box is ≳1.5×, and the only movements above it are
  the two `gen_wt_term` families. I did **not** `--save`; the committed baseline
  is restored (`git checkout crates/kernel/benches/baseline.tsv`) rather than
  overwritten with a reading taken on a loaded machine.

  **Those two families moved for a reason worth reading, and it is a decision
  for the coordinator.** `conv/perturbed-pairs` is 4.5–13.5× and reproduces at
  that magnitude in every generator-on run while **vanishing entirely** when the
  dispatch is put back to `r.below(27)` — a clean attribution to the fixture, not
  to the checker. The cause is a deliberate choice in the generator: the checked
  spellings' annotation is `El ⌜Σ⌝`, so every `fst@` in a generated term costs
  conversion a `Sigma`-against-`El⌜Sigma⌝` query — the head pair the issue's
  2026-09-18 trace put at 96 % of a record tower's misses. That is the *right*
  fixture for the differential tests and a *much harder* one for a benchmark
  whose baseline is a gate. Two readings of the same fact:

  - it is the first direct measurement that **the checked spellings are
    expensive under the syntax checker**, which is the case for stage 1b; and
  - a `check/generated-terms` slope of 1.04 → 2.5–2.7 is a materially worse
    gate, and a slope that moves because the fixture changed will bury the next
    real regression.

  The coordinator decides between re-saving with the verdict recorded, and
  isolating the fixture (e.g. the `@` arms generate a literal former as the
  annotation half the time, keeping the non-reflexive premise covered at half
  the difficulty shift — it will not remove the 13.5×). This should be settled
  on a quiet box, not this one.

  **The gate's real question — "not regressed" — is answered by the counters,
  which are exact and load-invariant** (`CLAUDE.md`: counters are exact on one
  tree). Two release binaries built from the same worktree (stash / stash-pop),
  distinct by `cmp`, run over `--timings`:

  | file | misses Δ | queries Δ | steps Δ | peak RSS before → after |
  |---|---|---|---|---|
  | `lib/ir_v1.hthr` (18 items) | **+0.0 %** | **+0.0 %** | **+0.0 %** | — |
  | `probes/t_cp9.hthr` | **+0.0 %** | **+0.0 %** | **+0.0 %** | 2 234 → 2 244 MB (+0.4 %) |
  | `probes/t_qt3.hthr` | **+0.0 %** | **+0.0 %** | **+0.0 %** | 4 003 → 4 058 MB (+1.4 %) |
  | `probes/str/p10.hthr` | **+0.0 %** | **+0.0 %** | **+0.0 %** | 5 709 → 5 842 MB (+2.3 %) |

  Every counter on every item is identical — `complete_post` at 3 699 898
  queries / 14 210 misses / 247 834 steps on both sides, `p10::char_run` at
  42 887 503 / 1 527 745 / 6 177 673 on both. **Stage 1a is behaviourally inert
  on the production path**, which is exactly what a stage whose forms nothing
  emits should be, and it is the strongest statement available that the
  `TmView::Fst`/`Snd` `Option`-levels edit changed no verdict. The seconds
  columns on the same runs swing −52 % to +42 % **in both directions on items
  neither binary treats differently** (`omega::cutsat_right_cut` −52 % on one
  file and −3.9 % on another), which is the same noise the bench saw. The RSS
  drift is small, one-signed and unattributed; nothing on the production path
  allocates differently, `size_of::<Val>()`'s assertion is untouched (there are
  no new value forms), and the new `Term` variants are smaller than the ones
  they spell — so this is the measurement's own spread, and stage 2 is where it
  should be re-read on a quiet box.

  **x86 certificate gates:** green inside the full suite (they are
  `crates/cli/tests/native*.rs`, which the full lane runs).
- 2026-09-20: Implementer, handover. The **final full `scripts/test` on the tree as it
  stands** — after the `ty_infer`-before-`whnf` ordering fix in all five rules
  (whnf is untyped and must not be handed an annotation nothing has checked) and
  the strengthened `inl@`/`inr@` negative control in the golden test (the
  summands were both `Nat`, so a spelling swap was invisible; they are now
  `Nat + Unit 0` and the wrong summand's inhabitant must be refused) — is

      == suite: 2827 passed, 0 failed, 5 ignored ==

  not INCOMPLETE, and the same count as the first full run.

  Nothing is committed. `crates/kernel/benches/baseline.tsv` is restored to the
  committed version (`git checkout`), so the bench control run left no trace.
  `probes/` is **untracked and not covered by `.gitignore`** — the coordinator
  should decide whether the six corpus files belong in the tree or in the ignore
  list before committing.
- 2026-09-20: Implementer, **stage 1b step 1 — the bench fixture is isolated, and the 4.5–13.5× is gone.**
  Standalone, before any `typing.rs` line moves.

  **The change.** `WtEnv` gains one field, `at_forms: bool`, **off by default**; the
  arm dispatch reads its modulus off it (`r.below(if env.at_forms { 32 } else { 27 })`)
  and the five `@` arms gain `env.at_forms &&` in their guards. `gen_wt_env` sets it
  false; the new `gen_wt_env_at` sets it true and is what the differential and lemma
  tests import (`use common::wt::{gen_wt_env_at as gen_wt_env, …}` — one line per file
  in `conv_differential.rs`, `eval_differential.rs`, `ch05_06_lemmas.rs`).
  `tests/typing.rs`'s golden coverage does not use `wt.rs` at all — it is hand-written
  syntax — so it needed nothing. The benches (`conv/perturbed-pairs`,
  `check/generated-terms`, both via `gen_wt_env`) are back on the old workload.
  wt.rs +31/−3; three test files +1/−1 each.

  **Off is byte-identical to the pre-`@` generator, by construction and not by
  measurement.** `Rng::below` draws exactly one word whatever the bound
  (`tests/common/mod.rs` ~59), so modulus 27 makes arms 27–31 unreachable *and*
  leaves the draw schedule untouched. `diff` of `git show 5cf63f2:…/wt.rs` against
  the current file removes exactly three lines — the two `WtEnv` literals and
  `match r.below(27)` — each replaced by an `at_forms`-carrying or
  `at_forms`-conditioned equivalent. Every other hunk is additive.

  **Measurement, on a quiet box** (load average 0.56 / 2.03 at launch; the stage-1a
  entry's readings were taken at 9.3–12.8 and are the reason this was re-done).
  Control: `scripts/bench --save` on HEAD *with* this change — the committed baseline
  is stale against this tree and is not a control (it has **no** `conv/vec-literal`
  rows at all, which is where the previous entry's "untracked — no baseline entry"
  came from). Then `scripts/bench --check` against it:

      ok: 112 comparisons within thresholds

  with the two families that had moved reading

  | fixture | slope now | slope with `@` on (stage 1a) | slope before `@` existed |
  |---|---:|---:|---:|
  | `check/generated-terms` | **1.04** | 2.5–2.7 | 1.04 |
  | `conv/perturbed-pairs` | **0.99** (2.90–2.98 µs/pair, flat) | 4.5–13.5× on time | — |

  So the fixture change is fully reverted and the gate is a gate again. The
  substance the `@` fixture was measuring — that a checked spelling whose
  annotation is `El ⌜Σ⌝` is expensive **under the syntax checker** — is not lost:
  it is exactly what `typing_differential` will exercise, and it is the case for
  stage 1b rather than a bench row.

  **State of `crates/kernel/benches/baseline.tsv`:** overwritten with the fresh
  control (the committed copy is preserved in the session scratch dir). It is the
  control the stage-1 gate's `--check` will run against. Whether it is committed is
  the coordinator's call; if not, `git checkout crates/kernel/benches/baseline.tsv`
  restores the committed one and the gate's reading below stands on its own.

  `scripts/test --fast` on the tree at this point: `== suite: 2687 passed, 0 failed, 5 ignored ==`.
- 2026-09-20: Implementer, **stage 1b step 0 (the no-op refactor) — landed and measured**, and then
  **stage 1b STOPPED again, on a second structural gap**: three of the six missing
  `Dom` constructors cannot be written at `Values` at all. Details below, in the
  order the coordinator needs them: what landed, what it costs, and what is blocked.

  ---

  ### What landed (step 0)

  **(a) The `Dom` boundary is out of `conv`.** `pub(super)` → `pub(crate)`
  throughout `conv/dom.rs` (9 items: `Dom`, `TyView`, `TmView`, `Values`, `Syn`
  and their inherent methods), `mod values` → `pub(crate) mod values`, and
  `conv::{Env, Conv, TyEnv, TyEnvNode}` made `pub(crate)`. Mechanical; no method
  body changed.

  **(b) `conv::Env` absorbed `typing::Env`.** Exactly as the earlier entry
  predicted: conv's is a strict superset but for `univs`, so the merge is "add
  `univs` (and, under the feature, `value_metrics`) to `conv::Env` and delete
  `typing::Env`". New: `Env::for_typing` (the checker's constructor — arena, Ψ,
  Γ, layer, `|L|`, cache, metrics) and `Env::push_spec_syn` (`Dom::push_spec`
  without the domain parameter, because the checker has `rec::Tele`'s syntax and
  never a domain object for it). `typing.rs`'s 30-odd `push_entry` calls became
  `push_entry_syn`, which was already there for conversion's own
  syntax-carrying pushes. `ConvMemo::psi` became `Rc<GlobalCtx>` — identity is
  preserved either way (`GlobalBindings` derives `Clone` over an `Rc<()>` token),
  so this is strictly cheaper and changes no verdict.

  **(c) §3.7's arena moved to the gate call.** Each public entry
  (`check_term`, `check_type`, `infer_term`, `infer_type`, `check_local_subst`,
  `check_local_ctx`, the two `_profiled` twins, and one per binding inside
  `check_global_ctx_extension`) now builds a `ValueArena` and hands it to
  `Env::for_typing`. `Tc::conv_ty` still calls `conv_type_cached`, which still
  builds its **own** arena per query — deliberately, so that step 0 is a no-op
  in verdicts *and* in counters and the arena's new lifetime can be priced on
  its own before anything depends on it.

  **(d) Three of the six missing constructors.** `unit`, `sigma`, `seq` at both
  `Syn` and `Values` — genuinely mechanical, one `Type` constructor and one
  `VTy` constructor each, `sigma` mirroring `pi` and `seq` mirroring `id`. They
  are `#[allow(dead_code)]` until `typing.rs` is `Tc<D>`.

  `conv.rs` +71/−14, `conv/dom.rs` +73/−11, `conv/dom/values.rs` +41,
  `typing.rs` +52/−118.

  ### The gate on step 0

  `scripts/test --fast`: **`== suite: 2687 passed, 0 failed, 5 ignored ==`**,
  the same count as before the change. Full `scripts/test` is running and is
  reported in the handover.

  **Counters: inert, to the unit.** Two release binaries from this worktree
  (`git stash` / `stash pop`), distinct by `cmp` (byte 25), over `--timings`,
  read with `scripts/timings --diff`:

  | file | items | queries Δ | misses Δ | steps Δ | shortcut Δ | memo Δ |
  |---|---:|---|---|---|---|---|
  | `lib/ir_v1.hthr` | 374 rows | **+0.0 %** | **+0.0 %** | **+0.0 %** | **+0.0 %** | **+0.0 %** |
  | `probes/t_cp9.hthr` | all rows | **+0.0 %** | **+0.0 %** | **+0.0 %** | **+0.0 %** | **+0.0 %** |

  Not one row of either file has a non-zero count delta. So the `Env` merge,
  the visibility widening and the `Rc<GlobalCtx>` memo key change no verdict and
  no shortcut/memo/miss outcome — which is what a step-0 refactor owes.

  ### **The cost, which is the finding: §3.7's arena is expensive, and this is only its lower bound**

  Peak RSS, same two binaries, same runs:

  | file | before | after | |
  |---|---:|---:|---|
  | `lib/ir_v1.hthr` | 631 MB | 637 MB | +1 % |
  | `probes/t_cp9.hthr` | 2 201 MB | 3 315 MB | **+51 %** |
  | `probes/str/p10.hthr` | 5 733 MB | 15 076 MB | **×2.63** |

  `p10` needed the cap raised to 16 GiB to finish at all; at the 8 GiB the
  `OOM-safe testing` rule uses it would have died. The attribution is exact and
  there is nothing else it could be: the only allocation the change moves is
  `Env::push_entry_syn`'s — one `TyClo`, one `Val::var` and one environment cell
  per binder push. In the before binary those live in conversion's per-query
  arena and are freed when the query ends; in the after binary they live in the
  checker's arena and are freed when the **declaration** ends. The growth tracks
  check volume exactly (ir_v1 ≈ 0, t_cp9 +1.1 GB, p10 +9.3 GB).

  And this is the *cheap* half. At step 0 conversion still frees its own arena
  per query. Stage 1b proper makes conversion allocate into the checker's arena
  too — every closure of every one of `p10::char_run`'s 42 887 503 queries
  retained for the declaration instead of for the query. §3.7 says "the
  address-space rail is the measurement of whether that retention is
  acceptable"; on the routine corpus, measured, **the answer at `p10` is no**,
  and `docs/conversion-query-arena-pooling-design.md` §3's per-query arena is
  not only a structural cost but also the thing keeping the corpus inside its
  rail. This should be settled before a line of stage 1b is written, the same
  way §3.6 was.

  ---

  ### **The stop: `upi`, `ctx_pi` and `ty_pi` have no implementation at `Values`**

  The earlier entry said the six missing constructors are "mechanical, because
  conversion views these and never builds them — each is one `VTy` constructor
  on the `Values` side". That is true of `sigma`, `seq` and `unit`, which are
  landed above. It is **false** of the other three, and the reason is structural,
  not an oversight in the transcription.

  **The shape of the three arms.** `tm_infer_inner`'s `ULam` / `CtxLam` / `TyLam`
  each push a telescope, infer the body there, and wrap:

      let e = env.push_univs(*num_vars);
      let (ty, lt) = self.tm_infer(&e, body)?;      //  ty is scoped in `e`
      Ok((Type::UPi { num_vars, level, body: Rc::new(ty) }, Level::Omega))

  Under `Tc<D>` that `ty` is a `D::TyC` **scoped inside the pushed telescope**.

  **The shape the value language demands.** `VTy::UPi { num_vars, level, body }`
  — and `CtxPi`/`TyPi` likewise — stores the body as a closure whose *syntax* is
  written under the binders and whose *captured environment* is written
  **outside** them. `eval.rs` ~758 builds exactly that (`yclo(env, body)` /
  `under_binder_ty(arena, env, body)` over the pre-push environment), and both
  consumers depend on it:

  - `Values::inst_univ_ty` (`values.rs` ~945) requires `body.clo.as_syn()` and
    then `bbody.inst_univ(phi)` — it instantiates the **syntax**. A body with no
    syntax is `NotConvertible`, i.e. a wrong answer.
  - `inst_global_ty` (~1702) does the same for `CtxPi`/`TyPi`, with a
    `debug_assert_eq!(benv.gshift(), 0)` pinning "the outer environment is
    materialized".
  - conversion's own arms (`conv.rs` ~1040 and ~1399) take the body out of the
    view, `push_univs(n)`, and then `D::under_tele_ty(body, n, 0)` — which is
    `value::shift::reenv_ty`, *weakening the captured environment into the
    telescope*. A body that is already inside the telescope would be shifted a
    second time.

  So `Dom::upi` would have to map a closure captured **inside** the telescope to
  one captured **outside** it — the inverse of `under_tele_ty`. That inverse does
  not exist in `value/shift.rs` (`Outer` only weakens; `Level::shift`,
  `shift_univ` and `shift_global` have no lowering form), and — this is the part
  that makes it not merely missing but impossible — **it does not exist
  mathematically**. A `ΠΠℓ⃗. T` whose body value genuinely depends on ℓ⃗ through
  its captured environment has no `VTy::UPi` representation at all. The witness
  is one line:

      Λℓ. f a          -- inferred type  cod[a/x],  where the argument value `a` mentions ℓ

  At `Values` the body's inferred type is `TyClo::Syn { ρ.extend(⟦a⟧), cod }` and
  `⟦a⟧` carries ℓ. Unshifting it is undefined; leaving it and letting conversion
  `reenv` it again corrupts it *silently*, which is worse than a rejection.

  **Why this cannot be papered over.** The three arms are layer-m and
  inference-position only — narrow — but a trusted checker may not be incomplete
  on a form the rules admit, and it certainly may not be silently wrong. There is
  no readback in the kernel to fall back on (`grep -rn 'fn quote\|readback\|fn
  reify' crates/kernel/src` returns nothing), and §5 of the design refuses
  building one.

  **Candidates, unpriced, in the order I would try them:**

  1. **The three arms stay on the rewriter.** `Tc<Values>`'s `ULam`/`CtxLam`/
     `TyLam` inference calls `Tc<Syn>`'s — which is the current, trusted
     checker — and `embed_ty`s the `Rc<Type>` it returns. Correct by
     construction (the syntax checker is the reference the whole differential
     test is built on), contained to three cold arms, and needs no new kernel
     machinery. Costs: a second `Tc` inside the first, and the differential test
     becomes uninformative on exactly those three arms — which should be said out
     loud rather than discovered.
  2. **A second shape for the three value formers**: `VTy::UPi` &c. gain a
     "domain body already inside the telescope" variant, and `inst_univ_ty` /
     `inst_global_ty` gain the value-level `inst_univ` / `apply_global` that shape
     needs. Principled and complete; it is a change to the **value language**,
     which §3.5 and stage 1a were careful to leave untouched, and it touches
     every reader of those three variants.
  3. **Narrow the migration**: `tm_check`'s expected types become `D::TyC` and
     `tm_infer` keeps returning syntax except at `fst@`/`snd@`. This is §6 item
     6's hybrid and is refused there, but it is worth re-pricing now that the
     *reason* for the hybrid is three named arms rather than a general unease.

  **What the coordinator has to decide, in order:**

  1. Whether §3.7's per-gate arena survives the RSS above (`p10` ×2.63 on the
     cheap half alone), and if it does not, what `Tc<D>`'s arena discipline is —
     because the `Env` merge is how the arena's lifetime is spelled, and the two
     are one edit.
  2. Which of the three candidates above the layer-m λ-inference arms take.
  3. Whether step 0 as landed (visibility, `Env` merge, three constructors,
     per-gate arena) is kept, kept-minus-the-arena, or reverted pending (1).

  Nothing else in stage 1b was attempted: `typing.rs` is still the concrete `Tc`
  on syntax, and `Tc<Syn>`, `typing::oracle` and `tests/typing_differential.rs`
  do not exist.
- 2026-09-20: Implementer, **handover: the full suite on the step-0 tree, and one more RSS datum.**

      == suite: 2827 passed, 0 failed, 5 ignored ==

  Not INCOMPLETE, and the same count as stage 1a's gate — so the bench-fixture
  isolation, the visibility widening, the `Env` merge, the per-gate arena and the
  three new `Dom` constructors break nothing, including the x86 certificate gates
  and `showcase_gate`.

  **But `showcase_gate` is the third RSS reading and it is the one with a
  comment attached to it:**

      calc_text    ok    239.3 s wall    237.8 s cpu    12.5 GiB peak

  against the **9.8 GiB** that `scripts/test`'s `showcase_gate` comment and
  `CLAUDE.md` both quote (measured 2026-09-19). **+28 %**, from the same one
  change — `Env::push_entry_syn` now allocating into an arena whose lifetime is
  the gate call's. `scripts/showcase`'s rail is sized "from the largest this file
  has actually been checked under (14 GiB) with headroom", so it passed, but the
  headroom it was sized with is most of what this change just spent. If step 0 is
  kept, that comment, `CLAUDE.md`'s `calc_text` line and the rail's own rationale
  need re-recording; if §3.7's arena is reconsidered (the first decision on the
  previous entry's list), they do not.

  The three readings together, one change, one binary pair, `before-after-binary-provenance` observed:

  | file | before | after | |
  |---|---:|---:|---|
  | `lib/ir_v1.hthr` | 631 MB | 637 MB | +1 % |
  | `docs/showcase/calc_text.hthr` | 9.8 GiB | **12.5 GiB** | +28 % |
  | `probes/t_cp9.hthr` | 2 201 MB | 3 315 MB | +51 % |
  | `probes/str/p10.hthr` | 5 733 MB | **15 076 MB** | **×2.63** |

  Counters on `ir_v1` and `t_cp9`: not one row moved.

  **Tree state.** Nothing committed. `crates/kernel/benches/baseline.tsv` holds
  the **fresh control** this round measured against, not the committed baseline
  (`git checkout crates/kernel/benches/baseline.tsv` restores the committed one;
  the `--check` verdict above stands either way, since the control was taken on
  the same tree it gated). `probes/` is still untracked and still not covered by
  `.gitignore` — the same decision the stage-1a handover left open. `typing.rs`
  is unchanged as a checker: still the concrete `Tc` on syntax; `Tc<Syn>`,
  `typing::oracle` and `tests/typing_differential.rs` do not exist.
- 2026-09-20: Coordinator: stage 1b's two stops are both answered by one change to the design, §3 rewritten (docs/intro-by-type-design.md, 2026-09-20). The `Tc<D: Dom>` migration is **withdrawn** and step 0 reverted (step 1, the bench-fixture isolation, is kept and committed): the arena finding is decisive on its own — an arena that outlives a query is +9.3 GB at `p10` before conversion's temporaries even join it — and the `UPi`/`CtxPi`/`TyPi` gap is a second symptom of the same thing (the checker was being asked to hold *values*). What replaces it: the checker holds **descriptions** — `ITy = Syn(Rc<Type>) | Sel { of, sel, at_depth }` with `Sel ∈ {Fst, Snd(a), Lhs, Rhs, Dom, Cod}` — arena-free, linear, formed only by the five `@` rules and by views of a `Sel`; consumed by `conv_ty` (structural `==` shortcut, memo keyed on `ITy`, a miss evaluates both sides into today's per-query arena) and by `view` (rewriter for `Syn` as today; value domain for `Sel` and for the `@` annotations, returning new `Sel`s for Π/Σ/Sum components and a materialized former otherwise). The three Λ inference arms materialize a `Sel` body through the rewriter — complete, never silently wrong, exponential exactly when today is, counted. The oracle is a `materialize_eagerly` mode of the same checker, so the differential tests exactly the new thing. Per-query re-evaluation cost is stage 2's first number (`sel_evals`), and a declaration-scoped memo is a separate design if it dominates. §6 item 6's refusal was of values in the checker; descriptions are what is adopted, and the distinction is the arena.
- 2026-09-20: Implementer, **stage 1b (`ITy`/`Sel`, the rewritten §3) — landed**. The
  migration to values is not attempted; the checker holds descriptions, no arena
  outlives a query, and every existing rule is untouched in its logic.

  ### What landed

  **`crates/kernel/src/typing/ity.rs` (146 lines, new).** `ITy = Syn(Rc<Type>) |
  Sel { of: Rc<ITy>, sel: Sel, at_depth: u32 }` with
  `Sel ∈ {Fst, Snd(Rc<Term>), Lhs, Rhs, Dom, Cod}`, plus `TyForm` (the checker's
  view: `Pi`/`Sigma`/`Sum`/`Other`) and `SndOf` (a Σ's codomain before the term it
  is instantiated at is known). `pub(crate)`, never a `Type` variant, no `Debug`
  (it is recursive; `CLAUDE.md`'s rule).

  **`at_depth` means the Γ-length the *selection* denotes at**, and
  `Sel::of_depth` derives the `of`'s from it — only `Cod` moves the scope, by one.
  Nothing is ever weakened: the value domain's variables are de Bruijn **levels**,
  so a description formed in a prefix of Γ evaluates in the identity environment
  of that prefix and is already correct in the longer scope. The design's
  "weakened to the current depth" is therefore a no-op and is not implemented as
  one; the rewriter side (`materialize`) *does* need the prefix Γ, and takes it.

  **`typing.rs`.** `tm_check`/`tm_infer` take/return `ITy`;
  `conv_ty(expected: &ITy, inferred: &ITy)`; nine `whnf` sites behind
  `Tc::whnf(&ITy)`; `Tc::view` / `view_expected` / `view_at`; `Tc::materialize`;
  the `materialize_eagerly` mode and `typing::oracle` (`check_term`,
  `infer_term`, `check_type`, `infer_type`, `check_local_ctx`,
  `check_local_subst`), documented like `conv::oracle`.

  **`conv.rs` / `conv/dom/values.rs`.** Two new crate-internal entries,
  `conv_ity_cached` and `head_ity_cached`, each building **its own arena and
  dropping it with the query** — `conv_type_cached`'s lifetime exactly;
  `Conv::<Values>::ity_root`; `values::eval_ity`, which evaluates a chain and,
  for `head_ity_cached`, reads the head and the levels and **throws the value
  away**. No conversion arm changed. `dom.rs` is `pub(super) mod values` (one
  word).

  **`stats.rs`.** `sel_evals` and `ity_materialized`, riding `Snapshot::NAMES`.

  **`tests/typing_differential.rs` (572 lines, new)** and 31 lines in
  `tests/common/wt.rs`.

  ### Six deviations from §3, each with its reason

  1. **`view` returns `TyForm`, not a general head view, and only `Π`/`Σ`/`+` get
     components.** Those are the only formers a *checking* rule descends into: of
     the nine `whnf` sites, eight match on `CodeTy`/`CodeTm`/`UPi`/`CtxPi`/`TyPi`
     and are served by `Tc::whnf` returning ordinary syntax, exactly as today.
     Only the λ checking descent needs a structured view, and only the five `@`
     rules need Σ/sum. So there is no second copy of `TyView` in the checker.
  2. **§3.3's `TyClo::as_syn` fast path for the "other formers" branch is not
     implemented**; that branch always goes through `materialize`. Same answer,
     and `ity_materialized` is the counter that says whether a workload ever
     reaches it. The fast path is an optimization with, so far, no customer.
  3. **The cross-head memo is skipped when either side is a `Sel`** rather than
     re-keyed on `ITy`. The bucket key is a `Type`'s discriminant plus a shallow
     anchor; a selection has neither, and inventing one would have put a new
     hashing decision underneath the "counters unchanged to the unit" gate. A
     `Syn`-against-`Syn` query takes the identical path it took before.
  4. **`Term::Lam`'s inference arm materializes too.** §3.5 names the three
     layer-m λ arms; the term-level λ has the same shape (it puts the body's
     inferred type inside a `Type::Pi`) and leaving it out would have been the
     one incomplete arm.
  5. **The five `@` rules moved out of `tm_infer_inner` into `Tc::tm_infer_at`,**
     and `tm_infer_inner` still returns `(Type, Level)` with `tm_infer` wrapping
     it. This is §3.2's "no existing rule constructs a `Sel`" made a property of
     the code rather than of a review: an arm in `tm_infer_inner` *cannot*
     return a description. Cost: one `Rc::new` per inferred type, which is the
     allocation the design owes anyway — an `ITy::Syn` holds an `Rc`.
  6. **`Tc::tm_check` has two thin wrappers**, `tm_check_rc` (caller already
     holds `Rc<Type>`) and `tm_check_ty` (rule built the type itself, shallow
     clone into an `Rc`). ~85 call sites changed by name only; no rule's logic
     moved.

  ### One thing found on the way

  `typing.rs`'s `term_head` (the miss sampler's site column, behind
  `value-metrics`) was never given the five `@` arms in stage 1a, so
  `cargo check --features value-metrics` did **not** build at `9c16741`. Nothing
  in `scripts/test` builds that feature — only `scripts/measure-x86-conv-miss`
  does — which is why it was invisible. Five arms added; the feature build is
  green. Worth a coordinator decision on whether the suite should build it.

  ### `wt.rs`: where the nesting comes from

  `gen_wt_term`'s `@` arms build one `@` form over component-form children, so
  nothing in the generator produced a **nested** `@` form and the `Sel` chains
  this round is about would never have formed. Added, gated on `at_forms` and on
  `layer.computes()` so the bench fixtures are untouched: `gen_wt_term_at`'s
  intro-directed descent now inhabits a Σ/sum target with `pair@`/`inl@`/`inr@`
  annotated by the **un-reduced** target. A `pair@` field is then itself a
  `pair@`, i.e. a description converted against an annotation. Projection chains
  (`fst@` of `snd@`) no generator arm reaches; they are handwritten in the test.

  `conv_differential.rs`, `eval_differential.rs` and `ch05_06_lemmas.rs` share
  `gen_wt_env_at` and so got the richer streams too; all three are green.

  ### `tests/typing_differential.rs`

  Eight tests: three generated streams (synthesis; a negative control at a wrong
  expected type; open terms in a non-empty Γ at a checked type), the two
  handwritten nesting tests, a fuel sweep over nine budgets, an identity-
  substitution stream, and one *softer* claim recorded on purpose —
  `error_variants_agree_too` — because `agree` compares `Ok` against `Err` and
  not the variant, and the stronger statement has in fact held.

  Every stream runs over Ψ and over an `opaque(Ψ)` copy. Failures report seeds
  only. `infer_term` is held to more than a verdict: where both modes answer,
  each side's inferred type must be accepted by the *other* side's `check_term` —
  the eager mode returns a spelling and the lazy one a description materialized
  at the gate, and the two need not be syntactically equal.

  **The vacuity guards matter more than the assertions.**
  `nested_projection_chains` asserts `intro_at_nodes > 0` and `sel_evals > 0`
  over its own run: without them a bug that stopped forming descriptions would
  make the whole file compare the oracle against itself and stay green. The first
  draft of the negative-control stream also asserted on refusals of
  `perturb_conv`, which is a *conversion* perturbation and stays well typed —
  that assertion fired, and the control is now the wrong expected type.

  `scripts/test --fast -p heather-kernel`: `== suite: 400 passed, 0 failed ==`.
- 2026-09-20: Implementer, **stage 1b gate — the counter and memory half, measured; the
  seconds are no result and the reason is not ambiguous**.

  **Provenance.** Two release binaries: `before` built from `9c16741` in
  `/tmp/claude-1000/before-9c16741`, `after` from this tree. `cmp` says they
  differ (byte 25). `before`'s `probes/str/p10.hthr` peak RSS came out at
  5 751 100 KB against the **5 733 MB the previous entry recorded for the same
  commit** — the before side is the before side.

  ### Counters: identical, row for row, on every file

  `heather check -L lib/std -L lib/std/parser --timings`, and
  `--cache --cache-dir <per-binary> --only parser_primitives::complete_post` over
  `docs/showcase/calc_parser.hthr` (each binary warmed its **own** cache dir
  first; `--only` over a shared one is a category error).

  Compared **every count column** the TSV carries — `conv_shortcut_hits`,
  `conv_memo_hits`, `conv_misses`, `conv_out_of_fuel`, `conv_not_convertible`,
  `eval_steps`, `eval_delta_steps`, `eval_drives`, `shift_global_nodes`,
  `delta_body_rescopes`, `global_ref_rescopes`, `global_sig_rescopes`,
  `check_terms`, `decls_gated`, `gendefs_pushed`, `mints_*`, `resolve_goals`,
  `unify_calls`, `cache_hashes`, `diag_*`, the four `*_cache_*` — per item,
  not per run:

  | file | rows | count columns that moved |
  |---|---:|---|
  | `lib/ir_v1.hthr` | 353 | **none** |
  | `probes/t_cp9.hthr` | 716 | **none** |
  | `probes/t_qt3.hthr` | 716 | **none** |
  | `probes/str/p10.hthr` | 745 | **none** |
  | `complete_post` (`--only`) | 42 | **none** |

  `intro_at_nodes`, `sel_evals`, `ity_materialized`: **0** on every row of every
  file, as required — there is still no emitter of `@` forms, so the checker
  must never form a description, and it does not.

  ### Peak RSS: flat, which was the point

  The before side was measured **twice** (the second pass is a spread sample),
  `ru_maxrss` of the child:

  | file | before #1 | before #2 | after | after vs. the before range |
  |---|---:|---:|---:|---|
  | `lib/ir_v1.hthr` | 634 380 | 628 948 | 629 496 | inside |
  | `probes/t_cp9.hthr` | 2 210 196 | 2 262 780 | 2 212 764 | inside |
  | `probes/t_qt3.hthr` | 4 003 044 | 4 120 576 | 4 039 464 | inside |
  | `probes/str/p10.hthr` | 5 751 100 | 5 842 132 | **5 739 708** | below both |
  | `complete_post` | — | 2 881 148 | 2 877 000 | −0.1 % |

  (KB.) **`p10` is the reading this round exists for**: the withdrawn §3.7
  design put it at 15 076 MB, ×2.63, and that is what killed the migration.
  Descriptions put it at 5 740 MB, which is *under* both before samples. No
  arena outlives a query, and the corpus says so.

  ### Seconds: no result, and the box says why

  The desktop was **not quiet**. Another session is running a test suite out of
  the main checkout (`/home/minus/Kairos/Code/heather/target/debug/deps/
  function_ir_composed_certificates`, `.../heather compile-x86`, at ~100 % each,
  started 14:41 and still running at 14:54); load average 10–17 throughout.

  The **before-against-before spread is larger than the before-against-after
  delta on every file**, which is the whole finding:

  | file | before #1 CPU-s | before #2 CPU-s | after CPU-s |
  |---|---:|---:|---:|
  | `lib/ir_v1.hthr` | 4.87 | 7.36 | 5.57 |
  | `probes/t_cp9.hthr` | 48.19 | 66.09 | 54.81 |
  | `probes/t_qt3.hthr` | 75.77 | 95.81 | 71.60 |
  | `probes/str/p10.hthr` | 137.70 | 185.57 | 129.41 |

  Four of four have the after inside or below the before range. The fifth,
  `complete_post`, has one before sample (17.45 CPU-s) against 28.40 — and it is
  the one to *ignore* most confidently, because the per-item table shows the
  same ≈1.6× on rows whose `kernel_gate_ns` is **zero**
  (`complete_sound` 6.86 s → 10.25 s, `recognize_sound` 1.01 ms → 2.50 ms,
  `fail_at`, `eof_at`, …). Those are elaboration-only items. Nothing in stage 1b
  can touch them. A uniform factor on work the change cannot reach is a machine
  state, not a code change.

  **What the round does owe, and cannot pay on this box:** the change *does* add
  one `Rc::new` per inferred type (`Tc::tm_infer`'s wrap) and one `Arc` refcount
  pair per `tm_check` (the `ITy::Syn` temporary). That is a real constant and it
  should be measured by `scripts/perf ab --before … --after … --marker sel_evals
  --samples 3` on a quiet box, which is the tool for exactly this and which I
  did not run because an interleaved A/B against a 100 %-busy neighbour is the
  `before-after-binary-provenance` mistake with extra steps. If the constant
  turns out to matter, two cheap moves are available and neither touches the
  design: `tm_check_ty` can take the `Type` by value instead of cloning it
  (~50 sites), and `tm_check` can take a borrowed `ITyRef<'_> = Syn(&Type) |
  Sel(&ITy)` so the checking direction — the overwhelmingly common one — pays no
  refcount at all.

  ### What is still owed on the gate

  - full `scripts/test` — running, reported next;
  - `scripts/bench --check` against the committed baseline — deliberately held
    until the neighbouring suite finishes, per `desktop-bench-gate-for-constants`.

  ### One small tool change

  `scripts/timings` gained three column aliases — `at` (`intro_at_nodes`),
  `sels` (`sel_evals`), `spelled` (`ity_materialized`) — so the round's three
  new columns are readable the same way as every other. Note the reader
  *refuses* `--diff` when one side's TSV predates a column, which is correct and
  is why the tables above were computed directly from the TSVs.
- 2026-09-20: Implementer, **the bench gate — it failed, what it caught was real, and two
  rounds of paying it down**. This is the entry the previous one said it owed.

  ### First reading: `nat/check-numeral` ×4.15

  `scripts/bench --check` against the committed baseline, nine regressions:

  ```
   REGRESSED  nat/check-numeral:64                     1.47 µs → 6.10 µs (4.15×)
   REGRESSED  nat/check-numeral:128                    3.19 µs → 13.08 µs (4.10×)
   REGRESSED  nat/check-numeral:256                    6.41 µs → 28.28 µs (4.41×)
   REGRESSED  nat/check-numeral:512                    14.96 µs → 59.66 µs (3.99×)
   REGRESSED  wf/check-tree:683                        111.89 µs → 144.74 µs (1.29×)
   REGRESSED  wf/check-tree:2963                       477.72 µs → 597.31 µs (1.25×)
   REGRESSED  code/check-identity-recursor:3           286.21 µs → 358.87 µs (1.25×)
   REGRESSED  code/check-identity-recursor:33          326.51 µs → 435.67 µs (1.33×)
   REGRESSED  stack/check-numeral depth                1512 → 1173 levels in 4 MiB (3576 B/level)
  ```

  A 4× is not box noise, and this is the reading the corpus could not give: the
  routine files are dominated by conversion, and a per-*node* constant in the
  checker disappears into them. `nat/check-numeral` is `Succ^n Zero : Nat` and
  therefore one `tm_infer` and one `tm_check` per node with nothing else in
  between — the one workload where widening the checker's channels *is* the
  measurement. **The harness earned its keep here**; without it this would have
  shipped and been found by someone else later, in something slower.

  ### The cause, and the fix

  `ITy::Syn(Rc<Type>)` was the only syntax shape, so `Tc::tm_infer`'s wrap
  `Ok((ITy::Syn(Rc::new(ty)), l))` was **one `malloc` per term node**, against
  a baseline whose per-node work is a `discriminant` compare.

  `ITy` gained a second syntax variant:

  ```
  ITy = Owned(Type)        -- the value the rule already had on its stack, moved
      | Syn(Rc<Type>)      -- syntax that is genuinely shared (an `@` annotation)
      | Sel { of, sel, at_depth }
  ```

  `as_syn` and a hand-written `PartialEq` treat the two as one case, so no rule
  and no view distinguishes them; the shape a value is *held* in is not part of
  the judgment. `tm_infer` wraps with `Owned` (a move), `tm_check_ty` builds
  `Owned` (a shallow clone, no allocation), `tm_check_rc` keeps `Syn`.

  **That one change took 4.15× → 1.64× and cleared four rows outright** —
  `wf/check-tree` and `code/check-identity-recursor` are back inside tolerance,
  which is the tell that the allocation, not the widening, was their whole
  cost.

  A second pass — `#[inline(always)]` on the two `tm_check` wrappers, which
  were costing a stack frame per level of a recursion that is measured by
  frames — took it to **1.42×** and recovered 46 stack levels.

  ### Where it stands, on a **quiet** box (load 1.9; the neighbouring session
  had finished)

  ```
   REGRESSED  nat/check-numeral:64      1.47 µs →  2.16 µs (1.47×)
   REGRESSED  nat/check-numeral:128     3.19 µs →  4.42 µs (1.39×)
   REGRESSED  nat/check-numeral:256     6.41 µs →  9.27 µs (1.45×)
   REGRESSED  nat/check-numeral:512    14.96 µs → 21.18 µs (1.42×)
   REGRESSED  stack/check-numeral depth  1512 → 1341 levels in 4 MiB (3128 B/level)
  ```

  Everything else passes, including the three rows that measure the same
  checker over bigger objects: `wf/check-tree`, `code/check-identity-recursor`
  and `check/generated-terms` (the broad checker-throughput row). So what is
  left is a per-node constant on the narrowest possible workload, plus the
  +358 B/frame that one `ITy` per level costs.

  **I did not `--save`**, per the brief. The committed baseline is untouched and
  the verdict above is reproducible. Filed as
  `issues/ity-widens-the-checker-per-node-constant.md` with the two candidate
  fixes (a borrowing `ITyRef` for the checking direction; or accept and
  re-record) — the choice is the coordinator's, because "a 1.4× per-node
  constant is the right price for removing a 3.5ⁿ" is a judgment about the
  round, not about the code.

  ### The suite, twice

  `== suite: 2835 passed, 0 failed, 5 ignored ==` on the tree *before* the
  `Owned` fix (2827 at stage 1a, plus the differential's 8), with
  `showcase_gate`'s `calc_text` at **9.8 GiB peak** — the number `CLAUDE.md`
  and the gate's own comment quote, against the withdrawn design's 12.5 GiB.
  Nothing to re-record. The suite is being re-run on the tree *after* the
  `Owned` fix and the inline hints, since those landed after it went green; that
  result is the next entry.
- 2026-09-20: Implementer, **stage 1b handover: the gate, on the final tree, on a quiet
  box** — and the one number the coordinator has to decide about.

  ### Green

  - **`scripts/test`: `== suite: 2835 passed, 0 failed, 5 ignored ==`**, run
    twice: once on the tree before the `ITy::Owned` fix and once after it, since
    the fix landed after the first run went green. 2827 at stage 1a plus the
    differential's 8.
  - **`showcase_gate` / `calc_text`: `ok  246.0 s wall  244.2 s cpu  9.8 GiB
    peak`** — the 9.8 GiB `CLAUDE.md` and the gate's comment quote, unchanged.
    (The withdrawn §3.7 arena had it at 12.5 GiB; nothing to re-record.)
  - **Counters: not one column moved, on any of the five files.** Every count
    column the TSV carries (27 of them), per item:

    | file | rows | moved |
    |---|---:|---|
    | `lib/ir_v1.hthr` | 353 | none |
    | `probes/t_cp9.hthr` | 716 | none |
    | `probes/t_qt3.hthr` | 716 | none |
    | `probes/str/p10.hthr` | 745 | none |
    | `complete_post` (`--only`) | 42 | none |

    `intro_at_nodes`, `sel_evals`, `ity_materialized`: **0** everywhere. No
    emitter, so no description is ever formed, so the checker is the old
    checker — which is the property the whole stage was designed around.
  - **Peak RSS: no direction.** −0.1 % to +4.1 % across the five; `p10` at
    5 774 MB against 5 755 MB, i.e. +0.3 %, where the withdrawn design was
    15 076 MB. The arena question is settled.

  ### The decision: a per-node constant, and the corpus split that explains it

  `scripts/bench --check` **fails**, on five rows, after two rounds of paying it
  down (4.15× → 1.64× → 1.42×; the previous entry has the mechanism):

  ```
   REGRESSED  nat/check-numeral:64      1.47 µs →  2.16 µs (1.47×)
   REGRESSED  nat/check-numeral:128     3.19 µs →  4.42 µs (1.39×)
   REGRESSED  nat/check-numeral:256     6.41 µs →  9.27 µs (1.45×)
   REGRESSED  nat/check-numeral:512    14.96 µs → 21.18 µs (1.42×)
   REGRESSED  stack/check-numeral depth  1512 → 1341 levels in 4 MiB (3128 B/level)
  ```

  The corpus, measured on the same quiet box with the same binaries, says the
  same thing and says **where it does and does not matter**:

  | file | before CPU-s | after CPU-s | | |
  |---|---:|---:|---|---|
  | `lib/ir_v1.hthr` | 3.94 | 5.26 | **+33 %** | many small declarations |
  | `probes/t_cp9.hthr` | 34.07 | 41.13 | **+21 %** | " |
  | `probes/t_qt3.hthr` | 49.75 | 62.72 | **+26 %** | " |
  | `probes/str/p10.hthr` | 118.75 | 113.65 | **−4 %** | 42 M conversion queries |
  | `complete_post` | 17.21 | 14.54 | **−16 %** | conversion over a replayed prefix |

  One constant, paid once per **term node**. A file whose time is conversion
  does not notice it and is, if anything, faster. A file made of many small
  declarations pays it in full. **The files this round exists for are the
  second kind** — which is the uncomfortable half of the reading and the reason
  this is a decision and not a note.

  Filed as `issues/ity-widens-the-checker-per-node-constant.md` with the split,
  the two attempts already made, and the one candidate that would close it
  without touching the design (`ITyRef<'a> = Syn(&'a Type) | Sel(&'a ITy)` for
  the checking direction, which constructs nothing in the common case).

  **The three things to decide, in order:**

  1. **Is the constant paid or fixed before stage 2?** Fixing it is a contained
     round against a named candidate; paying it is `scripts/bench --save` with
     the issue as the record. I did **not** `--save` — the committed baseline is
     untouched and the verdict reproduces.
  2. **Does the suite build `--features value-metrics`?** It does not today, and
     that is how stage 1a's missing `term_head` arms survived (fixed here).
  3. **Does `probes/` get committed or `.gitignore`d?** Still open from the
     stage-1a handover, and now three rounds have depended on it.

  ### Tree state

  Nothing committed. `crates/kernel/benches/baseline.tsv` is the **committed**
  one (the previous implementer's fresh control was overwritten by
  `git checkout` before this round began; `git status` is clean on it).
  `probes/` is still untracked.


### 2026-09-20 — where the constant landed

`issues/ity-widens-the-checker-per-node-constant.md` is **closed**. The three
questions the stage-1b entry above left open are answered in the first two
cases and unchanged in the third.

**1. Paid or fixed?** *Fixed*, and the committed baseline was never touched —
`scripts/bench --save` was not run and did not need to be. `scripts/bench
--check` is clean on a quiet box (loadavg 2.76): `ok: 112 comparisons within
thresholds`. The two rows that failed:

```
nat/check-numeral:512   14.96 µs → 17.65 µs   (stage 1b: 21.18 µs, 1.42×)
stack/check-numeral     1512 → 1548 levels    (stage 1b: 1341)
```

The stack row is now *past* the baseline. The corpus, by
`scripts/perf ab --base 9c16741 --samples 3` on the same box, is back inside
its own spread on all four files, with **every counter identical to the unit**
on every file and every sample:

| file | stage 1b | now |
|---|---:|---|
| `lib/ir_v1.hthr` | +33 % | **−0.9 %, no change** |
| `probes/t_cp9.hthr` | +21 % | **+0.2 %, no change** |
| `probes/t_qt3.hthr` | +26 % | **−0.7 %, no change** |
| `probes/str/p10.hthr` | −4 % | **+0.3 %, no change** |

And the diagnosis is worth carrying into stage 2, because the entry above
guessed wrong about it and so did this issue's own candidate list. **`ITy` was
never the cost.** It is 72 bytes — *exactly* `Type`'s, the tag rides in a
niche — so widening `tm_infer`'s return was free, and every
"shrink the return" idea was aimed at a channel that had not moved. What cost
was that the **checking** direction stopped borrowing: `tm_check` took a
`&ITy`, so each of the 86 call sites of its two wrappers built a 72-byte
temporary in its *caller's* frame, and the 24 `Rc` sites paid an `Arc`
increment and decrement per term node on top. `tm_check_inner`'s frame went
296 → 712 bytes, which is the whole stack row. The fix is a two-word `Copy`
borrow (`ITyRef<'a> = Syn(&'a Type) | Ity(&'a ITy)`), plus outlining the
checking λ — the one arm holding a 200-byte `TyForm` across its own descent —
off the recursion cycle. The cycle is now 2592 bytes against `9c16741`'s 2656:
the checker recurses in a *smaller* frame than before `ITy` existed.

The lesson for stage 2 is the instrument, not the fix: `size_of` and the
`sub $N,%rsp` of each symbol in the release rlib are **load-independent**, and
they settled this while the box was at load 12–18 and no timing was possible.

**2. `--features value-metrics`.** Now checked. `scripts/test` runs
`cargo check -p heather-kernel --features value-metrics` beside the
tree-sitter inventory check — a check and not tests, because the feature
changes instrumentation and not judgments, and seconds against a hole that
swallowed stage 1a's missing `term_head` arms.

**3. `probes/`.** Still untracked, and now four rounds have measured against
it. Unchanged from the stage-1a handover; still a decision for whoever takes
this thread next.

### Tree state

Nothing committed. `crates/kernel/benches/baseline.tsv` is still the
**committed** one and is what the clean gate above was measured against.
- 2026-09-20: Implementer, **stage 2 — STOPPED at the first emitter, on a layer the design
  and the implementation disagree about.** Nothing is wrong with stage 1; the
  forms, the rules and the checker are all correct. What is wrong is the
  *premise* that the elaborator ever emits at a computing layer.

  ### The finding, in one sentence

  **Every declaration body in Heather is kernel-checked at `Layer::Code`**, and
  the five checked spellings are refused at layer c by construction (§2.3,
  `Tc::computing_layer`, and stage 1a's own golden test pins it), so an `@` form
  written by any emitter is `LayerMismatch` — not on a metaprogram, on
  `fn mk(x: Nat) -> Box2 { Box2 { a: x, b: x } }`.

  ### Measured, not reasoned

  A throwaway spike (`build_fields_skel` emits `PairAt { ty: emit_ty(ctor_ty) }`
  instead of `Pair`, behind `HEATHER_AT_SPIKE`, release binary in
  `target-spike/`):

  ```
  $ heather check -L lib/std probes/tiny.hthr
  probes/tiny.hthr: ok

  $ HEATHER_AT_SPIKE=1 heather check -L lib/std probes/tiny.hthr
  error: the kernel rejected `mk`: LayerMismatch
    --> probes/tiny.hthr:6:1
  lib/std/pair.hthr: 2 errors
  ```

  ### Where the layer comes from, and why it is not an oversight

  - `crates/elab/src/lib.rs` ~3637 and ~3688: the inline gate builds
    `gate::GateItem { …, layer: Layer::Code, … }` and calls
    `kernel_check_term(&psi, Layer::Code, …)`; the deferred path
    (`defer_kernel_term`, lib.rs ~3688 and `gendefs.rs` ~3473) passes
    `Layer::Code` too. **The statement** is checked at `Layer::Prog`
    (`kernel_check_type(…, Layer::Prog, …)`) — which is why §1's "a type lives at
    `typeof(i)`, which is always a computing layer" is true and misleading: it is
    true of the *statement* and of `Tc::whnf`, and says nothing about the body.
  - `GlobalBinding::defined_tm(empty, Layer::Code, …)`: every binding lands in Ψ
    at layer c.
  - `crates/kernel/DESIGN.md` ~233 says why, and it is load-bearing: "**The body
    is checked at the binding's own layer** (`i = c`) … That is what makes δ
    layer-preserving: unfolding `u` at any layer `j ≥ i` can only produce a term
    that was already legal at `j`." A body containing a form illegal at c would
    break exactly that.
  - `Cx` (`crates/elab/src/context.rs` ~15) **has no `layer` field**, and grep
    finds no `cx.layer` anywhere in `crates/elab`. §2.3's "the elaborator already
    knows the layer at every emission site (`cx.layer`)" and the brief's
    "`cx.layer.computes()`" describe an API that does not exist — and if it did,
    it would return `Code` at every one of the four emitters.

  So §2.3's cost accounting ("the switch is one predicate at each of the ~4
  emitters") is not a small edit that was missed; the predicate it names is
  **constantly false**, and the design's layer restriction and Heather's
  definition-body layer are the same layer.

  ### What this does *not* break

  The restriction's purpose (§2.2) is that layer c is what the 56 recursor
  branches range over and `tm_pair`'s telescope types `u_a` by `U_S`. That
  purpose is about **code inside a `box`**, and in Heather a definition body at
  layer c is *not* reachable by the recursors: δ is opaque at c
  (`Defs::opaque`), ch. 06 blocks the code-recursion principles on global
  variables, and `box(u^δ)` keeps the body a variable. The conflation is that
  DeLaM uses the layer to mean "inside a quotation" and Heather also uses it to
  mean "a definition body".

  ### Candidates, priced as far as reading goes, for the coordinator

  1. **Guard on "under a quotation", not on the layer.** One bit in the merged
     `conv::Env` (`quoted: bool`), set by the `Box`/`BoxTy` rules where they
     descend into a payload; the five rules guard on `!quoted && not_var_layer`
     instead of `computing_layer`. The invariant §2.2 needs — no `@` form ever
     inside a `box` payload, so `Trm_c`'s grammar and all 56 branches are
     untouched — is then enforced by the kernel rather than by the elaborator's
     discipline, which is *stronger* than what §2.3 promised. Costs: a kernel
     rule change (so a stage 1c, not stage 2); §2.4's conservativity statement
     re-stated over "not under a box" instead of over p/m; the golden test's
     "layer c refuses all five" inverted into "layer c under a box refuses all
     five, layer c outside one admits them"; ch. 04's rule statement changes
     shape, which is the Coq formalization's cost this pass said was a
     consideration.
  2. **Gate declaration bodies at `Layer::Prog`.** Refused on reading alone:
     DESIGN.md ~233's δ layer-preservation argument is exactly this, and every
     quotation of a definition changes meaning.
  3. **Admit the five at layer c unconditionally.** This is §2.2's refusal
     verbatim — `box(pair@(T;a;b))` becomes well typed with no recursor branch,
     so "boxed code is exhaustively recursable" fails in the trusted base.
     Declined here without measurement.

  **I am not choosing between these**: (1) is a kernel rule change with a
  metatheory statement attached, which is the coordinator's call, and the
  previous two stops on this issue set the precedent that a design gap is logged
  and handed back rather than deviated through.

  ### What the round does next, instead of nothing

  Per the brief's own instruction to keep everything else, and because the
  kill-criterion question ("does the curve's per-layer ratio fall") is answerable
  without deciding (1)–(3): the four emitters are being implemented as designed,
  and measured behind a **spike** that relaxes the kernel guard for the
  measurement only. The before table (step 1) is already recorded below and the
  readers audit (§4.2) is owed regardless. Neither the spike nor the emitters are
  proposed for landing until the layer question is answered.
- 2026-09-20: Implementer, **stage 2's measurement, taken behind the spike — and the §9
  kill criterion fires: the per-layer query ratio does not move at all.** With
  the four emitters of §4.1 in and firing, `t_cp9 → t_qt3 → t_qt5` is
  **×3.31 / ×3.71 before and ×3.31 / ×3.71 after**, to three digits. The design's
  central claim — that the exponent is carried by what these four sites write —
  is refused by its own instrument, and the counters say where it actually is.

  ### Provenance

  `target-before/release/heather` is byte-identical (`cmp`) to a release build of
  the clean tree at `483d355`, so the before side is HEAD's. The after side is
  `target-spike/release/heather`, this tree, with `HEATHER_AT_SPIKE=1`. Counts
  are exact and load-invariant and are what the verdict rests on; the seconds
  below are **not** a result — `scripts/perf ab` was not run (see "deviations").
  Width one throughout; `ru_maxrss` of the child.

  ### The curve, per-item, on the probe theorem each file exists for

  | item | queries before | queries after | | per-layer before | per-layer after |
  |---|---:|---:|---:|---:|---:|
  | `t_qt2::qt_floor` | 6 516 | 6 520 | 1.001 | — | — |
  | `t_qt1::qt_pure` | 392 484 | 390 688 | 0.995 | ×60.2 | ×59.9 |
  | `t_cp9::cp_andt` | 2 407 804 | 2 398 322 | 0.996 | ×6.13 | ×6.14 |
  | `t_qt3::qt_deep` | 7 969 594 | 7 933 589 | 0.995 | **×3.31** | **×3.31** |
  | `t_qt5::qt_deeper` | 29 603 080 | 29 462 792 | 0.995 | **×3.71** | **×3.71** |

  **`complete_post`** (whole-run row of `t_cp9`): queries 3 699 898 → 3 684 206
  (0.996), `conv_shortcut_hits` 3 682 495 → 3 663 472 (−0.5 %), misses
  14 210 → 17 555, steps 247 834 → 342 347, `decl_emit` 698 → 604 ms,
  `elab_whnf` 1 359 → 1 570 ms. Against the mint's 0.78 M queries / 90 k emitted
  nodes, this is **3.68 M and no measurable shrink**.

  Whole-run counts, every file:

  | file | queries B | queries A | | misses B | misses A | steps B | steps A | `at` | `sels` | `spelled` |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
  | `t_qt2` | 8 959 776 | 8 998 564 | 1.004 | 157 117 | 351 160 | 3 435 947 | 3 596 471 | 139 365 | 230 934 | 0 |
  | `t_qt1` | 9 345 744 | 9 382 732 | 1.004 | 158 565 | 352 988 | 3 462 531 | 3 631 914 | 139 605 | 231 414 | 0 |
  | `t_cp9` | 11 361 064 | 11 390 366 | 1.003 | 165 956 | 362 040 | 3 598 664 | 3 810 508 | 140 721 | 233 583 | 0 |
  | `t_qt3` | 16 922 854 | 16 925 633 | 1.000 | 190 876 | 388 739 | 3 962 879 | 4 356 417 | 144 267 | 240 657 | 0 |
  | `t_qt5` | 38 556 340 | 38 454 836 | 0.997 | 285 139 | 494 310 | 5 360 725 | 6 555 054 | 158 181 | 268 467 | 0 |
  | `str/p10` | 62 230 517 | 61 354 198 | 0.986 | 1 741 768 | 1 924 197 | 12 365 533 | 12 462 583 | 150 408 | 249 095 | 0 |
  | `complete_post` (`--only`) | 3 861 605 | 3 845 590 | 0.996 | 16 388 | 22 056 | 282 584 | 376 501 | 4 147 | 7 494 | 0 |

  `ity_materialized` is **0** on every file: §3.5's rewriter escape hatch is never
  reached, so the checker is doing exactly what §3.3 designed and the answer is
  not an artefact of a fallback.

  Peak RSS (KB) and CPU-s, the same runs:

  | file | RSS before | RSS after | | CPU-s B | CPU-s A |
  |---|---:|---:|---:|---:|---:|
  | `t_qt2` | 2 115 124 | 1 920 832 | −9.2 % | 30.9 | 32.2 |
  | `t_qt1` | 2 121 944 | 1 863 796 | −12.2 % | 30.1 | 45.2 |
  | `t_cp9` | 2 223 868 | 1 964 352 | −11.7 % | 35.1 | 45.8 |
  | `t_qt3` | 4 010 848 | 3 846 572 | −4.1 % | 55.5 | 69.9 |
  | `t_qt5` | 12 715 584 | 12 502 616 | −1.7 % | 118.0 | 144.5 |
  | `str/p10` | 5 857 760 | 4 986 600 | −14.9 % | 105.2 | 99.7 |
  | `complete_post` (`--only`) | 2 886 176 | 2 614 392 | −9.4 % | 13.9 | 14.9 |

  So the round buys a **single-digit-percent RSS reduction and a constant-factor
  slowdown**, and changes the exponent by nothing.

  ### Why — and this is a defect in §4.1's table, not in the implementation

  `at` = 2 193 checked spellings in `complete_post`, against a reduct the earlier
  rounds measured at **2 634 824 nodes**. Two thousand annotation *sites* were
  rewritten and the term did not shrink, because **the type each of them now
  writes is itself a component of the reduct**:

  - `build_ctor` computes `expected = whnf(pre_whnf)` and then
    `let spine = self.spine(&expected, …)` (`inductive.rs` ~2237). The tuple is
    built by `build_fields_skel(cx, &spine.ctors[i].0, …)` — so the `ctor_ty`
    §4.1's second row calls "the un-reduced type" is `spine.ctors[i].0`, **a
    summand read out of the reduct**, not the type the elaborator started with.
  - Inside `build_fields_skel` the recursion is
    `tail = snd.apply_local(…)` where `snd` came from `whnf(ctor_ty)`, so every
    level below the first is a reduct component too.
  - `projection`'s `cur_emit` chain has the same shape: step 0's annotation is
    the receiver's own type (genuinely un-reduced, and a real win), and every
    later step's is `snd_e[proj/x]` off the previous whnf.
  - The **only** site that writes a genuinely un-reduced type is `inject`'s
    outermost layer, which takes `pre_whnf`: one annotation per constructor
    value. Everything else replaces *two* components of a whnf with *one*
    parent of that whnf, which is a factor of about two on a `3.5ⁿ` object.

  That is the whole result. §1's "the pre-whnf type is in hand one line above the
  call" is true at `build_ctor` and **false one call further down**, and the four
  emitters live further down. Getting an un-reduced type to them means not
  reading the constructor's type out of `spine(&expected)` — i.e. §5 candidate 3,
  "deciding the constructor without spelling", which is **stage 3**. The
  checked spellings are the syntax stage 3 would need; they are not, on their
  own, a smaller term.

  ### What the round *does* establish, and should be kept

  - **A `@`-bearing module round-trips.** `heather check --cache` over
    `calc_parser.hthr` with the spike on stored an 86 MB cache (the same 86 MB
    the before side stores); a second pass replays it — `0 declarations
    kernel-checked, 561 accepted from cache, 20 semantic modules replayed` — and
    `--only parser_primitives::complete_post` works on it (`1 declaration
    elaborated for --only, 34 replayed`). Stage 1a's five image tags, the five
    merkle tags and the `SemanticsIdentity` bump are correct in use, not only in
    a unit test.
  - **The checker behaves as §3 designed.** `ity_materialized` 0 everywhere;
    `sel_evals` ≈ 2 × `intro_at_nodes` (each `pair@` views its Σ twice), so the
    §3.7 re-evaluation cost is *bounded and visible*: 268 k evaluations on
    `t_qt5` against 38 M queries. §3.7's "whether that re-evaluation dominates is
    stage 2's first number" is answered: **it does not**, and no
    declaration-scoped memo is needed.
  - **The cost of a `Sel` is in misses, not in materialization.** Misses roughly
    double on the curve (157 k → 351 k on `t_qt2`; the extra are the
    `Sel`-vs-`Syn` queries the `==` shortcut and the cross-head memo both decline
    by §3's deviation 3). That is the price of the mechanism and it is paid
    without a compensating query reduction, which is why the seconds go the wrong
    way.

  ### Deviations from the brief, each with its reason

  1. **`scripts/perf ab` was not run.** The after side needs `HEATHER_AT_SPIKE=1`
     and the harness has no way to set it for one side; more to the point the
     verdict is a *counter* verdict — exact, load-invariant — and the counters
     moved by less than half a percent. The seconds above are reported as
     measurements taken the same way on both sides and **not** as a result. If
     the coordinator wants a seconds verdict, `--patch` with the env exported to
     both builds would do it (the before half has no emitter, so the variable is
     inert there).
  2. **`inject` takes the checked spelling at its outermost layer only.** Layer
     `j+1`'s type is layer `j`'s whnf's right summand, and a selection of a
     component is an `ITy::Sel`, which is checker-internal and has no syntax
     (§3.2). For a two-constructor declaration the chain is one layer deep, so
     this is exact where the parser tower is concerned.
  3. **A recursive declaration's label injection takes the `Wf`'s emitted
     `shape`, not `pre_whnf`** — the label's type is the shape, and using the
     same spelling the `sup_f` slot takes is what keeps their agreement a `==`.
     The `sup_f` slot computation moved above `inject` for this; no other
     behaviour changed.
  4. **`emit_ty` is still called** on the annotation, per §4.1, and on the
     *un-reduced* type — which is the one part of §4.1 that worked as written.
  5. **§4.4's deletions were not made**, and the reason is a measurement: all
     three hooks are already inert. `rbcount::at_build_ctor` returns on
     `!enabled()`, `rbname::at_build_ctor` on `!counting()`, `mint_ctor_reduct`
     on `!firing()` — all three keyed to `HEATHER_RB*`, all three false by
     default. §4.4's "the readback ran at every `build_ctor` … `elab_whnf_ns`
     ×3.5–4" is a statement about *fired* items under `HEATHER_RB_MINT=1`, not
     about the default path, so **there is nothing for the deletion to measure**:
     it is 6 419 lines of dead-code removal (`mint.rs` 1 808, `rbcount.rs` 1 755,
     `rbname.rs` 1 886, `rbemit.rs` 970) with a zero attached. Doing it inside a
     round that is stopped, on top of spike instrumentation that must not land,
     would bury both. It should be its own commit and it is ready to be one.
- 2026-09-20: Implementer, **§4.2's readers audit, walked, with one line per reader — and
  two readers the list does not name that broke a library file on the first
  run.** The principle held everywhere: every one of them was fixed *in the
  reader*, nothing was renamed, and no annotation carries a reduct to placate
  one.

  ### The two the list missed, found by running rather than by reading

  The first spike run over `probes/t_cp9.hthr` failed in `lib/std/`, not in the
  probe:

  ```
  error: `absurd` needs both sides of the equation to be constructor applications
    --> lib/std/list.hthr:840:35
  error: `omega` got stuck: Omega could not spell an integer expression
    --> lib/std/omega.hthr:1009:5   (and ~30 more)
  ```

  - **`inductive.rs` `read_ctor` (~4564)** — §4.2 lists it as "shape-only, add
    the arms, read nothing", and that is exactly right, but it is not optional:
    it walks the `Inl`/`Inr` path to identify the constructor and the `Pair`
    chain to collect the fields, and it is what `absurd`/`inj`/disjointness sit
    on. Fixed: the walk goes through `crate::spelling::{inj_of, pair_of, is_pair}`.
  - **`omega_cert.rs` `is_ctor_value` (~1211) and `children_fields` (~1224)** —
    not on the list at all. `is_ctor_value` gates Omega's constructor reflection
    on `Inl`/`Inr`; `children_fields` walks a children tuple. Both fixed by arms
    / the view.

  ### The list, answered

  - **`display.rs` ~443** (`display_tag_of` on an injection's annotation):
    **fixed one node higher rather than by a whnf.** `inl@` carries the *whole
    sum* and `tag_of` already walks a `Sum` to its leftmost constructor, so
    `display_tag_of(ty)` is the same lookup. An annotation that is not
    structurally a sum declines and the display falls back to `raw_tm`, as it
    does for every shape it cannot read — the design's "whnf `T` first" would
    need a `Span` the display path does not carry, and diagnostics are
    best-effort by construction here. Also: `Walk::tm`'s `Pair` arm, the
    `ctor_value` entry arm, and `ctor_value`'s injection walk and three tuple
    walks, all through `crate::spelling`.
  - **`inductive.rs` `projection`'s `cur_emit`**: carries `T` forward instead of
    components, as §4.2 predicted. The loop still computes `fst_e`/`snd_e` —
    `snd_e` advances `cur_emit` and `fst_e` is the field type the function
    returns — but neither is written into the term.
  - **`matching.rs` `field_rewrap` (~664)**: **the smaller invariant is real.**
    A `fst@` chain's η-expansion is `pair@(T↑; x₀, snd@(T↑; p↑))` — one
    annotation carried, none rebuilt, against the four `shift_local`s per level
    the component path does. A chain is homogeneous (one `projection` call
    writes one spelling all the way down), so the two loops never interleave.
    `matching.rs`'s `stuck_scrutinees` also took the arms.
  - **`lgg.rs` ~670**: five new arms, each anti-unifying **one** annotation and
    requiring **no** level equality — §4.2's "structurally smaller and more often
    identical" is the shape of the arm. Mixed spellings fall to `mismatch_tm` and
    generalize, which is what two different spellings of one term have always
    done here. `head_tm`'s name table gained `pair@`/`fst@`/`snd@`/`inl@`/`inr@`
    so a diagnostic does not say "Var".
  - **`emission_walk.rs`**: already exhaustive with the five `ty @ d` arms from
    stage 1a; nothing to do, and it is the reason the compiler would have caught
    a missing slot.
  - **`certgen.rs` (~2284, ~2312, ~2389)**: the payload-field read, the
    induction-hypothesis index walk and the `mark` re-builder. All three took
    arms; `mark` carries the annotation through untouched exactly as it carries
    the component ones.
  - **`oracle.rs` ~260** (the neutral-spine walk) and **`inductive.rs`
    `receiver_is_neutral` (~5236)**: two arms each, read nothing.
  - **`record_of_at` (~2957)**: unchanged and **correct as designed**. It is a
    reader of a *type*, and the `@` forms are terms; its "structural read first,
    whnf paid only when it fails" shape never meets one.
  - **`module_image.rs` encode/decode and `merkle.rs`**: stage 1a's five tags,
    **verified in use** — see the measurement entry: an 86 MB `@`-bearing cache
    stores, replays (`561 accepted from cache, 20 semantic modules replayed`)
    and serves `--only`.
  - **`gendefs.rs` ~343** (`head_tm`'s bucket name, diagnostics): arms added so
    a `pair@` is bucketed with a `pair`.

  ### Readers that are **tests**, and will need updating if this ever lands

  `wf.rs`'s in-file tests (~2706, ~3001, ~3029, ~3087, ~3272, ~3345) assert the
  component spelling of an emitted constructor value — that an `inr`'s two
  annotations *are* the shape's two summands, which is precisely the invariant
  the `@` form replaces. `expr.rs` (~1497) and `lgg.rs`'s own tests do the same
  in smaller form. They are green today only because the emitters are behind
  `HEATHER_AT_SPIKE`; a landing round owes them. This is the readers audit's
  real remaining bill and it is not small.

  ### Files touched for the audit

  `crates/elab/src/spelling.rs` (new, 64 lines: `inj_of`, `pair_of`, `is_pair`,
  `is_inj`, `proj_of` — the three views a shape-only reader needs, so the arms
  are written once and not at forty sites), plus arms or view calls in
  `display.rs`, `inductive.rs`, `matching.rs`, `omega_cert.rs`, `oracle.rs`,
  `certgen.rs`, `lgg.rs`, `gendefs.rs`. **All of this is landable independently
  of the layer decision**: with the spike off, `spelling::*` is called on terms
  that are never `@` forms and every arm is unreachable, so it is inert — and it
  is the part of stage 2 that would otherwise have to be re-derived by whoever
  picks the round up.
- 2026-09-20: Implementer, **stage 2 handover: tree state, what to keep, and the three
  decisions.** Nothing committed.

  ### The tree

  ```
   M crates/kernel/src/typing.rs      +21/-2   the HEATHER_AT_SPIKE relaxation of
                                               Tc::computing_layer — MUST NOT LAND
   M crates/elab/src/context.rs       +34      Cx::quoted, Cx::emits_at_forms, at_spike()
   M crates/elab/src/quote.rs          +4      pcx.quoted = true on a box payload
   M crates/elab/src/inductive.rs    +199/-38  inject_at, build_fields_skel, projection,
                                               wf_slots hoist; read_ctor + receiver_is_neutral
   M crates/elab/src/forded.rs        +14      build_fields_collect
  ?? crates/elab/src/spelling.rs      +64      the three shape views
   M crates/elab/src/{display,matching,omega_cert,oracle,certgen,lgg,gendefs}.rs
                                               the readers audit
   M crates/elab/src/lib.rs            +1      mod spelling;
  ```

  **Three separable pieces, and they should be separated:**

  1. **The readers audit** (`spelling.rs` + the seven readers + `read_ctor` +
     `receiver_is_neutral`) — inert with the spike off, correct, and the part
     that would otherwise be re-derived by the next attempt. Landable now.
  2. **The four emitters + `Cx::quoted`** — correct, measured, and pointless
     until the layer question is answered; `Cx::quoted` is also the elaborator
     half of candidate 1 whichever way that goes.
  3. **The kernel spike** — one function, clearly commented as an instrument.
     It must not land: under it `box(pair@(T;a;b))` is well typed with no
     recursor branch.

  `crates/kernel/benches/baseline.tsv` untouched. `probes/` still untracked
  (fifth round). `target-before/` is a verified byte-identical build of `483d355`
  and `target-spike/` is this tree; both are scratch and can be deleted.

  ### Gates

  - **Full `scripts/test`**: see below — it gates piece (1), which is the only
    part on the default path. The emitters cannot affect it: with the spike off,
    `Cx::emits_at_forms()` is constantly false and no `@` form is constructed.
  - **`scripts/bench --check`** was **not run**: nothing in this round is on the
    kernel's hot path with the spike off (the one kernel edit is a `||` in a
    guard reached only by the five `@` rules, which no fixture generates by
    default since stage 1b step 1 turned `at_forms` off), and the box was busy
    with the suite. If piece (3) is dropped, as it should be, there is no kernel
    change left to gate.
  - **`scripts/showcase check calc_text`** with the spike: not run. Its purpose
    in §9 is the image's node count against the 256 M budget, and the
    measurement entry already answers it — `conv_shortcut_hits` on
    `complete_post` moved by −0.5 % and the `calc_parser` cache came out at the
    same 86 MB on both sides, so the emitted term did not shrink and `calc_text`'s
    483 M-node image would not fit either. Spending 6 minutes and ~10 GiB to
    confirm an arithmetic consequence of a measurement already in hand was
    judged not worth it against the round's remaining budget; it is a ten-minute
    job for whoever wants it.

  ### The three decisions, in the order they matter

  1. **The layer.** Candidate 1 (guard on "under a quotation", one bit in the
     merged `conv::Env` set by the `Box` rules) versus 2 and 3, both declined on
     reading. This decides whether stage 2 exists at all. See the stop entry.
  2. **Whether stage 2 is worth landing even if (1) is answered.** On the
     measurement: it is not, *by itself*. The per-layer ratio is unchanged to
     three digits, the seconds go the wrong way, and the RSS win is single-digit
     percent. Its value is as the **syntax stage 3 needs**: the win requires the
     un-reduced type to reach `build_fields_skel`, which means not reading the
     constructor's type out of `spine(&whnf(expected))` — §5 candidate 3. Stage 2
     without stage 3 buys a constant; stage 3 without stage 2 has nothing to
     write. That pairing is the finding the coordinator should design against.
  3. **§4.4's deletions** (6 419 dead lines) as their own commit, with the
     measured "zero on the default path" recorded rather than the ×3.5–4 §4.4
     quotes, which is a fired-item number.
- 2026-09-20: Implementer, **stage 2's gate results, verbatim.**

  ### `scripts/test` — full, on this tree, spike off

  ```
  == suite: 2835 passed, 0 failed, 5 ignored ==
  ```

  Not INCOMPLETE, and the **same count as stage 1b's gate**. So the readers
  audit, `Cx::quoted`, the four emitters and the kernel's guard relaxation break
  nothing on the default path — which they must not, because with the spike off
  `Cx::emits_at_forms()` is constantly false, no `@` form is constructed, and
  every arm `spelling.rs` adds is unreachable. `showcase_gate` and the x86
  certificate gates are inside this run.

  ### `calc_text`, the two readings that share a box and a day

  The suite's own `showcase_gate`, spike **off**:

  ```
  calc_text    ok    536.1 s wall    516.5 s cpu    9.8 GiB peak
  ```

  `HEATHER_AT_SPIKE=1 scripts/showcase check calc_text`, minutes later on the
  same box:

  ```
  docs/showcase/calc_text.hthr: ok
  calc_text    ok    541.2 s wall    545.3 s cpu   10.1 GiB peak
  == showcase: 1 checked, all ok ==
  ```

  **+5.6 % CPU, +3 % peak, nothing recovered.** (The 516 CPU-s control is itself
  well above `CLAUDE.md`'s 334 — the box is loaded today — which is exactly why
  the control was taken from the same run rather than from the doc.) The file
  still checks with every constructor value, record projection and forded tuple
  written in the checked spelling, which is a correctness result even though it
  is not a performance one.

  **The image node count was not obtained.** `scripts/showcase` has no `--cache`
  flag, and the substitute datum is already recorded: `calc_parser` through
  `heather check --cache` stores **86 MB on both sides**, and
  `conv_shortcut_hits` on `complete_post` moved −0.5 %. The emitted term is the
  same size, so `calc_text`'s 483 M-node image is still over the 256 M decode
  budget and is still refused. **No budget was raised or proposed.**

  ### `scripts/bench --check` — not run, deliberately

  The only kernel edit in this round is `|| at_spike()` inside
  `Tc::computing_layer`, a guard reached **only** by the five `@` rules, which no
  bench fixture generates (stage 1b step 1 turned `wt.rs`'s `at_forms` off by
  default precisely so the fixtures measure the baseline's workload). There is
  nothing on a hot path to regress, and the box has been at load 17–22 all
  afternoon, which `desktop-bench-gate-for-constants` says is not a place to take
  a constant-factor reading. If the spike is dropped — as it should be — the
  kernel is byte-unchanged from `483d355` and the question does not arise.
- 2026-09-20: Coordinator: stage 2's two stops are one finding, and the design is revised again (docs/intro-by-type-design.md §2.1, §2.3, §3.4, §3.5, §4.1, §9 stage 2). (1) The layer: bodies are checked at c, so the restriction is a **side condition on the two box rules** — the payload contains no checked spelling — implemented as one Env bit set by BoxTy/BoxTm and read by the five rules; the code grammar and the recursors stay untouched, δ inside a box is opaque so nothing enters code by unfolding. (2) The exponent did not move behind the spike because the inner Σ layers have no un-reduced spelling (`ctor_ty` is a summand of the reduct). The fix is to write **no annotation** there: the intro annotation becomes `Option`, an unannotated `pair@(a;b)` is checked against the expected `ITy` (its fields' expected types are `Sel`s — descriptions, never spellings) and is NotInferable in inference position like `box`; `fst@(p)`/`snd@(p)` drop their annotation and infer from the receiver. The outermost injection keeps `Some(pre_whnf)` for the one inferring position. Stage 1b's ITy is exactly what makes this possible; stage 2 is now independent of stage 3. The value closures on Pair/Inl/Inr/Fst/Snd become `Option` (no reader reads them, stage 1a's grep). §4.4's deletions are a separate dead-code commit (measured zero on the default path). The instrumented tree is committed with the spike off; the next pass replaces the spike by the rule.
- 2026-09-22: 2026-09-22: Stage 2 landed as designed after the 09-20 revision (docs/intro-by-type-design.md §2.3, §4.1, §4.2 amended). Inner injections, tuples and projections are unannotated; the outermost injection, or a record's tuple root, carries pre_whnf. Readback/mint devices deleted (002bbed). The curve on the probes' own theorem, queries before → after: cp9 2.41M → 662k, qt3 7.97M → 827k, qt5 29.6M → 991k — per layer ×1.25/×1.20 against ×3.31/×3.71, the gate's small constant. qt5 kernel gate 71.2s → 2.4s, peak RSS 9.3 → 2.7 GB. complete_post 3.70M → 662k queries (×5.6; beats the mint's 0.78M, short of an order of magnitude). calc_text gate green at 5.4 GiB peak (9.8 recorded). Item totals still grow ×1.8/×2.6 per layer: the elaborator's transient reduct, i.e. stage 3. Finding: §2.3's box condition leaked through terms pasted into a quotation (a callee's statement copied into app annotations: ir_v1 ret_cert). Fixed by translating ⌊·⌋ at every box site with the eager checker (typing::spell_checked_in_code, untrusted — the box rule re-checks the result). Admitting the checked spellings into code was refused (code equality is syntactic; the branch cannot state the children's types); code's own sharing is filed as [[code-payload-sharing]]. Suite 2868/0 on base 9325800 (last green master: f9fe5ad breaks calc_parser, the owner is fixing it on master).
- 2026-09-22: 2026-09-22: calc_text's semantic image after stage 2: 265.5M nodes (483M before, −45%), still past the unchanged 256M decode budget, so still refused and --only still unavailable on it. The constructor values are no longer the whole of it; the remaining mass has another emitter (candidates: Case/match-lowering annotations, refl endpoints, the inject callers left in component form — forded, indexed, wf). Attribution by emitter is the next pass, before stage 3.
- 2026-09-22: 2026-09-22: Attributed calc_text's 265.5M-node image with a new instrument (HEATHER_IMAGE_ATTRIBUTION=<tsv>, per declaration and per emitted slot, counted by the image writer itself; _BIG=<tsv> dumps each ≥1M-node slot with its application head). App.cod + App.dom are 91% (264M + 67M of the tally); constructor values (PairAt.ty etc.) under 5%. Heaviest: checked_run#body 90M, close_body 32M, finish_text 29M, operator 24M; by callee, trans 66M, selected_of_match 36M, le_trans/cong_cons 11M each. Mechanism, by probe: one Cons at List<Char> costs 1,056 nodes (476 at Nat; Char's representation is spelled inline in the shape), and a two-step calc over it costs 19,370, of which 13,704 are the application annotations. Every node of a trans spine stores its Π components with the earlier arguments substituted in, so each endpoint value is re-spelled about 17 times, and nested applications multiply. Not stage 3's transient reduct. It is the intro-by-type question one former over: an application whose Π is read off the head's inferred type (ITy already has Dom/Cod). Conversion no longer reads the stored annotations (the typed application rule, 09-06, DESIGN.md), which removes the objection recorded in generated-term-oracle-controls-not-convertible.
- 2026-09-22: 2026-09-22: Design pass for the application carrier written, docs/app-by-head-type-design.md: app@(f; a), a sixth checked spelling whose Π is read off the head's inferred type, with a syntactic fast path so that ordinary calls check exactly as today. Kernel readers audited (only the typing rule and conversion's levels read App annotations); elaborator audited (three emitters in application.rs carry the mass; two semantic readers, unification's type-argument prefix and relational_context's carrier; about 50 shape-only readers go through spelling::app_of). Gate: calc_text's image stored under the unchanged budget, and corpus conv misses and kernel gate not up.
- 2026-09-22: 2026-09-22: app@ landed, both stages and every emitter (kernel a471678b, elab 54bb800f; docs/app-by-head-type-design.md §10). calc_text's image tally 362M → 11.4M nodes and it now publishes (warm replay ~1s, --only works); checked_run#body 90M → 0.37M. perf ab vs the stage-1 kernel, every metric separating: calc_parser conv_misses 299k → 58k, kernel gate 27s → 3.3s, peak 1.16GB → 164MB; cp9/qt3/qt5 alike (qt5 peak 2.7GB → 168MB). The app rule's annotation checks were most of the kernel's queries on these files. What is left in the image: PairAt.ty 5.4M (the outermost-injection annotation), Lam.dom, Supf shape/arity, case motives — the next attribution's subject, together with stage 3 and Char's inline representation. Suite 2870/0.
- 2026-09-22: 2026-09-22: Stage 3 (the elaborator's transient reduct) is deferred with no measured subject after app@ — the curve probes' theorems are 118/264/378 ms at 3/…/5 layers with queries +2.4k per layer. Kept open as [[intro-by-type-stage-3-transient-reduct]] because the library will grow deeper towers. The remaining corpus hot spots are filed separately: [[measure-obligation-omega-on-a-written-proof]] (calc_parser's heaviest item is an omega run on a trivial obligation), [[omega-cutsat-lemma-cost]], [[collection-literal-class-per-step-cost]].
