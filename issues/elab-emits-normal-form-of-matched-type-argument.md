---
title: The elaborator emits the normal form of a type argument it normalized to decide a match: 3.5× per combinator layer, written down
status: open
labels: [elaboration,representation,performance,design]
created: 2026-09-16
updated: 2026-09-20
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
