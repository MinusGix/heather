---
title: Move the declaration generators out of Rust and into the meta layer
status: open
labels: [metaprogramming,elaboration,design]
created: 2026-07-26
updated: 2026-08-11
---

Speculative / direction issue, not scheduled. Filed 2026-07-26 in the
priority discussion so the ambition is written down rather than assumed.

Every derived artifact today is **Rust that emits kernel terms**: the tier-0
and tier-1 lowerings, the recursor, no-confusion (disjointness and
injectivity), the `Wf` guard, the container schemas (`tab_cong`, `map`,
`tabulate`), `Acc`'s fording if it were ever generated. They are kernel-
checked, so they are not *trusted* — but they are not *in the language*
either. The project's thesis is a metaprogramming calculus with a modal
layer, and the kernel already carries it (`□(Δ ⊢ T)`, `letbox`, the code
recursors, `Trm_c`/`Typ_c` globals). The generators are the most obvious
thing that should eventually live there.

## The pull

- One less language. A user-written `deriving`-style generator, an
  optimization pass and a `Compile` instance are all the same kind of object
  ([[certifying-generator]], [[compile-typeclass-design]]), and today only
  the last of the three could be written by a user at all.
- It is what [[lsp-from-the-meta-layer]] and [[setoid-auto-lifting]] both
  assume exists.
- The elaborator stops being the place where language features live — the
  general complaint that motivated this priority round.

## The drag

- It wants [[surface-records]] and [[surface-polymorphism]] first: a
  generator is a generic function returning a record of code.
- It wants the implicit quotation / modal surface
  ([[surface-syntax]] round 2), which is a real syntax round on its own.
- [[box-synthesis-gap]] is closed but its conclusion binds here: elaborated
  code must emit `letbox`, not β-redexed meta-functions, and a generator
  written in-language is exactly the code that has to obey it.
- Migration is not all-or-nothing, and the honest first step is probably
  *one* small derived artifact (injectivity at a single field, say) written
  in-language and cross-checked against the Rust one, rather than a port.

## The question to answer before scheduling

Is the meta layer expressive enough to write the tier-1 lowering as it
stands — the `Wf` arity function, the code-valued predicates by large
elimination, the `Fin`-indexed ih — or does an in-language generator need
kernel/layer features that do not exist yet? That is a reading exercise
against `docs/delam/07` and `crates/kernel/src/rec.rs`, not a code round, and
it is what would turn this from "maybe" into a plan.

## Log

- 2026-07-27: Promoted from 'direction, not scheduled' to the ONLY route to a level-generic library, per [[surface-universe]] section 4. Checked against ch. 04 and the kernel rather than assumed: there is no encoding for universe-polymorphic functions (ch. 04 line 652) AND no code of any instantiation either, because UApp requires meta_layer (typing.rs:1425) while BoxTm checks its payload at Layer::Code (typing.rs:626) -- a layer-m term cannot sit inside a box. What IS well-formed is the flip, a polymorphic function returning code: 'forall l. box(|- T_l)', because code types live at level 0 (typing.rs:591,599) so UPi's body-at-its-declared-level requirement is met, and in_ctx preserves the universe context (typing.rs:275-277) so the boxed code may mention l. Ch. 04 (581-582) says that is WHY the layer-m restriction exists. Consequence for this issue: a universe-polymorphic library function is not compilable as such -- its generator is, once per level -- so 'fn f<l>' at the surface must elaborate to a layer-m generator plus auto-instantiation at each concrete level used. Caution: layers are not freely crossable (strict order and code promotion is a real operation), so 'a definition that moves between layers automatically' is a surface illusion the elaborator maintains and must be able to fail loudly.
- 2026-08-02: The expressiveness reading is done (ch. 04 modal fragment + 07's neutral laws + the full generator catalogue: elab/{inductive,wf,vec,indexed,code}.rs and kernel rec.rs — note the issue's 'rec.rs' is the code-recursor branch table, not the lowering; the lowering lives in crates/elab). Verdict: MISSING FEATURES, ENUMERABLE — the tier-1 lowering as it stands is not expressible at layer m, but the gaps are specific, and one whole family plus the certifying generator's v1 fragment ARE expressible. What works: the recursors are full structural recursion over code with sub-code recoverable (branches re-box their globals, 04:1164ff), motives may be Nat-valued, code-valued, or large (Ty l), code emission via box/letbox/splice-under-binders all checks; and the kernel's extension formers are layer-GENERIC (typing.rs:518-583), so layer m has Sigma/Sum/Wf/Vec/Fin — the paper's Nat-only bookkeeping gap does not apply to our kernel. The vec.rs schemas (map/tabulate/tab_cong/nth) consult no oracle and no declaration table — they are the honest first in-language artifact, as this issue guessed. Four blockers for the rest, each a real round: (1) GLOBAL REFERENCES ARE OPAQUE — no recursor branch for u^delta/U^delta, neutral by 07's stuck laws; and since the simulate-conversion-cost round made the elaborator emit Psi-references instead of inlining, real library code is exactly the shape the recursor cannot see through; a branch for globals (an intensional-analysis extension with ch. 07 obligations) or elaborator-side inlining-for-analysis is required for any generator over real fns. (2) NO GENERATION-TIME ORACLE — the Rust generators branch on whnf/conv against full Psi (projection's Sigma-peeling inductive.rs:2237, build_inj's dependent-field conv_type :2560, motive_head wf.rs:260); layer m has no reduce/convertible primitive on code, and manual recursor self-calls are stuck until concrete. (3) NO CODE EQUALITY — the Wf guard matches self-calls by shifted syntactic equality (lib.rs:1930-1937), strengthen occurs-checks by subst-then-compare (vec.rs:39-52); nothing at layer m decides equality of code. (4) NO CONTEXT COMPUTATION — Delta is a parameter, never a scrutinee (CApp wants a concrete context, 04:1086-1088), while every lowering is scope-indexed (the ubiquitous depth d + shift_local(d)); code cannot be built under a computed number of binders, so per-declaration case trees and n-ary-for-runtime-n artifacts are out of reach; per-arity monomorphization (what the surface does anyway) is the workaround. Also confirmed en passant: no code of UPi (level-generic libraries stay generator+instantiation, matching the 2026-07-27 entry), and rec.rs itself is recursion over the SIGNATURE (three binder namespaces, above-k shifts) — it stays Rust under any plan. Sequencing consequence, now measured rather than guessed: the certifying generator's v1 Rust fragment (structural self-recursion, no cross-function calls) coincides almost exactly with what elim^Trm could analyze (elim_N + constructors + variables, no global refs) — so the Rust transpiler is a faithful prototype of the in-language generator's natural first scope, and the in-language migration order is: a vec.rs schema first, the fragment transcriber second, guard/inj-style generators only after kernel rounds for (1)-(3).
- 2026-08-02: The migration's opening move landed ([[in-language-map]]): map_code in lib/vec_code.hthr, evaluated by the elaborator, convertible with the Rust schema. One refinement to the 2026-08-02 verdict from the implementing round: the verdict's 'code emission via box/letbox/splice-under-binders all checks' holds for TERM splices only — TYPE splices do not exist for pure quotation at all, because a TyPi-bound type is layer p and the binding invariant excludes it from layer-c payloads (annotations included). Polymorphic templates are closed code binding their types via Pi over Type<0>; type-code arguments (CodeTy locals + LetBoxTy) become useful only with the code recursors, i.e. they belong to the analysis stages gated by blockers (1)-(3), not to the quotation stage. The migration order stands: fragment transcriber next.
- 2026-08-11: Migration step 2 LANDED (2026-08-11, managed round): the fragment transcriber is in-language — the analysis stage's opening move, docs/certgen-transcriber-in-language-design.md; narrative on certifying-generator. One correction to the 2026-08-02 verdict, measured at the kernel: 'elim_N + constructors + variables' overstates the variable case. elim^Trm WALKS variables but cannot DISTINGUISH them — tm_var's telescope takes the variable as a layer-v global (rec.rs), one branch body for every variable at once, and transcription IS the occurrence-to-slot map. A FIFTH blocker beside (1)-(4), narrower than (4): not 'no code under computed binders' but 'no reading a de Bruijn index out of code at any fixed number of binders'. Closed Rust-side by the marker convention (the elaborator renames occurrences to closed level-carrying beta-redexes before boxing — mechanical scope resolution, no fragment knowledge); closes in-language when surface delayed substitution and meta-layer re-entry exist. What the step also bought the meta slice, recorded in meta-def-registration-design sec. 11: analyzer slots (data-returning meta fns registered by whole-signature convertibility), ordinary program-layer parameters/results on a meta fn, globals nameable from a meta body, and the MetaDef staleness fix. Next per the order: guard/inj-style generators still wait on kernel rounds for blockers (1)-(3); the analysis surface (match code, constant motives, 52 branches with a mandatory default) now exists for whatever comes.
- 2026-08-11: Migration step 3 (2026-08-11): the analysis surface widened to TYPES — match code over a TyCode scrutinee emits ElimCodeTy (same 52 branches, constant motive), TyCode(g) is an ordinary meta-fn local, and the first type-analyzing artifact is certgen's in-language signature checker fed by the pull reflection primitive ([[fn-reflection-for-analyzers]]; docs/fn-signature-reflection-design.md). One correction to the transcriber design's deferral table: sub-code binders and dependent motives did NOT have to arrive with it. Blockers (1)-(3) stand; the opaque-globals round now has its interface pre-cut.
- 2026-08-11: Blocker (1) DISCHARGED for analyzers (2026-08-11, opaque-globals round; docs/opaque-globals-analysis-design.md): global references stay opaque INSIDE code -- the book's blocking is deliberate (ch. 06 neutral grammar, following hu2024layered) and no recursor branch lands -- but the pull reflection API now lifts opacity per name at the boundary: fn_body_code hands analyzers marked closed code with callee markers (convention 3) and the tag->name table, and mul-via-add transcribes in-language byte-identical to Rust v2. Blockers (2) (no generation-time oracle) and (3) (no code equality) stand; a generator needing callee BODIES mid-walk rather than per-name pulls would be the first customer for anything more.
