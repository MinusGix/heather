---
title: LocalCtx/GlobalCtx are eagerly cloned Vecs; consider a shared-spine representation
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-08-01
---

Every profile from the [[subst-visits-closed-subtrees]] round (2026-07-31,
`code/check-identity-recursor` and neighbors) shows `Vec<CtxEntry>` and
`Vec<GlobalBinding>` clone/drop at a steady ~5–8%, independent of that
round's changes: `LocalCtx`/`GlobalCtx` are plain `Vec`s, and typing/
conversion clone them wholesale to extend by one entry (binder descent
does this constantly).

Candidate: an `Rc`-shared spine (persistent snoc list, or `Rc<[Entry]>`
with copy-on-extend), so extending by one is O(1) and dropping a derived
context frees one cell. Contained representation change — contexts are
*outside* the term language, so no substitution/conversion rule is
touched — but it has real surface: `LocalCtx` appears in terms
(`CodeTy`/`CodeTm`/`TyPi`/letbox/recursors) and is compared structurally
by conversion at boxed types, so the representation must keep cheap
structural equality, and `PartialEq` cost is on the conversion path.
Indexing direction matters too: entries[0] is outermost, `LocalVar` 0 is
innermost — a snoc spine matches variable lookup but reverses iteration.

Trigger: a profile where context clone/drop is a top-5 line *after* the
schema round ([[schema-construction-caching]]) lands — much of today's
context cloning is inside the fresh telescope construction that round
would eliminate; measure again before paying the churn here.

## Log

- 2026-07-31: Post-definitions profile of release heather check lib/ir_v1.hthr (~2.1s, perf 999Hz): Vec<GlobalBinding>::clone is the #1 self line at 12.8%, plus GlobalBinding drop glue 3.5% -- Psi clone+drop ~16% combined, ahead of everything else. The clones are Env construction (typing.rs:183,202,216,233,248,266; conv.rs:168) deep-cloning Psi, and the definitions round made Psi strictly bigger (every fn is now a bodied binding), which is why this surfaced. Note the split this reveals: the wait-for-schema-round caveat in the body applies to LocalCtx telescope churn (CtxEntry clone+drop ~5.7% here), but the Psi half is different -- Psi is append-only at declaration granularity and never extended mid-check, so an Rc-shared GlobalCtx (clone = refcount bump) is a contained mini-round separable from the shared-spine question, with none of the structural-equality surface (Psi does not appear in terms). Trigger for the Psi half: fired.
- 2026-07-31: Psi half done: GlobalCtx.bindings is now Rc<Vec<GlobalBinding>>, so cloning Psi is a refcount bump and the Env clones at every binder descent (typing.rs/conv.rs push_entry, in_ctx, and the public entry points) stop deep-copying the declaration list. Appends pay copy-on-write via GlobalCtx::push/extend, which is once per declaration; elab's goal_psi/refresh_delta_psi short-circuit to sharing Psi's Rc when goal_base is 0. Release heather check lib/ir_v1.hthr: 1.944s -> 1.475s (min of 3, same machine), a 24% cut; scripts/test green, scripts/bench --check clean (94 comparisons, no move -- the kernel benches run tiny Psis). Post-round profile: Vec<GlobalBinding>::clone and GlobalBinding drop glue are gone from the report entirely; the new #1 block is level arithmetic (Level::count 6.2%, normalize 3.2%, Level drop glue ~4.7%, BTreeMap dying_next 1.7%, BTreeMap eq 0.8%). THIS ISSUE STAYS OPEN for the Gamma half: LocalCtx/CtxEntry clone+drop is still ~4.6% (Vec<CtxEntry>::clone 3.2%, its drop 1.4%) and its trigger -- a profile after the schema round -- has not fired.
- 2026-08-01: **The Gamma half's trigger has effectively fired, and the schema-round caveat does NOT apply to the workload that fired it.** Perf on release `heather check lib/ir_v1.hthr` (~34s, 500Hz flat + fp call-graph rebuild for attribution): `Vec<CtxEntry>::clone` is the #1 self line at 5.3% with its drop at 2.6% (~8% combined). Immediate-caller counts over the raw stacks: 634/858 clone samples come from `conv::Env`'s derive(Clone) (i.e. `conv.rs push_entry`/`with_layer` cloning the whole Env per binder descent), 191/858 from `typing::Env::push_entry`, 27 from `Env::new` — telescope construction is nowhere in the attribution, so waiting on [[schema-construction-caching]] is not justified for this workload (it may still be for `code/check-identity-recursor`). Shape note for the round: conv.rs's own doc comment says the entries `push_entry` pushes are fillers ("nothing reads it but the length and the base"), but `gamma` IS read by index and by reference elsewhere (`conv/dom.rs:1170`, `conv/dom/values.rs:578`, `LocalSubst::id(&gamma)`, `branch_specs`, `wf_step_telescope`, the syntactic stepper's `step(&cur, &env.gamma)` loops), so an Env-local suffix representation has to keep real entries reachable and must price the materialization at those `&LocalCtx` boundaries — the syntactic-stepper loop being the one to watch.
