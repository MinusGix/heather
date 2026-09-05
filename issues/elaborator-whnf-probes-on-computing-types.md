---
title: Elaborator whnf probes run the small-step reducer on computing types
status: closed
labels: [elaboration,performance,kernel,conversion]
created: 2026-09-05
updated: 2026-09-05
---



`Elaborator::whnf` is `reduce::whnf_type_delta`: the kernel's
substitution-based small-step reducer with every definition transparent. It
is the right tool for the questions the elaborator asks -- "is this a Π", "is
this a universe", "which inductive is this" -- as long as the answer is a few
steps away. On a type that *computes*, it is not: reducing
`El^0(Le(x, dot(row, atoms)))` unfolds `Le` at `Int` to a match on
`dot(row, atoms)`, and reaching a constructor there means evaluating the dot
product -- `dot`, `scale`, `combo`, `basis`, `zeros`, `add`, `mul` -- by
`apply_local`, each step copying the row and atom lists and recomputing their
free-variable bounds (`bounds::Cache::compute_term`, half the samples). One
such whnf cost 1-7 s on the 7-atom certificate of
[[omega-per-goal-elaboration-cost]], and the answer was always "stuck".

Two probes did this on every argument of a generated certificate and were
made cheap in that round (2026-09-05): the universe probe in the checking
fallback now skips an `El` at level 0 (no `El^0` reduces to a `Ty`), and
`ctor_here_expected` stands down on a qualified name whose qualifier names no
inductive. That removes the two paths a certificate takes; the mechanism
remains. Any remaining `self.whnf(cx, expected, …)` probe -- the `Var` arm's
erased-universe check, the expected-type harvest, `anonymous_ctor_expected`,
an *unqualified* name reaching the constructor route -- pays the full
computation whenever a proposition's head is a `fn … → Type` over a computing
argument. `Le`/`Lt` at `Int` and at `Nat` are exactly that.

## Levers, when a workload shows one of the remaining probes

- **Value-domain whnf.** The conversion checker already evaluates in the value
  domain and is not pathological on these types (the kernel gate on the same
  certificate is ~0). A `whnf` that evaluates to a value and reads back only
  the head would make every probe cheap at once. Cost: the elaborator anchors
  on *spellings* in places (`unspell_here`, `wf-shape-code-design` §3.3), so
  a readback that respells has to be audited site by site.
- **Head-shape pre-tests.** The level-0 test is one instance: decide from the
  unreduced type what the reduct *cannot* be, and skip. `expected_ind` on a
  `Type::Pi`-free `El` whose code is a `GlobalTm` application of a `fn`
  (not a lowering) is another candidate.
- **Memoize per attempt.** The same `Rc<Type>` (a lemma binder's substituted
  domain) is probed two or three times along one checking path; a pointer-keyed
  memo on `SemanticOracle::whnf_type` would bound repeats, not the first hit.

## What it assumes from elsewhere

- **[[omega-per-goal-elaboration-cost]]** owns the certificate workload that
  found this and the two probe fixes; assumed here only that its reproducer
  (`cutsat_left_cut`) exercises `Le` at `Int` over a computing row.
- **[[bounds-metadata-taxes-one-shot-checking]]** owns the bounds memo's cost
  model; assumed here only that a miss recomputes bounds over the whole fresh
  subtree, which is what makes a substitution step O(term) here.
- **[[conversion-cost-at-large-values]]** owns the value domain's constant;
  assumed here only that conversion, not reduction, is what it measures.

## Log

- 2026-09-05: Precedent for the value-domain lever: [[whnf-sharing-term-growth]] closed by moving conversion to the value machine, and its 2026-08-13 entry records a second consumer -- certgen's analyzer readback moved from reduce::whnf_term_delta to eval::Eval::force. A head-only whnf for the elaborator's probes would be the third.
- 2026-09-05: Lever 1 landed, elaborator-side (SemanticOracle::whnf_type / whnf_term, crates/elab/src/oracle.rs). Shape: the value machine DECIDES, the small-step reducer SPELLS. When the head could compute at all (an El/Vec/Fin over an eliminator spine or a global; a bare variable or a canonical code skips the probe), eval::whnf_value_ty runs first in a fresh ValueArena with the same transparent Defs and fuel. A neutral head means the probe's answer is 'no former', so the reducer gets a fixed small step budget (STUCK_SPELLING_STEPS) for the stuck spelling and past it the input type itself is returned -- convertible to every reduct, and what the unifier/diagnostic consumers read before the probe anyway; a cheaply reached stuck form (RelId -> Id, Lt -> Le) is therefore spelled exactly as before, which is what the two solve_from_expected consumers of the reduct need. A former with sub-structure means the reducer runs as before (there is no readback from the value domain, by design: docs/nbe-conversion-design.md section 7, which now lists this consumer). A former with NO sub-structure (Nat, Ty l, Unit, Empty, sEmpty, and their codes at the term level) is read straight off the value -- the shape of a decidable proposition that computed, where the reducer would redo the computation by substitution to spell four bytes. Neither the reference-unspell in Elaborator::whnf (wf-shape-code-design section 3.3) nor any caller changed; the site-by-site audit of the 46 whnf callers and 13 whnf_tm callers found that on a neutral result they either match a former and fail, hand the result to unify_ty (the budget keeps their cheap reducts), or display it (the original spells better). whnf_term got the same wrapper because matching's motive exposure hands an El's encoding to it right after the type probe. MEASURED (release, quiet machine, scratch --cache-dir so the library is freshly checked; note the default cache dir silently replays lib images and prints no phases): omega closure 13 s -> 13 s, top-level goal-check sum 0.87 s -> 0.87 s; serial function_ir_x86_alu target 90.4 s -> 89.1 s -- i.e. with 9f36349's two guards in place no live workload still hits the class, and the probe's extra cost is invisible. THE MECHANISM ITSELF, shown by temporarily removing both guards on the same omega closure: goal-check sum 73.2 s -> 5.8 s, largest goal 29.0 s -> 1.4 s, wall 95 s -> 28 s. The guardless residual (5.8 s vs 0.87 s guarded) is the spelling budget: 64 substitution steps per probe on a certificate-sized term is not free, so the guards stay as the constant-factor fix and this round is the mechanism fix; nothing tunes the budget on that datum (one deliberate perf round). Hand-built reproducers of the named remaining probes (result-only implicit at a Le goal, a Lt argument at a Le parameter, trivial at a closed dot-product bound) were all sub-second on the old oracle too -- the pathology needs the certificate's context, which is why the guardless run is the demonstration. Residual, named: a former WITH sub-structure reached only after heavy computation (El of a code chosen by a computed match) still pays the reducer, and now the value evaluation too; no workload shows it. Tests: oracle.rs unit tests pin all four paths (cheap stuck = reducer spelling; stuck past budget = input; closed former from the value, reducer agreeing; structured former = reducer spelling; terms likewise).
- 2026-09-05: Final verification (2026-09-05): full scripts/test green -- 2360 passed, 0 failed, 5 ignored -- at HEATHER_TEST_JOBS=4. The default job bound's first run came back INCOMPLETE with function_ir_x86_alu and function_ir_x86_conditionals both at the 300 s CPU rail under contention (the pre-existing rail-hugging [[parallel-test-memory-headroom-under-heavy-prefixes]] records; each passes alone in ~90 s on this tree). Closing: the class -- a head-shape probe paying a computation to learn 'stuck' -- is gone by mechanism; the guardless demonstration above is the evidence, and the two 9f36349 guards remain as constant-factor pre-tests.
