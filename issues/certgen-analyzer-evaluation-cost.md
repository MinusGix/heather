---
title: The in-language analyzers' evaluation cost is the certifying generator's binding constraint
status: closed
labels: [performance,elaboration,metaprogramming,compiler]
created: 2026-08-13
updated: 2026-08-13
---

Promoted out of [[certgen-harness-cost]]'s log on 2026-08-13, because it stopped
being a floor and became a blocker: it is the reason
`docs/certgen-ctor-fields-design.md` defers constructor fields.

> **Fixed 2026-08-13** — `docs/analyzer-evaluation-design.md`; see the log.
> Read the attribution below as the *hypothesis the round tested*, not as the
> answer: the measurement found **no repetition to share**. The walk was
> already minimal; the cost was per rewrite step, in the size of the term the
> rewriter rebuilt. The fix is the kernel's value domain at this seam, not a
> memo table.

**What it is.** Running an analyzer is kernel reduction: `analyzer_app` builds
the application, and `certgen.rs`'s `Reader` drives it with
`whnf_term_delta` **spine-directed** — each `whnf` reduces from the top of the
sub-spine it is about to inspect, and nothing is shared between reductions. The
same is true of the certificate fold (`cert_body` applied to the transcriber's
`Ir`). No elaborator spelling round touches any of it: these are not terms the
elaborator emits, they are terms the kernel reduces at analysis time.

**Why it is now binding, with the shape** (numbers in the 2026-08-13 entry of
[[certgen-harness-cost]]): generating one fixture costs ~1x for the shipped
`Nat` fragment, ~18x for the shipped cross-function `mul`, ~24x for a
constructor with ONE bare field, ~100x for one computed field, ~135x for two
bare fields — and a constructor with two fields, one of them computed, does not
finish inside `scripts/test`'s address-space rail at all. Cost tracks the
payload's STRUCTURE, not the body's size. Two hypotheses were tested and
refuted while attributing it: not the marked code's `Pair`/`Inl`/`Inr` type
annotations (replacing them all with `Unit^0` in the marker pass moved nothing
— and the boxed code is never re-checked, so that experiment stays cheap), and
not the walker's own composition (the identical merge, written as a closed
`refl` in `lib/certgen_code.hthr`, reduces for free). What is left is repeated
unshared reduction of `match`es on `Pre` and `TA`, both `Wf`-lowered.

**Levers, in the order the measurement points at them:**

1. **Memoized or normalize-once analyzer evaluation.** One change at the
   invocation seam (`analyzer_app` + `Reader`), with the whole fragment behind
   it; it would also drop `certgen.rs`'s standing in-language-evaluation floor,
   which [[certgen-harness-cost]] records as the residual no verdict cache can
   touch. Watch the CLAUDE.md memory discipline: whatever replaces the
   spine-directed walk must not normalize a whole `Ir` tree at once.
2. **A smaller `TA`.** `lib/certgen_code.hthr`'s accumulator carries `Pre` and
   `Ir`; the `VOut` narrowing already showed what splitting a payload out of it
   buys at elaboration time, and this is the evaluation-time half of the same
   move. Worth measuring after (1), not before.
3. **Re-probe the fields stage.** `docs/certgen-ctor-fields-design.md` §§2–7 is
   designed, implemented and reverted; §9 says what to re-check first.

**Trigger.** Any fragment feature whose fixtures generate slower than the
shipped `mul`, or a second consumer of the analyzer seam.

## Log

- 2026-08-13: THE ROUND (docs/analyzer-evaluation-design.md), and it CORRECTS this issue's own attribution before fixing it -- which is the finding, because the correction changes the mechanism. Instrumented first, as chartered: counting every Reader::whnf call and every reduce::step_term_delta it spent, on the constructor-fields workload (debug, one thread, 2026-08-13). Generating `peek` -- ONE bare constructor field, 25.4 s -- is 312 reader forces and about TWO THOUSAND reduction steps in total (transcribe 1375, cert_fold 626). There is no repeated sub-spine to memoize: the spine-directed walk was already minimal and forced nothing twice. The cost is PER STEP, ~12 ms averaged, and far worse than the average at the tail: the single most expensive step in peek's certificate fold is ONE ElimWf step taking 2.06 s. Wall inside Reader::whnf accounts for ~99% of a fixture (peek: transcribe 3.83 s + cert_fold 22.40 s of 26.4 s), and the dominant site is the FOLD, not the transcriber, and inside it the Wf eliminator (peek's fold: 274 ElimWf steps = 15.58 s, 242 App = 5.94 s; mul: fold 16.11 s vs transcribe 2.57 s). Why: reduce.rs is a REWRITER -- step_term_delta descends the congruence rules and rebuilds the path, apply_local copies the branch body, and both carry every type annotation, which here are Wf-lowered Pre/Ir/Cert whose shape and arity slots are the largest terms in the library. Each step's output is bigger than its input, so the next step copies more: whnf-sharing-term-growth's pathology, surfacing at the one place in the elaborator that RUNS a program by reduction rather than comparing two terms. A third hypothesis tested and refuted en route, recorded so nobody re-tests it: it is NOT the delta rescope -- the reader had no BodyCache and every unfold shift_global-copied a library body, and wiring Defs::transparent_cached into the rewriter reader moved peek 25.4 -> 26.7 s, i.e. nothing. THE FIX, one seam and no kernel line: Reader is re-instantiated at the kernel's VALUE DOMAIN (heather_kernel::value / eval, shipped by the nbe-conversion round for conversion and entirely public). It holds Rc<TmClo> instead of &Term, forces instead of whnfs, matches Val::Supf/Pair/Inl/Inr/Triv/Zero/Succ instead of the Term of each name, and a field is an Rc clone instead of a term clone. Three properties do the work, all of them the domain's: beta extends an environment instead of copying a branch (the 2.06 s ElimWf becomes one env cell); annotations are TyClos and are never forced, so the Wf slots are carried as pointers end to end; and TmClo's memo gives the sharing this issue asked for -- for free, as the SMALLER half of the win. The one new piece of code is global_app1, which applies cert_body to the transcriber's Ir as a pending Elim::App over its own closure rather than building an application TERM around it: that keeps nbe-conversion-design sec. 7's invariant (no value is ever written back into syntax and re-evaluated) and lets the fold inherit every memo the transcription readback wrote. The frozen-walker rule holds absolutely: lib/certgen_code.hthr's analysis and lib/certgen_cert.hthr are byte-identical across the fix; what changed is how the elaborator RUNS them. MEMORY, the issue's hard constraint: this does not normalize an Ir tree -- Eval::force is weak-head, children stay closures, and the demand order is the same order the spine-directed walk had; the live set is smaller than the terms the rewriter built because its nodes point at shared syntax where the rewriter held copies; and Eval::drive keeps reduction steps off the native stack, so a runaway analyzer returns OutOfFuel where the rewriter recursed. Measured, not argued: the whole acceptance workload (library prefix + all eight fixtures) peaks at ~54 MiB RSS and runs inside scripts/test's OWN ulimit -v 4194304. Fuel: READ_FUEL stays DEFAULT_FUEL but is now per FORCE of a shared graph rather than per whnf of a sub-spine, i.e. strictly tighter; measured headroom is three orders of magnitude (worst single force 831 steps, whole generation ~2050, budget 1,048,576). NUMBERS, per-fixture generation, debug, one harness, one session, 2026-08-13 -- before (rewriter) -> after (values): add 1.3 s -> 28 ms; mul (the shipped fragment's most expensive fixture) 19.9 s -> 28 ms; seven 0.44 s -> 20 ms; is_zero 1.9 s -> 28 ms; peek (one bare field) 30.2 s -> 27 ms; PSome(Succ(k)) (one computed field) 109.5 s -> 32 ms; BSome(k, k) (two bare fields) 137.7 s -> 29 ms; BSome(k, Succ(k)) DID NOT FINISH at 16 GiB -> 32 ms. The gate is met with three orders of magnitude of headroom, so the parked constructor-fields feature LANDED in the same round (see certifying-generator and the design doc's sec. 9). LEVER 2 (a smaller TA) IS NOT TAKEN and is no longer worth taking: it was to be measured after lever 1, and after lever 1 there is nothing to measure it against. It stays available, unspent. Suite 1493 -> 1494 (the new perturbed-library field-merge control; the fields feature's own coverage is inside certgen_nonnat.rs's two existing tests, widened): 1494 passed, 0 failed. scripts/bench --check: 18 comparisons within thresholds -- the kernel is untouched, so any movement would have been a mistake. RECOMMENDED DISPOSITION: close. The defect is fixed at the seam it was filed against, both named levers are resolved (one taken, one retired with a reason), and the residual it inherited from certgen-harness-cost is gone rather than re-homed.
