---
title: Nested patterns and a default arm in match
status: closed
labels: [frontend,syntax,elaboration]
created: 2026-07-31
updated: 2026-08-05
---

Two sugarings, one round, both straight from lib/ir_v1.hthr
([[ir-simulate-design]]):

1. **Deep patterns.** `step_letmatch` and `step_loopiter` are towers of
   single-level matches; what they mean is one decision tree:

       match lookup(env)(scrut) {
           NoneV => Stuck,
           SomeV(VCon(tag, fields)) => ...,
           SomeV(other) => Stuck,
       }

   Elaboration is the classic pattern-matrix compilation into the nested
   single-level matches written by hand today — elaborator-only, no
   kernel change, motives synthesized per level exactly as now. The
   interaction to watch: patterns on a RECURSIVE argument position must
   keep the self-call guard's view of the binder (the guard matches
   syntactically — [[guard-matches-self-calls-by-term]]), so v1 can
   simply reject deep patterns in the decreasing position.

2. **A default arm.** `pick_arm` in ir_v1 writes seven identical
   `... => NoArm` arms because every constructor must appear. A `_ =>`
   arm (no binders, appears last, expands to the missing constructors'
   arms with the body duplicated) removes the worst of it. Notable: the
   duplication is per-arm term copies, and [[simulate-conversion-cost]]
   says term size is billed at conversion — so expansion should reuse
   one shared body where the motive allows rather than eight copies.

Lean-style equation definitions (`| Ret(rs) => ...` at the fn head) are
the same machinery worn as declaration syntax; fine, but it is sugar on
sugar — record here, do not gate on it. The more radical end of that
thought is [[case-algebra-definitions]].

## Log

- 2026-08-05: LANDED, both sugarings (managed round; docs/nested-match-patterns-design.md). Elaborator-only, no kernel change: one idempotent preprocessing pass (crates/elab/src/patterns.rs, ~470 lines) in front of the three entry points into arm-shaped work, rewriting surface arms into surface arms — every lowering below it is called with the arm shape it already accepted. Grammar: Arm.binders becomes Vec<Pat> and Arm gains `default: bool` (crates/syntax/src/ast.rs, parser.rs's new `pat`/`pat_args`); `_` already lexed as an identifier, so the default arm steals no token. Deep patterns compile by the classic pattern matrix — leftmost-non-wildcard column, first-match rows — and the *key finding* is that the two features are not independent: the compiler needs NO type information at any level because it emits a `_` arm for the fallthrough and lets each generated level expand its own, at the point where its scrutinee's type is known. Sharing (§5): a default body is elaborated once and parked in an Alias when the motive does not mention the scrutinee; measured as one elaboration always, one goal always (`_ => ?g` over three constructors raises exactly one, asserted off UnsolvedGoals), and one shared interior node in the emitted term when the body is closed — the head is re-allocated per arm because alias resolution returns a Term by value. A body that must be copied and contains a ?goal is a named error instead of the hole machinery's `internal:`. Boundaries: (a) §6's decreasing-position rejection fires on 'descends on a parameter AND an arm mentions the declaration's own name' — the first implementation refused on the parameter alone and that was measured useless within minutes, since `fn f(o: Opt<Res<A>>)` matching deeply on `o` is the feature's commonest shape and is not recursive; `_` is exempt entirely, which is what makes pick_arm's rewrite legal in the decreasing position. (b) §7: a deep pattern at an IndexVar field of an indexed/forded family is refused by name — that binder is the arm's index pattern variable, aliased to a projection of the index and read by the guard's rebind, not a value; payload fields of the same families are unrestricted and tested. (c) §10.2, inherited not introduced: a nested match on a field has a non-dependent synthesized motive, because a field binder is an alias and so a projection rather than a Var — deep patterns are a programming convenience in v1, not a proving one. (d) §8: a deep match may carry `match h : e`, and the equation is about the OUTER scrutinee refined to the outer constructor only; sharing is unavailable under a convoy by construction. `split` inherits both (`on _ := b;`, told from `on _: P :=` by one token). One live defect found, by axis 1 done properly: the generated column names shadowed each other across levels (a per-call counter starting at zero, re-run on every level the pass emits), so a leaf referring to a column two levels up silently got the wrong one — a WRONG ANSWER, not a rejection, and perfectly well typed since both columns have the same type. Only a literal-scrutinee test that must *compute* could see it; the fix starts the counter past every #p<k> visible in cx.names, cx.aliases and the arms' own patterns. Acceptance: crates/elab/tests/nested_match_patterns.rs, 26 tests (full suite 1067 -> 1093, 0 failed), axes 1/2/3/4/6 with the 2026-08-05 dependent-motive refinement, a nonzero-level case, and 11 negative controls. lib/ir_v1.hthr: all THREE hand-written towers rewritten (pick_arm 8 arms -> 2; step_letmatch 2 nested matches -> 1 deep row + _; step_loopiter 4 nested matches, 11 arms -> 3 rows + _), net -11 lines, every downstream proof unchanged, capped release check 60.3/60.0 s -> 59.6/59.4 s — inside the noise, which is the predicted result. Residue filed: [[match-arm-redundancy-warning]] (unreachable rows and redundant `_` are silent; both want a warning channel that does not exist) and [[diagnostics-name-the-written-form]] (a non-exhaustive inner column reports at the outer match, the second instance of the wart split's round recorded). Not built, as briefed: Lean-style equation definitions at the fn head.
