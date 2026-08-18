---
title: The LGG's mismatch diagnostic prints raw kernel terms, unreadably
status: closed
labels: [frontend,diagnostics,elaboration]
created: 2026-08-18
updated: 2026-08-18
---

`crates/elab/src/lgg.rs`'s `mismatch` builds its message with `{x:?}` on four
kernel `Term`s — the two sides at the differing position and the proof's two
endpoints. At a `Nat` goal that reads fine. At a **lowered inductive** it is a
wall of `inl[0,0](Σ[0,0](Unit 0). …)` several thousand characters long, four
times over, and the one thing the reader wants — *which subterm of my goal did
not match my proof* — is not recoverable from it.

Found while diagnosing [[congruence-by-anti-unification]] (2026-08-18): every
`cannot generalize` failure in `lib/std/int.hthr` and `lib/std/list.hthr`
produced one, and reading them required a script to slice the string.

`Debug` on kernel terms is budget-bounded and that is working as designed — the
bound is what stops this being an OOM. The defect is that a *user-facing
diagnostic* uses `Debug` at all.

## What it assumes from elsewhere

- `crates/elab/src/display.rs` can spell a `Type` (`spell_type`) and has no
  term-level counterpart. Assumed here: only that a term printer does not exist
  today, so this cannot be fixed by swapping one call.
- **[[display-inductive-type-arguments]]** owns what a lowered instance can say
  about itself. Assumed here: only that it is the same underlying gap — a
  lowered term does not remember its surface spelling.

## Shape of the fix

Two options, and the cheaper one may be enough.

1. **Say less.** The message does not need the four terms. It needs the
   *expected type* (which `spell_type` can already render) and a description of
   where the walk stopped — a path, or the head former of each side. Cheap, no
   new printer, and strictly more useful than the dump.
2. **A term printer.** The real fix, shared with every other diagnostic that
   currently cannot name a term, and the thing a lowered-inductive-aware
   display has to do anyway.

Take (1) as an interim only if (2) is not otherwise scheduled.

## Log

- 2026-08-18: Paid, and by shape (2) rather than the interim (1) — the costing said the real fix was already three quarters built.

**The costing.** `display.rs` has had a complete term walk since it was written: `Speller::tm` covers variables, numerals, λ, calls, pairs, constructor values, codes and globals, because an `El`'s payload, an equation's two sides and a call's arguments are all *terms*. What did not exist was an **entry point** at a term — `spell_type` is the only public door, and a diagnostic holding a bare `Term` therefore had no option but `{:?}`. The whole of the missing printer was `spell_term_clean`: one function, the same budgets, the same per-node fallback, the same abandon rule. So (2) landed and (1) was never built.

Only the *clean* flavour is exposed (no raw node at all). A diagnostic holding a bare term is making a claim about it, and a half-spelled lowered inductive is the `inl[0,0](Σ[0,0](Unit 0). …)` wall wearing surface syntax — the lesson [[check-fallback-discards-expected-type]] already recorded for types. A clause that cannot be said cleanly is not said.

**The other half was the solver.** `lgg.rs` is deliberately standalone (no `Cx`, no elaborator), so it cannot spell anything. It now fails with data — `Mismatch`: the head formers walked from the goal's root to the stopping node, the two sides' formers there, the two subterms, and the binder depth. The path costs two lines: `tm`/`ty` push their former on entry and pop only on success, so at a failure the stack *is* the path. `Mismatch`'s `Debug` is its `Display` on purpose — a derived one would print the two kernel terms, which is the wall this type exists to stop, and `.expect()` in a test is a `Debug` user.

The elaborator renders it (`Elaborator::cong_mismatch`): position, then the goal, then the endpoints, each clause dropped rather than half-said. The two sides at the stopping node are spelled only when they `strengthen_tm` out from under the binders the walk descended — a subterm mentioning the λ's own variable has no reading in the reader's context, and inventing one would misname their variables.

**What it still cannot say, measured rather than assumed.** At a *recursive* declaration (tier 1) the goal does not spell: the value is `supf` whose shape annotation is a generated global, and `tag_of` reads the tag only out of an inline `Wf`/`Sum`/`Sigma`. The one-lookup route was tried and does not reach — `unspell_here` inverts a `#tycode` reference, and this is a *shape* code — so recovering it is [[display-inductive-type-arguments]]'s inversion, not a display one-liner. At such a goal the message keeps the position, the endpoints and the absence of the wall, and simply omits the goal clause. At tier 0 the goal spells (`The goal is \`same(a) = Red\``).

Tests in `crates/elab/tests/congruence_lgg.rs`: `the_mismatch_at_a_lowered_inductive_is_readable` (a `Tree` goal — the live customer's shape; asserts the position, the endpoints, that none of `inl[`/`inr[`/`Σ[`/`«`/`El[` appears, and a 600-char bound where the walls ran to thousands), `the_diagnostic_states_the_goal_where_it_spells`, and `a_mismatch_under_a_binder_still_names_the_position` for the clause that must degrade rather than lie. A `Nat` goal would have hidden all four assertions.
