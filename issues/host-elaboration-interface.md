---
title: Expose a scoped host elaboration interface usable from Heather
status: open
labels: [metaprogramming,elaboration,design]
area: tactics
milestone: [tac-host-interface, hih-passes]
created: 2026-09-07
updated: 2026-10-22
---

Own the public interface between user metafunctions and the active compiler:
scoped name resolution, checking syntax against expected types, diagnostics,
instance lookup, and checked declaration publication. Initially implemented by
Rust, the interface must admit an ordinary Heather implementation later.

An import of elaborator definitions names a module implementation; it does not
implicitly replace the elaborator currently executing the build. Access to the
current environment is an explicit host context/capability. Pin the active
implementation for a build. Future self-hosting may build a selected toolchain
and hand off at a stage boundary; mid-module self-replacement is not required.
Artifact identity must account for dependencies/configuration, not just a version
string. Identity and correctness are separate claims.

## Acceptance

- Specify a bounded context interface and its effects, including instance lookup,
  expected-type checking, diagnostics, and publication after kernel checking.
- Keep structured syntax, source provenance, hygienic names, and typed references
  across calls; avoid requiring string round trips after resolution.
- Separate imported elaborator definitions from current host services explicitly.
- Document which parts are host primitives and how Heather implementations could
  replace them without changing generator clients.
- Distinguish well-typed emitted terms from preservation of surface semantics;
  moving elaboration into Heather enables proofs but does not itself prove either.

## What it assumes from elsewhere

- [[generators-in-the-language]] owns moving generators into Heather.
- [[scoped-declaration-generators]] owns invocation and module expansion.

## Log

- 2026-09-08: [[heather-checked-construction-api]] owns the first bounded Heather-side construction customer; this issue retains the host capability boundary.
- 2026-10-21: Design proposal: docs/host-elaboration-interface-design.md. Tactics are ordinary Heather values of a request tree `Tac<A>` (an interaction tree over a `Req`/`Resp` container) that the elaborator runs like an in-language analyzer, seeing terms through a lazy surface-level view with host-issued handles; layer-m Code stays the home of typed generators (design §2 says why tactics are the opposite case). Four decisions for Minus in §0; rounds R1–R4 in §10. The probe (crates/elab/tests/tactic_request_tree.rs) checks the protocol, `bind` and a Heather handler compute in today's surface.
- 2026-10-21: Round 1 (Minus approved §0 and the §8a execution tiers): lib/std/tactic.hthr (Tac, requests Goal/Defeq/Fail, `assumption`, the host_* protocol functions), the elaborator's host loop crates/elab/src/host.rs, `by t` in checking positions, and the NativeTactic Rust trait speaking the same protocol. Results are reified to kernel terms and conversion-checked at the goal; failures report each local tried. The kernel now memoizes the elim_W step syntax (fire_elim_w rebuilt a shifted eliminator per step). One run is limited to about a thousand requests: [[tactic-run-continuation-chain]]. Design §12 records what round 1 changed from the plan.
- 2026-10-21: The ~1000-request cap is lifted host-side ([[tactic-run-continuation-chain]], closed); left-nested binds remain exponential in their depth, [[tier2-left-nested-bind-cost]], which R3's loop combinators should know about.
- 2026-10-21: Minus: `Tac<A>` moves onto the tree library's `ITree` over a `Host` container (design §0, item 3) once R2 lands, not before (the other condition, the run-length fix of [[tactic-run-continuation-chain]], is in).
- 2026-10-21: Round 2: binders and composition. Requests Open/Infer/Resolve, `Lam` in `Expr`, binder scopes in host.rs, and quoting of the goal's terms where a tactic argument expects an `Expr` (`by apply(h2, apply(h1, assumption()))`). The library gains `focus`, `attempt`, `first_of` as pure handlers (no host rollback: requests have no side effects) and `exact`, `intro`, `apply`. Done-when met: `apply` closes implication chains (also a recursive client `auto`), and a failed `first_of` reports each alternative with its notes. View/Whnf/Hole move to R2½ with the speller refactor. Design §13 records the departures.
- 2026-10-22: Round 2½: View (on the speller's shared call recogniser and instance recognisers), Whnf, and Match (the elaborator's unifier with a function type's leading parameters as scratch-world metavariables). `apply` now fills every parameter its conclusion determines, implicit ones included (`by apply(sym, assumption())`), and proves the rest with its premise tactic. Bare globals are quoted and resolved with their whole type. Hole stays deferred: no tactic needs metavariables shared across premises yet. Design §14.
- 2026-10-22: Round 2¾ (host round 3): holes shared across premises. `Hole(ty)` makes a run-scoped metavariable in the unifier's scratch-world form; `Defeq` and every application's domain check solve holes by the elaborator's unifier (one home scope at a time, `unify_under`), and the kernel only ever sees zonked terms. `Mark`/`Restore` let `attempt` forget a failed alternative's solutions. `apply` makes a depended-on open parameter a hole, so `apply(trans, assumption())` closes `a = c`. Also `GlobalRef` identities (`Lookup`, `Global(g)`, `HGlobal`'s reference) and `At` notes, rendered by the host. Design §15.
- 2026-10-22: Round 3 (tac-first-port): split_all in Heather. New requests Cases(e, goal) (the elaborator's own match on e, the motive abstracting e and what reaches it through definitions, one branch per constructor with its fields and equation as locals), Constructor(goal) (one branch per field) and Close(split, proofs); View's HMatch(scrut). A split's skeleton is elaborated with marker leaves twice to record the branches (a dependent field is refused) and once more by Close with the proofs. lib/std/tactic.hthr gains reflexivity, cases_on and split_all; it closes the ten goals of goal_combinators.rs (tactic_split_all.rs). Evaluation between requests dominates a run: [[tactic-strategy-step-cost]]. Design §16.
