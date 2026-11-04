---
title: A member's bare base name is its self-reference; say so when a same-named global was meant
status: closed
labels: [diagnostics,frontend]
area: language
created: 2026-10-29
updated: 2026-11-02
---

Inside a member `T::name`, the bare base name `name` is the self-reference,
so a top-level declaration with the same name cannot be reached bare. The
refusal does not say so:

```
fn Sim() → Nat { 0 }
record Prog { n: Nat }
fn Prog::Sim(self p: Prog) → Nat { Sim() }
// error: recursive call to `Sim` is not structurally guarded
```

`<module>::Sim()` works (`prelude::cong` is the idiom for prelude names,
docs/sections-design.md). Probe on master 4f0ac27
([[proof-patterns-audit-2026-10]]). Rounds have hit this as `Program::Sim`
vs `Sim` (Linux spec, PR #110, renamed to `SimProgram`), `Eutt::trans` vs
`trans` (PR #143) and `Nat::same` inside `T::same`.

## Acceptance

- When a self-reference by base name is refused (not guarded, wrong arity,
  wrong type) and a declaration of that name resolves outside the member,
  the error names it and gives the qualified spelling that reaches it.
- Pinned in lib/_tests with `// expect-error:` naming the suggestion.

## Log

- 2026-11-02: Done. A refusal of a member's self-reference written by its bare
  base name (`Elaborator::self_call_noted` over `elab_self_call`, and the
  self-name-as-value refusal) now carries a note when a declaration of that
  name resolves outside the member: `note: inside the member `Spec::Sim`, the
  bare name `Sim` is `Spec::Sim` itself (its self-reference), which hides the
  declaration `m::Sim`; write `m::Sim` to reach it` (`prelude::cong` for a
  prelude name). The qualified spelling is offered only when it resolves back
  to the same key. Errors inside an argument that neither sit at the call nor
  name the callee pass through without the note. Not covered: a self-call
  that elaborates and then mismatches its expected type is refused by the
  caller, which does not know the head was a self-reference. Pinned in
  `lib/_tests/lang/self_reference_tests.hthr` (four noted refusals, one
  un-noted control, the qualified spelling checking). Pinning it found
  [[descend-refusal-misreads-chain-shape]].
