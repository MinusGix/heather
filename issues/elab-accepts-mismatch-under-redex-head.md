---
title: A mismatch under a let-bound or β-redex head is refused only by the kernel
status: closed
labels: [frontend,elaboration,diagnostics]
area: language
created: 2026-10-25
updated: 2026-10-26
---

Found while proving S3.2's dataflow leaf (`Target::goes_leaf`,
`lib/native/native_compile_leaf.hthr`, 2026-10-25). A proof of `P(s.memory)`
passed where `P(execute_block_normal(code, s).memory)` is expected gets past
the elaborator when the expected type's head is a let-bound lambda or a
β-redex, and only the kernel refuses it, with a type that "has no surface
spelling". Passed as a plain argument the elaborator refuses it at the span.
Reproduced against master on 2026-10-25:

```heather
import x86_64;
import x86_64_block;
import logic;
import list;

theorem weaken_like<M>(pre, entry: MachineState<M> → Type, into: (s: MachineState<M>) → entry(s) → pre(s)): True { trivial }

// Refused by the kernel only: the binders take their types from `entry`, the
// pair is checked against `pre(s)`, a β-redex.
theorem probe_inline<M>(code: List<Instruction>, P: M → Type, Q: Type, q: Q): True {
    weaken_like<M>(λ (s: MachineState<M>) => P(execute_block_normal(code, s).memory) ∧ Q, λ (s: MachineState<M>) => P(s.memory),
        λ s held => ⟨held, q⟩)
}

// Refused by the kernel only: the expected type's head is a let-bound lambda.
theorem probe_let_plain<M>(code: List<Instruction>, P: M → Type, s: MachineState<M>, h: P(s.memory)): True {
    let post = λ (u: MachineState<M>) => P(u.memory);
    let x: post(execute_block_normal(code, s)) = h;
    trivial
}
```

The same mismatch with the binders annotated (`λ (s: …) (held: P(s.memory))`),
or with a pair under the let-bound head, is refused by the elaborator with
the usual "this has type … but … is expected" at the span. So the check is
skipped on some path that both cases share, likely a comparison that gives
up on a stuck head (`execute_block_normal` of an open list) under a redex and
accepts rather than refusing or deferring with a span.

## Scope

- Find the path that accepts, and make it refuse at the span (or report the
  kernel's refusal at the argument with both types spelled).
- The two probes as refusal tests that name their reason.

Related: [[elab-accepts-conjunction-for-equation]] (another mismatch only the
kernel refuses), [[check-fallback-discards-expected-type]] (closed; the same
symptom from the check fallback).

## Resolution (2026-10-26)

**Cause.** Nothing on the checking path skipped the comparison. Both probes
reach the ordinary checking note (`note_check_mismatch`): the variable `h`
and the binder `held` are checked against their expected types, the
candidate is recorded, and when the gate refuses, the probe decides
`NotConvertible` and reports at the right expression. What failed was the
spelling. A `let`'s value is substituted where it is used, and an implicit
λ argument is substituted into the parameter types that mention it, so the
note's types held a β-redex: `El((λ u. P(u.memory))(execute_block_normal(code, s)))`
as the let's expected type, `El((λ s. P(s.memory))(s))` as `held`'s own
type. The display has no surface form for a redex, so one side printed raw,
the note fell back to the located form ("… has no surface spelling"), and
the message kept the kernel's `NotConvertible`. Annotating the binders, or
checking a pair under the let-bound head, avoided it only because those
routes whnf the type first, which contracts the redex. So "refused only by
the kernel" was the same as for every checking mismatch (the elaborator
records, the gate decides); the difference was a message with one type
missing.

**Fix.** The display contracts a β-redex at any node that would otherwise
print raw (`Speller::call` in `crates/elab/src/display.rs`, through
`spelling::beta_head`, moved there from the unifier). It is syntactic
substitution, charged to the node budget, and only in the reading flavours:
the source flavours (`spell_term_source`, `spell_type_source`), whose output
omega, ring and generated annotations re-parse, still decline a redex, so no
route that decides anything sees a different spelling. Every redex the elaborator leaves in a type now spells as
its contractum, at the head, under a curried spine, and inside an argument
(`And<P(n), True>` against `And<P(f(n)), True>`). Both probes now say
`this has type `P(s.memory)`, but `P(execute_block_normal(code, s).memory)`
is expected here` at the expression.

**Tests.** `crates/elab/tests/check_reports_mismatch.rs`:
`a_mismatch_under_a_redex_head_is_spelled_at_the_expression` (the two probes
at `Nat` with an opaque `f` for `execute_block_normal`, a curried and a
nested redex, each asserting the spelled message, no kernel prefix and the
span) and its control `a_redex_head_of_the_right_type_is_accepted`. One pinned kernel
refusal was this shape and is now `Refusal::Mismatch`:
`lib_setoid_mergeable.rs`'s `wrong_lift`, a closure goal filled with
`a.valid` where an instantiated λ predicate was expected.

Not covered: ι-redexes (a projection of a literal pair, a recursor applied to
a constructor) still print raw when one reaches a note; none has been seen
in a mismatch yet.

