---
title: A Pi codomain mentioning its binder panics the kernel when the body mismatches
status: closed
labels: [kernel,elab,bug]
created: 2026-09-17
updated: 2026-09-17
---

Checking a body against a **Π whose codomain is a type application mentioning
the binder** aborts the process with a kernel invariant violation as soon as
the body does *not* have that type. The mismatch report never gets written.

```heather
import logic;
theorem t<A>(P: A → Type, R: Type, h: R): (a: A) → And<P(a), R> { h }
```

```text
thread 'main' panicked at crates/kernel/src/subst.rs:1150:9:
kernel invariant violated: local variable 5 escapes the substitution's target
entries (variables cannot address a context-variable base)
```

It is a **panic, not a diagnostic**: `heather check` dies, so nothing else in
the file is reported.

## What was measured (2026-09-17)

Run on both the parent commit and the [[iff-in-type-valued-body]] tree; they
behave identically, so this is not that round's doing.

- Panics: `(a: A) → And<P(a), R>` expected, `h: R` supplied.
- Panics the same way with the notation: `(a: A) → (P(a) ∧ R)`.
- **Checks** when the body does have the type:
  `h: (a: A) → And<P(a), R>` against the same expected type — so the Π itself
  is fine and it is the *refusal* path that breaks.
- **Reports cleanly** when the codomain is a bare application rather than a
  type application: `(a: A) → P(a)` expected, `h: R` supplied, gives
  ``this has type `R`, but `(x: A) -> P(x)` is expected here``.
- **Reports cleanly** when the offending type is the *hypothesis* rather than
  the expected type: `h: And<(a: A) → P(a), R>` against `R`.

So the discriminator is: the **expected** type is a Π, its codomain is a
`TyKind::Named` whose arguments mention the binder, and the check fails.

## Why it matters beyond the crash

A kernel `assert`-class invariant reachable from ordinary surface source is a
crash, not a refusal — the term handed to `subst` is malformed, and the
question of *who* built it (the
mismatch renderer, or the checking path that precedes it) is the first thing to
answer, because a malformed term that merely happened to be on its way to an
error message is a different severity from one the checker itself builds.

## Acceptance

- The reproducer above reports an ordinary type mismatch and exits non-zero.
- The invariant is not merely silenced: name which builder produced the term
  whose variable escaped, and fix it there.
- A regression test with an **open** carrier (`A` a type parameter) and a
  codomain that genuinely depends on the binder, since a closed codomain does
  not reproduce it (docs/testing-generated-terms.md).

## What it assumes from elsewhere

- **[[std-logic-module]]** owns `And`; it is incidental here — any declared
  type constructor applied to the binder should do, and that is worth checking
  when the fix is scoped.

## Log

- 2026-09-17: Filed from the [[iff-in-type-valued-body]] round, which hit it
  probing adjacent connective spellings. Confirmed pre-existing by rebuilding
  the parent commit.
- 2026-09-17: CLOSED. **It is the mismatch renderer, not the checking path** —
  the question this issue put first, answered by the backtrace:
  `check_decl → kernel_error → display_type_clean → spell_within → Speller::ty
  → under → ty → display_targs → strengthen_ty → Type::apply_local`. The
  checker had already refused correctly; the abort was in saying so. So the
  severity is a crash, not unsoundness, and nothing the kernel accepted was
  ever wrong.

  The escaping variable is the **display walk's own binder**.
  `Elaborator::display_targs` recovers a declaration's monomorphized type
  arguments by strengthening field types out of its lowering, and was handed
  only the `Cx` the walk started from. A type printed under a `Π` is scoped in
  that `Cx` *plus* the binders the walk descended through, so
  `drop_binders` built a substitution short by exactly that many entries and
  the binder's variable indexed off the end — the assert at
  `crates/kernel/src/subst.rs:1150` firing correctly on a caller that lied
  about the context.

  The subtlety that made it a latent trap: the walk's `d` parameter looks like
  a binder depth and **is not**. It is the node/depth budget (`Speller::charge`)
  and is incremented on every descent — `Squash`'s payload, a `Π`'s *domain*, a
  spelled type argument. The real count is `names.len() - cx.names.len()`,
  since `Speller::under` pushes one name per binder (the `Π` arm pushes `"_"`
  even for an unused binder, commenting "to keep the index arithmetic
  honest") and `cx.names` is parallel to `cx.gamma.entries`. That is now
  `Speller::binders()`, threaded into `display_targs` as `under`.

  The kernel invariant is untouched and nothing is silenced: the arguments are
  strengthened past the walk's binders *as well as* the Σ spine's, which lands
  them in `cx` — where `lower_shape`'s re-lowering check already scopes them,
  so that check is unchanged — and are shifted forward again before being
  returned to a walk still standing under those binders.

  **A precision gain came with it.** The old code could not spell a
  declaration's arguments under a binder *at all*: an argument mentioning any
  outer context variable also ran off the end of the short substitution, so
  the outcome was a panic or, where it stayed in bounds, a failed round-trip
  and `<…>`. Now `(a: A) -> Both<P, R>` renders in full and only an argument
  that genuinely mentions a walked binder keeps the honest ellipsis —
  `(x: A) -> Both<…>` for the reproducer, which is the same fallback this
  recovery already used for indexed families and oversized declarations.
  Spelling *that* case needs the arguments kept at the walk's depth and a
  `lower_shape` in a correspondingly extended `Cx`, which the display walk
  does not build; filed as [[display-targs-under-binder-ellipsis]].

  Audited the sibling callers: `unification::strengthen_tm`'s other use
  (`Elaborator`'s conversion-mismatch sentence) already threads the mismatch
  walk's own `m.depth` and is correct by construction, and `mint`'s
  same-named helpers are a different function. `display_targs` was the only
  caller that dropped the depth.

  Test: `a_parameterized_inductive_under_a_binder_renders_instead_of_aborting`
  in `crates/elab/tests/display_surface.rs`, with the two axes the defect
  needs — an **open** carrier, or there is no `Π` whose codomain mentions its
  binder, and a **refusal**, since the crash was in rendering one — plus the
  recovered-argument case and the zero-binder control.
  `docs/surface-type-display-design.md` §4 records the rule, beside its own
  sentence that a display path which panics is worse than any message it could
  have printed.
