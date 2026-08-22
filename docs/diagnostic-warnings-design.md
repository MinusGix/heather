# Warnings: a diagnostic that is not a failure

Status: **landed 2026-08-16** (`issues/match-arm-redundancy-warning.md` is its
first customer). This document is the mechanization's source of truth; section
numbers are referenced from the code.

## 1. The problem

Every diagnostic the frontend can raise is fatal. `check_source` returns
`Vec<ElabError>` and its contract is stated in its own doc comment — *"empty
means the file is good"* — so there has been nowhere to say something true
about a file that checks. Two issues had been parked on exactly this and on
nothing else:

- `issues/match-arm-redundancy-warning.md` — an unreachable row and a `_` arm
  that stands for nothing. Both are silences the pattern-compiler round chose
  deliberately, and both were filed with the same conclusion: *"Both want the
  same thing, and it is the thing that does not exist."*
- `issues/warn-bare-eq-no-effect.md` — a statement-position `a = b;`, which
  computes nothing and discards a value.

Making either an **error** is the wrong trade, and the redundancy issue says
why: it turns a refactor that adds a constructor into a build break at every
`_` that used to cover it.

## 2. Decision 1: a separate channel, not a severity on `ElabError`

A `severity` field on `ElabError`, with warnings riding the existing `Vec`, is
the smaller diff and the wrong design. `check_source(…).is_empty()` is read as
"this file is good" at every call site in the tree — the cache's end-to-end
tests, the bench fixtures, the test helpers, the CLI's `ok` line — and a
warning arriving in that `Vec` would make a good file look failed at every one
of them. The failure mode is silent and distributed, which is the kind this
codebase pays a little to avoid.

So: `ElabError` is untouched, and `Warning` is its own type. The contract in
`check_source`'s doc comment stays true as written, which is the test
`a_warning_does_not_make_a_good_file_bad` pins.

## 3. Decision 2: the sink lives on the elaborator; the reader drains it

`Elaborator::warnings: RefCell<Vec<Warning>>`, raised through
`Elaborator::emit_lint(lint, msg, span)` and read through
`Elaborator::take_warnings()`.

Two reasons for a field rather than a return value. **`&self`**: the customers
hold shared borrows — the pattern compiler takes `&self` throughout — so a
returned channel would mean threading a sink parameter through every
elaboration path in the crate, for a feature that is inert in almost every
file. The codebase already keeps per-declaration side data exactly this way
(`goals`, `pending_derived`, `op_fallback_notes`). **Attribution**: the CLI
checks a module and renders its diagnostics against *that module's* source, so
a warning has to leave with the text its span indexes into, before the next
file is checked. `take_warnings` drains for that reason, and the CLI calls it
once per module.

## 4. Decision 3: a failed declaration says nothing, and warnings never fail a run

A declaration that fails registers nothing — not in Ψ, not in the globals, not
in the derived-instance queue — because everything it produced is as
speculative as it is. Warnings join that rule at the same site: the item loop
marks the warning count before each item and truncates back to it when the
item errors. `check_source` recovers per declaration, so an *earlier*
declaration's warning survives a *later* one's failure; both halves are pinned.

Warnings do not touch the exit code, and they do not touch the `ok` line —
cache-v1 reserved a bare `ok` for a full clean check and a gate can
mechanically demand it, so a warned file still prints `ok` and the warnings
are rendered before it, with a per-module count line that mirrors the error
path's. **No `-Werror` and no allow-list**: neither has a customer, and a
warning nobody can silence is a warning that has to be worth printing.

### 4.1 Generated text warns nobody

`Elaborator::emit_lint` drops the warning outright while generated source is being
elaborated (`access.generated > 0`, the depth the unnameable-names boundary
already keeps). A `datarepr`'s emission is elaborated *inside* an ordinary
check of the declaration that owns it, so its spans index into text the reader
does not have; rendered against the file being checked, a caret would land on
an unrelated line. Dropping at the raise site rather than filtering at the
render site keeps every future reader of the channel from having to know this.

Generated code that is genuinely wrong is the *generator's* problem and reports
as an error through the emission's own check, which is unchanged.

## 5. Decision 4: one shape and stable identity, one rendering

`Warning { lint, msg, span }`. Every warning anyone has actually asked for is a
message at a span; the listing-shaped diagnostic (`ElabError::UnsolvedGoals`)
exists because goal *state* is the point there, and nothing here needs it. A
listing-shaped warning can grow its own rendering the day a customer arrives.
`Lint` supplies a stable enum identity and kebab-case name, so tests and future
allow/deny configuration need not parse wording that should remain free to
improve.

`render` and `render_snippet` are the error renderers with the severity word
changed — the shared `headed(severity, …)` helper — so the two cannot drift
into two shapes a reader has to learn separately.

## 6. Decision 5: the channel lands with a customer

Infrastructure with no customer is untested infrastructure. The channel lands
with one of the two parked issues actually paid, which is also what proves the
staging rules above are the right ones.

### 6.1 Source-style rules have a registry

Semantic findings should still be emitted where their analysis lives: the
unreachable-arm lint consumes the pattern compiler's reachability census, and
duplicating that analysis in a generic pass would be worse modularity. Purely
syntactic style rules instead live in `crates/elab/src/lint.rs`. A shared AST
walker visits each successfully elaborated source item and calls a small
registry of expression-lint functions in deterministic source order.

Running the pass only after the item checks preserves §4 without asking each
rule to understand speculative declarations. All findings pass through
`emit_lint`, so generated-source suppression and future channel policy remain
centralized. The first registered source rule is
`match-function-application`, tracked by
`issues/lint-match-function-application.md`.

## 7. The first customer: an arm that can never be reached

`crates/elab/src/patterns.rs`. The pattern compiler already computes, for each
written arm, how many leaves of the compiled tree its body reached —
`Compile.uses`, the census §5 of the nested-match design needs to decide
between sharing an arm's body and copying it. **Reachability is not a new
analysis; it is that number being zero.** `settle` already branches on it (the
`0 => {}` arm, which is where a body that is never elaborated gets dropped),
so the customer is a warning at a branch that existed.

One mechanism covers both shapes the redundancy issue lists:

- a `_` arm whose constructors are all covered by arms of their own, and
- a row shadowed by an earlier, wider row — which needs the deep-pattern
  matrix to arise at all, a *shallow* duplicate being the existing
  `duplicate arm` error.

The message names the form the writer used (`match`/`split`), like every other
message that names one, and points at the **arm's** span rather than the
`match`'s.

Two things the warning is for, and the second is the one that justifies it
over "harmless": an unreachable arm's body is never elaborated, so it is also
**never checked**. The silence hid a body nobody had type-checked.

### 7.1 A generated level must not warn about its own arms

The compiler emits `_` arms of its own — a level standing for a pattern column
carries a fallthrough for the rows that had a variable there — and the pass
runs again over every level it emits (§9 of the nested-match design). So a
generated level whose column happens to be fully covered has a redundant `_`
that *nobody wrote*.

The redundancy issue named this as the blocker: refusing a redundant `_` "would
have meant marking generated arms and the pass remembering which spelling
produced it". Marking them is what this does, in the cheapest form available: a
`generated: bool` on `ExprKind::Match`, set by the pattern compiler's emit and
by nobody else, read by diagnostics only — the same discipline, and the field
right next to, `form: MatchForm`.

It suppresses nothing of the user's. One compilation's census spans every level
it emits, so reachability for the *written* arms is complete at the outermost
pass; the flag only silences a report about our own arms.

This is load-bearing rather than defensive, and it was checked by removing it:
without the guard,

```heather
fn h(p: P) -> Nat {
    match p { Mk(TA, TA) => 0, Mk(TB, TA) => 1, Mk(x, y) => 2 }
}
```

— where every written arm is reachable — reports a `_` arm that does not occur
in the source, pointed at the whole `match`. Pinned by
`a_generated_levels_own_default_arm_is_not_reported`.

## 8. Not in scope, with reasons

- **`warn-bare-eq-no-effect`**, the other parked issue. Its second blocker is
  untouched: there is no assignment form yet (`:=` is
  `issues/effects-direction`'s), so the statement it would warn about cannot
  be written in a way that means anything else. The channel it was waiting for
  now exists; that issue records this and stays open on its own remaining
  blocker.
- **Redundancy as an error**, refused above (§1).
- **Suppression** (`#[allow]`, `-Werror`, per-file pragmas): no customer.
- **Surfacing warnings to an editor**: `issues/lsp-from-the-meta-layer.md`
  owns that, and the channel it would read is this one.

## 9. Acceptance

`crates/elab/tests/warnings.rs`, split the way this document is: the channel
(contract untouched, drain semantics, a fresh elaborator carries none, a failed
declaration withdraws its own and only its own, the rendering) and the customer
(both reported shapes, both silent controls, the generated-level control, the
form name).
