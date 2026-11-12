---
title: A command that prints what a closed term evaluates to
status: open
labels: [cli,diagnostics]
area: infrastructure
created: 2026-11-12
updated: 2026-11-12
---

`heather` has no command that prints what a closed term evaluates to. Found lowering the probes of a call over views ([[native-library-exports-design]] §3.1): a FunctionIR program written as a Heather value was refused by `lower_program_lent`, and the report that says why (`Function::refused`, `lib/native/function_ir/function_ir_refusal.hthr`) is a `String` nothing would show. `compile-x86` prints it, but only for a `runtime fn` it reflects itself. A failed `refl` names the two sides and not their values, by design: a diagnostic spells what was written.

What I did instead: a script that appends `theorem why_k(): report.take(n) = "candidate" { refl }` for each message the mirror can produce and reads which one checks (twenty candidates a run). It found each refusal in one or two runs, and it is the wrong tool: the candidates have to be guessed from the mirror's source.

## Scope

- `heather eval <file.hthr> <term>` (or `check --eval <name>`): elaborate the term in the file's scope, evaluate it with the evaluator `compile-x86` and `write-elf` already use for `List<Nat>` answers (`crates/cli/src/native`), and print it: a `String` as text, a `Nat`, `Bool`, `List<Nat>`, `Option` of those; anything else by the bounded kernel printer.
- Capped like every other run, and labelled as an evaluation: it proves nothing and is not a check.

## Done when

`heather eval lib/_tests/native/function_ir/function_ir_lower_views_tests.hthr 'unguarded().refused(1, unguarded().plan(), 2, [1, 1])'` prints the sentence `unguarded_why` pins.

## Log

- 2026-11-12: A better stopgap than guessing candidates, found while reading a refusal of a lowered lend: a tactic that fails with the text prints the text's value.

      fn say(text: String) → Tac<Expr> { fail(text, []) }
      theorem why(): True { by say(f.refused(1, f.plan(), 2, [2, 2])) }

  The error reads "`by say(…)`: the tactic failed: " and then the evaluated report, whole. It needs `import tactic;` and works for any closed `String` the tactic evaluator can reach, `region.shown()` included; a long one runs the evaluator out of fuel (a loop's region did). It is a probe to delete afterwards, not something to leave in a module. The command is still wanted: this prints strings only and only through an error.
