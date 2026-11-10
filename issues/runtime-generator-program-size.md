---
title: A linked runtime program's proof and generator reply grow with all its functions at once
status: open
labels: [native,runtime-fn,performance]
area: heather-in-heather
milestone: [hih-native-heather,self-lexer]
created: 2026-11-10
updated: 2026-11-10
---

A `runtime fn` that calls others is published with one program and one
agreement for all of them (`runtime_linked`, `lib/native/runtime/runtime.hthr`).
Three costs of that grow with the program, and the scanner's automaton
(`lib/lang/lexer/lexer_scan.hthr`, about ninety states in twenty-three
functions) met each of them in turn. It is why that automaton is twenty-three
separate programs today and `scan_step` an ordinary function that picks one
from a list, with Rust making the same pick through a table
(`crates/linked/src/scanner.rs`).

## 1. The reply grew with the square of the program (fixed)

The linked program's sources, a list with an entry per function, were
spelled out in every `Compile::part`, and the program in each statement that
names it. The host reads a reply of at most `READ_BUDGET` nodes
(`crates/elab/src/host.rs`), so a function with eight callees was refused
as "an implausibly large `Expr`". Fixed in the round that found it:
`runtime_held` puts each in a hole it solves, so every later mention is one
node (`lib/_tests/native/runtime/runtime_tests.hthr`, `eighths`).

## 2. Requests and nodes still grow linearly

A reply holds the function it compiles, so the node budget is also the
largest single `runtime fn`. A family of the automaton, about a hundred
byte comparisons in sixteen arms, is about five thousand nodes, and six of
the twenty-three were past the 4096 the budget was. The same round raised
it to 2^14, which is a function of about three hundred comparisons: more
than the certificate accepts today ([[function-ir-scan-id-cost]],
[[compile-x86-certificate-memory]]), so it is no longer the first limit met.

With the sharing, a program of 88 functions made about 11,850 requests
against `REQUEST_BUDGET`'s 10,000, and its reply was past the node budget
as well. Both budgets are rails against a runaway tactic, not sizes anyone
chose for a program; raising them further is not the fix by itself, because
of the next cost.

## 3. The agreement is one declaration that evaluates every lowering

`f::agrees` cites `program_fit_sources` with, for each function,
`Compile::part` at two `trivial` side conditions (`calls_fit` at the
world's arity and the parameter count) that the kernel settles by forcing
that function's lowered code. They all sit in the one proof term of the
one declaration. Measured on the cloud box at width one: a twenty-two
function program of the automaton ran about 11.5 million kernel steps
against the 2^20 per declaration; each family alone costs two to three
million, but spread over its own declarations, each within the budget.

So the largest program is bounded by the *sum* of its functions' lowering
cost, where everything else in the pipeline is bounded by the largest
function (`program_scan_drop` in the certificate, [[function-ir-scan-id-cost]]).

## Direction

Linking should reuse what each callee already published, and prove nothing
about a callee's code again:

- each `runtime fn` publishes its own `calls_fit` and parameter-count facts
  as theorems at a *symbolic* arity world (they are checked once, in the
  callee's declaration);
- `Function::relabel` preserves both by a lemma, so a caller's `part` cites
  the callee's theorems through it and evaluates only the link tables;
- the program's arity (`program_arity`) is read from the signatures, not by
  lowering.

The agreement of a program is then linear in its function count with a
small constant, and no declaration forces more than one function's code.
The request count falls with it (the per-callee re-reading named in
[[runtime-generator-link-cost]] is the same work seen as seconds).

The x86 certificate has its own version of this cost
([[compile-x86-certificate-memory]]).

## Done when

The scanner's automaton is one program: `scan_step` is a `runtime fn`
calling its twenty-three families, `f::agrees` checks within the ordinary
budgets, and `crates/linked/src/scanner.rs`'s `step` is one call
([[self-lexer-linked]]).
