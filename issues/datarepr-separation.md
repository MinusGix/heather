---
title: Datarepr: kernel representation vs runtime representation
status: open
labels: [compiler,design,runtime]
created: 2026-07-24
updated: 2026-07-24
---



Decided in discussion (2026-07-24), recorded here because it keeps getting
re-derived: **the representation the kernel checks is not the representation
that runs.** Inductive types are specification objects; runtime data
structures are chosen separately and linked by certified refinement — the
same discipline as Isabelle's `code_datatype` + refinement lemmas or
CakeML's translator, and the sound version of what Coq's
`Extract Inductive nat => int` does by fiat. Canonical example: unary Peano
`Nat` for reasoning, GMP-style `Nat` at runtime.

## Execution model this sits inside

Ordinary `fn`s are **kerneltime**: they are the mathematics side, evaluate
by kernel computation ("a distinct sort of computable"), and are never
themselves compiled. Only `runtime_fn` crosses to hardware. Sketch
(docs/sketches/surface-v2.md has variants):

```heather
fn blah(x: Nat) -> Nat { … }             // 1. ordinary kerneltime code

fn blah_ir() -> List(Instr) {
    lower(blah.code)                     // 2. cross the boundary: syntax as data
}

instance Compile[Cpu] for blah {
    fn ir() -> List(Instr) { blah_ir() }
    theorem equiv(x: Nat):               // 3. certify against the interpreter
        simulate(ir(), [x]) == Some(blah(x)) { … }
}

runtime_fn main() { blah(7) }            // 4. run via any in-scope certificate
```

`main` is special only to the compiler (itself a Heather kerneltime
library): it does typeclass inference for `Compile[Target]` instances over
the call graph and emits their certified IR. The `Compile` class itself is
owned by [[compile-typeclass-design]]; `simulate`/IR by
[[ir-simulate-design]]. This issue owns the **representation** layer:

- A **datarepr typeclass** (name tentative) picks the runtime
  representation of each inductive. `runtime_fn` uses it by default and
  requires it in the background — the user's mental sketch, to be worked
  out here.
- The refinement obligation: datarepr instances carry the proof linking
  runtime operations to the spec inductive's constructors/eliminator
  (shape TBD — iso? simulation relation per operation?).

## Consequences already being relied on

- Efficiency of *kernel* encodings is off the ledger entirely: unary
  heights, Σ-of-Units tags, O(n) numerals never run. This is load-bearing
  for the branching-inductives decision
  (docs/branching-inductives-choice.md §3, [[tier1-branching-constructors]])
  — do not re-admit "the encoding is big/slow" as an argument there.
- The flat-IR escape hatch is off the table for the same reason: the IR
  datatype is a spec object chosen for provability.
- If route A (W + funext) were taken there, stuck `transport`s in
  kerneltime terms would be datarepr's problem at the boundary:
  representation-preserving coercions can compile to no-ops, certified in
  `equiv`. (Noted 2026-07-24 discussion; nothing depends on it yet.)

## Open

- Shape of the datarepr class and its refinement statement.
- Interaction with intensional instance keying (instances key on syntax —
  [[compile-typeclass-design]]): does datarepr key on the type's
  declaration the same way?
- Default instances: derived naive representation for every inductive, so
  `runtime_fn` works out of the box before anyone hand-tunes?
