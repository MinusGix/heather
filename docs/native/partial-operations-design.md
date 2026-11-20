# Partial operations: a node that requires facts of its operands

Status: **proposed 2026-11-20** (thread "Compile divide by a word with a
nonzero proof"). It extends `docs/compilation-vision.md` §6.2 ("facts on
demand", "the compiler sees only a proof") and
`docs/native/facts-on-demand-design.md` §5 (a compiler proved once over any
facts), and it is the "path-facts theory" that
`[[proof-carrying-index-round]]`'s step 2 waits on. The first customer is
`x / y` at a word, which compiles to x86's `DIV`.

## 0. The rule and the problem

Minus's rule for partial operations (2026-11-13, restated 2026-11-20 for
division): **the operation takes a proof of its precondition, found by
search, and nothing gives a junk value**. `x / y` at a word takes a proof
that `y ≠ 0`. No layer may say what `x / 0` is.

`DIV` faults on a zero divisor (`#DE`), so the code for `x / y` is one
instruction only if the proof reaches the block that holds it. Today proofs
stop at the source: `rt` erases them (a call drops its trailing proof
arguments, `rt_data_args`), FunctionIR's nodes are total
(`BufferLoad` is "zero past the end"), and the block layer refuses any
instruction that may fault (`Instruction::admitted`). Span reads pay for
this with a compare the proof already rules out
(`docs/native/native-library-exports-design.md` §0, "a read is in bounds
because a comparison says so").

## 1. The design in one paragraph

A partial operation's **requirement is part of its meaning at every level**,
and a level's meaning is relational. A FunctionIR node's equation for a
divide is "the divisor is not zero, and the output is the quotient":

```heather
Apply(op, width, output, left, right) =>
    Σ (needs: op.Requires(values(width, left), values(width, right))),
        values(width, output) = op.meaning(values(width, left), values(width, right), needs)
```

A valuation that satisfies a region therefore carries every fact its
partial nodes need. The lowering already takes the region's equations as
hypotheses (`Keeps`'s `facts`), so the divisor's register is known nonzero
where `DIV` runs, with no new plumbing in the lowering's statement. The
obligation moves to the one place that can meet it: showing the region is
satisfiable at the caller's arguments, which is the source's own proofs,
carried through `rt` (§3). A function whose source takes proofs gets a
precondition, and its certificate says "if the precondition holds, the code
returns the source's value" (§5).

Nothing in the chain is junk: `op.meaning` at a divide takes the proof, the
equation is stated only where the requirement holds, and no theorem anywhere
mentions the quotient by zero.

## 2. Operations take their requirement

`Operation` (`function_ir_operation`) gains one member per operation:

```heather
fn Operation::Requires(self op: Operation, x, y: BitVec(w)) → Type   // True but for UDiv, URem: y ≠ 0
fn Operation::meaning(self op: Operation, x, y: BitVec(w), needs: op.Requires(x, y)) → BitVec(w)
```

- Multiply and the shifts require `True`; their rows and proofs are unchanged
  but for an ignored argument.
- `UDiv` and `URem` require `y ≠ 0` and mean `x.div(y, needs)`,
  `x.rem(y, needs)` (§4).
- A row's theorem (`Row::Computes`) takes the requirement of the values it
  reads as a hypothesis. The divide-by-a-constant rows prove it from the
  constant; the `DIV` row passes it to the block (§6).
- The next partial operation (a signed divide, a load by index) is one more
  arm of `Requires`. Nothing else in the chain is per-operation.

## 3. Where the proofs come from: `rt`'s obligations

`rt`'s meaning stays a total function (`Tm::sem`). It must: the pin
`p.meaning(…) = f(…)` is checked by conversion, and the source's
`x.div(y, h)` unfolds to its definition there (§4). What `rt` gains is a
second, separate reading of a term, its **obligations**:

```heather
fn Tm::Safe(self t: Tm, w: World) → (g: List<Ty>) → Env(w.tys, g) → Type
fn Fun::requires(self f: Fun) → …    // the function's own proof parameters, as a Prop of its arguments
```

`Safe` is computed type-directed, like `sem`, and at each node is:

- a partial primitive: its `Requires` at its operands' values;
- a `Let`: the bound term's obligations, then the body's under the binding;
- a branch: each arm's obligations under that arm's test
  (`c = True → Safe(yes)` and `c = False → Safe(no)`);
- a call: the callee's `requires` at the arguments, and nothing inside the
  callee (its own certificate covers its body);
- everything else: `True`.

The reflector proves `f.requires(xs) → body.Safe(env xs)` **from the
source's own proof terms**. They already have the right types: the pin is
conversion, so each source proof `h: y ≠ 0` proves the obligation `Safe`
asks for at that node, up to unfolding. A proof made under a branch's
hypothesis (`if h: y != 0 { x / y }`) is used under the arm's equation.
Proofs the search lifted out (`f#found_N`, `measure::lift_found`) are called
as they are.

`rt_lower`'s soundness (`prim2_sound` and the rest) takes `Safe` as a
hypothesis and meets each node's requirement from it. That is the only
consumer.

## 4. The surface

```heather
fn BitVec::div({n: Nat}, self x, y: BitVec(n), nonzero: y ≠ 0 := by bv_omega()) → BitVec(n) { x.udiv(y) }
fn BitVec::rem({n: Nat}, self x, y: BitVec(n), nonzero: y ≠ 0 := by bv_omega()) → BitVec(n) { x.urem(y) }
designation / at BitVec(n) := BitVec::div
designation % at BitVec(n) := BitVec::rem
```

- `BitVec::udiv` and `urem` stay as they are: SMT-LIB's total functions, the
  long division the library's arithmetic is about. `div` is defined through
  `udiv` so that `rt`'s pin stays a conversion, as `Vec::at` is defined
  through `vector_get` (`[[proof-carrying-index-round]]`). No equation
  reads the definition at zero: the FunctionIR equation and every row are
  stated under the requirement, and `div`'s laws (`div_mul_add_rem`, the
  bound) take `nonzero`.
- The default search finds `10 ≠ 0` by evaluation and `y ≠ 0` from a branch
  test or a hypothesis in scope; where it fails, the elaborator says what it
  could not prove, as for `s[i]`.
- The library modules that use `/` or `%` at words (all import `bitvec_div`) move
  to `udiv` where they mean the total function, or pass the proof.

## 5. A function's precondition, and what the certificate says

A `runtime fn`'s trailing proof parameters (`h: y != 0`) are its
precondition, `requires`. They stay erased from the code (no argument
register carries a proof), and they move into the statement:

> for all arguments with `requires(args)`, the code returns `f(args)`.

- The certificate's theorem (`compiled_returns` and the export contract)
  gains the premise. A function without proof parameters has `requires =
  True`, so every existing statement is unchanged.
- A call between compiled functions: the call node's requirement is the
  callee's `requires` at the arguments, met from the caller's `Safe` (§3).
  This is how a callee takes proof parameters at all, which today is refused.
- An export to Rust (`crates/linked`): the generated declaration for a
  function with a precondition is the open question of §9.

## 6. FunctionIR, passes and the lowering

- **Equations.** `NodeHolds` at `Apply` is the Σ of §1. `eval` stays total
  (it is a schedule's runner, not a meaning, and computes `udiv`); the
  theorem that ties them, `eval_holds`, gains the premise that every partial
  node's requirement holds at the evaluated values (`Region::Defined`). A
  program's evaluated result is its functions' result at every argument
  list that is defined there (`program_eval_computes`).
- **Passes stay sane by their own theorems.** A pass is proved on runs
  (`List::optimised_runs`): the optimised nodes leave the same values in
  every live word. It now also proves `Defined` before implies `Defined`
  after. Dropping a node or folding it to a constant removes a requirement,
  which is free. Keeping a partial node with operands of the same values
  keeps its requirement. A pass that moves a divide past the test that
  justified it (hoisting out of an arm) cannot prove it, and so cannot be
  written: no runtime check, no special case in the pass.
- **The lowering's statement does not change.** `Keeps` already takes the
  node's equation as a hypothesis, and the equation now holds the
  requirement. The `DIV` row reads it as "the divisor's register is
  nonzero" through `File::Represents`.
- **The planner** keeps RAX and RDX free across a `DIV` row, as it does for
  the reciprocal rows (`Operation::writes_fixed`).

## 7. The machine: `DIV` and a block that may fault

This is the trust-base part, the same kind as `IMUL`/`MUL` in PR #811.

- **`DivR(source)`** (`F7 /6`): RDX:RAX divided by the source register,
  quotient to RAX, remainder to RDX, all flags undefined.
  `Instruction::faults` is true when the divisor is zero **or** the quotient
  does not fit 64 bits (RDX ≥ divisor), as the Intel manual says; the model
  already has the outcome (`ExecuteOutcome`, `Faulted(DivideError)`).
- **A block that holds an instruction that may fault.** `admitted` stops
  refusing `may_fault` statically. A block's run (`execute_block_normal`)
  is the real run only where no instruction faults, so the block theorem
  takes, per such instruction, a premise that it does not fault at the
  state it meets. Blocks without such an instruction get the premise for
  free (`never_faults`), so nothing existing changes.
- **The row**: `XOR EDX, EDX; MOV RAX, x; DIV y`. With RDX zero the quotient
  always fits, so the only fault left is the zero divisor, and the
  requirement rules it out.

## 8. What this unlocks after division

- **A load without its compare.** `BufferLoad` gets the requirement
  `index < length`, `s[i]`'s proof reaches it, and the compare the
  exports note says a read pays for goes away.
- **Callees with proof parameters** (§5), which the fact-taking loops'
  callers wait on (`issues/span-caller-of-fact-taking-loop.md`).
- **Signed divide** (`IDIV`), whose requirement adds the one overflowing
  pair (`MIN / -1`).

## 9. Open question for Minus

**What Rust sees for an export with a precondition.** Three readings:

1. The generated declaration is an `unsafe fn` whose doc comment states the
   precondition, and the caller's `unsafe` block is where it is met. The
   certificate's premise is the Rust caller's obligation, as a lent span's
   `Lends` already is.
2. A safe wrapper is generated that tests the precondition when it is
   decidable (`y != 0`) and returns `None` otherwise; the unchecked entry
   stays `unsafe`.
3. Exports with preconditions are refused for now; internal calls only.

Recommended: 2, since it costs one compare at the boundary only and keeps
Rust callers safe, with 1 available underneath.

## 10. Rounds

1. **Machine** (trust base, Minus merges): `DIV r64`, its faults, blocks
   admitting it under a no-fault premise, probes against `as` and the CPU.
2. **FunctionIR**: `Operation::Requires`, the Σ equation, `Defined`,
   `eval_holds` under it, passes' `Defined` preservation, the `DIV` row and
   the lowering.
3. **`rt`**: `Tm::Safe`, `Fun::requires`, the reflector's proof of `Safe`
   from the source's proofs, `rt_lower` soundness under it, the certificate's
   premise.
4. **Surface**: `BitVec::div`/`rem` and the designations; the library's
   users of `/` at words.
5. **Then**: loads without the compare; callee preconditions.
