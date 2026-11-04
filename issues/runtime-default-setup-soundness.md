---
title: The default setup's judgment, lowering and soundness theorem, proved once
status: open
labels: [native,compiler,proofs]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-04
---

Slice R5b of `docs/runtime-fn-setups-design.md` (§2, §5–§7): the `Setup`
record, the default setup's judgment and lowering, and its soundness theorem
proved once (route 2 of [[in-language-certificate-emission]]).

## Scope

- `Setup { name, judge, lower, sound }` and the `Compile(f)` class in
  `lib/native/runtime/`.
- The default judgment over `rt` (§5.1), with reasons and paths.
- The lowering to a FunctionIR program (§7): the primitive table, flat
  layouts (records and enums scalar-replaced, `Bool` as a bit, `Bytes` as a
  buffer and a length), `Call` regions, and `Loop` for `Fold`, `ForIn`,
  `Measured` and fuel recursion.
- `default().sound`: induction over `Tm` under the lowering invariant
  (environment to ports, fresh ids, valuation agreeing with the encoded
  meaning). V6 first: the `Prim(add)` and `If` cases, to fix the invariant.
  Per-construct cases reuse `function_ir_compile`'s loop lemmas and the
  node equations (design §6.3's table).

## Done when

`default().sound` is proved for every N1 construct of design §7, with no
per-program proof, and a negative control: a lowering perturbed at one
construct fails the theorem, not a test.

## Log

**2026-11-01 (R5b, V6).** `lib/native/runtime/rt_lower.hthr`: the lowering
of variables, `Let`, `Prim(Add)` and `If` into FunctionIR regions, and
`Tm::lower_sound`, proved once by induction over `Tm`; every other node
lowers to `None` for now. What V6 fixed (design §16.5):

- **The invariant** is three things: every variable's port holds its
  value's encoding (`EnvHolds`; a word at its width, a bit as `ofBool`),
  every port is below the fresh id `next` (`Below`), and the region keeps
  every id below `next` (`Keeps`). The result port then holds the encoded
  meaning. It is stated over `StructuredRegion::eval`, so FunctionIR's
  `program_eval_computes` carries it to the relational semantics.
- **No judgment hypothesis.** The lowering asks for each equation of codes
  the meaning casts along (`Ty::check`) and refuses without it, and the
  proof carries encodings along that equation (`Ty::cast_holds`, from
  `Ty::cast_self` and `Nat::equation_self`). So `sound` assumes only that
  the lowering accepted; `judge` can stay a reporter of reasons.
- **A branch's arms take disjoint fresh ids:** the second arm's start
  above the first's, and both move their result to one port above both.

Probes: `lib/_tests/native/runtime/rt_lower_tests.hthr` (`pick`, a branch
with an `Add` arm, and `twice`, a shared sum, each agreeing with the Heather
function by instantiating the theorem; a wrong claim and an `Add` lowered
to a `Sub` node refused). Next: the remaining primitives, `Lit`, `IfEq`,
records, calls and `Fold` (§6.3's table), and the `Fun`/`Program` wrapper
from parameters bound by `Valuation::bind` to `Function::eval`.

**2026-11-02 (R5b round 2).** `rt_lower.hthr` gains literals, the
primitives FunctionIR has nodes for (word `+ - & | ^`, `== <u <s`, `&& || !`
on bits), `IfEq` (lowered and proved as `If`, by `Tm::convoy_match`), calls
at a signature of 64-bit words, and the function wrapper `Fun::lower` /
`Fun::lower_sound`, from `Function::eval` to `Fun::meaning` (design §16.6).
The theorem now assumes `Tm::CallsAgree(w, call)`: every word-signature
function is answered with its meaning (`Ty::Answers`), which is exactly what
`Fun::lower_sound` concludes of a function, so a program discharges it
function by function. Probes instantiate the wrapper at the reflector's
`leaf`, `caller` and `safe_pred`; a `!` lowered against a zero constant fails
the `Neg` case.

Still to do for N1, each with its obstacle (§16.6): the program wrapper
(`CallsAgree` below a bound, as `program_eval` answers function `i` only by
the ones before it); records (a variable's encoding spans several ports, and
`Make` needs `get(mk(t)) = t`, which η for pairs should give by `refl`);
`Fold` and the byte primitives (buffers are read as empty by
`StructuredRegion::eval`, so the theorem moves to `function_ir_state`'s run);
`zero_extend` (no node, `function-ir-alu-core`).

**2026-11-02 (R5b round 3).** Records: `Make` and `Field` lowered and
proved, a record being its fields at consecutive ports (design §16.7). The
invariant's `Below` and frame (`Ty::Same`) are now spans typed by the
context's codes; branches move records a field at a time; `RecInfo` gains
`round: get(mk(t)) = t`, `refl` by η for every reflected record. Probes:
`wc_step` and a record-valued branch agree with their Heather functions
through the theorem. Left for N1: the program wrapper, `Fold` and the byte
primitives, `zero_extend`.

**2026-11-04.** The `Setup` record (`{ name, judge, lower, sound }`, `sound`
being `Fun::lower_sound`), `Fun::judge` with reasons, and the `Compile` class
landed in `lib/native/runtime/runtime.hthr` with the generator
([[runtime-fn-default-setup]], design §16.8). The open items here are
unchanged: the program wrapper, `Fold` and the byte primitives, `zero_extend`.
