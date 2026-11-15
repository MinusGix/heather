# Carrier-directed numerals: design record

## Decision

A written numeral is one syntax form, `ExprKind::Num(n)`. It is never an
integer literal and `-n` is never a second literal form: prefix negation remains
an ordinary operator applied to that numeral.

Numerals have two elaboration modes:

1. In inference position they retain the historical `Nat` default and emit the
   core natural term (`Zero`/`NatLit`, the compact form of `Succ` chains).
2. In checking position at `A`, after the existing special `Fin` rule and the
   byte-identical `Nat` rule, elaboration resolves `Numeral<A>` and applies its
   `ofNat : Nat -> A` field to the historical natural term.

The standard class is:

```heather
class Numeral<A> {
    ofNat: Nat -> A,
}
```

It is deliberately one embedding operation rather than a class indexed by the
literal value. Heather already has an ordinary `Nat` term for every numeral;
the notation needs a canonical map out of that carrier, not one dictionary per
number. Laws such as preservation of addition belong to each target carrier's
API and are not prerequisites for writing a numeral.

`algebra` supplies the identity instance at `Nat`; `int` supplies `OfNat` at
`Int`. The Nat instance exists for generic `<A: Numeral>` code. Ordinary Nat
source bypasses it so loading `algebra` does not replace every numeral by a
dictionary projection.

## How a carrier reaches a nested numeral

The resolver uses the nearest available bidirectional anchor without replacing
the Nat inference default:

- A checking position retains the expected-result hint for a numeral-led
  operator spine, even when a later leaf also needs checking. Thus a body
  expected at `Int` reads `-3` as Int negation and `2 + 3` as Int addition
  before checking their operands. Ordinary argument and field checking carry
  the same evidence: `as_int(-1)`, `as_int(--1)`, and a negative numeral in an
  `Int` record field use this route.
- Without that hint, an inference-capable non-numeral operand supplies an
  anchor, including inside nested operator notation. With `a : Int`,
  `let x = -(1 + a)`, `(1 + a) + 2`, and
  `1 + (2 + a)` infer Int. The first such leaf in operand order wins; a
  tree without such an anchor keeps its first numeral's Nat default if no
  checking position supplies a carrier.
- An equation infers its left endpoint first when that endpoint has an
  anchor. Thus `1 + a = 1` checks the right numeral at Int. Only an
  numeral-bearing left endpoint without an anchor borrows the right
  endpoint's type: `3 = OfNat(3)` and `-3 = NegSucc(2)` are Int equations,
  while `3 = 3` remains a Nat equation.

This is intentionally bounded bidirectionality rather than delayed typeclass
metavariables. A genuinely unanchored `let x = 3` remains `Nat`, preserving the
language's deterministic Nat default without adding delayed numeral metas.

The shared `operator_carrier_leaf` traversal searches leaves in operand order,
stopping at the first one the caller can infer. It does not infer whole nested
operator applications speculatively: doing so would repeat the prefix at every rung
and make a left-associated chain exponential. It stops at ordinary calls,
annotations, and other non-operator forms; those expressions supply their own
inferred result type, rather than exposing their arguments as carrier hints.
An explicit work stack handles long operator spines. The syntax traversal is
linear in the visited nodes, in addition to the cost of candidate probes;
this does not claim linear total elaboration for a chain.

The search consults the existing checking-only classifier before probing a
leaf. In particular, `one<A: Numeral>() -> A` supplies no carrier: its result
type is precisely what checking must provide. In `-(1 + one())` at Int,
the expected carrier must still flow inward; in `-(1 + one() + a)` with
`a : Int`, the search skips `one()` and finds `a`. Equations use the same
policy, so `1 + one() = OfNat(2)` retains right-to-left checking. A named
wrapper such as `identity(one())` can hide the same need, which classification
alone cannot see: if its inference probe fails, the search continues to a
later anchor or falls back to the numeral. Every probe uses a cloned
elaborator, isolating goals, diagnostics, and derived evidence. Equation
ordering confirms that its candidate leaf can infer before giving the left
endpoint priority. The structural type elaborator receives that decision
through its service interface; it does not acquire declaration state.

## Boundaries

- `Fin` numerals remain indices and keep their existing bounds diagnostics.
- The parser and AST contain no negative-numeral form.
- Missing `Numeral<A>` evidence reports the ordinary instance-resolution trace.
- The class is optional at the language level. Before a module imports or
  declares it, non-Nat numerals retain the historical conversion refusal.
- This feature does not promise an efficient runtime representation. As with
  every specification-level class, compilation and data representation remain
  separate concerns.
- Carrier probing retains the operator resolver's existing assumption about
  nested notation: an operand leaf proposes a designation, and ordinary
  application checking validates its domains and result. This is not a
  general solver for heterogeneous operator trees.
- Unknown implicit argument types keep the existing inference policy. For
  example, an uninstantiated generic `identity(3)` can choose Nat before its
  surrounding result is consulted. Use a known argument type or explicit
  type argument when that boundary needs another carrier. Numerals are not
  added to the deferred-argument queue by this change.

## 2026-09-14: nested anchors and the reopened issue

The recorded `as_int(-1)` refusal no longer reproduces on the current line;
its checking path already rewrites prefix notation with the argument's
expected type. The missing regression is now pinned explicitly, alongside
double negation, a function-valued callee, record fields, and generic local
`Numeral<A>` evidence.

Two related failures did reproduce: `let b = -(1 + a)` probed the `1` and
missed `a`, and `1 + a = 1` inferred the right numeral first and imposed Nat
on the left. Both came from treating a numeral at the *leftmost* leaf as
proof that an entire operator expression lacked an anchor. The shared syntax
search above replaces that criterion at both the operator and equation seams.

`crates/elab/tests/carrier_numerals.rs` exercises the protocol on a separate
`Sign` carrier alongside Nat designations. `lib_std_int.rs` pins the actual
Int consumer. Negative controls cover false equations, missing embedding
evidence, nonliteral Nat values, named-call boundaries, and out-of-bounds Fin
indices. An intentionally nonidentity `Numeral<Nat>` instance checks that
ordinary Nat literals still take the intrinsic path.
