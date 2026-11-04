---
title: Host requests for reading a definition's body: Body, λ and match-arm views, shared subterms
status: open
labels: [native,metaprogramming,host-interface]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-01
---

Slice R5a of `docs/runtime-fn-setups-design.md` (§3.2, §13): the host
requests a `runtime fn` generator needs to read a definition's elaborated
body. `View` was built for tactics, which read goals and never a
definition's code.

## Scope

- `Body(g: GlobalRef) → Checked<Handle>`: a definition's elaborated value.
  Refused, with the reason, for a theorem, an axiom, a constructor or a
  global with no body. An `interface fn` is not refused (boxing is
  intensional analysis, not conversion in a proof).
- λ in a view (`HLam(dom)`), opened by `Open` into a host local as a
  function type's binder is today.
- `match` with its arms (`HCases(scrut, motive, arms)`): each arm's
  constructor, its fields opened as locals, and its body, as `Cases`
  presents a split goal. Equation binders (`match h: c`) appear as a local
  whose type is a proposition.
- Sharing by identity: the same handle for the same shared subterm within a
  run (or a `Same(a, b)` request), so a reflector can memoise and rebuild a
  block's aliases as lets. A block's `let` is an alias, so the kernel term
  has only a shared subterm (`docs/let-and-blocks-design.md` §4.4).
- Record the cost as a shape against the body's DAG size. If one request per
  node dominates, add a bulk `Reflect(h)` answering a tree of heads with
  shared nodes numbered.

## Done when

The prototype reflector (`runtime-fn-reflected-language`) reads every
body under `examples/x86-native/` through these requests, with a shared
subterm read once (V5 of the design note).

## Log

**2026-11-01 (R5a).** Built in `crates/elab/src/host.rs` and
`lib/std/tactic/tactic.hthr`:

- `Body(g)` (request 22): a closed, monomorphic definition's value, its
  parameters as `λ`s; refused with the reason for a global with no body
  (theorems keep no proof, axioms have none). Constructors are not globals
  with bodies, so the "refuse a constructor" case does not arise.
- `HLam(dom)` in a view, and `Open` of a handle to a `λ` (a term handle
  now opens as a type handle does: a local of the domain, the body a term
  under it).
- `HCtor(ty, i, name, fields)` in a view: a constructor value, read by the
  display's own recogniser (`Elaborator::view_ctor`), so `WcState(a, b, c)`
  and `True` are presented, not `HOther`.
- `Arms(h)` (request 23) instead of an `HCases` head: `View` keeps `HMatch`
  for the tactics that read it, and `Arms` answers the scrutinee, one arm per
  constructor as a handle to a `λ` over the payload, and the arguments the
  match is applied to (`refl` for `match h:`). Two-constructor matches only;
  wider ones nest `Case`s and are refused until a reader needs them.
- One handle per shared subterm per scope (`Run::issue_shared`, keyed on
  the address). It works, but elaborated bodies turn out not to share
  let-bound values ([[elaborated-let-sharing-lost]]), so the reflector also
  numbers values.

The reflector (`lib/native/runtime/rt_reflect.hthr`) reads the bodies of
`branches.hthr`, `calls.hthr` and `sharing.hthr`, a record step, a `foldl`
and a `match h:` through these requests
(`lib/_tests/native/runtime/rt_tests.hthr`). Not yet: the loop examples'
`decreases` bodies (the reflector would need `f#rec`, and the pin needs
[[decreases-unfold-convoy-scrutinee]]), enum matches, and a cost shape; a
fresh `heather check` of the test module is dominated by checking the tactic
library, and each reflection is a few hundred requests.

Note for merging: the facts-on-demand round appends `Synth` to `Req` as
tag 22 too; whichever lands second renumbers.
