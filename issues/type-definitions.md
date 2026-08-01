---
title: Named type-level definitions, so a statement shape can have a name
status: closed
labels: [frontend, syntax, elaboration, design]
created: 2026-08-01
updated: 2026-08-01
---

`refines` cannot be a definition. The `fuel_monotone` round landed it as a
statement *shape* — spelled out verbatim in `refines_refl`, twice in
`refines_trans`'s hypotheses, and again in its conclusion — because a `fn`
body is an expression and `->` is not an expression, so there is no way to
write

```heather
type Refines(p1: Prog, i1: Ir, p2: Prog, i2: Ir, b: Nat -> Nat) =
    (env: Val) -> (vs: Val) -> (n: Nat)
    -> eval(n, p1)(env, i1) = Out(vs) -> eval(b(n), p2)(env, i2) = Out(vs)
```

(doc §13 note 7 records the gap; `docs/ir-simulate-design.md` §6 wants the
name, since `converges`/`refines` are the interface clients see.)

Two routes, not necessarily exclusive:

1. **A `type` declaration** — parameterized synonym, elaborated once,
   δ-transparent at its uses. Small, closed-form, no new typing questions
   beyond where it may be used.
2. **Types in expression position generally** — the motive-body round
   already added `ExprKind::TyLit` and parses a motive body with the type
   grammar ([[motives-as-lambdas]] log, 2026-07-31); `a = b` as a term
   already elaborates through its code `TmId : Ty l`
   (docs/surface-universe.md §13). Letting `->` into expression position
   would make a type-valued `fn` an ordinary `fn` and subsume route 1 —
   but it is a grammar decision with ambiguity surface, and codes cap the
   level ([[surface-universe]]).

Either route should answer: does the name survive into diagnostics (a
`Refines(…)` that unfolds on first mismatch is barely better than no name),
and does conversion see through it for free ([[schema-construction-caching]]
territory if not).

Customer list, so far: `refines` (three spellings today), `converges` once
[[surface-existential]] makes it statable, and every `Compile`-instance
obligation [[compile-typeclass-design]] will want to abbreviate.

## Log

- 2026-08-01: LANDED, route 2, and the issue closes. Types are expressions: `->` and `(x: A) ->` are admitted in expression position, so a type-valued `fn` is an ordinary `fn` and `Refines` has a name. Full write-up: docs/types-as-expressions.md. No kernel change, no new declaration form; route 1 (a `type` declaration) is now redundant and is dropped rather than deferred.

A1 (code coverage) — GATE PASSED, and more cleanly than expected. Every surface-writable type former has a code: Nat, Ty, El, Pi, Id, Sigma, Unit, Empty, Sum, W, Vec, Fin, Wf are all in `code_of`. The three kernel Type variants without one are UPi (layer m, never writable, [[surface-universe]] §7) and SEq/SEmpty/GlobalTy, which `crates/elab` never constructs at all (grep: zero occurrences). So Pi/Eq/Nat and everything `Refines` needs are covered with nothing left outside. CONSEQUENCE FOR THE BRIEF: the requested 'pin the uncovered-former diagnostic as a test' is IMPOSSIBLE — lib.rs's 'this type has no code' message is unreachable from any source text. It stays as the guard that keeps code_of's partiality from becoming an unwrap, but it has no input and therefore no test. Levels: code_of caps nothing; what caps is that Type<n> is written not inferred and universes are non-cumulative. `Refines` lands at Type<0> exactly (Level::max of zeros), and its quantifiers over Prog/Ir/Val/Nat->Nat all fit. `fn Bad() -> Type { Type }` is the level negative control (Type<0> is a value at level 1).

A2 (grammar) — GATE PASSED, and the conservative landing zone turned out to be unnecessary. `->` after an expression was ALWAYS a parse error before: the token occurs in four places in parser.rs and none follows an expression (group_is_type is a predicate; ty()'s binder group follows a `)` after a `:` the expr grammar lacks; a decl's `-> T` follows the param list's `)`; the retired `as z -> T` is caught by a two-token lookahead before any expr is parsed). Same for a leading `(x: A) ->`: `:` is not in the expression grammar. So the change is a pure extension with NO backtracking, and `->`/binder groups are allowed in EVERY expression position rather than a chosen subset. `=` binds tighter than `->`, matching ty() because there is one parse: parser.rs's new free `expr_as_ty` is the single reading of an expression as a type, shared by ty_atom's fall-through and the arrow's domain, and ty_atom UNWRAPS a TyLit so the old type grammar's output is byte-identical (no El-of-code for `Nat -> Nat`). [[annotated-let-swallows-the-equals]] is untouched — the annotation still parses with ty(). Not in the zone: `{x: A} -> B` (still the implicit-binder message), and `List<Nat> -> Nat` in expression position needs the domain parenthesised since `atom` reads `<` as `lt`.

THE DEFECT THE ROUND WAS WRITTEN BY. `El code ~> T` is a LAZY decode — decoding a code former leaves each child El-wrapped — so a type that arrives through an abbreviation is El-headed at every level below the first. Readers that whnf at each step (build_fields, the match field walk) were already fine; four STRUCTURAL readers were not, and now go through a new context-free `decoded` helper in inductive.rs: tag_of, read_tag, spine, and — the real one — tag_value, which emitted `<>` where a pair was needed. Tag 0's tag type IS Unit, so tag_value was correct for the first declaration in a file and wrong for every one after it: a checked-elaboration/kernel-NotConvertible, i.e. the 'wrong object' half of docs/testing-generated-terms.md, invisible to any single-declaration test. crates/elab/tests/types_as_expressions.rs §5 varies declaration ORDER for exactly this.

ACCEPTANCE, in lib/ir_v1.hthr: `fn Refines(p1: Prog, i1: Ir, p2: Prog, i2: Ir) -> Type { (env: Val) -> (vs: Val) -> Converges(p1, env, i1, vs) -> Converges(p2, env, i2, vs) }` — the fuel-map-free Converges-chaining shape, which is the right one to name since the bound is inside Converges and the relation then has exactly the four arguments it is about. refines_refl_conv, refines_trans_conv (both hypotheses AND the conclusion) and refines_of_bounded's conclusion are RESTATED through the name, spelled-out copies REPLACED not duplicated. The bounded form stays spelled out: it is refines_of_bounded's hypothesis and naming it would abbreviate one use.

COST — the guess was backwards. Naming Refines made the file FASTER: 35.96s -> 32.90s release (-8.5%), and the debug test binary 204 -> 194 CPU-s against the 300s rail. The statement is elaborated once instead of six times, and a delta-stuck head is cheaper to compare than the shape it unfolds to whenever the comparison succeeds first. Recorded on [[schema-construction-caching]].

DIAGNOSTICS VERDICT — mixed, good half is the half that matters. The name survives CONVERSION (delta is lazy; conv.rs's delta_head_ty looks through El), which is why naming is worth anything. It does not survive a type ERROR, but only because there is nothing to survive into: a kernel rejection is TypeError::NotConvertible with no types attached, which is [[cli-check-diagnostics]]'s standing complaint and predates this round. One NEW bad message, pinned as a test rather than fixed: a PARTIALLY APPLIED abbreviation is an ordinary value at `Nat -> Type<0>`, not a universe, so it says 'this is not a type' rather than an arity error. Correct and unhelpful; a diagnostics fix, not a typing one.

Tests: crates/elab/tests/types_as_expressions.rs, 23 new (grammar, neutral AND literal argument, open body, checking position, composition, records through the name at tags 0/1/2, a tier-1 value parameter, six negative controls incl. the level mismatch). Workspace 693 -> 716, all green.

Files: crates/syntax/src/parser.rs, crates/syntax/src/ast.rs, crates/elab/src/inductive.rs, lib/ir_v1.hthr, crates/elab/tests/types_as_expressions.rs, docs/types-as-expressions.md (new), docs/ir-simulate-design.md, docs/surface-existential-investigation.md.

NOT DONE: abbreviating an INDEXED family's formation through the same road — indexed.rs has its own copy of the constructor check and its own structural reader, neither touched. Untested; assume broken until someone tries it. Filed as the one follow-on in docs/types-as-expressions.md §7.
