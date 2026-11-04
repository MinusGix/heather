---
title: Audit the recorded proof workarounds and gotchas against master
status: closed
labels: [proofs,tactics,frontend,documentation]
area: tactics
created: 2026-10-29
updated: 2026-10-29
---

Rounds since 2026-10-08 recorded about 110 workarounds and gotchas in the
project's notes, round docs and issues ("closed facts by `Bool = True`
refl", "prove at a neutral width", "spell `n.is_zero()`", "omega treats
`a - b` as an atom", "string literals need `import bool`", …). Some were
fixed since and are still being taught; some are real gaps nobody owned;
some are how Heather is meant to be used and were only ever written down in
passing. This audit re-probed each against master 4f0ac27 (PR #252) with a
release build, small `.hthr` probes, `--timings` and a fresh cache, and
sorted them. The surviving rules are [docs/proof-patterns.md](../docs/proof-patterns.md).

## Real gaps, filed

- [[omega-nat-truncated-subtraction]]: `a - b + b = a` from `b <= a` refused.
- [[omega-closed-field-value-atomised]]: a record field read at closed
  arguments becomes an opaque atom (the native layouts' case).
- [[omega-nested-conjunction-facts]]: `a < b ∧ (b < c ∧ c < 5)` read one level.
- [[omega-redex-typed-fact-ignored]]: an `Exists`'s `.proof` is skipped.
- [[checking-tactic-in-inference-position-diagnostic]]: `let k = omega(h);`
  says "unbound name omega".
- [[closed-verdict-evaluated-twice]]: `trivial`/`decide` at a closed
  `IsTrue(b)` cost about 2.2× a `b = True` refl (527K vs 231K steps).
- [[repeated-parameter-name-shadows]]: `fn dup(x: Nat, x: Nat)` accepted.
- [[self-reference-hides-same-named-global]]: inside `Prog::Sim`, `Sim()`
  is refused as an unguarded recursion with no hint at the global.
- [[statement-leading-list-literal-parse]]: `theorem t(): [1] ++ [2] = …`
  does not parse.
- [[recursion-guard-takes-nearest-parameter-match]]: a self-call under a
  split on another parameter is refused.

Logged on existing issues: [[literal-classes-need-importing]] (string half
fixed by PR #250, byte half still real), [[feature-implicit-module-dependencies]]
(`∑` at Nat needs `algebra_rel` and `semiring`), [[list-literal-left-of-append]]
(still refused).

## Fixed with this audit

- `heather check --only nat::Nat::add_comm` (or `Nat::add_comm`) was
  refused for every owner-qualified name: the spec was split at its last
  `::`, so `Nat` was read as the module. Now the module is the first
  segment when the closure has one by that name
  (`crates/cli/src/main.rs`, test `only_reads_owner_qualified_names`).
  This is the "`--only` refuses on warm reruns, not investigated" note from
  PR #197.
- `omega` refused a negated relation as its goal (`a ≠ b`, `¬(b <= a)`):
  "expects False or an affine relation goal". It now assumes the relation
  and refutes it (`reconstruct` in crates/elab/src/omega_cert.rs; probes and
  a control in lib/_tests/std/tactic/omega_tests.hthr).
- Eight unused-payload lint warnings on master (lib/std/data/list.hthr from
  PR #251, lib/std/bitvec/bitvec.hthr since the lint landed): the library
  gate does not fail on warnings, so they drift.

## Already fixed on master (the notes were stale)

| Recorded gotcha | Fixed by | Probe |
|---|---|---|
| A Nat `match` on a literal whose arms call an enclosing recursion is exponential; spell `n.is_zero()` | [[kernel-fold-probe-evaluates-recursive-arms]] (PR #185) | `walk(24, 3) = 24` by refl: 10 steps |
| String literals need `import list; import bool; import char;` | [[literal-needs-module-names-wrong-module]] (PR #250) | `import string;` alone |
| cat capped at 256: `next_rip` iteration hits the depth limit | [[native-compile-address-depth]] (PR #183), [[eval-native-frame-size]] (PR #187) | cat at 1024 in lib |
| Width-64 runs thrash the kernel's 64K value cache | [[kernel-value-cache-evaluation-thrash]] (PR #141) | |
| A computed count is re-forced in nearest rounding | [[computed-argument-reevaluated-in-rounding]] (PR #141) | |
| A `match` on a trace witness under a computed binder costs 20–170× | [[trace-match-under-computed-binder-cost]] (closed) | |
| `absurd` reduces computed sides by substitution | [[absurd-reduces-computed-sides-by-substitution]] (closed) | |
| Every `Tac` mention spells its W lowering into the image | [[tactic-module-image-size]] (PR #227) | |
| `split_all` on a match nested in a scrutinee builds a kernel-rejected term | [[split-all-nested-scrutinee-kernel-reject]] (PR #170) | |
| An unused `let` of a refused constructor elaborates | [[unused-let-value-unchecked]] (PR #147) | |
| `ring` refuses a reading with unspellable atoms (`x.seq(n)`) | closed by PR #231 (aliased atoms) | |

Not reproduced at the shape recorded (probably fixed in passing; dropped
from the guide, reopen with a probe if one returns): a parameter named `j`
shadowing the `j` eliminator; `case` as a binder name; a λ body starting
with `[` parsing as a vector type (in a body or an argument); `let h: (x) → T`
needing parentheses; `||` and methods on an unannotated binder in a motive;
a method call on a `match`; `let x = match …` and `(match …).map(…)` without
a motive; a receiver call `.name()` inside `fn X::name` taken as recursion;
`omega` missing `List::len` of a literal list; `omega` inside `match` arms
over an `Or`; `Nil<…>` in a motive.

## Real and already owned

[[setoid-surface-kernel-cost]], [[rewrite-by-ih-after-unfolding]],
[[nested-match-on-list-tail-motive]], [[deep-pattern-dependent-later-field]],
[[codata-nested-guards]], [[all-numeral-relations-default-to-nat]],
[[parameter-defaults-mention-type-parameters]], [[partial-type-application]],
[[elab-whnf-copies-straight-continuations]] (the Wp `drain_pass` workload),
[[native-tool-test-cold-certificate-rail]], and [[omega-listed-facts-only]],
which waits on a decision (does a listed call read only what it lists).

## Design, documented rather than filed

Lockstep conversion of two computations, sharing by closure identity,
proving at a neutral parameter, stage theorems with written statements, the
λ annotation rule, convoys, recursions that vary a parameter returning a
function, `absurd` only at constructor clashes, tier-2 laws needing funext,
`+` in a section meaning the carrier's, generated-source spellings, and the
diagnosed syntax rules (`let p: (a = b)`, defaults by name, declare before
use, unqualified record names, reserved binder names, `Zero`/`Succ` built
in, ASCII identifiers, `0 + p` not `p`). All in docs/proof-patterns.md.
