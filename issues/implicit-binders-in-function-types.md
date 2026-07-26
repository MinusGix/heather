---
title: Implicit binders in function types and lambdas
status: open
labels: [frontend,elaboration,design]
created: 2026-07-26
updated: 2026-07-26
---

`{x: A} -> B` and `λ {x: A} => e`. Wanted, deliberately **out of scope** for
[[surface-function-types]], and split out here so it does not get lost as a
struck line in that issue.

Wanted because implicit arguments are useful on a function passed **by
value**, not only on a named declaration: the moment a `Compile` instance or
an optimization pass takes a lemma-shaped callback
([[compile-typeclass-design]], [[certifying-generator]]), that callback wants
its endpoints inferred exactly as `trans`/`sym` do today. Without this, every
higher-order use is `@`-spelled and the ergonomics that
[[elab-stage2-metas]] bought at the declaration level stop at the first
lambda.

## Why it did not come with function types

Structural, not effort. Implicitness is **not** in the kernel: `Type::Pi` has
`dom_level`/`cod_level`/`dom`/`cod` and no flag, and that is right — an
implicit argument is an elaboration concern, and the kernel must re-check the
saturated term either way.

Today it lives in the elaborator as `ParamMeta.implicit` on a *declaration*,
reached **by name**:

- `params_of` / `implicit_mask` (`crates/elab/src/lib.rs:1303–1315`) look the
  parameter list up in `self.globals` by the callee's name,
- `apply_implicit` (`lib.rs:1362`) consumes that `mask` to decide, per Π in
  the spine, whether to insert a fresh Ψ-meta or take the next argument.

So there are two gaps. A function **type** has nowhere to record the flag,
and a λ-bound **value** has no `ParamMeta` to look up. The consequence in the
current design is stated in [[surface-function-types]] §5.3: implicit
insertion is name-directed, so applying a function value is always explicit.

## What it would take

The flag has to travel with the type, without entering the kernel. The
options, roughly in increasing order of invasiveness:

1. **An implicitness spine beside the type.** The elaborator carries
   `(Type, Vec<bool>)` — or a small `FnShape` — wherever it carries a callee
   type, and `apply_implicit` reads the mask from there instead of from
   `params_of`. Cheap where types are built by the elaborator; the question is
   what happens to the mask when a type arrives from `whnf`, from a
   `GlobalSubst`, or out of an `inductive` field, where it is lost.
2. **A surface-level type wrapper.** Keep an elaborator-side type language
   that mirrors `Type` plus implicitness, and erase to `Type` at the kernel
   boundary. Honest and total, but it is a second type representation to keep
   in sync — the cost the codebase has so far avoided everywhere.
3. **Named-argument style instead of positional implicits** for function
   values, sidestepping inference. Not really the same feature.

Option 1 is the obvious first cut; option 2 is where it ends up if the mask
keeps getting lost.

## Sequencing

Not urgent while the surface has **no universe**: `TyKind` cannot say `Type`,
so `{A: Type} -> …` is not writable and implicit *value* binders
(`{n: Nat} -> …`) are the only expressible case. The feature becomes properly
valuable at the same time universe polymorphism reaches the surface, which is
layer-m work ([[elab-unifier-completeness]] notes level-meta inference is
naturally sequenced there too). Likely picked up with, or just after, the
trait layer.

Until then `{` in a function type or lambda binder is a diagnostic pointing
here ([[surface-function-types]] §8).

## Log

- 2026-07-26: Split out of [[surface-function-types]], whose scheme doc found
  the structural reason implicit binders could not ride along with function
  types. Kept as its own issue at the user's request: implicit arguments on a
  by-value function are a real feature, not just a symmetry with `fn`.
