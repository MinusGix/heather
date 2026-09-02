# Generated Heather construction API

## Purpose

Compiler and certificate generators need to construct substantial Heather
modules. Building those modules as interpolated strings makes names,
parentheses, named arguments, projection binding, declaration layout, and
proof blocks all implicit in unrelated formatting code. `heather_emit` is the
Rust-side emission IR for that boundary.

It is intentionally smaller than the surface AST and much higher-level than
kernel terms. A generator constructs `Expr`, `Parameter`, `Statement`,
`Block`, `Declaration`, and `Module` values. The module is serialized once,
then passes through the ordinary parser, elaborator, and kernel checker.

## Current expression vocabulary

The API represents:

- names and natural literals;
- positional and named calls;
- projections;
- equality;
- list literals;
- lambdas;
- explicit `let` and expression statements; and
- an explicit `Expr::raw` escape hatch for syntax not migrated yet.

Calls and lists choose a deterministic flat or multiline layout at a fixed
line width. Declaration spacing, binder layout, block indentation, and named
argument punctuation have one implementation. Generated names may still use
Rust formatting; generated Heather syntax should not.

`Expr::raw` is deliberately visible in review. It is not an implicit string
conversion and therefore marks the exact remaining migration boundary. New
forms should be added when multiple callers need them; the goal is a useful
compiler construction language, not a hurried clone of every parser node.

## Why rendering remains the first sink

Constructing kernel terms directly is the wrong initial optimization. It
would require generators to reproduce or bypass:

- name and namespace resolution;
- implicit and solver argument insertion;
- record and constructor metadata;
- expected-type-directed syntax;
- elaborator diagnostics and source identity; and
- the ordinary independent re-checking boundary.

Those are elaboration responsibilities, not instruction-selection
responsibilities. Direct kernel construction would also make generated
certificates less inspectable while moving more semantic responsibility into
Rust.

An alternative sink may eventually lower the same emission IR into elaborator
input data without a text parse. That optimization should preserve ordinary
name resolution and elaboration, and should be justified by a measured parsing
or allocation cost. [[generated-heather-direct-elaboration]] tracks that
question. The construction API is deliberately independent of the rendering
sink so such an experiment does not affect compiler clients.

## Adoption

The source-to-FunctionIR frontend constructs its source-denotation theorem and
source-level `BlockArtifact` entirely through this API. The common
straight-line x86 header also uses it for instruction values, instruction-list
spines, byte lists, byte lengths, and decoding declarations. That complete
header slice contains no raw Heather syntax.

The nested-source frontend also uses the API for its scheduled node-list
suffixes, graph-equation projections, per-node value theorems, operation
lambdas, and final source specialization. Generated names are the only string
formatting in that semantic proof path.

The older FunctionIR validity and x86 proof generators can migrate
declaration-by-declaration. `Module::raw` permits composition with their
already-checked output during that transition; it should not be the default
for new generators.
