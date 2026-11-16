---
title: Refinement between open components: CompCertO-style language interfaces
status: open
labels: [compiler,abi,semantics,design,research]
area: heather-in-heather
created: 2026-09-24
updated: 2026-09-24
---

Investigate **refinement between open components** in the style of
CompCertO (Koenig, Shao, *CompCertO: Compiling Certified Open C Components*,
PLDI 2021 — `docs/papers/compcerto-koenig-shao-pldi2021.pdf`), where correctness is
stated through *language interfaces* and *simulation conventions*: how two
levels agree at a boundary such as a calling convention or the syscall ABI.

## Why

The native line is about to cross exactly these boundaries: the syscall
ABI's register effects (RCX/R11 in [[linux-syscall-trace-model]]), calls
joining the fetched step relation, and foreign C imports
([[runtime-extern-c-abi]]). Today each certificate states its own boundary.
CompCertO's contribution is making the boundary a first-class object that
composes, so passes compose vertically and components horizontally.

## Acceptance (an investigation)

A note answering: (1) is a Heather ABI contract ([[named-abi-contracts]]) a
simulation convention, and what would composing two of them mean; (2) can
[[cross-ir-refinement]] be phrased as vertical composition of such
conventions; (3) what the syscall boundary looks like as a language
interface, and whether it is the same object as the event container in
[[interaction-trees-container-model]] (the paper's game-semantic reading
suggests yes).

## What it assumes from elsewhere

- **[[named-abi-contracts]]** owns what a convention says. Assumed here:
  only that it is a relation between caller and callee states, which is
  what a simulation convention is.
