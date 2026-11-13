---
title: Design question: the three runtime languages each rebuild loops, calls and linking
status: open
labels: [native,runtime,design]
area: heather-in-heather
milestone: [hih-native-heather]
created: 2026-11-12
updated: 2026-11-12
---

The runtime language is three reflected languages, each with its own terms, meaning, lowering, loop form, reflector and class:

- pure terms over a world that is read (`Tm`, `rt.hthr`, `Compile`);
- computations over a file that is written (`FTm`, `rt_file.hthr`, `CompileSpan`);
- computations over Linux (`ETm`, `rt_io.hthr`).

They nest (a file computation's leaves are pure terms, [[native-one-compiler]] §2.6 and the U5 note), and that is right for the meaning: a pure region stays a total function of its words. The cost is that a feature is built once for each layer. A measured loop was built three times (`rt_loop`, `rt_file_loop`, `rt_io_loop`), a call node is three nodes with three linking lemmas, and the next features ([[runtime-fn-recursion]], several spans in a loop [[runtime-loop-over-several-spans]], a computation over `Io` that calls a writer [[rt-io-calls-functions]]) each meet all three.

## The question

Whether the control structure (let, if, loop, call) can be one language indexed by its effect, with the three layers as instances: a carrier `M` with `bind`, an event signature, and the leaf language as a parameter. The lowering would be proved once against a class of carriers that say what their `bind` lowers to. [[effect-interfaces-over-carriers]] and [[carrier-parametricity]] are the language-side pieces.

What argues against: the pure layer's theorem is unconditional and its meaning is a value, not a tree, and the proofs are much smaller for it. An index that makes pure terms pay for a monad would be a loss. So the candidate is two layers sharing one control language (file and Io), with pure terms as the leaves of both, as now.

## Done when

A design note says which, with the loop as its worked example, or this is closed with the reason the three stay.
