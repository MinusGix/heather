---
title: A template instance was substituted and decoded again at every asking
status: closed
labels: [elaboration,performance]
area: language
created: 2026-11-11
updated: 2026-11-11
---

A use site that meets `El (app(D#tycode_fn^δ; ā))` asks for the inline lowering behind it: the declaration's template at `ā` (`gendefs.rs`, `instance_of_template`). Each asking substituted the arguments into the template and decoded the result (`inductive::decode_deep`), and the same instance was asked for again and again.

## What that cost

Checking `examples/x86-native/levels.hthr` cold at width one, under callgrind (whole run 117,741 M instructions, of which about 15,100 M is SHA-256 on the scalar path valgrind forces; a real run does not pay that part):

- `instance_of_template` was called 75,219 times and cost 5,615 M inclusive: 4,563 M in `decode_deep` (13.2 M one-level decodes through `reduce::step_type`) and 1,021 M in `Type::apply_local`.
- Counted by the template and the arguments' printed form, those are about 5,600 distinct instances. The most asked one, a width-indexed type at the literal `64`, was built 3,698 times; a bare `Nat` argument 2,693 times; one Σ code 2,524 times.
- Counted by the argument **nodes**, they are 59,424 distinct. So a table keyed by address would have caught a fifth of them. The arguments are equal and seldom the same nodes: a numeral is a node per mention, an argument read out of a substituted type is that substitution's copy, and `inlined_arguments` builds a new code for every type argument it replaces (16,072 of the calls had such an argument).

On the showcase (`docs/showcase/calc_parser.hthr`) the same function was 721 M of 41,076 M, over 26,435 calls.

## What is built

The instance is a function of the template and the arguments and of nothing else (no registry, no Ψ, no scope: the substitution's tail is the empty one). So a thread keeps the instances it has built (`gendefs::Instances`), by the template's address and a hash of the arguments' outer shape, and a hit is an entry whose arguments compare equal. The entry holds its template, so the address stays that template's.

- The shape (`args_shape`) reads the formers, literals and variables in the first 48 nodes of each argument, through code formers and applications. It only chooses where to look.
- A template nothing else holds was computed for one question (`Elaborator::constructor_spelling`) and is not kept.
- A debug build builds a sampled hit again and compares.

## The table's size, measured

The first version kept every instance (a bound of 16,384, never reached). It answered 92% of the askings and held 46 MB more at the certificate file's peak (+5.8% of peak memory, the sample sets separate), 10 MB more on the showcase.

The askings for one instance come close together, so a small table that starts over when it is full does nearly as well:

| table | built, certificate file (of 75,219) | built, showcase (of 26,435) | peak memory |
|---|---|---|---|
| none | 75,219 | 26,435 | baseline |
| 1 | | 20,862 | baseline |
| 128 | | 4,242 | baseline |
| 256 | 8,651 | 3,463 | baseline |
| 1,024 | 6,760 | 2,829 | baseline on the certificate file, +3 MB on the showcase |
| all | 5,645 | | +46 MB, +10 MB |

256 is what is built.

## Result

`instance_of_template`, certificate file: 5,615 M to 1,000 M instructions (595 M comparing arguments, 298 M building, 65 M dropping a full table, 34 M shapes). The whole run: 116,563 M to 110,969 M. Showcase: 41,076 M to 40,405 M.

Equal instances are now one piece of syntax, so everything downstream that stops at a shared node does. The run's counters move slightly for that reason (`local_subst_nodes` −6.4%, `syntax_eq_nodes` up by the argument comparisons, conversion and evaluation counts within 0.2%).

In seconds, on the certificate file at width one (`scripts/perf ab --mode cold`, five interleaved pairs, three runs with three sizes of table): medians −5.1% (the sets separate), −5.5% and −1.2% (they overlap). The box does not resolve it consistently.

## Left open

- What is left is comparing equal arguments on different nodes (595 M). The arguments would be the same nodes if `inlined_arguments` did not build a new code for every type argument, which is itself 720 M of `code_of` on this run; that function reads the registry, so keeping its answers needs the registry's rules and is not done here.
- `instance_match_entry` walks the template against the subject twice (`Holes::ty`, 2,267 M) and decodes each recovered code (766 M).
