---
title: A program builder that lowers named, structured programs to the effectful source
status: closed
labels: [native,frontend,ergonomics]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-27
---

Round 5 of `docs/native-real-programs-plan.md` (§3.3, §5, §6). A `Source`
is written as a hand AST over numbered words (`lib/native/native_cat.hthr`).
A leaf holds at most 14 values and may not write a word it reads, and loops
test bits the program sets itself. No real tool can be written this way.
The decided surface (uniqueness threading, [[effects-direction]]) is a
language round. This round builds the layer it will target.

## Scope

- `lib/native/native_build.hthr`: a structured program type with named words
  and buffers, expressions, `let`, `if`, `while`, `for` over a buffer's bytes,
  `read`/`write`/`exit`, and procedures inlined at build. A Heather function
  lowers it to a `Source`. It allocates ids, splits expressions into leaves
  that fit the register pool, adds temporaries for in-place updates, and
  makes the bits `Branch`/`Repeat` test. No proof: a tool's meaning is the
  `Source` it lowers to.
- Pure helpers written as ordinary Heather word functions, inlined as their
  reflected FunctionIR regions (the `compile-x86` reflector,
  `crates/elab/src/function_ir_source.rs`), with the reflector's agreement
  certificate.
- `write-elf` evaluates the lowering on its fork and states
  `<s>_lowered() = literal` by `refl`, then compiles the literal, so the
  builder's evaluation is not part of the emission check.

## Done when

`tr` and `head -c N` are rewritten in the builder, and a `wc -l` that
reports its count as the exit status builds and runs.

## What it assumes from elsewhere

- **[[native-source-bytes]]** owns the byte nodes the builder emits.
- **[[native-compile-wider-leaves]]** owns the region forms (conditionals,
  bounded loops) an inlined helper lowers to. Until it lands, the builder
  emits only dataflow leaves.
- **[[effects-direction]]** owns the eventual surface, which elaborates into
  this builder or straight into `Source`.

## Log

- 2026-10-26: [[native-source-bytes]] landed: the nodes are `BufferLoad(output, buffer, index)` and `BufferStore(output, buffer, index, value)`, and until [[native-compile-wider-leaves]] splits leaves, each must be a `Compute` leaf of its own (a leaf mixing them with pure nodes is refused). `lib/native/native_tools.hthr`'s tr is the hand-written shape.
- 2026-10-27: Done, with reflected helpers split out to [[native-build-reflected-helpers]]. `lib/native/native_build.hthr`: a `Tool` binds its buffers (`buffer`, `buffer_of`) and words (`local`) with Heather lambdas; values are `Val` (sums, bit operations, shifts, comparisons, `ByteAt`); statements are `Act` (assign, `Poke`, `When`, `While`, `DoWhile`, read, write, exit), sequenced by `++`; procedures are Heather functions returning `Act` (`for_count`, `each_read`, `write_all`). `Act` has a function field, so (docs/inductive-tier2-w-lowering.md §2.2) its two-part constructors hold their parts as `Bool → Act`. `Tool::source` numbers words as binders are met, gives each statement temporaries past them, writes an assignment's last node into its word unless the node reads it, and cuts the nodes into leaves greedily with `List::fits_leaf`, a copy of what `Prog::computes` takes (pure within the pool and `leaf_checks`, in-leaf reads at their written width, or one byte node). That predicate is the one thing [[native-compile-wider-leaves]] should relax. `lib/native/native_tools.hthr` holds cat, tr, yes, `head -c 10` and `wc -l` written this way (`native_cat`'s cat stays the one the spec proofs read); `crates/cli/tests/native_tools.rs` runs tr, yes, head and wc beside GNU's. `lib/_tests/native/native_build_tests.hthr` fixes the lowering of four small tools by `refl`. `write-elf` now reads every source back (`Source::spelled` in `lib/native/native_source_spelled.hthr`, which it loads for every program; crates/cli/src/native/lowered.rs), states it as `<s>_elf_lowered()` (subtrees past 48 statements and nodes as definitions of their own) with `<s>_elf_lowered_is` by `refl`, compiles the literal, and carries `<s>_elf_simulates` back to the source; a source with functions or a region past a dataflow leaf is compiled as it is. On `wc -l` the literal took the build's own declarations from about 6.8M to 4.8M kernel steps, with the same bytes. Elaborating `native_build` itself is slow for its size (its `Act` is a tier-2 inductive; about 25 s on the debug binary), paid once per image store and only by programs that import it.
- 2026-10-27: Wide leaves ([[native-compile-wider-leaves]], #218) adopted: an assignment writes its last node into its word even when it reads it (`x := x + y` is one node), and `List::takes` (replacing `fits_leaf`) grows a leaf while S4 takes it whole, else lets a leaf S4 does not take (byte nodes, in-place updates) take further nodes S4 would not take alone, a node at a time. Measured on the five tools (write-elf bytes): every leaf wide, 64-bit bit logic: larger (yes 1259 → 1295, cat 1428 → 1489); this rule: smaller everywhere (head -c 1535 → 1437, wc -l 1464 → 1444, tr 2087 → 2066, yes 1259 → 1230, cat 1428 → 1411). Also fixed `Stmt::leaf_names` on master: it counted label names only for a one-byte-node leaf, so write-elf refused every wide leaf with a byte node (#216 and #218 crossed); it now folds `Node::names_after` over the leaf (probe `wide_names_counted`).
