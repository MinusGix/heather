---
title: Emission walked every annotation's whole type for code literals, and name resolution paid a string searcher and SipHash per name
status: closed
labels: [elaboration,performance,kernel]
area: language
created: 2026-11-10
updated: 2026-11-11
---

With the kernel gate's constants taken down
([[free-variable-bounds-in-the-node]] and the changes before it), a whole
cold check's instruction profile had three leaves outside the gate that
were each larger than anything left inside it, and none of them was doing
work that had to be done.

## What cost

- **`inductive::decode_deep`**, the emission chokepoint's first step
  (`Elaborator::emit_ty_in`). It answers "is any type component the
  decoding of a code literal?", nearly always no, by walking the whole
  type as a tree: every annotation written, every shared component
  again. On top of that `decoded` built an empty context before looking
  at the node it was given.
- **`names::split_qual`** was `name.split_once("::")`. A two-byte pattern
  builds a `StrSearcher`, the two-way algorithm's preprocessing, per call,
  and resolution splits every name it keys, several times.
- **The name tables** (`Names`' and `Types`' layers) were `HashMap<String,
  _>` under the standard library's SipHash, hashed once per layer probed
  after the layer index had already hashed the name with its own word
  hash.

## What is built

- **A node can carry a client's mark** (`heather_kernel::rc::Mark`,
  `Rc::mark`, `Rc::marked`): a spare bit of the head
  [[free-variable-bounds-in-the-node]] put beside every syntax node. The
  kernel reads none, so nothing it decides depends on one; the client owes
  that the property is a function of the node's value alone, and
  `Rc::make_mut`/`Rc::get_mut` empty marks with the rest of the head.
- **`decode_deep` asks a node once.** A component that had nothing to
  decode is marked `Mark::DECODED` and answered from the mark afterwards.
  `None` is a function of the type alone (the decode steps in the empty
  context under opaque definitions). A component that did decode is not
  marked and decodes again at its next emission, as before.
- `decoded` looks at the node before it builds anything.
- `split_qual` is a byte scan, held to `split_once` by a unit test.
- The name tables hash with the layer index's word hash and its avalanche
  (`layered::NameHasher`, `NameMap`, `NameSet`).

No term changes: every count column of the showcase's `--timings` is the
same.

## Left open

- A component that *does* hold a code literal is decoded again at every
  emission (what is left of `decode_deep` after this). Keeping the decoded
  node would also give the kernel one node where it now gets equal copies,
  so it moves conversion's counters and wants its own measurement.
- `Elaborator::instance_match_entry` is now the larger half of
  `emit_ty_in`: about ten thousand misses of its memo a showcase, each a
  hundred thousand instructions.
- Resolution still asks the tables about a name many times over (twelve
  million string hashes for the showcase's few thousand declarations).
  The hash is cheap now; the number of questions is the same.

## Log

- 2026-11-10: Built. Callgrind over a whole cold check of
  `docs/showcase/calc_parser.hthr`, width one: 51,332 M instructions to
  47,449 M (−7.6%). By piece: `decode_deep` 3,421 M to 1,466 M inclusive
  (19.6 M recursive visits to 78 K; what remains is 1.87 M real decode
  steps), `emit_ty_in` 3,542 M to 1,796 M, `split_qual` 1,117 M inclusive
  to inlined and not visible, string hashing 1,095 M to 59 M.
- 2026-11-10: Two more of the same kind, over the same profile. `inductive::field_scope_cx` named every binder of a field scope `#use-site` by allocating the string per binder; it shares one (`Binders::all_named`). `names::qkey` built `module::name` through `format!`; it reserves and pushes. With the kernel's two arena changes of the same day ([[value-domain-allocation-constant]]'s log) the whole cold showcase is 46,740 M instructions, −8.9% from 51,332 M, every count column the same.
- 2026-11-11: Seconds for the seven changes together, `scripts/perf ab --mode cold` on the showcase, cloud box, the node-head tip against this one, 45 count columns identical. Width one, seven interleaved samples on a quiet box: wall 12.60 to 13.99 s before, 11.93 to 13.20 s after, median -5.3%, and the sample sets overlap, so by the tool's rule this is no result; kernel gate -1.5%, no result; peak RSS no change. Eight workers, five samples (the box was not quiet): wall median -2.9%, no result. What the changes are held to is the instruction count (51,332 M to 46,740 M over the whole check), which does not show as a separated wall time on this box.
