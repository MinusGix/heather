---
title: tr: a certified program that writes after every chunk
status: closed
labels: [x86,native,program]
created: 2026-09-30
updated: 2026-09-30
---

The third real program after `wc -l` and `wc` ([[native-wc]]): `tr a-z A-Z`
as a certified static executable. It breaks the read-everything-then-write
template twice. It writes inside the read loop, so read and write histories
interleave. And it stores a byte for every byte it reads, translating each
chunk in place before writing it back. Its claim has no bound on the input.

Design: `docs/native-tr-design.md`. The byte map is lowered through the
compiler (needs [[function-ir-narrow-arithmetic]]'s add/subtract, slice N);
the map loop and the process are library code proved once. `tr -d` and
`tr -s` are [[native-loop-emitting-stores]].

## Log

- 2026-09-30: 2026-09-30: Decisions (user): translate only; the byte map lowered through the compiler (the 256-byte table recorded as the alternative, design §6). Probe V2 found narrow add/subtract refused; slice N added it (design §4.2, [[function-ir-narrow-arithmetic]]).
- 2026-09-30: 2026-09-30: Slices N, A, B landed (0ec1173d, 5776d302, a71d9f65; suites 3129+flaky, 3130, 3130). Slice C (lib/elf64_read_map.hthr, read_map_runs + map_sends) checks; first version's map_byte took ~524 s of kernel gate at width 1 (97M steps) from let-inlined machine states, split behind `have` records it is ~2 s (design §3.1).
- 2026-09-30: 2026-09-30: Slice D landed: `build-x86 examples/x86-native/tr.hthr upcase --map` builds a 619-byte ELF that matches host `tr a-z A-Z` (native_tr: sizes around page boundaries, streaming before EOF, failed read and /dev/full exit 1, two refused builds). Library offsets take the piece length so the producer's jump facts rewrite with `_byte_length`. Suite 3133. read_map_process at 140 CPU-s in the full suite (70 alone), under the 300 CPU-s rail. Closing: -d/-s are [[native-loop-emitting-stores]]; narrow signed comparisons stay with [[function-ir-narrow-arithmetic]].
