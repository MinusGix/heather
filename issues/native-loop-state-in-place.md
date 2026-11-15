---
title: Let a loop step update its state in place
status: closed
labels: [compiler,function-ir,x86,native]
created: 2026-09-28
updated: 2026-09-29
---

The typed generator protects every input register: a result's register must
be a temporary, disjoint from the inputs (`lower_structured_results`). A loop
step therefore needs a register per state field for the carry and another
for the payload, and then copies the payload back. With the loop's own
registers (base, length, cursor, budget, byte, maybe the needle) that caps a
state at about three fields: `docs/archive/native-wc-design.md` §4.4 has the count,
and `wc` works around it by letting the process count bytes.

The capability: a result may be placed in an input register when no later
result reads that input. Sequence the results in dependency order,
computing each into scratch and copying it into its field's register, or
writing it there directly. `wc`'s step has such an order (the word count
reads `inside` before `inside` is written). The certificate changes from
"inputs preserved" to "each input preserved until the result that
overwrites it". This is related to parallel copies and join placement
([[function-ir-x86-join-placement]]), but not the same problem: here no
cycle needs a swap.

Owner of the need: [[native-wc]].

## Log

- 2026-09-29: Built by the record loop generator (docs/archive/native-wc-design.md §4.6–4.7, ce46cd60 and 9c1b2321): each field is certified alone into scratch and copied home in a write order where none reads a register already written back; a cycle is refused. Closing.
