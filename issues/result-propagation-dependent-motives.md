---
title: Preserve written dependent motives through non-tail Result propagation
status: open
labels: [frontend,elaboration,proofs,design]
area: language
created: 2026-09-14
updated: 2026-09-14
---

[[result-propagation]] keeps a non-tail written scope separate from its outer
continuation by packaging the scope's success value in a local Result.
An explicitly written match motive names the original value type; reusing it
for the locally packaged Result would be wrong. The parser refuses this case
with a suggestion to use a Result-returning helper. Tail matches and inferred
motives use ordinary matching.

A future slice should transform the motive with the actual error carrier in
hand, likely at elaboration time. Preserve dependencies on the scrutinee and
convoy evidence, and test an open indexed family, a neutral scrutinee, and a
false-equality control. No schedule until a concrete client needs this form.
