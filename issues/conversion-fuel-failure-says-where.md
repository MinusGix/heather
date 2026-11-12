---
title: A conversion that runs out of fuel does not say where the steps went
status: open
labels: [diagnostics,kernel,elaboration,performance]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-12
---

Three rounds now have found a conversion-budget failure only by patching the compiler to count ([[runtime-measured-instance-conversion-budget]], [[runtime-link-compares-functions]], and [[runtime-measured-reader-heavy-callee]] is waiting on the same). The message is the whole of what a user gets:

> an argument's type could not be compared with the expected type within the conversion budget (1048576 steps): the comparison ran out of fuel, which is not a mismatch

or, from the gate, `the kernel rejected f::compile: OutOfFuel`. Neither says which subterms the steps went to, and the terms are too large to read (a dump of the two sides of one link was gigabytes).

What found the last one, kept as a patch outside the tree (`host-conversion-ladder.patch`, in the project's shared files), is small:

- **A ladder**: the failed comparison run again at doubling fuel until it passes, so the cost is known and "infinite" is told from "twice the budget".
- **Unfoldings by head**: a count of δ-steps per global over the failed run, top forty by name. A function's own body among them is the sign that something is being evaluated that should have been compared.
- **Same-head attempts**: where `Conv::tm_w` compares two applications of one global argument by argument before unfolding, a line for each attempt over a threshold with the head, its cost and whether it succeeded. A failed attempt at a large cost names the pairing; this is the line that found the link.

It runs only where the elaborator's own budgeted comparison fails, not where the kernel gate does.

## Scope

- The three counters behind a flag (`heather check --explain-fuel`, or an environment variable as the patch has it), for a host failure and for a gate rejection of a named declaration (`--only`).
- No dump of terms by default; heads and counts only.
- Counting must cost nothing when off: the same-head line is in the kernel's conversion, which has no logging today, so it is a counter the caller reads and not a print, and that part is a kernel change, Minus's to accept.

## Done when

The reproduction in [[runtime-measured-reader-heavy-callee]] is located with a flag and no patch.
