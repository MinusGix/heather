---
title: Whether + and * should mean or and and at Bool
status: open
labels: [stdlib,frontend,design,traits]
created: 2026-08-09
updated: 2026-08-09
---

User doubt at the operators round's close (2026-08-09): lib/std/algebra.hthr designates +@Bool=or and *@Bool=and — the semiring convention, which some mathematics uses and which reads as weird at a Bool in a programming context. Options, with the coordinator's lean recorded: (i) delete both Bool designations now — the library already writes mconcat(or, bs)/mconcat(and, bs) explicitly, so only sum_all-at-Bool and its tests are touched; (ii) the real answer: || and && as the programming spelling, which is a lexicon extension owned by [[notation-extensibility]] (the operators round deliberately added no tokens), with the Boolean monoids designated there and +/* left to numeric-ish carriers; (iii) keep the semiring convention, documented. Lean: (i) then (ii). Note what does NOT change under any option: both CommMonoid<Bool> instances stay registered as equals, op_unit_of_comm stays generic (its (+) is the bound index's local name, not a designation), and nothing renominates — this is purely a question about what two SYMBOLS mean at one carrier, which is exactly the small question the designation table was built to make small. Trigger: next session touching lib/std or the operators line.
