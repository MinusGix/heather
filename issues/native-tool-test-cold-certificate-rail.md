---
title: Keep cat's native test under the CPU rail when its certificate is not cached
status: open
labels: [native,tests,perf]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-28
updated: 2026-10-28
---

`compiled_cat_files_runs_as_gnu_cat` (`crates/cli/tests/native_tools.rs`)
dies at the suite's 300 CPU-s rail on a cloud box the first time it runs
after any library change, and passes on the next run. It died with only
"checking `cat_files_tool`'s compile and its 21896 bytes" printed, so the
kernel's check of the certificate was what was running.

Why, measured on 2026-10-28 with the test-profile binary
(`--timings`, after #251 and #255): write-elf's own reads (the parts, the
byte reads, the probe) cost about the same either way, roughly half the
rail. The check of `cat_files_tool_elf_certificate` costs more than the
rest of the run together, and runs only when the verdict store does not hold
it. A library edit changes the certificate's imports, so the next run checks
it cold. Warm, the whole write-elf run is about half the rail. On the
pre-#251 sources the cold certificate cost more again, though that run also
elaborated the library cold beside it, so it shows only that this is not a
regression from #251 or #255. The certificate check, by kind
of statement, is mostly the per-statement `{p}_at_` and `{p}_checked_`
parts.

## Scope

- Find what the `{p}_at_` and `{p}_checked_` statements spend: there are
  hundreds of each. Either a shared lemma is re-proved per statement, or
  each re-derives something the parts could state once.
- Or, if that is the price, raise this test's rail deliberately (as the
  Linux tests did, PR #133), saying why in `scripts/test`.

## Done when

A cold run of the test (a fresh verdict store) passes under the suite's
rails on a cloud box.
