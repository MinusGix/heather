---
title: Narrow the PR lane's run-time readers to the modules they load
status: open
labels: [testing,performance]
area: infrastructure
created: 2026-10-30
updated: 2026-10-30
---

`scripts/affected-targets.mjs` (docs/testing-architecture-design.md
§2.2.1) treats a test file whose sources read files or spawn processes as
reading all of `lib/`, `examples/`, `docs/showcase/` and the editor corpus.
About thirty files qualify, and they include the suite's heaviest: the
showcase gate, the whole-library gate, the native gates (already trimmed by
#260's rule). So a leaf-module PR runs about an eighth of the files by
count but a much larger share of CPU.

Ways to narrow, cheapest first, to choose by the re-profile of the suite on
current master:

1. **Import closures for readers with a fixed root set.** The showcase gate
   checks `docs/showcase/*.hthr`; the native tests compile
   `examples/x86-native/*`. The loader (`crates/cli/src/loader.rs`) could
   print the closure of those roots (`heather deps`, or a test-only call),
   and the selector would select the reader only for a change inside it.
2. **Record what each reader actually opened** on every run (the runner can
   set an env var the loader appends paths to), the "record each target's
   module set" step of §4 item 3, and select by that record, falling back
   to everything when the record is missing or older than the reader's
   binary.

The library gate stays unconditional on `lib/` changes: it is the gate for
the library.
