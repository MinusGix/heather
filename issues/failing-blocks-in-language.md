---
title: In-language failing blocks for refusals, or keep the directive
status: open
labels: [testing,design,language]
area: infrastructure
created: 2026-10-25
updated: 2026-10-25
---

Whether Heather gets an in-language `failing "fragment" guards Name { … }`
block, as Idris 2 has (without the `guards`), in place of or beside the
`// expect-error` directive that `heather check --expectations` reads
(`docs/test-value-audit.md` §4.3, `crates/cli/src/expect.rs`).

Minus (2026-10-24) likes the block but worries about noise next to
theorems. The proposed answer: blocks live in `lib/_tests` by convention,
`guards` gives the LSP a link from the theorem to its negative controls,
and editors fold the few that stay inline. If `guards` is all a block would
add over the directive, the directive can carry it
(`// expect-error(guards Rat::inv_mul): …`) and the language does not
change. A block would also let plain `heather check` honour refusals, which
the directive deliberately does not (an unflagged check means every
declaration checks).

Decide once the corpus shows how often directives are used and whether
anyone reaches for `guards`. Split out of [[hthr-test-corpus]] when the
directive landed (2026-10-25). Either way the block reuses the directive's
matcher.
