# Docs

Design docs, guides and surveys. Read these first; CLAUDE.md says when:

- `roadmap.md`: the areas, their priority, the milestones.
- `compilation-vision.md`: the settled principles of native compilation.
- `proof-patterns.md`: how to write proofs that check cheaply.
- `testing-generated-terms.md`: the axes a test of generated terms varies.
- `test-value-audit.md`: when a claim is a Rust test and when a theorem.
- `agent-policy.md`: what a thread may decide and what it asks.

Elsewhere:

- `delam/`: the type theory (`delam/README.md` says which chapters matter).
- `papers/`: the papers the docs and issues read, with an index.
- `showcase/`: checked example programs and the prose around them.
- `archive/`: docs whose code is gone but whose sections live code still cites.

## Where a doc goes, and when it leaves

A design doc is named for its subject (`<subject>-design.md`) and sits with
the other docs of its area. When the code a doc describes is deleted or
replaced, the doc goes in the same change: deleted if nothing live cites it
(mentions become `docs/<name>.md@<rev>`, readable with `git show`), moved to
`archive/` if code still cites its sections.
