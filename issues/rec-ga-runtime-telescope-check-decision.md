---
title: rec_ga trusts its telescope tables at runtime: record the decision
status: open
labels: [kernel,design]
created: 2026-08-06
updated: 2026-08-06
code: crates/kernel/src/typing.rs @ HEAD
---

Filed from [[branch-telescope-entries-unchecked]]. The new telescope
well-formedness coverage is a `#[cfg(test)]` walk, so the tables are pinned
at HEAD — but the kernel proper still accepts a hypothetically ill-formed
telescope at runtime: `rec_ga` checks branch bodies against instantiated
motive types and never re-derives the entries' own well-formedness.

The likely verdict is that this is right: `branch_specs` is a constant
table, not user input, and a per-check `ty_wf` walk over 52 telescopes
would tax every recursor use for a property the suite already pins. But
there is an asymmetry to answer for — `check_global_ctx` *does* check its
bindings at runtime — so the choice should be a recorded decision in
`crates/kernel/DESIGN.md` (tables are trusted because they are tested;
what invalidates that trust is a table edit, which the suite gates),
rather than an accident of who wrote which code first.

## When

Next `DESIGN.md` pass, or the next time anyone proposes making the branch
tables dynamic (e.g. [[generators-in-the-language]]-style work reaching the
kernel), at which point the trust argument stops holding and this becomes a
real check, not a note.
