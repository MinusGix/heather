---
title: Build the uniqueness-threaded effects surface over the program builder
status: open
labels: [language,effects,native,frontend]
area: language
created: 2026-10-28
updated: 2026-10-31
milestone: [nh-effects, lang-sequencing]
---

The decided effects story ([[effects-direction]], 2026-10-21) is a
uniqueness-threaded surface that denotes interaction trees. Nothing builds it
yet: effectful programs are written in the program builder
(`lib/native/native_build.hthr`, [[native-source-builder]]) or as a `Source`
directly. This is the language round that gives them a front end.

## Scope

- Effectful code in ordinary Heather syntax over capabilities (`uniq Fd`,
  `uniq Buf`), elaborating locally into the builder or straight into
  `Source` (`docs/native-effect-source-design.md` §9): a `let` of pure
  expressions becomes a `Pure` leaf, `io.read(fd, buf)` a `Call`,
  `loop`/`while` a `Loop`, `for` and structural recursion FunctionIR's
  bounded loop.
- The pure reading users reason with (world threading) agrees with `denote`
  construct by construct, proved once (`ITree::run_state_bind`'s statement).
- The assignment glyph. `=` is propositional equality, so assignment is
  `:=` (held free for this by `docs/let-and-blocks-design.md` §3.1).
  [[warn-bare-eq-no-effect]] waits on it.
- Interleaved statements in a block (`let a = …; f(x); g(a)`), deferred here
  by `docs/let-and-blocks-design.md` §4.5: the form means something once a
  statement can have an effect.
- Users never write monadic types or prove against a CPS elaboration target
  ([[effects-direction]]'s "avoid").

## What it assumes from elsewhere

- **[[effects-direction]]** owns the decision. Assumed here: only that the
  surface is uniqueness threading denoting trees.
- **[[native-source-builder]]** owns the builder this surface targets.
  Assumed here: only that the builder is the surface's back half
  (`docs/native-real-programs-plan.md` §3.3).

## Log

- 2026-10-31: 2026-10-31: Round R6 of docs/compiler-milestones-proposal.md (§4.2 N3, milestone nh-effects): written with the sequencing surface ([[sequencing-surface-design]]) as a runtime fn under the default setup ([[runtime-fn-default-setup]]). Done when cat FILE…, wc and head -n are rewritten in it and pass the same GNU tests, and their builder versions are deleted. Also owns byte and string literals in programs and [[feature-implicit-module-dependencies]] for program files.
