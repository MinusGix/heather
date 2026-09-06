---
title: Project multi-parameter class fields through complete local dictionaries
status: closed
labels: [frontend,traits,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

FiniteSets<S,A> fixes both carrier and element type in a local constraint, but S.image was rejected because type projection supported only one-parameter classes. Use a complete visible local dictionary whose first carrier matches S; never guess remaining parameters from global instances. Check ambiguity, shadowing, aliases, and unrelated carriers. Keep explicit dictionary projection available. Customer: docs/showcase/finite_set_client.hthr. Related: [[finite-set-client-design]], [[operation-indexed-classes]].

## Log

- 2026-09-05: Implemented complete local dictionary projection, including primary-carrier-preserving tagged parent paths. All 27 projection tests pass, including new alias, binder, ambiguity, shadowing, and unrelated-carrier controls. Global inference narrowing remains intact.
