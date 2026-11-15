---
title: Stop making clients hand-import the modules a language feature is stated over
status: open
labels: [frontend,modules,elaboration,ergonomics,design]
area: language
created: 2026-09-16
updated: 2026-11-08
---

A module that uses a language *feature* must hand-import the modules that
feature's machinery is stated over, even when the module names none of them.
The mutual `decreases` group is today's instance: `docs/showcase/calc_parser.hthr`
writes

```heather
import pair;
import int;
import omega;
```

and no declaration in the file mentions `pair`, `int` or `omega`. Removing any
one of them is refused:

```
error: a mutual `decreases` group shares one recursion whose motive is the
       product of its members' (docs/language/recursion/mutual-recursion-design.md §3): `import pair;` first
error: a mutual `decreases` group states its obligations at the flattened measure of
       docs/language/recursion/mutual-recursion-design.md §4 and closes the arithmetic with `omega`:
       `import omega;` and `import int;` first
```

The diagnostics are good — each names exactly what to write — so this is not a
discoverability problem. It is that the requirement is an implementation detail
of the feature leaking into the client's import list, where it then reads as
dead weight: the natural tidy-up is to delete the three lines, and the natural
next step after being refused is to add a comment explaining why they stay.
That comment is now in `calc_parser.hthr`, which is the tell.

**Direction (decided 2026-09-16): put them in the prelude.** `pair`, `int` and
`omega` are common enough to carry unconditionally; that is one rule for every
client rather than a per-feature implicit-import mechanism, and it keeps the
name-resolution story (§4 of `docs/language/modules-design.md`: a name is a reference,
never a silently shadowed slot) unchanged — prelude residency is already how
`Nat` and friends arrive.

The alternative, feature-scoped implicit imports ("using `decreases` in its
mutual form pulls in what its obligations are stated over"), was considered and
is not preferred: it makes a module's visible name set depend on which language
constructs its bodies happen to use, which is exactly the kind of invisible
scoping the name regime rules out.

Two things to settle when this is picked up:

- **Ambiguity cost.** `int` and `nat` both declare `le_trans`, `le_dec` and
  friends, so prelude-resident `int` makes every bare `le_trans` in every module
  ambiguous-at-use. Either the prelude carries these modules *qualified-only*
  (visible as `int::le_trans`, not as a bare name), or the ambiguity regime has
  to be fine with a class of names that were previously bare. The qualified-only
  reading looks right and is the cheaper one, but it is a new visibility kind.
- **Does the requirement disappear or just move?** If the feature's obligations
  are still *stated over* these modules, a client that shadows or does not want
  them needs an answer. Prelude residency should make the imports unnecessary,
  not make them forbidden.

## What it assumes from elsewhere

- **[[lint-unused-imports]]** owns "an import is unused when removing it leaves
  elaboration unchanged". Assumed here: only that its definition is *semantic*,
  so `pair`/`int`/`omega` are correctly not flagged today — and that once this
  issue lands they become genuinely unused and start being flagged, which is the
  intended outcome, not a regression in that lint.
- **[[prelude-option-and-friends]]** owns prelude residency as a general
  question. Assumed here: only that the prelude is a place modules can be added
  to, not anything about which containers belong there.

## Log

- 2026-09-16: Filed from the `calc_parser.hthr` reexport cleanup, where the
  three imports survived a removal probe (one furnace `heather check` per
  import) and had to be kept with an explanatory comment.
- 2026-10-29: (proof-patterns audit, [[proof-patterns-audit-2026-10]]) Another instance, probed on master 4f0ac27: `∑ k < 0, f(k) = 0` at Nat with `import nat; import relation; import big_operator;` is refused with "cannot infer the implicit arguments needed for `MonoidRel<A>(≈, op)` in `MonoidRel::range` … supply the indices explicitly with `@MonoidRel::range(…)`", which points at the call rather than at the missing instance module; adding `import algebra_rel; import semiring;` (where Nat's `CommSemiring` instance lives) makes it check. Memory had it since 2026-10-27 as "∑ at Nat without `import relation` fails with a misleading note"; `relation` alone is not enough.
- 2026-11-03: 2026-11-03: [[std-prelude-facade]] built the qualified-only visibility this asked for: every module in the common prelude's closure (`pair` among them) is reachable qualified from any module. `int` and `omega` were kept out of the prelude's closure (they would grow most of the library's closures), so the mutual `decreases` imports remain.
- 2026-11-08: Stdlib awkwardness survey (docs/surveys/stdlib-math-awkwardness-survey.md §4, §12): analysis and float modules import 19–21 modules each (real_log.hthr 27), and `by` asks for `import tactic` by name. The layering half (theories that cannot use the tactics importing them) is [[theory-modules-after-their-tactics]].
