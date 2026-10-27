---
title: Tactic modules' images decode to gigabytes because every Tac<…> mention spells its lowering
status: closed
labels: [elaboration,representation,tactics,images,memory]
area: language
created: 2026-10-27
updated: 2026-10-27
---

Found in the `mono` class-carrier round (`issues/mono-class-laws.md`). The
whole-library gate runs each folder under the suite's 6 GiB address-space
rail, and folders that load `mono` (through `series.hthr`) are near it. Most of
their memory is two modules' images: `tactic` and `mono`, each decoded into
gigabytes, from images that are themselves a hundred-odd and tens of MB.
Every other library module is one or two orders of magnitude smaller.

`HEATHER_IMAGE_ATTRIBUTION` puts the nodes in the types the lowering writes
inline: `Lam.dom`, `Refl.ty`, `ElimEmpty.motive`, `Case.motive`,
`Pair.fst_ty`, `Sup.pos_ty`/`shape_ty`. `Tac<A>` (`inductive Tac<A> { Pure(a:
A), Ask(r: Req, k: Resp(r) → Tac<A>) }`) is a tier-2 family on W, and each
mention of it, in a statement, a λ's domain, a match motive or a constructor
value, writes its whole W lowering instead of a reference. A `Tac`
function's size therefore grows with how many times its body mentions `Tac`,
not with how much it does:

- a three-line `lookup(name).bind(λ c => match c { … => Pure(…), … })` is
  hundreds of thousands of nodes, and one `Pure(False)` alone is a fifth of
  that;
- a `match` returning `Tac<…>` inside another one multiplies: `mono_same`,
  with nested matches over `Head` whose arms each returned `Pure(False)` or
  a `bind`, was a third of `mono`'s image on its own.

The round worked around the second shape. A plain classifier
(`mono_pair: Head, Head → MonoPair`) decides, and one `match` over its
result is the only one whose motive is `Tac<Bool>`; the shared `mono_no()`
replaces the per-branch `Pure(False)`. That shrank `mono_same` about
seventeenfold and `mono`'s decoded image by about a third. It is advice for
tactic authors, not a fix.

The world amplifies it. A check over `--world lib` loads the world's order
up to the last shared module its folder needs (`docs/library-world-design.md`
§2), and `tactic` and `mono` sit early in that order, so folders that import
neither (`lib/std/arch`, `lib/std/os`) decode them too: on 2026-10-27 every
measured gate folder's peak was about the same, and adding `mono` (#222 and
the class round) raised all of them alike. Three such children side by side
exceed a cloud box's memory cgroup before any reaches its own rail, and the
kernel's OOM killer, not the rail, ends the gate (`dmesg`).

## Direction

The owner is [[elaborator-canonical-type-spelling]]: one spelling per type,
with the named code (`El(Tac#tycode(A))`) as that spelling at every emitted
mention. This issue is that invariant's most expensive case in the library
and its measurement: the per-function node counts above and the folders'
decode growth (`peak_growth_kb` on the `module` rows of a `--timings` table).
Done when a `Tac` function's emitted size is linear in its body, with
`Tac<A>` written as a reference, and the tactic folders sit well inside the
rail.

## What it assumes from elsewhere
- **[[elaborator-canonical-type-spelling]]** owns the spelling invariant.
  Assumed here: only that a tier-2 family's type can be emitted as its named
  code without the kernel unfolding it at every comparison.

## Log

- 2026-10-27: closed by #227 (module images written as DAGs). On top of it
  `mono`'s image is about a hundredth of its tree size, and the gate
  folders measured here (`lib/_tests/std/tactic`, `lib/_tests/std/num`,
  `lib/std/arch`) peak at a fraction of what they did; the full `--pr` suite
  passes on a cloud box with no OOM kill. Writing `Tac<A>` inline still costs
  its nodes where terms are built and checked rather than stored; that is
  [[elaborator-canonical-type-spelling]]'s, and the classifier shape above
  remains the cheaper way to write a `Tac` function.
