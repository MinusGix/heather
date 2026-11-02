---
title: The display prints a projection of a literal pair raw
status: open
labels: [diagnostics,display]
area: language
created: 2026-11-02
updated: 2026-11-02
---

A checking note whose expected type holds `π₀(⟨a, b⟩)` reports that type
as having "no surface spelling". Seen at an indexed codata constructor whose
index is a tuple: the payload types read the index binders as projections
of the index (`docs/codata-indexed-design.md` §3), so at the index `⟨s, t⟩`
the field `heads: hd(s) = hd(t)` is `hd(π₀⟨s, t⟩) = hd(π₁⟨s, t⟩)`:

```
codata SBisim : (s: Stream) -> (t: Stream) -> Type {
    Same(heads: hd(s) = hd(t), tails: SBisim(tl(s), tl(t))),
}
fn bad(s: Stream, t: Stream, h: hd(tl(s)) = hd(t)) -> SBisim(s, t) { Same(h, bad(tl(s), tl(t), h)) }
```

says `this has type hd(tl(s)) = hd(t), which does not convert to the type
expected here (that type has no surface spelling)`, located at `h`. The same
with constructors nested above the call (codata-elaborator §5.4).

This is the case `issues/elab-accepts-mismatch-under-redex-head.md` left
open ("ι-redexes … still print raw … none has been seen in a mismatch
yet"). The display contracts a β-redex for reading (`Speller::call`
through `spelling::beta_head`); a projection chain that bottoms out at a
literal pair (`spelling::project_value`) could be read the same way, in the
reading flavours only. `Snd`/`SndAt` also fall through to `raw_tm` today,
where `Fst` tries the field-read routes first.
