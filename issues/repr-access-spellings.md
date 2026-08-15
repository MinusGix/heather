---
title: One designed spelling for a repr's legitimate access points
status: open
labels: [design,frontend,ergonomics]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 5, user-confirmed wanted
(2026-08-15). Hand-written certificates today must spell minted names
(`Repr_ListTok::…`, `Impl_ListTok_length::…`, `ListTok_spec_rec`) and
there are TWO spellings for the same access
(`ListTok().mk_Cons(t)` vs `Repr_ListTok::mk_Cons()`), the split forced
by [[theorem-field-projection-oom]] and
[[receiver-method-shadows-record-field]]. The legitimate access points —
the ones user code is *supposed* to reach, as opposed to the internals
[[unnameable-generated-names]] will mark — deserve one designed spelling
(`ListTok::fold`, `ListTok::mk_Cons`, …-shaped), with the workaround
split dissolved rather than papered over: fixing the two underlying
defects is likely the first half of this issue.
