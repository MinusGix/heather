---
title: "Prefer canonical Unicode aliases in standard-library source"
status: closed
labels: [tooling,lint,syntax,stdlib,unicode,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

Heather intentionally supports approachable ASCII aliases, and ordinary user
programs should not be warned for choosing them. The standard library has a
different editorial role: it is reference source and should use the canonical
mathematical spellings consistently.

Under the stdlib lint profile, prefer only exact lexical aliases whose meaning
is identical before parsing:

```text
fun   → λ
->    → →
<->   → ↔
|-    → ⊢
```

Do not generalize this into an ASCII-looking-token rule. `<=`, `&&`, and `||`
do not currently have Unicode aliases for the same token; `=` and `:=` have
their own deliberate meanings; comments and examples may intentionally show
the portable spelling.

The initial stdlib migration is substantial (`->` remains common), so land the
rule and cleanup together or against an explicit temporary baseline. The
ordinary `heather check lib/std` workflow should enable the profile once clean.

## Acceptance

- The rule is active for the standard-library profile and absent from the
  conservative user default.
- It consumes token kinds plus written spans, recognizing only the four exact
  alias pairs above and never searching comments as code.
- Diagnostics carry exact mechanical replacements and can eventually expose
  them as fixes without re-lexing the message.
- Comments, documentation examples, generated fixtures, and ordinary user
  modules have explicit controls.
- `lib/std` is migrated to zero findings, and its normal directory check keeps
  that invariant.

## What it assumes from elsewhere

- [[lint-roadmap]] owns profile selection and is the blocker for enabling this
  without imposing the preference on user code.
- [[stdlib-surface-style-lint]] owns the broader canonical-source policy; this
  issue owns only exact ASCII/Unicode token aliases.

## Log

- 2026-08-22: Filed by user decision: ASCII aliases stay fully supported and
  comfortable generally, while stdlib source is consistently “proper” Unicode.
- 2026-08-22: Implemented `LintProfile::{Default, Stdlib}` above elaboration
  and the token/span-based `stdlib-unicode-spelling` lint with structured exact
  replacements. The CLI selects it only when the canonical requested target is
  the real `lib/std` tree (or a file inside it), comments remain outside the
  token stream, ordinary source keeps accepting the aliases silently, and all
  standard-library arrows were migrated to `→`.
