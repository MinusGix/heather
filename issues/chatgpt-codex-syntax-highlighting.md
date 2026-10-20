---
title: "Investigate non-invasive Heather highlighting in ChatGPT and Codex previews"
status: open
labels: [tooling,editor,syntax,research]
area: language
created: 2026-08-20
updated: 2026-08-20
---

Heather code shown in ChatGPT or Codex conversations is usually an unrecognized
fenced language, which makes reviewing proposed `.hthr` edits noisier than it
needs to be. Investigate whether these apps expose a supported, non-invasive
way for a project or language package to provide syntax highlighting.

As of filing, a search of official OpenAI documentation found no documented
custom-language or syntax-highlighter extension hook for ChatGPT/Codex code
previews. Do not patch installed application assets or rely on private bundle
layout. The useful outcomes are therefore either a supported integration with
an explicit maintenance story, or a documented negative result plus the best
portable fallback (for example, a recognized fence alias chosen only for
presentation, with clear limits).

## Acceptance

- Check current official OpenAI documentation and supported extension/plugin
  surfaces for a code-fence language registration mechanism.
- Determine whether repository metadata, a Codex skill/plugin, TextMate data,
  or Tree-sitter data can affect rendered chat previews without modifying app
  internals.
- If a supported hook exists, build the smallest integration and pin a visual
  fixture containing representative Heather syntax.
- If no hook exists, record the negative result, a non-invasive fallback, and
  what product capability would be required; do not ship an app-bundle patch.
- Re-check the result when the relevant desktop rendering/plugin API changes.

## What it assumes from elsewhere

- **[[tree-sitter-zed-language-support]]** and
  **[[textmate-vscode-syntax-highlighting]]** own reusable grammar artifacts.
  This issue only asks whether an OpenAI product can consume one of them.
- **[[machine-readable-syntax-manifest]]** owns a smaller portable lexical
  artifact if a supported preview hook accepts token metadata rather than a
  full editor grammar.

## Log

- 2026-08-20: Filed as a research issue. The official-documentation search
  produced no supported registration hook, so the issue explicitly permits a
  well-supported negative conclusion and forbids invasive local patching.
