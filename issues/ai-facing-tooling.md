---
title: AI-facing tooling: every failure returns the search state that produced it, as data
status: open
labels: [tooling,design,meta,diagnostics]
area: tactics
milestone: [tac-general]
created: 2026-08-05
updated: 2026-10-27
---

Direction issue, not scheduled — filed from the 2026-08-05 riff (while the
ergonomics round ran), so the design is written down rather than
re-derived. Premise: models working in Heather are already the norm, and
Heather is in no training data, so the tooling is the whole interface.

## The thesis this issue owns

**Every failure should return the search state that produced it, as
data.** One principle, several features, each with its own issue:

- Conversion failure -> a budget-bounded divergence trace (where the two
  sides split, after what unfoldings). Models handle such dumps far
  better than a casual human glance; humans get the prose summary on top.
- Resolution failure -> nearest names in scope.
- Solver failure -> the stuck state ([[grind-port]] owns the biggest
  instance).
- Statement before proof -> [[heather-disprove]].
- Discovery -> [[lemma-selection-and-search]].
- Measurement of all of the above -> [[proof-benchmark]].
- Conversation presentation -> [[chatgpt-codex-syntax-highlighting]], which
  owns whether ChatGPT/Codex expose a supported custom-language highlighting
  hook rather than diagnostic data.

Plus the loop primitive none of those work without: `heather check
--json` emitting decoded goals and diagnostics as data (the decode half
is [[goal-display-decodes]]; this adds the serializer), and eventually
`heather ctx <file> --json` — as modules grow, preserve today's
accidental virtue that everything in scope fits in a context window.

Two properties everything here inherits:

- **Truthfulness through the one resolution judgment**: anything a tool
  reports as reachable must resolve the same way elaboration does.
- **The kernel is the judge**: the elaborator is untrusted, so no tool
  output ever enters the trusted story; a wrong hint is a rejection.

## Assumption-aware proof actions

For a candidate theorem, the machine-readable search state should include the
requirement footprint from [[implicit-logical-assumptions]] and the ranking
owned by [[lemma-selection-and-search]]:

```text
candidate
result match
requirements already resolved, with providers
missing exact propositions or typeclass capabilities
profiles that can derive them
concrete providers available to `using`
axiom/provenance impact of each concrete choice
```

This gives an agent four explicit moves: prove the narrow premise, find a
specialized provider, add an ordinary parameter or generalize an item group
with `assuming`, or activate a concrete provider with `using`. Selecting an
axiom-backed provider is a trust-policy escalation, never an automatic “make
the proof close” step.

Do not hide down-ranked candidates from an agent. A missing proposition that
looks hard to name-based completion may be easy in the current special case,
and constructive and classical variants may have materially different
precision bounds or witnesses. Return both with their exact requirement
deltas; let the agent or policy choose, and let the kernel check the term.

## What it assumes from elsewhere
- **[[lsp-from-the-meta-layer]]** owns the editor-facing surface of the
  same information. Assumed here: only that the two share the
  serialization, not which lands first.
- **[[elaboration-determinism]]** owns reproducibility. Assumed here:
  only that programmatic scoring and stable dumps want it eventually.
- **Feedback latency** is owned by the perf accumulator issues; noted
  here only that agent loops multiply check time by hundreds, so they
  are quietly also AI-ergonomics issues.

## Proof opportunities and their conditional benefits

A failed generation or optimization attempt should explain what discharging
its exact remaining premises would enable. Return a structured candidate:

- proposed artifact/rewrite and exact goal in its local context;
- rule, known evidence, remaining premises and their dependency graph;
- candidate status: proved, missing evidence, unsupported analysis,
  resource-exhausted, or refuted (with validated witness when available);
- assumption/provenance impact and matching source/dictionary dependencies;
- a concrete benefit, with structural claims separated from measured or proved
  cost claims; useful alternative implementations and their different premises.

Identify whether the result includes a checked conditional term from premises
to certificate, or only an unverified proposal. Missing premises are those of
the attempted derivation, not necessarily logically necessary or minimal.
No checked declaration with outstanding holes is introduced. Supplying evidence
must yield a fully checked artifact before registration; changed dependencies
require rechecking. Strengthening a client's assumptions remains a visible edit.

The finite-set customer is owned by **[[finite-set-client-design]]**:
idempotence permits omitting a duplicate-removal pass before a compatible fold;
otherwise a certified duplicate-free enumeration enables a different fold.
Preserve all affected consumers' observations. The compiler-side owner retains
responsibility for whether a semantically valid optimization is profitable.
See `docs/finite-set-client-design.md` §6 for candidate examples.

## Log

- 2026-08-25: Added structured assumption-aware proof actions. Agent search
  receives exact missing requirements, checked profile expansions, concrete
  provider choices, and axiom impact; axiom-backed `using` is an explicit
  policy escalation rather than a silent fallback.

- 2026-08-20: Linked the separate conversation-preview research owner. Syntax
  highlighting makes agent edits easier to review, but it is presentation and
  does not belong to this issue's search-state-as-data contract.

- 2026-08-15: Two items from the obligation-records round (2026-08-15). (1) DELIVERED, small: 'heather obligations [--json] <file>' — one row per obligation-bearing field of every such declaration, with owner, the '::' path, field, state (supplied|defaulted), provenance (inline|named|derived|via) and the STATEMENT, printed as the synthesized source text rather than decoded from a kernel term. That is the property worth keeping: because the statement schema is built as surface source, the listing is legible without goal-display-decodes, and any future path that renders a statement from kernel terms inherits that problem while this one does not. The --json emitter is hand-rolled (dependency-policy) and is a fine template for the 'heather check --json' this issue owns. (2) WANT, recorded not built (round-5 verdict, 'not too important right now'): checking should CONTINUE past a failed obligation clause so that downstream breakage — a caller of the interface whose use no longer typechecks — surfaces before the proof is written. Today a '?' clause (the reporting hole: fails at its own span printing the statement it owes) stops the file there, which is exactly one fix per round-trip. This is error-tolerant elaboration, a diagnostics-mode change, and it belongs with the search-state-as-data thesis: a failure should return everything the file still has to say, not only the first thing it could not say.
- 2026-09-04: Added conditional proof opportunities and explicit benefits, shared by lifting and optimization; finite sets provide the first concrete design examples.

## Generated proof cost attribution

[[generated-proof-cost-diagnostics]] owns bounded declaration/conversion cost
diagnostics motivated by the x86 certificate round. This issue owns the shared
structured-output conventions.
- 2026-10-23: Arend's answer to the same premise is a skills pack for agents (formalize, prove, quirks, error diagnosis); Heather's is [[agent-skills-pack]] (docs/arend-survey.md §6).
- 2026-10-27: Related, filed 2026-10-27: [[lemma-search]] (heather search, exact?, apply?) returns its candidates as data in this form.
