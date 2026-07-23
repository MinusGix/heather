# DeLaM reading guide

DeLaM (Dependent Layered Modal Type Theory) is the type-theory target for the
Heather kernel. These chapters build the theory in two passes, and **only the
second pass is the system we implement**:

- **01–03 are a simplified warm-up system, NOT the target.** Chapter 02 builds
  a 2-layer *simply-typed* contextual modal theory (STLC + context variables,
  layers 0/1) and chapter 03 proves its normalization/convertibility. It
  exists to isolate the context-variable machinery before dependent types.
  Do not implement from it — its syntax (`S → T`, `(g : Ctx) ⇒ T`, single
  global-binding form) and 2-layer structure are superseded. The full theory
  does still *refer back* to it: local-substitution syntax and the
  composition/query operations (δ̂, δ̌) are introduced in 02 and reused, and
  several ch. 04–06 rules cite "following Sec. cv". Reference 02 for those
  details only.
- **04 is the actual DeLaM** — the dependent, 4-layer system: full syntax,
  universe levels (incl. the count/adjust normalization for level
  equivalence), all typing/equivalence judgments, the modal part, and the
  computation rules. This is the implementation source of truth.
- **05** defines the three substitution operations (universe φ, local δ,
  global σ) over the full syntax, then syntactic metatheory (presupposition,
  substitution lemmas, lifting). The operation tables at the start are
  implementation-relevant; the lemmas are the correctness argument.
- **06** gives WHNF/neutral syntax, the untyped reduction relations, and the
  algorithmic convertibility judgments — this *is* the conversion checker,
  rule for rule. Note: untyped weak-head reduction + preservation, not typed
  reduction and not NbE.
- **07/07a/07b** are the Kripke logical relations and fundamental theorems —
  pure metatheory justifying 06. Not needed for implementation.
- **08** instantiates the logical relations twice to get injectivity,
  consistency, soundness/completeness of convertibility, and decidability.
  Implementation-relevant only for the statement shapes (e.g. neutral
  convertibility is an *inference* step returning a type).

Kernel-facing summary of the layer structure (ch. 04, Table feat):

| layer | language | computes | meta-programming | layer of types |
|-------|----------|----------|------------------|----------------|
| v     | variables only | no | no | p |
| c (code) | MLTT | no | no | p |
| p (prog) | MLTT | yes | no | p |
| m (meta) | MLTT + □/recursors/ULam | yes | yes | m |

with v < c < p < m, and `typeof(v) = typeof(c) = typeof(p) = p`,
`typeof(m) = m`.
