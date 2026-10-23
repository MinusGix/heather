---
title: Program extension preserves convergence (the linking lemma)
status: open
labels: [ir,stdlib,compiler,design]
area: heather-in-heather
created: 2026-08-02
updated: 2026-08-11
---

Filed off the certifying-generator v2 design discussion (2026-08-02): a
certificate proved against a program \`p\` is a statement about that exact
\`Prog\` term, so it does not transport to \`p\` extended with more functions —
even though every body in \`p\` behaves identically there (calls are by
index, and \`p\`'s bodies only reference indices that exist in \`p\`). Today the
generator's workaround is re-deriving callee certificates inside each
combined program (cheap for machine-written text, quadratic in call-DAG
depth). The right answer is proved once:

    eval(n, p)(env, ir) = Out(vs)
    -> refs_below(ir, len(p)) -> all_refs_below(p)
    -> eval(n, append_prog(p, q))(env, ir) = Out(vs)

and its \`Converges\`-level corollary. Notes:

- The side condition is a syntactic **well-formedness predicate** on
  callee indices (\`refs_below\`). ir-simulate-design §5 deliberately kept
  well-formedness extrinsic ("an ordinary predicate when a pass wants
  it"); this is the first consumer that wants one, so its shape gets
  decided here — a boolean reflection like \`Le\`, presumably, decided by a
  structural walk over \`Ir\`/\`Prog\`.
- Proof shape: induction on fuel with env/ir generalized (the
  \`fuel_monotone\` pattern); the only interesting case is \`LetCall\`, where
  \`find_fun\` must agree on indices below \`len(p)\` — a lemma about
  \`find_fun\` and \`append_prog\`.
- Consumers: the certifying generator's cross-function composition
  ([[certifying-generator]] §8 item 1 — retires the re-derivation
  workaround); any future separate-compilation / library-linking story;
  version-bump refinements that add functions to a program.
- Not scheduled; wanted when the re-derivation workaround starts to hurt
  (deep call DAGs) or when a second consumer appears.

## Log

- 2026-08-11: Cross-reference (2026-08-11): the transcriber re-homing round named the fold-as-a-lemma route — one Converges theorem in lib/certgen/ir_v1.hthr by induction over Ir, of which the per-function kit folds are instances — as the alternative future for in-language certificate emission (certgen-transcriber-in-language-design sec. 5). It would retire this workaround too, but it changes the trust story from certifying to verified, so it must be argued on certifying-generator's charter, not assumed.
