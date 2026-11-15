---
title: A binder named `j` misparses at use with a baffling message
status: closed
labels: [frontend,syntax,parser,diagnostics]
created: 2026-07-31
updated: 2026-08-02
---

`j` is the J-eliminator special form in expression position, so a pattern
binder named `j` parses fine at binding time and then any USE like
`lookup(j, t)` reparses as the start of `j(proof, motive, case)`, failing
with `expected `(`, found Comma` pointing at the comma after `j` — a
message about an eliminator the user never wrote. Hit in practice writing
`Succ(j) => lookup(j, t)` while implementing [[ir-simulate-design]]'s
interpreter; the natural predecessor name for an index is exactly `j`.

Smallest fix: when `j` is NOT followed by `(`, parse it as an ordinary
identifier (the special form is always saturated). Alternatively (or
additionally) reject `j` as a binder name at binding time with a message
naming the collision, the way other reserved forms do. Same question
applies to any other one-letter special forms added later
([[special-forms-as-declarations]] would dissolve the problem entirely —
declarations shadow like anything else).

## Log

- 2026-08-02: New bite site (2026-08-02, the surface-fin-indexing round): the natural spelling of a match arm on Fin is FS(j), and the design doc's nth_code sketch wrote exactly that — a use of the binder then parses as the j expression form and dies at the missing opening paren. The surface_fin.rs suite works around it with jx; the quotation-stage port must too.
- 2026-08-02: RESOLVED by docs/language/let-and-blocks-design.md §5, which found the issue was one member of a set of six and not the worst one. The audit (§5.1), every expression-position form keyed on an identifier: | form | atom site | always followed by | failure of a binder by that name | | code | :1220 | `{` (and an ident after `let`) | NONE -- already guarded by lookahead | | j | :1211 | `(` -- the form is saturated | loud: expected (, found Comma | | calc | :1204 | `{` | loud: expected { | | match | :1201 | an arbitrary EXPRESSION | loud | | fun | :1214 | a binder (ident or `(`) | loud: a lambda needs at least one binder | | refl | :1207 | NOTHING (nullary) | SILENT: the use becomes ExprKind::Refl, dies at 'refl needs an = expected type' | | Type | :1198 | nothing, or `<n>` | SILENT: the use reaches the kernel as Type<0>, dies at LevelMismatch | So `j`, the one filed, is a LOUD member; the two dangerous ones are `refl` and `Type`, and a fix that only unblocked `j` would have left them standing. Fixed by three rules, each keyed on a property the form actually has rather than by enumeration, so the set stays classified when a seventh form arrives. Rule 1 (lookahead, the `code {` precedent): `j` requires `(` and `calc` requires `{` before the form is recognized. Exact, not heuristic -- j_expr and calc_expr already REQUIRED the same token one line later, so nothing that parsed before parses differently. Rule 2 (shadowing, the Succ/map/absurd precedent): the ExprKind::Refl arms in elab_check_hinted and elab_infer consult shadowed(cx, "refl") and elaborate a Var instead. Rule 3 (binder rejection, the self-as-type-parameter precedent): `match`, `fun` and `Type` are true keywords -- one takes an arbitrary expression, one a binder, one has no name left in the tree to check -- so a binder by their name is rejected AT THE BINDING SITE by a shared Parser::binder_ident, at all twelve binding positions, with a message naming the collision. Residue, stated rather than hidden (§5.3): after rule 1, `j(x)` -- a local of function type APPLIED -- still enters j_expr and fails its arity check. Left standing because an index is not applied, the failure is loud, and it dissolves under [[special-forms-as-declarations]]; j_expr's arity errors now name the collision and this issue. Acceptance: crates/elab/tests/surface_fin.rs's `jx` workaround binders are reverted to `j` and the suite is green, at the exact site that motivated the rename (lib/lang/vec_code.hthr and in_language_nth.rs reverted too). Nothing here is undone by [[special-forms-as-declarations]]: rule 1 is DELETED with j_expr, rule 2 is a down payment on it (its behaviour is what 'a declaration shadows like anything else' means), rule 3 is orthogonal and permanent.
