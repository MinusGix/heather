---
title: A binder named `j` misparses at use with a baffling message
status: open
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
