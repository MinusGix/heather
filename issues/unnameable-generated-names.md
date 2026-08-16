---
title: Generated names are not ordinary identifiers: the # hygiene boundary
status: open
labels: [frontend,elaboration,design,ergonomics]
created: 2026-08-14
updated: 2026-08-16
---

Filed from the datarepr design review (2026-08-14, user live commentary on
docs/datarepr-design.md sec. 1.4): generated artifacts (typeclass instance
records like Repr_ListTok, monomorph names, derived Impls) should NOT be
ordinary user-spellable identifiers. Lean is the counterexample: generated
instance names are referenceable as normal identifiers, which makes them
easy to reach but hard to trust — user code silently depends on a name the
elaborator invented and may respell. Wanted instead: generated names are
unnameable-by-default at the surface (sketch spelling: a # sigil, e.g.
#Repr_ListTok — lower layers treat it as any identifier), reached through
deliberate syntax or indirection (e.g. Repr<List<Tok>>::record_ty). This is
an overarching design boundary touching multiple features (datarepr,
Compile instances, certgen emissions, derived tables), not a datarepr
blocker — the datarepr landing round should merely avoid committing to
surface-spellable generated names. Related: [[datarepr-separation]],
[[compile-typeclass-design]].

2026-08-15, datarepr v1 landing: the round DID land nameable names
(`Repr_N`, `N_spec_rec`, `Repr_N::⟨clause⟩` — docs/datarepr-design.md §1.4
as-landed note 1), and the constraint is structural, not an oversight: the
artifacts are emitted as surface source and re-parsed (the certgen move,
for the same dependent-record reason), and `#` never *begins* a surface
identifier, so an unnameable name cannot be written in the text that
declares it. Whatever design lands here must either give the generated-
source path a way to declare-and-reference sigiled names (parser accepts
`#` in generated-source mode only), or move generation off surface text.
The datarepr names are the first standing customers to migrate.

2026-08-15, user verdicts on the above: `#` is WITHDRAWN as the sigil —
use a reserved Unicode character the way Lean marks inaccessible names
(its `✝` style). And the bar is softened: generated names need to be
*mostly* inaccessible — a clear visual "you should avoid depending on
this" marker plus convention — not 100% unwritable; harder inaccessibility
is a nicety. Sharpened same day: the marker should NOT be literally
typeable in ordinary source — "mostly inaccessible" means reaching such a
name takes deliberate code-kludging (programmatic identifier construction,
metaprogramming), not just typing the character. So the lexer rejects the
marker in user-written files while the generated-source path may produce
it — a mode split at the *lexer* for one character class, far smaller than
the parser-mode split feared above. Not immediate; implement when a round
wants it.

## Log

- 2026-08-15: New standing customer, deferred to here rather than decided elsewhere (docs/obligation-records-design.md §4.4): reprgen names derived artifacts at top level (add_derived, add_is_rec, add_derived_refines), and once 'impl add for BinNat := derive()' is writable from source those land in the USER's namespace from a user-written declaration. The design deliberately does NOT namespace them in v1 (it would change emission bytes for no v1 benefit) and satisfies the provenance verdict a different way — a Provenance enum on the registry entry, printed by the obligations listing, never consulted by a certificate. Moving derived artifacts under the owner's namespace, carrying this issue's marker, is the better answer and belongs here.
- 2026-08-16: A large piece of this landed sideways (2026-08-16, docs/repr-access-spellings-design.md): the datarepr/impl minted names — Repr_N::⟨member⟩, N_spec_rec, Impl_R_f::⟨member⟩, the assembled N_f_impl, the via_derived intermediate — are now REFUSED in user source, with the diagnostic naming the designed spelling (N::abs, Impl(add, BinNat)::refines). Three things this issue should take from it. (1) The boundary is a MODE, not a property of the text: Elaborator::generated_mode raises an exemption for the duration of one emission, and the new public Elaborator::elab_generated_source is the entry point for the standing customer that re-checks emitted text (the perturbed-emission mutation controls). That is exactly the harness this issue's lexer-level marker needs — once a marker character is refused in user files, generated text can ONLY be re-checked in generated mode, and the suite already does. (2) The designed name is deliberately NOT the declared name: N::abs is a resolution alias onto the declaration Repr_N::abs (crates/elab/src/access.rs), so the minted name can grow the marker without any surface spelling moving. The migration this issue names for the datarepr names is therefore a rename of the alias TARGET and nothing else. (3) Not done here, still owned here: Repr_N and Impl_R_f as TYPE names stay spellable (fn p(d: Repr_BinNat) is the only way to write 'a value of this repr's record type', and the Repr<List<Tok>>::record_ty sketch is this issue's design), and reprgen's derived artifacts (f_derived, f_is_rec, f_derived_refines) are untouched per obligation-records-design §4.4.
