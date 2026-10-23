---
title: First slice of type-owned namespaces: attach members, reach through the receiver
status: closed
labels: [frontend,elaboration,modules,syntax]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round): the receiver half of
[[type-owned-namespaces]], sized to land on existing machinery. Two pieces:

1. The checked declaration form that attaches a fn/theorem to a type's
   namespace (`List::nth`, `Le::refl` as declarations, not naming
   convention) — the `Type::member` grammar already exists for
   constructors; this opens membership.
2. Elimination-shaped reachability only: `t.nth(k)`, `p.trans(q)` resolve
   through the receiver's type via the existing method fallback
   (`resolve_dot` / the `self`-parameter desugaring,
   crates/elab/src/lib.rs). No expected-type (introduction-shaped)
   resolution, no head-symbol namespace picking — those stay with the
   parent.

Success shape: `lib/std/data/list.hthr` declares `List::nth` and call sites in
[[list-algorithms-exercise]] write `t.nth(k)` (with
[[call-site-overapplication]] handling the curried tail).

## Design (2026-08-05)

**The declaration form.** `fn List::nth<A>(self xs: List<A>) -> …` — the head is
the only thing that changes. The lexer already joins `List::nth` into one `Ident`
token (it is how `Option::None` is written), and the parser already has the two
readers: `qual_ident` for reference positions and `ident`, which is `qual_ident`
plus "a qualified name can never be a binding". A declaration head becomes the
third case: `qual_ident` plus the check that the qualifier names a *type*, which
is what makes the attachment checked rather than a convention. The type has to be
resolvable at declaration time (`lookup_inductive`, plus `Nat` which is a kernel
type with no declaration), so `fn Frobnicate::x()` is an error at the
declaration, not a mystery at the use.

**The name it declares.** The whole string `List::nth` is the declared name:
`NameIndex` gets `("list", "List::nth")` and the global table gets
`qkey("list", "List::nth")`. This is the smallest possible change to name
resolution and it inherits the whole [[modules]] regime for free — locals beat
unlisted imports, two modules declaring `List::nth` are ambiguous at use with
both origins named, and qualification by module still works because
`split_qual`'s `split_once` cuts at the *first* `::`. `resolve` gets one new arm,
after the module-path and constructor arms: try the whole written string as a
bare name. The deliberate consequence: a member does **not** put its base name in
the ambient namespace. `nth` alone is unbound after `List::nth` is declared,
which is the shrinking-ambient-namespace half of the parent design, and it is why
this slice can land without a deprecation dance — the surface has one `nth` and
it moves.

**Reachability through the receiver.** `resolve_dot` builds the method
desugaring by rewriting `t.nth(k)` into `nth(t, k)` with a `Var(name)` head. The
change is to pick the head: if some declaration attaches a member with base name
`nth` to some type, infer the receiver's type, read its nominal tag (`tag_of`,
plus `Nat`), and use `D::nth` as the head when that resolves. Two properties are
load-bearing:

- **The cheap negative test comes first**, exactly as for record fields: a
  `member_bases` set is consulted before the receiver is inferred, so a
  `.foo()` call where nothing declares a `foo` member costs what it cost before
  — no inference, no reduction, no behaviour change for `p.sym()`, `xs.map(f)`,
  `p.inj(1)`.
- **Evidence shrinks the candidate set; it never races candidates.** If both a
  bare `nth` and a `D::nth` are in scope at a receiver of type `D`, this reports
  an ambiguity naming both rather than preferring one. Preferring the member
  would mean that *adding* `List::nth` to a library silently reinterprets an
  existing `t.nth(k)` that used to mean the bare one — the growth invariant
  forbids exactly that. Preferring the bare name would make the feature
  unreachable. The error is the third option and the only one the invariant
  allows.

Everything after the head is untouched: `subject_index` (resolved against the
qualified name, so the `self` parameter is found), implicit insertion, and the
receiver's own elaboration all run as they do for a bare method call.

**Failure modes and negative controls.**
- `.nth(k)` on a receiver whose type has no `nth` member: falls back to the bare
  name, so the message is the ordinary unbound-name one, naming `nth`.
- A member declared on an unknown type: rejected at the declaration.
- A member whose base name also exists bare, reached through a receiver:
  ambiguity error naming both, not a silent pick.
- `List::nth` written directly (not through a receiver) resolves, so the member
  is not receiver-only.
- Out of scope, and each must still be an ordinary error rather than a guess:
  expected-type (introduction-shaped) resolution, head-symbol namespace picking,
  and `Type::member` on a *record field* name (fields win, as today).

**`Le::refl` is not spellable, and that is a finding, not an oversight.** This
issue's own example fails: `Le` is a `fn Nat -> Nat -> Type` — the *decided*
order, `leb(n)(m) = True` — not a declared inductive, so it names no type and
owns no namespace. Every predicate the library states by decision rather than
by declaration is in the same position, which means the namespace a proof
author most wants (`Le`, and any future decided relation) is exactly the one
this mechanism cannot give them. Two ways out, both the parent's: let a
`Type`-valued `fn` own a namespace (the qualifier resolves to a global whose
result is a universe), or reach members through the *goal's head symbol*,
which the parent already records as the function-subject extension. Recorded
here because the receiver half looked complete until a real predicate was
tried.

**One message is half-wrong and is left so.** When two modules attach the same
member, `ambiguity_msg` offers both of its standard fixes: qualify
(`a::List::nth` — which *does* resolve, since `split_qual` cuts at the first
`::`) and list it in the import (`import a::{List::nth};` — which does **not**
parse, because an import list is read with `ident` and a qualified name cannot
be one). Fixing it means either teaching the import list about members or
threading "this is a member" into the message; both are the parent's call about
what a member's standing disambiguation should even be, so the wrong half is
recorded rather than patched.

**Known limit of this slice.** The attachment is checked against the type's
name, not against the member's signature: nothing requires `List::nth`'s `self`
parameter to be a `List`. Receiver reachability only *finds* it if the receiver's
type matches, so a mis-attached member is unreachable rather than unsound, but
the declaration-time check that the `self` parameter's type is the owning type
belongs to the parent issue with the rest of the attachment rules.

## What it assumes from elsewhere
- **[[type-owned-namespaces]]** owns the design and its duality argument.
  Assumed here: only that the receiver direction is the
  uncontroversial half.
- **method-receiver-position** (closed) owns where the receiver lands in
  the argument list. Assumed here: only that `self`-parameter desugaring
  works for members resolved by type, same as for bare fns.

## Log

- 2026-08-05: LANDED, both pieces, as designed above. (1) The declaration form: a decl head is read with qual_ident (parser.rs), and the elaborator checks that the qualifier names a type in scope (lookup_inductive, plus the kernel types Nat/Type) — an unattachable member is an error at the declaration. The whole string 'List::nth' is the declared name, so NameIndex and the globals table key it as list::List::nth and the modules regime applies to it unchanged; names.rs's resolve gets one new arm (try the written string as a bare name) after the module-path and constructor arms, and key_of learns to keep both halves when the qualified string is itself declared. A member recurses under its BASE name (selfref), so inside fn List::nth the call is nth(t). (2) Reachability: resolve_dot picks its head via member_head, gated on a member_bases set so no receiver is inferred for a name nobody attaches — the same cheap-negative-test discipline as record fields. Ambiguity, not preference, when both an ambient name and a D::member could be meant (growth invariant); two modules attaching the same member are the ordinary ambiguity with both origins named. lib/std/data/list.hthr now declares fn List::nth<A>(self xs: …) and list_algos writes xs.nth(i) and append(xs, ys).nth(i). Tests: crates/elab/tests/type_members.rs, 15 tests, including the receiver and qualified spellings proved definitionally equal, a checking position at a literal head with a neutral tail and an open element type, self-marker placement resolved against the qualified name, cross-module reach, and five negatives (unknown owner, base name no longer ambient, member of another type unreachable, ambient-vs-member ambiguity, record field still wins). DECISIONS FOR REVIEW. (a) A member's base name is deliberately NOT ambient: bare nth is now unbound, which is the shrinking half of the parent design but is a breaking change to any file that used nth (only list_algos existed). (b) Nat and Type are allowed as owners although they have no declaration, so Nat::cong is spellable when someone wants it. (c) The attachment is checked against the type NAME only — nothing requires List::nth's self parameter to be a List. A mis-attached member is unreachable rather than unsound (the receiver's type is what finds it), but the signature check belongs to the parent issue. (d) Only nth moved in the library; list::map and option::map are still both ambient and hence already ambiguous for any importer of both — a second rename this round did not do.
