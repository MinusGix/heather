# Function types and lambdas at the surface

Status: **scheme written, not yet implemented** (2026-07-26). Written before
the code, per the discipline of `docs/inductive-tier0-lowering.md` and
`docs/wf-former-design.md`; this is the specification the implementation is
checked against, and §9 is the acceptance checklist.

Tracking issue: `issues/surface-function-types.md`.

The kernel side is **already done and has been since v0**: `Type::Pi`,
`Term::Lam`, `Term::App` (`crates/kernel/src/term.rs:465,474`), with full
type-directed η at `Π` (`crates/kernel/src/conv.rs:535`). Nothing here
touches the trusted base, so unlike `Wf` and `Unit^l` this round carries no
metatheory obligation and cannot break soundness. It is entirely a surface
grammar and elaborator round.

---

## 1. What the surface gains

Types (`crates/syntax/src/ast.rs:146`) go from

```
ty ::= 'Nat' | expr '=' expr | name ('<' ty,… '>')?
```

to that plus a dependent function type. Expressions gain a lambda, and
application stops requiring a *name* at the head.

### 1.1 Type grammar

```
ty       ::= '(' ident ':' ty ')' '->' ty      -- dependent, right-assoc
           | ty_atom '->' ty                    -- non-dependent, right-assoc
           | ty_atom

ty_atom  ::= 'Nat'
           | ident ('<' ty (',' ty)* '>')?
           | expr '=' expr
           | '(' ty ')'
```

`->` is right-associative, so `A -> B -> C` is `A -> (B -> C)`.

**One binder per parenthesis group.** `(x: A) (y: B) -> C` is *not* grammar;
write `(x: A) -> (y: B) -> C`. Right-associativity makes the nested form
read correctly and it needs no extra parsing. If the flat form is wanted
later it is additive.

Equality binds tighter than the arrow: `a = b -> C` is `(a = b) -> C`. This
falls out of the parse order in §3.1 and is also the only reading that
types, since `=`'s endpoints are *terms* and `b -> C` is a type.

### 1.2 Lambda

```
lambda   ::= ('λ' | 'fun') binder+ '=>' expr
binder   ::= ident | '(' ident ':' ty ')'
```

```heather
λ (x: Nat) => Succ(x)
λ x => Succ(x)                       -- annotation inferred in checking position
λ (x: Nat) (y: Nat) => add(x, y)     -- juxtaposed binders, sugar for nesting
fun (x: Nat) => Succ(x)              -- ASCII synonym, prints back as λ
```

`λ` is canonical and is what the printer emits; `fun` is accepted so that no
one is blocked on input method. The body is parsed at binding power 0, so it
extends as far as it can and stops at `,` `)` `}` `]` `;` — none of which are
infix operators. A lambda therefore needs no parentheses as a final argument
and needs them as a non-final one, which is the usual rule.

**`=>`, not `,`.** The argument is in the issue; the short version is that
container literals arrive with `nested-inductives-container-fields` and
`[λ (x: Nat), f(x), g]` would then be ambiguous between a one- and a
two-element vector. `FatArrow` already exists in the lexer
(`crates/syntax/src/lexer.rs:30`) for match arms, and `binders => body` is
the same rule in both places, so this is not an overload.

**`=>`, not `->`.** `->` is now the type arrow, so `λ (x: A) -> e` would read
as an ascription.

### 1.3 Application

Application becomes postfix rather than an atom-level named form:

```
postfix  ::= atom ( '.' ident '(' args ')' | '(' args ')' )*
```

so `f(a)`, `g(a)(b)`, `(λ x => x)(3)` and `xs.fold(z, f)(k)` all parse.
`@f(a, b)` **stays an atom-level named form** — see §5.3: `@` exists to
suppress implicit insertion, implicit insertion is name-directed, so `@` on a
non-name has nothing to suppress.

---

## 2. Two corrections that reading the code forced

Per the house pattern, the places where writing this against the actual
elaborator contradicted the issue's plan.

### 2.1 No implicit binders in function types or lambdas this round

The issue proposed `{x: A} -> B` and `λ {x: A} => e`, matching the `{}`
implicit-parameter spelling on `fn`/`theorem`. **That cannot work yet, and
the reason is structural.**

Implicitness is *not* a property of the kernel's `Type::Pi` — the kernel has
one function type and no notion of an implicit argument. It lives entirely in
the elaborator, as `ParamMeta.implicit` on a **declaration**, looked up *by
name* (`params_of`/`implicit_mask`, `crates/elab/src/lib.rs:1303–1315`), and
consumed by `apply_implicit`'s `mask` (`lib.rs:1362`).

So a function *type* has nowhere to record the flag, and a λ-bound value has
no `ParamMeta` to look up. Supporting implicit binders here means either
putting implicitness into the kernel (no — it is an elaboration concern) or
carrying an implicitness spine alongside every `Type` in the elaborator (a
real design, and not this round's).

It also buys nothing yet: **the surface has no universe.** `TyKind` cannot
say `Type`, so there is no `{A: Type}` to write, and type parameters exist
only on `inductive` declarations where they are monomorphized. Implicit
*value* binders in a function type (`{n: Nat} -> …`) are the only expressible
case and are not worth the machinery.

**Decision: explicit binders only.** `{` in a function type or lambda binder
is diagnosed (§8). Revisit with the universe/polymorphism layer.

### 2.2 The `Call`-head refactor is small, not broad

The issue called it "mechanical but broad … the bulk of the diff". Measured:
**13 sites**, 9 in the parser and 4 in the elaborator (`lib.rs:759, 774, 806,
1643`). Three of the four elaborator sites are name-keyed special forms
(`absurd`, constructors, `Succ`) that want a `Var` head anyway.

The bulk of the diff is instead §3.1's `ty()` restructure and §5's new
elaboration arms.

**Recommended shape:** `ExprKind::Call { name: String, args, explicit }`
becomes `ExprKind::App { head: Box<Expr>, args: Vec<Expr>, explicit }`, kept
**n-ary rather than curried**. N-ary preserves the existing implicit-insertion
algorithm, which needs the whole argument list at once, and keeps `@`
meaningful. Add one helper

```rust
fn as_named(e: &Expr) -> Option<(&str, &[Expr], bool)>
```

matching `App { head: Var(name), .. }`, and the four elaborator sites keep
their current shape.

---

## 3. Parsing

### 3.1 `ty()` restructure

`ty()` today (`crates/syntax/src/parser.rs:329`) parses an *expression* first
and reinterprets it, with an early return for the `Ident '<'` case. That
early return is why arrows need a restructure rather than an added branch:
`D<A> -> B` must not bypass the arrow check.

```
fn ty():
    if lookahead is LParen Ident Colon:          # 3-token; ty() already does 2
        parse '(' ident ':' ty ')' , expect '->' , cod = ty()
        return Fn { binder: Some(ident), dom, cod }
    lhs = ty_atom()
    if peek == Arrow:
        bump; return Fn { binder: None, dom: lhs, cod: ty() }   # right-assoc
    return lhs
```

`ty_atom()` is today's body of `ty()` with its early return kept internal.

**No new ambiguity at existing call sites**, each checked:

| Site | After the type comes | Safe because |
|---|---|---|
| `fn f(…) -> T { … }` (`parser.rs:228`) | `{` | `{` is not `->` |
| `theorem t(…): T { … }` | `{` | as above |
| `j(p, (y,q) -> M, case)` (`parser.rs:556`) | `,` | `,` is not `->` |
| `match … as x -> M { … }` (`parser.rs:508`) | `{` | as above |
| `let x: T = e;` (`parser.rs:264`) | `=` | as above |
| field types, type arguments | `,` `)` `>` | as above |

The `j` and `match`-motive forms use `->` for *binder-to-body*, which will
read oddly once `->` is the type arrow. That is a follow-on (§7), not part of
this round.

**One known restriction, recorded rather than discovered:** a type may not
*begin* with `{`, so if implicit binders are ever added to function types
(§2.1), an implicit-headed type would be ambiguous with a `match` arm brace
in `match t as x -> {…} -> T { … }` and would need parentheses.

### 3.2 Lexer

Add `TokKind::Lambda`, lexed from `λ` (U+03BB — a non-ASCII codepoint, so the
identifier rule must not swallow it). `fun` is an ordinary keyword via the
existing `at_kw`/`eat_kw`. `FatArrow` and `Arrow` already exist.

### 3.3 Expressions

`atom()` gains the lambda case. `postfix()` gains `'(' args ')'` alongside the
existing `'.' ident '(' args ')'`. `@name(args)` stays where it is.

---

## 4. What elaborates to what

Nothing new in the kernel; the mapping is the identity on the obvious things.

| Surface | Kernel |
|---|---|
| `(x: A) -> B` | `Type::Pi { dom_level, cod_level, dom, cod }`, `cod` binding one local |
| `A -> B` | the same, with `cod` not using its binder |
| `λ (x: A) => e` | `Term::Lam { dom_level, cod_level, dom, body }` |
| `f(a)` | `Term::App { fun, dom_level, cod_level, dom, cod, arg }` |

The Π level rule is `Level::max(dom_level, cod_level)`, exactly as
`elab_decl_inner` already computes when it closes a declaration's telescope
(`crates/elab/src/lib.rs:376–382`). **Use that rule from one place**; a
declaration's telescope and a written function type must not compute levels
differently.

---

## 5. Elaboration

### 5.1 `elab_ty` — the new `TyKind::Fn` arm

```
elaborate dom in cx                        -> (D, dl)
cx.push(binder-name or "#fn", D, dl)
elaborate cod in the extended cx           -> (C, cl)
return (Type::Pi { dl, cl, D, C }, Level::max(dl, cl))
```

The pushed name for a non-dependent arrow uses the `#`-prefix convention
already used for elaborator-introduced binders (they are filtered from the
goal listing as unspellable).

### 5.2 Lambda: checking and inference

**Checking** (`elab_check_hinted`, `lib.rs:724`) gains a `Lam` arm, and it is
the primary path:

```
whnf the expected type -> Type::Pi { dom_level, cod_level, dom, cod }
                          (else: "a lambda needs a function type here")
push the binder with `dom` (the *expected* domain)
check the body against `cod` at `cod_level`
return Term::Lam { dom_level, cod_level, dom, body }
```

An annotation on the binder is elaborated and must be **convertible** with
the expected `dom` — `conv_type` is already imported (`lib.rs:29`). Using the
expected domain rather than the annotation keeps the emitted term's
annotation aligned with the type it is checked against; the written
annotation is a readability aid and a wrong one is a diagnostic, not a
silently different term.

Multi-binder lambdas peel one Π per binder.

**Inference** (`elab_infer`, `lib.rs:789`) gains a `Lam` arm requiring **every
binder to be annotated**:

```
elaborate the annotation                   -> (D, dl)
push, infer the body                       -> (t, C, cl)
return (Term::Lam{…}, Type::Pi{…}, Level::max(dl, cl))
```

An unannotated binder in inference position is an error pointing at checking
position (§8). This is the same shape as the existing rule that holds for
`refl` and holes: forms whose type is not determined by their syntax are
checking-only.

### 5.3 Application with a general head

`apply_explicit` (`lib.rs:1320`) already does exactly the right thing: it
walks the Π spine from a `head: Term` and its type, supports **partial
application**, and uses `name` only for error text and goal-name hints. The
change is to take `Option<&str>` there instead of `&str`.

The dispatch, at an `App { head, args, explicit }`:

```
if head is Var(name) and not `explicit` and implicit_mask(name) has any true:
    apply_implicit(...)          # unchanged, name-directed
else:
    infer head -> (h, hty, hl)
    apply_explicit(cx, display_name, h, hty, hl, args)
```

**Implicit insertion stays name-directed and that is a real restriction, not
an oversight** (§2.1): a function *value* has no parameter metadata, so
applying one is always explicit. `apply_implicit`'s existing refusal to mix
partial application with implicit insertion is unchanged.

---

## 6. Interactions to test, not assume

The `Vec^l` level drop and the tier-0 tyvar capture were both "true by
construction" right up until they were not. Each of these is a claim this
round must *observe*.

1. **A self-call inside a lambda body.** The `Nat` guard compares a de Bruijn
   *level* (`cx.names.len() - 1 - i == pred_pos`, `lib.rs:1136`) and the `Wf`
   guard shifts children by `cx.names.len() - depth` (`lib.rs:1140`). Both are
   stable under extra binders by construction. Test
   `match t { Node(l, r) => g(λ (x: Nat) => f(l)) }` anyway.
2. **An alias referenced under a lambda.** `let` bindings and `Wf` arm binders
   are `Alias`es carrying a `depth` and shifted on use (`lib.rs:352`). A
   lambda pushes; check the shift.
3. **A hole under a lambda binder.** `new_goal` builds `?m^{id_Γ}` over the
   *current* Γ, which now includes the λ-binder, while the `on` discharge is
   elaborated outside it. This is the same shape as
   `issues/nested-goal-discharge.md` and is **expected to need a rejection**:
   a goal whose context mentions a binder not in scope at its discharge site
   cannot be strengthened back down. Diagnose it (§8) rather than emit a
   wrong term; lift it with, or after, `nested-goal-discharge`.
4. **η at `Π` is definitional.** `conv.rs:535` compares at a `Π` type by
   applying both sides to a fresh variable, unconditionally at every layer.
   So `λ (x: Nat) => f(x)` and `f` are convertible and `refl` proves it. Users
   will expect this; pin it, including for a *neutral* `f`.

   Note for whoever next edits `docs/wf-former-design.md`: its opening
   describes `Π` as "the one type family this kernel deliberately does not
   η-expand". Read literally against `conv.rs:535` that is wrong — the
   property route A actually lacked is that a *neutral* children-function
   cannot be reconstructed from a projection, which is not the same as
   lacking η. Worth a clarifying edit there; not this round's job.
5. **Partial application then re-application.** `add(1)` is a function value;
   `add(1)(2)` must equal `add(1, 2)`.

---

## 7. Follow-on this enables (explicitly not in this round)

`j(p, (y, q) -> M, case)` and `match … as x -> M` spell binder-to-body with
`->`. Once `->` is the type arrow those read as ascriptions, and once lambdas
exist the motives can simply *be* lambdas — two special-form syntaxes
collapsing into one general one. A small round of its own, after this lands
and after the printer is updated.

---

## 8. Rejections

Each is a diagnostic, not a mis-elaboration. The discipline is
`issues/goal-holes.md`'s: name the restriction and point at where it is
tracked.

| Written | Message |
|---|---|
| `λ x => e` in inference position | "this lambda's binder needs a type annotation, or the lambda needs a checking position (`let f: A -> B = λ x => e;`)" |
| `λ x => e` where a non-function is expected | "a lambda needs a function type here; expected `T`" |
| `{x: A} -> B`, `λ {x: A} => e` | "implicit binders are not supported in function types yet — implicitness is a property of a declaration's parameters (see issues/surface-function-types.md §2.1)" |
| `?p` under a λ-binder | "a hole may not appear under a lambda binder: its context would mention `x`, which is not in scope at the discharge (issues/nested-goal-discharge.md)" |
| `@` on a non-name head | "`@` suppresses implicit-argument insertion, which only applies to a named callee" |
| a function type as an `inductive` field | "a field of a finitary declaration may not be a function (that is the infinitary tier, issues/inductive-compiler.md)" |
| too many arguments | existing `apply_explicit` message, with the head printed when it is not a name |

The `inductive`-field rejection matters: a `Π` field is what makes a
declaration infinitary, and the tier-1 lowering assumes finitary children
throughout. Without this check a user could write one and the generator would
mis-lower it — the hazard class `docs/inductive-tier0-lowering.md` opens by
naming.

---

## 9. Acceptance checklist

Every item is a test, and every positive one is elaborated and then re-checked
by the real kernel.

1. `(x: A) -> B` and `A -> B` parse, print back, and elaborate to `Type::Pi`
   with the level `Level::max(dom, cod)`; `A -> B -> C` associates right.
2. `a = b -> C` parses as `(a = b) -> C`.
3. `D<A> -> B` parses — i.e. the `Ident '<'` early return no longer bypasses
   the arrow check (§3.1).
4. `λ` and `fun` both parse; the printer emits `λ`.
5. A lambda checks against an expected Π; a lambda with annotated binders
   infers; an unannotated binder in inference position is rejected (§8).
6. A multi-binder lambda equals its nested form.
7. `(λ (x: Nat) => Succ(x))(3) = 4` by `refl` — β fires.
8. **η**: `λ (x: Nat) => f(x)` and `f` are convertible, for `f` a global and
   for `f` a neutral local (§6.4).
9. A function-typed parameter: `fn twice(f: Nat -> Nat, n: Nat) -> Nat` with
   `twice(λ x => Succ(x), 0) = 2` by `refl`.
10. A dependent function type used for real: `cong` over an arbitrary
    function — the thing `issues/surface-operators.md` deferred.
11. Partial application: `add(1)` typechecks as a function value and
    `add(1)(2) = add(1, 2)`.
12. Head-is-an-expression: `(λ (f: Nat -> Nat) => f(0))(λ x => Succ(x)) = 1`.
13. Each §6 interaction, as its own test: self-call under a lambda, alias
    under a lambda, hole under a lambda (a rejection), partial re-application.
14. Each §8 rejection, with its message asserted.
15. The whole existing suite still passes — in particular the parser tests
    that pattern-match `ExprKind::Call` (§2.2) and the tier-0/tier-1
    acceptance files.
