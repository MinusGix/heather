# Checking-position sequent binders

Status: implemented 2026-08-19. Owning issue:
[`sequent-binder-expression`](../issues/sequent-binder-expression.md).

## Decision

Heather accepts

```heather
x y ⊢ body
(x: A) ⊢ body
```

as checking-position spellings of

```heather
λ x y => body
λ (x: A) => body
```

The Unicode `⊢` and ASCII `|-` lex to the same token. The turnstile is the
loosest expression form and associates to the right, so a match arm needs no
extra block:

```heather
Zero => bad ⊢ false_elim(bad),
```

The surface changes the reading direction, not the term theory. A lambda says
"construct a function"; a sequent says "under these assumptions, establish
the body." The parser lowers the latter directly to `ExprKind::Lam`, and the
elaborator and kernel never learn a new introduction form.

## Block scope

At a block's result position, a sequent header scopes over every remaining
statement and the result:

```heather
{
    x ⊢
    let y = f(x);
    g(y)
}
```

This lowers to `λ x => { let y = f(x); g(y) }`. Bindings before the sequent
remain outside it and are visible in its body. Goal discharges after the body
remain attached to the declaration block; the transparent block synthesized
under the lambda does not acquire a nested discharge scope.

## Binder rules

- Bare binders receive their domains from the expected Pi telescope.
- `(x: A)` checks `A` against the corresponding expected domain using the
  ordinary annotated-lambda rule.
- Several binders peel consecutive explicit Pis from left to right.
- Implicit binders are not inferred by an explicit sequent binder. The
  ordinary lambda diagnostics report an explicit/implicit mismatch.
- A sequent in inference position is refused exactly as its lowered
  unannotated lambda would be.

The deliberately separate anonymous form is designed in
[`argument-slot-sections`](../issues/argument-slot-sections.md). It will share
the checking-position Pi-introduction semantics but not this parser lowering.
