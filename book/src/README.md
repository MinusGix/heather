# The Heather language

Heather is a low-level, imperative-leaning theorem-prover language. Programs,
specifications, and proofs share one language. Definitions compute; theorems
are opaque after checking; axioms make assumptions explicit.

```heather
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k) => cong_succ(add_zero(k)),
    }
}
```

The trusted kernel checks the elaborated result. Surface conveniences and
tactics may construct proof terms, but none of them add a trusted proof rule.
Compilation follows the same principle: executable code is accompanied by a
certificate relating it to its specification.

This book is the user-facing guide to the implemented language. The parser and
surface AST in `crates/syntax`, together with elaborator tests, are its source
of truth. Files under `docs/` record design decisions and implementation
history; they are useful deeper reading, but many are not tutorials.

## How to read this book

Read [Getting started](getting-started.md), then the language chapters in
order if Heather is new to you. For a quick lookup, use the
[tactic reference](proofs/tactics.md) or [syntax index](reference/syntax-index.md).

Some features require a standard-library import. The reference calls this out
where it matters. Most words that look like keywords are contextual: they are
recognized only in the grammatical position where the form makes sense.
