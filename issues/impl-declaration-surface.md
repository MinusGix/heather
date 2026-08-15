---
title: The impl declaration as a first-class surface: inline proofs, derivation requests, transfer-on-demand
status: open
labels: [design,frontend,syntax,compiler]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] items 1+2 (2026-08-15); the
anchor issue for the design discussion. Two probed gaps and one design
question.

**Gap 1: transfers have no surface syntax.** `reprgen` is a Rust API; a
user cannot request "derive the Impl of `length` at `ListTok`" from a
`.hthr` file. **Gap 2: `impl` clauses refuse inline expressions** — every
hand override costs three named top-level artifacts plus the block naming
them; the user wants inline expressions "regardless", plus a first-class
`impl fn` conceptualization (§1.2 review wish, 2026-08-14).

**The design question (user, 2026-08-15), verbatim concerns:** a bare
`:= derived` "feels a bit mystical" — is derivation specific to the repr
in hand? how does it work under fancier repr generators (boxed-tree repr,
linear vectorized repr)? if autoderive works in most cases, why isn't it
the default? and if it can't, should Impl generation be part of how a
repr generator (`repr::naive()` and successors) metaprograms, rather than
something the caller requests?

**Coordinator's position going into the discussion** (to be tested
there): the transfer is repr-AGNOSTIC by construction — reprgen consumes
only the correctness basis (fold anchor + images), which is why one
generator serves naive, `Bin`, and `BinC` unchanged. So the layering that
falls out of the existing machinery:

1. *Repr generators* mint bases (and may pre-register cost-basis
   overrides for their signature ops — a vectorized repr registering O(1)
   `length`/`index` is just generated hand-overrides into the same open
   registry).
2. *The transfer* fills correctness-derived Impls **on demand**: the
   recursive-generation half already does exactly this inside an emission
   (a missing in-fragment callee is generated silently), so extending it
   to resolution sites (the `runtime_fn` boundary, an explicit use) makes
   derived-by-default true precisely where autoderive works, per the
   user's instinct — with a decline surfacing as the error, reason named.
3. The explicit `impl` spelling then exists for *pinning* (fail at
   declaration time, freeze bytes), hand overrides, and via-derived — not
   as the ordinary way transfers happen.

Related: [[generators-in-the-language]] (don't fight the eventual
meta-layer home), [[certifying-generator]] (certgen has the same
no-surface gap; one design should serve both), [[instance-shorthand-syntax]].
