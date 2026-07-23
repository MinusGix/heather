# Heather

A low-level, imperative-leaning theorem prover language. The core type theory
target is DeLaM (dependent layered modal type theory — see `docs/delam/`),
whose box modality gives intensional access to code as syntax.

The central design bet: everything is kerneltime by default. Definitions and
proofs live in one solid logical layer, and *compilation is certifying* — a
function becomes executable by having a `Compile` typeclass instance carrying
IR plus a proof that the IR's behavior matches the function. The compiler is
just another kerneltime function (privileged operationally, never logically):
it consumes proof-carrying instances and emits executables. Generators that
mint `Compile` instances by intensional analysis of boxed code need no
verification themselves — each output carries its own certificate.

Disciplines like lifetimes, uniqueness, or GPU-compatibility are intended to
be *libraries*: analysis functions over boxed code that mint typeclass
evidence, not kernel features.

## Layout

- `crates/kernel` — trusted checker (correctness first; mirrors the in-progress
  Coq formalization of DeLaM)
- `crates/syntax` — lexer/parser/surface AST (untrusted)
- `crates/cli` — `heather` driver binary
- `docs/` — papers; `docs/delam/` is the type-theory reference
- `issues/` — repo-local issue tracker (`scripts/issue`, see `issues/README.md`)
