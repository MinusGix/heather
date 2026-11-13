# `crates/linked` — compiled Heather linked into Rust

Paths here are relative to `crates/linked` unless they start at the
repository root.

- **`generated/*.s` is `compile-x86`'s checked-in output** for
  `generated/EXPORTS.tsv`, held to the compiler by
  `crates/cli/tests/native_linked.rs` (a native gate). After changing a linked
  module (`lib/native/crypto/`, `lib/lang/lexer/`), the lowering or the
  emitter, run **`scripts/linked`** to rewrite the files (`--check` compares;
  a row whose binary and import closure are unchanged is not recompiled) and
  the Rust declarations with them (`generated/exports.rs`, never edited:
  `crates/cli/tests/linked_exports.rs`).
- **A new export** is a line in the table (module, function, parameters, a
  span of bytes it reads as `name: span` and one it stores into as
  `name: span mut`; a method is named by its path, `List::f`, and exported
  under the symbol the path derives, `list_f`, or one written as
  `sym = List::f`; a fourth column names the export whose program the
  function is a function of, and it is then a label in that export's file,
  not a file), a wrapper in `src/`, and tests against an independent
  reference. Run `scripts/linked` before writing the wrapper: the compiler
  links this crate, so a wrapper of a symbol not yet generated stops the build
  that would generate it.
- **A value the Rust reads the linked code's answers with** is a `def` of the
  module (a numeral), a row of `generated/CONSTANTS.tsv`, and Rust's copy is
  `generated/constants.rs`, written by the same script (`TOKEN_END_BITS`).
- **A generated file that lost a symbol fails every build**: the `heather`
  binary links these files, so one that lost a symbol (a merge conflict taken
  from the wrong side) fails with `undefined symbol: scan_token`. Restore a
  complete copy (`git checkout HEAD -- crates/linked/generated/<file>.s`),
  build, then run `scripts/linked` (`issues/linked-assembly-bootstrap.md`).
- **The scanner** (`src/scanner.rs`) is held to `heather_syntax::lex` by
  `tests/scanner.rs`; after changing its `PROBES` or the automaton, run
  **`scripts/lexer-probes`** to rewrite the evaluated probes in
  `lib/_tests/lang/lexer`.
- **`HEATHER_LEXER=linked`** has the `heather` binary cut every source with
  Heather's own scanner (compiled, linked;
  `heather_syntax::lexer::install_scanner`, `issues/self-lexer-linked.md`);
  values and every refusal stay the Rust lexer's, so output is unchanged, and
  `HEATHER_LEXER_REPORT=1` prints who cut what. Off by default. A new token
  kind is three numberings to extend: `lexer_scan.hthr`'s `KIND_*`,
  `heather_linked::scanner::Kind` and `heather_syntax::lexer::scan_code`
  (`tests/scanner.rs` holds them to each other).
