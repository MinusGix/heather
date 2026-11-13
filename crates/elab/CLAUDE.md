# `crates/elab` — the elaborator

- **The unit tests (`crates/elab/src`) build and run as the
  `heather-elab-unit` package** (`scripts/test -p heather-elab-unit --lib`),
  not `-p heather-elab --lib`: a package of their own keeps their compile off
  the heather-cli dev-dependency chain
  (`issues/elab-unit-tests-wait-on-cli-dev-dependency.md`).
- **An elaborator method goes on its area's view, not on `Elaborator`**: each
  area's module defines `Area<'e>(&'e Elaborator)` for its `&self` methods and
  `AreaMut<'e>(&'e mut Elaborator)` for its `&mut self` ones, both
  dereferencing to the elaborator, and another area calls
  `Area(self).method(…)` (`crates/elab/src/lib.rs`'s module doc has the
  pattern and what differs: `self.0.clone()`, `self.0.a` for split borrows).
  rustc compiles all of one `Self` type's methods as one unit, wherever the
  `impl` blocks are written, so a method on `Elaborator` recompiles with
  everything else on it.
- **`scripts/codegen-units`** lists a build's units by size and what fills
  them; a unit that has grown back shows there.
- `scripts/rustc-wrapper` (wired in `.cargo/config.toml`) turns rustc's
  cross-unit optimisation pass off for the elaborator's incremental builds
  only, because there one edit redid it for the whole crate
  (`issues/elaborator-crate-compile-per-edit.md`).
