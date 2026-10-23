# certgen keys functions on global identity

Round design for `issues/certgen-namespaced-function-identity.md`, direction 2
(chosen 2026-09-23). Small and settled: this doc is the whole charter.

## Problem

certgen treats a function's **surface spelling** as its identity. It looks
declarations up by `d.name`, resolves callees to *base* names
(`Elaborator::global_name_at` strips everything up to the last `::`), compares
`Emission::closure` entries as strings, and splices the spelling into generated
identifiers (`{f}_gen_body`, `{m}_gen_conv_in_{f}`, …). Once `add` became
`Nat::add` this broke three ways:

- a base name can be ambiguous or unbound where the text is re-read (`add`
  alone no longer resolves);
- `Nat::add_gen_body` is either undeclarable or silently becomes a member of
  `Nat`'s namespace;
- two closure members with one base name would be conflated.

## Design

Two different jobs were being done by one string. Split them.

1. **Identity is the Ψ coordinate.** Resolve `d.name` exactly once at the top
   of `generate_in_language` (`global_abs`; decline if it does not resolve).
   From there on a function is its `abs: usize`. `BodyCode::callees` becomes
   `Vec<usize>`, filled with the callee's absolute index where it is currently
   turned into a name. `Emission::closure` becomes `Vec<usize>` too, and so do
   the lookups the chain renderer and `LetCall` indices do against it, the
   callee-closure prefix merge in `emit_with_model`, and `GenCtx` lookups of a
   callee's emission. Nothing compares function names as strings any more.
   The identity is per-elaborator, which is the lifetime `GenCtx` already has.

2. **A stem names generated items.** Each closure member gets a *stem* for
   `_gen_*` identifiers. It is derived from the global's **declared name**,
   meaning its qualified key minus the module path (`Nat::add`, `dbl`), with
   `::` replaced by `__`. So `Nat::add` gives `Nat__add_gen_body`, and
   top-level `dbl` stays `dbl_gen_body`, which leaves every existing fixture
   for a top-level test function byte-identical. Stems are computed once per
   emission, as a map `abs → stem`. If two distinct closure members get the
   same stem (the same declared name in two modules), certgen **declines**
   with a sentence naming both qualified globals. It does not invent a
   disambiguating suffix, because a stem has to be predictable from the
   source.

3. **A reference spelling names the function itself.** Wherever the emitted
   text *calls or names* a closure member (the spec argument in fixtures,
   `embed_T(f(…))`, `CompileNat1(f)`, the instance record `{record}({f})`,
   and so on), it uses a spelling that resolves back to that `abs` where the
   emission is elaborated. Hypothesis to verify: the canonical qualified
   name (`global_qualified_name_at`) always resolves, and the declared name
   (`Nat::add`) resolves wherever the emission's module imports the
   declaring one. Prefer the declared name when it resolves to the same
   global (`base_name_resolves_to`-style check, on the declared name), and
   fall back to the qualified one. Record in this doc what the probe showed.

4. **`Emission` exposes the readable form.** Keep `Emission::name` as the
   declared name of the emitted function. Add a
   `closure_names(&self, e) -> Vec<String>` (declared names) or store the
   declared names beside the indices, whichever reads better, so tests can
   pin `["Nat::add", "viaadd"]`.

## What the probe showed (2026-09-23)

A throwaway unit test, run through `scripts/test` before any restructuring:
prelude, `logic`, `bool`, `nat`, then a module `ir_v1` with `import nat;` and
`viaadd` (receiver-style), the same shape the certgen tests elaborate in.

- `global_qualified_name_at` gives `nat::Nat::add` for `Nat::add` and
  `ir_v1::viaadd` for the test-local `viaadd`. Both resolve back to their
  global (`base_name_resolves_to`), and both parse and elaborate as call heads
  inside a further `ir_v1` chunk.
- The declared name `Nat::add` resolves in `ir_v1` (it imports `nat`), and so
  does `viaadd`. The base name `add` resolves to nothing, which is the
  original failure.
- `global_abs("Nat::add")` resolves in the tests' elaborator state: after a
  module pass the elaborator stays in that module's scope, so it is the
  scope the emission is later elaborated in.
- The declared name is clean to get: the registry key is `module::name`, and
  `names::split_qual` splits at the first `::` (module names are single
  segment), giving `Nat::add` and `viaadd`. It is now
  `Elaborator::global_declared_name_at`.
- The hazard is real: `fn Nat::add_gen_body2()` declared in `ir_v1` lands as
  `ir_v1::Nat::add_gen_body2` and resolves as `Nat::add_gen_body2`, i.e. a
  member of `Nat`'s namespace. `Nat__add_gen_body` is an ordinary top-level
  item, and `Nat::add_gen_body` then names nothing.

So the hypothesis holds as written: the reference spelling is the declared name
where it resolves back to the global, else the qualified one.

## Implementation notes and amendments

- **§1.** The name is resolved once, in `generate_in_language`. The signature
  checker, the peel and the body reflection read Ψ by index from there
  (`fn_type_code_at`, `global_body_in_code_form_at`, `global_body_at`,
  `body_code(e, abs)`). The public `fn_body_code(name)` resolves and then
  delegates. `BodyCode::callees`, `Instr::Call`, `RCert::Call`, the closure,
  `GenCtx::get` and the fixture evaluator all key on `usize`.
- **§3, amended.** The spellings are checked against the elaborator's
  *current* scope when certgen runs. That is sound as long as the caller
  elaborates the emission in that same scope, which every caller does today.
  If neither the declared nor the qualified name resolves back, certgen
  declines instead of emitting text that names some other function.
- **§4.** The names are stored beside the indices: `Emission` keeps a
  per-member table (`abs`, declared name, stem, spelling), and
  `Emission::closure_names()` reads the declared names off it. The table is
  recomputed for each emission's own closure, so a callee's spelling is
  checked where the caller's emission is elaborated.
- **Tests, amended: `IR_ADD` changed.** `Emission::ir_body` prints the
  generated item names (`add_gen_arm_zero() = …`), so `IR_ADD`'s three item
  names became `Nat__add_gen_*`. Its instructions did not move. `IR_VIAADD`
  and every other IR literal are byte-identical.
- **Tests, amended: where (a) and (c) live.** `certgen.rs` elaborates no
  emission (it has only the declarations prefix, by budget), so (a), which
  needs the `Nat::add` emission elaborated, lives in `certgen_emissions.rs`.
  It checks `Nat__add_gen_body` and `Nat::add_gen_body` as twin probes, one
  resolving and one not. The negative control (c) is there too, as mutation
  (f): every `Nat::add(` in `viaadd`'s emission is respelled `Nat::mul(`,
  which leaves the program and every generated name alone, and the kernel
  refuses it. The existing member-swap control (e) is kept, with the
  `Nat__add` stem. (b), the stem-collision decline, is in `certgen.rs` as
  planned: modules `cgstem1` and `cgstem2` each declare `f`, the second calls
  the first, and the decline names `cgstem1::f` and `cgstem2::f`.

## Tests

- Callers written against the old spelling become `a.add(…)` or
  `Nat::add(a, …)`: `viaadd` (certgen, certgen_emissions), `viafield` (certgen_nonnat), `sel3` (certgen_t0param) and `esum` (certgen_tier1), the five red targets, each failing
  with `unbound name add`. `lib_decl("add")` becomes `lib_decl("Nat::add")`,
  since the parsed `Decl` already carries that name.
- Closure pins become declared names (`["Nat::add", "viaadd"]`). Text pins
  like `add_gen_conv_in_viaadd` or `PFun(add_gen_body(), …)` become the
  `Nat__add` stem. The reflected IR fixtures (`IR_ADD`, `IR_VIAADD`) should
  not change, because they are shape and not names. If one has to change,
  that is a finding, so report it.
- New, small, in `crates/elab/tests/certgen.rs`:
  - (a) a member function's emission elaborates, and **no** `_gen_` item
    lands in `Nat`'s namespace. Assert that `Nat::add_gen_body` does not
    resolve after the emission is elaborated.
  - (b) the stem-collision decline. Two modules each declare a top-level
    `f` in one closure; the result is a decline naming both.
  - (c) a negative control. With a hand-corrupted closure pointing at the
    wrong `abs` (or the members swapped, as the existing control (e) does),
    the kernel still refuses.

## Out of scope

Ghost/hygienic identifiers (direction 3). The stem scheme is a mangling, and
a user could still hand-write `Nat__add_gen_body`. Don't touch
`lib/certgen/certgen_code.hthr` or the kit.
