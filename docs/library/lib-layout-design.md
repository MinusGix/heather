# Library layout: folders for `lib/`

Status: adopted 2026-10-23. Minus agreed the layout and settled §5 the same
day (Linux into `std/os/linux`, `bitvec/` stays top-level, float stems stay
for now), and phases 0 and 1 (§6) landed together with this doc. Below,
"today" means master before the move, at ef37e97; the measurements in §2 and
§7 come from a prototype of the whole move made there.

The ask: give `lib/` a folder structure, so that tactics sit together,
algebra is grouped, number types have their own folder, and so on. Today
`lib/std` holds 59 modules side by side, plus four subfolders that grew one at
a time (`arch/x86_64/`, `bitvec/`, `float/`, `parser/`). `lib/` itself holds
another 31 modules, from the native compiler, the Linux model and certgen.

The short answer: folders are cheap in Heather because module names do not
contain them. A module is named by its file stem, and the loader already looks
in every folder below the search path (`docs/language/modules-design.md` §3.2). So
moving `rat.hthr` to `num/rat.hthr` changes no `import` line, no qualified
name, no exported Lean or Rocq name and no cache key. The prototype moved
all 120 modules with **zero edits to any `.hthr` file**. What does change is
every place that cites a file by its *path*: Rust `include_str!`s, docs,
issues and scripts. A script rewrites those mechanically (§6). Before the move,
two small CLI changes are needed (§6, phase 0). One of them also fixes an
existing gap: `heather check lib/std` silently skips 30 modules today (§2.2).

## 1. What a folder means in Heather today

- **Module = file, name = stem.** `import nat;` names `nat.hthr`, wherever
  it lives. There is no `std::num::nat`; hierarchical module paths were
  decided against (`docs/language/modules-design.md` §2, §3.4, "Not built").
- **Lookup tiers.** `import m` is looked up first in the importing file's own
  folder, then in each `-L` folder (the CLI defaults to `-L lib/std`), then
  in **every folder below** those `-L` folders, at any depth. Dot-folders are
  skipped (`crates/cli/src/loader.rs`, `directories_below`). If a name is
  found in two folders of the same tier, that is an error. So a folder can
  hide nothing and shadow nothing: stems must be unique across the whole
  tree, and the loader already enforces it.
- **Folders are not namespaces.** `x86_64_fetch` and `parser_core` carry
  their family in the stem because two folders cannot both have a `core`.
  `float/` broke that habit (`round`, `error`, `arith`), and it works
  because nothing else is called `round` yet.
- **What keys on the path.** The *lint profile* does: everything below
  `lib/std` gets `LintProfile::Stdlib`, which asks for Unicode `→ ↔ ⊢ λ`
  (`crates/cli/src/main.rs`, `lint_profile_for_path`). The profile is part of the
  semantic-image key. Nothing else in the elaborator, the cache, or the
  exporter looks at a path: image keys hash the module name, the source, the
  dependency interfaces and the lint profile (`crates/cache/src/module_image.rs`,
  `ModuleCacheKey::for_source`), and the exporter names every declaration
  `module::name` from the stem.

## 2. Survey

### 2.1 Who cites a library file by path

Counted by the prototype's rewrite script. Each count is a path that would
go stale after the move and needs rewriting.

| Where | Files | Path citations | Kind |
|---|---|---|---|
| Rust (tests, `native/support.rs`, `certgen.rs`, comments) | 170 | 1168 | `include_str!("../../../lib/std/rat.hthr")`: a broken one fails the build |
| `docs/` | 127 | 409 | prose links |
| `issues/` | 245 | 595 | prose links |
| `scripts/` (`perf` corpus, `probe-whnf-sharing`) | 3 | 17 | paths handed to `heather check` |
| `examples/`, `perf/README.md`, `lib/**/README.md` | 3 | 3 | prose |
| `probes/` | 77 | ~6000 | frozen snapshots of old trees: **left alone** |
| `perf/snapshots/*.json` | | | the diary, keyed by file path: history, left alone (§7) |

These need no change: the 1046 `include_str!` pairs pass the stem as the
module name next to the path, so only the path half moves; `import` lines;
the elaborator's built-in module names (`relational_context.rs` asks for
`relation_props` and `relation_context` by name); test-family names
(`lib_std_rat.rs` stays `lib_std_rat.rs`); the LSP and the native builder,
which already search `lib/std` and `lib`; the formatter, which already walks
folders recursively.

There are 189 citations of modules that no longer exist at all (`elf64_runs`,
`decimal_line`, … from the burned process stack). The script skips them. They
are history and do not get worse.

### 2.2 A gap the move exposes: `heather check lib/std` is not the whole library

A directory argument checks only its *immediate* `.hthr` files, plus whatever
those files import (`roots_for_path`, `docs/language/modules-design.md` §3.3). Nothing
at the top of `lib/std` imports `float/*`, `bitvec_omega`, `byte` or any of
`arch/x86_64/*`, so **30 modules are not checked by the command
`CLAUDE.md` and the modules design call the whole-library check**. The export
wide sweep (`crates/export/tests/library_wide.rs`) has the same blind spot,
because it uses its own non-recursive `read_dir`. The tests do cover those
modules one by one, so this is a gap in the command and not a hole in the
suite. After the move, though, `lib/std` would have no files at its top level,
and the command would check nothing at all. Phase 0 fixes that (§6).

### 2.3 How the modules depend on each other

The import graph (from `import`/`export` lines) already has the shape of the
folders below. `core` imports nothing. `num` imports `core`. `algebra` and
`relation` import `core` and `num`. `data` imports `core` and `nat`. `tactic`
kits import `num` and `data`. `itree` imports only `logic` and `nat`.
`arch/x86_64` imports `bitvec`, `data`, `machine/location` and `relation`. `os/linux` imports `arch` and `itree`. The
native compiler (`function_ir*`) imports all of them. The only edges that run
"upward" are two tactic kits imported by the libraries they serve:
`omega` (by `rat`, `creal`, `float/*`, `memory`, `decimal`, `parser*` and the
x86 and Linux models) and `ring` (by `rat` and `float/*`). That is expected, and folders impose no
order anyway.

## 3. The proposed layout

```text
lib/
  std/                         the library programs import (Stdlib lint profile)
    core/        logic bool option pair result
    num/         nat int rat creal
      float/     float dyadic round error arith
    bitvec/      bitvec bitvec_nat bitvec_bytes byte
    algebra/     algebra algebra_rel semiring ordered_field order
    analysis/    real_fn (functions on an ordered field and their derivatives)
    relation/    relation relation_props relation_function
    data/        list vector bounded_list tree certified_lookup
      set/       finite_set list_setoid list_finite_set tree_finite_set
                 tree_list_set_transfer
    text/        char string utf8 decimal
    parser/      parser (the facade, moved in) parser_core parser_contracts …
    tactic/      tactic omega ring bitvec_omega relation_context
    itree/       itree itree_trace itree_sim itree_state coitree coitree_eutt
                 coitree_bridge coitree_rec
    machine/     memory location
    arch/
      x86_64/    unchanged (24 modules)
    os/
      linux/     linux_calls linux_trees linux_trees_sim linux_x86_64_*  (10)
                 elf64 elf64_load elf64_calls
  native/                      the compiler proved in Heather (heather-in-heather)
    function_ir/ function_ir function_ir_eval function_ir_loop* function_ir_lower*
                 function_ir_x86* function_ir_certificates
    native_source stream_filter stream_filter_spec filter_step_piece
  certgen/       certgen_cert certgen_code ir_v1
  lang/          list_algos subtype subtype_code vec_code
    lexer/       lexer_scan lexer_tokens     Heather's own scanner (linked: crates/linked)
```

Reasons for the less obvious placements:

- **`ring` and `omega` go in `tactic/`, not in `algebra/` or `num/`.**
  `ring.hthr` is the kit of the reflective ring normaliser, and `omega.hthr` is
  the certificate algebra the Rust Omega searcher's proofs are checked against.
  Both serve a tactic, so neither is a theory of a type. The algebraic theory
  of rings is `algebra/semiring.hthr`. `bitvec_omega` (the facts `bv_omega`
  builds) and `relation_context` (the certificates for the relational-context
  generator) are kits too. This matches the roadmap's Tactics lane, which lists
  exactly those elaborator files (`docs/roadmap.md`, Parallel lanes).
- **`order` goes in `algebra/`.** It holds order *structures* (`Preorder`,
  `PartialOrder`, `LinearOrder` over a relation, and their products and pullbacks), and it sits beneath `ordered_field`.
  `relation/` keeps the relation calculus itself.
- **`decimal` goes in `text/`.** It is how `%d` prints a count, as bytes. It is
  a formatting spec, not a number type.
- **`memory` and `location` go in `machine/`.** These are the
  architecture-neutral machine models. `arch/` keeps its own README's rule:
  what is specific to an architecture goes under `arch/<name>/`, and what is
  shared between architectures sits beside it.
- **`parser.hthr` moves into `parser/`.** It was kept at the top so that
  `check lib/std` would reach the components. A recursive check (phase 0)
  does that anyway, and the facade-plus-components pattern works the same from
  inside the folder.
- **`tree` goes in `data/`, next to `list`.** `tree_finite_set` and the
  transfer go in `data/set/` with the other finite-set backends, and
  `finite_set` there is their interface.

### 3.1 How the parallel lanes map onto folders

Folders also make the roadmap's lane footprints readable as directories.
Native code becomes `lib/native/`, `lib/std/arch/` and `lib/std/os/`.
Tactics becomes `lib/std/tactic/`. Interaction trees becomes `lib/std/itree/`.
Mathematics becomes `lib/std/{num,algebra,relation}/`. After the move, the
Parallel lanes table can say that instead of "`lib/std/*.hthr` other than the
above".

## 4. Placement rules (for `docs/language/modules-design.md` and future modules)

1. **A module's folder is chosen by its subject: the type or theory it is
   about.** This is the folder version of the existing rule that facts live
   in their type's file. A lemma about `Nat` goes in `num/nat.hthr`, even if
   only `float/round` uses it, and a folder never becomes the place to park
   a client's helper.
2. **A tactic's kit lives in `tactic/`.** A kit is the checker or certificate
   algebra that a tactic emits proofs against. An ordinary fact that a kit
   needs still lives with its type (rule 1). `int` cannot import `omega`
   today, and a folder changes nothing about that.
3. **Stems stay globally unique. A family prefix is needed only when the stem
   would be generic on its own.** `x86_64_fetch` keeps its prefix. A new
   module called `error` or `core` would collide with something sooner or
   later. The loader reports a collision loudly (two hits in one tier), so this
   rule is about keeping names readable, not about safety.
4. **Folder names are short, lowercase, singular identifiers** (`num`,
   `tactic`, `itree`). If compound module paths ever arrive (they would be
   parser-only, `docs/language/modules-design.md` §2), the folders would become their
   segments, so the names should be ones we would accept as `std::num::rat`.
   Nothing here commits to that.
5. **No facade per folder.** `export` takes an explicit, non-empty list and has
   no whole-module form, so a `num.hthr` reexporting four modules would be a
   long list for little gain. `import rat;` already works from anywhere. The
   parser stays the one facade, because it has a real public/private split.
6. **`lib/std` is what programs import.** Anything that proves the compiler
   (`function_ir*`, certgen) or tests a language feature stays outside it,
   with the default lint profile.

## 5. Choices (settled 2026-10-23)

Minus took 1 and 2 as recommended and left 3 as it is. He would like the
float modules namespaced better somehow, but there is no design for that yet.


1. **Should the Linux and ELF model go in `lib/std/os/linux/` (recommended),
   or in `lib/native/`?** The S1 spec (`linux_calls`, `linux_trees`, `Sim`) and
   the process image are models a verified program is stated against, in the
   same way that `arch/x86_64` is, and none of the 13 files imports a compiler
   module. Moving them into `std` puts them under the Stdlib lint profile. I
   checked them for `-> <-> |- fun` spellings and found none, so no new lints
   appear. Their image keys change once (the profile is in the key).
2. **Should `bitvec/` stay a top-level folder (recommended) or move to
   `num/bitvec/`?** Words are numbers modulo 2ⁿ, but nearly every importer is
   machine code. It is also the folder that exists already.
3. **Should the generic stems in `float/` be renamed (`round` → `float_round`,
   `error` → `float_error`, `arith` → `float_arith`)?** Rule 3 suggests it.
   Unlike the move, this does change `import` lines and qualified names
   (`round::…` becomes `float_round::…`, and so do the exported names), so it
   would be its own small PR. Not recommended now, because nothing collides yet.

## 6. Migration plan

**Phase 0: tooling, one small PR, before anything moves.**

- *A directory argument is checked recursively.* `heather check lib/std` takes
  every `.hthr` at or below the folder as a root, skipping dot-folders, which
  is the same set the loader's lower tier already treats as one flat
  namespace. The reason given for keeping it non-recursive ("recursing would
  silently merge unrelated module namespaces", `roots_for_path`) no longer
  holds, because the loader merges them for lookup already and refuses
  duplicates. `library_wide.rs` walks recursively too. Both now cover
  `float/*` and `arch/x86_64/*`. The whole-library check gets correspondingly
  longer. The wide export sweep's refusal counts move, which tells us how
  float and x86 export. `scripts/test` does not run `check lib/std` as a gate
  (`timings.rs` kills it early on purpose), so the suite's cost does not change.
- *The CLI's default search path becomes `lib/std` then `lib`*, the same as
  the native builder and the LSP. In the prototype, with `-L lib/std` alone,
  four modules in `lib/native/` fail to resolve when checked on their own
  (`native_source` cannot see `function_ir/`). Today they work only because
  every file in `lib/` is a sibling. With both folders searched, all 120
  modules resolve, alone and together. The lint profile keeps keying on
  `lib/std` alone, so `lib/native` stays at the default profile.
- *`scripts/lib-paths` (`--check`, `--fix`).* It finds every `lib/…/<stem>.hthr`
  path that no longer exists, in tracked Rust, docs, issues and scripts, and
  rewrites it to the stem's one file under `lib/`. It skips `probes/`,
  `perf/snapshots/` and citations of deleted modules. The prototype is about
  60 lines of Python. `--check` could join the `scripts/test` preamble so that
  dead doc links show up as they appear. Whether to do that is optional.

**Phase 1: the move, one PR in two commits.**

1. `git mv` only, so that the rename commit has pure renames and `git log
   --follow` and blame carry through.
2. `scripts/lib-paths --fix` and the README touch-ups (`arch/README.md`,
   `parser/README.md`, which still says "supply `-L lib/std/parser`", stale
   since the lower tier landed), the roadmap's lanes table, and the
   modules-design note on placement (§4).

Then the plain full `scripts/test`, because the change touches `lib/`.

**In-flight branches.** Rebasing over the move keeps their edits to moved
files (git follows the renames). A test they *added* still points at the old
path and fails to build, so the rule is the same as after the formatter
change: rebase, then run `scripts/lib-paths --fix`. GitHub has no open PRs
right now, so the move costs least if it lands before the next parallel batch
starts.

**Not in this plan:** renaming test files (`lib_std_rat.rs` does not need to
say where `rat` lives), the float stems (§5.3), and a shared table of
`include_str!` sources for the tests. That table would make the next move a
one-file change, but 122 test files would have to switch to it. It is worth
an issue, not this PR.

## 7. Costs

Measured on the prototype unless marked as expected:

- **Sources:** 87 files moved (the 33 already in `arch/x86_64/`, `parser/`
  and `bitvec/` stayed where they were). No `import` or code line changed. The
  landed move also rewrote the comments in 11 sources that cite other files
  by path, so those modules' images re-key. `logic` is one of them, so the
  first check after the move is cold.
- **Path rewrites:** 2081 changed lines across 628 files, besides the renames,
  all mechanical (Rust 1168, issues 595, docs 409, scripts 17, other 3).
- **Build:** `cargo test --workspace --no-run` passes on the prototype. A
  stale `include_str!` is a compile error, so that means every Rust path
  resolved. The suite itself was not run; phase 1 runs the full suite.
- **Cache (expected):** no image is invalidated by its path. Two things do
  cost one cold rebuild. First, the 13 Linux/ELF modules change lint profile,
  if they go into `std` (§5.1). Second, the root order of a directory check
  changes, because roots are sorted by path and the current image format needs
  the exact Ψ prefix.
- **Perf diary (expected):** `scripts/perf` keys its snapshot rows by file
  path, so rows from before the move do not line up with rows after it. The
  corpus paths in `scripts/perf` are rewritten, and the report needs an
  old-path→new-path alias (or it can key on the stem) so that history stays
  comparable. The newest snapshot is from 2026-09-27, so little is lost either
  way.
- **Exporter:** none. Module-qualified names (`rat::add_comm`) and the
  per-module Lean files are named by stem.
- **Editor:** none. The LSP already searches `lib/std` and `lib`, and the Zed
  README's paths stay valid.
