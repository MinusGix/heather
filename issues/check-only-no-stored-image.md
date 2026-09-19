---
title: check --only refuses on every module: no stored image found, immediately after the --cache run it asks for
status: open
labels: [tooling,cli,cache,regression]
created: 2026-09-18
updated: 2026-09-18
---

`check --cache --only <item>` refuses on every module tried on the 3d10b94 tree,
always with the same line, and always immediately after a plain
`heather check --cache` on the very file it names:

```text
error: --only: no stored image of module `string` over these dependencies to
replay the prefix from; run `heather check --cache` on the file once first
```

Three repros, each preceded by the `--cache` run the message asks for:

```sh
target/release/heather check --cache -L lib/std lib/std/string.hthr
target/release/heather check --cache --only string_eq_dec -L lib/std lib/std/string.hthr

target/release/heather check --cache -L lib/std -L lib/std/parser docs/showcase/calc_parser.hthr
target/release/heather check --cache --only checked_expr -L lib/std -L lib/std/parser docs/showcase/calc_parser.hthr

# and with the file reachable through -L, the way docs/showcase/README.md invokes it
target/release/heather check --cache --only checked_expr -L lib/std -L lib/std/parser -L /tmp/calc /tmp/calc/calc_text.hthr
```

The seeding runs succeed and report replaying 20–21 semantic modules, so images
exist in `target/decl-cache`; `load_previous` is not finding the root module's.
Note the third form rules out "the root file must be reachable through `-L`",
and the first rules out anything showcase-specific.

`docs/check-only-design.md` records this working on exactly these targets — its
own table has `--only close_body` on `calc_parser` at 7.0 s against 48 s for the
full file, with the counts matching the full run — so this is a regression
against a landed and measured feature, not a misuse.

## Why it matters now

`CLAUDE.md` prescribes `--cache --only <item> --timings f.tsv` as *the* way to
probe one declaration, and the probe loop it cites (13 s instead of 48 s) is
unavailable. Measured on this tree, a **theorem-only** edit to
`docs/showcase/calc_text.hthr` costs **95 s** to recheck, unloaded — and a
grammar-level edit costs 96 s, i.e. the edit's size does not matter, because the
floor is re-elaborating the module. That floor is the inner loop for the
language-quality work [[sequence-parser-source]] is now a target for, so this is
the difference between a ~13 s and a ~95 s iteration.
