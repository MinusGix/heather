# Command-line reference

## Check

```text
heather check [options] <file-or-directory>...
```

A directory checks its immediate `.hthr` files as one deduplicated import
closure. Important options:

| Option | Meaning |
|---|---|
| `-L <dir>` | Add a module search directory; repeatable |
| `--cache` | Read and write accepted declaration cache entries |
| `--cache-dir <dir>` | Select the cache directory and enable caching |
| `--accept-stale-images` | Kernel-recheck semantic images from another compiler build |
| `--only a,b` | With cache, elaborate and gate only named declarations |
| `--deny-axioms` | Fail when proved/computing declarations reach a user axiom |
| `--review` | Enable additional review-mode lints |
| `--timings <file.tsv>` | Write per-declaration and run attribution |
| `--kernel-workers <n>` | Set proof-checking worker count |

Exit status is 0 for success, 1 for source diagnostics, and 2 for invocation
or loading failures.

## Inspect obligations and axioms

```text
heather obligations [check options] [--json] <file.hthr>...
heather axioms <target> [check options] [--json] <file-or-directory>...
```

`obligations` reports representation/implementation obligations.
`axioms` reports the explicit axiom provenance of a target declaration.

## Format

```text
heather fmt [--check] <file-or-directory>...
```

`--check` reports non-canonical files without rewriting them.

## Native x86-64 output

```text
heather compile-x86 <file.hthr> <function> -o <output.s> [options]
heather build-x86 <file.hthr> <function> --arg <u64> --arg <u64> \
    -o <executable> [options]
```

These commands export a supported checked function through the certified x86
pipeline. See `examples/x86-native/README.md` for the supported source subset,
callee options, and proof boundary.

## Build this book

With `mdbook` installed:

```console
$ mdbook build
$ mdbook serve --open
```

The generated site is written to `target/book`.
