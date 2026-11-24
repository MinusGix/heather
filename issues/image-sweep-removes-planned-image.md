---
title: A store sweep can remove an image another run has planned to replay, which then fails instead of rebuilding
status: closed
labels: [tooling,infrastructure,cache]
area: infrastructure
created: 2026-11-11
updated: 2026-11-24
---

A run that has planned to replay a module from the image store fails if
another process's sweep removes that image before it is read:

```
error: module `yes_args_tool_elf_certificate` could not be placed in its world: the image of `mono_laws` is gone from the store
```

Seen once, 2026-11-11, in `crates/cli/tests/native_tools.rs`
(`compiled_yes_takes_its_line_as_gnu_yes`) under `scripts/test --pr`,
right after a merge of master that changed `lib/std/data/list.hthr` and
so re-imaged the whole library. `target/cli-check-images` was at its
4 GiB budget (`DEFAULT_RETAIN_BYTES`, `crates/cache/src/module_image.rs`),
so every publish swept, and the test binary's `write-elf` children share
that store. The same test passed alone afterwards.

The sweep's own comment says an image it removes "may be one another
process was about to load: both outcomes are an ordinary cache miss, which
the reader already handles by rebuilding". That holds where a module is
planned and loaded in one step. It does not hold in
`SemanticSession::canonical_delta` (`crates/cli/src/semantic.rs`): a module already
planned as a replay, whose delta was not held, is decoded from the store
when a later module's world is built, and `Ok(None)` there is the error
above, not a rebuild.

Options: have `canonical_delta` fall back to elaborating the module (it
has the source); or have a planner keep what it planned on alive (hold the
delta, or touch the image so the oldest-first sweep passes it by); or
exempt images younger than the running processes from a sweep.

Until then a red `native_tools` with this message on a store at its
budget is this race: rerun the test.

## Log

- 2026-11-11: Seen again on a suite run over a store past its budget (`target/cli-check-images` at 4.5 GiB of 4 GiB): `compiled_yes_takes_its_line_as_gnu_yes` failed with "the image of `char` is gone from the store", and a rerun of `native_tools` alone failed the same way, so on such a store a rerun does not help. Deleting images older than a day (`find target/cli-check-images -name '*.hmi' -mmin +1440 -delete`, 2.2 GiB left) and rerunning passed, 19 of 19. Until one of the options above is taken, that trim is the workaround, not a rerun.
- 2026-11-12: Seen again 2026-11-12 on PR #551, and this time it repeats: `compiled_yes_takes_its_line_as_gnu_yes` failed under `scripts/test --pr` with "the image of `char` is gone from the store", failed again with the same message when `native_tools` was run on its own (its twenty tests share the store), and passed run alone. `target/cli-check-images` was 5.2 GiB on disk against the 4 GiB budget, after a day of rounds that each re-imaged the library, so every publish swept and `char`, an image nothing had rewritten, was among the oldest. So a store at its budget stays there and the race stops being rare: until the loader rebuilds on a miss, the remedy for a red with this message is to clear `target/cli-check-images` and not only to rerun.
- 2026-11-24: 2026-11-24: a sibling failure in moving an image over another dependency world is [[image-move-fails-under-concurrent-rewrite]].
