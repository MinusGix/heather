# Architecture library layout

Architecture-specific machine descriptions live below `arch/<architecture>/`.
Each architecture may split typed instructions, decoding, execution, ABI, and
encoding into separate modules as those surfaces grow. Code shared by several
architectures belongs directly under `arch/`; code that is broadly useful
beyond machine models remains in `std/`.

The initial layout is:

```text
arch/
  x86_64/
    x86_64.hthr      decoded register instructions and typed execution
    x86_64_*.hthr    blocks, fetch, calls, stores, … over that model
```

Module names are flat file stems (docs/modules-design.md §3.2), so each
module carries its architecture in its name: `x86_64_fetch.hthr` is the
module `x86_64_fetch` for the CLI, the editor and the native builder alike.
The loader finds it below `lib/std` without a `-L` of its own.
