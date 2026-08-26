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
    model.hthr       decoded register instructions and typed execution
```

The public Heather module name is currently chosen by the loader (`x86_64` in
the integration test), independently of the source file's repository path.
