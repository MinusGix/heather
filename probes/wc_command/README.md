# wc as a command: probes

Probes for `docs/native-wc-command-design.md` §10.1. Not part of the build or
the suite.

- `digit_emit.hthr` (V5): one digit of the `%*d` formatter's `emit` loop at
  an open place value. Reproduce its cost beside the write loop's:

  ```
  (ulimit -v 8388608 -t 1800 -c 0; HEATHER_KERNEL_WORKERS=1 target/release/heather check \
     -L lib -L lib/std -L lib/std/arch/x86_64 --kernel-workers 1 --timings /tmp/v5.tsv \
     probes/wc_command/digit_emit.hthr lib/elf64_write_loop.hthr)
  ```

  then sum `total_ns` by module (`scripts/timings /tmp/v5.tsv digit_emit::`).

V4 is not a probe file: it is the change to `eof_run` in
`lib/elf64_read_pieces.hthr`, measured by an A/B cold `build-x86` of
`examples/x86-native/wc.hthr`. The library sources are compiled into the
`heather` binary, so each side needs its own build.
