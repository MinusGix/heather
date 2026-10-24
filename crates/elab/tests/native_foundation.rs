use crate::read_loop_fixture::checker_with;

// What the native rebuild stands on once the hand-proved process stack is
// gone (docs/native-program-logic-design.md §3.1, §3.3): the label assembler,
// the stream filter's spec and its step piece, and the decimal spec salvaged
// from the burned formatters. No program imports them until the compiler
// does, so this is what keeps them checking.
#[test]
fn the_kept_foundation_checks() {
    checker_with(&[
        ("x86_64_stack", include_str!("../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
        ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
        ("stream_filter", include_str!("../../../lib/native/stream_filter.hthr")),
        ("decimal", include_str!("../../../lib/std/text/decimal.hthr")),
    ]);
}
