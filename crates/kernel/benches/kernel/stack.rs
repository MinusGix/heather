//! Stack cost, measured by subprocess bisection.
//!
//! Time is not the only cost model the kernel has: it also spends stack, one
//! frame per level of a recursive walk, and that is a resource with a hard
//! cliff. [[numeral-stack-depth]] is the live example — ~47 KB of stack per
//! `Succ` level, which caps what the surface can express — and it was found
//! by accident, at the cost of an hour of bisection that looked like a
//! projection loop. This module is that measurement done on purpose.
//!
//! **Why a subprocess.** A stack overflow cannot be caught: the guard page
//! faults and the process dies. So the probe spawns *itself* with
//! `--stack-child`, which runs the walk on a thread of an exactly known
//! stack size; if the child dies, that size was not enough. Bisecting the
//! depth at a fixed stack size yields the maximum workable depth, and the
//! quotient is bytes per level — the number a fix to that issue has to move.
//!
//! The number is a property of the *code and the compiler*, not of the
//! machine: frame sizes come out of codegen. So unlike times, it is
//! comparable across machines with the same toolchain and profile, and the
//! baseline gates it whenever the recorded `rustc` matches.

use std::path::PathBuf;
use std::process::{Command, Stdio};

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, Type};
use heather_kernel::typing::check_term;

use crate::fixtures::terms::{nat_ctx, num};
use crate::fixtures::FUEL;

/// The stack a probe child gives the walk. Small enough that bisection is
/// quick and the quotient is fine-grained; large enough that the fixed cost
/// of getting into `check_term` is a rounding error on the result.
pub const PROBE_STACK: usize = 4 << 20;

/// Bisection ceiling. At ~47 KB/level a 4 MiB stack reaches ~85 levels; a
/// fix that got frames down to a few hundred bytes would reach thousands, and
/// this cap keeps that outcome from turning into a minutes-long search.
const MAX_LEVELS: u64 = 1 << 14;

pub struct Probe {
    pub name: &'static str,
    pub stack_bytes: u64,
    /// Deepest numeral that checks within `stack_bytes`.
    pub max_levels: u64,
}

impl Probe {
    pub fn bytes_per_level(&self) -> f64 {
        self.stack_bytes as f64 / self.max_levels.max(1) as f64
    }
}

/// The work being probed, run by the child on a thread of known stack size.
/// One walk of `check_term` over `Succ^n Zero`, which is the shallowest
/// interesting recursion in the kernel: depth is exactly `n`, so the frame
/// size is the quotient and nothing else.
pub fn child_main(stack_bytes: usize, levels: u64) -> i32 {
    let handle = std::thread::Builder::new()
        .stack_size(stack_bytes)
        .spawn(move || {
            let gamma = nat_ctx(1);
            let t = num(levels);
            check_term(
                &GlobalCtx::default(),
                0,
                Layer::Prog,
                &gamma,
                &t,
                &Type::Nat,
                &Level::Zero,
                FUEL,
            )
            .is_ok()
        })
        .expect("probe thread");
    match handle.join() {
        Ok(true) => 0,
        // Well-typed input that fails to check is a fixture bug, and must not
        // be reported as a stack limit.
        Ok(false) => 3,
        Err(_) => 4,
    }
}

fn child_survives(exe: &PathBuf, stack_bytes: usize, levels: u64) -> bool {
    let status = Command::new(exe)
        .arg("--stack-child")
        .arg(stack_bytes.to_string())
        .arg(levels.to_string())
        // The overflow message ("thread … has overflowed its stack") is the
        // expected outcome of half these runs, not news.
        .stderr(Stdio::null())
        .stdout(Stdio::null())
        .status()
        .expect("re-exec self for the stack probe");
    match status.code() {
        Some(0) => true,
        Some(3) => panic!("stack probe: the numeral fixture stopped checking"),
        // Any other code, or death by signal (the overflow case): too deep.
        _ => false,
    }
}

/// Deepest numeral that checks in `PROBE_STACK`, by doubling then bisecting.
pub fn probe() -> Probe {
    let exe = std::env::current_exe().expect("current_exe for the stack probe");
    assert!(child_survives(&exe, PROBE_STACK, 1), "one Succ level does not fit in 4 MiB");

    // Double until it breaks: `lo` always fits, `hi` never does.
    let mut lo = 1u64;
    let mut hi = 2u64;
    while hi <= MAX_LEVELS && child_survives(&exe, PROBE_STACK, hi) {
        lo = hi;
        hi *= 2;
    }
    if hi > MAX_LEVELS {
        // Frames got small enough that the cap binds first. Report the cap;
        // the bytes/level figure is then an upper bound, which is the good
        // direction to be wrong in.
        return Probe { name: "stack/check-numeral", stack_bytes: PROBE_STACK as u64, max_levels: lo };
    }
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if child_survives(&exe, PROBE_STACK, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    Probe { name: "stack/check-numeral", stack_bytes: PROBE_STACK as u64, max_levels: lo }
}
