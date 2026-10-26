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
//! Two walks are probed. `stack/check-numeral` is the checking walk of
//! [[numeral-stack-depth]]. `stack/eval-nested-scrutinee` is the evaluator's
//! value-nested chain of [[eval-native-frame-size]]: the one recursion the
//! depth budget (`reduce::NATIVE_DEPTH_LIMIT`) counts, so its bytes per
//! level times that bound is the stack a budgeted run can stand on
//! (docs/native-depth-budget-design.md §8).
//!
//! The number is a property of the *code and the compiler*, not of the
//! machine: frame sizes come out of codegen. So unlike times, it is
//! comparable across machines with the same toolchain and profile, and the
//! baseline gates it whenever the recorded `rustc` matches.

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::Arc as Rc;

use heather_kernel::eval::Eval;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{Defs, NATIVE_DEPTH_LIMIT};
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::check_term;
use heather_kernel::value::{Env, Val, ValueArena};

use crate::fixtures::terms::{nat_ctx, num, rt, rty, v};
use crate::fixtures::FUEL;

/// What a probe child runs.
#[derive(Clone, Copy)]
pub enum Kind {
    /// One walk of `check_term` over `Succ^n Zero`, which is the shallowest
    /// interesting recursion in the kernel: depth is exactly `n`, so the
    /// frame size is the quotient and nothing else.
    CheckNumeral,
    /// One evaluation of `f(f(… f(1)))`, `n` deep, for
    /// `f = λx. elim_Nat(_. Nat; ze; a b. b; x)`. Each scrutinee is a
    /// variable standing for the argument's thunk, so forcing it re-enters
    /// `Eval::drive` while the enclosing drive is still in its loop: one
    /// counted level per `f`, from syntax of fixed depth (the shape of
    /// `eval_differential.rs`'s `nested_scrutinee_value`).
    EvalNestedScrutinee,
}

impl Kind {
    pub const ALL: [Kind; 2] = [Kind::CheckNumeral, Kind::EvalNestedScrutinee];

    pub fn name(self) -> &'static str {
        match self {
            Kind::CheckNumeral => "stack/check-numeral",
            Kind::EvalNestedScrutinee => "stack/eval-nested-scrutinee",
        }
    }

    /// What one level is, for the report.
    pub fn level(self) -> &'static str {
        match self {
            Kind::CheckNumeral => "deepest numeral that checks",
            Kind::EvalNestedScrutinee => "deepest nested scrutinee that evaluates",
        }
    }

    fn parse(s: &str) -> Option<Kind> {
        Kind::ALL.into_iter().find(|k| k.name() == s)
    }

    /// The stack a probe child gives the walk. Small enough that bisection
    /// is quick and the quotient is fine-grained; large enough that the
    /// fixed cost of getting into the walk is a rounding error on the
    /// result. The evaluator's is smaller because the depth budget refuses
    /// past `NATIVE_DEPTH_LIMIT` levels, and the probe must run out of
    /// stack before it runs out of budget to measure anything.
    fn stack_bytes(self) -> usize {
        match self {
            Kind::CheckNumeral => 4 << 20,
            Kind::EvalNestedScrutinee => 512 << 10,
        }
    }

    /// Bisection ceiling. For the checking walk it keeps a fix that got
    /// frames down to a few hundred bytes from turning into a minutes-long
    /// search; for the evaluator it is the budget, past which a run is
    /// refused rather than measured.
    fn max_levels(self) -> u64 {
        match self {
            Kind::CheckNumeral => 1 << 14,
            Kind::EvalNestedScrutinee => u64::from(NATIVE_DEPTH_LIMIT) - 1,
        }
    }
}

pub struct Probe {
    pub name: &'static str,
    pub level: &'static str,
    pub stack_bytes: u64,
    /// Deepest instance that runs within `stack_bytes`.
    pub max_levels: u64,
}

impl Probe {
    pub fn bytes_per_level(&self) -> f64 {
        self.stack_bytes as f64 / self.max_levels.max(1) as f64
    }
}

fn nested_scrutinee(levels: u64) -> Rc<Term> {
    let drain = rt(Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        body: rt(Term::ElimNat {
            level: Level::Zero,
            motive: rty(Type::Nat),
            base: rt(Term::Zero),
            step: rt(v(0)),
            scrut: rt(v(0)),
        }),
    });
    let mut t = rt(num(1));
    for _ in 0..levels {
        t = rt(Term::App {
            fun: Rc::clone(&drain),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::Nat),
            cod: rty(Type::Nat),
            arg: t,
        });
    }
    t
}

/// The work being probed, run by the child on a thread of known stack size.
pub fn child_main(kind: &str, stack_bytes: usize, levels: u64) -> i32 {
    let kind = Kind::parse(kind).expect("stack probe kind");
    let handle = match kind {
        Kind::CheckNumeral => std::thread::Builder::new().stack_size(stack_bytes).spawn(move || {
            let gamma = nat_ctx(1);
            let t = num(levels);
            check_term(&GlobalCtx::default(), 0, Layer::Prog, &gamma, &t, &Type::Nat, &Level::Zero, FUEL)
                .is_ok()
        }),
        // The term is built before the thread starts and never dropped, so
        // neither its construction nor its drop is what is measured.
        Kind::EvalNestedScrutinee => {
            let t = nested_scrutinee(levels);
            std::thread::Builder::new().stack_size(stack_bytes).spawn(move || {
                let arena = ValueArena::new();
                let mut ev = Eval::new(FUEL, Defs::opaque(), LocalCtx::nil().base, &arena);
                let ok = matches!(ev.eval_tm(&t, &Env::empty()).as_deref(), Ok(Val::Zero));
                std::mem::forget(t);
                ok
            })
        }
    }
    .expect("probe thread");
    match handle.join() {
        Ok(true) => 0,
        // Well-typed input that fails to answer is a fixture bug (or, for the
        // evaluator, the depth budget binding first), and must not be
        // reported as a stack limit.
        Ok(false) => 3,
        Err(_) => 4,
    }
}

fn child_survives(exe: &PathBuf, kind: Kind, levels: u64) -> bool {
    let status = Command::new(exe)
        .arg("--stack-child")
        .arg(kind.name())
        .arg(kind.stack_bytes().to_string())
        .arg(levels.to_string())
        // The overflow message ("thread … has overflowed its stack") is the
        // expected outcome of half these runs, not news.
        .stderr(Stdio::null())
        .stdout(Stdio::null())
        .status()
        .expect("re-exec self for the stack probe");
    match status.code() {
        Some(0) => true,
        Some(3) => panic!("stack probe {}: the fixture stopped answering", kind.name()),
        // Any other code, or death by signal (the overflow case): too deep.
        _ => false,
    }
}

/// Deepest instance of `kind` that runs in its probe stack, by doubling
/// then bisecting.
pub fn probe(kind: Kind) -> Probe {
    let exe = std::env::current_exe().expect("current_exe for the stack probe");
    let cap = kind.max_levels();
    let found = |max_levels| Probe {
        name: kind.name(),
        level: kind.level(),
        stack_bytes: kind.stack_bytes() as u64,
        max_levels,
    };
    assert!(child_survives(&exe, kind, 1), "one level of {} does not fit", kind.name());

    // Double until it breaks: `lo` always fits, `hi` never does.
    let mut lo = 1u64;
    let mut hi = 2u64;
    while hi <= cap && child_survives(&exe, kind, hi) {
        lo = hi;
        hi *= 2;
    }
    if hi > cap {
        if child_survives(&exe, kind, cap) {
            // Frames got small enough that the cap binds first. Report the
            // cap; the bytes/level figure is then an upper bound, which is
            // the good direction to be wrong in.
            return found(cap);
        }
        hi = cap;
    }
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if child_survives(&exe, kind, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    found(lo)
}

/// Every probe, in [`Kind::ALL`] order.
pub fn probes() -> Vec<Probe> {
    Kind::ALL.into_iter().map(probe).collect()
}
