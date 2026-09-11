//! The deferred kernel gate (`docs/parallel-kernel-gate-design.md`,
//! `issues/parallel-kernel-gate.md`).
//!
//! Each test pins one half of the contract: a module whose proofs are checked
//! off-thread still accepts exactly what the serial gate accepted, still
//! refuses exactly what it refused, refuses it *before* anything downstream
//! can publish, vouches for exactly the prefix the serial gate vouched for,
//! and still attributes the kernel's time to the declaration that spent it.
//!
//! The default — one worker — is not tested here on purpose: it is the code
//! path the whole rest of the suite already runs.

use std::cell::RefCell;
use std::sync::Arc as Rc;

use heather_elab::gate::{GateItem, KernelGate};
use heather_elab::stats::{self, ScopeKind};
use heather_elab::{ElabError, Elaborator, ModuleDependencyIdentity};
use heather_kernel::term::GlobalCtx;

/// Six independent theorems: nothing here depends on another's proof, which is
/// the shape the certificate workload has.
const INDEPENDENT: &str = r#"
fn id_nat(n: Nat) -> Nat { n }

theorem one_one(): id_nat(1) = 1 { refl }
theorem two_two(): id_nat(2) = 2 { refl }
theorem three_three(): id_nat(3) = 3 { refl }
theorem four_four(): id_nat(4) = 4 { refl }
theorem five_five(): id_nat(5) = 5 { refl }
theorem six_six(): id_nat(6) = 6 { refl }
"#;

/// The same, with a declaration the **kernel** refuses in the middle:
/// `n = Succ(n)` is well-formed on both sides and genuinely not convertible,
/// so the gate is what rejects it (the fixture `check_diagnostics.rs` uses).
const LATE_FAILURE: &str = r#"
fn id_nat(n: Nat) -> Nat { n }

theorem one_one(): id_nat(1) = 1 { refl }
theorem two_two(): id_nat(2) = 2 { refl }
theorem broken(n: Nat): n = Succ(n) { refl }
theorem five_five(): id_nat(5) = 5 { refl }
theorem six_six(): id_nat(6) = 6 { refl }
"#;

fn with_workers(n: usize) -> Elaborator {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    elab.set_kernel_workers(n);
    assert_eq!(elab.kernel_workers(), n);
    elab
}

#[test]
fn four_workers_accept_independent_theorems() {
    let mut elab = with_workers(4);
    let errors = elab.check_module_source("pool", INDEPENDENT);
    assert!(errors.is_empty(), "{errors:?}");
    // Every binding landed: a deferred proof still commits its declaration,
    // and a later module can name it.
    let later = elab.check_module_source(
        "pool",
        "theorem uses(): id_nat(1) = 1 { one_one }\n",
    );
    assert!(later.is_empty(), "{later:?}");
}

/// The join is what a caller's publication sits behind. `check_module_delta`
/// is the function the semantic session, the module image and the declaration
/// cache all run inside, so a proof that fails after its declaration committed
/// must make *it* return `Err` — no delta, nothing to publish, nothing written.
#[test]
fn a_late_failure_rejects_the_module_before_anything_is_published() {
    let mut elab = with_workers(4);
    let deps = ModuleDependencyIdentity::new(Vec::new());
    let delta = elab.check_module_delta("pool_bad", LATE_FAILURE, deps);
    let errors = delta.err().expect("a module with a refused proof yields no delta");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ElabError::Kernel { decl, .. } if decl == "broken")),
        "the failing declaration is named: {errors:?}",
    );
}

/// The same module, checked twice at different widths, must reach the same
/// verdict: the width is a scheduling decision and never a semantic one.
#[test]
fn every_width_reaches_the_same_verdict() {
    for workers in [1usize, 2, 4, 8] {
        let mut good = with_workers(workers);
        assert!(
            good.check_module_source("same", INDEPENDENT).is_empty(),
            "width {workers} refused a good module",
        );
        let mut bad = with_workers(workers);
        let errors = bad.check_module_source("same", LATE_FAILURE);
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ElabError::Kernel { decl, .. } if decl == "broken")),
            "width {workers} accepted a refused proof: {errors:?}",
        );
    }
}

/// A gate that vouches for nothing and records what the kernel passed, in the
/// order it was told. This is the cache's seam (`crates/cache/src/lib.rs`), and
/// what it must never do is record a verdict for a proof still in flight.
#[derive(Default)]
struct Recorder {
    accepted: RefCell<Vec<String>>,
}

impl KernelGate for Recorder {
    fn admits(&self, _psi: &GlobalCtx, _item: &GateItem<'_>) -> bool {
        false
    }
    fn accepted(&self, _psi: &GlobalCtx, item: &GateItem<'_>) {
        self.accepted.borrow_mut().push(item.name.to_string());
    }
}

/// Two properties at once: a verdict is recorded only after the deferred check
/// passes, and a failing module vouches for exactly the prefix the serial gate
/// vouched for — everything before the first failure, nothing after it.
#[test]
fn a_verdict_is_recorded_only_for_the_prefix_before_the_failure() {
    let recorder = Rc::new(Recorder::default());
    let mut elab = with_workers(4);
    elab.set_gate(Rc::clone(&recorder) as Rc<dyn KernelGate>);
    let errors = elab.check_module_source("pool_prefix", LATE_FAILURE);
    assert!(!errors.is_empty(), "the fixture must fail");

    let accepted = recorder.accepted.borrow().clone();
    assert!(accepted.contains(&"one_one".to_string()), "{accepted:?}");
    assert!(accepted.contains(&"two_two".to_string()), "{accepted:?}");
    assert!(!accepted.contains(&"broken".to_string()), "a refused proof is never vouched for");
    // Declaration order, and nothing past the failure.
    let one = accepted.iter().position(|n| n == "one_one").expect("one_one");
    let two = accepted.iter().position(|n| n == "two_two").expect("two_two");
    assert!(one < two, "verdicts are replayed in declaration order: {accepted:?}");
    assert!(
        !accepted.contains(&"five_five".to_string())
            && !accepted.contains(&"six_six".to_string()),
        "nothing after the first failure is vouched for: {accepted:?}",
    );
}

/// A good module's verdicts still arrive for every declaration, in declaration
/// order.
#[test]
fn a_good_module_vouches_for_everything_in_order() {
    let recorder = Rc::new(Recorder::default());
    let mut elab = with_workers(4);
    elab.set_gate(Rc::clone(&recorder) as Rc<dyn KernelGate>);
    assert!(elab.check_module_source("pool_all", INDEPENDENT).is_empty());
    let accepted = recorder.accepted.borrow().clone();
    let expect = ["one_one", "two_two", "three_three", "four_four", "five_five", "six_six"];
    let positions: Vec<usize> = expect
        .iter()
        .map(|n| accepted.iter().position(|a| a == n).unwrap_or_else(|| panic!("{n}: {accepted:?}")))
        .collect();
    assert!(positions.windows(2).all(|w| w[0] < w[1]), "declaration order: {accepted:?}");
}

/// Attribution survives the trip off-thread: a worker's `check_term` time and
/// the kernel counters it moved are folded back into the declaration's own row
/// at join time (`docs/parallel-kernel-gate-design.md` §7), so `--timings`
/// still reads `kernel_gate_ns` per item.
#[test]
fn a_worker_s_time_folds_back_into_its_declaration_s_row() {
    let mut elab = with_workers(4);
    elab.enable_item_timings();
    {
        let _module = stats::scope(ScopeKind::Module, "folded", "");
        let errors = elab.check_module_source("folded", INDEPENDENT);
        assert!(errors.is_empty(), "{errors:?}");
    }
    let rows = stats::take_rows();
    stats::disable();

    let items: Vec<_> = rows.iter().filter(|r| r.kind == ScopeKind::Item).collect();
    assert!(items.len() >= 7, "one row per declaration: {items:?}");
    const THEOREMS: [&str; 6] =
        ["one_one", "two_two", "three_three", "four_four", "five_five", "six_six"];
    let theorems: Vec<_> =
        items.iter().filter(|r| THEOREMS.contains(&r.item.as_str())).collect();
    assert!(!theorems.is_empty());
    assert!(
        theorems.iter().all(|r| r.kernel_ns > 0),
        "every deferred theorem's kernel time comes home: {:?}",
        theorems.iter().map(|r| (&r.item, r.kernel_ns)).collect::<Vec<_>>(),
    );
    assert!(
        theorems.iter().all(|r| r.kernel_ns <= r.total_ns),
        "and the row still contains it",
    );
    assert!(
        theorems.iter().any(|r| r.kernel.eval_steps > 0),
        "the worker's kernel counters come home with its clock",
    );
    let module_row = rows.iter().find(|r| r.kind == ScopeKind::Module).expect("a module row");
    assert!(
        module_row.kernel_ns >= items.iter().map(|r| r.kernel_ns).max().unwrap_or(0),
        "a still-open enclosing scope accounts for work done off-thread",
    );
}

/// `HEATHER_KERNEL_WORKERS` names the width when no flag does, by this rule.
/// Parsed permissively on purpose: instrumentation must never be why a check
/// fails. (The variable itself is exercised end-to-end in
/// `crates/cli/tests/kernel_workers.rs`, where a subprocess can carry one
/// without a test binary mutating its own environment.)
#[test]
fn the_environment_s_width_is_a_positive_decimal_or_nothing() {
    assert_eq!(heather_elab::kernel_workers_from_spec("3"), Some(3));
    assert_eq!(heather_elab::kernel_workers_from_spec(" 8 "), Some(8));
    assert_eq!(heather_elab::kernel_workers_from_spec("0"), None, "zero is not a width");
    assert_eq!(heather_elab::kernel_workers_from_spec("lots"), None, "nonsense is ignored");
    assert_eq!(heather_elab::kernel_workers_from_spec(""), None);
    assert_eq!(heather_elab::kernel_workers_from_spec("-2"), None);
}
