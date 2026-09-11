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
///
/// And not only the verdict: a failing module's *diagnostics* and *bindings*
/// are the serial gate's, because the parallel pass that committed `broken`
/// before checking it is discarded whole and replayed serially
/// (`docs/parallel-kernel-gate-design.md` §5.1).
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

    // The serial run, for comparison: same errors, in the same order, and the
    // same set of names registered afterwards.
    let mut serial = with_workers(1);
    let serial_errors = serial
        .check_module_delta("pool_bad", LATE_FAILURE, ModuleDependencyIdentity::new(Vec::new()))
        .err()
        .expect("the serial gate refuses it too");
    assert_eq!(
        errors.iter().map(render).collect::<Vec<_>>(),
        serial_errors.iter().map(render).collect::<Vec<_>>(),
        "the width is a scheduling decision and never a diagnostic one",
    );
    assert_eq!(
        registered(&elab, &["id_nat", "one_one", "two_two", "broken", "five_five", "six_six"]),
        registered(&serial, &["id_nat", "one_one", "two_two", "broken", "five_five", "six_six"]),
        "a refused declaration stays unregistered at every width",
    );
}

fn render(e: &ElabError) -> String {
    format!("{e:?}")
}

/// Which of `names` the elaborator will resolve — the registration count the
/// contract is about, asked through the ordinary name judgment.
fn registered(elab: &Elaborator, names: &[&str]) -> Vec<String> {
    names
        .iter()
        .filter(|n| elab.axiom_report(n).is_ok())
        .map(|n| n.to_string())
        .collect()
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
/// passes, and a failing module records exactly the verdicts the serial gate
/// records — no more, because a discarded parallel pass vouches for nothing at
/// all, and no fewer, because the serial replay is what the cache sees
/// (`docs/parallel-kernel-gate-design.md` §5.1).
#[test]
fn a_failing_module_records_exactly_the_serial_gate_s_verdicts() {
    let recorder = Rc::new(Recorder::default());
    let mut elab = with_workers(4);
    elab.set_gate(Rc::clone(&recorder) as Rc<dyn KernelGate>);
    let errors = elab.check_module_source("pool_prefix", LATE_FAILURE);
    assert!(!errors.is_empty(), "the fixture must fail");

    let serial_recorder = Rc::new(Recorder::default());
    let mut serial = with_workers(1);
    serial.set_gate(Rc::clone(&serial_recorder) as Rc<dyn KernelGate>);
    let serial_errors = serial.check_module_source("pool_prefix", LATE_FAILURE);

    let accepted = recorder.accepted.borrow().clone();
    assert!(!accepted.contains(&"broken".to_string()), "a refused proof is never vouched for");
    assert_eq!(
        accepted,
        *serial_recorder.accepted.borrow(),
        "the same verdicts, in the same order, at any width",
    );
    assert_eq!(
        errors.iter().map(render).collect::<Vec<_>>(),
        serial_errors.iter().map(render).collect::<Vec<_>>(),
    );
}

/// The parallel pass a failure discards leaves the *oracle* untouched too: a
/// gate that is told about a declaration and then never hears the module was
/// abandoned would record a verdict nobody asked it to keep.
#[test]
fn a_discarded_pass_vouches_for_nothing_before_the_replay() {
    let recorder = Rc::new(Recorder::default());
    let mut elab = with_workers(4);
    elab.set_gate(Rc::clone(&recorder) as Rc<dyn KernelGate>);
    assert!(!elab.check_module_source("pool_discard", LATE_FAILURE).is_empty());
    let accepted = recorder.accepted.borrow().clone();
    let mut once = accepted.clone();
    once.sort();
    once.dedup();
    assert_eq!(once.len(), accepted.len(), "no declaration is vouched for twice: {accepted:?}");
}

/// A declaration form that rolls itself back by restoring a whole *clone* of
/// the elaborator — `instance` is the one (`traits.rs`, `elab_instance`) — and
/// that queues a false proof before it fails. The member loop elaborates in
/// order, so `unit_l` is deferred and `nope` is refused after it: the rollback
/// happens with a rejection in flight, which is the case
/// `Elaborator::restore_from_clone` exists for.
const ROLLED_BACK_INSTANCE: &str = r#"
class Monoid<A> {
  unit: A,
  op: A -> A -> A,
  unit_l: (x: A) -> op(unit, x) = x,
}

inductive Z { Z0, Z1 }

instance Monoid<Z> {
  fn unit() -> Z { Z0 }
  fn op(x: Z, y: Z) -> Z { x }
  theorem unit_l(x: Z): op(unit(), x) = x { refl }
  fn nope() -> Z { Z0 }
}

theorem after(): Z::Monoid.op(Z0, Z1) = Z1 { refl }
"#;

/// A rolled-back declaration must not take the *module's* gate down with it.
///
/// The pool is not declaration state: it holds every proof the module has
/// queued, and a clone's pool is inline and empty by construction. Restoring
/// one over the live pool threw away the queued rejection of `unit_l` — so
/// the join saw nothing, the module never took the serial fallback, and the
/// gate ran inline for the rest of the module — which made the module's
/// answer depend on how fast a worker was, the one thing §5.1 forbids. The
/// false proof here is queued and the failing member refused inside *one*
/// item, so no early abort can intervene and the loss is deterministic.
#[test]
fn a_rolled_back_declaration_keeps_the_modules_queued_verdicts() {
    const NAMES: [&str; 4] = ["Z::Monoid", "Z::Monoid::op", "Z::Monoid::unit_l", "after"];
    let mut elab = with_workers(4);
    let errors = elab.check_module_source("pool_rollback", ROLLED_BACK_INSTANCE);
    assert_eq!(
        elab.kernel_workers(),
        4,
        "a declaration's rollback is not allowed to reconfigure the module's gate",
    );

    let mut serial = with_workers(1);
    let serial_errors = serial.check_module_source("pool_rollback", ROLLED_BACK_INSTANCE);
    assert!(
        serial_errors
            .iter()
            .any(|e| matches!(e, ElabError::Kernel { decl, .. } if decl.ends_with("unit_l"))),
        "the fixture's point is a false proof: {serial_errors:?}",
    );
    assert_eq!(
        errors.iter().map(render).collect::<Vec<_>>(),
        serial_errors.iter().map(render).collect::<Vec<_>>(),
        "the same errors, in the same order, at four workers as at one",
    );
    assert_eq!(
        registered(&elab, &NAMES),
        registered(&serial, &NAMES),
        "and the same names registered afterwards",
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
    // The enclosing rows stay wall-shaped at every width: a worker's CPU goes
    // to the declaration that spent it, and what the module row is charged for
    // the deferral is the wall this thread really spent blocked at the join
    // (`docs/parallel-kernel-gate-design.md` §7). So the exclusive rule —
    // no row claiming more phase time than it took — holds at eight workers
    // exactly as it holds at one, which is what `--timings` consumers read.
    let module_row = rows.iter().find(|r| r.kind == ScopeKind::Module).expect("a module row");
    for row in &rows {
        assert!(
            row.kernel_ns <= row.total_ns,
            "row {:?}/{:?} claims {}ns of kernel in {}ns",
            row.kind,
            row.item,
            row.kernel_ns,
            row.total_ns,
        );
    }
    assert!(
        module_row.kernel.eval_steps > 0,
        "a still-open enclosing scope still accounts for the *counters* moved off-thread",
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
