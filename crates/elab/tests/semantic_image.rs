//! Stage 1 of semantic module images: the explicit in-memory committed-state
//! boundary. Persistent images and imported-binding rechecks are later stages
//! of `docs/semantic-module-images-design.md`.

use heather_elab::Elaborator;

mod support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");

fn prefix() -> Elaborator {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    elab.elab_module_source("logic", LOGIC).expect("logic");
    elab.elab_module_source("bool", BOOL).expect("bool");
    elab.elab_module_source(
        "fixture",
        r#"
import bool;

inductive Parcel<A> { Wrap(value: A) }

fn wrap<A>(value: A) -> Parcel<A> { Wrap(value) }
"#,
    )
    .expect("fixture");
    elab
}

const SUFFIX: &str = r#"
import fixture;
import bool;

fn wrapped_true() -> Parcel<Bool> { wrap(True) }

theorem wrapped_true_is_wrap(): wrapped_true() = Wrap(True) { refl }
"#;

#[test]
fn a_restored_image_elaborates_the_exact_fresh_suffix() {
    let base = prefix();
    let image = base.semantic_image();

    let mut restored = image.elaborator();
    restored.elab_module_source("consumer", SUFFIX).expect("restored suffix");

    let mut fresh = prefix();
    fresh.elab_module_source("consumer", SUFFIX).expect("fresh suffix");

    assert_eq!(restored.psi(), fresh.psi());
    assert_eq!(support::psi_hash(restored.psi()), support::psi_hash(fresh.psi()));
}

#[test]
fn image_forks_commit_isolated_suffixes() {
    let base = prefix();
    let prefix_len = base.psi().bindings.len();
    let image = base.semantic_image();

    let mut left = image.elaborator();
    left.elab_module_source(
        "left",
        "import bool;\nfn chosen() -> Bool { True }",
    )
    .expect("left suffix");

    let mut right = image.elaborator();
    let error = right
        .elab_module_source(
            "right",
            "import left;\nfn observed() -> Bool { chosen() }",
        )
        .expect_err("one image fork must not observe another fork's module");
    assert!(error.to_string().contains("unknown module `left`"), "{error}");

    right
        .elab_module_source("right", "import bool;\nfn chosen() -> Bool { False }")
        .expect("independent right suffix");

    assert_eq!(base.psi().bindings.len(), prefix_len);
    assert!(left.psi().bindings.len() > prefix_len);
    assert!(right.psi().bindings.len() > prefix_len);

    let before_failed_bundle = right.psi().bindings.len();
    right
        .elab_generated_source(
            "fn speculative() -> Nat { 0 }\nfn broken() -> Nat { missing }",
        )
        .expect_err("a failed generated bundle rolls its earlier declaration back");
    assert_eq!(right.psi().bindings.len(), before_failed_bundle);
}

#[test]
fn a_fork_starts_without_diagnostic_history() {
    let mut base = prefix();
    base.enable_item_timings();
    base.elab_module_source(
        "warning_source",
        r#"
inductive Token { A, B }
fn choose(token: Token) -> Nat {
    match token { A => 0, B => 1, _ => 2 }
}
"#,
    )
    .expect("warning source");
    assert!(!base.take_warnings().is_empty(), "fixture must produce a warning");
    let timings = base.take_item_timings();
    assert_eq!(timings.len(), 2);
    assert_eq!(timings.last().unwrap().item, "choose");
    assert!(timings.iter().all(|timing| timing.kernel_ns <= timing.total_ns));

    let image = base.semantic_image();
    let mut fork = image.elaborator();
    assert!(fork.take_warnings().is_empty());
    assert!(fork.take_omega_reports().is_empty());
    assert!(fork.take_omega_failure_reports().is_empty());
    assert!(fork.take_item_timings().is_empty(), "instrumentation policy is transient");
}
