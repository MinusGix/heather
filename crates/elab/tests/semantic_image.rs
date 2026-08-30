//! Stage 1 of semantic module images: the explicit in-memory committed-state
//! boundary. Persistent images and imported-binding rechecks are later stages
//! of `docs/semantic-module-images-design.md`.

use heather_elab::{Elaborator, ModuleDependencyIdentity, ModuleReplayError};

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

#[test]
fn a_logical_module_delta_replays_over_an_independently_rebuilt_prefix() {
    let dependencies = ModuleDependencyIdentity::new(vec![[7; 32], [11; 32]]);
    let mut source = prefix();
    let delta = source
        .elab_module_delta("consumer", SUFFIX, dependencies.clone())
        .expect("extract consumer delta");

    let mut replayed = prefix();
    replayed
        .replay_module_delta(&delta, &dependencies)
        .expect("recheck and replay consumer delta");

    assert_eq!(delta.module(), "consumer");
    assert!(delta.binding_count() >= 2);
    assert_eq!(replayed.psi(), source.psi());
    assert_eq!(support::psi_hash(replayed.psi()), support::psi_hash(source.psi()));

    let downstream = r#"
import consumer;
import fixture;
import bool;
fn observed() -> Parcel<Bool> { wrapped_true() }
theorem observed_is_wrap(): observed() = Wrap(True) { refl }
"#;
    source
        .elab_module_source("downstream", downstream)
        .expect("source-built downstream");
    replayed
        .elab_module_source("downstream", downstream)
        .expect("replay-built downstream");
    assert_eq!(replayed.psi(), source.psi());
}

#[test]
fn replay_refuses_wrong_dependency_identity_without_mutating_the_world() {
    let expected = ModuleDependencyIdentity::new(vec![[1; 32]]);
    let mut source = prefix();
    let delta = source
        .elab_module_delta("consumer", SUFFIX, expected)
        .expect("extract consumer delta");

    let mut target = prefix();
    let before = target.psi().clone();
    let wrong = ModuleDependencyIdentity::new(vec![[2; 32]]);
    assert!(matches!(
        target.replay_module_delta(&delta, &wrong),
        Err(ModuleReplayError::DependencyIdentity)
    ));
    assert_eq!(target.psi(), &before);
}

#[test]
fn failed_delta_extraction_rolls_back_the_whole_module() {
    let mut elab = prefix();
    let before = elab.psi().clone();
    let result = elab.elab_module_delta(
        "broken",
        "import bool;\nfn landed() -> Bool { True }\nfn broken() -> Bool { missing }",
        ModuleDependencyIdentity::default(),
    );
    let error = match result {
        Ok(_) => panic!("a module delta cannot contain a successful prefix"),
        Err(error) => error,
    };
    assert!(error.to_string().contains("missing"), "{error}");
    assert_eq!(elab.psi(), &before);
    elab.elab_module_source("broken", "import bool;\nfn landed() -> Bool { True }")
        .expect("the rolled-back name is reusable");
}
