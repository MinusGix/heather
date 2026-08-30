//! The semantic loader is a library boundary, not merely an implementation
//! detail of the `heather` binary.

use heather_cli::loader::Module;
use heather_cli::semantic::SemanticSession;
use heather_elab::{Elaborator, LintProfile};

fn temp(tag: &str) -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "heather-semantic-session-{tag}-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&path);
    path
}

#[test]
fn a_fresh_consumer_can_replay_a_previous_sessions_module() {
    let cache = temp("replay");
    let module = Module {
        name: "sample".into(),
        path: "sample.hthr".into(),
        src: "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n".into(),
    };

    let mut cold_elab = Elaborator::with_prelude().unwrap();
    let mut cold = SemanticSession::new(Some(cache.clone()));
    let outcome = cold.check(&mut cold_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(!outcome.replayed);
    assert_eq!(cold.hits(), 0);

    let expected_psi = cold_elab.psi().clone();
    let mut warm_elab = Elaborator::with_prelude().unwrap();
    let mut warm = SemanticSession::new(Some(cache.clone()));
    let outcome = warm.check(&mut warm_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(outcome.replayed);
    assert_eq!(warm.hits(), 1);
    assert_eq!(warm_elab.psi(), &expected_psi);

    let _ = std::fs::remove_dir_all(cache);
}

#[test]
fn an_uncached_session_preserves_the_plain_source_path() {
    let module = Module {
        name: "bad".into(),
        path: "bad.hthr".into(),
        src: "theorem open(n: Nat): n = n { ? }".into(),
    };
    let mut elab = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(None);
    let outcome = session.check(&mut elab, &module, LintProfile::Default);
    assert!(!outcome.errors.is_empty());
    assert!(!outcome.replayed);
    assert!(outcome.notices.is_empty());
    assert_eq!(session.hits(), 0);
}
