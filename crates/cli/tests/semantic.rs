//! The semantic loader is a library boundary, not merely an implementation
//! detail of the `heather` binary.

use heather_cli::loader::Module;
use heather_cache::module_image::{ImageFreshness, ModuleCacheKey, ModuleImageCache, SemanticsIdentity};
use heather_cli::semantic::{CacheNoticeKind, SemanticSession};
use heather_elab::ModuleDependencyIdentity;
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

/// The inner-loop policy after a compiler edit: an image another build wrote
/// is replayed and said so, per module; the default policy rebuilds instead.
#[test]
fn a_stale_image_is_replayed_only_under_the_accepting_policy_and_is_reported() {
    let cache = temp("stale");
    let module = Module {
        name: "sample".into(),
        path: "sample.hthr".into(),
        src: "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n".into(),
    };
    // Stage the artifact a previous build would have left behind.
    let dependencies = ModuleDependencyIdentity::default();
    let key = ModuleCacheKey::for_source(&module.name, &module.src, &dependencies, LintProfile::Default);
    let mut writer = Elaborator::with_prelude().unwrap();
    let delta = writer
        .elab_module_delta(&module.name, &module.src, dependencies)
        .unwrap();
    let expected_psi = writer.psi().clone();
    ModuleImageCache::new(cache.clone())
        .publish_as(key, &delta, &[], SemanticsIdentity::of("older", "build"))
        .unwrap();

    let mut exact_elab = Elaborator::with_prelude().unwrap();
    let mut exact = SemanticSession::new(Some(cache.clone()));
    let outcome = exact.check(&mut exact_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(!outcome.replayed, "the exact policy rebuilds");
    assert!(outcome.notices.is_empty(), "{:?}", outcome.notices);
    assert_eq!(exact.stale_hits(), 0);

    // The rebuild overwrote the artifact; stage the stale one again.
    ModuleImageCache::new(cache.clone())
        .publish_as(key, &delta, &[], SemanticsIdentity::of("older", "build"))
        .unwrap();
    let mut stale_elab = Elaborator::with_prelude().unwrap();
    let mut stale = SemanticSession::new(Some(cache.clone()))
        .with_freshness(ImageFreshness::AcceptStale);
    let outcome = stale.check(&mut stale_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(outcome.replayed);
    assert_eq!(stale.hits(), 1);
    assert_eq!(stale.stale_hits(), 1);
    assert_eq!(outcome.notices.len(), 1);
    assert_eq!(outcome.notices[0].kind, CacheNoticeKind::StaleReplayed);
    assert!(outcome.notices[0].to_string().contains("another build"), "{}", outcome.notices[0]);
    assert_eq!(stale_elab.psi(), &expected_psi);

    let _ = std::fs::remove_dir_all(cache);
}

#[test]
fn reexport_dependencies_load_replay_and_invalidate_through_a_facade() {
    let root = temp("reexports");
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    let origin = root.join("origin.hthr");
    let facade = root.join("facade.hthr");
    let client = root.join("client.hthr");
    std::fs::write(&origin, "fn value() -> Nat { 7 } fn hidden() -> Nat { 9 }").unwrap();
    std::fs::write(&facade, "export origin::{value};").unwrap();
    std::fs::write(&client, "import facade; theorem correct(): facade::value() = 7 { refl }").unwrap();
    for warm in [false, true] {
        let modules = heather_cli::loader::load(&client, &[]).unwrap_or_else(|e| panic!("{}", e.msg));
        assert_eq!(modules.iter().map(|m| m.name.as_str()).collect::<Vec<_>>(), ["origin", "facade", "client"]);
        let mut e = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(cache.clone()));
        for module in &modules {
            let out = session.check(&mut e, module, LintProfile::Default);
            assert!(out.errors.is_empty(), "{}", module.name);
            assert_eq!(out.replayed, warm, "{}", module.name);
        }
    }
    // A changed origin invalidates the unchanged facade and its client.
    std::fs::write(&origin, "fn value() -> Nat { 8 } fn hidden() -> Nat { 9 }").unwrap();
    let modules = heather_cli::loader::load(&client, &[]).unwrap_or_else(|e| panic!("{}", e.msg));
    let mut e = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(Some(cache.clone()));
    for module in &modules {
        let out = session.check(&mut e, module, LintProfile::Default);
        assert!(!out.replayed, "{}", module.name);
        assert_eq!(out.errors.is_empty(), module.name != "client");
    }
    // Export edges participate in the loader's ordinary cycle check.
    std::fs::write(&origin, "export facade::{value};").unwrap();
    assert!(heather_cli::loader::load(&client, &[]).is_err());
    let _ = std::fs::remove_dir_all(root);
}

/// Two processes missing one key at once build it once: the second waits on
/// the key's build lock, looks again, and replays what the first published
/// (`ModuleImageCache::build_lock`). The test holds the lock itself as the
/// "first process", so the session under test must be blocked while it is
/// held and must replay, not elaborate, once it is released.
#[test]
fn a_miss_waits_for_a_concurrent_build_of_the_same_key_and_replays_it() {
    let cache = temp("single-flight");
    let name = "sample";
    let src = "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n";
    let dependencies = ModuleDependencyIdentity::default();
    let key = ModuleCacheKey::for_source(name, src, &dependencies, LintProfile::Default);
    let store = ModuleImageCache::new(cache.clone());
    let lock = store.build_lock(key).expect("a fresh store can take a build lock");

    let (done, finished) = std::sync::mpsc::channel();
    let waiter = std::thread::spawn({
        let cache = cache.clone();
        move || {
            let module = Module { name: name.into(), path: "sample.hthr".into(), src: src.into() };
            let mut elab = Elaborator::with_prelude().unwrap();
            let mut session = SemanticSession::new(Some(cache));
            let outcome = session.check(&mut elab, &module, LintProfile::Default);
            done.send(()).unwrap();
            (outcome.errors.is_empty(), outcome.replayed, session.hits(), elab.psi().clone())
        }
    });
    // Elaborating this module takes milliseconds; a session that did not
    // wait would be finished long before this.
    assert!(
        finished.recv_timeout(std::time::Duration::from_millis(500)).is_err(),
        "the session elaborated instead of waiting on the build lock"
    );

    let mut writer = Elaborator::with_prelude().unwrap();
    let delta = writer.elab_module_delta(name, src, dependencies).unwrap();
    store.publish(key, &delta, &[]).unwrap();
    drop(lock);

    let (clean, replayed, hits, psi) = waiter.join().unwrap();
    assert!(clean);
    assert!(replayed, "the waiter rebuilt a key the lock holder published");
    assert_eq!(hits, 1);
    assert_eq!(&psi, writer.psi());

    let _ = std::fs::remove_dir_all(cache);
}
