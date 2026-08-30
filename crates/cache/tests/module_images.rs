use heather_cache::module_image::{ModuleCacheError, ModuleCacheKey, ModuleImageCache};
use heather_elab::{Elaborator, LintProfile, ModuleDependencyIdentity};

fn temp(tag: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!("heather-module-image-{tag}-{}", std::process::id()))
}

#[test]
fn source_dependencies_and_semantics_select_a_content_addressed_artifact() {
    let none = ModuleDependencyIdentity::default();
    let dependency = ModuleDependencyIdentity::new(vec![[7; 32]]);
    let key = |module, source, dependencies, profile| {
        ModuleCacheKey::for_source(module, source, dependencies, profile)
    };
    let a = key("m", "fn x() -> Nat { 0 }", &none, LintProfile::Default);
    assert_eq!(
        a,
        key("m", "fn x() -> Nat { 0 }", &none, LintProfile::Default)
    );
    assert_ne!(
        a,
        key("n", "fn x() -> Nat { 0 }", &none, LintProfile::Default)
    );
    assert_ne!(
        a,
        key("m", "fn x() -> Nat { 1 }", &none, LintProfile::Default)
    );
    assert_ne!(
        a,
        key("m", "fn x() -> Nat { 0 }", &dependency, LintProfile::Default)
    );
    assert_ne!(a, key("m", "fn x() -> Nat { 0 }", &none, LintProfile::Stdlib));
}

#[test]
fn module_interface_is_proof_and_span_insensitive_but_definition_sensitive() {
    fn delta(src: &str) -> heather_elab::ModuleDelta {
        Elaborator::with_prelude()
            .unwrap()
            .elab_module_delta("sample", src, ModuleDependencyIdentity::default())
            .unwrap()
    }

    let short_proof = delta("theorem stable(n: Nat): n = n { refl }");
    let longer_proof = delta(
        "theorem stable(n: Nat): n = n { let p: (n = n) = refl; p }",
    );
    assert_ne!(short_proof.to_image_bytes(), longer_proof.to_image_bytes());
    assert_eq!(
        ModuleImageCache::interface_hash(&short_proof),
        ModuleImageCache::interface_hash(&longer_proof),
        "opaque proof edits do not change what dependents observe"
    );

    let compact = delta("fn value() -> Nat { 0 }");
    let respanned = delta("\nfn value() -> Nat {\n    0\n}\n");
    assert_ne!(compact.to_image_bytes(), respanned.to_image_bytes());
    assert_eq!(
        ModuleImageCache::interface_hash(&compact),
        ModuleImageCache::interface_hash(&respanned),
        "source layout is not a semantic interface fact"
    );

    let changed_body = delta("fn value() -> Nat { 1 }");
    assert_ne!(
        ModuleImageCache::interface_hash(&compact),
        ModuleImageCache::interface_hash(&changed_body),
        "transparent bodies remain part of the interface"
    );
    let changed_statement = delta("theorem stable(n: Nat): Succ(n) = Succ(n) { refl }");
    assert_ne!(
        ModuleImageCache::interface_hash(&short_proof),
        ModuleImageCache::interface_hash(&changed_statement),
        "opaque statements remain part of the interface"
    );
}

#[test]
fn published_image_round_trips_and_replays_against_the_supplied_prefix() {
    let dir = temp("round-trip");
    let _ = std::fs::remove_dir_all(&dir);
    let cache = ModuleImageCache::new(dir.clone());
    let dependencies = ModuleDependencyIdentity::default();
    let src = "fn value() -> Nat { 0 }";
    let key = ModuleCacheKey::for_source("sample", src, &dependencies, LintProfile::Default);

    let mut source = Elaborator::with_prelude().unwrap();
    let prefix = source.psi().clone();
    let delta = source
        .elab_module_delta("sample", src, dependencies.clone())
        .unwrap();
    let written_interface = cache.publish(key, &delta, &[]).unwrap();
    let loaded = cache
        .load(key, prefix, src.len())
        .unwrap()
        .expect("published image exists");
    assert_eq!(loaded.interface_hash, written_interface);

    let mut target = Elaborator::with_prelude().unwrap();
    target
        .replay_module_delta(&loaded.delta, &dependencies)
        .unwrap();
    target
        .elab_module_source("consumer", "import sample;\nfn use() -> Nat { value() }")
        .unwrap();
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn corruption_is_rejected_before_semantic_replay() {
    let dir = temp("corrupt");
    let _ = std::fs::remove_dir_all(&dir);
    let cache = ModuleImageCache::new(dir.clone());
    let dependencies = ModuleDependencyIdentity::default();
    let src = "fn value() -> Nat { 0 }";
    let key = ModuleCacheKey::for_source("sample", src, &dependencies, LintProfile::Default);
    let mut source = Elaborator::with_prelude().unwrap();
    let prefix = source.psi().clone();
    let delta = source
        .elab_module_delta("sample", src, dependencies)
        .unwrap();
    cache.publish(key, &delta, &[]).unwrap();

    let path = cache.path(key);
    let mut bytes = std::fs::read(&path).unwrap();
    let last = bytes.len() - 1;
    bytes[last] ^= 1;
    std::fs::write(path, bytes).unwrap();
    assert!(matches!(
        cache.load(key, prefix, src.len()),
        Err(ModuleCacheError::Corrupt(_))
    ));
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn warnings_round_trip_with_lint_fixes_and_source_bounded_spans() {
    let dir = temp("warnings");
    let _ = std::fs::remove_dir_all(&dir);
    let cache = ModuleImageCache::new(dir.clone());
    let dependencies = ModuleDependencyIdentity::default();
    let src = "fn identity(x: Nat) -> Nat { x }";
    let key = ModuleCacheKey::for_source("sample", src, &dependencies, LintProfile::Stdlib);
    let mut source = Elaborator::with_prelude().unwrap();
    source.set_lint_profile(LintProfile::Stdlib);
    let prefix = source.psi().clone();
    let delta = source
        .check_module_delta("sample", src, dependencies)
        .expect("warning does not fail the module");
    let warnings = source.take_warnings();
    assert!(!warnings.is_empty());
    assert!(warnings[0].fix.is_some());
    cache.publish(key, &delta, &warnings).unwrap();

    let loaded = cache.load(key, prefix.clone(), src.len()).unwrap().unwrap();
    assert_eq!(loaded.warnings.len(), warnings.len());
    assert_eq!(loaded.warnings[0].lint, warnings[0].lint);
    assert_eq!(loaded.warnings[0].msg, warnings[0].msg);
    assert_eq!(loaded.warnings[0].span, warnings[0].span);
    assert_eq!(
        loaded.warnings[0].fix.as_ref().map(|fix| (&fix.replacement, fix.span)),
        warnings[0].fix.as_ref().map(|fix| (&fix.replacement, fix.span))
    );

    assert!(matches!(
        cache.load(key, prefix, 0),
        Err(ModuleCacheError::Corrupt(_))
    ));
    let _ = std::fs::remove_dir_all(dir);
}
