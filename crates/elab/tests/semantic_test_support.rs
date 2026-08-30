//! Controls for the shared semantic test-fixture boundary.

mod support;

fn temp() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "heather-semantic-test-support-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&path);
    path
}

#[test]
fn a_corrupt_fixture_image_rebuilds_before_fresh_suffixes_run() {
    let dir = temp();
    let modules = &[(
        "base",
        "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n",
    )];
    let cold = support::semantic_test_base_at(modules, dir.clone());
    let expected = cold.psi().clone();

    let artifact = std::fs::read_dir(dir.join("modules-v1"))
        .unwrap()
        .next()
        .expect("one semantic test image")
        .unwrap()
        .path();
    std::fs::write(artifact, b"not an image").unwrap();
    let mut rebuilt = support::semantic_test_base_at(modules, dir.clone());
    assert_eq!(rebuilt.psi(), &expected);
    rebuilt
        .elab_module_source(
            "consumer",
            "import base; theorem uses_stable(n: Nat): n = n { stable(n) }",
        )
        .expect("a fresh suffix sees the rebuilt semantic world");

    let _ = std::fs::remove_dir_all(dir);
}
