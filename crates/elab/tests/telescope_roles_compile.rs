//! Compile the real private wrapper module, with a positive control before
//! the role swap. The two frontend stubs supply signatures only; no fixture
//! runs, and all role definitions and the kernel types are production code.

use std::{fs, path::PathBuf, process::Command};

#[test]
fn a_structural_type_cannot_fill_the_emitted_telescope_slot() {
    let deps = std::env::current_exe().unwrap().parent().unwrap().to_owned();
    let kernel = fs::read_dir(&deps).unwrap().filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.file_name().unwrap().to_string_lossy().starts_with("libheather_kernel-")
            && path.extension().is_some_and(|ext| ext == "rlib"))
        .max_by_key(|path| path.metadata().unwrap().modified().unwrap())
        .expect("Cargo built the kernel dependency");
    let module = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/wf_types.rs");
    let dir = std::env::temp_dir().join(format!("heather-telescope-roles-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); }
    }
    let _cleanup = Cleanup(dir.clone());
    let prefix = format!(r#"
use std::sync::Arc;
use heather_kernel::{{level::Level, term::{{LocalCtx, Term, Type}}}};
struct Cx;
struct Elaborator;
impl Elaborator {{
    fn annotation_type(&self, _: &Cx, _: &Type, _: u32) -> Type {{ unreachable!() }}
}}
#[path = {module:?}]
mod roles;
use roles::{{StructuralWf, EmittedType}};
fn probe(structural: &StructuralWf<'_>, emitted: &EmittedType,
    gamma: &LocalCtx, level: &Level, motive: &Arc<Type>,
    shape: &Arc<Type>, arity: &Arc<Term>) {{
"#);
    for (name, arg) in [("valid", "emitted"), ("swapped", "structural")] {
        let source = dir.join(format!("{name}.rs"));
        fs::write(&source, format!("{prefix}\nstructural.telescope(gamma, level, motive, {arg}, (shape, arity));\n}}\n")).unwrap();
        let output = Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()))
            .arg("--edition=2024").arg("--crate-type=lib").arg("--emit=metadata")
            .arg("--cap-lints=allow")
            .arg("--extern").arg(format!("heather_kernel={}", kernel.display()))
            .arg("-L").arg(format!("dependency={}", deps.display()))
            .arg("-o").arg(dir.join(format!("{name}.rmeta"))).arg(&source)
            .output().expect("run rustc under scripts/test's inherited resource limits");
        let diagnostic = String::from_utf8_lossy(&output.stderr);
        if name == "valid" {
            assert!(output.status.success(), "positive control must compile: {diagnostic}");
        } else {
            assert!(!output.status.success(), "the structural-for-emitted swap compiled");
            assert!(diagnostic.contains("E0308") && diagnostic.contains("expected `&EmittedType`")
                && diagnostic.contains("found `&StructuralWf"),
                "must fail on the role, not imports or privacy: {diagnostic}");
        }
    }
}
