//! The whole-library sweep (`docs/library/export-fragment-design.md` §7): every
//! module of `lib/std` and its folders, exported, with each refusal counted by cause. Opt-in (`#[ignore]`): it elaborates the
//! library and spells every proof, which is minutes of release time and
//! past the suite's rails in a debug build. `scripts/export-recheck --wide`
//! runs it and hands `Wide.hxk` to Lean's kernel.

use heather_cli::loader;
use heather_elab::Elaborator;
use heather_export::{Source, export, print_kernel};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The causes a refusal may have today; a new one is a change to look at.
const KNOWN: &[&str] = &[
    "mentions a refused declaration",
    // A tier-1 instance whose declaration was refused or not recognised,
    // or a level profile the elaborator does not lower: none in the library
    // since value parameters and other profiles are realised (design §5.1),
    // but the causes the realisation names.
    "Wf instance of a declaration the exporter has not met",
    "Wf instance at a level other than its declaration's",
    // Codata (`coitree`, `coitree_eutt`) lowers to the kernel's `M`, which
    // has no realisation in either target yet (issues/export-codata-m.md).
    "M (not exported yet)",
];

#[test]
#[ignore = "minutes in release; run by scripts/export-recheck --wide"]
fn std_library_exports() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    // Every module, folders included, as `heather check lib/std` takes them
    // (docs/library/lib-layout-design.md): the library's stems are unique, so no
    // nested file is shadowed.
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        for p in std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()) {
            if p.is_dir() {
                if !p.file_name().unwrap().to_string_lossy().starts_with('.') {
                    walk(&p, out);
                }
            } else if p.extension().is_some_and(|x| x == "hthr") {
                out.push(p);
            }
        }
    }
    let mut roots: Vec<PathBuf> = Vec::new();
    walk(&root, &mut roots);
    roots.sort();
    let refs: Vec<&Path> = roots.iter().map(PathBuf::as_path).collect();
    let modules = loader::load_many(&refs, &[root.clone()]).map_err(|e| e.msg).expect("load");
    let mut e = Elaborator::with_prelude_for_export().expect("prelude");
    for m in &modules {
        e.elab_module_source(&m.name, &m.src).unwrap_or_else(|err| panic!("{}: {err}", m.name));
    }
    let decls = export(&Source {
        psi: e.psi(),
        proof: &|abs| e.export_proof(abs).cloned(),
        name: &|abs| e.global_key_at(abs).map(str::to_string).or_else(|| e.generated_key_at(abs)),
        ctors: &|tag| e.constructor_names(tag as u32),
        tycode_at: &|tag, levels| e.tycode_fn_at(tag as u32, levels),
    });
    let mut causes: BTreeMap<String, usize> = BTreeMap::new();
    for d in &decls {
        if let Err(r) = &d.decl {
            let cause = if r.0.starts_with("mentions refused") { "mentions a refused declaration".into() } else { r.0.clone() };
            if !r.0.starts_with("mentions refused") {
                eprintln!("refused {}: {}", d.name.as_deref().unwrap_or("?"), r.0);
            }
            *causes.entry(cause).or_default() += 1;
        }
    }
    let ok = decls.iter().filter(|d| d.decl.is_ok()).count();
    eprintln!("wide: {} modules, {} bindings, {ok} exported, refused by cause: {causes:#?}", modules.len(), decls.len());
    let unknown: Vec<&String> = causes.keys().filter(|c| !KNOWN.contains(&c.as_str())).collect();
    assert!(unknown.is_empty(), "refused for a new cause: {unknown:#?}");
    let kernel = print_kernel(&decls);
    if let Some(dir) = std::env::var_os("HEATHER_EXPORT_OUT") {
        std::fs::write(PathBuf::from(dir).join("Wide.hxk"), kernel).unwrap();
    }
}
