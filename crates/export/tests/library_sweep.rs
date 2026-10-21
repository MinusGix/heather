//! The library sweep (`issues/export-library-sweep.md`): export the closure
//! of `lib/std/list.hthr` (list, nat, bool, logic, option, pair) and report
//! every refusal by cause. With `HEATHER_EXPORT_OUT` set it writes
//! `Sweep.lean` for `scripts/export-recheck` to hand to Lean.

use heather_cli::loader;
use heather_elab::Elaborator;
use heather_export::{Source, Target, export, print};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

#[test]
fn std_list_closure_exports() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    let modules = loader::load(&root.join("list.hthr"), &[PathBuf::from(&root)]).map_err(|e| e.msg).expect("load");
    let mut e = Elaborator::with_prelude_for_export().expect("prelude");
    for m in &modules {
        e.elab_module_source(&m.name, &m.src).unwrap_or_else(|err| panic!("{}: {err}", m.name));
    }
    let decls = export(&Source {
        psi: e.psi(),
        proof: &|abs| e.export_proof(abs).cloned(),
        name: &|abs| e.global_key_at(abs).map(str::to_string).or_else(|| e.generated_key_at(abs)),
    });
    let mut causes: BTreeMap<String, usize> = BTreeMap::new();
    for d in &decls {
        if let Err(r) = &d.decl {
            // A dependency refusal names its dependency; count it by kind.
            let cause = if r.0.starts_with("mentions refused") { "mentions a refused declaration".into() } else { r.0.clone() };
            if !r.0.starts_with("mentions refused") && !r.0.starts_with("Wf ") {
                eprintln!("refused {}: {}", d.name.as_deref().unwrap_or("?"), r.0);
            }
            *causes.entry(cause).or_default() += 1;
        }
    }
    let ok = decls.iter().filter(|d| d.decl.is_ok()).count();
    eprintln!("sweep: {} bindings, {ok} exported, refused by cause: {causes:#?}", decls.len());
    // Nothing in this closure is modal or level-polymorphic: the only
    // refusals are `Wf` (every `List` declaration) and what mentions it.
    assert!(
        causes.keys().all(|c| c.starts_with("Wf ") || c == "mentions a refused declaration"),
        "refused: {causes:#?}"
    );
    assert!(ok >= 290, "{ok} exported");
    if let Some(dir) = std::env::var_os("HEATHER_EXPORT_OUT") {
        std::fs::write(PathBuf::from(dir).join("Sweep.lean"), print(Target::Lean, &decls)).unwrap();
    }
}
