//! The library sweep (`issues/export-library-sweep.md`): export the closure
//! of `lib/std/data/list.hthr` (list, nat, bool, logic, option, pair) and report
//! every refusal by cause. With `HEATHER_EXPORT_OUT` set it writes
//! `Sweep.lean`, the same split one file per module under `Sweep/` (listed
//! in dependency order in `Sweep/order`), the kernel-route twin
//! `Sweep.hxk`, and the Rocq file `Sweep.v`, for `scripts/export-recheck`.

use heather_cli::loader;
use heather_elab::Elaborator;
use heather_export::{Source, Target, export, print, print_kernel, print_lean_files};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing;
use std::sync::Arc as Rc;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

#[test]
fn std_list_closure_exports() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    let modules = loader::load(&root.join("data/list.hthr"), &[PathBuf::from(&root)]).map_err(|e| e.msg).expect("load");
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
    // Nothing in this closure is modal or level-polymorphic, and `List`'s
    // `Wf` is realised as a native inductive: nothing is refused.
    assert!(causes.is_empty(), "refused: {causes:#?}");
    // Every checked spelling is erased by the kernel's own `⌊·⌋`, so no
    // body keeps a hole and the kernel route skips nothing.
    let kernel = print_kernel(&decls);
    let holes: Vec<&str> = kernel.lines().filter(|l| l.starts_with("x\t")).collect();
    assert!(holes.is_empty(), "skipped by the kernel route:\n{}", holes.join("\n"));
    assert!(kernel.contains("\ni\tlist::List\t1\t"), "List is a native inductive with one parameter");
    if let Some(dir) = std::env::var_os("HEATHER_EXPORT_OUT") {
        let dir = PathBuf::from(dir);
        std::fs::write(dir.join("Sweep.lean"), print(Target::Lean, &decls)).unwrap();
        std::fs::write(dir.join("Sweep.v"), print(Target::Coq, &decls)).unwrap();
        // The same, one Lean file per module, in dependency order.
        let split = dir.join("Sweep");
        std::fs::create_dir_all(&split).unwrap();
        let files = print_lean_files(&decls);
        for (name, text) in &files {
            std::fs::write(split.join(format!("{name}.lean")), text).unwrap();
        }
        let order: Vec<&str> = files.iter().map(|(n, _)| n.as_str()).collect();
        std::fs::write(split.join("order"), order.join("\n") + "\n").unwrap();
        std::fs::write(dir.join("Sweep.hxk"), kernel).unwrap();
        std::fs::write(dir.join("Control.hxk"), open_tag_control(&e)).unwrap();
    }
}

/// The negative control for the realisation's side condition (design §5.1):
/// a declaration that uses `elim_Wf`'s β at an **open** tag. Heather's
/// kernel accepts it; the native recursor cannot reduce there, so Lean must
/// reject it, and `scripts/export-recheck` checks that it does.
///
/// `Π(A : Ty 0) (a : S) (cs : Vec(List A; n[a])). elim_Wf(_. Nat; _ _ _. 0; sup_f(a; cs)) = 0`, by `refl`.
fn open_tag_control(e: &Elaborator) -> String {
    let psi = e.psi();
    let list = (0..psi.bindings.len()).find(|&a| e.generated_key_at(a).as_deref() == Some("list::List#tycode_fn")).expect("List");
    let GlobalBinding::Tm { body: Some(code), .. } = &psi.bindings[list] else { panic!("List's code") };
    let Term::Lam { body: wf, .. } = &**code else { panic!("List's parameter") };
    let Term::TmWf { level, shape, arity } = &**wf else { panic!("List's Wf") };
    let l = level.clone();
    // In (A): the shape and the arity (under x). The control sits after the
    // whole of Ψ, so List's globals are weakened past what follows it.
    let up = (psi.bindings.len() - list) as u32;
    let shape = Rc::new(Type::El { level: l.clone(), tm: Rc::new(shape.shift_global(up)) });
    let arity = Rc::new(arity.shift_global(up));
    let wf_at = |by: u32| Type::Wf { level: l.clone(), shape: Rc::new(shape.shift_local(by)), arity: Rc::new(arity.shift_local_above(by, 1)) };
    let nat = Rc::new(Type::Nat);
    let zero = Rc::new(Term::Zero);
    // In (A, a, cs).
    let Type::Wf { shape: s2, arity: n2, .. } = wf_at(2) else { unreachable!() };
    let lhs = Term::ElimWf {
        level: l.clone(),
        motive_level: Level::Zero,
        shape: s2.clone(),
        arity: n2.clone(),
        motive: nat.clone(),
        step: zero.clone(),
        scrut: Rc::new(Term::Supf { level: l.clone(), shape: s2, arity: n2, label: Rc::new(Term::Var(LocalVar(1))), children: Rc::new(Term::Var(LocalVar(0))) }),
    };
    let goal = Type::Id { level: Level::Zero, ty: nat.clone(), lhs: Rc::new(lhs), rhs: zero.clone() };
    let cs_ty = Rc::new(Type::Vec { level: l.clone(), elem: Rc::new(wf_at(1)), len: arity.clone() });
    let pi = |dom_level: Level, dom: Rc<Type>, cod_level: Level, cod: Type| Type::Pi { dom_level, cod_level, dom, cod: Rc::new(cod) };
    // Each Π lives at the join of its domain's and codomain's levels.
    let (one, l_cs) = (Level::succ(Level::Zero), Level::max(l.clone(), Level::Zero));
    let l_a = Level::max(l.clone(), l_cs.clone());
    let ty = pi(one.clone(), Rc::new(Type::Ty(Level::Zero)), l_a.clone(),
        pi(l.clone(), shape.clone(), l_cs.clone(), pi(l.clone(), cs_ty.clone(), Level::Zero, goal)));
    let lam = |dom_level: Level, dom: Rc<Type>, cod_level: Level, body: Term| Term::Lam { dom_level, cod_level, dom, body: Rc::new(body) };
    let proof = lam(one.clone(), Rc::new(Type::Ty(Level::Zero)), l_a.clone(),
        lam(l.clone(), shape, l_cs.clone(), lam(l.clone(), cs_ty, Level::Zero, Term::Refl { level: Level::Zero, ty: nat, tm: zero })));
    let l = Level::max(one, l_a);
    let mut world = psi.clone();
    typing::check_term(&world, 0, Layer::Code, &LocalCtx::nil(), &proof, &ty, &l, typing::DEFAULT_FUEL)
        .expect("Heather's kernel accepts β at an open tag");
    let abs = world.bindings.len();
    world.push(GlobalBinding::Tm { ctx: LocalCtx::nil(), layer: Layer::Code, ty: Rc::new(ty), level: l, body: Some(Rc::new(proof)) });
    let decls = export(&Source {
        psi: &world,
        proof: &|a| e.export_proof(a).cloned(),
        name: &|a| if a == abs { Some("control::open_tag_beta".into()) } else { e.global_key_at(a).map(str::to_string).or_else(|| e.generated_key_at(a)) },
        ctors: &|tag| e.constructor_names(tag as u32),
        tycode_at: &|tag, levels| e.tycode_fn_at(tag as u32, levels),
    });
    let control = decls.last().expect("the control");
    assert!(control.decl.is_ok(), "the control exports: {:?}", control.decl.as_ref().err());
    print_kernel(&decls)
}
