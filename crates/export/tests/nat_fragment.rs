//! The prototype's acceptance: a few `Nat` declarations and a two-constructor
//! enum export with no refusal, and — when `HEATHER_EXPORT_OUT` names a
//! directory — are written there as `Exported.lean` / `Exported.v` beside the
//! preludes, for `scripts/export-recheck` to hand to Lean and Rocq.

use heather_elab::Elaborator;
use heather_export::{Source, Target, export, print, print_kernel};

const SOURCE: &str = r#"
fn Nat::add(self a: Nat, b: Nat) → Nat { match b { Zero => a, Succ(k) => Succ(a.add(k)) } }
theorem Nat::add_left_zero(self x: Nat): Nat::add(0, x) = x {
    match x { Zero => refl, Succ(k) => Nat::cong_succ(k.add_left_zero()) }
}
theorem Nat::add_succ_left(self a: Nat, b: Nat): Nat::add(Succ(a), b) = Succ(Nat::add(a, b)) {
    match b { Zero => refl, Succ(k) => Nat::cong_succ(a.add_succ_left(k)) }
}
theorem Nat::add_assoc(self x: Nat, y: Nat, z: Nat): Nat::add(Nat::add(x, y), z) = Nat::add(x, Nat::add(y, z)) {
    match z { Zero => refl, Succ(k) => Nat::cong_succ(x.add_assoc(y, k)) }
}
inductive B { T, F }
fn B::not(self b: B) -> B { match b { T => F, F => T } }
theorem B::not_not(self b: B): b.not().not() = b { match b { T => refl, F => refl } }
theorem big(): Nat::add(1000000000000000000000, 1) = 1000000000000000000001 { refl }
inductive Tree { Leaf, Node(l: Tree, r: Tree) }
fn Tree::size(self t: Tree) → Nat { match t { Leaf => 1, Node(l, r) => Nat::add(l.size(), r.size()) } }
theorem Tree::size_node(l: Tree, r: Tree): Node(l, r).size() = Nat::add(l.size(), r.size()) { refl }
theorem Tree::size_leaf(): Tree::size(Leaf) = 1 { refl }
fn Tree::mirror(self t: Tree) → Tree { match t { Leaf => Leaf, Node(l, r) => Node(r.mirror(), l.mirror()) } }
theorem Tree::size_mirror_node(l: Tree, r: Tree): Node(l, r).mirror().size() = Nat::add(r.mirror().size(), l.mirror().size()) {
    refl
}
class Rel<A>(R: A → A → Type) {
    rel_refl: (x: A) → R(x, x),
    rel_sym: (x, y: A) → R(x, y) → R(y, x),
}
class Rel2<A>(R: A → A → Type) extends Rel<A>(R) {
    rel_trans: (x, y, z: A) → R(x, y) → R(y, z) → R(x, z),
}
theorem Rel2::loop<A: Rel2(R)>(R: A → A → Type, x: A): R(x, x) {
    A.rel_trans(x, x, x, A.rel_sym(x, x, A.rel_refl(x)), A.rel_refl(x))
}
"#;

/// Native inductives beyond one profile of type parameters
/// (`issues/export-inductive-coverage.md`): a value parameter, as
/// `itree_trace::Trace<R>(E: Events)` has, and a declaration used at a type
/// argument of another level (`List<A → B → Type>` in `relation::AnyOf`),
/// built, matched and recursed over at both.
const INDUCTIVES: &str = r#"
record Sig2 { Cmd: Type, Resp: Cmd → Type }
inductive Log<R>(E: Sig2) { Done(r: R), Step(c: E.Cmd, a: E.Resp(c), rest: Log<R>(E)) }
fn Log::steps<R>(E: Sig2, l: Log<R>(E)) → Nat { match l { Done(_) => 0, Step(_, _, rest) => Succ(Log::steps(E, rest)) } }
fn Bits() → Sig2 { Sig2(B, λ _ => B) }
fn two_steps() → Log<Nat>(Bits()) { Step(T, F, Step(F, T, Done(0))) }
theorem two_steps_steps(): Log::steps(Bits(), two_steps()) = 2 { refl }
inductive Seq<A> { End, More(x: A, rest: Seq<A>) }
fn Seq::len<A>(s: Seq<A>) → Nat { match s { End => 0, More(_, r) => Succ(Seq::len(r)) } }
fn Seq::count_types(s: Seq<Type>) → Nat { match s { End => 0, More(_, r) => Succ(Seq::count_types(r)) } }
fn kinds() → Seq<Type> { More(Nat, More(B, End)) }
theorem kinds_count(): Seq::count_types(kinds()) = 2 { refl }
"#;

#[test]
fn nat_and_enum_export_without_refusal() {
    let mut e = Elaborator::with_prelude_for_export().expect("prelude");
    e.elab_source(&format!("{SOURCE}{INDUCTIVES}")).expect("source checks");
    let decls = export(&Source {
        psi: e.psi(),
        proof: &|abs| e.export_proof(abs).cloned(),
        name: &|abs| e.global_key_at(abs).map(str::to_string).or_else(|| e.generated_key_at(abs)),
        ctors: &|tag| e.constructor_names(tag as u32),
        tycode_at: &|tag, levels| e.tycode_fn_at(tag as u32, levels),
    });
    let refused: Vec<_> = decls.iter().filter(|d| d.decl.is_err()).collect();
    assert!(refused.is_empty(), "refused: {refused:?}");
    // Every theorem kept its proof, the prelude's included: nothing exports
    // as an assumption.
    let assumed: Vec<_> =
        decls.iter().filter(|d| d.decl.as_ref().is_ok_and(|d| d.body.is_none() && d.inductive.is_none())).map(|d| &d.name).collect();
    assert!(assumed.is_empty(), "exported as axioms: {assumed:?}");
    let lean = print(Target::Lean, &decls);
    assert!(lean.contains("def Heather.main.Nat.add_assoc :"), "{lean}");
    // A class's fields are projections of its record, which the targets
    // type themselves: `⌊·⌋` leaves them, and the kernel route writes each as
    // `Expr.proj` with nothing skipped (issues/export-spelling-cost.md).
    let kernel = print_kernel(&decls);
    assert!(kernel.lines().any(|l| l.starts_with("j\t")), "no projection in:\n{kernel}");
    // `Log` over its value parameter, and `Seq` once at its own profile and
    // once more at `Seq<Type>`'s, each with the eliminator its match uses.
    for (inductive, nparams) in [("main::Log", 2), ("main::Seq", 1), ("main::Seq::at#1", 1)] {
        let head = format!("i\t{inductive}\t{nparams}\t");
        assert!(kernel.lines().any(|l| l.starts_with(&head)), "no native inductive {inductive}:\n{kernel}");
    }
    assert!(kernel.lines().any(|l| l.starts_with("d\tmain::Seq::at#1::elim#")), "Seq<Type> is not eliminated at its own profile");
    let skipped: Vec<&str> = kernel.lines().filter(|l| l.starts_with("x\t")).collect();
    assert!(skipped.is_empty(), "skipped by the kernel route:\n{}", skipped.join("\n"));
    if let Some(dir) = std::env::var_os("HEATHER_EXPORT_OUT") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::write(dir.join("Exported.lean"), lean).unwrap();
        std::fs::write(dir.join("Exported.v"), print(Target::Coq, &decls)).unwrap();
        std::fs::write(dir.join("Exported.hxk"), kernel).unwrap();
    }
}

/// An ordinary elaborator keeps no proof for a theorem whose statement
/// carries no data, so it exports as an assumption: the export mode is what
/// changes that, and it must not change what an ordinary check keeps.
#[test]
fn without_export_mode_theorems_are_assumptions() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(SOURCE).expect("source checks");
    let decls = export(&Source::psi(e.psi()));
    assert!(decls.iter().all(|d| d.decl.is_ok()));
    let assumed = decls.iter().filter(|d| d.decl.as_ref().is_ok_and(|d| d.body.is_none())).count();
    assert!(assumed >= 5, "{assumed}");
    assert!((0..e.psi().bindings.len()).all(|abs| e.export_proof(abs).is_none()));
}
