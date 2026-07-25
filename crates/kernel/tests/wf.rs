//! `Wf`, `sup_f`, `elim_Wf`: phase 2 of the landing
//! (`docs/wf-former-design.md` §§1.3–5, `issues/wf-former.md`).
//!
//! The working example is the type the whole decision was about —
//! `Tree { Leaf, Node(Tree, Tree) }`, the smallest declaration the finitary
//! encodings provably cannot reach (`docs/branching-inductives-choice.md`
//! §1) — built here as
//!
//! ```text
//! Tree = Wf^0(x : Unit + Unit). case x of inl _ ⇒ 0 | inr _ ⇒ 2
//! ```
//!
//! and the acceptance criterion of the design doc §9 is the last two tests:
//! the same theorem the three postulate prototypes proved
//! (`crates/elab/tests/branching_route_*.rs`) now goes through against the
//! real former with **every β-marker deleted** — the Leaf arm is literally
//! `refl`, and the Node arm is `cong`, `cong`, `trans`. Route A's arms keep
//! a funext-and-transport bridge in that same place forever.

use std::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{
    nth, CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type,
};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 1_000_000;

// -------------------------------------------------------------------------
// Helpers
// -------------------------------------------------------------------------

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn c(n: u64) -> Level {
    Level::constant(n)
}

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn nil_ctx() -> LocalCtx {
    LocalCtx { base: CtxBase::Nil, entries: vec![] }
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

fn two() -> Type {
    Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(Type::Unit),
    }
}

/// `inl u` / `inr u` at `Unit + Unit`.
fn inj(right: bool, val: Term) -> Term {
    if right {
        Term::Inr {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit),
            rhs: rty(Type::Unit),
            val: rt(val),
        }
    } else {
        Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit),
            rhs: rty(Type::Unit),
            val: rt(val),
        }
    }
}

/// `arity a = case a of inl _ ⇒ 0 | inr _ ⇒ 2` — Leaf is nullary, Node is
/// binary. This is the *whole* declaration: the tag set is the shape and
/// the field count is a function of it.
fn arity_of(scrut: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(Type::Unit),
        motive: rty(Type::Nat),
        case_l: rt(Term::Zero),
        case_r: rt(nat(2)),
        scrut: rt(scrut),
    }
}

/// `Tree = Wf^0(x : 2). arity x` — closed, so it never needs shifting.
fn tree() -> Type {
    Type::Wf { level: c(0), shape: rty(two()), arity: rt(arity_of(v(0))) }
}

fn supf(label: Term, children: Term) -> Term {
    Term::Supf {
        level: c(0),
        shape: rty(two()),
        arity: rt(arity_of(v(0))),
        label: rt(label),
        children: rt(children),
    }
}

fn leaf() -> Term {
    supf(inj(false, Term::Triv), Term::Triv)
}

/// The canonical children tuple `(l, (r, ⟨⟩)) : Vec(Tree; 2)`.
fn pair2(l: Term, r: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree()),
        snd_ty: rty(Type::Vec { level: c(0), elem: rty(tree()), len: rt(nat(1)) }),
        fst: rt(l),
        snd: rt(Term::Pair {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: rty(tree()),
            snd_ty: rty(Type::Vec { level: c(0), elem: rty(tree()), len: rt(nat(0)) }),
            fst: rt(r),
            snd: rt(Term::Triv),
        }),
    }
}

fn node(l: Term, r: Term) -> Term {
    supf(inj(true, Term::Triv), pair2(l, r))
}

fn vec_tree(len: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(tree()), len: rt(len) }
}

fn fin(len: Term) -> Type {
    Type::Fin { len: rt(len) }
}

/// `nth^0(Tree; k; cs; i)`.
fn nth_tree(k: Term, cs: Term, i: Term) -> Term {
    nth(&c(0), &rty(tree()), &rt(k), rt(cs), rt(i))
}

/// Index 0 / 1 of `Fin 2` (`Unit + (Unit + Empty)`).
fn idx(one: bool) -> Term {
    let inner = Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(Type::Empty),
    };
    if one {
        Term::Inr {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit),
            rhs: rty(inner),
            val: rt(Term::Inl {
                lhs_level: c(0),
                rhs_level: c(0),
                lhs: rty(Type::Unit),
                rhs: rty(Type::Empty),
                val: rt(Term::Triv),
            }),
        }
    } else {
        Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit),
            rhs: rty(inner),
            val: rt(Term::Triv),
        }
    }
}

// -------------------------------------------------------------------------
// Checking helpers
// -------------------------------------------------------------------------

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("type does not check: {e:?}"));
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn ck_fails(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("the kernel gate must reject this");
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

// -------------------------------------------------------------------------
// `mirror` — non-dependent recursion, the constant motive
// -------------------------------------------------------------------------

/// `mirror t` — swap every node's children. The step cases on the tag
/// first, generalizing `cs` and `ih` in the case motive, so that inside
/// each branch the arity is a literal and `Vec`/`Fin` reduce. That is the
/// shape the generated recursor will emit.
fn mirror(scrut: Term) -> Term {
    // Case motive, binds z at (…, a, cs, ih, z):
    //   Π(cs' : Vec(Tree; arity z)). Π(ih' : Π(i : Fin (arity z)). Tree). Tree
    let cmot = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(arity_of(v(0)))),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(arity_of(v(1)))),
                cod: rty(tree()),
            }),
            cod: rty(tree()),
        }),
    };
    // Leaf arm: the ih is unused (arity 0).
    let arm_l = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(nat(0))),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(nat(0))),
                cod: rty(tree()),
            }),
            body: rt(leaf()),
        }),
    };
    // Node arm: `node (ih' 1) (ih' 0)` — the swap, reading the recursive
    // results out of the transient ih at literal indices.
    let ih_at = |i: Term| Term::App {
        fun: rt(v(0)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(fin(nat(2))),
        cod: rty(tree()),
        arg: rt(i),
    };
    let arm_r = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(nat(2))),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(nat(2))),
                cod: rty(tree()),
            }),
            body: rt(node(ih_at(idx(true)), ih_at(idx(false)))),
        }),
    };
    // Step at (Γ, a = 2, cs = 1, ih = 0).
    let cased = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(Type::Unit),
        motive: rty(cmot),
        case_l: rt(arm_l),
        case_r: rt(arm_r),
        scrut: rt(v(2)),
    };
    let at_cs = Term::App {
        fun: rt(cased),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(arity_of(v(2)))),
        // binds cs'; a = v(3) here.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(arity_of(v(3)))),
                cod: rty(tree()),
            }),
            cod: rty(tree()),
        }),
        arg: rt(v(1)),
    };
    let step = Term::App {
        fun: rt(at_cs),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(fin(arity_of(v(2)))),
            cod: rty(tree()),
        }),
        cod: rty(tree()),
        arg: rt(v(0)),
    };
    Term::ElimWf {
        level: c(0),
        motive_level: c(0),
        shape: rty(two()),
        arity: rt(arity_of(v(0))),
        motive: rty(tree()),
        step: rt(step),
        scrut: rt(scrut),
    }
}

fn mm(t: Term) -> Term {
    mirror(mirror(t))
}

// -------------------------------------------------------------------------
// Formation, introduction, computation
// -------------------------------------------------------------------------

#[test]
fn the_type_and_the_constructors_check() {
    let g = nil_ctx();
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &g, &tree(), &c(0), FUEL).unwrap();
    ck(&g, &leaf(), &tree(), c(0));
    ck(&g, &node(leaf(), leaf()), &tree(), c(0));
    ck(&g, &node(node(leaf(), leaf()), leaf()), &tree(), c(0));
}

#[test]
fn constructors_take_open_children() {
    // Γ = (l r : Tree) ⊢ node l r : Tree — constructor form whatever the
    // children are. This is the thing the finitary encodings could not do.
    let g = ext(&ext(&nil_ctx(), tree(), c(0)), tree(), c(0));
    ck(&g, &node(v(1), v(0)), &tree(), c(0));
}

#[test]
fn canonical_forms_are_unique() {
    let g = nil_ctx();
    conv(&g, &node(leaf(), leaf()), &node(leaf(), leaf()), &tree(), c(0));
    not_conv(&g, &leaf(), &node(leaf(), leaf()), &tree(), c(0));
    not_conv(
        &g,
        &node(node(leaf(), leaf()), leaf()),
        &node(leaf(), node(leaf(), leaf())),
        &tree(),
        c(0),
    );
}

#[test]
fn mirror_computes_on_closed_data() {
    let g = nil_ctx();
    let t = node(node(leaf(), leaf()), leaf());
    ck(&g, &mirror(t.clone()), &tree(), c(0));
    conv(&g, &mirror(leaf()), &leaf(), &tree(), c(0));
    conv(&g, &mirror(t), &node(leaf(), node(leaf(), leaf())), &tree(), c(0));
}

#[test]
fn beta_fires_on_open_children() {
    // Γ = (l r : Tree) ⊢ mirror (node l r) ≡ node (mirror r) (mirror l).
    // The eliminator reduces because the *scrutinee* is a constructor form,
    // regardless of what the children are — β on open subterms, which route
    // A also has and every finitary encoding lacks.
    let g = ext(&ext(&nil_ctx(), tree(), c(0)), tree(), c(0));
    let lhs = mirror(node(v(1), v(0)));
    let rhs = node(mirror(v(0)), mirror(v(1)));
    ck(&g, &lhs, &tree(), c(0));
    conv(&g, &lhs, &rhs, &tree(), c(0));
}

#[test]
fn neutral_on_a_neutral_scrutinee() {
    // An open scrutinee leaves `elim_Wf` stuck but well-typed, and two such
    // eliminations of the same term are convertible (the neutral congruence
    // in conv.rs, which induction over an open term needs).
    let g = ext(&nil_ctx(), tree(), c(0));
    ck(&g, &mirror(v(0)), &tree(), c(0));
    assert!(matches!(
        whnf_term(&mirror(v(0)), &g, FUEL).unwrap(),
        Term::ElimWf { .. }
    ));
    conv(&g, &mirror(v(0)), &mirror(v(0)), &tree(), c(0));
    conv(&g, &mm(v(0)), &mm(v(0)), &tree(), c(0));
}

// -------------------------------------------------------------------------
// What makes the arms work: `nth` and Σ-η
// -------------------------------------------------------------------------

#[test]
fn nth_projects_out_of_a_neutral_tuple() {
    // The ih side of wrinkle 6.2: at a literal arity, `nth` reduces to the
    // projections even though the tuple is a variable — so applying the
    // transient ih at a literal index lands on the actual child.
    let g = ext(&ext(&nil_ctx(), tree(), c(0)), tree(), c(0));
    let cs = pair2(v(1), v(0));
    conv(&g, &nth_tree(nat(2), cs.clone(), idx(false)), &v(1), &tree(), c(0));
    conv(&g, &nth_tree(nat(2), cs, idx(true)), &v(0), &tree(), c(0));

    // …and out of a genuinely neutral tuple, via Σ-η.
    let g2 = ext(&nil_ctx(), vec_tree(nat(2)), c(0));
    let l = nth_tree(nat(2), v(0), idx(false));
    let r = nth_tree(nat(2), v(0), idx(true));
    ck(&g2, &l, &tree(), c(0));
    ck(&g2, &r, &tree(), c(0));
    not_conv(&g2, &l, &r, &tree(), c(0));
}

#[test]
fn sigma_eta_bridges_the_constructor_form() {
    // THE property route C was chosen for, now at the real former: for a
    // *neutral* children tuple `cs`, the abstract constructor `sup_f(inr u;
    // cs)` is convertible with the concrete `node (nth 2 cs 0) (nth 2 cs 1)`.
    // Route A's analogue of this equation is what needs funext, per arm,
    // forever (`crates/elab/tests/branching_route_a.rs`).
    let g = ext(&ext(&nil_ctx(), Type::Unit, c(0)), vec_tree(nat(2)), c(0));
    let abstract_node = supf(inj(true, v(1)), v(0));
    let concrete = node(nth_tree(nat(2), v(0), idx(false)), nth_tree(nat(2), v(0), idx(true)));
    ck(&g, &abstract_node, &tree(), c(0));
    conv(&g, &abstract_node, &concrete, &tree(), c(0));

    // Arity 0 is proof-irrelevant, so *every* nullary constructor form is
    // the same leaf — no funext, no transport, and no `Empty`-η needed.
    let g0 = ext(&ext(&nil_ctx(), Type::Unit, c(0)), vec_tree(nat(0)), c(0));
    conv(&g0, &supf(inj(false, v(1)), v(0)), &leaf(), &tree(), c(0));
}

#[test]
fn layer_c_accepts_wf_and_its_constructors() {
    // Phase 2 gated these out of layer c; phase 3's codes and branches let
    // them in (docs/wf-former-design.md §6, tests/wf_codes.rs).
    let g = nil_ctx();
    check_type(&GlobalCtx::default(), 0, Layer::Code, &g, &tree(), &c(0), FUEL)
        .expect("layer c accepts Wf since phase 3");
    check_term(&GlobalCtx::default(), 0, Layer::Code, &g, &leaf(), &tree(), &c(0), FUEL)
        .expect("layer c accepts sup_f since phase 3");
}

// -------------------------------------------------------------------------
// The acceptance criterion: dependent induction, with no β-markers left
// -------------------------------------------------------------------------

fn id_tree(l: Term, r: Term) -> Type {
    Type::Id { level: c(0), ty: rty(tree()), lhs: rt(l), rhs: rt(r) }
}

fn refl_tree(t: Term) -> Term {
    Term::Refl { level: c(0), ty: rty(tree()), tm: rt(t) }
}

/// From `p : Id(x; y)`, `q : Id(y; z)`: `Id(x; z)`.
fn trans(x: Term, y: Term, z: Term, p: Term, q: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree()),
        lhs: rt(y),
        motive: rty(id_tree(x.shift_local(2), v(1))),
        case: rt(p),
        rhs: rt(z),
        proof: rt(q),
    }
}

/// From `p : Id(x; y)`: `Id(node x b; node y b)`.
fn cong_node_l(b: Term, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree()),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            node(x.clone().shift_local(2), b.clone().shift_local(2)),
            node(v(1), b.clone().shift_local(2)),
        )),
        case: rt(refl_tree(node(x, b))),
        rhs: rt(y),
        proof: rt(p),
    }
}

/// From `p : Id(x; y)`: `Id(node a x; node a y)`.
fn cong_node_r(a: Term, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree()),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            node(a.clone().shift_local(2), x.clone().shift_local(2)),
            node(a.clone().shift_local(2), v(1)),
        )),
        case: rt(refl_tree(node(a.clone(), x))),
        rhs: rt(y),
        proof: rt(p),
    }
}

/// `Γ = (t : Tree) ⊢ mirror (mirror t) = t`, by `elim_Wf` at an `Id`
/// motive. `leaf_arm` is a parameter so a negative test can show the arms
/// are load-bearing.
fn mirror_mirror(leaf_arm: Term) -> Term {
    // Case motive, binds z at (t, a, cs, ih, z) — depth 5.
    //   Π(cs' : Vec(Tree; arity z)).
    //     Π(ih' : Π(i : Fin (arity z)). Id(mm (nth _ cs' i); nth _ cs' i)).
    //       Id(mm (sup_f(z; cs')); sup_f(z; cs'))
    let ih_cod = |z: u32, cs: u32| {
        let child = nth_tree(arity_of(v(z)), v(cs), v(0));
        id_tree(mm(child.clone()), child)
    };
    let cmot = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(arity_of(v(0)))),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            // at (…, z, cs'): z = 1, cs' = 0; under i: z = 2, cs' = 1.
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(arity_of(v(1)))),
                cod: rty(ih_cod(2, 1)),
            }),
            // at (…, z, cs', ih'): z = 2, cs' = 1.
            cod: rty(id_tree(mm(supf(v(2), v(1))), supf(v(2), v(1)))),
        }),
    };

    // Leaf arm at (t, a, cs, ih, u): λcs'. λih'. <leaf_arm>.
    // The goal is Id(mm (sup_f(inl u; cs')); sup_f(inl u; cs')), and *both*
    // `u : Unit` and `cs' : Vec(Tree; 0) ≡ Unit` are proof-irrelevant, so
    // the constructor form is definitionally `leaf` and `mm leaf ⇝ leaf`.
    let arm_l = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(nat(0))),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(nat(0))),
                cod: rty({
                    let child = nth_tree(nat(0), v(1), v(0));
                    id_tree(mm(child.clone()), child)
                }),
            }),
            body: rt(leaf_arm),
        }),
    };

    // Node arm at (t, a, cs, ih, u, cs', ih') — depth 7: ih' = 0, cs' = 1.
    let l = || nth_tree(nat(2), v(1), idx(false));
    let r = || nth_tree(nat(2), v(1), idx(true));
    let ih_at = |i: Term| Term::App {
        fun: rt(v(0)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(fin(nat(2))),
        cod: rty({
            let child = nth_tree(nat(2), v(2), v(0));
            id_tree(mm(child.clone()), child)
        }),
        arg: rt(i),
    };
    // cong on the two ihs, stitched with one trans. Nothing else: the
    // constructor-form gap that route A bridges with funext is closed here
    // by conversion, so it does not appear in the proof at all.
    let node_arm = trans(
        node(mm(l()), mm(r())),
        node(l(), mm(r())),
        node(l(), r()),
        cong_node_l(mm(r()), mm(l()), l(), ih_at(idx(false))),
        cong_node_r(l(), mm(r()), r(), ih_at(idx(true))),
    );
    let arm_r = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(nat(2))),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(nat(2))),
                // under `i`: cs' = 1 (as in the Leaf arm); `ih_at` below is
                // an App whose `cod` binds its argument, so cs' = 2 there.
                cod: rty({
                    let child = nth_tree(nat(2), v(1), v(0));
                    id_tree(mm(child.clone()), child)
                }),
            }),
            body: rt(node_arm),
        }),
    };

    // Step at (t, a = 2, cs = 1, ih = 0), commuting the case over the tag.
    let cased = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(Type::Unit),
        motive: rty(cmot),
        case_l: rt(arm_l),
        case_r: rt(arm_r),
        scrut: rt(v(2)),
    };
    let at_cs = Term::App {
        fun: rt(cased),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(arity_of(v(2)))),
        // binds cs' → (t, a, cs, ih, cs'): a = 3.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(arity_of(v(3)))),
                cod: rty(ih_cod(4, 1)),
            }),
            cod: rty(id_tree(mm(supf(v(4), v(1))), supf(v(4), v(1)))),
        }),
        arg: rt(v(1)),
    };
    let step = Term::App {
        fun: rt(at_cs),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(fin(arity_of(v(2)))),
            cod: rty(ih_cod(3, 2)),
        }),
        // `cod` binds the argument, so a = 3 and cs = 2 here.
        cod: rty(id_tree(mm(supf(v(3), v(2))), supf(v(3), v(2)))),
        arg: rt(v(0)),
    };
    Term::ElimWf {
        level: c(0),
        motive_level: c(0),
        shape: rty(two()),
        arity: rt(arity_of(v(0))),
        motive: rty(id_tree(mm(v(0)), v(0))),
        step: rt(step),
        scrut: rt(v(0)),
    }
}

#[test]
fn mirror_mirror_by_induction() {
    // THE acceptance test (docs/wf-former-design.md §9). Compare with
    // `crates/elab/tests/branching_route_a.rs`, where the same theorem needs
    // a funext application in *every* arm, and the finished proof is not
    // convertible with `refl` at closed data.
    let g = ext(&nil_ctx(), tree(), c(0));
    let proof = mirror_mirror(refl_tree(leaf()));
    ck(&g, &proof, &id_tree(mm(v(0)), v(0)), c(0));
}

#[test]
fn the_leaf_arm_is_literally_refl() {
    // Route A's leaf arm needs funext because an abstract children function
    // is not convertible with leaf's stored one. Here the children are a
    // tuple at arity 0, i.e. `Unit`, so the arm's goal *is* Id(leaf; leaf)
    // and `refl leaf` closes it — recorded as its own test because it is
    // exactly the difference the decision turned on.
    let g = ext(&nil_ctx(), tree(), c(0));
    let bare_refl = refl_tree(leaf());
    ck(&g, &mirror_mirror(bare_refl), &id_tree(mm(v(0)), v(0)), c(0));
}

#[test]
fn the_kernel_gate_rejects_a_wrong_arm() {
    // The proof is doing real work: a leaf arm proving the wrong equation
    // must not check.
    let g = ext(&nil_ctx(), tree(), c(0));
    let wrong = refl_tree(node(leaf(), leaf()));
    ck_fails(&g, &mirror_mirror(wrong), &id_tree(mm(v(0)), v(0)), c(0));
    // …and `mm t = t` is not `refl` on an open `t`: the induction is needed.
    ck_fails(&g, &refl_tree(v(0)), &id_tree(mm(v(0)), v(0)), c(0));
}

