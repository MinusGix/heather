//! Branching-inductives prototype, route A (`docs/branching-inductives-choice.md` §4):
//! `Tree { Leaf, Node(Tree, Tree) }` as a container on the kernel's `W`,
//! with funext postulated in Ψ where the dependent eliminator needs it.
//!
//! The point is evidence, not machinery: validate exactly which of route A's
//! promised behaviours hold against the real checker —
//!
//! 1. constructors are `sup` forms and `match` β-reduces **on open subterms**
//!    (no funext anywhere): `mirror (node l r) ≡ node (mirror r) (mirror l)`
//!    with `l`, `r` variables;
//! 2. non-dependent recursion computes definitionally on closed data;
//! 3. the **dependent** induction `mirror (mirror t) = t` goes through, but
//!    every constructor arm — including `leaf`'s — routes through a
//!    postulated funext instance and a transport that will never reduce.
//!
//! Companion: `branching_route_c.rs` proves the same theorem against a
//! postulated `Wf`-style interface for comparison.
//!
//! Shape `S = Unit + Unit` (`inl` = Leaf, `inr` = Node); positions
//! `P (inl _) = Empty`, `P (inr _) = Unit + Unit`, via large elimination to
//! `Ty 0` and `El`.

use std::sync::Arc as Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{check_global_ctx, check_term, check_type};

const FUEL: u64 = 1_000_000;

// ---------------------------------------------------------------------------
// Construction helpers (as in tier1_fording.rs)
// ---------------------------------------------------------------------------

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
    LocalCtx::nil()
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

// ---------------------------------------------------------------------------
// The container: shapes, positions, the W type
// ---------------------------------------------------------------------------

/// `2 = Unit + Unit`.
fn two() -> Type {
    Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
    }
}

fn inl_triv() -> Term {
    Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        val: rt(Term::Triv { level: Level::Zero }),
    }
}

fn inr_triv() -> Term {
    Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        val: rt(Term::Triv { level: Level::Zero }),
    }
}

/// `P x = El (case x of inl _ => ⌜Empty⌝ | inr _ => ⌜Unit + Unit⌝)` — arity 0
/// for Leaf, arity 2 for Node.
fn pos_of(x: Term) -> Type {
    Type::El {
        level: c(0),
        tm: rt(Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: c(1),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Unit { level: Level::Zero }),
            motive: rty(Type::Ty(c(0))),
            case_l: rt(Term::TmEmpty { level: Level::Zero }),
            case_r: rt(Term::TmSum {
                lhs_level: c(0),
                rhs_level: c(0),
                lhs: rt(Term::TmUnit { level: Level::Zero }),
                rhs: rt(Term::TmUnit { level: Level::Zero }),
            }),
            scrut: rt(x),
        }),
    }
}

/// `Tree = W^{0,0}(x : 2). P x`.
fn tree() -> Type {
    Type::W {
        shape_level: c(0),
        pos_level: c(0),
        shape: rty(two()),
        pos: rty(pos_of(v(0))),
    }
}

fn sup(label: Term, children: Term) -> Term {
    Term::Sup {
        shape_level: c(0),
        pos_level: c(0),
        shape_ty: rty(two()),
        pos_ty: rty(pos_of(v(0))),
        label: rt(label),
        children: rt(children),
    }
}

/// `Π(y : dom). Tree`.
fn children_pi(dom: Type) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(dom),
        cod: rty(tree()),
    }
}

/// `leaf = sup(inl ⟨⟩; λ(y : Empty). elim_Empty y)`.
fn leaf() -> Term {
    sup(
        inl_triv(),
        Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Empty { level: Level::Zero }),
            body: rt(Term::ElimEmpty {
                level: c(0),
            scrut_level: Level::Zero,
                motive: rty(tree()),
                scrut: rt(v(0)),
            }),
        },
    )
}

/// The canonical children function of a `node`: `λ(y : 2). case y of
/// inl _ => l | inr _ => r`. `l`, `r` are scoped *outside* and get shifted
/// under the λ and the case arm.
fn node_children(l: Term, r: Term) -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        body: rt(Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Unit { level: Level::Zero }),
            motive: rty(tree()),
            case_l: rt(l.shift_local(2)),
            case_r: rt(r.shift_local(2)),
            scrut: rt(v(0)),
        }),
    }
}

/// `node l r = sup(inr ⟨⟩; node_children l r)`.
fn node(l: Term, r: Term) -> Term {
    sup(inr_triv(), node_children(l, r))
}

/// Fully annotated application at `Π(y : dom). Tree`.
fn app_tree(f: Term, dom: Type, arg: Term) -> Term {
    Term::App {
        fun: rt(f),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(dom),
        cod: rty(tree()),
        arg: rt(arg),
    }
}

// ---------------------------------------------------------------------------
// Non-dependent recursion: `mirror`
// ---------------------------------------------------------------------------

/// `mirror t` — swap every node's children, by `elim_W` at the constant
/// motive `Tree`.
///
/// The step must consume `ih : Π(y : P a). Tree` at an *abstract* shape `a`,
/// so it commutes the case over `a` first, generalizing `ih` in the motive —
/// inside each arm `P (inl u)` / `P (inr u)` reduces and `ih'` is applicable.
/// This is pure plumbing (no funext): the constant motive never mentions the
/// scrutinee.
fn mirror(scrut: Term) -> Term {
    // Case motive, binds (z : 2): `Π(ih' : Π(y : P z). Tree). Tree`.
    let case_motive = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(pos_of(v(0)))),
        cod: rty(tree()),
    };
    // inl arm, binds (u : Unit): `λ(ih' : Π(y : Empty). Tree). leaf`.
    let arm_leaf = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(Type::Empty { level: Level::Zero })),
        body: rt(leaf()),
    };
    // inr arm, binds (u : Unit):
    // `λ(ih' : Π(y : 2). Tree). node (ih' (inr ⟨⟩)) (ih' (inl ⟨⟩))`.
    let arm_node = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(two())),
        body: rt(node(
            app_tree(v(0), two(), inr_triv()),
            app_tree(v(0), two(), inl_triv()),
        )),
    };
    // Step, binds (a = 2, f = 1, ih = 0): case a (generalizing ih), then
    // apply to ih.
    let cased = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        motive: rty(case_motive),
        case_l: rt(arm_leaf),
        case_r: rt(arm_node),
        scrut: rt(v(2)),
    };
    let step = Term::App {
        fun: rt(cased),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(pos_of(v(2)))),
        cod: rty(tree()),
        arg: rt(v(0)),
    };
    Term::ElimW {
        shape_level: c(0),
        pos_level: c(0),
        motive_level: c(0),
        shape: rty(two()),
        pos: rty(pos_of(v(0))),
        motive: rty(tree()),
        step: rt(step),
        scrut: rt(scrut),
    }
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck_in(psi: &GlobalCtx, gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(psi, 0, Layer::Prog, gamma, ty, &level, FUEL).expect("the type is well-formed");
    check_term(psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    ck_in(&GlobalCtx::default(), gamma, t, ty, level);
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

// ---------------------------------------------------------------------------
// Stage 3: funext in Ψ, and the dependent induction `mirror (mirror t) = t`
// ---------------------------------------------------------------------------

fn id_tree(l: Term, r: Term) -> Type {
    Type::Id { level: c(0), ty: rty(tree()), lhs: rt(l), rhs: rt(r) }
}

fn mm(x: Term) -> Term {
    mirror(mirror(x))
}

/// funext at domain `d`, codomain `Tree`:
/// `Π(F G : d → Tree). (Π(y : d). Id(Tree; F y; G y)) → Id(d → Tree; F; G)`.
///
/// The real axiom would be schematic; the prototype postulates the two
/// instances `Tree`'s recursor needs (`Empty` for Leaf, `2` for Node) — one
/// per constructor, which is itself a datapoint about what a generator
/// would have to mint.
fn funext_ty(d: &Type) -> Type {
    let ft = || children_pi(d.clone());
    // scope (F, G), binds y.
    let pw = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(d.clone()),
        cod: rty(id_tree(
            app_tree(v(2), d.clone(), v(0)),
            app_tree(v(1), d.clone(), v(0)),
        )),
    };
    Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(ft()),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(ft()),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(pw),
                cod: rty(Type::Id {
                    level: c(0),
                    ty: rty(ft()),
                    lhs: rt(v(2)),
                    rhs: rt(v(1)),
                }),
            }),
        }),
    }
}

const FUNEXT_EMPTY: u32 = 1;
const FUNEXT_TWO: u32 = 0;

/// Ψ = (funext at `Empty → Tree`, funext at `2 → Tree`).
fn psi() -> GlobalCtx {
    GlobalCtx::new(vec![
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: rty(funext_ty(&Type::Empty { level: Level::Zero })),
                level: c(0),
                body: None,
            },
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: rty(funext_ty(&two())),
                level: c(0),
                body: None,
            },
        ])
}

fn global(var: u32, depth: u32) -> Term {
    Term::GlobalTm {
        var: GlobalVar(var),
        subst: LocalSubst {
            tail: SubstTail::Empty,
            terms: vec![],
        },
    }
}

/// `funext_d f g pw`, fully annotated.
fn apply_funext(gvar: u32, depth: u32, d: &Type, f: Term, g: Term, pw: Term) -> Term {
    let ft = || children_pi(d.clone());
    // The generic pointwise type, scope (F, G): as in `funext_ty`.
    let pw_gen = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(d.clone()),
        cod: rty(id_tree(
            app_tree(v(2), d.clone(), v(0)),
            app_tree(v(1), d.clone(), v(0)),
        )),
    };
    let app1 = Term::App {
        fun: rt(global(gvar, depth)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(ft()),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(ft()),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(pw_gen),
                cod: rty(Type::Id {
                    level: c(0),
                    ty: rty(ft()),
                    lhs: rt(v(2)),
                    rhs: rt(v(1)),
                }),
            }),
        }),
        arg: rt(f.clone()),
    };
    let app2 = Term::App {
        fun: rt(app1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(ft()),
        // binds G; `f` shifts under G (and y / H below).
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(d.clone()),
                cod: rty(id_tree(
                    app_tree(f.clone().shift_local(2), d.clone(), v(0)),
                    app_tree(v(1), d.clone(), v(0)),
                )),
            }),
            cod: rty(Type::Id {
                level: c(0),
                ty: rty(ft()),
                lhs: rt(f.clone().shift_local(2)),
                rhs: rt(v(1)),
            }),
        }),
        arg: rt(g.clone()),
    };
    Term::App {
        fun: rt(app2),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(d.clone()),
            cod: rty(id_tree(
                app_tree(f.clone().shift_local(1), d.clone(), v(0)),
                app_tree(g.clone().shift_local(1), d.clone(), v(0)),
            )),
        }),
        // binds the pointwise witness; the result does not mention it.
        cod: rty(Type::Id {
            level: c(0),
            ty: rty(ft()),
            lhs: rt(f.shift_local(1)),
            rhs: rt(g.shift_local(1)),
        }),
        arg: rt(pw),
    }
}

/// From `p : Id(Tree; x; y)` and `q : Id(Tree; y; z)`: `Id(Tree; x; z)`.
fn trans_tree(x: Term, y: Term, z: Term, p: Term, q: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree()),
        lhs: rt(y),
        motive: rty(id_tree(x.clone().shift_local(2), v(1))),
        case: rt(p),
        rhs: rt(z),
        proof: rt(q),
    }
}

fn refl_tree(t: Term) -> Term {
    Term::Refl { level: c(0), ty: rty(tree()), tm: rt(t) }
}

/// From `p : Id(d → Tree; f; g)`: `Id(Tree; sup(tag; f); sup(tag; g))`.
fn cong_sup(tag: Term, d: &Type, f: Term, g: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(children_pi(d.clone())),
        lhs: rt(f.clone()),
        motive: rty(id_tree(
            sup(tag.clone().shift_local(2), f.clone().shift_local(2)),
            sup(tag.clone().shift_local(2), v(1)),
        )),
        case: rt(refl_tree(sup(tag, f))),
        rhs: rt(g),
        proof: rt(p),
    }
}

/// From `p : Id(Tree; x; y)`: `Id(Tree; node x b; node y b)`.
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
        case: rt(refl_tree(node(x, b.clone()))),
        rhs: rt(y),
        proof: rt(p),
    }
}

/// From `p : Id(Tree; x; y)`: `Id(Tree; node a x; node a y)`.
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

/// The children function `leaf` stores.
fn leaf_children() -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Empty { level: Level::Zero }),
        body: rt(Term::ElimEmpty { level: c(0),
            scrut_level: Level::Zero, motive: rty(tree()), scrut: rt(v(0)) }),
    }
}

/// `Id(Tree; leaf; sup(inl ⟨⟩; fp))` for `fp : Empty → Tree` in scope.
/// One funext application — the Leaf arm is NOT free (absent `Empty`-η).
fn eta_leaf(depth: u32, fp: Term) -> Term {
    // λ(y : Empty). elim_Empty(z. Id(Tree; leaf_children z; fp z); y)
    let pw = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Empty { level: Level::Zero }),
        body: rt(Term::ElimEmpty {
            level: c(0),
            scrut_level: Level::Zero,
            motive: rty(id_tree(
                app_tree(leaf_children(), Type::Empty { level: Level::Zero }, v(0)),
                app_tree(fp.clone().shift_local(2), Type::Empty { level: Level::Zero }, v(0)),
            )),
            scrut: rt(v(0)),
        }),
    };
    let eq_fun = apply_funext(FUNEXT_EMPTY, depth, &Type::Empty { level: Level::Zero }, leaf_children(), fp.clone(), pw);
    cong_sup(inl_triv(), &Type::Empty { level: Level::Zero }, leaf_children(), fp, eq_fun)
}

/// `Id(Tree; node (fp (inl ⟨⟩)) (fp (inr ⟨⟩)); sup(inr ⟨⟩; fp))` for
/// `fp : 2 → Tree` in scope. One funext application; the pointwise family is
/// a dependent case whose arms are `refl` after β.
fn eta_node(depth: u32, fp: Term) -> Term {
    let a = app_tree(fp.clone(), two(), inl_triv());
    let b = app_tree(fp.clone(), two(), inr_triv());
    let nc = node_children(a.clone(), b.clone());
    // λ(y : 2). case y of (z. Id(Tree; nc z; fp z)) | inl _ => refl | inr _ => refl
    let pw = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        body: rt(Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Unit { level: Level::Zero }),
            motive: rty(id_tree(
                app_tree(nc.clone().shift_local(2), two(), v(0)),
                app_tree(fp.clone().shift_local(2), two(), v(0)),
            )),
            case_l: rt(refl_tree(app_tree(fp.clone().shift_local(2), two(), inl_triv()))),
            case_r: rt(refl_tree(app_tree(fp.clone().shift_local(2), two(), inr_triv()))),
            scrut: rt(v(0)),
        }),
    };
    let eq_fun = apply_funext(FUNEXT_TWO, depth, &two(), nc.clone(), fp.clone(), pw);
    cong_sup(inr_triv(), &two(), nc, fp, eq_fun)
}

/// `Π(y : d). Id(Tree; mm (f' y); f' y)` — the ih annotation used in the
/// arms, where the enclosing binder is `f'`.
fn ih_pi_ty(d: &Type) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(d.clone()),
        cod: rty(id_tree(
            mm(app_tree(v(1), d.clone(), v(0))),
            app_tree(v(1), d.clone(), v(0)),
        )),
    }
}

/// `Γ = (t : Tree) ⊢ mirror (mirror t) = t`, by dependent `elim_W` with the
/// case commuted over the shape (generalizing `f` and `ih` in the motive).
fn mirror_mirror_proof() -> Term {
    mirror_mirror_proof_with_leaf_arm(eta_leaf(7, v(1)))
}

/// Same, with the Leaf arm's body swappable so a test can pin that the
/// funext there is load-bearing.
fn mirror_mirror_proof_with_leaf_arm(leaf_body: Term) -> Term {
    // Leaf arm, scope (t, a, f, ih, u, f', ih') — depth 7, f' = v(1).
    // Goal: Id(Tree; mm (sup(inl u; f')); sup(inl u; f')). The LHS computes
    // to `leaf`; the remaining gap is exactly `eta_leaf` — a funext use in
    // the arm that "should" be trivial.
    let arm_leaf = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(Type::Empty { level: Level::Zero })),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(ih_pi_ty(&Type::Empty { level: Level::Zero })),
            body: rt(leaf_body),
        }),
    };

    // Node arm, same scope: ih' = v(0), f' = v(1).
    // Goal: Id(Tree; mm (sup(inr u; f')); sup(inr u; f')); the LHS computes
    // to node (mm (f' (inl ⟨⟩))) (mm (f' (inr ⟨⟩))); cong twice on the ihs,
    // then `eta_node`.
    let a_ = app_tree(v(1), two(), inl_triv());
    let b_ = app_tree(v(1), two(), inr_triv());
    let (mma, mmb) = (mm(a_.clone()), mm(b_.clone()));
    let ih_at = |arg: Term| Term::App {
        fun: rt(v(0)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        cod: rty(id_tree(
            mm(app_tree(v(2), two(), v(0))),
            app_tree(v(2), two(), v(0)),
        )),
        arg: rt(arg),
    };
    let e1 = cong_node_l(mmb.clone(), mma.clone(), a_.clone(), ih_at(inl_triv()));
    let e2 = cong_node_r(a_.clone(), mmb.clone(), b_.clone(), ih_at(inr_triv()));
    let e3 = trans_tree(
        node(mma.clone(), mmb.clone()),
        node(a_.clone(), mmb.clone()),
        node(a_.clone(), b_.clone()),
        e1,
        e2,
    );
    let e4 = eta_node(7, v(1));
    let e5 = trans_tree(node(mma, mmb), node(a_, b_), sup(inr_triv(), v(1)), e3, e4);
    let arm_node = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(two())),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(ih_pi_ty(&two())),
            body: rt(e5),
        }),
    };

    // Case motive, binds (z2 : 2):
    // Π(f' : Π(y : P z2). Tree).
    //   Π(ih' : Π(y : P z2). Id(mm (f' y); f' y)).
    //     Id(mm (sup(z2; f')); sup(z2; f'))
    let papp = |f_idx: u32, z2_idx: u32| Term::App {
        fun: rt(v(f_idx)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(pos_of(v(z2_idx))),
        cod: rty(tree()),
        arg: rt(v(0)),
    };
    let case_motive = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(pos_of(v(0)))),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            // scope (z2, f'), binds y: z2 = v(2), f' = v(1).
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(pos_of(v(1))),
                cod: rty(id_tree(mm(papp(1, 2)), papp(1, 2))),
            }),
            // scope (z2, f', ih'): z2 = v(2), f' = v(1).
            cod: rty(id_tree(mm(sup(v(2), v(1))), sup(v(2), v(1)))),
        }),
    };

    // Step, scope (t, a, f, ih): a = v(2), f = v(1), ih = v(0).
    let cased = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        motive: rty(case_motive),
        case_l: rt(arm_leaf),
        case_r: rt(arm_node),
        scrut: rt(v(2)),
    };
    let app_f = Term::App {
        fun: rt(cased),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(children_pi(pos_of(v(2)))),
        // binds f' (= the arg); scope (t, a, f, ih, f'): a = v(3).
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(pos_of(v(3))),
                cod: rty(id_tree(mm(papp(1, 4)), papp(1, 4))),
            }),
            cod: rty(id_tree(mm(sup(v(4), v(1))), sup(v(4), v(1)))),
        }),
        arg: rt(v(1)),
    };
    let app_ih = Term::App {
        fun: rt(app_f),
        dom_level: c(0),
        cod_level: c(0),
        // ih : Π(y : P a). Id(mm (f y); f y); under y: a = v(3), f = v(2).
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(pos_of(v(2))),
            cod: rty(id_tree(mm(papp(2, 3)), papp(2, 3))),
        }),
        // binds the arg; scope (t, a, f, ih, x): a = v(3), f = v(2).
        cod: rty(id_tree(mm(sup(v(3), v(2))), sup(v(3), v(2)))),
        arg: rt(v(0)),
    };
    Term::ElimW {
        shape_level: c(0),
        pos_level: c(0),
        motive_level: c(0),
        shape: rty(two()),
        pos: rty(pos_of(v(0))),
        motive: rty(id_tree(mm(v(0)), v(0))),
        step: rt(app_ih),
        scrut: rt(v(0)),
    }
}

fn not_conv_in(psi: &GlobalCtx, gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(psi, gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

// ---------------------------------------------------------------------------
// Stage 1–2 tests: the encoding, and what computes without funext
// ---------------------------------------------------------------------------

#[test]
fn the_type_and_the_constructors_check() {
    let g = nil_ctx();
    ck(&g, &leaf(), &tree(), c(0));
    ck(&g, &node(leaf(), leaf()), &tree(), c(0));
    ck(&g, &node(node(leaf(), leaf()), leaf()), &tree(), c(0));
}

#[test]
fn node_on_open_children_checks() {
    // Γ = (l r : Tree) ⊢ node l r : Tree — constructor form whatever the
    // children are; this is what the finitary encodings could not do.
    let g = ext(&ext(&nil_ctx(), tree(), c(0)), tree(), c(0));
    ck(&g, &node(v(1), v(0)), &tree(), c(0));
}

#[test]
fn generated_canonical_forms_are_unique() {
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
fn mirror_checks_and_computes_on_closed_data() {
    let g = nil_ctx();
    let t = node(node(leaf(), leaf()), leaf());
    ck(&g, &mirror(t.clone()), &tree(), c(0));
    conv(
        &g,
        &mirror(t),
        &node(leaf(), node(leaf(), leaf())),
        &tree(),
        c(0),
    );
    conv(&g, &mirror(leaf()), &leaf(), &tree(), c(0));
}

#[test]
fn mirror_beta_fires_on_open_children() {
    // Γ = (l r : Tree) ⊢ mirror (node l r) ≡ node (mirror r) (mirror l) —
    // route A's headline: `match` on a constructor β-reduces with open
    // subterms, no funext anywhere in sight.
    let g = ext(&ext(&nil_ctx(), tree(), c(0)), tree(), c(0));
    let lhs = mirror(node(v(1), v(0)));
    let rhs = node(mirror(v(0)), mirror(v(1)));
    ck(&g, &lhs, &tree(), c(0));
    conv(&g, &lhs, &rhs, &tree(), c(0));
    // …and on an open scrutinee it is neutral but typed.
    ck(&g, &mirror(v(0)), &tree(), c(0));
}

// ---------------------------------------------------------------------------
// Stage 3 tests: the dependent induction, and what it costs
// ---------------------------------------------------------------------------

#[test]
fn the_funext_postulates_check() {
    let psi = psi();
    check_global_ctx(&psi, 0, FUEL).unwrap();
}

#[test]
fn mirror_mirror_by_induction_with_funext() {
    // Γ = (t : Tree) ⊢ mirror (mirror t) = t. Route A's dependent
    // elimination: it goes through, with one funext application per
    // constructor arm — including Leaf's.
    let psi = psi();
    let g = ext(&nil_ctx(), tree(), c(0));
    let proof = mirror_mirror_proof();
    let goal = id_tree(mm(v(0)), v(0));
    ck_in(&psi, &g, &proof, &goal, c(0));
}

#[test]
fn the_leaf_arm_funext_is_load_bearing() {
    // Replace the Leaf arm's η-bridge with a bare `refl leaf` — the kernel
    // must reject it: `f'` is an abstract `Empty → Tree` and without
    // `Empty`-η it is not convertible with leaf's stored children function.
    let psi = psi();
    let g = ext(&nil_ctx(), tree(), c(0));
    let bad = mirror_mirror_proof_with_leaf_arm(refl_tree(leaf()));
    let goal = id_tree(mm(v(0)), v(0));
    check_term(&psi, 0, Layer::Prog, &g, &bad, &goal, &c(0), FUEL)
        .expect_err("the kernel gate must reject the refl leaf arm");
}

#[test]
fn dependent_recursion_does_not_compute() {
    // Route A's admitted cost, pinned: instantiate the induction at the
    // *closed* scrutinee `leaf`. The proof term still checks, but it reduces
    // to a stuck funext application — it is NOT convertible with `refl`,
    // even though both inhabit `Id(Tree; leaf; leaf)` after reduction.
    let psi = psi();
    let g = nil_ctx();
    let proof_at_leaf =
        mirror_mirror_proof().apply_local(&LocalSubst::id(&nil_ctx()).extended(rt(leaf())));
    let goal = id_tree(mm(leaf()), leaf());
    ck_in(&psi, &g, &proof_at_leaf, &goal, c(0));
    not_conv_in(&psi, &g, &proof_at_leaf, &refl_tree(leaf()), &goal, c(0));
}
