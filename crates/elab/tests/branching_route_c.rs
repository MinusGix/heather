//! Branching-inductives prototype, route C (`docs/branching-inductives-choice.md`
//! §6, de-risk plan §13 steps 1–2): the *interface* a `Wf`-style former would
//! give `Tree { Leaf, Node(Tree, Tree) }`, postulated in Ψ, with the same
//! theorem as `branching_route_a.rs` proved against it.
//!
//! Postulates: a code `treeCode : Ty 0` (so `Tree = El treeCode` — wrinkle 1
//! of §6, shapes must be code-expressible, exercised deliberately), `leaf`,
//! `node`, a motive-polymorphic dependent eliminator, and the two β laws for
//! the derived `mirror` **as propositional equalities**. Under the real
//! former the β laws are definitional; every use of one below is therefore a
//! marker reading "this step would be `refl` under route C", and the proof
//! structure that *remains* after deleting the markers is route C's honest
//! user-facing cost — to be compared with route A's arms, which keep their
//! funext/η steps forever.
//!
//! What step 2 validates: the typing interface (motive polymorphism through
//! `Ty 0` codes, the ih telescope, constructor arms) checks against the real
//! kernel. What it cannot validate (needs the former): definitional β,
//! canonical-form uniqueness, neutral-arity behaviour — those are §13 step 3.

use std::rc::Rc;

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
// Construction helpers
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
    LocalCtx { base: CtxBase::Nil, entries: vec![] }
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

// ---------------------------------------------------------------------------
// The postulated interface
// ---------------------------------------------------------------------------

// Absolute positions in Ψ (0 = outermost). `GlobalVar` indices count from
// the *last visible* binding, and inside Ψ a binding's type sees only its
// prefix — so references go through `gv`, which converts an absolute
// position to an index under the currently visible count.
const G_TREECODE: u32 = 0;
const G_LEAF: u32 = 1;
const G_NODE: u32 = 2;
const G_ELIM: u32 = 3;
const G_MBETA_LEAF: u32 = 4;
const G_MBETA_NODE: u32 = 5;

thread_local! {
    static VISIBLE: std::cell::Cell<u32> = const { std::cell::Cell::new(6) };
}

/// Build `f`'s result with `n` Ψ-bindings visible (for binding types, which
/// see only their prefix). Tests and proof terms use the default of 6.
fn with_visible<T>(n: u32, f: impl FnOnce() -> T) -> T {
    VISIBLE.with(|v| {
        let old = v.get();
        v.set(n);
        let r = f();
        v.set(old);
        r
    })
}

fn gv(pos: u32) -> u32 {
    VISIBLE.with(|v| v.get()) - 1 - pos
}

fn global(pos: u32, depth: u32) -> Term {
    Term::GlobalTm {
        var: GlobalVar(gv(pos)),
        subst: LocalSubst {
            tail: SubstTail::Empty { len: depth, base: CtxBase::Nil },
            terms: vec![],
        },
    }
}

/// `Tree = El treeCode`.
fn tree_c(depth: u32) -> Type {
    Type::El { level: c(0), tm: rt(global(G_TREECODE, depth)) }
}

fn gleaf(depth: u32) -> Term {
    global(G_LEAF, depth)
}

/// `El (m t)` for a motive term `m : Π(_ : Tree). Ty 0`.
fn el_app(m: Term, arg: Term, depth: u32) -> Type {
    Type::El {
        level: c(0),
        tm: rt(Term::App {
            fun: rt(m),
            dom_level: c(0),
            cod_level: c(1),
            dom: rty(tree_c(depth)),
            cod: rty(Type::Ty(c(0))),
            arg: rt(arg),
        }),
    }
}

/// `node l r`, fully annotated.
fn node_app(l: Term, r: Term, depth: u32) -> Term {
    let n1 = Term::App {
        fun: rt(global(G_NODE, depth)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            cod: rty(tree_c(depth + 2)),
        }),
        arg: rt(l),
    };
    Term::App {
        fun: rt(n1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        cod: rty(tree_c(depth + 1)),
        arg: rt(r),
    }
}

/// `Π(_ : Tree). Ty 0` — the motive type.
fn mot_ty(depth: u32) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(tree_c(depth)),
        cod: rty(Type::Ty(c(0))),
    }
}

/// The step type `Π(l r : Tree). El(m l) → El(m r) → El(m (node l r))`,
/// with `m` given in the scope where the whole Π sits.
fn step_ty(m: Term, depth: u32) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el_app(m.clone().shift_local(2), v(1), depth + 2)),
                cod: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(el_app(m.clone().shift_local(3), v(1), depth + 3)),
                    cod: rty(el_app(
                        m.shift_local(4),
                        node_app(v(3), v(2), depth + 4),
                        depth + 4,
                    )),
                }),
            }),
        }),
    }
}

/// The eliminator's type:
/// `Π(M : Π(_:Tree). Ty 0). El(M leaf) → step_ty(M) → Π(t : Tree). El(M t)`.
fn elim_ty(depth: u32) -> Type {
    Type::Pi {
        dom_level: c(1),
        cod_level: c(0),
        dom: rty(mot_ty(depth)),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el_app(v(0), gleaf(depth + 1), depth + 1)),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(step_ty(v(1), depth + 2)),
                cod: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(tree_c(depth + 3)),
                    cod: rty(el_app(v(3), v(0), depth + 4)),
                }),
            }),
        }),
    }
}

/// `elim m bl bn t`, fully annotated.
fn apply_elim(depth: u32, m: Term, bl: Term, bn: Term, t: Term) -> Term {
    let a1 = Term::App {
        fun: rt(global(G_ELIM, depth)),
        dom_level: c(1),
        cod_level: c(0),
        dom: rty(mot_ty(depth)),
        // binds M — the cod of `elim_ty`.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el_app(v(0), gleaf(depth + 1), depth + 1)),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(step_ty(v(1), depth + 2)),
                cod: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(tree_c(depth + 3)),
                    cod: rty(el_app(v(3), v(0), depth + 4)),
                }),
            }),
        }),
        arg: rt(m.clone()),
    };
    let a2 = Term::App {
        fun: rt(a1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el_app(m.clone(), gleaf(depth), depth)),
        // binds bl.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(step_ty(m.clone().shift_local(1), depth + 1)),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(tree_c(depth + 2)),
                cod: rty(el_app(m.clone().shift_local(3), v(0), depth + 3)),
            }),
        }),
        arg: rt(bl),
    };
    let a3 = Term::App {
        fun: rt(a2),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(step_ty(m.clone(), depth)),
        // binds bn.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            cod: rty(el_app(m.clone().shift_local(2), v(0), depth + 2)),
        }),
        arg: rt(bn),
    };
    Term::App {
        fun: rt(a3),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        // binds t.
        cod: rty(el_app(m.shift_local(1), v(0), depth + 1)),
        arg: rt(t),
    }
}

// ---------------------------------------------------------------------------
// The derived `mirror`, and the β postulates about it
// ---------------------------------------------------------------------------

/// The constant motive `λ(_ : Tree). treeCode`.
fn const_motive(depth: u32) -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(tree_c(depth)),
        body: rt(global(G_TREECODE, depth + 1)),
    }
}

/// The swapping step `λ l r ihl ihr. node ihr ihl`. The ih annotations can
/// be written at `Tree` directly because `El (const_motive x)` β-reduces.
fn swap_step(depth: u32) -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(tree_c(depth + 2)),
                body: rt(Term::Lam {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(tree_c(depth + 3)),
                    body: rt(node_app(v(0), v(1), depth + 4)),
                }),
            }),
        }),
    }
}

/// `mirror t = elim (λ_. treeCode) leaf (λ l r ihl ihr. node ihr ihl) t`.
fn mirror(depth: u32, t: Term) -> Term {
    apply_elim(depth, const_motive(depth), gleaf(depth), swap_step(depth), t)
}

fn mm(depth: u32, t: Term) -> Term {
    mirror(depth, mirror(depth, t))
}

fn id_tree(l: Term, r: Term, depth: u32) -> Type {
    Type::Id { level: c(0), ty: rty(tree_c(depth)), lhs: rt(l), rhs: rt(r) }
}

/// Ψ: the code, the constructors, the eliminator, and `mirror`'s β laws as
/// propositional postulates (each use below = "refl under the real former").
fn psi() -> GlobalCtx {
    GlobalCtx {
        bindings: vec![
            // treeCode : Ty 0
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: rty(Type::Ty(c(0))),
                level: c(1),
                body: None,
            },
            // leaf : Tree
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(1, || rty(tree_c(0))),
                level: c(0),
                body: None,
            },
            // node : Tree → Tree → Tree
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(2, || {
                    rty(Type::Pi {
                        dom_level: c(0),
                        cod_level: c(0),
                        dom: rty(tree_c(0)),
                        cod: rty(Type::Pi {
                            dom_level: c(0),
                            cod_level: c(0),
                            dom: rty(tree_c(1)),
                            cod: rty(tree_c(2)),
                        }),
                    })
                }),
                level: c(0),
                body: None,
            },
            // elim : Π(M). El(M leaf) → step → Π t. El(M t)
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(3, || rty(elim_ty(0))),
                level: c(1),
                body: None,
            },
            // mirror leaf = leaf
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(4, || rty(id_tree(mirror(0, gleaf(0)), gleaf(0), 0))),
                level: c(0),
                body: None,
            },
            // Π(l r). mirror (node l r) = node (mirror r) (mirror l)
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(5, || {
                    rty(Type::Pi {
                        dom_level: c(0),
                        cod_level: c(0),
                        dom: rty(tree_c(0)),
                        cod: rty(Type::Pi {
                            dom_level: c(0),
                            cod_level: c(0),
                            dom: rty(tree_c(1)),
                            cod: rty(id_tree(
                                mirror(2, node_app(v(1), v(0), 2)),
                                node_app(mirror(2, v(0)), mirror(2, v(1)), 2),
                                2,
                            )),
                        }),
                    })
                }),
                level: c(0),
                body: None,
            },
        ],
    }
}

/// `mbeta_node l r`, fully annotated.
fn apply_mbeta_node(depth: u32, l: Term, r: Term) -> Term {
    let m1 = Term::App {
        fun: rt(global(G_MBETA_NODE, depth)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        // binds l.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            cod: rty(id_tree(
                mirror(depth + 2, node_app(v(1), v(0), depth + 2)),
                node_app(mirror(depth + 2, v(0)), mirror(depth + 2, v(1)), depth + 2),
                depth + 2,
            )),
        }),
        arg: rt(l.clone()),
    };
    Term::App {
        fun: rt(m1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        // binds r.
        cod: rty(id_tree(
            mirror(depth + 1, node_app(l.clone().shift_local(1), v(0), depth + 1)),
            node_app(
                mirror(depth + 1, v(0)),
                mirror(depth + 1, l.shift_local(1)),
                depth + 1,
            ),
            depth + 1,
        )),
        arg: rt(r),
    }
}

// ---------------------------------------------------------------------------
// Identity helpers at `Tree`
// ---------------------------------------------------------------------------

fn refl_tree(t: Term, depth: u32) -> Term {
    Term::Refl { level: c(0), ty: rty(tree_c(depth)), tm: rt(t) }
}

/// From `p : Id(x; y)`, `q : Id(y; z)`: `Id(x; z)`.
fn trans_tree(depth: u32, x: Term, y: Term, z: Term, p: Term, q: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_c(depth)),
        lhs: rt(y),
        motive: rty(id_tree(x.clone().shift_local(2), v(1), depth + 2)),
        case: rt(p),
        rhs: rt(z),
        proof: rt(q),
    }
}

/// From `p : Id(x; y)`: `Id(mirror x; mirror y)`.
fn cong_mirror(depth: u32, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_c(depth)),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            mirror(depth + 2, x.clone().shift_local(2)),
            mirror(depth + 2, v(1)),
            depth + 2,
        )),
        case: rt(refl_tree(mirror(depth, x), depth)),
        rhs: rt(y),
        proof: rt(p),
    }
}

/// From `p : Id(x; y)`: `Id(node x b; node y b)`.
fn cong_node_l(depth: u32, b: Term, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_c(depth)),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            node_app(x.clone().shift_local(2), b.clone().shift_local(2), depth + 2),
            node_app(v(1), b.clone().shift_local(2), depth + 2),
            depth + 2,
        )),
        case: rt(refl_tree(node_app(x, b, depth), depth)),
        rhs: rt(y),
        proof: rt(p),
    }
}

/// From `p : Id(x; y)`: `Id(node a x; node a y)`.
fn cong_node_r(depth: u32, a: Term, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_c(depth)),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            node_app(a.clone().shift_local(2), x.clone().shift_local(2), depth + 2),
            node_app(a.clone().shift_local(2), v(1), depth + 2),
            depth + 2,
        )),
        case: rt(refl_tree(node_app(a, x, depth), depth)),
        rhs: rt(y),
        proof: rt(p),
    }
}

// ---------------------------------------------------------------------------
// The theorem: `Γ = (t : Tree) ⊢ mirror (mirror t) = t`
// ---------------------------------------------------------------------------

/// The induction motive as a code: `λ z. ⌜Id(Tree; mm z; z)⌝`.
fn thm_motive(depth: u32) -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(tree_c(depth)),
        body: rt(Term::TmId {
            level: c(0),
            ty: rt(global(G_TREECODE, depth + 1)),
            lhs: rt(mm(depth + 1, v(0))),
            rhs: rt(v(0)),
        }),
    }
}

/// The Leaf arm: goal `Id(mm leaf; leaf)`. Under the real former this is
/// `refl leaf`; here it is two β-markers stitched with cong and trans.
fn leaf_arm(depth: u32) -> Term {
    let ml = mirror(depth, gleaf(depth));
    let p1 = global(G_MBETA_LEAF, depth);
    let p2 = cong_mirror(depth, ml.clone(), gleaf(depth), p1.clone());
    trans_tree(depth, mm(depth, gleaf(depth)), ml, gleaf(depth), p2, p1)
}

/// The Node arm body, scope (…, l, r, ihl, ihr): goal
/// `Id(mm (node l r); node l r)`. Under the real former only q5–q7 remain
/// (cong twice on the ihs, one trans) — q1–q4 are β-markers.
fn node_arm(depth: u32) -> Term {
    let d = depth + 4;
    let (l, r, ihl, ihr) = (v(3), v(2), v(1), v(0));
    let nlr = node_app(l.clone(), r.clone(), d);
    let (ml, mr) = (mirror(d, l.clone()), mirror(d, r.clone()));
    let (mml, mmr) = (mm(d, l.clone()), mm(d, r.clone()));
    let q1 = apply_mbeta_node(d, l.clone(), r.clone());
    let q2 = cong_mirror(
        d,
        mirror(d, nlr.clone()),
        node_app(mr.clone(), ml.clone(), d),
        q1,
    );
    let q3 = apply_mbeta_node(d, mr.clone(), ml.clone());
    let q4 = trans_tree(
        d,
        mm(d, nlr.clone()),
        mirror(d, node_app(mr, ml, d)),
        node_app(mml.clone(), mmr.clone(), d),
        q2,
        q3,
    );
    let q5 = cong_node_l(d, mmr.clone(), mml.clone(), l.clone(), ihl);
    let q6 = cong_node_r(d, l.clone(), mmr.clone(), r.clone(), ihr);
    let q7 = trans_tree(
        d,
        node_app(mml.clone(), mmr.clone(), d),
        node_app(l.clone(), mmr.clone(), d),
        nlr.clone(),
        q5,
        q6,
    );
    trans_tree(d, mm(d, nlr.clone()), node_app(mml, mmr, d), nlr, q4, q7)
}

/// The full proof, in `Γ = (t : Tree)`.
fn mirror_mirror_proof() -> Term {
    let depth = 1;
    // The step lambda: annotations at `Tree` / the reduced ih types.
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                // ihl : Id(mm l; l), scope (t, l, r): l = v(1).
                dom: rty(id_tree(mm(depth + 2, v(1)), v(1), depth + 2)),
                body: rt(Term::Lam {
                    dom_level: c(0),
                    cod_level: c(0),
                    // ihr : Id(mm r; r), scope (t, l, r, ihl): r = v(1).
                    dom: rty(id_tree(mm(depth + 3, v(1)), v(1), depth + 3)),
                    body: rt(node_arm(depth)),
                }),
            }),
        }),
    };
    apply_elim(depth, thm_motive(depth), leaf_arm(depth), step, v(0))
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck_in(psi: &GlobalCtx, gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(psi, 0, Layer::Prog, gamma, ty, &level, FUEL).expect("the type is well-formed");
    check_term(psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn the_postulated_interface_checks() {
    check_global_ctx(&psi(), 0, FUEL).unwrap();
}

#[test]
fn constructors_and_mirror_check() {
    let psi = psi();
    let g = nil_ctx();
    let t = node_app(gleaf(0), node_app(gleaf(0), gleaf(0), 0), 0);
    ck_in(&psi, &g, &t, &tree_c(0), c(0));
    ck_in(&psi, &g, &mirror(0, t.clone()), &tree_c(0), c(0));
    // With the interface postulated, `mirror` on closed data is *stuck* —
    // the whole point of §13 step 3 is that the real former makes this
    // conversion definitional. Pinned so the file is honest about what the
    // postulate prototype does and does not show.
    conv_term(
        &psi,
        &g,
        Layer::Prog,
        &mirror(0, t),
        &node_app(node_app(gleaf(0), gleaf(0), 0), gleaf(0), 0),
        &tree_c(0),
        &c(0),
        FUEL,
    )
    .expect_err("postulated elim cannot compute; the real former would");
}

#[test]
fn mirror_mirror_by_induction_against_the_interface() {
    // Γ = (t : Tree) ⊢ mirror (mirror t) = t. The arm structure that
    // survives deleting the β-markers — refl for Leaf; cong twice plus one
    // trans for Node — is route C's user-facing proof, with no funext and no
    // η anywhere.
    let psi = psi();
    let g = ext(&nil_ctx(), tree_c(0), c(0));
    let proof = mirror_mirror_proof();
    let goal = id_tree(mm(1, v(0)), v(0), 1);
    ck_in(&psi, &g, &proof, &goal, c(0));
}

#[test]
fn the_kernel_gate_rejects_a_swapped_ih() {
    // Negative control: use ihr where ihl is needed (congruence on the wrong
    // side) — the checker must reject the node arm.
    let psi = psi();
    let g = ext(&nil_ctx(), tree_c(0), c(0));
    let depth = 1;
    let bad_step = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(id_tree(mm(depth + 2, v(1)), v(1), depth + 2)),
                body: rt(Term::Lam {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(id_tree(mm(depth + 3, v(1)), v(1), depth + 3)),
                    // ihl and ihr swapped relative to `node_arm`.
                    body: {
                        let d = depth + 4;
                        let (l, r) = (v(3), v(2));
                        let nlr = node_app(l.clone(), r.clone(), d);
                        let (mml, mmr) = (mm(d, l.clone()), mm(d, r.clone()));
                        let q5 = cong_node_l(d, mmr.clone(), mml.clone(), l.clone(), v(0));
                        let q6 = cong_node_r(d, l.clone(), mmr.clone(), r.clone(), v(1));
                        let q7 = trans_tree(
                            d,
                            node_app(mml.clone(), mmr.clone(), d),
                            node_app(l.clone(), mmr.clone(), d),
                            nlr.clone(),
                            q5,
                            q6,
                        );
                        let q1 = apply_mbeta_node(d, l.clone(), r.clone());
                        let q2 = cong_mirror(
                            d,
                            mirror(d, nlr.clone()),
                            node_app(mirror(d, r.clone()), mirror(d, l.clone()), d),
                            q1,
                        );
                        let q3 =
                            apply_mbeta_node(d, mirror(d, r.clone()), mirror(d, l.clone()));
                        let q4 = trans_tree(
                            d,
                            mm(d, nlr.clone()),
                            mirror(d, node_app(mirror(d, r), mirror(d, l), d)),
                            node_app(mml.clone(), mmr.clone(), d),
                            q2,
                            q3,
                        );
                        rt(trans_tree(
                            d,
                            mm(d, nlr.clone()),
                            node_app(mml, mmr, d),
                            nlr,
                            q4,
                            q7,
                        ))
                    },
                }),
            }),
        }),
    };
    let bad = apply_elim(depth, thm_motive(depth), leaf_arm(depth), bad_step, v(0));
    let goal = id_tree(mm(1, v(0)), v(0), 1);
    check_term(&psi, 0, Layer::Prog, &g, &bad, &goal, &c(0), FUEL)
        .expect_err("the kernel gate must reject the swapped ihs");
}
