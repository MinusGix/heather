//! `Wf` elimination at depth — the branching-inductive substrate
//! (`docs/kernel/wf-former-design.md`, [[branching-inductives-decision]]). Every
//! user-declared branching datatype compiles through this former, so its
//! elimination cost is the cost of running generated recursors.
//!
//! The `Tree`/`mirror` machinery below is the working example of
//! `tests/wf.rs`, re-transcribed here and parameterized by depth. The
//! duplication is deliberate and cheap to keep honest: the involution
//! `mirror (mirror t) ≡ t` is asserted at setup, so a copy that drifted from
//! the tested one stops the bench instead of quietly measuring nonsense.

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, Term, Type};
use heather_kernel::typing::check_term;

use super::terms::{c, nil_ctx, num, rt, rty, v};
use super::FUEL;
use crate::common::count_term;
use crate::harness::{Case, Family};

const DEPTHS: [u32; 4] = [2, 3, 4, 5];

pub fn families() -> Vec<Family> {
    vec![check(), involution()]
}

// -------------------------------------------------------------------------
// Tree = Wf^0(x : Unit + Unit). case x of inl _ ⇒ 0 | inr _ ⇒ 2
// -------------------------------------------------------------------------

fn two() -> Type {
    Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
    }
}

fn triv() -> Term {
    Term::Triv { level: Level::Zero }
}

fn inj(right: bool, val: Term) -> Term {
    let (lhs, rhs) = (rty(Type::Unit { level: Level::Zero }), rty(Type::Unit { level: Level::Zero }));
    if right {
        Term::Inr { lhs_level: c(0), rhs_level: c(0), lhs, rhs, val: rt(val) }
    } else {
        Term::Inl { lhs_level: c(0), rhs_level: c(0), lhs, rhs, val: rt(val) }
    }
}

/// `arity a = case a of inl _ ⇒ 0 | inr _ ⇒ 2`.
fn arity_of(scrut: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        motive: rty(Type::Nat),
        case_l: rt(Term::Zero),
        case_r: rt(num(2)),
        scrut: rt(scrut),
    }
}

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

fn vec_tree(len: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(tree()), len: rt(len) }
}

fn fin(len: Term) -> Type {
    Type::Fin { len: rt(len) }
}

fn leaf() -> Term {
    supf(inj(false, triv()), triv())
}

/// The children tuple `(l, (r, ⟨⟩)) : Vec(Tree; 2)`.
fn pair2(l: Term, r: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree()),
        snd_ty: rty(vec_tree(num(1))),
        fst: rt(l),
        snd: rt(Term::Pair {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: rty(tree()),
            snd_ty: rty(vec_tree(num(0))),
            fst: rt(r),
            snd: rt(triv()),
        }),
    }
}

fn node(l: Term, r: Term) -> Term {
    supf(inj(true, triv()), pair2(l, r))
}

/// Index 0 / 1 of `Fin 2 = Unit + (Unit + Empty)`.
fn idx(one: bool) -> Term {
    let inner = Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Empty { level: Level::Zero }),
    };
    if one {
        Term::Inr {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(inner),
            val: rt(Term::Inl {
                lhs_level: c(0),
                rhs_level: c(0),
                lhs: rty(Type::Unit { level: Level::Zero }),
                rhs: rty(Type::Empty { level: Level::Zero }),
                val: rt(triv()),
            }),
        }
    } else {
        Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(inner),
            val: rt(triv()),
        }
    }
}

/// The full binary tree of depth `d` (`2^(d+1) - 1` constructors).
fn full_tree(d: u32) -> Term {
    if d == 0 {
        leaf()
    } else {
        let sub = full_tree(d - 1);
        node(sub.clone(), sub)
    }
}

/// `mirror t` — swap every node's children; the shape a generated recursor
/// emits (case on the tag first, so the arity is a literal inside each arm
/// and `Vec`/`Fin` reduce).
fn mirror(scrut: Term) -> Term {
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
    let arm_l = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(num(0))),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(num(0))),
                cod: rty(tree()),
            }),
            body: rt(leaf()),
        }),
    };
    let ih_at = |i: Term| Term::App {
        fun: rt(v(0)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(fin(num(2))),
        cod: rty(tree()),
        arg: rt(i),
    };
    let arm_r = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(vec_tree(num(2))),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin(num(2))),
                cod: rty(tree()),
            }),
            body: rt(node(ih_at(idx(true)), ih_at(idx(false)))),
        }),
    };
    let cased = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
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

// -------------------------------------------------------------------------
// Families
// -------------------------------------------------------------------------

/// `check_term(t : Tree)` on a full tree. Every `sup_f` node forces the
/// arity to a literal and the `Vec` former to unfold, so this is the
/// per-constructor cost of *reading* branching data — paid on every generated
/// declaration the tier-1 lowering emits.
fn check() -> Family {
    let cases = DEPTHS
        .iter()
        .map(|&d| {
            let gamma = nil_ctx();
            let t = full_tree(d);
            let size = count_term(&t);
            let go = move || {
                check_term(
                    &GlobalCtx::default(),
                    0,
                    Layer::Prog,
                    &gamma,
                    &t,
                    &tree(),
                    &Level::Zero,
                    FUEL,
                )
                .is_ok() as u64
            };
            assert!(go() == 1, "the depth-{d} tree does not check at Tree");
            Case::new(size, 1, go)
        })
        .collect();
    Family {
        name: "wf/check-tree",
        what: "check_term(full tree : Tree) — Vec/Fin unfolding per constructor",
        unit: "nodes",
        expect_slope: Some((0.85, 1.35)),
        cases,
    }
}

/// `mirror (mirror t) ≡ t` by conversion: two full eliminations over the
/// tree, then a structural comparison. Elimination *at depth* — the recursive
/// call is synthesized under a λ and applied at literal `Fin` indices, so the
/// cost per node includes the transient ih that route C buys η-freedom with.
fn involution() -> Family {
    let cases = DEPTHS
        .iter()
        .map(|&d| {
            let gamma = nil_ctx();
            let t = full_tree(d);
            let size = count_term(&t);
            let mm = mirror(mirror(t.clone()));
            let go = move || {
                conv_term(
                    &GlobalCtx::default(),
                    &gamma,
                    Layer::Prog,
                    &mm,
                    &t,
                    &tree(),
                    &Level::Zero,
                    FUEL,
                )
                .is_ok() as u64
            };
            assert!(go() == 1, "mirror (mirror t) ≢ t at depth {d}");
            Case::new(size, 1, go)
        })
        .collect();
    Family {
        name: "wf/mirror-involution",
        what: "conv(mirror (mirror t), t) — two eliminations over a full tree",
        unit: "nodes",
        expect_slope: Some((0.85, 1.60)),
        cases,
    }
}
