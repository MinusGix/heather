//! Branching-inductives prototype, route C, wrinkle 6.2 round
//! (`docs/branching-inductives-choice.md` §6.2, §13 step 2): the *n-ary*
//! `Wf`-style interface — children as a Σ-tuple, induction hypothesis as a
//! function of a `Fin`-style index — postulated in Ψ, with the same theorem
//! as the other two prototypes proved against it.
//!
//! What is postulated (4 bindings): `treeCode : Ty 0`, the generic
//! constructor `supf : Π(a : 2). El (tup (arity a)) → Tree`, the generic
//! eliminator with the **n-ary ih** `Π(i : El (fin (arity a))). El (M (nth
//! (arity a) cs i))`, and ONE generic β law for the derived `mirror` (each
//! use below = "refl under the real former").
//!
//! What is *defined*, so the real kernel computes it: `arity` (case on the
//! tag), `tup k` (k-fold Σ of Tree, Unit-terminated, by `elim_Nat` into
//! `Ty 0`), `fin k` (`Empty` / `Unit + fin k`), and `nth` (by `elim_Nat` at
//! a Π motive). Per-constructor β facts are NOT postulated — they follow
//! from the single generic law by kernel computation, exactly as they would
//! from the former's actual β rule.
//!
//! The two claims this round pins against the real checker:
//!
//! 1. **The n-ary ih is usable** (wrinkle 6.2): `nth` at a literal arity and
//!    a neutral tuple reduces to the projections, so `ih i₀ : M (fst cs)`
//!    definitionally; the η-deficiency of the ih *function* never bites
//!    because the ih is transient — applied, never stored or compared.
//! 2. **Σ-η + Unit-η do the bridging funext did in route A**: for a neutral
//!    `cs : Σ(_:Tree). Σ(_:Tree). Unit`,
//!    `supf (inr u) cs ≡ node (fst cs) (fst (snd cs))` holds by conversion
//!    (see `sigma_eta_bridges_the_constructor_form`) — the arm obligation at
//!    a generalized tuple IS the constructor-form obligation, no transport.

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

// ---------------------------------------------------------------------------
// Ψ positions and prefix-relative global references
// ---------------------------------------------------------------------------

const G_TREECODE: u32 = 0;
const G_SUPF: u32 = 1;
const G_ELIM: u32 = 2;
const G_MBETA: u32 = 3;

thread_local! {
    static VISIBLE: std::cell::Cell<u32> = const { std::cell::Cell::new(4) };
}

fn with_visible<T>(n: u32, f: impl FnOnce() -> T) -> T {
    VISIBLE.with(|vis| {
        let old = vis.get();
        vis.set(n);
        let r = f();
        vis.set(old);
        r
    })
}

fn global(pos: u32, depth: u32) -> Term {
    let idx = VISIBLE.with(|vis| vis.get()) - 1 - pos;
    Term::GlobalTm {
        var: GlobalVar(idx),
        subst: LocalSubst {
            tail: SubstTail::Empty { len: depth, base: CtxBase::Nil },
            terms: vec![],
        },
    }
}

fn tree_c(depth: u32) -> Type {
    Type::El { level: c(0), tm: rt(global(G_TREECODE, depth)) }
}

fn el(tm: Term) -> Type {
    Type::El { level: c(0), tm: rt(tm) }
}

// ---------------------------------------------------------------------------
// The defined machinery: arity, tup, fin, nth
// ---------------------------------------------------------------------------

/// `arity a = case a of inl _ => 0 | inr _ => 2 : Nat`.
fn arity(a: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        motive: rty(Type::Nat),
        case_l: rt(Term::Zero),
        case_r: rt(Term::Succ(rt(Term::Succ(rt(Term::Zero))))),
        scrut: rt(a),
    }
}

/// `tup k : Ty 0` — the code of the k-fold Σ-tuple of `Tree`,
/// Unit-terminated: `tup 0 = ⌜Unit⌝`, `tup (S m) = ⌜Σ(_ : Tree). El (tup m)⌝`.
fn tup_code(k: Term, depth: u32) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        // (m : Nat, rec : Ty 0) ⊢ ⌜Σ(_ : Tree). El rec⌝; rec is v(1) under
        // the Σ-code's own binder, treeCode's subst is 2 binders deep.
        step: rt(Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(global(G_TREECODE, depth + 2)),
            snd: rt(v(1)),
        }),
        scrut: rt(k),
    }
}

/// `fin k : Ty 0` — `fin 0 = ⌜Empty⌝`, `fin (S m) = ⌜Unit + El (fin m)⌝`.
fn fin_code(k: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmEmpty { level: Level::Zero }),
        step: rt(Term::TmSum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rt(Term::TmUnit { level: Level::Zero }),
            rhs: rt(v(0)),
        }),
        scrut: rt(k),
    }
}

/// `El (fin 2)` reduced: `Unit + (Unit + Empty)`.
fn fin2_ty() -> Type {
    Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Sum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Empty { level: Level::Zero }),
        }),
    }
}

/// Index 0 of `fin 2`.
fn i0() -> Term {
    Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Sum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Empty { level: Level::Zero }),
        }),
        val: rt(Term::Triv { level: Level::Zero }),
    }
}

/// Index 1 of `fin 2`.
fn i1() -> Term {
    Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Sum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Empty { level: Level::Zero }),
        }),
        val: rt(Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Empty { level: Level::Zero }),
            val: rt(Term::Triv { level: Level::Zero }),
        }),
    }
}

fn nat2() -> Term {
    Term::Succ(rt(Term::Succ(rt(Term::Zero))))
}

/// `nth n cs i : Tree` — by `elim_Nat` on `n` at the motive
/// `Π(cs : El (tup k)). Π(i : El (fin k)). Tree`, then applied. Entirely
/// defined; computes at literal `n` and projects out of `cs` even when the
/// tuple's elements are open.
fn nth_app(n: Term, cs: Term, i: Term, depth: u32) -> Term {
    // base : Π(cs : Unit). Π(i : Empty). Tree.
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Unit { level: Level::Zero }),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Empty { level: Level::Zero }),
            body: rt(Term::ElimEmpty {
                level: c(0),
            scrut_level: Level::Zero,
                motive: rty(tree_c(depth + 3)),
                scrut: rt(v(0)),
            }),
        }),
    };
    // step, binds (m, rec); then λ cs. λ i. case i of inl _ => fst cs
    //                                              | inr j => rec (snd cs) j.
    // Scope inside the case arms: (m=4, rec=3, cs=2, i=1, arm-var=0).
    let fst_cs = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth + 5)),
        snd_ty: rty(el(tup_code(v(5), depth + 6))),
        pair: rt(v(2)),
    };
    let snd_cs = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth + 5)),
        snd_ty: rty(el(tup_code(v(5), depth + 6))),
        pair: rt(v(2)),
    };
    let rec_call = Term::App {
        fun: rt(Term::App {
            fun: rt(v(3)),
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(v(4), depth + 5))),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(v(5)))),
                cod: rty(tree_c(depth + 7)),
            }),
            arg: rt(snd_cs),
        }),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(fin_code(v(4)))),
        cod: rty(tree_c(depth + 6)),
        arg: rt(v(0)),
    };
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        // cs : Σ(_ : Tree). El (tup m); scope (m=1, rec=0), +1 under snd.
        dom: rty(Type::Sigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rty(tree_c(depth + 2)),
            snd: rty(el(tup_code(v(2), depth + 3))),
        }),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            // i : Unit + El (fin m); scope (m=2, rec=1, cs=0).
            dom: rty(Type::Sum {
                lhs_level: c(0),
                rhs_level: c(0),
                lhs: rty(Type::Unit { level: Level::Zero }),
                rhs: rty(el(fin_code(v(2)))),
            }),
            body: rt(Term::Case {
                lhs_level: c(0),
                rhs_level: c(0),
                motive_level: c(0),
                lhs: rty(Type::Unit { level: Level::Zero }),
                rhs: rty(el(fin_code(v(3)))),
                motive: rty(tree_c(depth + 5)),
                case_l: rt(fst_cs),
                case_r: rt(rec_call),
                scrut: rt(v(0)),
            }),
        }),
    };
    let recursion = Term::ElimNat {
        level: c(0),
        // binds k: Π(cs : El (tup k)). Π(i : El (fin k)). Tree.
        motive: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(v(0), depth + 1))),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(v(1)))),
                cod: rty(tree_c(depth + 3)),
            }),
        }),
        base: rt(base),
        step: rt(step),
        scrut: rt(n.clone()),
    };
    let at_cs = Term::App {
        fun: rt(recursion),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(tup_code(n.clone(), depth))),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(fin_code(n.clone().shift_local(1)))),
            cod: rty(tree_c(depth + 2)),
        }),
        arg: rt(cs),
    };
    Term::App {
        fun: rt(at_cs),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(fin_code(n))),
        cod: rty(tree_c(depth + 1)),
        arg: rt(i),
    }
}

// ---------------------------------------------------------------------------
// Constructors through the postulated `supf`
// ---------------------------------------------------------------------------

/// `supf a cs`, fully annotated.
fn supf_app(a: Term, cs: Term, depth: u32) -> Term {
    let head = Term::App {
        fun: rt(global(G_SUPF, depth)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        // binds a.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(arity(v(0)), depth + 1))),
            cod: rty(tree_c(depth + 2)),
        }),
        arg: rt(a.clone()),
    };
    Term::App {
        fun: rt(head),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(tup_code(arity(a), depth))),
        cod: rty(tree_c(depth + 1)),
        arg: rt(cs),
    }
}

fn leaf(depth: u32) -> Term {
    supf_app(inl_triv(), Term::Triv { level: Level::Zero }, depth)
}

/// The canonical 2-tuple `(l, (r, ⟨⟩))`.
fn pair2(l: Term, r: Term, depth: u32) -> Term {
    let inner = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth)),
        snd_ty: rty(Type::Unit { level: Level::Zero }),
        fst: rt(r),
        snd: rt(Term::Triv { level: Level::Zero }),
    };
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth)),
        snd_ty: rty(Type::Sigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rty(tree_c(depth + 1)),
            snd: rty(Type::Unit { level: Level::Zero }),
        }),
        fst: rt(l),
        snd: rt(inner),
    }
}

fn node(l: Term, r: Term, depth: u32) -> Term {
    supf_app(inr_triv(), pair2(l, r, depth), depth)
}

/// `Σ(_ : Tree). Σ(_ : Tree). Unit` — `El (tup 2)` reduced.
fn sigma2_ty(depth: u32) -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(tree_c(depth)),
        snd: rty(Type::Sigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rty(tree_c(depth + 1)),
            snd: rty(Type::Unit { level: Level::Zero }),
        }),
    }
}

/// `fst cs` / `fst (snd cs)` for `cs : Σ(_:Tree). Σ(_:Tree). Unit`.
fn proj_l(cs: Term, depth: u32) -> Term {
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth)),
        snd_ty: rty(Type::Sigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rty(tree_c(depth + 1)),
            snd: rty(Type::Unit { level: Level::Zero }),
        }),
        pair: rt(cs),
    }
}

fn proj_r(cs: Term, depth: u32) -> Term {
    let snd = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth)),
        snd_ty: rty(Type::Sigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rty(tree_c(depth + 1)),
            snd: rty(Type::Unit { level: Level::Zero }),
        }),
        pair: rt(cs),
    };
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_c(depth)),
        snd_ty: rty(Type::Unit { level: Level::Zero }),
        pair: rt(snd),
    }
}

// ---------------------------------------------------------------------------
// The postulated eliminator, its type, and the derived `mirror`
// ---------------------------------------------------------------------------

fn mot_ty(depth: u32) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(tree_c(depth)),
        cod: rty(Type::Ty(c(0))),
    }
}

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

/// The generic step type with the n-ary ih:
/// `Π(a : 2). Π(cs : El (tup (arity a))).
///    (Π(i : El (fin (arity a))). El (m (nth (arity a) cs i)))
///  → El (m (supf a cs))`.
fn step_ty(m: Term, depth: u32) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(arity(v(0)), depth + 1))),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                // ih; scope (a, cs), +1 under i: a = v(2), cs = v(1).
                dom: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(el(fin_code(arity(v(1))))),
                    cod: rty(el_app(
                        m.clone().shift_local(3),
                        nth_app(arity(v(2)), v(1), v(0), depth + 3),
                        depth + 3,
                    )),
                }),
                // scope (a, cs, ih): a = v(2), cs = v(1).
                cod: rty(el_app(
                    m.shift_local(3),
                    supf_app(v(2), v(1), depth + 3),
                    depth + 3,
                )),
            }),
        }),
    }
}

fn elim_ty(depth: u32) -> Type {
    Type::Pi {
        dom_level: c(1),
        cod_level: c(0),
        dom: rty(mot_ty(depth)),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(step_ty(v(0), depth + 1)),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(tree_c(depth + 2)),
                cod: rty(el_app(v(2), v(0), depth + 3)),
            }),
        }),
    }
}

/// `elim m st t`, fully annotated.
fn apply_elim(depth: u32, m: Term, st: Term, t: Term) -> Term {
    let a1 = Term::App {
        fun: rt(global(G_ELIM, depth)),
        dom_level: c(1),
        cod_level: c(0),
        dom: rty(mot_ty(depth)),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(step_ty(v(0), depth + 1)),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(tree_c(depth + 2)),
                cod: rty(el_app(v(2), v(0), depth + 3)),
            }),
        }),
        arg: rt(m.clone()),
    };
    let a2 = Term::App {
        fun: rt(a1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(step_ty(m.clone(), depth)),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(tree_c(depth + 1)),
            cod: rty(el_app(m.clone().shift_local(2), v(0), depth + 2)),
        }),
        arg: rt(st),
    };
    Term::App {
        fun: rt(a2),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(tree_c(depth)),
        cod: rty(el_app(m.shift_local(1), v(0), depth + 1)),
        arg: rt(t),
    }
}

fn const_motive(depth: u32) -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(tree_c(depth)),
        body: rt(global(G_TREECODE, depth + 1)),
    }
}

/// `mirror`'s generic step: case the tag, generalizing `cs` and `ih` in the
/// motive; the Node arm swaps via the ih at the two `fin 2` indices.
fn mirror_step(depth: u32) -> Term {
    // Case motive, binds (z : 2), at scope (a, cs, ih) = depth + 3:
    // Π(cs' : El (tup (arity z))). Π(ih' : Π(i : El (fin (arity z))). Tree). Tree.
    let cmot = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(tup_code(arity(v(0)), depth + 4))),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(arity(v(1))))),
                cod: rty(tree_c(depth + 6)),
            }),
            cod: rty(tree_c(depth + 6)),
        }),
    };
    // Leaf arm (binds u): λ(cs' : Unit). λ(ih' : Π(i : Empty). Tree). leaf.
    let arm_l = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Unit { level: Level::Zero }),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Empty { level: Level::Zero }),
                cod: rty(tree_c(depth + 6)),
            }),
            body: rt(leaf(depth + 6)),
        }),
    };
    // Node arm (binds u): λ(cs' : Σ…). λ(ih' : Π(i : fin 2). Tree).
    //   node (ih' i₁) (ih' i₀)   — the swap.
    let ih_at = |i: Term| Term::App {
        fun: rt(v(0)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(fin2_ty()),
        cod: rty(tree_c(depth + 7)),
        arg: rt(i),
    };
    let arm_r = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(sigma2_ty(depth + 4)),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin2_ty()),
                cod: rty(tree_c(depth + 6)),
            }),
            body: rt(node(ih_at(i1()), ih_at(i0()), depth + 6)),
        }),
    };
    // Step scope (a, cs, ih): a = v(2), cs = v(1), ih = v(0).
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
        dom: rty(el(tup_code(arity(v(2)), depth + 3))),
        // binds cs'; scope (a, cs, ih, cs'): a = v(3).
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(arity(v(3))))),
                cod: rty(tree_c(depth + 5)),
            }),
            cod: rty(tree_c(depth + 5)),
        }),
        arg: rt(v(1)),
    };
    let at_ih = Term::App {
        fun: rt(at_cs),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(fin_code(arity(v(2))))),
            cod: rty(tree_c(depth + 4)),
        }),
        cod: rty(tree_c(depth + 4)),
        arg: rt(v(0)),
    };
    Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(arity(v(0)), depth + 1))),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(el(fin_code(arity(v(1))))),
                    cod: rty(tree_c(depth + 3)),
                }),
                body: rt(at_ih),
            }),
        }),
    }
}

fn mirror(depth: u32, t: Term) -> Term {
    apply_elim(depth, const_motive(depth), mirror_step(depth), t)
}

fn mm(depth: u32, t: Term) -> Term {
    mirror(depth, mirror(depth, t))
}

/// The RHS of the generic β law: `mirror_step a cs (λ i. mirror (nth
/// (arity a) cs i))`, fully annotated.
fn mbeta_rhs(a: Term, cs: Term, depth: u32) -> Term {
    let ih_fun = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(fin_code(arity(a.clone())))),
        body: rt(mirror(
            depth + 1,
            nth_app(
                arity(a.clone().shift_local(1)),
                cs.clone().shift_local(1),
                v(0),
                depth + 1,
            ),
        )),
    };
    let s1 = Term::App {
        fun: rt(mirror_step(depth)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        // binds a.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(arity(v(0)), depth + 1))),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(el(fin_code(arity(v(1))))),
                    cod: rty(tree_c(depth + 3)),
                }),
                cod: rty(tree_c(depth + 3)),
            }),
        }),
        arg: rt(a.clone()),
    };
    let s2 = Term::App {
        fun: rt(s1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(tup_code(arity(a.clone()), depth))),
        // binds cs.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(arity(a.clone().shift_local(1))))),
                cod: rty(tree_c(depth + 2)),
            }),
            cod: rty(tree_c(depth + 2)),
        }),
        arg: rt(cs),
    };
    Term::App {
        fun: rt(s2),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(fin_code(arity(a)))),
            cod: rty(tree_c(depth + 1)),
        }),
        cod: rty(tree_c(depth + 1)),
        arg: rt(ih_fun),
    }
}

/// Ψ: the code, `supf`, the n-ary eliminator, and ONE generic β law for the
/// derived `mirror` — per-constructor facts follow by kernel computation.
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
            // supf : Π(a : 2). El (tup (arity a)) → Tree
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(1, || {
                    rty(Type::Pi {
                        dom_level: c(0),
                        cod_level: c(0),
                        dom: rty(two()),
                        cod: rty(Type::Pi {
                            dom_level: c(0),
                            cod_level: c(0),
                            dom: rty(el(tup_code(arity(v(0)), 1))),
                            cod: rty(tree_c(2)),
                        }),
                    })
                }),
                level: c(0),
                body: None,
            },
            // elim : Π(M). step → Π(t). El (M t)
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(2, || rty(elim_ty(0))),
                level: c(1),
                body: None,
            },
            // Π(a)(cs). mirror (supf a cs) = mirror_step a cs (λi. mirror (nth _ cs i))
            GlobalBinding::Tm {
                ctx: nil_ctx(),
                layer: Layer::Code,
                ty: with_visible(3, || {
                    rty(Type::Pi {
                        dom_level: c(0),
                        cod_level: c(0),
                        dom: rty(two()),
                        cod: rty(Type::Pi {
                            dom_level: c(0),
                            cod_level: c(0),
                            dom: rty(el(tup_code(arity(v(0)), 1))),
                            cod: rty(Type::Id {
                                level: c(0),
                                ty: rty(tree_c(2)),
                                lhs: rt(mirror(2, supf_app(v(1), v(0), 2))),
                                rhs: rt(mbeta_rhs(v(1), v(0), 2)),
                            }),
                        }),
                    })
                }),
                level: c(0),
                body: None,
            },
        ],
    }
}

/// `mbeta a cs`, fully annotated.
fn apply_mbeta(depth: u32, a: Term, cs: Term) -> Term {
    let m1 = Term::App {
        fun: rt(global(G_MBETA, depth)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        // binds a.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(arity(v(0)), depth + 1))),
            cod: rty(Type::Id {
                level: c(0),
                ty: rty(tree_c(depth + 2)),
                lhs: rt(mirror(depth + 2, supf_app(v(1), v(0), depth + 2))),
                rhs: rt(mbeta_rhs(v(1), v(0), depth + 2)),
            }),
        }),
        arg: rt(a.clone()),
    };
    Term::App {
        fun: rt(m1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(tup_code(arity(a.clone()), depth))),
        // binds cs.
        cod: rty(Type::Id {
            level: c(0),
            ty: rty(tree_c(depth + 1)),
            lhs: rt(mirror(
                depth + 1,
                supf_app(a.clone().shift_local(1), v(0), depth + 1),
            )),
            rhs: rt(mbeta_rhs(a.shift_local(1), v(0), depth + 1)),
        }),
        arg: rt(cs),
    }
}

// ---------------------------------------------------------------------------
// Identity helpers
// ---------------------------------------------------------------------------

fn id_tree(l: Term, r: Term, depth: u32) -> Type {
    Type::Id { level: c(0), ty: rty(tree_c(depth)), lhs: rt(l), rhs: rt(r) }
}

fn refl_tree(t: Term, depth: u32) -> Term {
    Term::Refl { level: c(0), ty: rty(tree_c(depth)), tm: rt(t) }
}

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

fn cong_node_l(depth: u32, b: Term, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_c(depth)),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            node(x.clone().shift_local(2), b.clone().shift_local(2), depth + 2),
            node(v(1), b.clone().shift_local(2), depth + 2),
            depth + 2,
        )),
        case: rt(refl_tree(node(x, b, depth), depth)),
        rhs: rt(y),
        proof: rt(p),
    }
}

fn cong_node_r(depth: u32, a: Term, x: Term, y: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_c(depth)),
        lhs: rt(x.clone()),
        motive: rty(id_tree(
            node(a.clone().shift_local(2), x.clone().shift_local(2), depth + 2),
            node(a.clone().shift_local(2), v(1), depth + 2),
            depth + 2,
        )),
        case: rt(refl_tree(node(a, x, depth), depth)),
        rhs: rt(y),
        proof: rt(p),
    }
}

// ---------------------------------------------------------------------------
// The theorem: `Γ = (t : Tree) ⊢ mirror (mirror t) = t`, through the n-ary ih
// ---------------------------------------------------------------------------

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

/// Leaf arm body, scope (…, u, cs', ih'). Goal:
/// `Id(mm (supf (inl u) cs'); supf (inl u) cs')` — convertible with
/// `Id(mm leaf; leaf)` by Unit-η on BOTH `u` and the arity-0 tuple `cs'`:
/// route C's "leaf uniqueness is proof irrelevance" claim, checked here.
fn leaf_arm_body(depth: u32) -> Term {
    let lf = leaf(depth);
    let ml = mirror(depth, lf.clone());
    // β-marker: Id(mirror leaf; leaf) — the mbeta RHS at (inl ⟨⟩, ⟨⟩)
    // computes to `leaf` (case fires, arm ignores the ih).
    let p1 = apply_mbeta(depth, inl_triv(), Term::Triv { level: Level::Zero });
    let p2 = cong_mirror(depth, ml.clone(), lf.clone(), p1.clone());
    trans_tree(depth, mm(depth, lf.clone()), ml, lf, p2, p1)
}

/// Node arm body, scope (…, u, cs', ih') with `cs'` a *neutral* Σ-tuple and
/// `ih'` the n-ary hypothesis. `l`/`r` are the projections of `cs'`; the ihs
/// are `ih'` applied at the `fin 2` indices — `nth` computes to the
/// projections, so their types are `Id(mm l; l)` / `Id(mm r; r)`
/// definitionally (wrinkle 6.2's crux). The final check needs
/// `node l r ≡ supf (inr u) cs'`, which is Σ-η + Unit-η — no funext.
fn node_arm_body(depth: u32) -> Term {
    let cs = v(1);
    let l = proj_l(cs.clone(), depth);
    let r = proj_r(cs.clone(), depth);
    let (ml, mr) = (mirror(depth, l.clone()), mirror(depth, r.clone()));
    let (mml, mmr) = (mm(depth, l.clone()), mm(depth, r.clone()));
    let sup_u = supf_app(inr_triv(), cs.clone(), depth);
    let ih_at = |i: Term| Term::App {
        fun: rt(v(0)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(fin2_ty()),
        cod: rty(id_tree(
            mm(depth + 1, nth_app(nat2(), v(2), v(0), depth + 1)),
            nth_app(nat2(), v(2), v(0), depth + 1),
            depth + 1,
        )),
        arg: rt(i),
    };
    // β-marker: mirror (supf (inr u) cs') = node (mirror r) (mirror l).
    let q1 = apply_mbeta(depth, inr_triv(), cs.clone());
    let q2 = cong_mirror(
        depth,
        mirror(depth, sup_u.clone()),
        node(mr.clone(), ml.clone(), depth),
        q1,
    );
    // β-marker: mirror (node (mirror r) (mirror l)) = node (mm l) (mm r).
    let q3 = apply_mbeta(depth, inr_triv(), pair2(mr.clone(), ml.clone(), depth));
    let q4 = trans_tree(
        depth,
        mm(depth, sup_u.clone()),
        mirror(depth, node(mr, ml, depth)),
        node(mml.clone(), mmr.clone(), depth),
        q2,
        q3,
    );
    // The genuine inductive content: cong on the two n-ary ihs.
    let q5 = cong_node_l(depth, mmr.clone(), mml.clone(), l.clone(), ih_at(i0()));
    let q6 = cong_node_r(depth, l.clone(), mmr.clone(), r.clone(), ih_at(i1()));
    let q7 = trans_tree(
        depth,
        node(mml.clone(), mmr.clone(), depth),
        node(l.clone(), mmr.clone(), depth),
        node(l.clone(), r.clone(), depth),
        q5,
        q6,
    );
    // Endpoint `node l r`; the goal wants `supf (inr u) cs'` — Σ-η closes it.
    trans_tree(
        depth,
        mm(depth, sup_u),
        node(mml, mmr, depth),
        node(l, r, depth),
        q4,
        q7,
    )
}

/// The full proof, in `Γ = (t : Tree)`.
fn mirror_mirror_proof(leaf_body: Term) -> Term {
    let depth = 1;
    // Case motive, binds z, at scope (t, a, cs, ih) = 4:
    // Π(cs' : El (tup (arity z))).
    //   Π(ih' : Π(i : El (fin (arity z))). Id(mm (nth _ cs' i); nth _ cs' i)).
    //     Id(mm (supf z cs'); supf z cs')
    let cmot = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(tup_code(arity(v(0)), 5))),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            // scope (z, cs'), binds i: z = v(2), cs' = v(1).
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(arity(v(1))))),
                cod: rty(id_tree(
                    mm(7, nth_app(arity(v(2)), v(1), v(0), 7)),
                    nth_app(arity(v(2)), v(1), v(0), 7),
                    7,
                )),
            }),
            // scope (z, cs', ih'): z = v(2), cs' = v(1).
            cod: rty(id_tree(
                mm(7, supf_app(v(2), v(1), 7)),
                supf_app(v(2), v(1), 7),
                7,
            )),
        }),
    };
    // Leaf arm (binds u; then cs', ih') — bodies at scope depth 7.
    let arm_l = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Unit { level: Level::Zero }),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Empty { level: Level::Zero }),
                cod: rty(id_tree(
                    mm(7, nth_app(Term::Zero, v(1), v(0), 7)),
                    nth_app(Term::Zero, v(1), v(0), 7),
                    7,
                )),
            }),
            body: rt(leaf_body),
        }),
    };
    // Node arm (binds u; then cs', ih').
    let arm_r = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(sigma2_ty(5)),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(fin2_ty()),
                cod: rty(id_tree(
                    mm(7, nth_app(nat2(), v(1), v(0), 7)),
                    nth_app(nat2(), v(1), v(0), 7),
                    7,
                )),
            }),
            body: rt(node_arm_body(7)),
        }),
    };
    // Step, scope (t, a, cs, ih) = 4: a = v(2), cs = v(1), ih = v(0).
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
        dom: rty(el(tup_code(arity(v(2)), 4))),
        // binds cs'; scope (t, a, cs, ih, cs'): a = v(3).
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(el(fin_code(arity(v(3))))),
                cod: rty(id_tree(
                    mm(6, nth_app(arity(v(4)), v(1), v(0), 6)),
                    nth_app(arity(v(4)), v(1), v(0), 6),
                    6,
                )),
            }),
            cod: rty(id_tree(
                mm(6, supf_app(v(4), v(1), 6)),
                supf_app(v(4), v(1), 6),
                6,
            )),
        }),
        arg: rt(v(1)),
    };
    let at_ih = Term::App {
        fun: rt(at_cs),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(fin_code(arity(v(2))))),
            cod: rty(id_tree(
                mm(5, nth_app(arity(v(3)), v(2), v(0), 5)),
                nth_app(arity(v(3)), v(2), v(0), 5),
                5,
            )),
        }),
        // binds the ih arg; scope (t, a, cs, ih, x): a = v(3), cs = v(2).
        cod: rty(id_tree(
            mm(5, supf_app(v(3), v(2), 5)),
            supf_app(v(3), v(2), 5),
            5,
        )),
        arg: rt(v(0)),
    };
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(two()),
        body: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(tup_code(arity(v(0)), 2))),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Pi {
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(el(fin_code(arity(v(1))))),
                    cod: rty(id_tree(
                        mm(4, nth_app(arity(v(2)), v(1), v(0), 4)),
                        nth_app(arity(v(2)), v(1), v(0), 4),
                        4,
                    )),
                }),
                body: rt(at_ih),
            }),
        }),
    };
    apply_elim(depth, thm_motive(depth), step, v(0))
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck_in(psi: &GlobalCtx, gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(psi, 0, Layer::Prog, gamma, ty, &level, FUEL).expect("the type is well-formed");
    check_term(psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn conv_in(psi: &GlobalCtx, gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(psi, gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn the_postulated_interface_checks() {
    check_global_ctx(&psi(), 0, FUEL).unwrap();
}

#[test]
fn constructors_check_including_on_open_children() {
    let psi = psi();
    let g = nil_ctx();
    ck_in(&psi, &g, &leaf(0), &tree_c(0), c(0));
    ck_in(&psi, &g, &node(leaf(0), node(leaf(0), leaf(0), 0), 0), &tree_c(0), c(0));
    let g1 = ext(&ext(&nil_ctx(), tree_c(0), c(0)), tree_c(1), c(0));
    ck_in(&psi, &g1, &node(v(1), v(0), 2), &tree_c(2), c(0));
}

#[test]
fn nth_computes_to_the_projections() {
    // `nth 2 (l, (r, ⟨⟩)) i₀ ≡ l` and `… i₁ ≡ r` with `l`, `r` open — the
    // ih-side of wrinkle 6.2: applications of the n-ary ih at literal
    // indices reach the actual children definitionally.
    let psi = psi();
    let g = ext(&ext(&nil_ctx(), tree_c(0), c(0)), tree_c(1), c(0));
    let cs = pair2(v(1), v(0), 2);
    conv_in(&psi, &g, &nth_app(nat2(), cs.clone(), i0(), 2), &v(1), &tree_c(2), c(0));
    conv_in(&psi, &g, &nth_app(nat2(), cs, i1(), 2), &v(0), &tree_c(2), c(0));
}

#[test]
fn sigma_eta_bridges_the_constructor_form() {
    // THE route-C claim, against today's kernel: for a *neutral* tuple `cs`,
    // `supf (inr u) cs ≡ node (fst cs) (fst (snd cs))` — i.e. the arm
    // obligation at a generalized tuple IS the constructor-form obligation,
    // by Σ-η and Unit-η, with no transport and no funext. This is exactly
    // the equation route A had to postulate funext to cross.
    let psi = psi();
    let g = ext(&ext(&nil_ctx(), Type::Unit { level: Level::Zero }, c(0)), sigma2_ty(1), c(0));
    let u_inj = Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        val: rt(v(1)),
    };
    let lhs = supf_app(u_inj, v(0), 2);
    let rhs = node(proj_l(v(0), 2), proj_r(v(0), 2), 2);
    ck_in(&psi, &g, &lhs, &tree_c(2), c(0));
    conv_in(&psi, &g, &lhs, &rhs, &tree_c(2), c(0));
    // And the arity-0 analogue: any `cs' : Unit` gives the same leaf.
    let g0 = ext(&nil_ctx(), Type::Unit { level: Level::Zero }, c(0));
    conv_in(&psi, &g0, &supf_app(inl_triv(), v(0), 1), &leaf(1), &tree_c(1), c(0));
}

#[test]
fn mirror_mirror_by_induction_with_the_nary_ih() {
    // Γ = (t : Tree) ⊢ mirror (mirror t) = t, through the generic n-ary
    // step. The surviving content after deleting the β-markers: Leaf arm
    // `refl`-shaped, Node arm cong twice + trans, with the ihs obtained by
    // *applying* the Fin-indexed hypothesis — wrinkle 6.2 exercised end to
    // end, Σ-η discharging the constructor-form gap silently.
    let psi = psi();
    let g = ext(&nil_ctx(), tree_c(0), c(0));
    let proof = mirror_mirror_proof(leaf_arm_body(7));
    let goal = id_tree(mm(1, v(0)), v(0), 1);
    ck_in(&psi, &g, &proof, &goal, c(0));
}

#[test]
fn the_kernel_gate_rejects_a_bare_refl_leaf_arm() {
    // `mirror` is postulated, so `mm leaf` is stuck and a bare refl cannot
    // close the leaf arm — the β-markers are load-bearing for the checker.
    let psi = psi();
    let g = ext(&nil_ctx(), tree_c(0), c(0));
    let bad = mirror_mirror_proof(refl_tree(leaf(7), 7));
    let goal = id_tree(mm(1, v(0)), v(0), 1);
    check_term(&psi, 0, Layer::Prog, &g, &bad, &goal, &c(0), FUEL)
        .expect_err("the kernel gate must reject the bare refl");
}

