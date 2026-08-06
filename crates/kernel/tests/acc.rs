//! `Acc` via `W`: the indexed-container reduction, hand-built and
//! kernel-checked. Scheme: `docs/acc-via-w.md`;
//! [[stress-proof-suite]] item 3 / [[inductive-compiler]] tier 2.
//!
//! `elim_W`'s β synthesizes the induction hypothesis **under a λ** —
//! `elim_W(sup(a; f)) ⇝ s[a, f, λy. elim_W(…; f y)]` — and it is the only β
//! rule in the kernel with that shape (`Wf`'s ih is `Fin`-indexed and
//! transient, so it never exercises the abstract-position case). `Acc` is
//! the construction that genuinely needs it. Nothing in the frontend reaches
//! `W`, so this file is insurance on trusted code, not frontend progress.
//!
//! The encoding (`docs/acc-via-w.md` §1):
//!
//! ```text
//! Below(a) := Σ(b : A). R(b, a)
//! W₀       := W^{0,0}(x : A). Below(x)
//! root(sup(a; f)) ⇝ a                                  elim_W at motive A
//! coh(sup(a; f)) ⇝ Π(y : Below a). Σ(_ : Id(A; root(f y); fst y)). coh(f y)
//!                                                      elim_W at motive Ty 0
//! Acc(a)   := Σ(t : W₀). Σ(_ : Id(A; root t; a)). El (coh t)
//! ```
//!
//! Instance: the ω+1 order — `A = Unit + Nat`, every numeral below
//! `ω = inl ⟨⟩`, nothing below a numeral. One node of *infinite* arity,
//! which is what puts `Acc` in tier 2 (no uniform arity ⇒ not `Wf`).
//!
//! Ψ is empty throughout, which is the point of §4: the recursion direction
//! of tier 2 buys **no funext** and needs **no `Empty`-η`**.

use std::rc::Rc;

use heather_kernel::conv::{conv_term, conv_type};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 1_000_000;

// ---------------------------------------------------------------------------
// Helpers (as in wf.rs / branching_route_a.rs)
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

/// `Π^{0,0}(x : dom). cod` — the common case; `cod` binds one variable.
fn pi0(dom: Type, cod: Type) -> Type {
    Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(dom), cod: rty(cod) }
}

/// `λ^{0,0}(x : dom). body`.
fn lam0(dom: Type, body: Term) -> Term {
    Term::Lam { dom_level: c(0), cod_level: c(0), dom: rty(dom), body: rt(body) }
}

/// `app(f; 0, 0; _ : dom. cod; arg)` — `cod` binds one variable.
fn app0(f: Term, dom: Type, cod: Type, arg: Term) -> Term {
    Term::App {
        fun: rt(f),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(dom),
        cod: rty(cod),
        arg: rt(arg),
    }
}

/// `Σ^{0,0}(x : fst). snd`.
fn sigma0(fst: Type, snd: Type) -> Type {
    Type::Sigma { fst_level: c(0), snd_level: c(0), fst: rty(fst), snd: rty(snd) }
}

fn pair0(fst_ty: Type, snd_ty: Type, fst: Term, snd: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        fst: rt(fst),
        snd: rt(snd),
    }
}

fn fst0(fst_ty: Type, snd_ty: Type, pair: Term) -> Term {
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        pair: rt(pair),
    }
}

fn snd0(fst_ty: Type, snd_ty: Type, pair: Term) -> Term {
    Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        pair: rt(pair),
    }
}

fn id_a(lhs: Term, rhs: Term) -> Type {
    Type::Id { level: c(0), ty: rty(ty_a()), lhs: rt(lhs), rhs: rt(rhs) }
}

fn el0(tm: Term) -> Type {
    Type::El { level: c(0), tm: rt(tm) }
}

fn nat_lit(n: u32) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

// ---------------------------------------------------------------------------
// The carrier `A = Unit^0 + Nat` and the ω+1 relation
// ---------------------------------------------------------------------------

fn ty_a() -> Type {
    Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Nat),
    }
}

/// `⌜A⌝ : Ty 0`.
fn tm_a() -> Term {
    Term::TmSum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rt(Term::TmUnit { level: Level::Zero }),
        rhs: rt(Term::TmNat),
    }
}

/// `ω = inl ⟨⟩`.
fn omega() -> Term {
    Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Nat),
        val: rt(Term::Triv { level: Level::Zero }),
    }
}

/// `num n = inr n`.
fn num(n: Term) -> Term {
    Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Nat),
        val: rt(n),
    }
}

/// `case^{0,0,1}(_. Ty 0; …; scrut)` — large elimination on `A`.
fn case_ty0(case_l: Term, case_r: Term, scrut: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(1),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Nat),
        motive: rty(Type::Ty(c(0))),
        case_l: rt(case_l),
        case_r: rt(case_r),
        scrut: rt(scrut),
    }
}

/// `⌜R(b, a)⌝ : Ty 0` — `Unit` iff `a = ω` and `b` is a numeral, else
/// `Empty`. Each `case` arm binds the injected value, so `b` is shifted
/// under the outer arm.
fn r_code(b: Term, a: Term) -> Term {
    let inner = case_ty0(
        Term::TmEmpty { level: Level::Zero },
        Term::TmUnit { level: Level::Zero },
        b.shift_local(1),
    );
    case_ty0(inner, Term::TmEmpty { level: Level::Zero }, a)
}

fn r_ty(b: Term, a: Term) -> Type {
    el0(r_code(b, a))
}

/// `Below(a) = Σ(b : A). R(b, a)`; the Σ binds `b`, so `a` shifts under it.
fn below(a: Term) -> Type {
    sigma0(ty_a(), r_ty(v(0), a.shift_local(1)))
}

/// `⌜Below(a)⌝ : Ty 0`.
fn below_code(a: Term) -> Term {
    Term::TmSigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rt(tm_a()),
        snd: rt(r_code(v(0), a.shift_local(1))),
    }
}

/// `fst y` at `y : Below(a)`.
fn fst_below(y: Term, a: Term) -> Term {
    fst0(ty_a(), r_ty(v(0), a.shift_local(1)), y)
}

/// `snd y` at `y : Below(a)`.
fn snd_below(y: Term, a: Term) -> Term {
    snd0(ty_a(), r_ty(v(0), a.shift_local(1)), y)
}

/// `⟨b, r⟩ : Below(a)`.
fn mk_below(b: Term, r: Term, a: Term) -> Term {
    pair0(ty_a(), r_ty(v(0), a.shift_local(1)), b, r)
}

// ---------------------------------------------------------------------------
// `W₀`, `root`, `coh`, `Acc`
// ---------------------------------------------------------------------------

fn w0() -> Type {
    Type::W {
        shape_level: c(0),
        pos_level: c(0),
        shape: rty(ty_a()),
        pos: rty(below(v(0))),
    }
}

fn sup(label: Term, children: Term) -> Term {
    Term::Sup {
        shape_level: c(0),
        pos_level: c(0),
        shape_ty: rty(ty_a()),
        pos_ty: rty(below(v(0))),
        label: rt(label),
        children: rt(children),
    }
}

/// `f y` at `f : Π(y : Below a). W₀`.
fn child(f: Term, a: Term, y: Term) -> Term {
    app0(f, below(a), w0(), y)
}

/// `root : W₀ → A`, by `elim_W` at the constant motive `A`; step is the
/// label (`a = v(2)`).
fn root(t: Term) -> Term {
    Term::ElimW {
        shape_level: c(0),
        pos_level: c(0),
        motive_level: c(0),
        shape: rty(ty_a()),
        pos: rty(below(v(0))),
        motive: rty(ty_a()),
        step: rt(v(2)),
        scrut: rt(t),
    }
}

/// `coh : W₀ → Ty 0`, by `elim_W` at the large motive `Ty 0`. The step binds
/// `a = v(2)`, `f = v(1)`, `ih = v(0)` and builds the **code**
/// `Π(y : Below a). Σ(_ : Id(A; root (f y); fst y)). ih y`.
fn coh(t: Term) -> Term {
    // Under the `Π`-code's binder `y`: a = v(3), f = v(2), ih = v(1), y = v(0).
    let idx_code = Term::TmId {
        level: c(0),
        ty: rt(tm_a()),
        lhs: rt(root(child(v(2), v(3), v(0)))),
        rhs: rt(fst_below(v(0), v(3))),
    };
    // Under the `Σ`-code's binder: y = v(1), ih = v(2), a = v(4).
    let rest_code = Term::App {
        fun: rt(v(2)),
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(below(v(4))),
        cod: rty(Type::Ty(c(0))),
        arg: rt(v(1)),
    };
    let step = Term::TmPi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rt(below_code(v(2))),
        cod: rt(Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(idx_code),
            snd: rt(rest_code),
        }),
    };
    Term::ElimW {
        shape_level: c(0),
        pos_level: c(0),
        motive_level: c(1),
        shape: rty(ty_a()),
        pos: rty(below(v(0))),
        motive: rty(Type::Ty(c(0))),
        step: rt(step),
        scrut: rt(t),
    }
}

/// The coherence type of a *specific* tree: `El (coh t)` unfolded one step —
/// `Π(y : Below a). Σ(_ : Id(A; root (f y); fst y)). El (coh (f y))`, the
/// shape `El (coh (sup(a; f)))` weak-head-reduces to.
fn coh_unfolded(a: Term, f: Term) -> Type {
    let a1 = a.shift_local(1);
    let f1 = f.shift_local(1);
    pi0(
        below(a.clone()),
        sigma0(
            Type::Id {
                level: c(0),
                ty: rty(ty_a()),
                lhs: rt(root(child(f1.clone(), a1.clone(), v(0)))),
                rhs: rt(fst_below(v(0), a1.clone())),
            },
            el0(coh(child(f1.shift_local(1), a1.shift_local(1), v(1)))),
        ),
    )
}

/// `Acc(a) = Σ(t : W₀). Σ(_ : Id(A; root t; a)). El (coh t)`.
fn acc_ty(a: Term) -> Type {
    sigma0(w0(), acc_rest(a.shift_local(1)))
}

/// The inner Σ of `Acc(a)`, in a scope where the tree is `v(0)`.
fn acc_rest(a: Term) -> Type {
    sigma0(id_a(root(v(0)), a), el0(coh(v(1))))
}

/// `fst acc : W₀`.
fn acc_tree(acc: Term, a: Term) -> Term {
    fst0(w0(), acc_rest(a.shift_local(1)), acc)
}

/// `snd acc : Σ(_ : Id(A; root (fst acc); a)). El (coh (fst acc))`.
fn acc_rest_of(acc: Term, a: Term) -> Term {
    snd0(w0(), acc_rest(a.shift_local(1)), acc)
}

/// `fst (snd acc)` — the index proof.
fn acc_idx(acc: Term, a: Term) -> Term {
    let t = acc_tree(acc.clone(), a.clone());
    fst0(
        id_a(root(t.clone()), a.clone()),
        el0(coh(t.shift_local(1))),
        acc_rest_of(acc, a),
    )
}

/// `snd (snd acc)` — the coherence proof.
fn acc_coh(acc: Term, a: Term) -> Term {
    let t = acc_tree(acc.clone(), a.clone());
    snd0(
        id_a(root(t.clone()), a.clone()),
        el0(coh(t.shift_local(1))),
        acc_rest_of(acc, a),
    )
}

// ---------------------------------------------------------------------------
// `intro`
// ---------------------------------------------------------------------------

/// `Π(b : A). Π(_ : R(b, a)). Acc(b)` — the type of `intro`'s field.
fn h_ty(a: Term) -> Type {
    pi0(ty_a(), pi0(r_ty(v(0), a.shift_local(1)), acc_ty(v(1))))
}

/// `h (fst y) (snd y) : Acc(fst y)`, at `y : Below(a)`.
fn h_at(h: Term, a: Term, y: Term) -> Term {
    let b = fst_below(y.clone(), a.clone());
    let inner = app0(
        h,
        ty_a(),
        pi0(r_ty(v(0), a.shift_local(1)), acc_ty(v(1))),
        b.clone(),
    );
    app0(
        inner,
        r_ty(b.clone(), a.clone()),
        acc_ty(b.shift_local(1)),
        snd_below(y, a),
    )
}

/// The children function `λ(y : Below a). fst (h (fst y) (snd y))`.
fn intro_children(a: Term, h: Term) -> Term {
    let a1 = a.shift_local(1);
    let h1 = h.shift_local(1);
    let y = v(0);
    let b = fst_below(y.clone(), a1.clone());
    lam0(
        below(a),
        acc_tree(h_at(h1, a1, y), b),
    )
}

/// `intro(a; h) : Acc(a)`.
fn intro(a: Term, h: Term) -> Term {
    let f = intro_children(a.clone(), h.clone());
    let t = sup(a.clone(), f.clone());

    // The coherence component: λ(y : Below a). ⟨fst (snd (h … )), snd (snd (h … ))⟩,
    // whose annotations are the *expected* shape (`f y`, not `fst (h … )`) —
    // the two are bridged by β, which is §2.1's third definitional fact.
    let a1 = a.shift_local(1);
    let f1 = f.shift_local(1);
    let y = v(0);
    let b1 = fst_below(y.clone(), a1.clone());
    let ch = h_at(h.shift_local(1), a1.clone(), y.clone());
    let coh_component = lam0(
        below(a.clone()),
        pair0(
            Type::Id {
                level: c(0),
                ty: rty(ty_a()),
                lhs: rt(root(child(f1.clone(), a1.clone(), y.clone()))),
                rhs: rt(b1.clone()),
            },
            el0(coh(child(
                f1.shift_local(1),
                a1.shift_local(1),
                y.shift_local(1),
            ))),
            acc_idx(ch.clone(), b1.clone()),
            acc_coh(ch, b1),
        ),
    );

    pair0(
        w0(),
        acc_rest(a1.clone()),
        t.clone(),
        pair0(
            id_a(root(t.clone()), a.clone()),
            el0(coh(t.shift_local(1))),
            Term::Refl { level: c(0), ty: rty(ty_a()), tm: rt(a) },
            coh_component,
        ),
    )
}

// ---------------------------------------------------------------------------
// Well-founded recursion
// ---------------------------------------------------------------------------
//
// The motive is a term `p : Π(a : A). Ty 0`; `P a := El (p a)`. That covers
// both the open case (`p` a context variable) and the closed one
// (`p := λa. ⌜Nat⌝`) with one construction.

fn p_ty() -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(ty_a()),
        cod: rty(Type::Ty(c(0))),
    }
}

/// `P a = El (p a)`.
fn p_at(p: Term, a: Term) -> Type {
    el0(Term::App {
        fun: rt(p),
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(ty_a()),
        cod: rty(Type::Ty(c(0))),
        arg: rt(a),
    })
}

/// `Π(b : A). Π(_ : R(b, a)). P b` — what the step gets to call.
fn kfn_ty(p: Term, a: Term) -> Type {
    pi0(
        ty_a(),
        pi0(
            r_ty(v(0), a.shift_local(1)),
            p_at(p.shift_local(2), v(1)),
        ),
    )
}

/// `Π(a : A). (Π(b : A). Π(_ : R(b, a)). P b) → P a`.
fn st_ty(p: Term) -> Type {
    pi0(
        ty_a(),
        pi0(
            kfn_ty(p.shift_local(1), v(0)),
            p_at(p.shift_local(2), v(1)),
        ),
    )
}

/// `M(z) = Π(a : A). Π(_ : Id(A; root z; a)). Π(_ : El (coh z)). P a`,
/// instantiated at the tree `t`.
fn m_ty(p: Term, t: Term) -> Type {
    pi0(ty_a(), m_cod1(p.shift_local(1), t.shift_local(1)))
}

/// `M`'s body under its first binder (`a = v(0)`).
fn m_cod1(p: Term, t: Term) -> Type {
    pi0(
        id_a(root(t.clone()), v(0)),
        m_cod2(p.shift_local(1), t.shift_local(1), v(1)),
    )
}

/// `Π(_ : El (coh t)). P a`.
fn m_cod2(p: Term, t: Term, a: Term) -> Type {
    pi0(el0(coh(t)), p_at(p.shift_local(1), a.shift_local(1)))
}

/// The `elim_W` step of `wfrec`. Binds `a₀ = v(2)`, `f = v(1)`, `ih = v(0)`;
/// `p`, `st` come from the ambient scope and are shifted here.
fn wfrec_step(p: Term, st: Term) -> Term {
    // Scope after the three λs below: a₀ = v(5), f = v(4), ih = v(3),
    // a = v(2), q = v(1), coh_arg = v(0). `p`/`st` shift by 6.
    let (a0, _f, ih, a, q, ch) = (v(5), v(4), v(3), v(2), v(1), v(0));
    let p6 = p.shift_local(6);
    let st6 = st.shift_local(6);

    // k = λ(b : A). λ(r : R(b, a₀)).
    //       ih ⟨b, r⟩ b (fst (coh_arg ⟨b, r⟩)) (snd (coh_arg ⟨b, r⟩))
    let k = {
        // Under both λs: a₀ = v(7), f = v(6), ih = v(5), a = v(4), q = v(3),
        // coh_arg = v(2), b = v(1), r = v(0).
        let (a0k, fk, ihk, chk, b, r) = (v(7), v(6), v(5), v(2), v(1), v(0));
        let y = mk_below(b.clone(), r, a0k.clone());
        let f_y = child(fk.clone(), a0k.clone(), y.clone());
        let ch_y = app0(
            chk,
            below(a0k.clone()),
            sigma0(
                Type::Id {
                    level: c(0),
                    ty: rty(ty_a()),
                    lhs: rt(root(child(
                        fk.shift_local(1),
                        a0k.shift_local(1),
                        v(0),
                    ))),
                    rhs: rt(fst_below(v(0), a0k.shift_local(1))),
                },
                el0(coh(child(
                    fk.shift_local(2),
                    a0k.shift_local(2),
                    v(1),
                ))),
            ),
            y.clone(),
        );
        let idx = fst0(
            Type::Id {
                level: c(0),
                ty: rty(ty_a()),
                lhs: rt(root(f_y.clone())),
                rhs: rt(b.clone()),
            },
            el0(coh(f_y.shift_local(1))),
            ch_y.clone(),
        );
        let coh_arg = snd0(
            Type::Id {
                level: c(0),
                ty: rty(ty_a()),
                lhs: rt(root(f_y.clone())),
                rhs: rt(b.clone()),
            },
            el0(coh(f_y.shift_local(1))),
            ch_y,
        );
        let p8 = p.shift_local(8);
        // `ih : Π(y : Below a₀). M[f y/z]` — the position comes first; only
        // then the three arguments `M` abstracts (index, index proof,
        // coherence proof).
        let step0 = app0(
            ihk,
            below(a0k.clone()),
            m_ty(
                p8.shift_local(1),
                child(fk.shift_local(1), a0k.shift_local(1), v(0)),
            ),
            y.clone(),
        );
        let step1 = app0(
            step0,
            ty_a(),
            m_cod1(p8.shift_local(1), f_y.shift_local(1)),
            b.clone(),
        );
        let step2 = app0(
            step1,
            id_a(root(f_y.clone()), b.clone()),
            m_cod2(p8.shift_local(1), f_y.shift_local(1), b.shift_local(1)),
            idx,
        );
        let step3 = app0(
            step2,
            el0(coh(f_y.clone())),
            p_at(p8.shift_local(1), b.shift_local(1)),
            coh_arg,
        );
        // The `r` binder's domain is one λ in, where a₀ is v(6) and b is v(0).
        lam0(ty_a(), lam0(r_ty(v(0), v(6)), step3))
    };

    // st a₀ k : P a₀
    let st_a0 = app0(
        st6.clone(),
        ty_a(),
        pi0(
            kfn_ty(p6.shift_local(1), v(0)),
            p_at(p6.shift_local(2), v(1)),
        ),
        a0.clone(),
    );
    let st_call = app0(
        st_a0,
        kfn_ty(p6.clone(), a0.clone()),
        p_at(p6.shift_local(1), a0.shift_local(1)),
        k,
    );

    // Transport P a₀ → P a along q : Id(A; a₀; a).
    let transported = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(ty_a()),
        lhs: rt(a0.clone()),
        motive: rty(p_at(p6.shift_local(2), v(1))),
        case: rt(st_call),
        rhs: rt(a.clone()),
        proof: rt(q),
    };
    let _ = (ih, ch);

    let sup_af = sup(v(2), v(1));
    lam0(
        ty_a(),
        lam0(
            id_a(root(sup_af.shift_local(1)), v(0)),
            lam0(el0(coh(sup_af.shift_local(2))), transported),
        ),
    )
}

/// `elim_W(…; z. M; step; t) : M[t/z]`.
fn wf_elim(p: Term, st: Term, t: Term) -> Term {
    Term::ElimW {
        shape_level: c(0),
        pos_level: c(0),
        motive_level: c(0),
        shape: rty(ty_a()),
        pos: rty(below(v(0))),
        motive: rty(m_ty(p.shift_local(1), v(0))),
        step: rt(wfrec_step(p, st)),
        scrut: rt(t),
    }
}

/// `wfrec(a; acc) : P a`.
fn wfrec(p: Term, st: Term, a: Term, acc: Term) -> Term {
    let t = acc_tree(acc.clone(), a.clone());
    let e = wf_elim(p.clone(), st, t.clone());
    let s1 = app0(e, ty_a(), m_cod1(p.shift_local(1), t.shift_local(1)), a.clone());
    let s2 = app0(
        s1,
        id_a(root(t.clone()), a.clone()),
        m_cod2(p.shift_local(1), t.shift_local(1), a.shift_local(1)),
        acc_idx(acc.clone(), a.clone()),
    );
    app0(
        s2,
        el0(coh(t)),
        p_at(p.shift_local(1), a.shift_local(1)),
        acc_coh(acc, a),
    )
}

// ---------------------------------------------------------------------------
// The ω+1 instance: accessibility proofs
// ---------------------------------------------------------------------------

/// `h_num n = λb. λr. elim_Empty(r)` — `R(b, num n) ⇝ Empty`.
fn h_num(n: Term) -> Term {
    let a = num(n);
    lam0(
        ty_a(),
        lam0(
            r_ty(v(0), a.shift_local(1)),
            Term::ElimEmpty {
                level: c(0),
                scrut_level: Level::Zero,
                motive: rty(acc_ty(v(2))),
                scrut: rt(v(0)),
            },
        ),
    )
}

/// `acc_num n : Acc(num n)`.
fn acc_num(n: Term) -> Term {
    intro(num(n.clone()), h_num(n))
}

/// `h_ω = λb. (case b of inl _ ⇒ λr. elim_Empty r | inr n ⇒ λr. acc_num n) `,
/// with `r` generalized into the case motive.
fn h_omega() -> Term {
    // Under the λ binding b: b = v(0).
    let motive = pi0(r_ty(v(0), omega()), acc_ty(v(1)));
    // Each arm binds the injected value: `inl u ≡ ω` by Unit-η, and the `inr`
    // arm's numeral is `v(0)` in the domain, `v(1)` under the λ.
    let arm_l = lam0(
        r_ty(omega(), omega()),
        Term::ElimEmpty {
            level: c(0),
            scrut_level: Level::Zero,
            motive: rty(acc_ty(omega())),
            scrut: rt(v(0)),
        },
    );
    let arm_r = lam0(r_ty(num(v(0)), omega()), acc_num(v(1)));
    lam0(
        ty_a(),
        Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Nat),
            motive: rty(motive),
            case_l: rt(arm_l),
            case_r: rt(arm_r),
            scrut: rt(v(0)),
        },
    )
}

/// `acc_ω : Acc(ω)` — the infinitely-branching node.
fn acc_omega() -> Term {
    intro(omega(), h_omega())
}

/// The closed motive `p := λ(a : A). ⌜Nat⌝`.
fn p_nat() -> Term {
    Term::Lam {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(ty_a()),
        body: rt(Term::TmNat),
    }
}

/// `st := λa. λk. case a of inl _ ⇒ Succ (k (num 5) ⟨⟩) | inr _ ⇒ 0`, with
/// `k` generalized into the case motive.
fn st_nat() -> Term {
    let p = p_nat();
    // Under the two λs: a = v(1), k = v(0).
    let motive = pi0(kfn_ty(p.shift_local(1), v(0)), p_at(p.shift_local(2), v(1)));
    // In each arm the injected value is v(0) and the generalized k is v(0)
    // after the arm's own λ.
    let arm_l = {
        // binds u : Unit; then λ(k' : Kfn(inl u)).
        let a = omega();
        let call = app0(
            app0(
                v(0),
                ty_a(),
                pi0(
                    r_ty(v(0), a.shift_local(1)),
                    p_at(p.shift_local(2), v(1)),
                ),
                num(nat_lit(5)),
            ),
            r_ty(num(nat_lit(5)), a.clone()),
            p_at(p.shift_local(1), num(nat_lit(5))),
            Term::Triv { level: Level::Zero },
        );
        lam0(kfn_ty(p.clone(), a), Term::Succ(rt(call)))
    };
    let arm_r = lam0(kfn_ty(p.clone(), num(v(0))), Term::Zero);
    lam0(
        ty_a(),
        Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Nat),
            motive: rty(motive),
            case_l: rt(arm_l),
            case_r: rt(arm_r),
            scrut: rt(v(0)),
        },
    )
}

// ---------------------------------------------------------------------------
// Checking helpers — Ψ is empty everywhere (docs/acc-via-w.md §4).
// ---------------------------------------------------------------------------

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .expect("the type is well-formed");
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn ck_err(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .expect("the type is well-formed");
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("expected the kernel to reject this term");
}

fn ck_ty(gamma: &LocalCtx, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("type is not well-formed: {e:?}"));
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn conv_tys(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    conv_type(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &level, FUEL)
        .unwrap_or_else(|e| panic!("types not convertible: {e:?}"));
}

fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

/// `Γ = a : A` — the open-index context.
fn ctx_a() -> LocalCtx {
    ext(&nil_ctx(), ty_a(), c(0))
}

/// `Γ = a : A, h : Π(b : A). R(b, a) → Acc(b)`.
fn ctx_a_h() -> LocalCtx {
    ext(&ctx_a(), h_ty(v(0)), c(0))
}

/// `Γ = p : Π(a : A). Ty 0, st : …, a : A, h : …` — everything open.
fn ctx_open() -> LocalCtx {
    let g = ext(&nil_ctx(), p_ty(), c(1));
    let g = ext(&g, st_ty(v(0)), c(0));
    let g = ext(&g, ty_a(), c(0));
    ext(&g, h_ty(v(0)), c(0))
}

// ---------------------------------------------------------------------------
// 1. The encoding is well-formed, at an open index
// ---------------------------------------------------------------------------

#[test]
fn w0_root_and_coh_are_well_formed() {
    let g = nil_ctx();
    ck_ty(&g, &w0(), c(0));
    // root : W₀ → A
    ck(&g, &lam0(w0(), root(v(0))), &pi0(w0(), ty_a()), c(0));
    // coh : W₀ → Ty 0
    ck(
        &g,
        &Term::Lam {
            dom_level: c(0),
            cod_level: c(1),
            dom: rty(w0()),
            body: rt(coh(v(0))),
        },
        &Type::Pi {
            dom_level: c(0),
            cod_level: c(1),
            dom: rty(w0()),
            cod: rty(Type::Ty(c(0))),
        },
        c(1),
    );
}

#[test]
fn acc_is_a_type_at_an_open_index() {
    ck_ty(&ctx_a(), &acc_ty(v(0)), c(0));
}

// ---------------------------------------------------------------------------
// 2. `intro` at an open index and an open field
// ---------------------------------------------------------------------------

/// §2.1 fact 2 in isolation: `El (coh (sup(a; f)))` unfolds — the
/// synthesized ih fires *under the λ*, at an abstract position, with `a` and
/// `f` open.
#[test]
fn coh_unfolds_at_an_open_node() {
    let g = ext(&ctx_a(), pi0(below(v(0)), w0()), c(0));
    // a = v(1), f = v(0)
    let (a, f) = (v(1), v(0));
    let unfolded = coh_unfolded(a.clone(), f.clone());
    ck_ty(&g, &unfolded, c(0));
    conv_tys(&g, &el0(coh(sup(a, f))), &unfolded, c(0));
}

#[test]
fn intro_checks_with_open_index_and_field() {
    let g = ctx_a_h();
    // a = v(1), h = v(0)
    ck(&g, &intro(v(1), v(0)), &acc_ty(v(1)), c(0));
}

// ---------------------------------------------------------------------------
// 3. The instance: numerals (open `n`) and ω (infinite arity)
// ---------------------------------------------------------------------------

#[test]
fn acc_num_checks_at_an_open_numeral() {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    ck(&g, &acc_num(v(0)), &acc_ty(num(v(0))), c(0));
}

#[test]
fn acc_omega_checks() {
    ck(&nil_ctx(), &acc_omega(), &acc_ty(omega()), c(0));
}

// ---------------------------------------------------------------------------
// 4. `wfrec` at an open motive and step
// ---------------------------------------------------------------------------

#[test]
fn wfrec_checks_at_an_open_motive_and_step() {
    // Γ = p, st, a, acc
    let g = ext(&nil_ctx(), p_ty(), c(1));
    let g = ext(&g, st_ty(v(0)), c(0));
    let g = ext(&g, ty_a(), c(0));
    let g = ext(&g, acc_ty(v(0)), c(0));
    let (p, st, a, acc) = (v(3), v(2), v(1), v(0));
    ck(&g, &wfrec(p.clone(), st, a.clone(), acc), &p_at(p, a), c(0));
}

// ---------------------------------------------------------------------------
// 5. The β equation — the headline (docs/acc-via-w.md §2.3)
// ---------------------------------------------------------------------------

#[test]
fn wfrec_beta_fires_at_an_open_index_and_field() {
    let g = ctx_open();
    let (p, st, a, h) = (v(3), v(2), v(1), v(0));

    let lhs = wfrec(p.clone(), st.clone(), a.clone(), intro(a.clone(), h.clone()));

    // st a (λb. λr. wfrec(b; h b r))
    let rhs = {
        // Under λb λr: p = v(5), st = v(4), a = v(3), h = v(2), b = v(1), r = v(0).
        let (p5, h2, a3, b, r) = (v(5), v(2), v(3), v(1), v(0));
        let hbr = app0(
            app0(
                h2,
                ty_a(),
                pi0(r_ty(v(0), a3.shift_local(1)), acc_ty(v(1))),
                b.clone(),
            ),
            r_ty(b.clone(), a3.clone()),
            acc_ty(b.shift_local(1)),
            r,
        );
        let inner = wfrec(p5.clone(), v(4), b.clone(), hbr);
        let k = lam0(ty_a(), lam0(r_ty(v(0), v(2)), inner));
        app0(
            app0(
                st.clone(),
                ty_a(),
                pi0(
                    kfn_ty(p.shift_local(1), v(0)),
                    p_at(p.shift_local(2), v(1)),
                ),
                a.clone(),
            ),
            kfn_ty(p.clone(), a.clone()),
            p_at(p.shift_local(1), a.shift_local(1)),
            k,
        )
    };

    ck(&g, &lhs, &p_at(p.clone(), a.clone()), c(0));
    ck(&g, &rhs, &p_at(p.clone(), a.clone()), c(0));
    conv(&g, &lhs, &rhs, &p_at(p, a), c(0));
}

// ---------------------------------------------------------------------------
// 6. Closed computation through the infinitely-branching node
// ---------------------------------------------------------------------------

#[test]
fn wfrec_computes_through_the_infinite_node() {
    let g = nil_ctx();
    let call = wfrec(p_nat(), st_nat(), omega(), acc_omega());
    ck(&g, &call, &Type::Nat, c(0));
    conv(&g, &call, &nat_lit(1), &Type::Nat, c(0));
}

#[test]
fn wfrec_computes_at_a_numeral() {
    let g = nil_ctx();
    let call = wfrec(p_nat(), st_nat(), num(nat_lit(5)), acc_num(nat_lit(5)));
    ck(&g, &call, &Type::Nat, c(0));
    conv(&g, &call, &nat_lit(0), &Type::Nat, c(0));
}

// ---------------------------------------------------------------------------
// 7-9. Negative controls
// ---------------------------------------------------------------------------

/// Coherence is load-bearing: children about the wrong index are rejected.
/// Without this the fording could be vacuous.
#[test]
fn mis_indexed_children_are_rejected() {
    // λb. λr. acc_num 7 — every child is a tree about `num 7`, whatever the
    // position says it should be about.
    let bad_h = lam0(
        ty_a(),
        lam0(r_ty(v(0), omega()), acc_num(nat_lit(7))),
    );
    ck_err(&nil_ctx(), &bad_h, &h_ty(omega()), c(0));
    ck_err(&nil_ctx(), &intro(omega(), bad_h), &acc_ty(omega()), c(0));
}

#[test]
fn the_computed_value_is_not_anything_else() {
    let g = nil_ctx();
    let call = wfrec(p_nat(), st_nat(), omega(), acc_omega());
    not_conv(&g, &call, &nat_lit(0), &Type::Nat, c(0));
    not_conv(&g, &call, &nat_lit(2), &Type::Nat, c(0));
}

/// At a neutral accessibility proof the recursor does not fire — β is not
/// blind. Same call as `wfrec_computes_through_the_infinite_node`, with the
/// *only* difference that the proof is a variable rather than `intro`.
#[test]
fn wfrec_is_neutral_at_a_variable_accessibility_proof() {
    let g = ext(&nil_ctx(), acc_ty(omega()), c(0));
    let neutral = wfrec(p_nat(), st_nat(), omega(), v(0));
    ck(&g, &neutral, &Type::Nat, c(0));
    not_conv(&g, &neutral, &nat_lit(1), &Type::Nat, c(0));
    not_conv(&g, &neutral, &nat_lit(0), &Type::Nat, c(0));
}
