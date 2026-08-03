//! Indexed families, route 2b over a **`Wf` skeleton** — the prototype for
//! `docs/inductive-fording-lowering.md` §13.1.
//!
//! `crates/elab/tests/indexed_route_2b.rs` validated the fording *layer*
//! (the `sEq` index equation, irrelevance, the setoid bar) over a tier-1
//! *height* skeleton. That skeleton is not what any generator emits:
//! `docs/inductive-tier1-wf-lowering.md` §9 retired exact-height fording as a
//! generator path, so a recursive family's skeleton is a `Wf`, always
//! (fording doc §4.1). This file is that composition — the corner
//! `issues/indexed-families.md` carries as untested (2026-07-29 caveat).
//!
//! The declaration under test, one vehicle for every §13.1 item because it
//! has both an invertible and a computed result index and it branches:
//!
//! ```text
//! inductive Rope<A> : (n: Nat) -> Type {
//!     Nil                                             : Rope<A>(0),
//!     Cons(n: Nat, x: A, xs: Rope<A>(n))              : Rope<A>(Succ(n)),
//!     Cat(n: Nat, m: Nat, l: Rope<A>(n), r: Rope<A>(m)) : Rope<A>(plus(n, m)),
//! }
//! ```
//!
//! `Nil`/`Cons` are route-1-eligible on their own (§8.2 form A); `Cat` is
//! not (§8.3 form B), which is what fords the whole declaration (§3). The
//! lowering, per §4–§8:
//!
//! ```text
//! Skel  = Wf^l(x : Unit^l + (Σ(pay). Unit^l) + Unit^l). arity x   -- 0 / 1 / 2
//! μ     = elim_Wf(_. Nat; …)   Nil ↦ 0, Cons ↦ S (ih ι₀), Cat ↦ plus (ih ι₀) (ih ι₁)
//! ⟦Rope<A>(m)⟧ = Σ(s : Skel). sEq^0(Nat; μ s; m)
//! ```
//!
//! The nominal tag (tier 0 §3.3) is deliberately absent: it is generator
//! bookkeeping and adds a Σ component to every label without touching a
//! single claim below.
//!
//! Axes (`docs/testing-generated-terms.md`): the payload type is a parameter
//! of every helper, instantiated at a **closed** `Nat`, at an **open** `El A`
//! (`open_payload_type_instance`) and at a `Type`-valued field
//! (`fields_above_level_zero`, §13.1 item 7); scrutinees are literal *and*
//! neutral; every eliminator use is a checking position (its result is
//! compared against a written reduct rather than merely typed); and every
//! encoding decision has a negative control (§13.1 items 4 and 6).

use std::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    nth, CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalSubst, LocalVar, Term, Type,
};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 4_000_000;

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

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// A context of `n` entries, for building substitutions — `LocalSubst::id`
/// reads only the length and base, so the entry types are irrelevant.
fn scope(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: (0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: c(0) }).collect(),
    }
}

/// `plus a b` by recursion on `a` — the computed index of `Cat`, and the
/// reason the declaration fords at all (§3.4).
fn plus(a: Term, b: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(b),
        // (k, rec) ⊢ S rec
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(a),
    }
}

/// `pred`, and the two no-confusion codes of §8.2's form A, at `Nat`.
fn pred(n: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(v(1)),
        scrut: rt(n),
    }
}

/// `⌜Unit⌝` at 0, `⌜Empty⌝` at `S _`.
fn zero_pred(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        step: rt(Term::TmEmpty { level: Level::Zero }),
        scrut: rt(n),
    }
}

/// `⌜Empty⌝` at 0, `⌜Unit⌝` at `S _`.
fn is_succ(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmEmpty { level: Level::Zero }),
        step: rt(Term::TmUnit { level: Level::Zero }),
        scrut: rt(n),
    }
}

fn el_of(code: Term) -> Type {
    Type::El { level: c(0), tm: rt(code) }
}

fn seqn(lhs: Term, rhs: Term) -> Type {
    Type::SEq { level: c(0), ty: rty(Type::Nat), lhs: rt(lhs), rhs: rt(rhs) }
}

fn srefl_n(t: Term) -> Term {
    Term::SRefl { level: c(0), ty: rty(Type::Nat), tm: rt(t) }
}

// ---------------------------------------------------------------------------
// The payload type, threaded like `el` was in the tier-1 prototype: every
// helper takes it **scoped where the helper's own result lives** and shifts
// it under its own binders. A closed instance hides shift bugs (axis 2), so
// the tests instantiate it three ways.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Pay {
    ty: Type,
    lvl: Level,
}

impl Pay {
    fn sh(&self, k: u32) -> Pay {
        Pay { ty: self.ty.shift_local(k), lvl: self.lvl.clone() }
    }
}

fn unit_l(l: &Level) -> Type {
    Type::Unit { level: l.clone() }
}

fn triv_l(l: &Level) -> Term {
    Term::Triv { level: l.clone() }
}

// ---------------------------------------------------------------------------
// The skeleton (§4): the declaration with its indices erased, lowered by the
// unindexed tiers — `Wf`, because it is recursive.
//
//   ⟦SNil⟧  = Unit^l          ⟦SCons⟧ = Σ(pay). Unit^l       ⟦SCat⟧ = Unit^l
//   S       = ⟦SNil⟧ + (⟦SCons⟧ + ⟦SCat⟧)
//   arity   = 0 / 1 / 2
//
// The child-index fields (`n` of `Cons`, `n`/`m` of `Cat`) are **not stored**
// (§4.2): they are what `μ` recomputes.
// ---------------------------------------------------------------------------

fn sh_nil(p: &Pay) -> Type {
    unit_l(&p.lvl)
}

fn sh_cons(p: &Pay) -> Type {
    Type::Sigma {
        fst_level: p.lvl.clone(),
        snd_level: p.lvl.clone(),
        fst: rty(p.ty.clone()),
        snd: rty(unit_l(&p.lvl)),
    }
}

fn sh_cat(p: &Pay) -> Type {
    unit_l(&p.lvl)
}

fn sh_tail(p: &Pay) -> Type {
    Type::Sum {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        lhs: rty(sh_cons(p)),
        rhs: rty(sh_cat(p)),
    }
}

fn shape(p: &Pay) -> Type {
    Type::Sum {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        lhs: rty(sh_nil(p)),
        rhs: rty(sh_tail(p)),
    }
}

/// `arity x` — tier 1 §3's constant-motive case tree at motive `Nat`.
/// `p` and `x` are scoped together.
fn arity(p: &Pay, x: Term) -> Term {
    let p1 = p.sh(1);
    let inner = Term::Case {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        motive_level: c(0),
        lhs: rty(sh_cons(&p1)),
        rhs: rty(sh_cat(&p1)),
        motive: rty(Type::Nat),
        case_l: rt(nat(1)),
        case_r: rt(nat(2)),
        scrut: rt(v(0)),
    };
    Term::Case {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        motive_level: c(0),
        lhs: rty(sh_nil(p)),
        rhs: rty(sh_tail(p)),
        motive: rty(Type::Nat),
        case_l: rt(Term::Zero),
        case_r: rt(inner),
        scrut: rt(x),
    }
}

fn skel(p: &Pay) -> Type {
    Type::Wf {
        level: p.lvl.clone(),
        shape: rty(shape(p)),
        arity: rt(arity(&p.sh(1), v(0))),
    }
}

fn vec_skel(p: &Pay, len: Term) -> Type {
    Type::Vec { level: p.lvl.clone(), elem: rty(skel(p)), len: rt(len) }
}

fn fin(len: Term) -> Type {
    Type::Fin { len: rt(len) }
}

/// The index `t` of `Fin(m)` — `wf.rs::fin_index`'s shape, `Fin`-annotated
/// at each tail (tier 1 §6.3).
fn fin_idx(t: usize, m: usize) -> Term {
    let unit = || rty(Type::Unit { level: Level::Zero });
    let mut acc = Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: unit(),
        rhs: rty(fin(nat((m - t - 1) as u64))),
        val: rt(Term::Triv { level: Level::Zero }),
    };
    for k in (0..t).rev() {
        acc = Term::Inr {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: rty(fin(nat((m - k - 1) as u64))),
            val: rt(acc),
        };
    }
    acc
}

/// `nth^l(Skel; m; cs; ι_t)` at a literal arity — tier 1 §6.3's child.
fn child_at(p: &Pay, m: usize, t: usize, cs: Term) -> Term {
    nth(&p.lvl, &rty(skel(p)), &rt(nat(m as u64)), rt(cs), rt(fin_idx(t, m)))
}

fn lab_nil(p: &Pay) -> Term {
    Term::Inl {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        lhs: rty(sh_nil(p)),
        rhs: rty(sh_tail(p)),
        val: rt(triv_l(&p.lvl)),
    }
}

fn lab_cons(p: &Pay, x: Term) -> Term {
    let payload = Term::Pair {
        fst_level: p.lvl.clone(),
        snd_level: p.lvl.clone(),
        fst_ty: rty(p.ty.clone()),
        snd_ty: rty(unit_l(&p.lvl)),
        fst: rt(x),
        snd: rt(triv_l(&p.lvl)),
    };
    Term::Inr {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        lhs: rty(sh_nil(p)),
        rhs: rty(sh_tail(p)),
        val: rt(Term::Inl {
            lhs_level: p.lvl.clone(),
            rhs_level: p.lvl.clone(),
            lhs: rty(sh_cons(p)),
            rhs: rty(sh_cat(p)),
            val: rt(payload),
        }),
    }
}

fn lab_cat(p: &Pay) -> Term {
    Term::Inr {
        lhs_level: p.lvl.clone(),
        rhs_level: p.lvl.clone(),
        lhs: rty(sh_nil(p)),
        rhs: rty(sh_tail(p)),
        val: rt(Term::Inr {
            lhs_level: p.lvl.clone(),
            rhs_level: p.lvl.clone(),
            lhs: rty(sh_cons(p)),
            rhs: rty(sh_cat(p)),
            val: rt(triv_l(&p.lvl)),
        }),
    }
}

fn supf_(p: &Pay, label: Term, children: Term) -> Term {
    Term::Supf {
        level: p.lvl.clone(),
        shape: rty(shape(p)),
        arity: rt(arity(&p.sh(1), v(0))),
        label: rt(label),
        children: rt(children),
    }
}

/// The children tuples at literal arities 0/1/2 — tier 1 §5, `Triv` at the
/// declaration's level because `Vec^l(T; 0) ⇝ Unit^l`.
fn cs0(p: &Pay) -> Term {
    triv_l(&p.lvl)
}

fn cs1(p: &Pay, a: Term) -> Term {
    Term::Pair {
        fst_level: p.lvl.clone(),
        snd_level: p.lvl.clone(),
        fst_ty: rty(skel(p)),
        snd_ty: rty(vec_skel(&p.sh(1), Term::Zero)),
        fst: rt(a),
        snd: rt(cs0(p)),
    }
}

fn cs2(p: &Pay, a: Term, b: Term) -> Term {
    Term::Pair {
        fst_level: p.lvl.clone(),
        snd_level: p.lvl.clone(),
        fst_ty: rty(skel(p)),
        snd_ty: rty(vec_skel(&p.sh(1), nat(1))),
        fst: rt(a),
        snd: rt(cs1(p, b)),
    }
}

fn snil(p: &Pay) -> Term {
    supf_(p, lab_nil(p), cs0(p))
}

fn scons(p: &Pay, x: Term, s: Term) -> Term {
    supf_(p, lab_cons(p, x), cs1(p, s))
}

fn scat(p: &Pay, a: Term, b: Term) -> Term {
    supf_(p, lab_cat(p), cs2(p, a, b))
}

// ---------------------------------------------------------------------------
// The measure `μ` (§5): `elim_Wf` at motive `Nat`, one branch per
// constructor, each branch the *written result index* with the child-index
// variables replaced by the recursion at that child.
//
// `left_only` is §13.1 item 6's falsifier: it builds the measure a
// shared-child-index declaration (`Cat(n, l: Rope(n), r: Rope(n))`) would
// force — `plus (ih ι₀) (ih ι₀)`, which reads one child and ignores the
// other. F2 exists because of what that admits.
// ---------------------------------------------------------------------------

fn mu_gen(p: &Pay, s: Term, left_only: bool) -> Term {
    let l = p.lvl.clone();
    // Γ3 = (Γ, a : S, cs, ih); p3 is the payload there.
    let p3 = p.sh(3);
    let p4 = p.sh(4);
    let p5 = p.sh(5);

    // The case motive P(z), over (Γ3, z : S), at the constant motive `Nat`:
    //   Π(cs' : Vec^l(Skel; arity z)). Π(ih' : Π(Fin (arity z)). Nat). Nat
    let p_ty = |z: Term, extra: u32| -> Type {
        let pe = p.sh(extra);
        let pe1 = p.sh(extra + 1);
        Type::Pi {
            dom_level: l.clone(),
            cod_level: c(0),
            dom: rty(vec_skel(&pe, arity(&pe, z.clone()))),
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Pi {
                    dom_level: Level::Zero,
                    cod_level: c(0),
                    dom: rty(fin(arity(&pe1, z.shift_local(1)))),
                    cod: rty(Type::Nat),
                }),
                cod: rty(Type::Nat),
            }),
        }
    };

    // One branch: λcs'. λih'. ⟦e_c⟧, at the *literal* arity (tier 1 §6.3).
    let arm = |m: usize, body: Term, extra: u32| -> Term {
        let pe = p.sh(extra);
        Term::Lam {
            dom_level: l.clone(),
            cod_level: c(0),
            dom: rty(vec_skel(&pe, nat(m as u64))),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(Type::Pi {
                    dom_level: Level::Zero,
                    cod_level: c(0),
                    dom: rty(fin(nat(m as u64))),
                    cod: rty(Type::Nat),
                }),
                body: rt(body),
            }),
        }
    };

    // `ih' ι_t : Nat` inside a branch of literal arity `m`; `ih'` is Var 0.
    let ih_at = |m: usize, t: usize| Term::App {
        fun: rt(v(0)),
        dom_level: Level::Zero,
        cod_level: c(0),
        dom: rty(fin(nat(m as u64))),
        cod: rty(Type::Nat),
        arg: rt(fin_idx(t, m)),
    };

    // Branch bodies: the constructors' own result indices (§5 fact 1).
    let body_nil = Term::Zero;
    let body_cons = Term::Succ(rt(ih_at(1, 0)));
    let body_cat = if left_only {
        plus(ih_at(2, 0), ih_at(2, 0))
    } else {
        plus(ih_at(2, 0), ih_at(2, 1))
    };

    // The case tree over the shape, scoped (Γ3, ·).
    let inner = Term::Case {
        lhs_level: l.clone(),
        rhs_level: l.clone(),
        motive_level: Level::max(l.clone(), c(0)),
        // A `Case`'s summand types are scoped at the `Case` itself — under
        // `y`, one binder past Γ3 — while its *motive* binds one more.
        lhs: rty(sh_cons(&p4)),
        rhs: rty(sh_cat(&p4)),
        // over (Γ3, y, w) — P(inr w)
        motive: rty(p_ty(
            Term::Inr {
                lhs_level: l.clone(),
                rhs_level: l.clone(),
                lhs: rty(sh_nil(&p5)),
                rhs: rty(sh_tail(&p5)),
                val: rt(v(0)),
            },
            5,
        )),
        case_l: rt(arm(1, body_cons, 5)),
        case_r: rt(arm(2, body_cat, 5)),
        scrut: rt(v(0)),
    };
    let cased = Term::Case {
        lhs_level: l.clone(),
        rhs_level: l.clone(),
        motive_level: Level::max(l.clone(), c(0)),
        lhs: rty(sh_nil(&p3)),
        rhs: rty(sh_tail(&p3)),
        motive: rty(p_ty(v(0), 4)),
        case_l: rt(arm(0, body_nil, 4)),
        case_r: rt(inner),
        scrut: rt(v(2)),
    };
    // (Γ3) ⊢ (case on a) cs ih : Nat
    let at_cs = Term::App {
        fun: rt(cased),
        dom_level: l.clone(),
        cod_level: c(0),
        dom: rty(vec_skel(&p3, arity(&p3, v(2)))),
        // binds cs'; a = Var 3 there.
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Pi {
                dom_level: Level::Zero,
                cod_level: c(0),
                dom: rty(fin(arity(&p4, v(3)))),
                cod: rty(Type::Nat),
            }),
            cod: rty(Type::Nat),
        }),
        arg: rt(v(1)),
    };
    let step = Term::App {
        fun: rt(at_cs),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Pi {
            dom_level: Level::Zero,
            cod_level: c(0),
            dom: rty(fin(arity(&p3, v(2)))),
            cod: rty(Type::Nat),
        }),
        cod: rty(Type::Nat),
        arg: rt(v(0)),
    };
    Term::ElimWf {
        level: l,
        motive_level: c(0),
        shape: rty(shape(p)),
        arity: rt(arity(&p.sh(1), v(0))),
        motive: rty(Type::Nat),
        step: rt(step),
        scrut: rt(s),
    }
}

fn mu(p: &Pay, s: Term) -> Term {
    mu_gen(p, s, false)
}

// ---------------------------------------------------------------------------
// The forded family (§6): `Σ(s : Skel). sEq(Nat; μ s; m)`.
// ---------------------------------------------------------------------------

fn ropef_gen(p: &Pay, m: Term, left_only: bool) -> Type {
    Type::Sigma {
        fst_level: p.lvl.clone(),
        snd_level: c(0),
        fst: rty(skel(p)),
        snd: rty(seqn(mu_gen(&p.sh(1), v(0), left_only), m.shift_local(1))),
    }
}

fn ropef(p: &Pay, m: Term) -> Type {
    ropef_gen(p, m, false)
}

fn fst_f(p: &Pay, m: Term, x: Term) -> Term {
    Term::Fst {
        fst_level: p.lvl.clone(),
        snd_level: c(0),
        fst_ty: rty(skel(p)),
        snd_ty: rty(seqn(mu(&p.sh(1), v(0)), m.shift_local(1))),
        pair: rt(x),
    }
}

fn snd_f(p: &Pay, m: Term, x: Term) -> Term {
    Term::Snd {
        fst_level: p.lvl.clone(),
        snd_level: c(0),
        fst_ty: rty(skel(p)),
        snd_ty: rty(seqn(mu(&p.sh(1), v(0)), m.shift_local(1))),
        pair: rt(x),
    }
}

fn pairf(p: &Pay, m: Term, s: Term, e: Term) -> Term {
    Term::Pair {
        fst_level: p.lvl.clone(),
        snd_level: c(0),
        fst_ty: rty(skel(p)),
        snd_ty: rty(seqn(mu(&p.sh(1), v(0)), m.shift_local(1))),
        fst: rt(s),
        snd: rt(e),
    }
}

// ---------------------------------------------------------------------------
// Constructors (§7): the skeleton constructor paired with the index proof,
// the proof being the children's own proofs pushed through the written
// result index by `transp`. Every proof below sits at `sEq`, where the
// irrelevance arm erases it — §9's cast rule does not bind here.
// ---------------------------------------------------------------------------

fn fnil(p: &Pay) -> Term {
    pairf(p, Term::Zero, snil(p), srefl_n(Term::Zero))
}

/// `cons_f n x v : Rope_f(S n)` for `v : Rope_f(n)`.
fn fcons(p: &Pay, n: Term, x: Term, v_: Term) -> Term {
    let s0 = fst_f(p, n.clone(), v_.clone());
    let e0 = snd_f(p, n.clone(), v_);
    let sh = scons(p, x, s0.clone());
    let mu_s = mu(p, sh.clone());
    // transp(Nat; z. sEq(Nat; μ ŝ; S z); μ s₀; n; e₀; srefl (μ ŝ))
    let proof = Term::Transp {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        motive: rty(seqn(mu_s.shift_local(1), Term::Succ(rt(v(0))))),
        lhs: rt(mu(p, s0)),
        rhs: rt(n.clone()),
        proof: rt(e0),
        tm: rt(srefl_n(mu_s)),
    };
    pairf(p, Term::Succ(rt(n)), sh, proof)
}

/// `cat_f n m vl vr : Rope_f(plus n m)`.
fn fcat(p: &Pay, n: Term, m: Term, vl: Term, vr: Term) -> Term {
    let sl = fst_f(p, n.clone(), vl.clone());
    let sr = fst_f(p, m.clone(), vr.clone());
    let el = snd_f(p, n.clone(), vl);
    let er = snd_f(p, m.clone(), vr);
    let sh = scat(p, sl.clone(), sr.clone());
    let mu_s = mu(p, sh.clone());
    let mu_l = mu(p, sl);
    let mu_r = mu(p, sr);
    // Innermost: srefl at μ ŝ ≡ plus (μ sl) (μ sr) — §5 fact 3's β.
    // Then rewrite the *right* child's measure to `m`, then the left's to `n`.
    let inner = Term::Transp {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        motive: rty(seqn(
            mu_s.shift_local(1),
            plus(mu_l.shift_local(1), v(0)),
        )),
        lhs: rt(mu_r),
        rhs: rt(m.clone()),
        proof: rt(er),
        tm: rt(srefl_n(mu_s.clone())),
    };
    let proof = Term::Transp {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        motive: rty(seqn(mu_s.shift_local(1), plus(v(0), m.shift_local(1)))),
        lhs: rt(mu_l),
        rhs: rt(n.clone()),
        proof: rt(el),
        tm: rt(inner),
    };
    pairf(p, plus(n, m), sh, proof)
}

// ---------------------------------------------------------------------------
// The eliminator (§8). One skeleton recursion at the fording motive
//
//   Q(σ) = Π(m' : Nat). Π(e : sEq(Nat; μ σ; m')). M[m', ⟨σ, e⟩]
//
// with each arm in form A (index inversion, §8.2) or form B (one transp at
// the arm's head, §8.3).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    /// Every arm by §8.3's transp — the form available at any index.
    B,
    /// `Nil`/`Cons` by §8.2's inversion (they are route-1-eligible on their
    /// own); `Cat` still by transp, because `plus(n, m)` is not a pattern.
    A,
}

/// `M[m, val]` for a motive scoped `(Γ, m' : Nat, z : Rope_f(m'))`, with
/// `m`/`val` scoped `extra` binders past Γ.
fn mot2_at(depth: u32, m2: &Type, m: Term, val: Term, extra: u32) -> Type {
    m2.apply_local(
        &LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(m)).extended(rt(val)),
    )
}

/// The elimination `elim_Rope(m' z. M; nil; n x xs ih. cons; n m l r ihl ihr. cat; idx; val)`.
///
/// `nil_case : M[0, nil_f]` in `Γ`;
/// `cons_case : M[S n, cons_f n x xs]` in `(Γ, n, x : pay, xs : Rope_f(n), ih : M[n, xs])`;
/// `cat_case : M[plus n m, cat_f n m l r]` in
/// `(Γ, n, m, l : Rope_f(n), r : Rope_f(m), ihl : M[n, l], ihr : M[m, r])`.
#[allow(clippy::too_many_arguments)]
fn rope_rec(
    depth: u32,
    p: &Pay,
    mlvl: &Level,
    m2: &Type,
    nil_case: Term,
    cons_case: Term,
    cat_case: Term,
    idx: Term,
    val: Term,
    form: Form,
) -> Term {
    let l = p.lvl.clone();
    let ql = Level::max(Level::Zero, mlvl.clone());
    let pl = Level::max(l.clone(), ql.clone());

    // Q over (Γ, σ : Skel).
    let q = Type::Pi {
        dom_level: c(0),
        cod_level: ql.clone(),
        dom: rty(Type::Nat),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu(&p.sh(2), v(1)), v(0))),
            cod: rty(mot2_at(depth, m2, v(1), pairf(&p.sh(3), v(1), v(2), v(0)), 3)),
        }),
    };
    let q_at = |t: Term, extra: u32| -> Type {
        q.apply_local(&LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(t)))
    };

    // `ih_ty` at a given label/children pair: Π(i : Fin k). Q[nth(Skel; k; cs; i)].
    // `k` is `arity z` in the telescope and the *literal* arity inside a
    // branch (tier 1 §6.3) — one formula, two callers.
    let ih_ty_at = |k: Term, cs: Term, extra: u32| -> Type {
        let pe1 = p.sh(extra + 1);
        Type::Pi {
            dom_level: Level::Zero,
            cod_level: ql.clone(),
            dom: rty(fin(k.clone())),
            cod: rty(q_at(
                nth(
                    &l,
                    &rty(skel(&pe1)),
                    &rt(k.shift_local(1)),
                    rt(cs.shift_local(1)),
                    rt(v(0)),
                ),
                extra + 1,
            )),
        }
    };

    // P(z)'s tail — everything after the `cs'` binder, which is Var 0 here:
    //   Π(ih' : ih_ty[z, cs']). Q[sup_f(z; cs')]
    let p_tail = |z: Term, k: Term, extra: u32| -> Type {
        let pe1 = p.sh(extra + 1);
        Type::Pi {
            dom_level: ql.clone(),
            cod_level: ql.clone(),
            dom: rty(ih_ty_at(k, v(0), extra)),
            cod: rty(q_at(
                supf_(&pe1, z.shift_local(1), v(1)),
                extra + 1,
            )),
        }
    };

    // P(z), over a scope where `z` is the given term.
    let p_ty = |z: Term, extra: u32| -> Type {
        let pe = p.sh(extra);
        Type::Pi {
            dom_level: l.clone(),
            cod_level: ql.clone(),
            dom: rty(vec_skel(&pe, arity(&pe, z.clone()))),
            cod: rty(p_tail(
                z.shift_local(1),
                arity(&p.sh(extra + 1), z.shift_local(1)),
                extra + 1,
            )),
        }
    };

    // ---- the arms ------------------------------------------------------
    //
    // Each is `λ(cs' : Vec^l(Skel; m_lit)). λ(ih' : …). ⟦the Q-term⟧`, built
    // at the literal arity. In the arm's own scope `ih'` is Var 0 and `cs'`
    // is Var 1; `extra_b` is the branch binder's depth past Γ.
    let arm = |m_lit: usize, extra_b: u32, body: Term| -> Term {
        let pe = p.sh(extra_b);
        Term::Lam {
            dom_level: l.clone(),
            cod_level: ql.clone(),
            dom: rty(vec_skel(&pe, nat(m_lit as u64))),
            body: rt(Term::Lam {
                dom_level: ql.clone(),
                cod_level: ql.clone(),
                dom: rty(ih_ty_at(nat(m_lit as u64), v(0), extra_b + 1)),
                body: rt(body),
            }),
        }
    };

    // The pieces every arm's Q-term needs, at arm scope `d` (= extra_b + 2).
    let sh_at = |label: Term, d: u32| supf_(&p.sh(d), label, v(1));

    // ---- form B (§8.3) -------------------------------------------------
    //
    //   λm'. λe. transp(Nat; z. Π(e₀ : sEq(μ ŝ; z)). M[z, ⟨ŝ, e₀⟩];
    //                   μ ŝ; m'; e; λe₀. body) e
    //
    // The Π-motive is forced: `M[z, ⟨ŝ, ?⟩]` alone is unstateable, because
    // the pair's second component's type depends on `z`.
    let form_b = |sh: Term, d: u32, mk_body: &dyn Fn(u32) -> Term| -> Term {
        let mu_s = |k: u32| mu(&p.sh(d + k), sh.shift_local(k));
        // motive at (…, m', e, z) = d+3; inside its Π, (…, e₀) = d+4.
        let motive = Type::Pi {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu_s(3), v(0))),
            cod: rty(mot2_at(
                depth,
                m2,
                v(1),
                pairf(&p.sh(d + 4), v(1), sh.shift_local(4), v(0)),
                d + 4,
            )),
        };
        let tm = Term::Lam {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu_s(2), mu_s(2))),
            body: rt(mk_body(d + 3)),
        };
        let transp = Term::Transp {
            ty_level: c(0),
            motive_level: ql.clone(),
            ty: rty(Type::Nat),
            motive: rty(motive),
            lhs: rt(mu_s(2)),
            rhs: rt(v(1)),
            proof: rt(v(0)),
            tm: rt(tm),
        };
        Term::Lam {
            dom_level: c(0),
            cod_level: ql.clone(),
            dom: rty(Type::Nat),
            body: rt(Term::Lam {
                dom_level: c(0),
                cod_level: mlvl.clone(),
                dom: rty(seqn(mu_s(1), v(0))),
                body: rt(Term::App {
                    fun: rt(transp),
                    dom_level: c(0),
                    cod_level: mlvl.clone(),
                    dom: rty(seqn(mu_s(2), v(1))),
                    cod: rty(mot2_at(
                        depth,
                        m2,
                        v(2),
                        pairf(&p.sh(d + 3), v(2), sh.shift_local(3), v(0)),
                        d + 3,
                    )),
                    arg: rt(v(0)),
                }),
            }),
        }
    };

    // ---- the three constructors' bodies --------------------------------
    //
    // Arm scopes: Nil is (Γ, a, cs, ih, u, cs', ih') = Γ+6; Cons and Cat are
    // (Γ, a, cs, ih, y, ·, cs', ih') = Γ+7. In every arm `ih'` is Var 0 and
    // `cs'` is Var 1.
    let d_nil = 6u32;
    let d_cons = 7u32;
    let d_cat = 7u32;

    // `ih' ι_t` at a literal arity: Q[child_t].
    let ihq = |m_lit: usize, t: usize, d: u32, k: u32| -> Term {
        let pe1 = p.sh(d + k + 1);
        Term::App {
            fun: rt(v(k)),
            dom_level: Level::Zero,
            cod_level: ql.clone(),
            dom: rty(fin(nat(m_lit as u64))),
            // The codomain is `ih'`'s own, so it mentions the **bound**
            // index `i` (Var 0) — not `ι_t`. Substituting the literal here
            // typechecks nowhere and is the easiest annotation to get
            // subtly wrong, because the *result* type does use `ι_t`.
            cod: rty(q_at(
                nth(
                    &l,
                    &rty(skel(&pe1)),
                    &rt(nat(m_lit as u64)),
                    rt(v(k + 2)),
                    rt(v(0)),
                ),
                d + k + 1,
            )),
            arg: rt(fin_idx(t, m_lit)),
        }
    };

    // `Q[child]` applied at an index and a proof — the value-level ih the
    // arm hands the user's case (§8.1's table).
    let ih_val = |m_lit: usize, t: usize, d: u32, k: u32, at: Term, proof: Term| -> Term {
        let pe = p.sh(d + k);
        let child = child_at(&pe, m_lit, t, v(k + 1));
        let inner = Term::App {
            fun: rt(ihq(m_lit, t, d, k)),
            dom_level: c(0),
            cod_level: ql.clone(),
            dom: rty(Type::Nat),
            // Binds `m''`, so `child`/`cs'` move out by one — and only the
            // Π's *codomain* moves out by a second, for `e''`. Getting that
            // second shift wrong in the domain is the slip this annotation
            // exists to make visible.
            cod: rty(Type::Pi {
                dom_level: c(0),
                cod_level: mlvl.clone(),
                dom: rty(seqn(
                    mu(&p.sh(d + k + 1), child_at(&p.sh(d + k + 1), m_lit, t, v(k + 2))),
                    v(0),
                )),
                cod: rty(mot2_at(
                    depth,
                    m2,
                    v(1),
                    pairf(
                        &p.sh(d + k + 2),
                        v(1),
                        child_at(&p.sh(d + k + 2), m_lit, t, v(k + 3)),
                        v(0),
                    ),
                    d + k + 2,
                )),
            }),
            arg: rt(at.clone()),
        };
        Term::App {
            fun: rt(inner),
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu(&pe, child.clone()), at.clone())),
            cod: rty(mot2_at(
                depth,
                m2,
                at.shift_local(1),
                pairf(&p.sh(d + k + 1), at.shift_local(1), child.shift_local(1), v(0)),
                d + k + 1,
            )),
            arg: rt(proof),
        }
    };

    let subst_case = |case: &Term, extra: u32, args: Vec<Term>| -> Term {
        let mut s = LocalSubst::id(&scope(depth)).shift_local(extra);
        for a in args {
            s = s.extended(rt(a));
        }
        case.apply_local(&s)
    };

    // Nil, form B and A. `ŝ = sup_f(inl u; cs')`.
    let nil_label = |d: u32| -> Term {
        let pe = p.sh(d);
        Term::Inl {
            lhs_level: l.clone(),
            rhs_level: l.clone(),
            lhs: rty(sh_nil(&pe)),
            rhs: rty(sh_tail(&pe)),
            // the branch binder `u`, two binders out (cs', ih')
            val: rt(v(2)),
        }
    };
    let cons_label = |d: u32| -> Term {
        let pe = p.sh(d);
        Term::Inr {
            lhs_level: l.clone(),
            rhs_level: l.clone(),
            lhs: rty(sh_nil(&pe)),
            rhs: rty(sh_tail(&pe)),
            val: rt(Term::Inl {
                lhs_level: l.clone(),
                rhs_level: l.clone(),
                lhs: rty(sh_cons(&pe)),
                rhs: rty(sh_cat(&pe)),
                val: rt(v(2)),
            }),
        }
    };
    let cat_label = |d: u32| -> Term {
        let pe = p.sh(d);
        Term::Inr {
            lhs_level: l.clone(),
            rhs_level: l.clone(),
            lhs: rty(sh_nil(&pe)),
            rhs: rty(sh_tail(&pe)),
            val: rt(Term::Inr {
                lhs_level: l.clone(),
                rhs_level: l.clone(),
                lhs: rty(sh_cons(&pe)),
                rhs: rty(sh_cat(&pe)),
                val: rt(v(2)),
            }),
        }
    };

    // The payload `x` of a Cons label, at scope `d + k`: `fst` of the
    // branch binder.
    let cons_payload = |d: u32, k: u32| -> Term {
        let pe = p.sh(d + k);
        Term::Fst {
            fst_level: l.clone(),
            snd_level: l.clone(),
            fst_ty: rty(pe.ty.clone()),
            snd_ty: rty(unit_l(&l)),
            pair: rt(v(k + 2)),
        }
    };

    // -- Nil ------------------------------------------------------------
    let sh_nil_t = sh_at(nil_label(d_nil), d_nil);
    let nil_body_b = form_b(sh_nil_t.clone(), d_nil, &|k| {
        subst_case(&nil_case, d_nil + (k - d_nil), vec![])
    });
    let nil_body_a = {
        let d = d_nil;
        let mu_s = |k: u32| mu(&p.sh(d + k), sh_nil_t.shift_local(k));
        // elim_Nat motive over (…, m', ẑ) = d+2; inside its Π, d+3.
        let nmot = Type::Pi {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu_s(2), v(0))),
            cod: rty(mot2_at(
                depth,
                m2,
                v(1),
                pairf(&p.sh(d + 3), v(1), sh_nil_t.shift_local(3), v(0)),
                d + 3,
            )),
        };
        let base = Term::Lam {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu_s(1), Term::Zero)),
            body: rt(subst_case(&nil_case, d + 2, vec![])),
        };
        // (…, m', k, ihN) = d+3; body adds e.
        let goal = mot2_at(
            depth,
            m2,
            Term::Succ(rt(v(2))),
            pairf(&p.sh(d + 4), Term::Succ(rt(v(2))), sh_nil_t.shift_local(4), v(0)),
            d + 4,
        );
        let absurd = Term::Transp {
            ty_level: c(0),
            motive_level: c(0),
            ty: rty(Type::Nat),
            motive: rty(el_of(zero_pred(v(0)))),
            lhs: rt(mu_s(4)),
            rhs: rt(Term::Succ(rt(v(2)))),
            proof: rt(v(0)),
            tm: rt(Term::Triv { level: Level::Zero }),
        };
        let step = Term::Lam {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu_s(3), Term::Succ(rt(v(1))))),
            body: rt(Term::ElimEmpty {
                level: mlvl.clone(),
                scrut_level: Level::Zero,
                motive: rty(goal.shift_local(1)),
                scrut: rt(absurd),
            }),
        };
        Term::Lam {
            dom_level: c(0),
            cod_level: ql.clone(),
            dom: rty(Type::Nat),
            body: rt(Term::ElimNat {
                level: mlvl.clone(),
                motive: rty(nmot),
                base: rt(base),
                step: rt(step),
                scrut: rt(v(0)),
            }),
        }
    };

    // -- Cons -----------------------------------------------------------
    let sh_cons_t = sh_at(cons_label(d_cons), d_cons);
    let cons_body_b = form_b(sh_cons_t.clone(), d_cons, &|k| {
        let d = d_cons;
        let kk = k - d; // 3
        let pe = p.sh(k);
        let child = child_at(&pe, 1, 0, v(kk + 1));
        let n = mu(&pe, child.clone());
        let xs = pairf(&pe, n.clone(), child.clone(), srefl_n(n.clone()));
        let ih = ih_val(1, 0, d, kk, n.clone(), srefl_n(n.clone()));
        subst_case(&cons_case, k, vec![n, cons_payload(d, kk), xs, ih])
    });
    let cons_body_a = {
        let d = d_cons;
        let mu_s = |k: u32| mu(&p.sh(d + k), sh_cons_t.shift_local(k));
        let nmot = Type::Pi {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu_s(2), v(0))),
            cod: rty(mot2_at(
                depth,
                m2,
                v(1),
                pairf(&p.sh(d + 3), v(1), sh_cons_t.shift_local(3), v(0)),
                d + 3,
            )),
        };
        // Zero branch: μ ŝ is `S`-headed, so `sEq(μ ŝ; 0)` is absurd.
        let base = {
            let goal = mot2_at(
                depth,
                m2,
                Term::Zero,
                pairf(&p.sh(d + 2), Term::Zero, sh_cons_t.shift_local(2), v(0)),
                d + 2,
            );
            let absurd = Term::Transp {
                ty_level: c(0),
                motive_level: c(0),
                ty: rty(Type::Nat),
                motive: rty(el_of(is_succ(v(0)))),
                lhs: rt(mu_s(2)),
                rhs: rt(Term::Zero),
                proof: rt(v(0)),
                tm: rt(Term::Triv { level: Level::Zero }),
            };
            Term::Lam {
                dom_level: c(0),
                cod_level: mlvl.clone(),
                dom: rty(seqn(mu_s(1), Term::Zero)),
                body: rt(Term::ElimEmpty {
                    level: mlvl.clone(),
                    scrut_level: Level::Zero,
                    motive: rty(goal.shift_local(1)),
                    scrut: rt(absurd),
                }),
            }
        };
        // Succ branch, scope (…, m', k, ihN, e) = d+4: the inversion. The
        // tail's proof is re-derived by transp at the `pred` motive; the
        // stored proof is consulted nowhere, which is what makes β
        // definitional on open data (§8.2).
        let step = {
            let k4 = 4u32;
            let pe = p.sh(d + k4);
            let child = child_at(&pe, 1, 0, v(k4 + 1));
            let e_tail = Term::Transp {
                ty_level: c(0),
                motive_level: c(0),
                ty: rty(Type::Nat),
                motive: rty(seqn(
                    mu(
                        &p.sh(d + k4 + 1),
                        child_at(&p.sh(d + k4 + 1), 1, 0, v(k4 + 2)),
                    ),
                    pred(v(0)),
                )),
                lhs: rt(mu_s(4)),
                rhs: rt(Term::Succ(rt(v(2)))),
                proof: rt(v(0)),
                tm: rt(srefl_n(mu(&pe, child.clone()))),
            };
            let xs = pairf(&pe, v(2), child, e_tail.clone());
            let ih = ih_val(1, 0, d, k4, v(2), e_tail);
            let body = subst_case(
                &cons_case,
                d + k4,
                vec![v(2), cons_payload(d, k4), xs, ih],
            );
            Term::Lam {
                dom_level: c(0),
                cod_level: mlvl.clone(),
                dom: rty(seqn(mu_s(3), Term::Succ(rt(v(1))))),
                body: rt(body),
            }
        };
        Term::Lam {
            dom_level: c(0),
            cod_level: ql.clone(),
            dom: rty(Type::Nat),
            body: rt(Term::ElimNat {
                level: mlvl.clone(),
                motive: rty(nmot),
                base: rt(base),
                step: rt(step),
                scrut: rt(v(0)),
            }),
        }
    };

    // -- Cat (always form B: `plus(n, m)` is not a pattern) --------------
    let sh_cat_t = sh_at(cat_label(d_cat), d_cat);
    let cat_body = form_b(sh_cat_t.clone(), d_cat, &|k| {
        let d = d_cat;
        let kk = k - d;
        let pe = p.sh(k);
        let cl = child_at(&pe, 2, 0, v(kk + 1));
        let cr = child_at(&pe, 2, 1, v(kk + 1));
        let n = mu(&pe, cl.clone());
        let m = mu(&pe, cr.clone());
        let vl = pairf(&pe, n.clone(), cl.clone(), srefl_n(n.clone()));
        let vr = pairf(&pe, m.clone(), cr.clone(), srefl_n(m.clone()));
        let ihl = ih_val(2, 0, d, kk, n.clone(), srefl_n(n.clone()));
        let ihr = ih_val(2, 1, d, kk, m.clone(), srefl_n(m.clone()));
        subst_case(&cat_case, k, vec![n, m, vl, vr, ihl, ihr])
    });

    let (nil_body, cons_body) = match form {
        Form::B => (nil_body_b, cons_body_b),
        Form::A => (nil_body_a, cons_body_a),
    };

    // ---- the case tree and the two trailing applications ---------------
    let p3 = p.sh(3);
    let p4 = p.sh(4);
    let p5 = p.sh(5);
    let inner = Term::Case {
        lhs_level: l.clone(),
        rhs_level: l.clone(),
        motive_level: pl.clone(),
        // Scoped at the `Case` (under `y`), not under its motive binder.
        lhs: rty(sh_cons(&p4)),
        rhs: rty(sh_cat(&p4)),
        motive: rty(p_ty(
            Term::Inr {
                lhs_level: l.clone(),
                rhs_level: l.clone(),
                lhs: rty(sh_nil(&p5)),
                rhs: rty(sh_tail(&p5)),
                val: rt(v(0)),
            },
            5,
        )),
        case_l: rt(arm(1, 5, cons_body)),
        case_r: rt(arm(2, 5, cat_body)),
        scrut: rt(v(0)),
    };
    let cased = Term::Case {
        lhs_level: l.clone(),
        rhs_level: l.clone(),
        motive_level: pl.clone(),
        lhs: rty(sh_nil(&p3)),
        rhs: rty(sh_tail(&p3)),
        motive: rty(p_ty(v(0), 4)),
        case_l: rt(arm(0, 4, nil_body)),
        case_r: rt(inner),
        scrut: rt(v(2)),
    };
    let at_cs = Term::App {
        fun: rt(cased),
        dom_level: l.clone(),
        cod_level: ql.clone(),
        dom: rty(vec_skel(&p3, arity(&p3, v(2)))),
        cod: rty(p_tail(v(3), arity(&p4, v(3)), 4)),
        arg: rt(v(1)),
    };
    let step = Term::App {
        fun: rt(at_cs),
        dom_level: ql.clone(),
        cod_level: ql.clone(),
        dom: rty(ih_ty_at(arity(&p3, v(2)), v(1), 3)),
        cod: rty(q_at(supf_(&p4, v(3), v(2)), 4)),
        arg: rt(v(0)),
    };

    let s_val = fst_f(p, idx.clone(), val.clone());
    let recursion = Term::ElimWf {
        level: l.clone(),
        motive_level: ql.clone(),
        shape: rty(shape(p)),
        arity: rt(arity(&p.sh(1), v(0))),
        motive: rty(q.clone()),
        step: rt(step),
        scrut: rt(s_val.clone()),
    };
    // …applied at the index and the stored proof.
    let r1 = Term::App {
        fun: rt(recursion),
        dom_level: c(0),
        cod_level: ql.clone(),
        dom: rty(Type::Nat),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: mlvl.clone(),
            dom: rty(seqn(mu(&p.sh(1), s_val.shift_local(1)), v(0))),
            cod: rty(mot2_at(
                depth,
                m2,
                v(1),
                pairf(&p.sh(2), v(1), s_val.shift_local(2), v(0)),
                2,
            )),
        }),
        arg: rt(idx.clone()),
    };
    Term::App {
        fun: rt(r1),
        dom_level: c(0),
        cod_level: mlvl.clone(),
        dom: rty(seqn(mu(p, s_val.clone()), idx.clone())),
        cod: rty(mot2_at(
            depth,
            m2,
            idx.shift_local(1),
            pairf(&p.sh(1), idx.shift_local(1), s_val.shift_local(1), v(0)),
            1,
        )),
        arg: rt(snd_f(p, idx, val)),
    }
}

// ---------------------------------------------------------------------------
// The consumer: `to_nvec : Π m (v : Rope_f(m)). Vec^0(Nat; m)` — a dependent
// motive over the index, the fording analogue of the tier-1 prototype's
// `to_kvec`. `Cat` uses **both** ihs through `vappend`, so a swapped `Fin`
// index is a type error rather than a silent wrong answer (tier 1 §10 item 5's
// asymmetric-motive lesson).
// ---------------------------------------------------------------------------

fn nvec(m: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(Type::Nat), len: rt(m) }
}

/// `vappend n m u v : Vec(Nat; plus n m)`, by recursion on `n`.
fn vappend(depth: u32, n: Term, m: Term, u: Term, w: Term) -> Term {
    let _ = depth;
    let motive = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(nvec(v(0))),
        cod: rty(nvec(plus(v(1), m.shift_local(2)))),
    };
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(nvec(Term::Zero)),
        body: rt(w.shift_local(1)),
    };
    // (k, rec) ⊢ λ(u : Vec(Nat; S k)). ⟨fst u, rec (snd u)⟩; body scope +1.
    let step = {
        let head = Term::Fst {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: rty(Type::Nat),
            snd_ty: rty(nvec(v(3))),
            pair: rt(v(0)),
        };
        let tail = Term::Snd {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: rty(Type::Nat),
            snd_ty: rty(nvec(v(3))),
            pair: rt(v(0)),
        };
        let rec = Term::App {
            fun: rt(v(1)),
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(nvec(v(2))),
            cod: rty(nvec(plus(v(3), m.shift_local(4)))),
            arg: rt(tail),
        };
        Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(nvec(Term::Succ(rt(v(1))))),
            body: rt(Term::Pair {
                fst_level: c(0),
                snd_level: c(0),
                fst_ty: rty(Type::Nat),
                snd_ty: rty(nvec(plus(v(3), m.shift_local(4)))),
                fst: rt(head),
                snd: rt(rec),
            }),
        }
    };
    Term::App {
        fun: rt(Term::ElimNat {
            level: c(0),
            motive: rty(motive),
            base: rt(base),
            step: rt(step),
            scrut: rt(n.clone()),
        }),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(nvec(n.clone())),
        // The cod binds the argument even when it does not mention it, so
        // an open `n`/`m` must be shifted past that binder.
        cod: rty(nvec(plus(n.shift_local(1), m.shift_local(1)))),
        arg: rt(u),
    }
}

fn to_nvec(depth: u32, p: &Pay, idx: Term, val: Term, form: Form) -> Term {
    // Motive over (Γ, m', z): Vec(Nat; m').
    let m2 = nvec(v(1));
    let nil_case = Term::Triv { level: Level::Zero };
    // (Γ, n, x, xs, ih): ⟨0, ih⟩ : Vec(Nat; S n).
    let cons_case = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(v(4))),
        fst: rt(Term::Zero),
        snd: rt(v(0)),
    };
    // (Γ, n, m, l, r, ihl, ihr): append, at the index arithmetic the motive
    // demands — `Vec(Nat; plus n m)`.
    let cat_case = vappend(depth + 6, v(5), v(4), v(1), v(0));
    rope_rec(depth, p, &c(0), &m2, nil_case, cons_case, cat_case, idx, val, form)
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("the type does not check: {e:?}"));
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

fn nat_pay() -> Pay {
    Pay { ty: Type::Nat, lvl: c(0) }
}

// ---------------------------------------------------------------------------
// §13.1 item 1 — the `Wf` skeleton, forded
// ---------------------------------------------------------------------------

#[test]
fn wf_skeleton_and_measure_check_and_compute() {
    let p = nat_pay();
    let g = nil_ctx();

    // The skeleton is a `Wf`, and its constructors check.
    ck(&g, &snil(&p), &skel(&p), c(0));
    ck(&g, &scons(&p, nat(7), snil(&p)), &skel(&p), c(0));
    ck(&g, &scat(&p, snil(&p), scons(&p, nat(7), snil(&p))), &skel(&p), c(0));

    // Axis 1: `μ` *computes* on literal data (§5 fact 3).
    conv(&g, &mu(&p, snil(&p)), &Term::Zero, &Type::Nat, c(0));
    conv(&g, &mu(&p, scons(&p, nat(7), snil(&p))), &nat(1), &Type::Nat, c(0));
    let two = scat(&p, scons(&p, nat(1), snil(&p)), scons(&p, nat(2), snil(&p)));
    conv(&g, &mu(&p, two), &nat(2), &Type::Nat, c(0));

    // Axis 1, the other half: `μ` computes on **open** children too — the
    // property every arm below leans on. Γ = (s : Skel).
    let g1 = ext(&nil_ctx(), skel(&p), c(0));
    let p1 = nat_pay();
    conv(
        &g1,
        &mu(&p1, scons(&p1, nat(7), v(0))),
        &Term::Succ(rt(mu(&p1, v(0)))),
        &Type::Nat,
        c(0),
    );
    conv(
        &g1,
        &mu(&p1, scat(&p1, v(0), v(0))),
        &plus(mu(&p1, v(0)), mu(&p1, v(0))),
        &Type::Nat,
        c(0),
    );
}

#[test]
fn forded_family_and_constructors_check() {
    let p = nat_pay();
    let g = nil_ctx();

    ck(&g, &fnil(&p), &ropef(&p, Term::Zero), c(0));
    let one = fcons(&p, Term::Zero, nat(7), fnil(&p));
    ck(&g, &one, &ropef(&p, nat(1)), c(0));
    let two = fcat(&p, nat(1), nat(1), one.clone(), one.clone());
    ck(&g, &two, &ropef(&p, plus(nat(1), nat(1))), c(0));
    // …and at the computed index's *value*: `plus 1 1 ≡ 2`, a checking
    // position across the equation.
    ck(&g, &two, &ropef(&p, nat(2)), c(0));

    // Axis: neutral. Γ = (n, m, x, l : Rope_f(n), r : Rope_f(m)) — every
    // constructor with open children *and* open indices.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, ropef(&p, v(2)), c(0));
    let g = ext(&g, ropef(&p, v(2)), c(0));
    // n = 4, m = 3, x = 2, l = 1, r = 0.
    ck(&g, &fcons(&p, v(4), v(2), v(1)), &ropef(&p, Term::Succ(rt(v(4)))), c(0));
    ck(&g, &fcat(&p, v(4), v(3), v(1), v(0)), &ropef(&p, plus(v(4), v(3))), c(0));
}

#[test]
fn the_eliminator_computes_on_literal_data() {
    // Axis 1 for the eliminator: literal scrutinee, asserted to *compute*
    // against the expected reduct rather than merely to type.
    let p = nat_pay();
    let g = nil_ctx();

    let t0 = to_nvec(0, &p, Term::Zero, fnil(&p), Form::B);
    ck(&g, &t0, &nvec(Term::Zero), c(0));
    conv(&g, &t0, &Term::Triv { level: Level::Zero }, &nvec(Term::Zero), c(0));

    let one = fcons(&p, Term::Zero, nat(7), fnil(&p));
    let t1 = to_nvec(0, &p, nat(1), one.clone(), Form::B);
    ck(&g, &t1, &nvec(nat(1)), c(0));
    let expect1 = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(Term::Zero)),
        fst: rt(Term::Zero),
        snd: rt(Term::Triv { level: Level::Zero }),
    };
    conv(&g, &t1, &expect1, &nvec(nat(1)), c(0));

    // Through `Cat`, where the arm uses both ihs and the index is computed.
    let two = fcat(&p, nat(1), nat(1), one.clone(), one);
    let t2 = to_nvec(0, &p, nat(2), two, Form::B);
    ck(&g, &t2, &nvec(nat(2)), c(0));
    let expect2 = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(nat(1))),
        fst: rt(Term::Zero),
        snd: rt(expect1),
    };
    conv(&g, &t2, &expect2, &nvec(nat(2)), c(0));
}

#[test]
fn the_eliminator_is_typed_on_a_neutral_scrutinee() {
    // Axis 2: neutral scrutinee — stuck, but typed at the family instance
    // over the open index.
    let p = nat_pay();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, ropef(&p, v(0)), c(0));
    ck(&g, &to_nvec(2, &p, v(1), v(0), Form::B), &nvec(v(1)), c(0));
    ck(&g, &to_nvec(2, &p, v(1), v(0), Form::A), &nvec(v(1)), c(0));
}

// ---------------------------------------------------------------------------
// §13.1 item 2 — the transp-only eliminator, MEASURED
// ---------------------------------------------------------------------------

#[test]
fn form_b_beta_fires_on_closed_data_and_stalls_on_open_data() {
    // The measurement §8.4 of the fording doc marks as owed, and the one
    // `indexed_route_2b.rs` never took (it built only the inverting
    // eliminator). Both halves are asserted, the negative deliberately.
    let p = nat_pay();

    // (a) Closed data: the stored proof whnfs to `srefl`, the arm's transp
    // β-fires, and the eliminator lands on the reduct. Pinned by
    // `the_eliminator_computes_on_literal_data` above; repeated here at
    // `Cat` with a *convertible-not-equal* index spelling, a checking
    // position across the equation.
    let g = nil_ctx();
    let one = fcons(&p, Term::Zero, nat(7), fnil(&p));
    let two = fcat(&p, nat(1), nat(1), one.clone(), one.clone());
    let t = to_nvec(0, &p, plus(nat(1), nat(1)), two, Form::B);
    ck(&g, &t, &nvec(nat(2)), c(0));

    // (b) Open recursive data: the value's stored proof is neutral, so the
    // arm's `transp` does not β and the residue is a stuck
    // `App(transp …, e)`. The head-only strip cannot reach it — the head of
    // the compared term is the `App`
    // (docs/metatheory-ch07-extensions.md §22.1's `elim(cast)` shape in a
    // new position), *although* at the redex the transp's endpoints
    // `μ ŝ` and the index ARE convertible: β-reduction manufactures a
    // redundant cast out of a redundancy-free term (§22.3's honest limit,
    // met in the wild).
    //
    // Γ = (n, x, xs : Rope_f(n)); n = 2, x = 1, xs = 0.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, ropef(&p, v(1)), c(0));
    let w = fcons(&p, v(2), v(1), v(0));
    let lhs = to_nvec(3, &p, Term::Succ(rt(v(2))), w, Form::B);
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(v(3))),
        fst: rt(Term::Zero),
        snd: rt(to_nvec(3, &p, v(2), v(0), Form::B)),
    };
    let at = nvec(Term::Succ(rt(v(2))));
    ck(&g, &lhs, &at, c(0));
    ck(&g, &rhs, &at, c(0));
    not_conv(&g, &lhs, &rhs, &at, c(0));

    // (c) The cause is the **stored proof**, not the open data — the
    // distinction §8.4's third bullet turns on. The same *open* skeleton
    // carrying a `srefl` proof at its own measure β-fires: nothing about
    // the element, the tail or the index changed, only whether the arm's
    // `transp` meets a canonical proof.
    // `xs : Rope_f(n)` with n = Var 2 in this Γ — the projection's own
    // annotation carries that index.
    let tail_s = fst_f(&p, v(2), v(0));
    let mu_tail = mu(&p, tail_s.clone());
    let sh_open = scons(&p, v(1), tail_s.clone());
    let mu_open = mu(&p, sh_open.clone());
    let w2 = pairf(&p, mu_open.clone(), sh_open, srefl_n(mu_open.clone()));
    let lhs2 = to_nvec(3, &p, mu_open.clone(), w2, Form::B);
    let rhs2 = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(mu_tail.shift_local(1))),
        fst: rt(Term::Zero),
        snd: rt(to_nvec(
            3,
            &p,
            mu_tail.clone(),
            pairf(&p, mu_tail.clone(), tail_s, srefl_n(mu_tail)),
            Form::B,
        )),
    };
    let at2 = nvec(mu_open);
    ck(&g, &lhs2, &at2, c(0));
    conv(&g, &lhs2, &rhs2, &at2, c(0));
}

// ---------------------------------------------------------------------------
// §13.1 item 3 — form A inside a ford
// ---------------------------------------------------------------------------

#[test]
fn form_a_beta_is_definitional_on_open_recursive_data() {
    // The same declaration, the same scrutinee, the *inverting* arm: β fires
    // with the element, the tail and the index all open. The stored proof is
    // consulted nowhere — every equation the arm produces sits at `sEq`.
    let p = nat_pay();
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, ropef(&p, v(1)), c(0));
    let w = fcons(&p, v(2), v(1), v(0));
    let lhs = to_nvec(3, &p, Term::Succ(rt(v(2))), w, Form::A);
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(v(3))),
        fst: rt(Term::Zero),
        snd: rt(to_nvec(3, &p, v(2), v(0), Form::A)),
    };
    let at = nvec(Term::Succ(rt(v(2))));
    ck(&g, &lhs, &at, c(0));
    conv(&g, &lhs, &rhs, &at, c(0));

    // The `Nil` arm's inversion, at a convertible-not-equal index spelling.
    let g0 = nil_ctx();
    let t = to_nvec(0, &p, plus(Term::Zero, Term::Zero), fnil(&p), Form::A);
    conv(&g0, &t, &Term::Triv { level: Level::Zero }, &nvec(Term::Zero), c(0));

    // And the form-B `Cat` arm still computes inside the same eliminator.
    let one = fcons(&p, Term::Zero, nat(7), fnil(&p));
    let two = fcat(&p, nat(1), nat(1), one.clone(), one);
    let t2 = to_nvec(0, &p, nat(2), two, Form::A);
    ck(&g0, &t2, &nvec(nat(2)), c(0));
}

// ---------------------------------------------------------------------------
// §13.1 item 4 — negative controls (axis 4)
// ---------------------------------------------------------------------------

#[test]
fn negative_controls_mismatched_indices_reject() {
    let p = nat_pay();
    let g = nil_ctx();

    // `nil_f` is not at index 1.
    ck_fails(&g, &fnil(&p), &ropef(&p, nat(1)), c(0));

    // The quotient control: a length-1 skeleton cannot inhabit `Rope_f(0)`,
    // whatever proof is tried. Dropping the `sEq` component (or an
    // unfaithful `μ`) is exactly what this would stop catching.
    let s1 = scons(&p, nat(9), snil(&p));
    for proof in [srefl_n(Term::Zero), srefl_n(nat(1))] {
        let bad = pairf(&p, Term::Zero, s1.clone(), proof);
        ck_fails(&g, &bad, &ropef(&p, Term::Zero), c(0));
    }

    // Distinct *neutral* indices do not convert.
    let g2 = ext(&ext(&nil_ctx(), Type::Nat, c(0)), Type::Nat, c(0));
    let g2 = ext(&g2, ropef(&p, v(1)), c(0));
    ck_fails(&g2, &v(0), &ropef(&p, v(1)), c(0));

    // Off-by-one on an open index, at a *computed* one: `cat_f n m l r` does
    // not check at `Rope_f(S (plus n m))`.
    let g3 = ext(&nil_ctx(), Type::Nat, c(0));
    let g3 = ext(&g3, Type::Nat, c(0));
    let g3 = ext(&g3, ropef(&p, v(1)), c(0));
    let g3 = ext(&g3, ropef(&p, v(1)), c(0));
    // n = 3, m = 2, l = 1, r = 0.
    let t = fcat(&p, v(3), v(2), v(1), v(0));
    ck(&g3, &t, &ropef(&p, plus(v(3), v(2))), c(0));
    ck_fails(&g3, &t, &ropef(&p, Term::Succ(rt(plus(v(3), v(2))))), c(0));

    // Irrelevance does not leak into the data: same index, different
    // elements — inconvertible; same elements — convertible.
    let a = fcons(&p, Term::Zero, nat(1), fnil(&p));
    let b = fcons(&p, Term::Zero, nat(2), fnil(&p));
    not_conv(&g, &a, &b, &ropef(&p, nat(1)), c(0));
    conv(&g, &a, &a.clone(), &ropef(&p, nat(1)), c(0));
}

// ---------------------------------------------------------------------------
// §13.1 item 5 — value equality costs no transport lemmas
// ---------------------------------------------------------------------------

#[test]
fn value_equality_needs_no_transport_lemmas() {
    let p = nat_pay();
    // Γ = (n, w : Rope_f(n), e2 : sEq(Nat; μ (fst w); n)) — a *different*
    // proof of the same equation than the one stored in `w`.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, ropef(&p, v(0)), c(0));
    let g = ext(&g, seqn(mu(&p, fst_f(&p, v(1), v(0))), v(1)), c(0));
    // n = 2, w = 1, e2 = 0.
    let repacked = pairf(&p, v(2), fst_f(&p, v(2), v(1)), v(0));
    conv(&g, &repacked, &v(1), &ropef(&p, v(2)), c(0));

    // The would-be cross-spelling transport lemma is `refl`: the same value
    // consumed at `n` and at `plus 0 n` gives the same vector definitionally.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, ropef(&p, plus(Term::Zero, v(0))), c(0));
    // n = 1, w = 0.
    let lhs = to_nvec(2, &p, v(1), v(0), Form::B);
    let rhs = to_nvec(2, &p, plus(Term::Zero, v(1)), v(0), Form::B);
    let at = nvec(v(1));
    let goal =
        Type::Id { level: c(0), ty: rty(at.clone()), lhs: rt(lhs.clone()), rhs: rt(rhs) };
    let proof = Term::Refl { level: c(0), ty: rty(at), tm: rt(lhs) };
    ck(&g, &proof, &goal, c(0));
}

// ---------------------------------------------------------------------------
// §13.1 item 6 — the F1/F2 falsifier
// ---------------------------------------------------------------------------

#[test]
fn f2_falsifier_a_shared_child_index_is_unenforceable() {
    // Suppose the declaration had been
    //   `Cat(n: Nat, l: Rope(n), r: Rope(n)) : Rope(plus(n, n))`
    // — F2's rejection (§3.3). The generator would have to pick *one* child
    // to recompute `n` from, since the skeleton cannot record that the two
    // agree (a label cannot mention its children, tier 1 §2). `mu_gen(…,
    // left_only = true)` is that measure.
    //
    // What it admits, and what the rejection therefore prevents: a value
    // whose two children have *different* measures still inhabits the
    // family at the index the declaration says both of them have.
    let p = nat_pay();
    let g = nil_ctx();
    let left = snil(&p); // μ = 0
    let right = scons(&p, nat(9), snil(&p)); // μ = 1
    let bad = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(skel(&p)),
        snd_ty: rty(seqn(mu_gen(&p.sh(1), v(0), true), Term::Zero)),
        fst: rt(scat(&p, left, right)),
        snd: rt(srefl_n(Term::Zero)),
    };
    // It checks — at index 0, i.e. "both children are empty", with a
    // one-element right child. The encoding is a quotient of the declared
    // family, which is why F2 is a restriction and not caution.
    ck(&g, &bad, &ropef_gen(&p, Term::Zero, true), c(0));

    // The faithful measure rejects the same value at the same index, which
    // is the contrast that makes the falsifier a falsifier rather than a
    // typo: with `μ = plus (μ l) (μ r)` the index is 1, not 0.
    let honest = pairf(
        &p,
        Term::Zero,
        scat(&p, snil(&p), scons(&p, nat(9), snil(&p))),
        srefl_n(Term::Zero),
    );
    ck_fails(&g, &honest, &ropef(&p, Term::Zero), c(0));
}

// ---------------------------------------------------------------------------
// Axis 2 — the open payload type
// ---------------------------------------------------------------------------

#[test]
fn open_payload_type_instance() {
    // Γ = (A : Ty 0, n : Nat, x : El A, xs : Rope_f(A; n)); A = 3, n = 2,
    // x = 1, xs = 0. A de Bruijn slip in any schema above stops being the
    // identity here.
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, el_of(v(1)), c(0));
    let p = Pay { ty: el_of(v(2)), lvl: c(0) };
    let g = ext(&g, ropef(&p, v(1)), c(0));

    let p = Pay { ty: el_of(v(3)), lvl: c(0) };
    let t = fcons(&p, v(2), v(1), v(0));
    ck(&g, &t, &ropef(&p, Term::Succ(rt(v(2)))), c(0));

    // β on open recursive data at the open payload type, form A.
    let lhs = to_nvec(4, &p, Term::Succ(rt(v(2))), t, Form::A);
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(v(3))),
        fst: rt(Term::Zero),
        snd: rt(to_nvec(4, &p, v(2), v(0), Form::A)),
    };
    let at = nvec(Term::Succ(rt(v(2))));
    ck(&g, &lhs, &at, c(0));
    conv(&g, &lhs, &rhs, &at, c(0));
}

// ---------------------------------------------------------------------------
// §13.1 item 7 — a nonzero level
// ---------------------------------------------------------------------------

#[test]
fn fields_above_level_zero() {
    // A `Type`-valued payload field: the skeleton and the family live at
    // level 1 while the motive stays at 0, so every `l ⊔ mlvl` that was
    // silently `mlvl` at level 0 is now a different level (§6.2, route 1
    // §10.5's lesson).
    let p = Pay { ty: Type::Ty(c(0)), lvl: c(1) };
    let g = nil_ctx();

    ck(&g, &snil(&p), &skel(&p), c(1));
    ck(&g, &fnil(&p), &ropef(&p, Term::Zero), c(1));
    let one = fcons(&p, Term::Zero, Term::TmNat, fnil(&p));
    ck(&g, &one, &ropef(&p, nat(1)), c(1));
    let two = fcat(&p, nat(1), nat(1), one.clone(), one.clone());
    ck(&g, &two, &ropef(&p, nat(2)), c(1));

    // The eliminator at a level-0 motive over a level-1 family, computing.
    let t = to_nvec(0, &p, nat(2), two, Form::B);
    ck(&g, &t, &nvec(nat(2)), c(0));
    let expect1 = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(Term::Zero)),
        fst: rt(Term::Zero),
        snd: rt(Term::Triv { level: Level::Zero }),
    };
    let expect2 = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(nat(1))),
        fst: rt(Term::Zero),
        snd: rt(expect1),
    };
    conv(&g, &t, &expect2, &nvec(nat(2)), c(0));

    // And form A, on open recursive data, at level 1.
    let g1 = ext(&nil_ctx(), Type::Nat, c(0));
    let g1 = ext(&g1, ropef(&p, v(0)), c(1));
    let w = fcons(&p, v(1), Term::TmNat, v(0));
    let lhs = to_nvec(2, &p, Term::Succ(rt(v(1))), w, Form::A);
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(nvec(v(2))),
        fst: rt(Term::Zero),
        snd: rt(to_nvec(2, &p, v(1), v(0), Form::A)),
    };
    let at = nvec(Term::Succ(rt(v(1))));
    ck(&g1, &lhs, &at, c(0));
    conv(&g1, &lhs, &rhs, &at, c(0));
}

