//! Indexed-families route 1 hand prototype: the family by large elimination
//! on the index (`docs/inductive-indexed-lowering.md`; section numbers below
//! are that document's).
//!
//! The forcing function for the route-1 round of `issues/indexed-families.md`:
//! before a generator emits indexed declarations, the encoding is built by
//! hand at the kernel level and checked by the real kernel. Three
//! declarations, chosen to cover the scheme's load-bearing claims:
//!
//! - `Vec<E>`  — the motivating example, at an **open element code** `e : Ty 0`
//!   (the open-element axis of `docs/testing-generated-terms.md`);
//! - `Fin`     — an `Empty` branch doing real work, two constructors in one
//!   index class, and within-class no-confusion (§7);
//! - `Tree`    — `Node(n, l: Tree(n), r: Tree(n)) : Tree(S n)`: **branching
//!   is free** (§5.1), the claim that separates this scheme from
//!   exact-height fording, whose §8.1 wall was precisely here.
//!
//! Nothing uses the elaborator; the terms are what the generator will emit.
//! Elisions, as in the sibling prototypes: the tier-0 nominal tag (field 0 of
//! every constructor, mechanical) and the `Unit` terminator of field spines.
//! With those elided, single-constructor classes have no sum and one-field
//! spines are the field itself.

use std::sync::Arc as Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalSubst, LocalVar, Term, Type,
};
use heather_kernel::typing::{check_term, check_type};

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
    LocalCtx::nil()
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

/// A context of `n` entries for building substitutions: `LocalSubst::id`
/// reads only the length and the base.
fn scope(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: c(0) }).collect::<Vec<_>>()).into(),
    }
}

fn el(t: Term) -> Type {
    Type::El { level: c(0), tm: rt(t) }
}

/// `M[h, z]` for a motive scoped in `(Γ, h : Nat, z : El (fam h))`, with `h`
/// and `z` scoped in Γ extended by `extra` binders.
fn mot_at(depth: u32, motive: &Type, h: Term, z: Term, extra: u32) -> Type {
    motive.apply_local(
        &LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(h)).extended(rt(z)),
    )
}

// ---------------------------------------------------------------------------
// §4 The family, generically: one `elim_Nat` at motive `Ty 0`, one branch
// per index-constructor class. The three declarations differ only in the two
// branch codes.
// ---------------------------------------------------------------------------

/// `fam(base; step; e) : Ty 0` by `elim_Nat` at the large motive. `step` is
/// scoped in `(Γ, m : Nat, rec : Ty 0)`.
fn fam(base: Term, step: Term, idx: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(base),
        step: rt(step),
        scrut: rt(idx),
    }
}

// ---------------------------------------------------------------------------
// `Vec<E> : (n : Nat) -> Type { Nil : Vec(0), Cons(n, x: E, xs: Vec(n)) :
// Vec(Succ(n)) }` — at an open element *code* `e : Ty 0`, so the element
// type is `El e` throughout. The pattern-variable field `n` is not stored
// (§4.1): the `Zero` branch is `⌜Unit⌝` (Nil's empty spine), the `Succ`
// branch `⌜Σ(x : El e). El rec⌝` (Cons minus `n`).
// ---------------------------------------------------------------------------

/// `famVec e n : Ty 0`. `e` is scoped in the ambient Γ; inside the step it
/// sits under `(m, rec)`, and inside the Σ-code's `snd` one deeper, where
/// `rec` is `Var 1` (`TmSigma`'s `snd` binds; its `fst` does not).
fn vec_fam(e: Term, idx: Term) -> Term {
    fam(
        Term::TmUnit { level: Level::Zero },
        Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(e.shift_local(2)),
            snd: rt(v(1)),
        },
        idx,
    )
}

fn vec_ty(e: Term, idx: Term) -> Type {
    el(vec_fam(e, idx))
}

/// `Nil = ⟨⟩` — `famVec e 0 ⇝ ⌜Unit⌝`.
fn vnil() -> Term {
    Term::Triv { level: Level::Zero }
}

/// `Cons(n, x, xs) = pair(x; xs)` at `Vec(S n)` — the index argument `n`
/// appears in the *annotations only* (§5): the value stores no index and no
/// proof. `famVec e (S n)` unfolds whatever `n` is, which is why this checks
/// (and β-fires) on fully open arguments.
fn vcons(e: Term, n: Term, x: Term, xs: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el(e.clone())),
        snd_ty: rty(vec_ty(e.shift_local(1), n.shift_local(1))),
        fst: rt(x),
        snd: rt(xs),
    }
}

/// A closed `Vec<Nat>` literal, indices descending toward `Nil`.
fn nat_vec(elems: &[u64]) -> Term {
    let mut t = vnil();
    for (k, &x) in elems.iter().rev().enumerate() {
        t = vcons(Term::TmNat, nat(k as u64), nat(x), t);
    }
    t
}

/// §6: the derived eliminator. `motive` is scoped in `(Γ, h : Nat,
/// z : El (famVec e h))` at level `ml`; `nil_case` in Γ; `cons_case` in
/// `(Γ, n : Nat, x : El e, xs : Vec(n), ih : M[n, xs])` — note the arm
/// *binds the pattern variable*: it is the `elim_Nat` binder, recovered for
/// free (§4.1). `idx`/`scrut` are the scrutinee's index and value.
fn vec_elim(
    depth: u32,
    ml: &Level,
    e: Term,
    motive: &Type,
    nil_case: Term,
    cons_case: Term,
    idx: Term,
    scrut: Term,
) -> Term {
    // Mot(h) = Π(pv : El (famVec e h)). M[h, pv] — the Π's binder is
    // exactly the motive's `z`, so `cod` is the motive verbatim.
    let mot_pi = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_ty(e.clone().shift_local(1), v(0))),
        cod: rty(motive.clone()),
    };

    // base : Mot(0). `famVec e 0 ⇝ ⌜Unit⌝`, so the bound payload is
    // irrelevant (Unit η) and the body is the nil case weakened.
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_ty(e.clone(), Term::Zero)),
        body: rt(nil_case.shift_local(1)),
    };

    // step, scoped (Γ, m : Nat, rec : Mot(m)):
    //   λ(pv : El (famVec e (S m))). cons_case[m, fst pv, snd pv, rec (snd pv)]
    // In (Γ, m, rec, pv): m = Var 2, rec = Var 1, pv = Var 0, and
    // `famVec e (S m)` whnf-reduces to `Σ(x : El e). El (famVec e m)`.
    let fst_ann = || rty(el(e.clone().shift_local(3)));
    let snd_ann = || rty(vec_ty(e.clone().shift_local(4), v(3)));
    let x_proj = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: fst_ann(),
        snd_ty: snd_ann(),
        pair: rt(v(0)),
    };
    let xs_proj = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: fst_ann(),
        snd_ty: snd_ann(),
        pair: rt(v(0)),
    };
    let ih = Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_ty(e.clone().shift_local(3), v(2))),
        cod: rty(mot_at(depth, motive, v(3), v(0), 4)),
        arg: rt(xs_proj.clone()),
    };
    let step_body = cons_case.apply_local(
        &LocalSubst::id(&scope(depth))
            .shift_local(3)
            .extended(rt(v(2)))
            .extended(rt(x_proj))
            .extended(rt(xs_proj))
            .extended(rt(ih)),
    );
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_ty(e.clone().shift_local(2), Term::Succ(rt(v(1))))),
        body: rt(step_body),
    };

    // The recursion applied to the scrutinee. §6's second composition point:
    // the motive's instance at the scrutinee is `M[idx, scrut]` directly —
    // no repackaging pair, no Σ-η obligation on the index side.
    Term::App {
        fun: rt(Term::ElimNat {
            level: ml.clone(),
            motive: rty(mot_pi),
            base: rt(base),
            step: rt(step),
            scrut: rt(idx.clone()),
        }),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec_ty(e, idx.clone())),
        cod: rty(mot_at(depth, motive, idx.shift_local(1), v(0), 1)),
        arg: rt(scrut),
    }
}

/// `plus`, recursing on its **first** argument, so `plus (S n) m ⇝
/// S (plus n m)` and `plus 0 m ⇝ m` — the reductions `append`'s arm and
/// base obligations lean on (§9 item 3).
fn plus(a: Term, b: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(b),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(a),
    }
}

/// `append : Vec(n) → Vec(m) → Vec(plus n m)` by the eliminator at the
/// index-dependent motive `M[h, z] = Vec(plus h m)`.
fn append(depth: u32, e: Term, n_idx: Term, m_idx: Term, xs: Term, ys: Term) -> Term {
    let motive = vec_ty(
        e.clone().shift_local(2),
        plus(v(1), m_idx.clone().shift_local(2)),
    );
    // (Γ, n, x, xs', ih) ⊢ Cons(plus n m, x, ih) : Vec(S (plus n m)),
    // owed M[S n] = Vec(plus (S n) m) — convertible because `plus` recurses
    // on its first argument. The definitional-index-arithmetic claim.
    let cons_case = vcons(
        e.clone().shift_local(4),
        plus(v(3), m_idx.shift_local(4)),
        v(2),
        v(0),
    );
    vec_elim(depth, &c(0), e, &motive, ys, cons_case, n_idx, xs)
}

// ---------------------------------------------------------------------------
// `Fin : (n : Nat) -> Type { FZ(n) : Fin(S n), FS(n, i: Fin(n)) : Fin(S n) }`
// — both constructors in the `Succ` class, so that branch is a real sum;
// the `Zero` class is empty, so `famFin 0 = ⌜Empty⌝` (§4: a correct branch,
// not a degenerate one).
// ---------------------------------------------------------------------------

/// `famFin n : Ty 0`. `TmSum` binds nothing, so `rec` is `Var 0` in both
/// summands' scope.
fn fin_fam(idx: Term) -> Term {
    fam(
        Term::TmEmpty { level: Level::Zero },
        Term::TmSum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rt(Term::TmUnit { level: Level::Zero }),
            rhs: rt(v(0)),
        },
        idx,
    )
}

fn fin_ty(idx: Term) -> Type {
    el(fin_fam(idx))
}

/// `FZ(n) = inl ⟨⟩` at `Fin(S n)` — the pattern-variable field is the index.
fn fz(n: Term) -> Term {
    Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(fin_ty(n)),
        val: rt(Term::Triv { level: Level::Zero }),
    }
}

/// `FS(n, i) = inr i` at `Fin(S n)`.
fn fs(n: Term, i: Term) -> Term {
    Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(fin_ty(n)),
        val: rt(i),
    }
}

/// §7 within-class no-confusion: the tag predicate over the `Succ` branch's
/// sum, as a *code* — `⌜Unit⌝` at `inl`, `⌜Empty⌝` at `inr`. Tier 0 §6.1
/// verbatim, because inside the branch the type *is* a tier-0 sum.
fn is_fz(n: Term, y: Term) -> Term {
    Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(1),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(fin_ty(n)),
        motive: rty(Type::Ty(c(0))),
        case_l: rt(Term::TmUnit { level: Level::Zero }),
        case_r: rt(Term::TmEmpty { level: Level::Zero }),
        scrut: rt(y),
    }
}

// ---------------------------------------------------------------------------
// `Tree : (n : Nat) -> Type { Leaf : Tree(0), Node(n, l: Tree(n),
// r: Tree(n)) : Tree(S n) }` — §5.1: two recursive fields, both at the
// pattern variable, `El rec` spliced twice. No height computation, no
// `max`, no `D_below`.
// ---------------------------------------------------------------------------

/// `famTree n : Ty 0`. In `(Γ, m, rec)` the Σ-code's `fst` sees `rec` as
/// `Var 0`; its `snd` binds one, so there `rec` is `Var 1`.
fn tree_fam(idx: Term) -> Term {
    fam(
        Term::TmUnit { level: Level::Zero },
        Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(v(0)),
            snd: rt(v(1)),
        },
        idx,
    )
}

fn tree_ty(idx: Term) -> Type {
    el(tree_fam(idx))
}

fn leaf() -> Term {
    Term::Triv { level: Level::Zero }
}

/// `Node(n, l, r) = pair(l; r)` at `Tree(S n)` — a branching constructor in
/// constructor form with both children open.
fn node(n: Term, l: Term, r: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(tree_ty(n.clone())),
        snd_ty: rty(tree_ty(n.shift_local(1))),
        fst: rt(l),
        snd: rt(r),
    }
}

/// The `Tree` eliminator. `node_case` is scoped
/// `(Γ, n, l, r, ih_l, ih_r)` — two children, two ihs, both drawn from the
/// *same* `rec` because both children sit at the same pattern variable.
fn tree_elim(
    depth: u32,
    ml: &Level,
    motive: &Type,
    leaf_case: Term,
    node_case: Term,
    idx: Term,
    scrut: Term,
) -> Term {
    let mot_pi = Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(tree_ty(v(0))),
        cod: rty(motive.clone()),
    };
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(tree_ty(Term::Zero)),
        body: rt(leaf_case.shift_local(1)),
    };
    // (Γ, m, rec, pv) with pv : Σ(_ : Tree(m)). Tree(m) after whnf.
    let fst_ann = || rty(tree_ty(v(2)));
    let snd_ann = || rty(tree_ty(v(3)));
    let l_proj = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: fst_ann(),
        snd_ty: snd_ann(),
        pair: rt(v(0)),
    };
    let r_proj = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: fst_ann(),
        snd_ty: snd_ann(),
        pair: rt(v(0)),
    };
    let ih = |child: &Term| Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(tree_ty(v(2))),
        cod: rty(mot_at(depth, motive, v(3), v(0), 4)),
        arg: rt(child.clone()),
    };
    let step_body = node_case.apply_local(
        &LocalSubst::id(&scope(depth))
            .shift_local(3)
            .extended(rt(v(2)))
            .extended(rt(l_proj.clone()))
            .extended(rt(r_proj.clone()))
            .extended(rt(ih(&l_proj)))
            .extended(rt(ih(&r_proj))),
    );
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(tree_ty(Term::Succ(rt(v(1))))),
        body: rt(step_body),
    };
    Term::App {
        fun: rt(Term::ElimNat {
            level: ml.clone(),
            motive: rty(mot_pi),
            base: rt(base),
            step: rt(step),
            scrut: rt(idx.clone()),
        }),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(tree_ty(idx.clone())),
        cod: rty(mot_at(depth, motive, idx.shift_local(1), v(0), 1)),
        arg: rt(scrut),
    }
}

/// `mirror : Tree(n) → Tree(n)` — swap the children, motive `Tree(h)`.
fn mirror(depth: u32, idx: Term, scrut: Term) -> Term {
    // (Γ, n, l, r, ih_l, ih_r) ⊢ Node(n, ih_r, ih_l)
    let node_case = node(v(4), v(0), v(1));
    tree_elim(depth, &c(0), &tree_ty(v(1)), leaf(), node_case, idx, scrut)
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .expect("the type is well-formed");
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn ck_fails(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("the kernel gate must reject this");
}

fn ty_fails(gamma: &LocalCtx, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .expect_err("the type must be ill-formed");
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
// Contexts
// ---------------------------------------------------------------------------

/// `[e : Ty 0, n : Nat, x : El e, xs : Vec<e>(n)]` — everything open:
/// element code, index, element, tail. `e = Var 3, n = Var 2, x = Var 1,
/// xs = Var 0`.
fn vec_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, el(v(1)), c(0));
    ext(&g, vec_ty(v(2), v(1)), c(0))
}

/// `vec_ctx` plus a default element in front:
/// `[e : Ty 0, d : El e, n : Nat, x : El e, xs : Vec<e>(n)]` —
/// `e = Var 4, d = Var 3, n = Var 2, x = Var 1, xs = Var 0`.
fn vec_ctx_d() -> LocalCtx {
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let g = ext(&g, el(v(0)), c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, el(v(2)), c(0));
    ext(&g, vec_ty(v(3), v(1)), c(0))
}

// ---------------------------------------------------------------------------
// Tests — Vec
// ---------------------------------------------------------------------------

#[test]
fn the_type_and_the_constructors_check() {
    // Closed, at element code ⌜Nat⌝: literals at their exact indices.
    let g = nil_ctx();
    ck(&g, &vnil(), &vec_ty(Term::TmNat, Term::Zero), c(0));
    ck(&g, &nat_vec(&[1, 2, 3]), &vec_ty(Term::TmNat, nat(3)), c(0));

    // Open: element code, index, element and tail all variables. The result
    // index is `Succ`-headed, so `famVec e (S n)` unfolds and the pair
    // checks with no coercion (§5).
    let g = vec_ctx();
    ck(&g, &vcons(v(3), v(2), v(1), v(0)), &vec_ty(v(3), Term::Succ(rt(v(2)))), c(0));
}

#[test]
fn beta_fires_on_fully_open_data() {
    // §6.2, the property the route was chosen for: match on
    // `Cons(n, x, xs)` reduces to the arm with n, x, xs (and the element
    // code!) all variables. Arm returns the element: elim ≡ x.
    let g = vec_ctx_d();
    let (e, d, n, x, xs) = (v(4), v(3), v(2), v(1), v(0));
    let elim = vec_elim(
        5,
        &c(0),
        e.clone(),
        &el(v(6)), // M[h, z] = El e, constant (e under h, z)
        d,
        v(2), // (Γ, n', x', xs', ih) ⊢ x'
        Term::Succ(rt(n.clone())),
        vcons(e.clone(), n, x.clone(), xs),
    );
    conv(&g, &elim, &x, &el(e.clone()), c(0));

    // The same fact in *checking* position: refl proves elim = x.
    let id_ty = Type::Id { level: c(0), ty: rty(el(e.clone())), lhs: rt(elim), rhs: rt(x.clone()) };
    ck(&g, &Term::Refl { level: c(0), ty: rty(el(e)), tm: rt(x) }, &id_ty, c(0));
}

#[test]
fn the_arm_recovers_the_pattern_variable() {
    // §4.1: `Cons`'s index field is not stored, and the arm that binds it
    // receives the eliminator's own binder — for free, no inversion.
    let g = vec_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));
    let elim = |arm: Term| {
        vec_elim(
            4,
            &c(0),
            e.clone(),
            &Type::Nat,
            Term::Zero,
            arm,
            Term::Succ(rt(n.clone())),
            vcons(e.clone(), n.clone(), x.clone(), xs.clone()),
        )
    };
    // (Γ, n', x', xs', ih) ⊢ n' — the recovered index of an *open* Cons.
    conv(&g, &elim(v(3)), &n, &Type::Nat, c(0));
    // Negative: the recovered variable is the index, not its successor.
    not_conv(&g, &elim(v(3)), &Term::Succ(rt(n.clone())), &Type::Nat, c(0));

    // And `len` computes on closed data: arm = S ih.
    let len = vec_elim(
        0,
        &c(0),
        Term::TmNat,
        &Type::Nat,
        Term::Zero,
        Term::Succ(rt(v(0))),
        nat(3),
        nat_vec(&[5, 6, 7]),
    );
    conv(&nil_ctx(), &len, &nat(3), &Type::Nat, c(0));
}

#[test]
fn append_checks_at_open_indices_and_computes() {
    // §9 item 3. The type `Vec(plus n m)` with n, m open is the checking-
    // position exercise of definitional index arithmetic: the cons arm owes
    // `Vec(plus (S n) m)` and pays `Vec(S (plus n m))`.
    // Γ = [n : Nat, m : Nat, xs : Vec<Nat>(n), ys : Vec<Nat>(m)].
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, vec_ty(Term::TmNat, v(1)), c(0));
    let g = ext(&g, vec_ty(Term::TmNat, v(1)), c(0));
    let (n, m, xs, ys) = (v(3), v(2), v(1), v(0));

    let app = append(4, Term::TmNat, n.clone(), m.clone(), xs.clone(), ys.clone());
    ck(&g, &app, &vec_ty(Term::TmNat, plus(n.clone(), m.clone())), c(0));

    // β on an open Cons: append (Cons(n, 7, xs)) ys ≡
    // Cons(plus n m, 7, append xs ys), everything else neutral.
    let app_cons = append(
        4,
        Term::TmNat,
        Term::Succ(rt(n.clone())),
        m.clone(),
        vcons(Term::TmNat, n.clone(), nat(7), xs.clone()),
        ys.clone(),
    );
    let expected = vcons(Term::TmNat, plus(n.clone(), m.clone()), nat(7), app);
    conv(
        &g,
        &app_cons,
        &expected,
        &vec_ty(Term::TmNat, Term::Succ(rt(plus(n, m)))),
        c(0),
    );

    // Closed computation: [1, 2] ++ [3] ≡ [1, 2, 3].
    let closed = append(
        0,
        Term::TmNat,
        nat(2),
        nat(1),
        nat_vec(&[1, 2]),
        nat_vec(&[3]),
    );
    conv(&nil_ctx(), &closed, &nat_vec(&[1, 2, 3]), &vec_ty(Term::TmNat, nat(3)), c(0));
}

#[test]
fn map_id_by_induction() {
    // A real induction with the motive dependent on the index: for
    // map = elim at M[h, z] = Vec(h), prove Id(Vec(n); map id xs; xs) with
    // n and xs open. The step is one J (cong of Cons at a fixed head).
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, vec_ty(v(1), v(0)), c(0));
    let (e, n, xs) = (v(2), v(1), v(0));

    let id_lam = |e: Term| Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(el(e.clone())),
        body: rt(v(0)),
    };
    // map (λx. x) — at `depth`, of the vector `scrut` at index `idx`.
    let map = |depth: u32, e: Term, idx: Term, scrut: Term| {
        let arm_x = Term::App {
            fun: rt(id_lam(e.clone().shift_local(4))),
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(el(e.clone().shift_local(4))),
            cod: rty(el(e.clone().shift_local(5))),
            arg: rt(v(2)),
        };
        let cons_case = vcons(e.clone().shift_local(4), v(3), arm_x, v(0));
        vec_elim(
            depth,
            &c(0),
            e.clone(),
            &vec_ty(e.shift_local(2), v(1)),
            vnil(),
            cons_case,
            idx,
            scrut,
        )
    };

    // M_p[h, z] = Id(Vec(h); map z; z), scoped (Γ, h, z).
    let motive = Type::Id {
        level: c(0),
        ty: rty(vec_ty(e.clone().shift_local(2), v(1))),
        lhs: rt(map(5, e.clone().shift_local(2), v(1), v(0))),
        rhs: rt(v(0)),
    };
    // Base: map Nil ⇝ Nil, and the bound payload is Nil up to Unit η.
    let nil_case = Term::Refl {
        level: c(0),
        ty: rty(vec_ty(e.clone(), Term::Zero)),
        tm: rt(vnil()),
    };
    // Step, scoped (Γ, n', x, xs', ih): J on ih at the motive
    // (y, p) ⊢ Id(Vec(S n'); Cons(n', x, map xs'); Cons(n', x, y)).
    let mapx = map(7, e.clone().shift_local(4), v(3), v(1));
    let cons_case = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(vec_ty(e.clone().shift_local(4), v(3))),
        lhs: rt(mapx.clone()),
        motive: rty(Type::Id {
            level: c(0),
            ty: rty(vec_ty(e.clone().shift_local(6), Term::Succ(rt(v(5))))),
            lhs: rt(vcons(e.clone().shift_local(6), v(5), v(4), mapx.clone().shift_local(2))),
            rhs: rt(vcons(e.clone().shift_local(6), v(5), v(4), v(1))),
        }),
        case: rt(Term::Refl {
            level: c(0),
            ty: rty(vec_ty(e.clone().shift_local(4), Term::Succ(rt(v(3))))),
            tm: rt(vcons(e.clone().shift_local(4), v(3), v(2), mapx)),
        }),
        rhs: rt(v(1)),
        proof: rt(v(0)),
    };
    let proof = vec_elim(3, &c(0), e.clone(), &motive, nil_case, cons_case, n.clone(), xs.clone());
    let goal = mot_at(3, &motive, n, xs.clone(), 0);
    ck(&g, &proof, &goal, c(0));

    // Negative control: a bare refl does not prove the induction — the lhs
    // is neutral on an open scrutinee, not xs.
    let bare = Term::Refl {
        level: c(0),
        ty: rty(vec_ty(e, v(1))),
        tm: rt(xs),
    };
    ck_fails(&g, &bare, &goal, c(0));
}

#[test]
fn the_kernel_gate_rejects_the_near_misses() {
    let g = vec_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));

    // A Cons at index 0: fam unfolds to ⌜Unit⌝ and the pair is rejected.
    ck_fails(&g, &vcons(e.clone(), n.clone(), x.clone(), xs.clone()), &vec_ty(e.clone(), Term::Zero), c(0));
    // A Cons at a non-constructor-headed index: the family is stuck on the
    // neutral `n`, and a canonical pair does not inhabit a neutral type.
    ck_fails(&g, &vcons(e.clone(), n.clone(), x.clone(), xs.clone()), &vec_ty(e.clone(), n.clone()), c(0));
    // Nil at a successor index.
    ck_fails(&g, &vnil(), &vec_ty(e.clone(), Term::Succ(rt(n.clone()))), c(0));
    // The axis-4 control: a length-1 literal does not check at Vec(0), and
    // vice versa.
    ck_fails(&nil_ctx(), &nat_vec(&[1]), &vec_ty(Term::TmNat, Term::Zero), c(0));
    ck_fails(&nil_ctx(), &vnil(), &vec_ty(Term::TmNat, nat(1)), c(0));

    // A tail at the wrong index: Γ' adds m : Nat, and Cons(m, x, xs) with
    // xs : Vec(n) must fail at Vec(S m) — the annotation says Vec(m).
    let g2 = ext(&g, Type::Nat, c(0));
    let (e, n, x, xs, m) = (v(4), v(3), v(2), v(1), v(0));
    let _ = n;
    ck_fails(
        &g2,
        &vcons(e.clone(), m.clone(), x, xs),
        &vec_ty(e, Term::Succ(rt(m))),
        c(0),
    );
}

#[test]
fn cross_class_equations_fail_to_state() {
    // §7: Nil vs Cons no-confusion is vacuous — `Id` between them is not
    // even well-formed at either index, because the *type* separates them.
    let g = vec_ctx();
    let (e, n, x, xs) = (v(3), v(2), v(1), v(0));
    let cons = vcons(e.clone(), n.clone(), x, xs);
    ty_fails(
        &g,
        &Type::Id {
            level: c(0),
            ty: rty(vec_ty(e.clone(), Term::Zero)),
            lhs: rt(vnil()),
            rhs: rt(cons.clone()),
        },
        c(0),
    );
    ty_fails(
        &g,
        &Type::Id {
            level: c(0),
            ty: rty(vec_ty(e, Term::Succ(rt(n)))),
            lhs: rt(vnil()),
            rhs: rt(cons),
        },
        c(0),
    );
}

// ---------------------------------------------------------------------------
// Tests — Fin
// ---------------------------------------------------------------------------

#[test]
fn fin_zero_is_empty() {
    // The empty index class is ⌜Empty⌝, and it *is* Empty definitionally: a
    // hypothesis at Fin(0) checks at Empty with no elimination at all.
    let g = ext(&nil_ctx(), fin_ty(Term::Zero), c(0));
    ck(&g, &v(0), &Type::Empty { level: Level::Zero }, c(0));
    // And nothing canonical inhabits it.
    ck_fails(&nil_ctx(), &Term::Triv { level: Level::Zero }, &fin_ty(Term::Zero), c(0));
    ck_fails(&nil_ctx(), &fz(Term::Zero), &fin_ty(Term::Zero), c(0));
}

#[test]
fn fin_constructors_check_at_an_open_index() {
    // Γ = [n : Nat, i : Fin(n)].
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, fin_ty(v(0)), c(0));
    let (n, i) = (v(1), v(0));
    ck(&g, &fz(n.clone()), &fin_ty(Term::Succ(rt(n.clone()))), c(0));
    ck(&g, &fs(n.clone(), i.clone()), &fin_ty(Term::Succ(rt(n.clone()))), c(0));
    // Distinct constructors at the same open index are not convertible.
    not_conv(&g, &fz(n.clone()), &fs(n.clone(), i), &fin_ty(Term::Succ(rt(n))), c(0));
}

#[test]
fn fin_no_confusion_within_a_class() {
    // §7: FZ vs FS share the Succ class, so disjointness is tier 0's tag
    // predicate inside the branch — Case to a code, J at El of it.
    // Γ = [n : Nat, i : Fin(n), q : Id(Fin(S n); FZ(n); FS(n, i))].
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, fin_ty(v(0)), c(0));
    let g = ext(
        &g,
        Type::Id {
            level: c(0),
            ty: rty(fin_ty(Term::Succ(rt(v(1))))),
            lhs: rt(fz(v(1))),
            rhs: rt(fs(v(1), v(0))),
        },
        c(0),
    );
    let (n, i, q) = (v(2), v(1), v(0));
    let absurd = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(fin_ty(Term::Succ(rt(n.clone())))),
        lhs: rt(fz(n.clone())),
        // (y, p) ⊢ El (is_fz y): ⌜Unit⌝ at the fixed endpoint, ⌜Empty⌝ at FS.
        motive: rty(el(is_fz(n.clone().shift_local(2), v(1)))),
        case: rt(Term::Triv { level: Level::Zero }),
        rhs: rt(fs(n, i)),
        proof: rt(q),
    };
    ck(&g, &absurd, &Type::Empty { level: Level::Zero }, c(0));
}

// ---------------------------------------------------------------------------
// Tests — Tree (branching is free, §5.1)
// ---------------------------------------------------------------------------

#[test]
fn tree_declares_and_branching_beta_fires_on_open_children() {
    // Closed: a full tree of height 2 at its exact index.
    let g = nil_ctx();
    let t1 = node(Term::Zero, leaf(), leaf());
    let t2 = node(nat(1), t1.clone(), t1.clone());
    ck(&g, &t2, &tree_ty(nat(2)), c(0));

    // Open children: Node(n, l, r) is in constructor form with l, r
    // variables — the §5.1 claim, and the exact point where exact-height
    // fording failed (its §8.1: the payload needed the height comparison).
    // Γ = [n : Nat, l : Tree(n), r : Tree(n)].
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, tree_ty(v(0)), c(0));
    let g = ext(&g, tree_ty(v(1)), c(0));
    let (n, l, r) = (v(2), v(1), v(0));
    ck(&g, &node(n.clone(), l.clone(), r.clone()), &tree_ty(Term::Succ(rt(n.clone()))), c(0));

    // mirror (Node(n, l, r)) ≡ Node(n, mirror r, mirror l) — β through a
    // branching constructor on fully open children.
    let lhs = mirror(3, Term::Succ(rt(n.clone())), node(n.clone(), l.clone(), r.clone()));
    let rhs = node(
        n.clone(),
        mirror(3, n.clone(), r),
        mirror(3, n.clone(), l),
    );
    conv(&g, &lhs, &rhs, &tree_ty(Term::Succ(rt(n))), c(0));
}

#[test]
fn mirror_computes_and_mirror_mirror_is_identity() {
    // Closed computation: mirror swaps an asymmetric tree.
    let asym = node(nat(1), node(Term::Zero, leaf(), leaf()), leaf());
    // At index 2 the right child must also be at index 1 — build the
    // symmetric-height counterpart instead: Node(1, Node(0,·,·), Node(0,·,·))
    // is the honest height-2 tree; asym is *not* index-correct and must fail.
    ck_fails(&nil_ctx(), &asym, &tree_ty(nat(2)), c(0));
    let t1 = node(Term::Zero, leaf(), leaf());
    let t2 = node(nat(1), t1.clone(), t1.clone());
    let m = mirror(0, nat(2), t2.clone());
    conv(&nil_ctx(), &m, &t2, &tree_ty(nat(2)), c(0));

    // mirror (mirror t) = t by induction, t and its index open.
    // Γ = [n : Nat, t : Tree(n)].
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, tree_ty(v(0)), c(0));
    let (n, t) = (v(1), v(0));

    let mm = |depth: u32, idx: Term, tm: Term| {
        mirror(depth, idx.clone(), mirror(depth, idx, tm))
    };
    // M_p[h, z] = Id(Tree(h); mirror (mirror z); z).
    let motive = Type::Id {
        level: c(0),
        ty: rty(tree_ty(v(1))),
        lhs: rt(mm(4, v(1), v(0))),
        rhs: rt(v(0)),
    };
    let leaf_case = Term::Refl {
        level: c(0),
        ty: rty(tree_ty(Term::Zero)),
        tm: rt(leaf()),
    };
    // Step, scoped (Γ, n', l, r, ih_l, ih_r). The obligation's lhs reduces
    // (open-children β, twice) to Node(n', mm l, mm r); two J's rewrite the
    // children by ih_l then ih_r.
    let mml = mm(7, v(4), v(3));
    let mmr = mm(7, v(4), v(2));
    // J1 : Id(Tree(S n'); Node(mm l, mm r); Node(l, mm r)).
    let j1 = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_ty(v(4))),
        lhs: rt(mml.clone()),
        motive: rty(Type::Id {
            level: c(0),
            ty: rty(tree_ty(Term::Succ(rt(v(6))))),
            lhs: rt(node(v(6), mml.clone().shift_local(2), mmr.clone().shift_local(2))),
            rhs: rt(node(v(6), v(1), mmr.clone().shift_local(2))),
        }),
        case: rt(Term::Refl {
            level: c(0),
            ty: rty(tree_ty(Term::Succ(rt(v(4))))),
            tm: rt(node(v(4), mml.clone(), mmr.clone())),
        }),
        rhs: rt(v(3)),
        proof: rt(v(1)),
    };
    // J2 : Id(Tree(S n'); Node(mm l, mm r); Node(l, r)) — its case is J1.
    let j2 = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(tree_ty(v(4))),
        lhs: rt(mmr.clone()),
        motive: rty(Type::Id {
            level: c(0),
            ty: rty(tree_ty(Term::Succ(rt(v(6))))),
            lhs: rt(node(v(6), mml.shift_local(2), mmr.shift_local(2))),
            rhs: rt(node(v(6), v(5), v(1))),
        }),
        case: rt(j1),
        rhs: rt(v(2)),
        proof: rt(v(0)),
    };
    let proof = tree_elim(2, &c(0), &motive, leaf_case, j2, n.clone(), t.clone());
    let goal = mot_at(2, &motive, n, t, 0);
    ck(&g, &proof, &goal, c(0));
}
