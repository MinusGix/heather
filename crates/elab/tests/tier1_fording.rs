//! Tier-1 hand prototype: exact-height fording, on `List<Nat>` (§3–§6) and
//! on `Bits` (§7, two recursive constructors).
//!
//! The forcing function for `issues/inductive-compiler.md` tier 1 and item 2
//! of `issues/stress-proof-suite.md`: before a generator emits recursive
//! inductives, the encoding is built by hand at the kernel level and checked
//! by the real kernel, so the scheme in `docs/inductive-tier1-lowering.md`
//! is validated against the checker rather than against intuition. The
//! section numbers here are that document's.
//!
//! Nothing here uses the elaborator; the terms are what the generator will
//! emit. The tier-0 nominal tag (`docs/inductive-tier0-lowering.md` §3.3) is
//! elided — the prototype is about the height recursion, and the tag rides
//! along unchanged as field 0 of each constructor.

use std::rc::Rc;

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

/// A context of `n` entries, for building substitutions: `LocalSubst::id`
/// reads only the length and the base, so the entry types are irrelevant and
/// term construction only needs to know how deep it is.
fn scope(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: (0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: c(0) }).collect(),
    }
}

// ---------------------------------------------------------------------------
// §3 The type: `List Nat = Σ(n : Nat). El (vec n)`
// ---------------------------------------------------------------------------

/// `vec n : Ty 0` — the code of "exactly `n` elements", by `elim_Nat` on the
/// height. `vec 0 = ⌜Unit⌝`, `vec (S m) = ⌜Σ(_ : Nat). El (vec m)⌝`, with the
/// recursive occurrence being the `elim_Nat` recursion variable *as a code*
/// (no `El`/`⌜⌝` round trip).
fn vec_code(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        // (m : Nat, rec : Ty 0) ⊢ ⌜Σ(_ : Nat). El rec⌝; `rec` is Var 1 under
        // the Σ-code's own binder.
        step: rt(Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(Term::TmNat),
            snd: rt(v(1)),
        }),
        scrut: rt(n),
    }
}

fn vec(n: Term) -> Type {
    Type::El { level: c(0), tm: rt(vec_code(n)) }
}

/// `List Nat = Σ(n : Nat). El (vec n)`.
fn list() -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(vec(v(0))),
    }
}

/// The height field of a list: `fst l`.
fn height(l: Term) -> Term {
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(vec(v(0))),
        pair: rt(l),
    }
}

/// The payload field of a list: `snd l : El (vec (fst l))`.
fn payload(l: Term) -> Term {
    Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(vec(v(0))),
        pair: rt(l),
    }
}

// ---------------------------------------------------------------------------
// §4 Constructors
// ---------------------------------------------------------------------------

/// `nil = pair(0; ⟨⟩)` — the payload type `vec 0` reduces to `Unit`.
fn nil() -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(vec(v(0))),
        fst: rt(Term::Zero),
        snd: rt(Term::Triv { level: Level::Zero }),
    }
}

/// `cons a l = pair(S (fst l); pair(a; snd l))` — the height is *computed*,
/// which is what makes canonical forms unique (§2 of the scheme).
fn cons(a: Term, l: Term) -> Term {
    let h = height(l.clone());
    let inner = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        // The tail's payload type does not mention the element binder, so the
        // height is shifted under it.
        snd_ty: rty(vec(h.clone().shift_local(1))),
        fst: rt(a),
        snd: rt(payload(l)),
    };
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(vec(v(0))),
        fst: rt(Term::Succ(rt(h))),
        snd: rt(inner),
    }
}

fn list_of(elems: &[u64]) -> Term {
    let mut t = nil();
    for &e in elems.iter().rev() {
        t = cons(nat(e), t);
    }
    t
}

// ---------------------------------------------------------------------------
// §5 The eliminator: `elim_Nat` on the height, at the family of payloads
// ---------------------------------------------------------------------------

/// `M[l/z]`, for a motive `M` scoped in `(Γ, z : List Nat)` and a list term
/// `l` scoped in `Γ` extended by `extra` binders.
fn mot_at(depth: u32, motive: &Type, l: Term, extra: u32) -> Type {
    motive.apply_local(&LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(l)))
}

/// `pair(n; v)` — repackage a height and a payload as a list.
fn repack(n: Term, payload: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(vec(v(0))),
        fst: rt(n),
        snd: rt(payload),
    }
}

/// The `elim_Nat` motive `Π(v : vec n). M[pair(n; v)/z]`, scoped in `(Γ, n)`.
fn rec_motive(depth: u32, ml: &Level, motive: &Type) -> Type {
    Type::Pi {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec(v(0))),
        cod: rty(mot_at(depth, motive, repack(v(1), v(0)), 2)),
    }
}

/// `elim_List^{l''}(z. M; nil_case; a tail ih. cons_case; scrut)`.
///
/// - `motive` is scoped in `(Γ, z : List Nat)` and lives at `ml`;
/// - `nil_case : M[nil/z]` is scoped in `Γ`;
/// - `cons_case : M[cons a tail/z]` is scoped in
///   `(Γ, a : Nat, tail : List Nat, ih : M[tail/z])`.
fn list_rec(
    depth: u32,
    ml: &Level,
    motive: &Type,
    nil_case: Term,
    cons_case: Term,
    scrut: Term,
) -> Term {
    // base : Π(v : vec 0). M[pair(0; v)/z] — `vec 0 ⇝ Unit`, so the bound
    // payload is irrelevant and the body is the nil case weakened.
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec(Term::Zero)),
        body: rt(nil_case.shift_local(1)),
    };

    // step, scoped in (Γ, m : Nat, rec : Π(v : vec m). M[pair(m; v)/z]):
    //   λ(payload : vec (S m)). cons_case[fst payload, pair(m; snd payload),
    //                                     rec (snd payload)]
    // In (Γ, m, rec, payload): m = Var 2, rec = Var 1, payload = Var 0, and
    // `vec (S m)` whnf-reduces to `Σ(_ : Nat). vec m`.
    let tail_vec = || rty(vec(v(3)));
    let elem = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: tail_vec(),
        pair: rt(v(0)),
    };
    let tail_payload = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: tail_vec(),
        pair: rt(v(0)),
    };
    let tail = repack(v(2), tail_payload.clone());
    let ih = Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec(v(2))),
        cod: rty(mot_at(depth, motive, repack(v(3), v(0)), 4)),
        arg: rt(tail_payload),
    };
    let step_body = cons_case.apply_local(
        &LocalSubst::id(&scope(depth))
            .shift_local(3)
            .extended(rt(elem))
            .extended(rt(tail))
            .extended(rt(ih)),
    );
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec(Term::Succ(rt(v(1))))),
        body: rt(step_body),
    };

    // The whole recursion applied to the scrutinee's payload.
    let recursion = Term::ElimNat {
        level: ml.clone(),
        motive: rty(rec_motive(depth, ml, motive)),
        base: rt(base),
        step: rt(step),
        scrut: rt(height(scrut.clone())),
    };
    Term::App {
        fun: rt(recursion),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(vec(height(scrut.clone()))),
        cod: rty(mot_at(depth, motive, repack(height(scrut.clone()).shift_local(1), v(0)), 1)),
        arg: rt(payload(scrut)),
    }
}

/// `append xs ys` — recursion on `xs` with a constant motive.
fn append(depth: u32, xs: Term, ys: Term) -> Term {
    list_rec(
        depth,
        &c(0),
        &list(),
        ys.clone(),
        // (Γ, a, tail, ih) ⊢ cons a ih
        cons(v(2), v(0)),
        xs,
    )
}

// ---------------------------------------------------------------------------
// §6 Identity helpers (`cong` for `cons`, the Nat zero/succ predicate)
// ---------------------------------------------------------------------------

fn id_list(lhs: Term, rhs: Term) -> Type {
    Type::Id { level: c(0), ty: rty(list()), lhs: rt(lhs), rhs: rt(rhs) }
}

fn refl_at(ty: Type, t: Term) -> Term {
    Term::Refl { level: c(0), ty: rty(ty), tm: rt(t) }
}

/// `cong (cons a ·) p` — from `p : Id(List; l; l')` derive
/// `Id(List; cons a l; cons a l')`, by `J` at the fixed endpoint `l`.
fn cong_cons(a: Term, l: Term, l_prime: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(list()),
        lhs: rt(l.clone()),
        // (Γ, y, p) ⊢ Id(List; cons a l; cons a y)
        motive: rty(id_list(
            cons(a.clone().shift_local(2), l.clone().shift_local(2)),
            cons(a.clone().shift_local(2), v(1)),
        )),
        case: rt(refl_at(list(), cons(a, l))),
        rhs: rt(l_prime),
        proof: rt(p),
    }
}

/// `zero_pred n : Ty 0` — `⌜Unit⌝` at `0`, `⌜Empty⌝` at a successor. The
/// large elimination that makes `0 ≠ S n` provable; tier 1 reaches for it on
/// the *height*, not on the payload.
fn zero_pred(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        step: rt(Term::TmEmpty { level: Level::Zero }),
        scrut: rt(n),
    }
}

fn el(t: Term) -> Type {
    Type::El { level: c(0), tm: rt(t) }
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

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn the_type_and_the_constructors_check() {
    let g = nil_ctx();
    ck(&g, &nil(), &list(), c(0));
    ck(&g, &cons(nat(3), nil()), &list(), c(0));
    ck(&g, &list_of(&[1, 2, 3]), &list(), c(0));
}

#[test]
fn cons_on_an_open_tail_checks() {
    // Γ = (l : List Nat) ⊢ cons 0 l : List Nat — the height `S (fst l)` is
    // symbolic, and `vec (S (fst l))` still whnf-reduces to a Σ.
    let g = ext(&nil_ctx(), list(), c(0));
    ck(&g, &cons(Term::Zero, v(0)), &list(), c(0));
}

#[test]
fn heights_are_exact_and_computed() {
    let g = nil_ctx();
    conv(&g, &height(list_of(&[1, 2, 3])), &nat(3), &Type::Nat, c(0));
    conv(&g, &height(nil()), &nat(0), &Type::Nat, c(0));
}

#[test]
fn append_checks_and_computes() {
    let g = nil_ctx();
    let t = append(0, list_of(&[1, 2]), list_of(&[3]));
    ck(&g, &t, &list(), c(0));
    conv(&g, &t, &list_of(&[1, 2, 3]), &list(), c(0));
    // The nil and cons β rules, separately.
    conv(&g, &append(0, nil(), list_of(&[3])), &list_of(&[3]), &list(), c(0));
    conv(&g, &append(0, list_of(&[1]), nil()), &list_of(&[1]), &list(), c(0));
}

#[test]
fn append_on_an_open_argument_is_neutral_but_typed() {
    // Γ = (xs : List Nat, ys : List Nat) ⊢ append xs ys : List Nat, stuck.
    let g = ext(&ext(&nil_ctx(), list(), c(0)), list(), c(0));
    ck(&g, &append(2, v(1), v(0)), &list(), c(0));
    // `append nil ys ≡ ys` still fires with an open `ys`.
    conv(&g, &append(2, nil(), v(0)), &v(0), &list(), c(0));
}

#[test]
fn append_nil_by_induction() {
    // Γ = (xs : List Nat) ⊢ append xs nil = xs, by the derived recursor at an
    // Id motive: the base case is `refl` up to β, the step case is `cong`.
    let g = ext(&nil_ctx(), list(), c(0));
    let motive = id_list(append(2, v(0), nil()), v(0));
    let proof = list_rec(
        1,
        &c(0),
        &motive,
        refl_at(list(), nil()),
        // (xs, a, tail, ih) ⊢ cong (cons a ·) ih
        cong_cons(v(2), append(4, v(1), nil()), v(1), v(0)),
        v(0),
    );
    ck(&g, &proof, &id_list(append(1, v(0), nil()), v(0)), c(0));
}

#[test]
fn append_assoc_by_induction() {
    // Γ = (xs, ys, zs) ⊢ (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
    let g = ext(&ext(&ext(&nil_ctx(), list(), c(0)), list(), c(0)), list(), c(0));
    // In (xs, ys, zs, z): ys = 2, zs = 1, z = 0.
    let motive = id_list(
        append(4, append(4, v(0), v(2)), v(1)),
        append(4, v(0), append(4, v(2), v(1))),
    );
    // In (xs, ys, zs): ys = 1, zs = 0.
    let base = refl_at(list(), append(3, v(1), v(0)));
    // In (xs, ys, zs, a, tail, ih): ys = 4, zs = 3, a = 2, tail = 1, ih = 0.
    let step = cong_cons(
        v(2),
        append(6, append(6, v(1), v(4)), v(3)),
        append(6, v(1), append(6, v(4), v(3))),
        v(0),
    );
    let proof = list_rec(3, &c(0), &motive, base, step, v(2));
    let goal = id_list(
        append(3, append(3, v(2), v(1)), v(0)),
        append(3, v(2), append(3, v(1), v(0))),
    );
    ck(&g, &proof, &goal, c(0));
}

#[test]
fn no_confusion_nil_versus_cons() {
    // Γ = (a : Nat, l : List Nat, e : Id(List; nil; cons a l)) ⊢ Empty.
    // The heights differ in *shape* (0 vs S _), so one `J` at the zero
    // predicate composed with the height projection does it — no case
    // analysis on the payload at all.
    let g = ext(
        &ext(&ext(&nil_ctx(), Type::Nat, c(0)), list(), c(0)),
        id_list(nil(), cons(v(1), v(0))),
        c(0),
    );
    let absurd = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(list()),
        lhs: rt(nil()),
        // (Γ, y, p) ⊢ El (zero_pred (fst y))
        motive: rty(el(zero_pred(height(v(1))))),
        case: rt(Term::Triv { level: Level::Zero }),
        rhs: rt(cons(v(2), v(1))),
        proof: rt(v(0)),
    };
    ck(&g, &absurd, &Type::Empty { level: Level::Zero }, c(0));
    // ...and `Empty` eliminates into any goal, e.g. a false equation.
    let anything = Term::ElimEmpty {
        level: c(0),
            scrut_level: Level::Zero,
        motive: rty(id_list(nil(), list_of(&[7])).shift_local(1)),
        scrut: rt(absurd),
    };
    ck(&g, &anything, &id_list(nil(), list_of(&[7])), c(0));
}

#[test]
fn no_confusion_cons_is_injective() {
    // Γ = (a, l, a', l', e : Id(List; cons a l; cons a' l')) ⊢ a = a' and
    // l = l'. Both projections are total functions built by the recursor with
    // the left-hand side's own field as the default in the nil branch (the
    // constant-motive trick of the tier-0 scheme, §6.2).
    let eq = id_list(cons(v(3), v(2)), cons(v(1), v(0)));
    let g = ext(&ext(&nil_ctx(), Type::Nat, c(0)), list(), c(0));
    let g = ext(&ext(&g, Type::Nat, c(0)), list(), c(0));
    let g = ext(&g, eq, c(0));
    // In Γ (depth 5): a = 4, l = 3, a' = 2, l' = 1, e = 0.
    let lhs = cons(v(4), v(3));
    let rhs = cons(v(2), v(1));

    // head x = elim_List(_. Nat; a; b _ _. b; x) — `head (cons b m) ⇝ b`.
    let head = |x: Term, depth: u32, a_default: Term| {
        list_rec(depth, &c(0), &Type::Nat, a_default, v(2), x)
    };
    let head_eq = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(list()),
        lhs: rt(lhs.clone()),
        // (Γ, y, p) ⊢ Id(Nat; a; head y)
        motive: rty(Type::Id {
            level: c(0),
            ty: rty(Type::Nat),
            lhs: rt(v(6)),
            rhs: rt(head(v(1), 7, v(6))),
        }),
        case: rt(refl_at(Type::Nat, v(4))),
        rhs: rt(rhs.clone()),
        proof: rt(v(0)),
    };
    let head_goal =
        Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(4)), rhs: rt(v(2)) };
    ck(&g, &head_eq, &head_goal, c(0));

    // tail x = elim_List(_. List; l; _ m _. m; x) — `tail (cons b m) ⇝ m`.
    let tail = |x: Term, depth: u32, l_default: Term| {
        list_rec(depth, &c(0), &list(), l_default, v(1), x)
    };
    let tail_eq = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(list()),
        lhs: rt(lhs),
        // (Γ, y, p) ⊢ Id(List; l; tail y)
        motive: rty(id_list(v(5), tail(v(1), 7, v(5)))),
        case: rt(refl_at(list(), v(3))),
        rhs: rt(rhs),
        proof: rt(v(0)),
    };
    ck(&g, &tail_eq, &id_list(v(3), v(1)), c(0));
}

#[test]
fn cons_beta_fires_on_an_open_element_and_tail() {
    // Γ = (a : Nat, l : List Nat, ys : List Nat) ⊢
    //   append (cons a l) ys ≡ cons a (append l ys)
    // — the step case computes with *nothing* concrete but the constructor,
    // because the height `S (fst l)` is Succ-headed whatever `l` is.
    let g = ext(&ext(&ext(&nil_ctx(), Type::Nat, c(0)), list(), c(0)), list(), c(0));
    let lhs = append(3, cons(v(2), v(1)), v(0));
    let rhs = cons(v(2), append(3, v(1), v(0)));
    ck(&g, &lhs, &list(), c(0));
    conv(&g, &lhs, &rhs, &list(), c(0));
}

#[test]
fn the_kernel_gate_rejects_the_near_misses() {
    // 1. `append xs nil = xs` is not `refl` — with `xs` open the left side is
    //    neutral, so the induction is doing real work.
    let g1 = ext(&nil_ctx(), list(), c(0));
    let goal1 = id_list(append(1, v(0), nil()), v(0));
    ck_fails(&g1, &refl_at(list(), v(0)), &goal1, c(0));

    // 2. A step case that conses the wrong element does not check.
    let motive = id_list(append(2, v(0), nil()), v(0));
    let bad = list_rec(
        1,
        &c(0),
        &motive,
        refl_at(list(), nil()),
        cong_cons(Term::Zero, append(4, v(1), nil()), v(1), v(0)),
        v(0),
    );
    ck_fails(&g1, &bad, &goal1, c(0));

    // 3. The height-shape disjointness argument must *not* fire between two
    //    uses of the same constructor: both heights are `S _`, so the zero
    //    predicate decodes to `Empty` on the left and the `⟨⟩` fails.
    let g3 = ext(
        &ext(&ext(&ext(&nil_ctx(), Type::Nat, c(0)), list(), c(0)), Type::Nat, c(0)),
        list(),
        c(0),
    );
    let g3 = ext(&g3, id_list(cons(v(3), v(2)), cons(v(1), v(0))), c(0));
    let not_absurd = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(list()),
        lhs: rt(cons(v(4), v(3))),
        motive: rty(el(zero_pred(height(v(1))))),
        case: rt(Term::Triv { level: Level::Zero }),
        rhs: rt(cons(v(2), v(1))),
        proof: rt(v(0)),
    };
    ck_fails(&g3, &not_absurd, &Type::Empty { level: Level::Zero }, c(0));
}

#[test]
fn canonical_forms_are_unique() {
    // Equal lists are convertible; different lists are not — no padding
    // degrees of freedom (the dragon a depth-*bound* encoding would have).
    let g = nil_ctx();
    conv(&g, &list_of(&[1, 2]), &list_of(&[1, 2]), &list(), c(0));
    not_conv(&g, &list_of(&[1, 2]), &list_of(&[2, 1]), &list(), c(0));
    not_conv(&g, &list_of(&[1]), &list_of(&[1, 1]), &list(), c(0));
    not_conv(&g, &nil(), &list_of(&[0]), &list(), c(0));
}

// ---------------------------------------------------------------------------
// §7 Two recursive constructors: `inductive Bits { Nil, B0(Bits), B1(Bits) }`
//
// `List` degenerates in one respect: each height class holds exactly one
// constructor, so its payload spine has no sum at all. `Bits` is the smallest
// declaration that exercises the rest of the scheme — a sum spine at the
// successor heights, `match` as `elim_Nat` then `Case`, and same-height
// disjointness, which needs the tag predicate to be a *function of the
// height* rather than a plain nested `Case`.
// ---------------------------------------------------------------------------

/// `spine n : Ty 0` — `⌜Unit⌝` (the `Nil` branch) at `0`, `⌜rec + rec⌝` (the
/// `B0`/`B1` branches) at a successor. Non-recursive constructors live only
/// at height 0 and recursive ones only above it, so neither class needs an
/// `Empty` padding branch in the other's spine.
fn spine_code(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        step: rt(Term::TmSum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rt(v(0)),
            rhs: rt(v(0)),
        }),
        scrut: rt(n),
    }
}

fn bspine(n: Term) -> Type {
    Type::El { level: c(0), tm: rt(spine_code(n)) }
}

fn bits() -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(bspine(v(0))),
    }
}

fn bheight(x: Term) -> Term {
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(bspine(v(0))),
        pair: rt(x),
    }
}

fn bpayload(x: Term) -> Term {
    Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(bspine(v(0))),
        pair: rt(x),
    }
}

fn brepack(n: Term, payload: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(bspine(v(0))),
        fst: rt(n),
        snd: rt(payload),
    }
}

fn bnil() -> Term {
    brepack(Term::Zero, Term::Triv { level: Level::Zero })
}

/// `B0 x` / `B1 x` — the injection into the successor spine's sum, then the
/// computed height. `right = false` is `B0`.
fn bcons(right: bool, x: Term) -> Term {
    let h = bheight(x.clone());
    let branch = rty(bspine(h.clone()));
    let inj = if right {
        Term::Inr {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: Rc::clone(&branch),
            rhs: branch,
            val: rt(bpayload(x)),
        }
    } else {
        Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: Rc::clone(&branch),
            rhs: branch,
            val: rt(bpayload(x)),
        }
    };
    brepack(Term::Succ(rt(h)), inj)
}

/// `elim_Bits^{l''}(z. M; nil_case; tail ih. b0_case; tail ih. b1_case; x)`:
/// `elim_Nat` on the height, then `Case` on the payload. The two step arms
/// are scoped in `(Γ, tail : Bits, ih : M[tail/z])`.
fn bits_rec(
    depth: u32,
    ml: &Level,
    motive: &Type,
    nil_case: Term,
    b0_case: Term,
    b1_case: Term,
    scrut: Term,
) -> Term {
    let bmot_at = |l: Term, extra: u32| {
        motive.apply_local(&LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(l)))
    };
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(bspine(Term::Zero)),
        body: rt(nil_case.shift_local(1)),
    };

    // (Γ, m, rec, v, x): m = 3, rec = 2, v = 1, x = 0.
    let arm = |case: &Term| {
        let ih = Term::App {
            fun: rt(v(2)),
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(bspine(v(3))),
            cod: rty(bmot_at(brepack(v(4), v(0)), 5)),
            arg: rt(v(0)),
        };
        case.apply_local(
            &LocalSubst::id(&scope(depth))
                .shift_local(4)
                .extended(rt(brepack(v(3), v(0))))
                .extended(rt(ih)),
        )
    };
    // (Γ, m, rec, v): m = 2, rec = 1, v = 0.
    let step_body = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: ml.clone(),
        lhs: rty(bspine(v(2))),
        rhs: rty(bspine(v(2))),
        // (Γ, m, rec, v, z) ⊢ M[pair(S m; z)/z']
        motive: rty(bmot_at(brepack(Term::Succ(rt(v(3))), v(0)), 4)),
        case_l: rt(arm(&b0_case)),
        case_r: rt(arm(&b1_case)),
        scrut: rt(v(0)),
    };
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(bspine(Term::Succ(rt(v(1))))),
        body: rt(step_body),
    };

    let recursion = Term::ElimNat {
        level: ml.clone(),
        motive: rty(Type::Pi {
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(bspine(v(0))),
            cod: rty(bmot_at(brepack(v(1), v(0)), 2)),
        }),
        base: rt(base),
        step: rt(step),
        scrut: rt(bheight(scrut.clone())),
    };
    Term::App {
        fun: rt(recursion),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(bspine(bheight(scrut.clone()))),
        cod: rty(bmot_at(brepack(bheight(scrut.clone()).shift_local(1), v(0)), 1)),
        arg: rt(bpayload(scrut)),
    }
}

/// `flip` — swap `B0` and `B1`, by recursion with a constant motive.
fn flip(depth: u32, x: Term) -> Term {
    bits_rec(
        depth,
        &c(0),
        &bits(),
        bnil(),
        // (Γ, tail, ih) ⊢ B1 ih / B0 ih
        bcons(true, v(0)),
        bcons(false, v(0)),
        x,
    )
}

fn id_bits(lhs: Term, rhs: Term) -> Type {
    Type::Id { level: c(0), ty: rty(bits()), lhs: rt(lhs), rhs: rt(rhs) }
}

/// `cong (B_i ·) p`.
fn cong_bcons(right: bool, x: Term, x_prime: Term, p: Term) -> Term {
    Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(bits()),
        lhs: rt(x.clone()),
        motive: rty(id_bits(
            bcons(right, x.clone().shift_local(2)),
            bcons(right, v(1)),
        )),
        case: rt(Term::Refl { level: c(0), ty: rty(bits()), tm: rt(bcons(right, x)) }),
        rhs: rt(x_prime),
        proof: rt(p),
    }
}

/// `is_B0 x : Ty 0` — the tag predicate. Unlike tier 0's nested `Case`, it is
/// a *function of the height*: `Empty` at height 0 (that is `Nil`), and at a
/// successor a `Case` on the payload. Large elimination through a Π over the
/// payload, so the `elim_Nat` motive is `Π(v : El (spine n)). Ty 0 @ 1`.
fn is_b0(x: Term) -> Term {
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(bspine(Term::Zero)),
        body: rt(Term::TmEmpty { level: Level::Zero }),
    };
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(bspine(Term::Succ(rt(v(1))))),
        body: rt(Term::Case {
            lhs_level: c(0),
            rhs_level: c(0),
            motive_level: c(1),
            lhs: rty(bspine(v(2))),
            rhs: rty(bspine(v(2))),
            motive: rty(Type::Ty(c(0))),
            case_l: rt(Term::TmUnit { level: Level::Zero }),
            case_r: rt(Term::TmEmpty { level: Level::Zero }),
            scrut: rt(v(0)),
        }),
    };
    let recursion = Term::ElimNat {
        level: c(1),
        motive: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(1),
            dom: rty(bspine(v(0))),
            cod: rty(Type::Ty(c(0))),
        }),
        base: rt(base),
        step: rt(step),
        scrut: rt(bheight(x.clone())),
    };
    Term::App {
        fun: rt(recursion),
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(bspine(bheight(x.clone()))),
        cod: rty(Type::Ty(c(0))),
        arg: rt(bpayload(x)),
    }
}

#[test]
fn bits_type_constructors_and_computation() {
    let g = nil_ctx();
    let b010 = bcons(false, bcons(true, bcons(false, bnil())));
    ck(&g, &bnil(), &bits(), c(0));
    ck(&g, &b010, &bits(), c(0));
    conv(&g, &bheight(b010.clone()), &nat(3), &Type::Nat, c(0));
    // Distinct bit strings of the same length are inconvertible: the sum
    // spine's tags are what tells them apart.
    not_conv(&g, &b010, &bcons(false, bcons(false, bcons(false, bnil()))), &bits(), c(0));

    // `flip` computes, and on an open argument it is neutral but typed.
    let flipped = bcons(true, bcons(false, bcons(true, bnil())));
    ck(&g, &flip(0, b010.clone()), &bits(), c(0));
    conv(&g, &flip(0, b010), &flipped, &bits(), c(0));
    let g1 = ext(&nil_ctx(), bits(), c(0));
    ck(&g1, &flip(1, v(0)), &bits(), c(0));
    // β on a constructor with an open argument: flip (B0 x) ≡ B1 (flip x).
    conv(&g1, &flip(1, bcons(false, v(0))), &bcons(true, flip(1, v(0))), &bits(), c(0));
}

#[test]
fn flip_flip_is_identity_by_induction() {
    let g = ext(&nil_ctx(), bits(), c(0));
    let motive = id_bits(flip(2, flip(2, v(0))), v(0));
    let proof = bits_rec(
        1,
        &c(0),
        &motive,
        Term::Refl { level: c(0), ty: rty(bits()), tm: rt(bnil()) },
        // (x, tail, ih): flip (flip (B0 tail)) ≡ B0 (flip (flip tail))
        cong_bcons(false, flip(3, flip(3, v(1))), v(1), v(0)),
        cong_bcons(true, flip(3, flip(3, v(1))), v(1), v(0)),
        v(0),
    );
    ck(&g, &proof, &id_bits(flip(1, flip(1, v(0))), v(0)), c(0));
}

#[test]
fn bits_no_confusion_at_the_same_height() {
    // Γ = (x, y : Bits, e : Id(Bits; B0 x; B1 y)) ⊢ Empty. The heights agree
    // here (`S (fst x)` vs `S (fst y)`), so the height-shape argument that
    // separated `nil` from `cons` cannot fire; the tag predicate does it.
    let g = ext(&ext(&nil_ctx(), bits(), c(0)), bits(), c(0));
    let g = ext(&g, id_bits(bcons(false, v(1)), bcons(true, v(0))), c(0));
    let absurd = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(bits()),
        lhs: rt(bcons(false, v(2))),
        motive: rty(Type::El { level: c(0), tm: rt(is_b0(v(1))) }),
        case: rt(Term::Triv { level: Level::Zero }),
        rhs: rt(bcons(true, v(1))),
        proof: rt(v(0)),
    };
    ck(&g, &absurd, &Type::Empty { level: Level::Zero }, c(0));

    // The same term shape must NOT check when both sides are `B0` — there the
    // predicate decodes to `Unit` on both endpoints and proves nothing.
    let g2 = ext(&ext(&nil_ctx(), bits(), c(0)), bits(), c(0));
    let g2 = ext(&g2, id_bits(bcons(false, v(1)), bcons(false, v(0))), c(0));
    let not_absurd = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(bits()),
        lhs: rt(bcons(false, v(2))),
        motive: rty(Type::El { level: c(0), tm: rt(is_b0(v(1))) }),
        case: rt(Term::Triv { level: Level::Zero }),
        rhs: rt(bcons(false, v(1))),
        proof: rt(v(0)),
    };
    ck_fails(&g2, &not_absurd, &Type::Empty { level: Level::Zero }, c(0));
}
