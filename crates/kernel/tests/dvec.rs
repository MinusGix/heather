//! `DVec` and `dnth`: step 2 of the `IWf` landing
//! (`docs/kernel/iwf-former-design.md` §1.1, §3, §13; `issues/iwf-former.md`).
//!
//! `DVec^l(k; i. F)` is `Vec` with a per-position element type. Like `Vec` it
//! has no introduction or elimination forms of its own: its content is the
//! length-driven reduction into `Unit`/`Σ`, and its projection `dnth` is a
//! fixed `elim_Nat` schema (`term::dnth`), not a former. The rule shapes are
//! the Coq formalization's (heather-coq `M17_DESIGN.md`, M17a:
//! `Validity/DVec.v`, `Typing/DNth.v`, `Validity/DVecNth.v`,
//! `Validity/DVecNthReds.v`), which this file follows case by case.
//!
//! Coverage: the reductions at literal and computed lengths, with the
//! family instantiated at `inl ⟨⟩`/`inr j`; neutrality at a neutral length
//! and the structural congruence there (the family under `i : Fin k`);
//! `Vec`/`DVec` agreeing at a canonical length and not at a neutral one
//! (design §1.1); formation, its level and its layer gate; a heterogeneous
//! tuple inhabiting its type; `dnth`'s typing at an open length (the β steps
//! the Coq formalization's `V_dnth` had to check) and at literal ones; and
//! the neutral-tuple property `dnth(3; F; cs; inr (inl ⟨⟩)) ≡ fst (snd cs)`.

use heather_kernel::rc::Rc;

use heather_kernel::conv::{conv_term, conv_type, oracle};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{is_whnf_type, whnf_term, whnf_type};
use heather_kernel::term::{
    dnth, fin_first, fin_next, CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type,
};
use heather_kernel::typing::{self, check_term, check_type, TypeError};

const FUEL: u64 = 100_000;

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

fn unit0() -> Type {
    Type::Unit { level: Level::Zero }
}

fn fin(len: Term) -> Type {
    Type::Fin { len: rt(len) }
}

fn dvec(l: Level, len: Term, fam: Type) -> Type {
    Type::DVec { level: l, len: rt(len), fam: rty(fam) }
}

fn vec(elem: Type, len: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(elem), len: rt(len) }
}

fn sigma(fst: Type, snd: Type) -> Type {
    Type::Sigma { fst_level: c(0), snd_level: c(0), fst: rty(fst), snd: rty(snd) }
}

fn pair(fst_ty: Type, snd_ty: Type, fst: Term, snd: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        fst: rt(fst),
        snd: rt(snd),
    }
}

/// `inl ⟨⟩ : Fin(S k)` and `inr j : Fin(S k)`.
fn first(k: Term) -> Term {
    fin_first(rt(k))
}

fn next(k: Term, j: Term) -> Term {
    fin_next(rt(k), rt(j))
}

/// Position `p` of `Fin(n)`, `p < n`: `inr^p (inl ⟨⟩)`.
fn pos(n: u64, p: u64) -> Term {
    assert!(p < n);
    let mut t = first(nat(n - p - 1));
    for q in (0..p).rev() {
        t = next(nat(n - q - 1), t);
    }
    t
}

/// `Id^0(Fin(k); i; i)` with `i` the innermost variable — a family that
/// mentions its position, so an instantiation at the wrong index shows.
fn id_at_i(k: Term) -> Type {
    Type::Id { level: c(0), ty: rty(fin(k)), lhs: rt(v(0)), rhs: rt(v(0)) }
}

/// The heterogeneous family over `i : Fin(S (S k))`, as a code under `El`:
/// position 0 is `Nat`, position 1 is `Nat → Nat`, the rest `Unit`.
/// `k` is scoped in the ambient Γ (the family is under `i`).
fn hetero_fam(k: Term) -> Type {
    let ty0 = Rc::new(Type::Ty(c(0)));
    let k = rt(k);
    // Under `i`, then under the outer case's `inr` binder `j : Fin(S k)`.
    let inner = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(1),
        lhs: rty(unit0()),
        rhs: rty(Type::Fin { len: Rc::new(k.shift_local(2)) }),
        motive: Rc::clone(&ty0),
        case_l: rt(Term::TmPi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rt(Term::TmNat),
            cod: rt(Term::TmNat),
        }),
        case_r: rt(Term::TmUnit { level: c(0) }),
        scrut: rt(v(0)),
    };
    let outer = Term::Case {
        lhs_level: c(0),
        rhs_level: c(0),
        motive_level: c(1),
        lhs: rty(unit0()),
        rhs: rty(Type::Fin { len: Rc::new(Term::Succ(Rc::new(k.shift_local(1)))) }),
        motive: ty0,
        case_l: rt(Term::TmNat),
        case_r: rt(inner),
        scrut: rt(v(0)),
    };
    Type::El { level: c(0), tm: rt(outer) }
}

fn whnf(t: &Type, gamma: &LocalCtx) -> Type {
    whnf_type(t, gamma, FUEL).expect("enough fuel")
}

fn ck_ty_at(layer: Layer, gamma: &LocalCtx, t: &Type, level: &Level) -> Result<(), TypeError> {
    check_type(&GlobalCtx::default(), 0, layer, gamma, t, level, FUEL)
}

fn ck_ty(gamma: &LocalCtx, t: &Type, level: Level) {
    ck_ty_at(Layer::Prog, gamma, t, &level).unwrap_or_else(|e| panic!("type does not check: {e:?}"));
}

/// Checked twice: by the gate and by `typing::oracle`, the checker with
/// every selection spelled (its whole gate, not a hand-picked half).
fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    ck_ty(gamma, ty, level.clone());
    let psi = GlobalCtx::default();
    check_term(&psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
    typing::oracle::check_term(&psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check (oracle): {e:?}"));
}

fn not_ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    let psi = GlobalCtx::default();
    check_term(&psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL).expect_err("expected ill-typed");
    typing::oracle::check_term(&psi, 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("expected ill-typed (oracle)");
}

// Every verdict is asked of both conversion checkers: the value machine
// (`conv::conv_*`) and the rewriter (`conv::oracle`, ch. 06 over `reduce.rs`),
// so `DVec`'s two reductions (`Eval::dvec_ty`, `reduce::step_type`) and its
// two congruence instantiations are held to the same answers.

fn conv_ty_both(gamma: &LocalCtx, a: &Type, b: &Type, level: &Level) -> [bool; 2] {
    let psi = GlobalCtx::default();
    [
        conv_type(&psi, gamma, Layer::Prog, a, b, level, FUEL).is_ok(),
        oracle::conv_type(&psi, gamma, Layer::Prog, a, b, level, FUEL).is_ok(),
    ]
}

fn conv_tm_both(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: &Level) -> [bool; 2] {
    let psi = GlobalCtx::default();
    [
        conv_term(&psi, gamma, Layer::Prog, a, b, ty, level, FUEL).is_ok(),
        oracle::conv_term(&psi, gamma, Layer::Prog, a, b, ty, level, FUEL).is_ok(),
    ]
}

fn conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    assert_eq!(conv_ty_both(gamma, a, b, &level), [true, true], "types not convertible (values, rewriter)");
}

fn not_conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    assert_eq!(conv_ty_both(gamma, a, b, &level), [false, false], "types convertible (values, rewriter)");
}

fn conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    assert_eq!(conv_tm_both(gamma, a, b, ty, &level), [true, true], "terms not convertible (values, rewriter)");
}

fn not_conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    assert_eq!(conv_tm_both(gamma, a, b, ty, &level), [false, false], "terms convertible (values, rewriter)");
}

fn fst_of(fst_ty: Type, snd_ty: Type, p: Term) -> Term {
    Term::Fst { fst_level: c(0), snd_level: c(0), fst_ty: rty(fst_ty), snd_ty: rty(snd_ty), pair: rt(p) }
}

fn snd_of(fst_ty: Type, snd_ty: Type, p: Term) -> Term {
    Term::Snd { fst_level: c(0), snd_level: c(0), fst_ty: rty(fst_ty), snd_ty: rty(snd_ty), pair: rt(p) }
}

// -------------------------------------------------------------------------
// Reduction
// -------------------------------------------------------------------------

#[test]
fn dvec_reduces_on_a_literal_length() {
    let g = nil_ctx();
    // DVec^l(0; i. F) ⇝ Unit^l — the nullary reduct carries the level.
    assert_eq!(whnf(&dvec(c(2), nat(0), Type::Nat), &g), Type::Unit { level: c(2) });
    // DVec(2; i. Id(Fin 2; i; i)) ⇝ Σ(_ : Id(Fin 2; inl ⟨⟩; inl ⟨⟩)). DVec(1; j. F[inr j]):
    // one step, the head instantiated at the first position and the tail's
    // family at `inr j`, both annotated by `Fin(2)`'s reduct.
    let ty = dvec(c(0), nat(2), id_at_i(nat(2)));
    let step = whnf(&ty, &g);
    let Type::Sigma { fst, snd, .. } = &step else { panic!("expected Σ, got {step:?}") };
    let at_first = Type::Id {
        level: c(0),
        ty: rty(fin(nat(2))),
        lhs: rt(first(nat(1))),
        rhs: rt(first(nat(1))),
    };
    assert_eq!(**fst, at_first);
    // The tail, in (·, x): DVec(1; j. Id(Fin 2; inr^{0,0}(Unit; Fin 1; j); …)).
    let at_next = Type::Id {
        level: c(0),
        ty: rty(fin(nat(2))),
        lhs: rt(next(nat(1), v(0))),
        rhs: rt(next(nat(1), v(0))),
    };
    assert_eq!(**snd, dvec(c(0), nat(1), at_next));
    // The whole chain against the explicit tuple type.
    let at = |p: u64| Type::Id { level: c(0), ty: rty(fin(nat(2))), lhs: rt(pos(2, p)), rhs: rt(pos(2, p)) };
    conv_ty(&g, &ty, &sigma(at(0), sigma(at(1), unit0())), c(0));
    // A position mismatch is visible: the family is not constant.
    not_conv_ty(&g, &ty, &sigma(at(1), sigma(at(1), unit0())), c(0));
    not_conv_ty(&g, &ty, &sigma(at(0), sigma(at(0), unit0())), c(0));
}

#[test]
fn dvec_reduces_at_a_numeral_and_a_computed_length() {
    let g = nil_ctx();
    let fam = id_at_i(nat(3));
    let lit = Type::DVec { level: c(0), len: rt(Term::NatLit(3u64.into())), fam: rty(fam.clone()) };
    conv_ty(&g, &lit, &dvec(c(0), nat(3), fam.clone()), c(0));
    // A length that computes: elim_Nat(_. Nat; 0; S (S r); 1) = 2, against
    // the family over `Fin 2`.
    let computed = Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(nat(0)),
        step: rt(Term::Succ(rt(Term::Succ(rt(v(0)))))),
        scrut: rt(nat(1)),
    };
    let fam2 = id_at_i(nat(2));
    conv_ty(&g, &dvec(c(0), computed, fam2.clone()), &dvec(c(0), nat(2), fam2), c(0));
}

#[test]
fn neutral_at_a_neutral_length() {
    // Γ = (k : Nat): DVec(k; i. F) is stuck, and congruence compares level,
    // length and family — the family under `i : Fin k` (`gne_ty_dvec`).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let fam = id_at_i(v(1));
    let dk = dvec(c(0), v(0), fam.clone());
    assert!(is_whnf_type(&dk));
    assert_eq!(whnf(&dk, &g), dk);
    ck_ty(&g, &dk, c(0));
    conv_ty(&g, &dk, &dk.clone(), c(0));
    // Different length, family, or level: distinguished.
    not_conv_ty(&g, &dk, &dvec(c(0), Term::Succ(rt(v(0))), fam.clone()), c(0));
    not_conv_ty(&g, &dk, &dvec(c(0), v(0), Type::Nat), c(0));
    not_conv_ty(&g, &dk, &dvec(c(1), v(0), fam.clone()), c(0));
    // Families convertible only under the binder: `Id(Fin k; i; i)` against
    // its spelling with the endpoints as `elim_Nat(_. Fin k; i; _ _. i; 0)`.
    let i_again = Term::ElimNat {
        level: c(0),
        motive: rty(fin(v(2))),
        base: rt(v(0)),
        step: rt(v(2)),
        scrut: rt(nat(0)),
    };
    let fam2 = Type::Id { level: c(0), ty: rty(fin(v(1))), lhs: rt(i_again.clone()), rhs: rt(i_again) };
    conv_ty(&g, &dk, &dvec(c(0), v(0), fam2), c(0));
    // Successor of a neutral still reduces.
    let ds = dvec(c(0), Term::Succ(rt(v(0))), id_at_i(Term::Succ(rt(v(1)))));
    let head = Type::Id {
        level: c(0),
        ty: rty(fin(Term::Succ(rt(v(0))))),
        lhs: rt(first(v(0))),
        rhs: rt(first(v(0))),
    };
    let tail_fam = Type::Id {
        level: c(0),
        ty: rty(fin(Term::Succ(rt(v(2))))),
        lhs: rt(next(v(2), v(0))),
        rhs: rt(next(v(2), v(0))),
    };
    conv_ty(&g, &ds, &sigma(head, dvec(c(0), v(1), tail_fam)), c(0));
}

#[test]
fn vec_and_a_constant_dvec_agree_only_at_a_canonical_length() {
    // Design §1.1/§10: reduct for reduct at a canonical length…
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    conv_ty(&g, &vec(Type::Nat, nat(2)), &dvec(c(0), nat(2), Type::Nat), c(0));
    conv_ty(&g, &vec(Type::Nat, Term::Succ(rt(nat(0)))), &dvec(c(0), nat(1), Type::Nat), c(0));
    // …and two distinct neutral types at a neutral one: no conversion
    // between the two spellings is stated or wanted (option 1).
    not_conv_ty(&g, &vec(Type::Nat, v(0)), &dvec(c(0), v(0), Type::Nat), c(0));
}

// -------------------------------------------------------------------------
// Formation
// -------------------------------------------------------------------------

#[test]
fn formation_and_level() {
    // ⊢ DVec^l(k; i. F) @ l ⟸ k : Nat, (Γ, i : Fin k) ⊢ F @ l.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    ck_ty(&g, &dvec(c(0), v(0), id_at_i(v(1))), c(0));
    ck_ty(&g, &dvec(c(1), v(0), Type::Ty(c(0))), c(1));
    ck_ty(&g, &dvec(c(0), Term::Succ(rt(Term::Succ(rt(v(0))))), hetero_fam(v(0))), c(0));
    // The level is the family's, not one above it.
    assert_eq!(
        ck_ty_at(Layer::Prog, &g, &dvec(c(1), v(0), Type::Ty(c(0))), &c(2)),
        Err(TypeError::LevelMismatch)
    );
    // The family's annotation level must be its level.
    assert!(ck_ty_at(Layer::Prog, &g, &dvec(c(0), v(0), Type::Ty(c(0))), &c(0)).is_err());
    // The binder is `Fin k`, not `Nat`: `i` is not a length.
    assert!(ck_ty_at(Layer::Prog, &g, &dvec(c(0), v(0), fin(v(0))), &c(0)).is_err());
    // The length is a Nat.
    assert!(ck_ty_at(Layer::Prog, &nil_ctx(), &dvec(c(0), Term::Triv { level: c(0) }, Type::Nat), &c(0)).is_err());
}

#[test]
fn formation_is_admitted_at_layer_c() {
    // Design §13 step 4: `DVec` has a code (`TmDVec`, `tests/iwf_codes.rs`),
    // so it is admitted at layer c (the code recursors' layer) as at p and m.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let dk = dvec(c(0), v(0), Type::Nat);
    for layer in [Layer::Code, Layer::Prog, Layer::Meta] {
        assert_eq!(ck_ty_at(layer, &g, &dk, &c(0)), Ok(()));
    }
    // Nested under another former at layer c too.
    let nested = Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(Type::Nat), cod: rty(dvec(c(0), v(0), Type::Nat)) };
    assert_eq!(ck_ty_at(Layer::Code, &nil_ctx(), &nested, &c(0)), Ok(()));
    // The premises are still checked there: the family must be a type.
    assert!(ck_ty_at(Layer::Code, &g, &dvec(c(0), v(0), fin(v(0))), &c(0)).is_err());
}

// -------------------------------------------------------------------------
// Values
// -------------------------------------------------------------------------

#[test]
fn a_heterogeneous_tuple_inhabits_its_type() {
    // DVec(2; i. [Nat, Nat → Nat]) ∋ (3, (λx. x, ⟨⟩)): each position at its
    // own element type, read through the family's `case` on the position.
    let g = nil_ctx();
    let ty = dvec(c(0), nat(2), hetero_fam(nat(0)));
    let nat_to_nat =
        Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(Type::Nat), cod: rty(Type::Nat) };
    let id_fn = Term::Lam { dom_level: c(0), cod_level: c(0), dom: rty(Type::Nat), body: rt(v(0)) };
    let tail_ty = sigma(nat_to_nat.clone(), unit0());
    let tuple = pair(Type::Nat, tail_ty.clone(), nat(3), pair(nat_to_nat.clone(), unit0(), id_fn.clone(), Term::Triv { level: c(0) }));
    ck(&g, &tuple, &ty, c(0));
    // The positions are not interchangeable.
    let swapped = pair(nat_to_nat.clone(), sigma(Type::Nat, unit0()), id_fn, pair(Type::Nat, unit0(), nat(3), Term::Triv { level: c(0) }));
    not_ck(&g, &swapped, &ty, c(0));
    // Σ-η and Unit irrelevance reach the tuple through the reduction: a
    // variable of the type is its own projections.
    let gx = ext(&g, ty.clone(), c(0));
    let x = v(0);
    let eta = pair(
        Type::Nat,
        tail_ty.clone(),
        fst_of(Type::Nat, tail_ty.clone(), x.clone()),
        pair(
            nat_to_nat.clone(),
            unit0(),
            fst_of(nat_to_nat.clone(), unit0(), snd_of(Type::Nat, tail_ty.clone(), x.clone())),
            Term::Triv { level: c(0) },
        ),
    );
    conv_tm(&gx, &x, &eta, &ty, c(0));
    // At length 0, every two values are equal (Unit's irrelevance).
    let g0 = ext(&ext(&g, dvec(c(0), nat(0), Type::Nat), c(0)), dvec(c(0), nat(0), Type::Nat), c(0));
    conv_tm(&g0, &v(0), &v(1), &dvec(c(0), nat(0), Type::Nat), c(0));
    // At a neutral length, only the neutral comparison is left.
    let gk = ext(&ext(&ext(&g, Type::Nat, c(0)), dvec(c(0), v(0), Type::Nat), c(0)), dvec(c(0), v(1), Type::Nat), c(0));
    conv_tm(&gk, &v(0), &v(0), &dvec(c(0), v(2), Type::Nat), c(0));
    not_conv_tm(&gk, &v(0), &v(1), &dvec(c(0), v(2), Type::Nat), c(0));
}

// -------------------------------------------------------------------------
// dnth
// -------------------------------------------------------------------------

/// `dnth^l(n; F; cs; i)` with every argument a variable of
/// Γ = (n : Nat, cs : DVec^l(n; F), i : Fin n), at the family `fam_at(n)`.
fn open_dnth_ctx_at(l: Level, fam_at: impl Fn(Term) -> Type) -> (LocalCtx, Term, Type) {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, dvec(l.clone(), v(0), fam_at(v(1))), l.clone());
    let g = ext(&g, fin(v(1)), c(0));
    let fam = rty(fam_at(v(3)));
    let t = dnth(&l, &rt(v(2)), &fam, rt(v(1)), rt(v(0)));
    // The result type F[i/i], in Γ.
    let res = fam.inst_top(0, &v(0));
    (g, t, res)
}

fn open_dnth_ctx(fam_at: impl Fn(Term) -> Type) -> (LocalCtx, Term, Type) {
    open_dnth_ctx_at(c(0), fam_at)
}

#[test]
fn dnth_types_at_an_open_length() {
    // The schema's typing derivation crosses the three conversions the Coq
    // formalization's `dnth_wf`/`V_dnth` check (M17a): `Fin`'s computation
    // at the base and the step, Unit-η at the `inl` arm (the family at
    // `e (inl x)` against `e (inl ⟨⟩)`), and β at the recursive call (the
    // family at `(λy. e (inr y)) j` against `e (inr j)`) and at the
    // identity embedding. A family that mentions its position is what
    // makes each of them load-bearing.
    let (g, t, res) = open_dnth_ctx(id_at_i);
    ck(&g, &t, &res, c(0));
    // A family that does not mention it, and one at a higher level.
    let (g, t, res) = open_dnth_ctx(|_| Type::Nat);
    ck(&g, &t, &res, c(0));
    let (g, t, res) = open_dnth_ctx_at(c(1), |_| Type::Ty(c(0)));
    ck(&g, &t, &res, c(1));
    // Its type is the family at the index and nothing else.
    let (g, t, _) = open_dnth_ctx(id_at_i);
    not_ck(&g, &t, &Type::Nat, c(0));
}

#[test]
fn dnth_types_at_a_literal_length_and_a_heterogeneous_family() {
    // n = 2 over hetero_fam: dnth(2; F; cs; inl ⟨⟩) : Nat and
    // dnth(2; F; cs; inr (inl ⟨⟩)) : Nat → Nat, for an open `cs`.
    let fam = rty(hetero_fam(nat(0)));
    let g = ext(&nil_ctx(), dvec(c(0), nat(2), hetero_fam(nat(0))), c(0));
    let nat_to_nat =
        Type::Pi { dom_level: c(0), cod_level: c(0), dom: rty(Type::Nat), cod: rty(Type::Nat) };
    let at0 = dnth(&c(0), &rt(nat(2)), &fam, rt(v(0)), rt(pos(2, 0)));
    let at1 = dnth(&c(0), &rt(nat(2)), &fam, rt(v(0)), rt(pos(2, 1)));
    ck(&g, &at0, &Type::Nat, c(0));
    ck(&g, &at1, &nat_to_nat, c(0));
    not_ck(&g, &at0, &nat_to_nat, c(0));
    // At a canonical tuple it is the component.
    let id_fn = Term::Lam { dom_level: c(0), cod_level: c(0), dom: rty(Type::Nat), body: rt(v(0)) };
    let tuple = pair(
        Type::Nat,
        sigma(nat_to_nat.clone(), unit0()),
        nat(3),
        pair(nat_to_nat.clone(), unit0(), id_fn.clone(), Term::Triv { level: c(0) }),
    );
    let g0 = nil_ctx();
    conv_tm(&g0, &dnth(&c(0), &rt(nat(2)), &fam, rt(tuple.clone()), rt(pos(2, 0))), &nat(3), &Type::Nat, c(0));
    conv_tm(&g0, &dnth(&c(0), &rt(nat(2)), &fam, rt(tuple), rt(pos(2, 1))), &id_fn, &nat_to_nat, c(0));
}

#[test]
fn dnth_of_a_neutral_tuple_is_its_projections() {
    // Design §3 / heather-coq `dnth_reds_example`: at a literal length and a
    // **neutral** tuple, dnth reduces to the projections — the property that
    // makes `elim_IWf`'s induction hypothesis usable, as `nth`'s is for `Wf`.
    // Γ = (cs : DVec(3; i. Id(Fin 3; i; i))).
    let fam3 = id_at_i(nat(3));
    let ty = dvec(c(0), nat(3), fam3.clone());
    let g = ext(&nil_ctx(), ty.clone(), c(0));
    let fam = rty(fam3);
    let cs = v(0);
    // The projections, annotated by the reducts' components.
    let at = |p: u64| Type::Id { level: c(0), ty: rty(fin(nat(3))), lhs: rt(pos(3, p)), rhs: rt(pos(3, p)) };
    let t2 = sigma(at(2), unit0());
    let t1 = sigma(at(1), t2.clone());
    let p0 = fst_of(at(0), t1.clone(), cs.clone());
    let s1 = snd_of(at(0), t1.clone(), cs.clone());
    let p1 = fst_of(at(1), t2.clone(), s1.clone());
    let s2 = snd_of(at(1), t2.clone(), s1);
    let p2 = fst_of(at(2), unit0(), s2);
    for (p, proj) in [(0, &p0), (1, &p1), (2, &p2)] {
        let t = dnth(&c(0), &rt(nat(3)), &fam, rt(cs.clone()), rt(pos(3, p)));
        ck(&g, &t, &at(p), c(0));
        conv_tm(&g, &t, proj, &at(p), c(0));
    }
    // The instance the design states: dnth(3; F; cs; inr (inl ⟨⟩)) ≡ fst (snd cs).
    let t = dnth(&c(0), &rt(nat(3)), &fam, rt(cs.clone()), rt(pos(3, 1)));
    not_conv_tm(&g, &t, &p0, &at(1), c(0));
    // The rewriter reaches the projection too: its weak head normal form is
    // `fst (snd cs)`, whatever its annotations.
    let w = whnf_term(&t, &g, FUEL).expect("enough fuel");
    let Term::Fst { pair, .. } = &w else { panic!("expected a projection, got {w:?}") };
    let Term::Snd { pair, .. } = &**pair else { panic!("expected snd cs, got {pair:?}") };
    assert_eq!(**pair, cs);
}

#[test]
fn dnth_is_neutral_at_a_neutral_index_or_length() {
    // A neutral index at a literal length: stuck on the `case`, so not
    // convertible with any one projection.
    let fam3 = id_at_i(nat(3));
    let g = ext(&ext(&nil_ctx(), dvec(c(0), nat(3), fam3.clone()), c(0)), fin(nat(3)), c(0));
    let fam = rty(fam3);
    let res = Type::Id { level: c(0), ty: rty(fin(nat(3))), lhs: rt(v(0)), rhs: rt(v(0)) };
    let t = dnth(&c(0), &rt(nat(3)), &fam, rt(v(1)), rt(v(0)));
    ck(&g, &t, &res, c(0));
    conv_tm(&g, &t, &t.clone(), &res, c(0));
    // A neutral length: stuck on the `elim_Nat`, and two different indices
    // give two different neutrals.
    let (g, t, res) = open_dnth_ctx(|_| Type::Nat);
    conv_tm(&g, &t, &t.clone(), &res, c(0));
    let g2 = ext(&g, fin(v(2)), c(0));
    let t_i = dnth(&c(0), &rt(v(3)), &rty(Type::Nat), rt(v(2)), rt(v(1)));
    let t_j = dnth(&c(0), &rt(v(3)), &rty(Type::Nat), rt(v(2)), rt(v(0)));
    not_conv_tm(&g2, &t_i, &t_j, &Type::Nat, c(0));
}
