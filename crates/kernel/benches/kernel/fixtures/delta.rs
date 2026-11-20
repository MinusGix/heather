//! Conversion over **definitions**: the δ-lazy machinery (`Conv::delta_lazy`,
//! `Dom::delta_tm`) and the run machinery meeting glued values, which no
//! Ψ-free fixture reaches. Every family here has a Ψ of bodied globals and a
//! query whose cost is set by how conversion chooses to unfold them.
//!
//! The shapes are the ones the library has hit as cliffs:
//!
//! - **`closed-sum`** is the cliff of
//!   `issues/conversion-closed-sum-opaque-counter.md`: both sides are
//!   applications of the same defined `add`, so conversion first compares
//!   them argument by argument and advances the newer side one opaque δ-step
//!   at a time, down to a synchronous fold (`max`) over a glued counter. The
//!   counter is a chain of definitions each of which folds over the one
//!   before. Before `Eval::force_counter` the run machinery forced each such
//!   counter in the opaque run's mode, every match inside stalled, and each
//!   level replayed the one below twice: exponential in the chain.
//!   `closed-numeral` is the same left side against a numeral, which skips
//!   the same-head attempt; the two should cost the same.
//! - **`lockstep`** compares two separately defined chains with the same
//!   value: neither side is a numeral, so conversion advances the newer side
//!   (`issues/conversion-meet-past-newer-head.md`) until the heads meet.
//! - **`same-head-args`** is a same-head application whose arguments agree
//!   only by computation: the attempt that compares arguments must fail
//!   cheaply and fall back to unfolding, not pay for both.
//!
//! Sizes are the length of the definition chain, so a linear slope is the
//! claim: one δ-step and a bounded amount of work per definition.

use heather_kernel::conv::{conv_term, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::typing::{check_global_ctx, check_term};
use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar, LocalSubst, SubstTail, Term, Type};

use super::terms::{nil_ctx, num, rt, rty, v};
use super::FUEL;
use crate::harness::{Case, Family};

pub fn families() -> Vec<Family> {
    vec![
        closed_sum(),
        closed_numeral(),
        lockstep(),
        refusal(),
        same_head_args(),
        shared_dag(),
        record_projections(),
        check_refl(),
        bool_verdict(),
    ]
}

const SIZES: [u64; 5] = [8, 16, 32, 64, 128];

/// `Nat → Nat`.
pub(super) fn nat_to_nat() -> Type {
    Type::Pi { dom_level: Level::Zero, cod_level: Level::Zero, dom: rty(Type::Nat), cod: rty(Type::Nat) }
}

/// `Nat → Nat → Nat`.
pub(super) fn nat2_to_nat() -> Type {
    Type::Pi { dom_level: Level::Zero, cod_level: Level::Zero, dom: rty(Type::Nat), cod: rty(nat_to_nat()) }
}

pub(super) fn lam(body: Term) -> Term {
    Term::Lam { dom_level: Level::Zero, cod_level: Level::Zero, dom: rty(Type::Nat), body: rt(body) }
}

pub(super) fn app_at(f: Term, a: Term, cod: Type) -> Term {
    Term::App {
        fun: rt(f),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(cod),
        arg: rt(a),
    }
}

/// `f a b` for `f : Nat → Nat → Nat`.
pub(super) fn app2(f: Term, a: Term, b: Term) -> Term {
    app_at(app_at(f, a, nat_to_nat()), b, Type::Nat)
}

/// `u : Trm_c(· ⊢ ty @ 0) := body`.
pub(super) fn def(ty: Type, body: Term) -> GlobalBinding {
    GlobalBinding::Tm { ctx: nil_ctx(), layer: Layer::Code, ty: rty(ty), level: Level::Zero, body: Some(rt(body)) }
}

/// A Ψ built oldest first, handing each body a way to name the bindings
/// before it by **position** rather than by de Bruijn index.
pub(super) struct Defs {
    bindings: Vec<GlobalBinding>,
}

impl Defs {
    pub(super) fn new() -> Defs {
        Defs { bindings: vec![] }
    }

    /// The position the next binding will take.
    pub(super) fn next(&self) -> usize {
        self.bindings.len()
    }

    /// The binding at position `p`, referenced from a body at position
    /// `from` (or from the query when `from` is the final length).
    pub(super) fn at(p: usize, from: usize) -> Term {
        assert!(p < from, "a body can only name an older binding");
        Term::GlobalTm {
            var: GlobalVar::index((from - 1 - p) as u32),
            subst: LocalSubst { tail: SubstTail::Empty, terms: vec![] },
        }
    }

    pub(super) fn push(&mut self, ty: Type, body: impl FnOnce(usize) -> Term) -> usize {
        let p = self.next();
        let body = body(p);
        self.bindings.push(def(ty, body));
        p
    }

    pub(super) fn finish(self) -> (GlobalCtx, usize) {
        let n = self.bindings.len();
        let psi = GlobalCtx::new(self.bindings);
        // A fixture over an ill-typed Ψ would measure an error path.
        assert!(check_global_ctx(&psi, 0, FUEL).is_ok(), "the fixture's Ψ does not check");
        (psi, n)
    }
}

/// `add := λm n. elim_Nat(n; Nat; m; _ ih. Succ ih)` — recursion on the
/// second argument, an affine fold.
pub(super) fn add_def() -> Term {
    lam(lam(Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(v(1)),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(v(0)),
    }))
}

/// `max := λa. elim_Nat(a; Nat → Nat; λb. b; k ih. λb. elim_Nat(b; Nat;
/// Succ k; l _. Succ (ih l)))` — the synchronous fold (`FoldClass::Sync`):
/// one successor from each counter, one successor out.
pub(super) fn max_def() -> Term {
    // Inner step binders: _ = 0, l = 1, b = 2, ih = 3, k = 4.
    let inner = Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(Term::Succ(rt(v(2)))),
        step: rt(Term::Succ(rt(app_at(v(3), v(1), Type::Nat)))),
        scrut: rt(v(0)),
    };
    lam(Term::ElimNat {
        level: Level::Zero,
        motive: rty(nat_to_nat()),
        base: rt(lam(v(0))),
        step: rt(lam(inner)),
        scrut: rt(v(0)),
    })
}

/// `pred t`: a fold that does not use its hypothesis (`FoldClass::Direct`),
/// i.e. a `match`.
pub(super) fn pred(t: Term) -> Term {
    Term::ElimNat { level: Level::Zero, motive: rty(Type::Nat), base: rt(Term::Zero), step: rt(v(1)), scrut: rt(t) }
}

/// The value every chain level of [`closed_chain`] has.
const LEVEL_VALUE: u64 = 40;

/// Ψ = `add, max, d₀ := 40, dᵢ := Succ(max(pred dᵢ₋₁, pred dᵢ₋₁)), top :=
/// max(dₙ, 0)`. Every `dᵢ` is 40, but only a run that unfolds `dᵢ₋₁` gets
/// past the `pred`: the counter `max` folds over is a glued definition whose
/// body matches on another one, which is the shape of the compiler's
/// `Source::top` folding `Nat::max` over `reach_by(…)`.
///
/// Returns Ψ, its length, and the positions of `add` and `top`.
fn closed_chain(n: u64) -> (GlobalCtx, usize, usize, usize) {
    let mut ds = Defs::new();
    let add = ds.push(nat2_to_nat(), |_| add_def());
    let max = ds.push(nat2_to_nat(), |_| max_def());
    let mut prev = ds.push(Type::Nat, |_| num(LEVEL_VALUE));
    for _ in 0..n {
        prev = ds.push(Type::Nat, |at| {
            let d = || Defs::at(prev, at);
            app2(Defs::at(max, at), d(), pred(d()))
        });
    }
    let top = ds.push(Type::Nat, |at| app2(Defs::at(max, at), Defs::at(prev, at), Term::Zero));
    let (psi, len) = ds.finish();
    (psi, len, add, top)
}

fn conv_case(n: u64, psi: GlobalCtx, lhs: Term, rhs: Term) -> Case {
    let gamma = nil_ctx();
    let go = move || {
        conv_term(&psi, &gamma, Layer::Prog, &lhs, &rhs, &Type::Nat, &Level::Zero, FUEL).is_ok() as u64
    };
    assert!(go() == 1, "the size-{n} definition fixture does not convert");
    Case::new(n, 1, go)
}

/// `add(top, 8) ≡ add(add(8, 16), 24)`: the same defined head on both sides.
fn closed_sum() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let (psi, len, add, top) = closed_chain(n);
            let a = || Defs::at(add, len);
            let lhs = app2(a(), Defs::at(top, len), num(8));
            let rhs = app2(a(), app2(a(), num(8), num(16)), num(LEVEL_VALUE - 16));
            conv_case(n, psi, lhs, rhs)
        })
        .collect();
    Family {
        name: "delta/closed-sum",
        what: "add(top, 8) ≡ add(add(8, 16), 24) — top a max over a chain of glued definitions",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}

/// `add(top, 8) ≡ 48`: the control for `closed-sum`. No same-head attempt;
/// the left side is unfolded by one transparent run.
fn closed_numeral() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let (psi, len, add, top) = closed_chain(n);
            let lhs = app2(Defs::at(add, len), Defs::at(top, len), num(8));
            conv_case(n, psi, lhs, num(LEVEL_VALUE + 8))
        })
        .collect();
    Family {
        name: "delta/closed-numeral",
        what: "add(top, 8) ≡ 48 — closed-sum's left side against a numeral",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}

/// Two chains `aᵢ := add(aᵢ₋₁, 1)` and `bᵢ := Succ(bᵢ₋₁)` from `a₀ := b₀ :=
/// 0`, interleaved in Ψ so that neither chain is wholly newer than the
/// other; `aₙ ≡ bₙ`.
fn lockstep() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let mut ds = Defs::new();
            let add = ds.push(nat2_to_nat(), |_| add_def());
            let mut a = ds.push(Type::Nat, |_| Term::Zero);
            let mut b = ds.push(Type::Nat, |_| Term::Zero);
            for _ in 0..n {
                a = ds.push(Type::Nat, |at| app2(Defs::at(add, at), Defs::at(a, at), num(1)));
                b = ds.push(Type::Nat, |at| Term::Succ(rt(Defs::at(b, at))));
            }
            let (psi, len) = ds.finish();
            conv_case(n, psi, Defs::at(a, len), Defs::at(b, len))
        })
        .collect();
    Family {
        name: "delta/lockstep",
        what: "aₙ ≡ bₙ — two interleaved chains of definitions with the same value",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}

/// `f(cₙ) ≡ f(n)` for `f := λx. add(x, x)` and a chain `cᵢ := Succ(cᵢ₋₁)`:
/// the same defined head, arguments equal only after unfolding the chain.
/// The argument comparison succeeds here, by unfolding `cₙ`; what the family
/// pins is that it costs one walk of the chain, not one per comparison.
fn same_head_args() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let mut ds = Defs::new();
            let add = ds.push(nat2_to_nat(), |_| add_def());
            let f = ds.push(nat_to_nat(), |at| lam(app2(Defs::at(add, at), v(0), v(0))));
            let mut c = ds.push(Type::Nat, |_| Term::Zero);
            for _ in 0..n {
                c = ds.push(Type::Nat, |at| Term::Succ(rt(Defs::at(c, at))));
            }
            let (psi, len) = ds.finish();
            let lhs = app_at(Defs::at(f, len), Defs::at(c, len), Type::Nat);
            let rhs = app_at(Defs::at(f, len), num(n), Type::Nat);
            conv_case(n, psi, lhs, rhs)
        })
        .collect();
    Family {
        name: "delta/same-head-args",
        what: "f(cₙ) ≡ f(n) — a defined head, arguments equal only through a chain",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}

/// The interleaved chains of [`lockstep`], `aᵢ := add(aᵢ₋₁, 1)` from `a₀ :=
/// 0` and `bᵢ := Succ(bᵢ₋₁)` from `b₀ := base`. Returns Ψ, its length, and
/// the positions of `aₙ` and `bₙ`.
fn two_chains(n: u64, base: u64) -> (GlobalCtx, usize, usize, usize) {
    let mut ds = Defs::new();
    let add = ds.push(nat2_to_nat(), |_| add_def());
    let mut a = ds.push(Type::Nat, |_| Term::Zero);
    let mut b = ds.push(Type::Nat, |_| num(base));
    for _ in 0..n {
        a = ds.push(Type::Nat, |at| app2(Defs::at(add, at), Defs::at(a, at), num(1)));
        b = ds.push(Type::Nat, |at| Term::Succ(rt(Defs::at(b, at))));
    }
    let (psi, len) = ds.finish();
    (psi, len, a, b)
}

/// `aₙ ≢ bₙ` for [`two_chains`] one apart: the cost of a **refusal**. A
/// mismatch has to be found by the same lockstep that finds a match, and a
/// failed attempt must not fall back into a second full unfolding; the
/// family pins that it costs what `lockstep` costs.
fn refusal() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let (psi, len, a, b) = two_chains(n, 1);
            let (lhs, rhs) = (Defs::at(a, len), Defs::at(b, len));
            let gamma = nil_ctx();
            let go = move || conv_term(&psi, &gamma, Layer::Prog, &lhs, &rhs, &Type::Nat, &Level::Zero, FUEL);
            // A refusal for fuel would measure the budget, not the mismatch.
            assert_eq!(go(), Err(ConvError::NotConvertible), "size {n}: not a genuine mismatch");
            Case::new(n, 0, move || go().is_ok() as u64)
        })
        .collect();
    Family {
        name: "delta/refusal",
        what: "aₙ ≢ bₙ — lockstep's chains one apart: what finding a mismatch costs",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}

/// `dₙ ≡ 40` for `dᵢ := max(dᵢ₋₁, dᵢ₋₁)`: a chain whose **tree** doubles at
/// every level while its DAG grows by one node. Each definition is reached
/// twice from the one above, so anything that forgets an unfolding it has
/// already done (a glued value's memo, the δ-cache) turns linear into
/// exponential. Sizes stay small enough that an exponential still ends.
fn shared_dag() -> Family {
    let cases = [4u64, 8, 12, 16, 20]
        .iter()
        .map(|&n| {
            let mut ds = Defs::new();
            let max = ds.push(nat2_to_nat(), |_| max_def());
            let mut d = ds.push(Type::Nat, |_| num(LEVEL_VALUE));
            for _ in 0..n {
                d = ds.push(Type::Nat, |at| app2(Defs::at(max, at), Defs::at(d, at), Defs::at(d, at)));
            }
            let (psi, len) = ds.finish();
            conv_case(n, psi, Defs::at(d, len), num(LEVEL_VALUE))
        })
        .collect();
    Family {
        name: "delta/shared-dag",
        what: "dₙ ≡ 40, dᵢ := max(dᵢ₋₁, dᵢ₋₁) — a tree 2ⁿ wide over a DAG n long",
        unit: "definitions",
        expect_slope: Some((0.70, 1.40)),
        cases,
    }
}

/// `Σ(_ : Nat). Nat`.
fn nat_pair() -> Type {
    Type::Sigma { fst_level: Level::Zero, snd_level: Level::Zero, fst: rty(Type::Nat), snd: rty(Type::Nat) }
}

fn fst(p: Term) -> Term {
    Term::Fst { fst_level: Level::Zero, snd_level: Level::Zero, fst_ty: rty(Type::Nat), snd_ty: rty(Type::Nat), pair: rt(p) }
}

fn snd(p: Term) -> Term {
    Term::Snd { fst_level: Level::Zero, snd_level: Level::Zero, fst_ty: rty(Type::Nat), snd_ty: rty(Type::Nat), pair: rt(p) }
}

fn pair(a: Term, b: Term) -> Term {
    Term::Pair {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        fst: rt(a),
        snd: rt(b),
    }
}

/// `add(fst rₙ, snd rₙ) ≡ n + 7` for records `r₀ := (0, 7)`, `rᵢ := (Succ
/// (fst rᵢ₋₁), snd rᵢ₋₁)`: every field read is a projection out of a glued
/// definition, the way the compiler's records (a source, its homes and
/// bodies) are read. One field moves and one is carried, so both the
/// projection of a computed field and of a copied one are walked.
fn record_projections() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let mut ds = Defs::new();
            let add = ds.push(nat2_to_nat(), |_| add_def());
            let mut r = ds.push(nat_pair(), |_| pair(Term::Zero, num(7)));
            for _ in 0..n {
                r = ds.push(nat_pair(), |at| {
                    pair(Term::Succ(rt(fst(Defs::at(r, at)))), snd(Defs::at(r, at)))
                });
            }
            let (psi, len) = ds.finish();
            let lhs = app2(Defs::at(add, len), fst(Defs::at(r, len)), snd(Defs::at(r, len)));
            conv_case(n, psi, lhs, num(n + 7))
        })
        .collect();
    Family {
        name: "delta/record-projections",
        what: "add(fst rₙ, snd rₙ) ≡ n + 7 — field reads out of a chain of glued records",
        unit: "definitions",
        expect_slope: Some((0.70, 1.40)),
        cases,
    }
}

/// `check_term(refl : aₙ = n)` over [`two_chains`]'s `a`: the gate's own
/// path to a closed equation (`theorem … { refl }`), through the checker's
/// conversion of the two endpoints rather than a bare `conv_term`.
fn check_refl() -> Family {
    let cases = SIZES
        .iter()
        .map(|&n| {
            let (psi, len, a, _) = two_chains(n, 0);
            let an = Defs::at(a, len);
            let refl = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(an.clone()) };
            let goal = Type::Id { level: Level::Zero, ty: rty(Type::Nat), lhs: rt(an), rhs: rt(num(n)) };
            let gamma = nil_ctx();
            let go = move || {
                check_term(&psi, 0, Layer::Prog, &gamma, &refl, &goal, &Level::Zero, FUEL).is_ok() as u64
            };
            assert!(go() == 1, "size {n}: refl does not check");
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "delta/check-refl",
        what: "check(refl : aₙ = n) — a closed equation through the checker",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}

fn unit() -> Type {
    Type::Unit { level: Level::Zero }
}

/// `Bool := Unit + Unit`, `true` on the left.
fn bool_ty() -> Type {
    Type::Sum { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs: rty(unit()), rhs: rty(unit()) }
}

fn truth(b: bool) -> Term {
    let val = rt(Term::Triv { level: Level::Zero });
    let (lhs, rhs) = (rty(unit()), rty(unit()));
    if b {
        Term::Inl { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs, rhs, val }
    } else {
        Term::Inr { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs, rhs, val }
    }
}

/// `if scrut then yes else no` at `Bool`, where `yes`/`no` are scoped under
/// the case's one binder.
fn if_bool(scrut: Term, yes: Term, no: Term) -> Term {
    Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(unit()),
        rhs: rty(unit()),
        motive: rty(bool_ty()),
        case_l: rt(yes),
        case_r: rt(no),
        scrut: rt(scrut),
    }
}

/// `b = True` by `refl` for a verdict folded over a chain: `and := λa b.
/// if a then b else false`, `pos := λk. elim_Nat(k; Bool; false; _ _.
/// true)`, `v₀ := true`, `vᵢ := and(vᵢ₋₁, pos(i))`. The library's rule for
/// closed facts (`docs/proof-patterns.md`: closed verdicts as `b = True` by
/// `refl`) at the size of a verdict over many rows.
fn bool_verdict() -> Family {
    fn bool_to(cod: Type) -> Type {
        Type::Pi { dom_level: Level::Zero, cod_level: Level::Zero, dom: rty(bool_ty()), cod: rty(cod) }
    }
    fn lam_bool(body: Term) -> Term {
        Term::Lam { dom_level: Level::Zero, cod_level: Level::Zero, dom: rty(bool_ty()), body: rt(body) }
    }
    fn app_bool(f: Term, a: Term, cod: Type) -> Term {
        Term::App {
            fun: rt(f),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(bool_ty()),
            cod: rty(cod),
            arg: rt(a),
        }
    }
    let cases = SIZES
        .iter()
        .map(|&n| {
            let mut ds = Defs::new();
            // λa b. case a of inl _ ⇒ b | inr _ ⇒ false; under the case's
            // binder, b = 1 and a = 2.
            let and = ds.push(bool_to(bool_to(bool_ty())), |_| {
                lam_bool(lam_bool(if_bool(v(1), v(1), truth(false))))
            });
            let pos = ds.push(
                Type::Pi { dom_level: Level::Zero, cod_level: Level::Zero, dom: rty(Type::Nat), cod: rty(bool_ty()) },
                |_| {
                    lam(Term::ElimNat {
                        level: Level::Zero,
                        motive: rty(bool_ty()),
                        base: rt(truth(false)),
                        step: rt(truth(true)),
                        scrut: rt(v(0)),
                    })
                },
            );
            let mut verdict = ds.push(bool_ty(), |_| truth(true));
            for i in 1..=n {
                verdict = ds.push(bool_ty(), |at| {
                    let row = app_at(Defs::at(pos, at), num(i), bool_ty());
                    app_bool(app_bool(Defs::at(and, at), Defs::at(verdict, at), bool_to(bool_ty())), row, bool_ty())
                });
            }
            let (psi, len) = ds.finish();
            let vn = Defs::at(verdict, len);
            let refl = Term::Refl { level: Level::Zero, ty: rty(bool_ty()), tm: rt(vn.clone()) };
            let goal = Type::Id { level: Level::Zero, ty: rty(bool_ty()), lhs: rt(vn), rhs: rt(truth(true)) };
            let gamma = nil_ctx();
            let go = move || {
                check_term(&psi, 0, Layer::Prog, &gamma, &refl, &goal, &Level::Zero, FUEL).is_ok() as u64
            };
            assert!(go() == 1, "size {n}: the verdict is not True by refl");
            Case::new(n, 1, go)
        })
        .collect();
    Family {
        name: "delta/bool-verdict",
        what: "check(refl : vₙ = true) — a closed verdict and-ed over n rows of definitions",
        unit: "definitions",
        expect_slope: Some((0.80, 1.40)),
        cases,
    }
}
