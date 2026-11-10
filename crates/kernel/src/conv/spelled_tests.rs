//! The lockstep walk ([`Conv::lockstep`]) and the closed-pair table
//! ([`ClosedPairs`]): what they accept, what they must still refuse, and
//! what the table may keep.
//!
//! The differential tests (`tests/conv_differential.rs`) hold the verdicts
//! to the rewriter, which takes neither ([`Dom::SPELLED`]). These are the
//! cases that need one [`GlobalCache`] across queries, which no public entry
//! lends, and the ones about cost: fuel, depth, and what a table hit skips.

use super::*;
use crate::term::{CtxBase, CtxEntry, LocalSubst, SubstTail};

const FUEL: u64 = 100_000;

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn zero() -> Level {
    Level::Zero
}

fn ctx(entries: Vec<(Type, Level)>) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: entries.into_iter().map(|(ty, level)| CtxEntry { ty: rty(ty), level }).collect::<Vec<_>>().into(),
    }
}

/// `u^·`: a closed mention of the global at index `var`.
fn glob(var: u32) -> Term {
    Term::GlobalTm { var: GlobalVar::index(var), subst: LocalSubst { tail: SubstTail::Empty, terms: vec![] } }
}

/// `u : Trm_c(· ⊢ ty @ level)`, defined when `body` is given.
fn binding(ty: Type, level: Level, body: Option<Term>) -> GlobalBinding {
    GlobalBinding::Tm { ctx: ctx(vec![]), layer: Layer::Code, ty: rty(ty), level, body: body.map(rt) }
}

fn el(code: &Rc<Term>) -> Type {
    Type::El { level: zero(), tm: Rc::clone(code) }
}

fn sum(lhs: Type, rhs: Type) -> Type {
    Type::Sum { lhs_level: zero(), rhs_level: zero(), lhs: rty(lhs), rhs: rty(rhs) }
}

fn sigma(fst: Type, snd: Type) -> Type {
    Type::Sigma { fst_level: zero(), snd_level: zero(), fst: rty(fst), snd: rty(snd) }
}

fn tm_sigma(fst: Term, snd: Term) -> Term {
    Term::TmSigma { fst_level: zero(), snd_level: zero(), fst: rt(fst), snd: rt(snd) }
}

fn tm_sum(lhs: &Rc<Term>, rhs: Term) -> Term {
    Term::TmSum { lhs_level: zero(), rhs_level: zero(), lhs: Rc::clone(lhs), rhs: rt(rhs) }
}

/// `Nat → Ty 0`, the type of a family of codes.
fn family() -> Type {
    Type::Pi { dom_level: zero(), cod_level: Level::constant(1), dom: rty(Type::Nat), cod: rty(Type::Ty(zero())) }
}

/// `f n` for `f : Nat → Ty 0`.
fn at(f: Term, n: Term) -> Rc<Term> {
    rt(Term::App {
        fun: rt(f),
        dom_level: zero(),
        cod_level: Level::constant(1),
        dom: rty(Type::Nat),
        cod: rty(Type::Ty(zero())),
        arg: rt(n),
    })
}

fn types(psi: &GlobalCtx, gamma: &LocalCtx, a: &Type, b: &Type, fuel: u64, cache: &Rc<GlobalCache>) -> R {
    let arena = ValueArena::new();
    let env = Env::new_with(&arena, psi, gamma, Layer::Prog, Rc::clone(cache));
    Conv::<Values>::new(fuel, psi).ty_root(&env, a, b, &zero())
}

/// Two codes at `Ty 0`.
fn codes(psi: &GlobalCtx, a: &Term, b: &Term, cache: &Rc<GlobalCache>) -> R {
    let arena = ValueArena::new();
    let env = Env::new_with(&arena, psi, &ctx(vec![]), Layer::Prog, Rc::clone(cache));
    Conv::<Values>::new(FUEL, psi).tm_root(&env, a, b, &Type::Ty(zero()), &Level::constant(1))
}

fn kept(cache: &Rc<GlobalCache>) -> usize {
    cache.closed.borrow().pairs.len()
}

fn fresh(psi: &GlobalCtx) -> Rc<GlobalCache> {
    Rc::new(GlobalCache::for_psi(psi))
}

/// `Σ(_ : Nat). … Σ(_ : Nat). leaf`, `depth` deep, as a code.
fn nest_code(depth: u32, leaf: Term) -> Term {
    (0..depth).fold(leaf, |code, _| tm_sigma(Term::TmNat, code))
}

/// The type [`nest_code`] spells.
fn nest_type(depth: u32, leaf: Type) -> Type {
    (0..depth).fold(leaf, |ty, _| sigma(Type::Nat, ty))
}

/// `inner := Nat : Ty 0` and `code := Σ(_ : Nat). … inner : Ty 0`, or the
/// two declared and not defined. From outside, `code` is index 0. Judging
/// `code` against its spelling unfolds both, which costs enough to be kept
/// ([`CLOSED_PAIR_WORTH`]).
fn named_nest(defined: bool) -> GlobalCtx {
    let ty0 = || Type::Ty(zero());
    GlobalCtx::new(vec![
        binding(ty0(), Level::constant(1), defined.then_some(Term::TmNat)),
        binding(ty0(), Level::constant(1), defined.then(|| nest_code(12, glob(0)))),
    ])
}

/// `Σ(x : Nat). Id(Nat; x; rhs)` as a type, and its code.
fn sigma_id(rhs: Term) -> (Type, Rc<Term>) {
    let id = Type::Id { level: zero(), ty: rty(Type::Nat), lhs: rt(Term::Var(LocalVar(0))), rhs: rt(rhs.clone()) };
    let code = Term::TmId { level: zero(), ty: rt(Term::TmNat), lhs: rt(Term::Var(LocalVar(0))), rhs: rt(rhs) };
    (sigma(Type::Nat, id), rt(tm_sigma(Term::TmNat, code)))
}

#[test]
fn a_code_and_the_type_it_spells_are_compared_without_reducing() {
    let psi = GlobalCtx::new(vec![]);
    let g = ctx(vec![]);
    let (ty, code) = sigma_id(Term::Zero);
    // One unit for the root and one per component pair: nothing is
    // evaluated, so a budget this small is enough.
    assert_eq!(types(&psi, &g, &ty, &el(&code), 8, &fresh(&psi)), Ok(()));
    assert_eq!(types(&psi, &g, &el(&code), &ty, 8, &fresh(&psi)), Ok(()));
    // Negative controls: another endpoint, and another level on the former.
    let (other, _) = sigma_id(Term::Succ(rt(Term::Zero)));
    assert_eq!(types(&psi, &g, &other, &el(&code), FUEL, &fresh(&psi)), Err(NC));
    let lifted = Type::Sigma {
        fst_level: zero(),
        snd_level: Level::constant(1),
        fst: rty(Type::Nat),
        snd: rty(Type::Ty(zero())),
    };
    let flat = rt(tm_sigma(Term::TmNat, Term::TmTy(zero())));
    assert_eq!(types(&psi, &g, &lifted, &el(&flat), FUEL, &fresh(&psi)), Err(NC));
}

#[test]
fn the_walk_is_bounded_by_fuel_and_by_depth() {
    let psi = GlobalCtx::new(vec![]);
    let g = ctx(vec![]);
    let nest = |depth: u32| (nest_type(depth, Type::Nat), rt(nest_code(depth, Term::TmNat)));
    let (ty, code) = nest(64);
    assert_eq!(types(&psi, &g, &ty, &el(&code), 16, &fresh(&psi)), Err(ConvError::OutOfFuel));
    assert_eq!(types(&psi, &g, &ty, &el(&code), FUEL, &fresh(&psi)), Ok(()));
    // Deeper than the native frames allowed: refused as exhaustion, with
    // fuel to spare, and not by the stack.
    let (ty, code) = nest(NATIVE_DEPTH_LIMIT + 64);
    assert_eq!(types(&psi, &g, &ty, &el(&code), 1 << 30, &fresh(&psi)), Err(ConvError::OutOfFuel));
}

#[test]
fn a_named_code_against_its_spelling_is_kept_for_the_next_query() {
    let psi = named_nest(true);
    let g = ctx(vec![]);
    let named = rt(glob(0));
    let a = sum(el(&named), Type::Nat);
    let b = sum(nest_type(12, Type::Nat), Type::Nat);
    // A root and two component pairs: three units reach the named code,
    // and unfolding it needs more.
    let cache = fresh(&psi);
    assert_eq!(types(&psi, &g, &a, &b, 3, &cache), Err(ConvError::OutOfFuel));
    assert_eq!(kept(&cache), 0, "exhaustion is not a verdict");
    assert_eq!(types(&psi, &g, &a, &b, FUEL, &cache), Ok(()));
    assert!(kept(&cache) >= 1);
    // The same nodes again: the pair is known, so three units are enough.
    assert_eq!(types(&psi, &g, &a, &b, 3, &cache), Ok(()));
    // A table is its Ψ's. Under another, the same nodes are judged afresh.
    let declared = named_nest(false);
    assert_eq!(types(&declared, &g, &a, &b, FUEL, &cache), Err(NC));
    assert_eq!(types(&declared, &g, &a, &b, FUEL, &fresh(&declared)), Err(NC));
    // Negative control at the first Ψ: a refusal keeps nothing.
    let wrong = sum(nest_type(12, Type::Unit { level: zero() }), Type::Nat);
    let cache = fresh(&psi);
    assert_eq!(types(&psi, &g, &a, &wrong, FUEL, &cache), Err(NC));
    assert_eq!(kept(&cache), 0);
}

#[test]
fn a_judgment_that_cost_little_is_not_kept() {
    // `code := Nat`: unfolding it is all there is to do.
    let psi = GlobalCtx::new(vec![binding(Type::Ty(zero()), Level::constant(1), Some(Term::TmNat))]);
    let named = rt(glob(0));
    let cache = fresh(&psi);
    assert_eq!(types(&psi, &ctx(vec![]), &sum(el(&named), Type::Nat), &sum(Type::Nat, Type::Nat), FUEL, &cache), Ok(()));
    assert_eq!(kept(&cache), 0);
}

#[test]
fn only_closed_spellings_are_kept() {
    // `twelve := 12 : Nat`, and `Q : Nat → Ty 0` declared. Unfolding the
    // name against the numeral costs enough to be kept
    // ([`CLOSED_PAIR_WORTH`]), so that what is not kept below is not kept
    // for being open.
    let twelve = (0..12).fold(Term::Zero, |n, _| Term::Succ(rt(n)));
    let psi = GlobalCtx::new(vec![
        binding(Type::Nat, zero(), Some(twelve.clone())),
        binding(family(), Level::constant(1), None),
    ]);
    // Open: the family is a variable of Γ. The pair `P twelve`, `P 12` is
    // convertible, and it is a fact about this Γ: the same two nodes under
    // another context name another family.
    let g = ctx(vec![(family(), Level::constant(1))]);
    let p = || Term::Var(LocalVar(0));
    let (named, spelt) = (at(p(), glob(1)), at(p(), twelve.clone()));
    let cache = fresh(&psi);
    assert_eq!(types(&psi, &g, &sum(el(&named), Type::Nat), &sum(el(&spelt), Type::Nat), FUEL, &cache), Ok(()));
    assert_eq!(kept(&cache), 0);
    // Closed: the family is the global, so the pair is a fact about Ψ, and
    // it is kept whatever Γ it was met under.
    let (named, spelt) = (at(glob(0), glob(1)), at(glob(0), twelve));
    assert_eq!(types(&psi, &g, &sum(el(&named), Type::Nat), &sum(el(&spelt), Type::Nat), FUEL, &cache), Ok(()));
    assert_eq!(kept(&cache), 1);
    let empty = ctx(vec![]);
    assert_eq!(types(&psi, &empty, &sum(el(&named), Type::Nat), &sum(el(&spelt), Type::Nat), 3, &cache), Ok(()));
}

#[test]
fn two_types_kept_convertible_are_not_two_convertible_codes() {
    // `El` is not injective: `Vec(Nat; 8)` and its `Σ` chain are one type,
    // and their codes are two.
    let psi = GlobalCtx::new(vec![]);
    let g = ctx(vec![]);
    let eight = (0..8).fold(Term::Zero, |n, _| Term::Succ(rt(n)));
    let vec = rt(Term::TmVec { level: zero(), elem: rt(Term::TmNat), len: rt(eight) });
    let chain = rt(nest_code(8, Term::TmUnit { level: zero() }));
    let (a, b) = (tm_sum(&vec, Term::TmNat), tm_sum(&chain, Term::TmNat));
    // The control: with nothing kept, the codes are refused.
    assert_eq!(codes(&psi, &a, &b, &fresh(&psi)), Err(NC));
    // The types are accepted, and the pair of code nodes is kept as types:
    // three units judge it again.
    let cache = fresh(&psi);
    let (ta, tb) = (sum(el(&vec), Type::Nat), sum(el(&chain), Type::Nat));
    assert_eq!(types(&psi, &g, &ta, &tb, 3, &cache), Err(ConvError::OutOfFuel));
    assert_eq!(types(&psi, &g, &ta, &tb, FUEL, &cache), Ok(()));
    assert_eq!(types(&psi, &g, &ta, &tb, 3, &cache), Ok(()));
    // The same two nodes, met as codes under the same table.
    assert_eq!(codes(&psi, &a, &b, &cache), Err(NC));
}

#[test]
fn codes_at_a_universe_are_walked_and_kept_as_codes() {
    let psi = named_nest(true);
    let named = rt(glob(0));
    let spelt = rt(nest_code(12, Term::TmNat));
    let cache = fresh(&psi);
    assert_eq!(codes(&psi, &tm_sum(&named, Term::TmNat), &tm_sum(&spelt, Term::TmNat), &cache), Ok(()));
    assert!(kept(&cache) >= 1);
    // Negative control: another spelling under the same name.
    let other = rt(nest_code(12, Term::TmUnit { level: zero() }));
    assert_eq!(codes(&psi, &tm_sum(&named, Term::TmNat), &tm_sum(&other, Term::TmNat), &cache), Err(NC));
}
