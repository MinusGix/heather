//! Regression cases for issues/closed-nat-equality-depth-budget.md.
//! Build values rather than large numeral syntax: parsing/packing a literal
//! can erase the very successor chain this regression needs to exercise.

use super::*;
use crate::conv::ConvError;
use crate::reduce::NATIVE_DEPTH_LIMIT;
use crate::term::{CtxEntry, GlobalCtx};

const FUEL: u64 = 1 << 22;

fn zero<'v>(arena: &'v ValueArena<'v>) -> &'v TmClo<'v> {
    arena.tm(TmClo::val(Rc::new(Val::Zero)))
}

fn chain<'v>(
    env: &Env<'v>,
    count: u32,
    mut tail: &'v TmClo<'v>,
    delayed: bool,
) -> TmC<'v> {
    let step = Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))));
    for _ in 0..count {
        tail = if delayed {
            // Each environment binds a distinct, still-unforced predecessor.
            // This is not one syntactic numeral or one ready NatRun.
            let rho = value::Env::empty().push(env.arena, tail);
            env.arena.tm(TmClo::syn(rho, Rc::clone(&step)))
        } else {
            // Deliberately do not use the packing constructor: also pin the
            // ordinary Succ/Succ and mixed Succ/NatRun comparison paths.
            env.arena.tm(TmClo::val(Rc::new(Val::Succ(tail))))
        };
    }
    TmC::here(env, tail)
}

#[test]
fn closed_nat_equality_depth_budget_long_prefixes() {
    for (n, left_delayed, right_delayed) in [
        (1025, true, true),
        (2757, true, true),
        (20_000, true, true),
        (20_000, false, true),
        (20_000, true, false),
        (20_000, false, false),
        (50_000, true, true),
    ] {
        let psi = GlobalCtx::default();
        let gamma = LocalCtx::nil();
        let arena = ValueArena::new();
        let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
        let left = chain(&env, n, zero(&arena), left_delayed);
        let right = chain(&env, n, zero(&arena), right_delayed);
        let ty = Values::nat(&env);
        let mut cv = Conv::<Values>::new(FUEL, &psi);
        assert_eq!(cv.tm(&env, &left, &right, &ty, &Level::Zero), Ok(()),
            "n={n}, delayed={left_delayed}/{right_delayed}");
        assert_eq!(cv.depth, 0);
    }
}

#[test]
fn closed_nat_equality_depth_budget_segmented_runs() {
    let psi = GlobalCtx::default();
    let gamma = LocalCtx::nil();
    let arena = ValueArena::new();
    let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
    let program = value::program::ContextProgram::run(
        (), std::num::NonZeroU64::new(3).unwrap(),
    );
    let segmented = || {
        let mut tail = zero(&arena);
        for _ in 0..4096 {
            // Keep segment boundaries: each cancellation must continue at
            // another run rather than finishing at one compressed numeral.
            tail = arena.tm(TmClo::val(Rc::new(Val::NatRun {
                program: Rc::clone(&program), tail,
            })));
        }
        TmC::here(&env, tail)
    };
    let left = segmented();
    let ty = Values::nat(&env);
    for right in [segmented(), chain(&env, 12_288, zero(&arena), false)] {
        let mut cv = Conv::<Values>::new(FUEL, &psi);
        assert_eq!(cv.tm(&env, &left, &right, &ty, &Level::Zero), Ok(()));
        assert_eq!(cv.depth, 0);
    }
}

#[test]
fn closed_nat_equality_depth_budget_rejects_off_by_one() {
    let psi = GlobalCtx::default();
    let gamma = LocalCtx::nil();
    let arena = ValueArena::new();
    let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
    let left = chain(&env, 20_000, zero(&arena), true);
    let right = chain(&env, 20_001, zero(&arena), true);
    let ty = Values::nat(&env);
    let mut cv = Conv::<Values>::new(FUEL, &psi);
    for (a, b) in [(&left, &right), (&right, &left)] {
        assert_eq!(cv.tm(&env, a, b, &ty, &Level::Zero), Err(ConvError::NotConvertible));
        assert_eq!(cv.depth, 0);
        let key = Values::tm_memo_key(&env, a, b).unwrap();
        assert_eq!(cv.memo.get(&key), Some(&false));
    }
}

#[test]
fn closed_nat_equality_depth_budget_open_tails() {
    let psi = GlobalCtx::default();
    let mut gamma = LocalCtx::nil();
    for _ in 0..2 {
        gamma.entries.push(CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero });
    }
    let arena = ValueArena::new();
    let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
    let x = arena.tm(TmClo::val(Rc::new(Val::var(0))));
    let same_x = arena.tm(TmClo::val(Rc::new(Val::var(0))));
    let y = arena.tm(TmClo::val(Rc::new(Val::var(1))));
    let a = chain(&env, 2048, x, true);
    let equal = chain(&env, 2048, same_x, true);
    let different = chain(&env, 2048, y, true);
    let closed = chain(&env, 2048, zero(&arena), true);
    let ty = Values::nat(&env);
    let mut cv = Conv::<Values>::new(FUEL, &psi);
    assert_eq!(cv.tm(&env, &a, &equal, &ty, &Level::Zero), Ok(()));
    assert_eq!(cv.tm(&env, &a, &different, &ty, &Level::Zero), Err(ConvError::NotConvertible));
    assert_eq!(cv.tm(&env, &a, &closed, &ty, &Level::Zero), Err(ConvError::NotConvertible));
    assert_eq!(cv.depth, 0);
}

#[test]
fn closed_nat_equality_depth_budget_exhaustion_is_not_a_verdict() {
    for extra in [0, 1] {
        let psi = GlobalCtx::default();
        let gamma = LocalCtx::nil();
        let arena = ValueArena::new();
        let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
        let a = chain(&env, 4096, zero(&arena), true);
        let b = chain(&env, 4096 + extra, zero(&arena), true);
        let ty = Values::nat(&env);
        let mut cv = Conv::<Values>::new(32, &psi);
        assert_eq!(cv.tm(&env, &a, &b, &ty, &Level::Zero), Err(ConvError::OutOfFuel));
        assert_eq!(cv.depth, 0);
        assert!(cv.memo.is_empty());
        cv.fuel = FUEL;
        let expected = if extra == 0 { Ok(()) } else { Err(ConvError::NotConvertible) };
        assert_eq!(cv.tm(&env, &a, &b, &ty, &Level::Zero), expected);
        assert_eq!(cv.depth, 0);
    }
}

#[test]
fn closed_nat_equality_depth_budget_keeps_the_depth_guard() {
    let psi = GlobalCtx::default();
    let gamma = LocalCtx::nil();
    let arena = ValueArena::new();
    let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
    let a = chain(&env, 2, zero(&arena), true);
    let b = chain(&env, 2, zero(&arena), true);
    let ty = Values::nat(&env);
    let mut cv = Conv::<Values>::new(FUEL, &psi);
    cv.depth = NATIVE_DEPTH_LIMIT;
    assert_eq!(cv.tm(&env, &a, &b, &ty, &Level::Zero), Err(ConvError::OutOfFuel));
    assert_eq!(cv.depth, NATIVE_DEPTH_LIMIT);
    assert!(cv.memo.is_empty());
    cv.depth = 0;
    assert_eq!(cv.tm(&env, &a, &b, &ty, &Level::Zero), Ok(()));
    assert_eq!(cv.depth, 0);
}

#[test]
fn closed_nat_equality_depth_budget_residual_memo_and_caller_depth() {
    for extra in [0, 1] {
        let psi = GlobalCtx::default();
        let gamma = LocalCtx::nil();
        let arena = ValueArena::new();
        let env = Env::new(&arena, &psi, &gamma, crate::layer::Layer::Prog);
        let a = chain(&env, 4096, zero(&arena), true);
        let b = chain(&env, 4096 + extra, zero(&arena), true);
        let outer_a = chain(&env, 1, a.clo, false);
        let outer_b = chain(&env, 1, b.clo, false);
        let ty = Values::nat(&env);
        let expected = if extra == 0 { Ok(()) } else { Err(ConvError::NotConvertible) };
        let mut cv = Conv::<Values>::new(FUEL, &psi);
        cv.depth = 7;
        assert_eq!(cv.tm(&env, &outer_a, &outer_b, &ty, &Level::Zero), expected);
        assert_eq!(cv.depth, 7);
        // The loop must memoize its residual pairs too, after their verdict
        // exists. A hit still needs only entry fuel and no new depth slot.
        let key = Values::tm_memo_key(&env, &a, &b).unwrap();
        assert_eq!(cv.memo.get(&key), Some(&(extra == 0)));
        cv.fuel = 1;
        cv.depth = NATIVE_DEPTH_LIMIT;
        assert_eq!(cv.tm(&env, &a, &b, &ty, &Level::Zero), expected);
        assert_eq!(cv.depth, NATIVE_DEPTH_LIMIT);
        assert_eq!(cv.fuel, 0);
    }
}
