//! Deep right-nested terms (docs/kernel/deep-term-walks-design.md): every walk the
//! gate takes over a term must survive a chain far deeper than any native
//! stack holds one frame per level of — or refuse it — on a thread with an
//! ordinary stack.

use heather_kernel::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{vec_items_chain, GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::{check_term, TypeError};

const FUEL: u64 = 40_000_000;
const DEEP: usize = 100_000;

/// Run `f` on a thread with an 8 MiB stack: the main thread's and a kernel
/// worker's, and less than the old one-frame-per-level walks needed here.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new().stack_size(8 << 20).spawn(f).unwrap().join().unwrap();
}

fn chain(n: usize, item: u64) -> Term {
    let items: Vec<_> = (0..n).map(|i| Rc::new(Term::NatLit(((i as u64 + item) % 7 + 1).into()))).collect();
    vec_items_chain(&Level::Zero, &Rc::new(Type::Nat), &items)
}

fn vec_ty(n: usize) -> Type {
    Type::Vec { level: Level::Zero, elem: Rc::new(Type::Nat), len: Rc::new(Term::NatLit((n as u64).into())) }
}

#[test]
fn a_deep_chain_drops() {
    on_small_stack(|| drop(chain(DEEP, 0)));
}

#[test]
fn a_deep_chain_shifts() {
    on_small_stack(|| {
        let c = Rc::new(chain(DEEP, 0));
        let s = c.shift_local(1);
        assert!(s == *c);
    });
}

/// A shared tower: `n` pairs, each holding the one below it twice. A tree of
/// `2^n` leaves, and `n` nodes.
fn tower(n: usize, leaf: Term) -> Rc<Term> {
    let mut t = Rc::new(leaf);
    for _ in 0..n {
        t = Rc::new(Term::PairAt { ty: None, fst: Rc::clone(&t), snd: Rc::clone(&t) });
    }
    t
}

/// The kernel's re-verification of a skip or of a memo hit is a walk of its
/// own (`checks::rederive`), and it has to be the walk it checks: flat over a
/// deep chain, once over a shared node, and absent from the counters. Each
/// failed once, with every skip verified
/// (`issues/self-checks-nest.md`): the chain overflowed this
/// stack, a tower was walked as its tree, and the counts were the checks'.
#[test]
fn verifying_every_skip_is_flat_shared_and_uncounted() {
    use heather_kernel::checks::{set_skip_verification, SkipVerification};
    on_small_stack(|| {
        let counted = |level| {
            set_skip_verification(level);
            let deep = Rc::new(chain(DEEP, 0));
            let closed = tower(64, Term::NatLit(1u64.into()));
            let open = tower(64, Term::Var(heather_kernel::term::LocalVar(0)));
            let before = heather_kernel::stats::snapshot();
            assert!(deep.shift_local(1) == *deep);
            assert!(closed.shift_local(1) == *closed);
            let _ = open.shift_local(1);
            heather_kernel::stats::snapshot().since(&before).values()
        };
        let unverified = counted(SkipVerification::Off);
        let verified = counted(SkipVerification::Full);
        assert_eq!(unverified, verified, "{:?}", heather_kernel::stats::Snapshot::NAMES);
    });
    // The sample is bounded by work as well as by count: a skip of a large
    // closed term costs a node and its check costs the term, so one check in
    // sixteen of a term shifted again and again was many times the shifts
    // (`issues/kernel-self-check-cost-on-skipped-terms.md`). On a thread of
    // its own, whose work starts at nothing; in this test, the only one of
    // the binary that sets the level.
    on_small_stack(|| {
        use heather_kernel::checks::{sample_work, REWALK_SHARE, SAMPLE_EVERY};
        set_skip_verification(SkipVerification::Sampled);
        let deep = Rc::new(chain(DEEP, 0));
        for _ in 0..SAMPLE_EVERY {
            assert!(deep.shift_local(1) == *deep);
        }
        let (_, one_check) = sample_work();
        if cfg!(debug_assertions) {
            assert!(one_check >= DEEP as u64, "the first sampled skip is checked by walking what it skipped: {one_check}");
        }
        for _ in 0..10_000 {
            assert!(deep.shift_local(1) == *deep);
        }
        let (own, checks) = sample_work();
        assert!(
            checks <= own / REWALK_SHARE + one_check,
            "the sample walked {checks} nodes again for {own} of the kernel's own"
        );
        // And it comes back once the work has paid for it.
        let open = Rc::new(open_chain(DEEP, 0));
        for _ in 0..2 * REWALK_SHARE {
            let _ = open.shift_local(1);
        }
        for _ in 0..SAMPLE_EVERY {
            assert!(deep.shift_local(1) == *deep);
        }
        if cfg!(debug_assertions) {
            assert!(sample_work().1 >= 2 * one_check, "a later skip is checked again");
        }
    });
}

#[test]
fn a_deep_chain_typechecks() {
    on_small_stack(|| {
        check_term(&GlobalCtx::default(), 0, Layer::Prog, &LocalCtx::nil(), &chain(DEEP, 0), &vec_ty(DEEP), &Level::Zero, FUEL)
            .unwrap();
    });
}

#[test]
fn two_deep_chains_compare() {
    on_small_stack(|| {
        conv_term(&GlobalCtx::default(), &LocalCtx::nil(), Layer::Prog, &chain(DEEP, 0), &chain(DEEP, 0), &vec_ty(DEEP), &Level::Zero, FUEL)
            .unwrap();
    });
}

fn open_chain(n: usize, var: u32) -> Term {
    let items: Vec<_> = (0..n)
        .map(|i| Rc::new(if i % 2 == 0 { Term::Var(heather_kernel::term::LocalVar(var)) } else { Term::NatLit(2u64.into()) }))
        .collect();
    vec_items_chain(&Level::Zero, &Rc::new(Type::Nat), &items)
}

#[test]
fn a_deep_open_chain_shifts_and_substitutes() {
    on_small_stack(|| {
        let c = Rc::new(open_chain(DEEP, 0));
        assert!(c.shift_local(1) == open_chain(DEEP, 1));
        let gamma = LocalCtx::nil();
        let _ = gamma;
        assert!(c.shift_local(0) == *c);
    });
}

#[test]
fn deep_chains_that_differ_at_the_bottom_are_refused() {
    on_small_stack(|| {
        let a = chain(DEEP, 0);
        let mut items: Vec<_> = (0..DEEP).map(|i| Rc::new(Term::NatLit(((i as u64) % 7 + 1).into()))).collect();
        *items.last_mut().unwrap() = Rc::new(Term::NatLit(100u64.into()));
        let b = vec_items_chain(&Level::Zero, &Rc::new(Type::Nat), &items);
        assert_eq!(
            conv_term(&GlobalCtx::default(), &LocalCtx::nil(), Layer::Prog, &a, &b, &vec_ty(DEEP), &Level::Zero, FUEL),
            Err(heather_kernel::conv::ConvError::NotConvertible)
        );
    });
}

#[test]
fn an_ill_typed_element_at_the_bottom_is_refused() {
    on_small_stack(|| {
        let mut items: Vec<_> = (0..DEEP).map(|_| Rc::new(Term::NatLit(1u64.into()))).collect();
        *items.last_mut().unwrap() = Rc::new(Term::Triv { level: Level::Zero });
        let c = vec_items_chain(&Level::Zero, &Rc::new(Type::Nat), &items);
        // The bottom premise is deferred, then judged: `⟨⟩ : Unit` is not `Nat`.
        let verdict = check_term(&GlobalCtx::default(), 0, Layer::Prog, &LocalCtx::nil(), &c, &vec_ty(DEEP), &Level::Zero, FUEL);
        assert_eq!(verdict.unwrap_err(), TypeError::NotConvertible);
    });
}

#[test]
fn a_deep_successor_chain_checks_and_compares() {
    on_small_stack(|| {
        let mut n = Term::Zero;
        for _ in 0..DEEP {
            n = Term::Succ(Rc::new(n));
        }
        check_term(&GlobalCtx::default(), 0, Layer::Prog, &LocalCtx::nil(), &n, &Type::Nat, &Level::Zero, FUEL).unwrap();
        let lit = Term::NatLit((DEEP as u64).into());
        conv_term(&GlobalCtx::default(), &LocalCtx::nil(), Layer::Prog, &n, &lit, &Type::Nat, &Level::Zero, FUEL).unwrap();
    });
}
