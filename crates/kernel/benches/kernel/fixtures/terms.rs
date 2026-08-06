//! Term builders shared by the fixtures. Deliberately *parameterized by
//! size* — the difference between these and the hand-built terms in
//! `tests/` is that a benchmark needs a family, not a case.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, CtxEntry, LocalCtx, LocalVar, Term, Type};

pub fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

pub fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

pub fn c(n: u64) -> Level {
    Level::constant(n)
}

pub fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

pub fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}

/// Γ = `x₀ : Nat, …, x_{n-1} : Nat`.
pub fn nat_ctx(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: Level::Zero }).collect::<Vec<_>>()).into(),
    }
}

/// The unary numeral `Succ^n Zero`.
pub fn num(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// `Succ^k t`.
pub fn succs(k: u32, t: Term) -> Term {
    let mut t = t;
    for _ in 0..k {
        t = Term::Succ(rt(t));
    }
    t
}

/// Read a closed `Nat` term off by repeated weak-head reduction. WHNF stops
/// at each `Succ`, so this is the kernel's "run it and print the answer" —
/// and the only way to get a *number* out of a fixture cheaply enough to use
/// as a checksum.
pub fn nat_value(t: &Term, gamma: &LocalCtx, fuel: u64) -> u64 {
    use heather_kernel::reduce::whnf_term;
    let mut n = 0;
    let mut cur = t.clone();
    loop {
        match whnf_term(&cur, gamma, fuel).expect("numeral fixture exhausted fuel") {
            Term::Zero => return n,
            Term::Succ(inner) => {
                n += 1;
                cur = (*inner).clone();
            }
            // No Debug-format here: an unexpected head could be a large
            // term (CLAUDE.md's OOM rule). The shape name is enough.
            _ => panic!("numeral fixture did not reduce to a numeral"),
        }
    }
}

/// `add m n = elim_Nat^0 (_. Nat) n (x, y. su y) m` — recursion on the
/// *first* argument, so `m` sets the number of β-steps.
pub fn add(m: Term, n: Term) -> Term {
    Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(n),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(m),
    }
}

/// `mul m n = elim_Nat^0 (_. Nat) 0 (x, y. add n y) m` — `m` additions of
/// `n`, i.e. `m · n` β-steps of `add`. The one fixture whose cost is
/// quadratic *by construction*: it is what proves the scaling fit can tell
/// a quadratic from a linear apart.
pub fn mul(m: Term, n: Term) -> Term {
    Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        // Under (x = pred at 1, y = rec at 0); `n` is closed so it needs no
        // shifting.
        step: rt(add(n, v(0))),
        scrut: rt(m),
    }
}

/// A λ-chain of depth `n` over `Nat`, whose body mentions an **ambient**
/// variable (index `n` from the inside, i.e. Γ's `x₀`) as well as the
/// innermost binder. Both halves matter: the ambient reference is what a
/// shift has to renumber, and the local one is what it must leave alone.
pub fn lam_chain(n: u32) -> Term {
    let mut body = Term::App {
        fun: rt(v(n)),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
        arg: rt(succs(2, v(0))),
    };
    for _ in 0..n {
        body = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::Nat),
            body: rt(body),
        };
    }
    body
}

/// Depth of the outer λ-chain — an O(depth) probe of a substitution's
/// result, cheap next to the allocating walk that produced it, and enough to
/// catch a substitution that silently stopped descending.
pub fn lam_depth(t: &Term) -> u64 {
    let mut n = 0;
    let mut cur = t;
    while let Term::Lam { body, .. } = cur {
        n += 1;
        cur = body;
    }
    n
}

/// `Π(x₁ : Nat). … Π(x_n : Nat). Nat` — code of a type, of size linear in
/// `n`, for the code-recursor fixtures.
pub fn pi_chain(n: u32) -> Type {
    let mut t = Type::Nat;
    for _ in 0..n {
        t = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::Nat),
            cod: rty(t),
        };
    }
    t
}
