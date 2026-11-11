//! The range sum `MonoidRel::range(op, n, f)` (lib/std/algebra/big_operator.hthr),
//! as the arithmetic tactics read it (issues/tactics-and-big-operators.md).
//!
//! A sum is an atom to `ring`, `linarith` and `omega`, with two exceptions,
//! both its definition: at the bound zero it is the operation's unit, and at
//! a bound that is a successor as written — `Succ(m)`, `m + c` at a numeral
//! `c`, or a small numeral — it is `range(op, m, f) ∙ f(m)`. The second is
//! the step every proof by induction over a sum takes (`∑ k < n + 1, f(k)`
//! against the hypothesis about `∑ k < n, f(k)`). Both hold by conversion, so
//! a certificate stated over the unfolded form checks at the goal as
//! written. Every other law (reindexing, splitting, linearity) is a named
//! lemma, not a reading.

use heather_kernel::rc::Rc;

use heather_kernel::term::{Term, nat_lit_pred};

use crate::Elaborator;

/// The global a range sum is a call of.
const RANGE: &str = "big_operator::MonoidRel::range";

/// The largest numeral bound read term by term: `∑ k < 3, f(k)` is `f(0) +
/// f(1) + f(2)`, while past this a closed bound is as opaque as an open one,
/// so a reading never grows with the numeral.
const UNROLLED_BOUND: u64 = 16;

/// A range sum one step unfolded: `rest ∙ last`, at the operation `op`.
pub(crate) struct Peeled {
    pub(crate) op: Rc<Term>,
    pub(crate) rest: Rc<Term>,
    pub(crate) last: Rc<Term>,
}

/// `tm` read as `range(op, m, f) ∙ f(m)` when it is a range sum at a bound
/// that is a successor as written.
pub(crate) fn peel(elab: &Elaborator, tm: &Rc<Term>) -> Option<Peeled> {
    let args = crate::omega_cert::named_args(elab, tm, RANGE)?;
    // The carrier and its relation come first, then the operation, the
    // instance dictionary, and the bound and the terms.
    let [.., op, _dictionary, bound, f] = args.as_slice() else { return None };
    let pred = predecessor(elab, bound)?;
    let rest = with_bound(tm, &pred)?;
    let applied = Term::AppAt { fun: Rc::clone(f), arg: Rc::clone(&pred) };
    let last = Rc::new(crate::spelling::beta_head(&applied).unwrap_or(applied));
    Some(Peeled { op: Rc::clone(op), rest, last })
}

/// The operation of a range sum at the bound zero: the sum is that
/// operation's unit.
pub(crate) fn empty(elab: &Elaborator, tm: &Rc<Term>) -> Option<Rc<Term>> {
    let args = crate::omega_cert::named_args(elab, tm, RANGE)?;
    let [.., op, _dictionary, bound, _] = args.as_slice() else { return None };
    heather_kernel::term::is_nat_zero(bound).then(|| Rc::clone(op))
}

/// Is `op` the global `name`, unapplied?
pub(crate) fn op_is(elab: &Elaborator, op: &Term, name: &str) -> bool {
    crate::omega_cert::named_args(elab, op, name).is_some_and(|args| args.is_empty())
}

/// The predecessor of a bound that is a successor as written.
fn predecessor(elab: &Elaborator, bound: &Rc<Term>) -> Option<Rc<Term>> {
    match &**bound {
        Term::Succ(m) => return Some(Rc::clone(m)),
        Term::NatLit(n) if !n.is_zero() && n.as_u64().is_some_and(|n| n <= UNROLLED_BOUND) => {
            return Some(Rc::new(nat_lit_pred(n)));
        }
        _ => {}
    }
    // `m + c`: `Nat::add` recurses on its right operand, so `m + 1` is
    // `Succ(m)` and `m + (c + 1)` is `Succ(m + c)`.
    let args = crate::omega_cert::named_args(elab, bound, "nat::Nat::add")?;
    let [m, c] = args.as_slice() else { return None };
    let c = match &***c {
        Term::NatLit(c) if !c.is_zero() => c,
        Term::Succ(c) if matches!(&**c, Term::Zero) => return Some(Rc::clone(m)),
        _ => return None,
    };
    let pred = nat_lit_pred(c);
    if matches!(pred, Term::Zero) {
        return Some(Rc::clone(m));
    }
    with_last_arg(bound, 0, Rc::new(pred))
}

/// The range sum `tm` at the bound `bound`.
fn with_bound(tm: &Rc<Term>, bound: &Rc<Term>) -> Option<Rc<Term>> {
    with_last_arg(tm, 1, Rc::clone(bound))
}

/// `tm` with the argument `outward` places from the end of its spine
/// replaced.
fn with_last_arg(tm: &Rc<Term>, outward: usize, new: Rc<Term>) -> Option<Rc<Term>> {
    let (fun, arg) = crate::spelling::app_of(tm)?;
    if outward > 0 {
        let fun = with_last_arg(fun, outward - 1, new)?;
        return Some(Rc::new(rebuilt(tm, fun, Rc::clone(arg))));
    }
    Some(Rc::new(rebuilt(tm, Rc::clone(fun), new)))
}

fn rebuilt(tm: &Term, fun: Rc<Term>, arg: Rc<Term>) -> Term {
    match tm {
        Term::App { dom_level, cod_level, dom, cod, .. } => Term::App {
            fun,
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
            arg,
        },
        _ => Term::AppAt { fun, arg },
    }
}
