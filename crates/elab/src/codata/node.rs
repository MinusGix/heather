//! A constructor `corec` read as a node: its children as the terms they were
//! written as, and the same constructor rebuilt with one child replaced
//! (`docs/equation-rewrite-design.md` §11.5).
//!
//! A constructor is the apomorphism's `in` (§3, and
//! docs/codata-indexed-design.md §4): its children sit at the leaves of a
//! case tree over the step's positions,
//!
//! ```text
//! corec(sig; _. Unit; _ _. ⟨ℓ, λp. kids(p)⟩; ⟨⟩; ⟨⟩)          unindexed
//! corec(sig; i. Out(i); i x. ⟨fst x, λp. inr(snd x p)⟩; j; ⟨ℓ, λp. kids(p)⟩)   indexed
//! ```
//!
//! where `kids(p)` cases down the position sum and each leaf is child `r`
//! shifted past every binder above it — `inr(t)` unindexed, `t` indexed —
//! and a function child is applied to the position's payload, the case's
//! own binder (`k(y)`). [`MParts::kids_lam`] builds exactly that shape; the
//! reader here takes it apart in either spelling (annotated or checked), and
//! anything else is not a constructor it reads.
//!
//! [`MParts::kids_lam`]: super::MParts

use std::sync::Arc as Rc;

use heather_kernel::term::{LocalVar, Term};

/// A constructor's child, scoped where the constructor is: a tree for a
/// plain child, the function itself (`k`, a λ as written) for a function
/// child.
pub(crate) struct Child {
    pub(crate) term: Rc<Term>,
    pub(crate) function: bool,
}

/// A constructor `corec` taken apart: its label (the nominal tag and the
/// payload, scoped where the constructor is) and its children, in position
/// order — the declaration's order of its child fields.
pub(crate) struct CtorNode {
    pub(crate) label: Rc<Term>,
    pub(crate) children: Vec<Child>,
}

/// `t` scoped `d` binders further out, when it mentions none of the
/// innermost `d`.
fn lowered(t: &Term, d: u32) -> Option<Term> {
    let mut cur = t.clone();
    for _ in 0..d {
        let dropped = cur.inst_top_above(0, 0, &Term::Zero);
        if dropped.shift_local(1) != cur {
            return None;
        }
        cur = dropped;
    }
    Some(cur)
}

/// Where the node's label and children function sit, and how deep the
/// children function is below the constructor's context.
fn kids_of(t: &Term) -> Option<(&Rc<Term>, &Rc<Term>, u32, bool)> {
    let Term::Corec { step, seed, .. } = t else { return None };
    // Indexed: the step is the generic `in`, `⟨fst x, λp. inr(snd x p)⟩`,
    // and the node is the seed.
    if let Some((fst, snd)) = crate::spelling::pair_of(step)
        && matches!(&**fst, Term::Fst { pair, .. } | Term::FstAt { pair } if matches!(&**pair, Term::Var(LocalVar(0))))
        && matches!(&**snd, Term::Lam { body, .. } if matches!(&**body, Term::Inr { .. } | Term::InrAt { .. }))
    {
        let (label, kids) = crate::spelling::pair_of(seed)?;
        return Some((label, kids, 0, false));
    }
    // Unindexed: the node is the step, under its two binders.
    let (label, kids) = crate::spelling::pair_of(step)?;
    Some((label, kids, 2, true))
}

/// Visit the leaves of a children function's body, `body` at depth `d` past
/// the constructor's context, in position order. `leaf(d, leaf)` is called
/// per leaf; the case tree itself is rebuilt around what it returns.
fn leaves(body: &Rc<Term>, d: u32, leaf: &mut dyn FnMut(u32, &Rc<Term>) -> Option<Rc<Term>>) -> Option<Rc<Term>> {
    match &**body {
        // No children: a function out of `Empty`.
        Term::ElimEmpty { .. } => Some(Rc::clone(body)),
        // Child `r` on the left, the rest of the sum on the right, each
        // under the case's binder; the scrutinee is the binder above.
        Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, scrut }
            if matches!(&**scrut, Term::Var(LocalVar(0))) =>
        {
            let l = leaf(d + 1, case_l)?;
            let r = leaves(case_r, d + 1, leaf)?;
            Some(Rc::new(Term::Case {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                motive_level: motive_level.clone(),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
                motive: Rc::clone(motive),
                case_l: l,
                case_r: r,
                scrut: Rc::clone(scrut),
            }))
        }
        _ => leaf(d, body),
    }
}

/// The value at a leaf: past `inr` when the node exits there (unindexed).
fn exit(leaf: &Term, exits: bool) -> Option<&Rc<Term>> {
    if !exits {
        return None;
    }
    match leaf {
        Term::Inr { val, .. } | Term::InrAt { val, .. } => Some(val),
        _ => None,
    }
}

/// A leaf's child, scoped `d` binders further out: a plain child mentions
/// none of the binders above it, a function child is applied to the
/// innermost one.
fn child_at(value: &Term, d: u32) -> Option<Child> {
    if let Some(t) = lowered(value, d) {
        return Some(Child { term: Rc::new(t), function: false });
    }
    match value {
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } if matches!(&**arg, Term::Var(LocalVar(0))) => {
            lowered(fun, d).map(|f| Child { term: Rc::new(f), function: true })
        }
        _ => None,
    }
}

impl CtorNode {
    /// `t` read as a constructor node, when it is one.
    pub(crate) fn read(t: &Term) -> Option<CtorNode> {
        let (label, kids, k, exits) = kids_of(t)?;
        let label = Rc::new(lowered(label, k)?);
        let Term::Lam { body, .. } = &**kids else { return None };
        let mut children = Vec::new();
        leaves(body, k + 1, &mut |d, leaf| {
            let value = if exits { exit(leaf, true)? } else { leaf };
            children.push(child_at(value, d)?);
            Some(Rc::clone(leaf))
        })?;
        Some(CtorNode { label, children })
    }

    /// The constructor `t` (which [`Self::read`] read) with child `r`
    /// replaced by `with`, scoped where `t` is: a tree for a plain child, a
    /// function for a function child, applied to the position as the
    /// original was.
    pub(crate) fn replaced(t: &Term, r: usize, with: &Rc<Term>) -> Option<Term> {
        let (_, kids, k, exits) = kids_of(t)?;
        let Term::Lam { dom_level, cod_level, dom, body } = &**kids else { return None };
        let mut at = 0usize;
        let body = leaves(body, k + 1, &mut |d, leaf| {
            let mine = at == r;
            at += 1;
            if !mine {
                return Some(Rc::clone(leaf));
            }
            let value = if exits { exit(leaf, true)? } else { leaf };
            let new = match child_at(value, d)?.function {
                false => Rc::new(with.shift_local(d)),
                true => match &**value {
                    Term::App { dom_level, cod_level, dom, cod, arg, .. } => Rc::new(Term::App {
                        fun: Rc::new(with.shift_local(d)),
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::clone(dom),
                        cod: Rc::clone(cod),
                        arg: Rc::clone(arg),
                    }),
                    Term::AppAt { arg, .. } => Rc::new(Term::AppAt { fun: Rc::new(with.shift_local(d)), arg: Rc::clone(arg) }),
                    _ => return None,
                },
            };
            Some(match &**leaf {
                Term::Inr { lhs_level, rhs_level, lhs, rhs, .. } if exits => Rc::new(Term::Inr {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                    val: new,
                }),
                Term::InrAt { ty, .. } if exits => Rc::new(Term::InrAt { ty: ty.clone(), val: new }),
                _ => new,
            })
        })?;
        if at <= r {
            return None;
        }
        let kids = Rc::new(Term::Lam { dom_level: dom_level.clone(), cod_level: cod_level.clone(), dom: Rc::clone(dom), body });
        let Term::Corec { sig, carrier_level, carrier, step, index, seed } = t else { unreachable!("read above") };
        let node = |pair: &Rc<Term>| -> Rc<Term> {
            Rc::new(match &**pair {
                Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, .. } => Term::Pair {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: Rc::clone(fst_ty),
                    snd_ty: Rc::clone(snd_ty),
                    fst: Rc::clone(fst),
                    snd: Rc::clone(&kids),
                },
                Term::PairAt { ty, fst, .. } => Term::PairAt { ty: ty.clone(), fst: Rc::clone(fst), snd: Rc::clone(&kids) },
                _ => unreachable!("read as a pair above"),
            })
        };
        let (step, seed) = if k == 0 { (Rc::clone(step), node(seed)) } else { (node(step), Rc::clone(seed)) };
        Some(Term::Corec {
            sig: Rc::clone(sig),
            carrier_level: carrier_level.clone(),
            carrier: Rc::clone(carrier),
            step,
            index: Rc::clone(index),
            seed,
        })
    }
}
