//! The head layer of a weak head value, read back as syntax
//! (issues/elab-whnf-copies-straight-continuations.md).
//!
//! [`crate::oracle::SemanticOracle::whnf_type`] decides a probe's answer in
//! the value domain. When the answer is a former *with* sub-structure (a Π,
//! a Σ, an `Id` …) the elaborator still needs it as syntax, and the
//! small-step reducer used to spell it by redoing the whole computation by
//! substitution — copying every continuation and every branch bundle at each
//! β and each `case` (on a straight stretch, an encoded `match` whose every
//! arm spells the inductive's whole encoding, copied once per step).
//!
//! This module reads the former off the value instead. Only the **top
//! layer** is a value; every child is a closure — an environment plus the
//! syntax the machine has not evaluated — and reads back as that syntax
//! with the environment substituted in, which is exactly the term the
//! reducer's weak head reduct carries there: weak head reduction never
//! enters an argument, so the reducer's children are the same syntax under
//! the same substitution. Nothing here forces, evaluates or normalises, so
//! the result is no larger than the reducer's, and it is built in one
//! substitution per closure instead of one per reduction step.
//!
//! The few values the machine computes rather than captures (a literal's
//! predecessor, an eliminator's induction hypothesis) are spelled as the
//! reducer's β spells them. Every form the readback does not know (any other
//! computed value, a binder over globals or universes) declines with `None`, and the caller spells the reduct with the reducer as
//! before. The kernel's own invariant (docs/nbe-conversion-design.md §7: no
//! value is converted back into syntax that the kernel then evaluates) is a
//! statement about the kernel, which still has no readback; this is the
//! elaborator's, and what it produces is the reducer's spelling.

use std::collections::HashMap;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
#[cfg(debug_assertions)]
use heather_kernel::reduce::Defs;
use heather_kernel::subst::{local_bound, local_bound_ty};
use heather_kernel::term::{nth, IWfSig, LocalCtx, LocalSubst, LocalVar, Numeral, SubstTail, Term, Type};
use heather_kernel::value::program::ContextProgram;
use heather_kernel::value::{Elim, Env, Head, TmClo, TyClo, VTail, VTy, Val};

/// One readback, at one Γ. Memoizes environment entries by identity, so a
/// captured value shared by many closures (a stretch's continuation, the
/// identity prefix) is read back once and its syntax shared.
pub(crate) struct Readback<'v, 'g> {
    gamma: &'g LocalCtx,
    len: u32,
    entries: HashMap<*const TmClo<'v>, Rc<Term>>,
}

impl<'v, 'g> Readback<'v, 'g> {
    pub(crate) fn new(gamma: &'g LocalCtx) -> Self {
        Self { gamma, len: gamma.entries.len() as u32, entries: HashMap::new() }
    }

    /// The type former at the head of `v`, its children as syntax; `None`
    /// when any child is not a form read back here.
    pub(crate) fn head(&mut self, v: &VTy<'v>) -> Option<Type> {
        Some(match v {
            VTy::Nat => Type::Nat,
            VTy::Ty(l) => Type::Ty(l.clone()),
            VTy::Unit { level } => Type::Unit { level: level.clone() },
            VTy::Empty { level } => Type::Empty { level: level.clone() },
            VTy::SEmpty { level } => Type::SEmpty { level: level.clone() },
            VTy::Squash { level, ty } => Type::Squash { level: level.clone(), ty: self.ty(ty, 0)? },
            VTy::Pi { dom_level, cod_level, dom, cod } => Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: self.ty(dom, 0)?,
                cod: self.ty(cod, 1)?,
            },
            VTy::Sigma { fst_level, snd_level, fst, snd } => Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: self.ty(fst, 0)?,
                snd: self.ty(snd, 1)?,
            },
            VTy::W { shape_level, pos_level, shape, pos } => Type::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: self.ty(shape, 0)?,
                pos: self.ty(pos, 1)?,
            },
            VTy::Wf { level, shape, arity } => Type::Wf {
                level: level.clone(),
                shape: self.ty(shape, 0)?,
                arity: self.tm(arity, 1)?,
            },
            VTy::Sum { lhs_level, rhs_level, lhs, rhs } => Type::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: self.ty(lhs, 0)?,
                rhs: self.ty(rhs, 0)?,
            },
            VTy::Id { level, ty, lhs, rhs } => Type::Id {
                level: level.clone(),
                ty: self.ty(ty, 0)?,
                lhs: self.tm(lhs, 0)?,
                rhs: self.tm(rhs, 0)?,
            },
            VTy::SEq { level, ty, lhs, rhs } => Type::SEq {
                level: level.clone(),
                ty: self.ty(ty, 0)?,
                lhs: self.tm(lhs, 0)?,
                rhs: self.tm(rhs, 0)?,
            },
            VTy::Vec { level, elem, len } => Type::Vec {
                level: level.clone(),
                elem: self.ty(elem, 0)?,
                len: Rc::new(self.val(len)?),
            },
            VTy::Fin { len } => Type::Fin { len: Rc::new(self.val(len)?) },
            VTy::DVec { level, len, fam } => Type::DVec {
                level: level.clone(),
                len: Rc::new(self.val(len)?),
                fam: self.ty(fam, 1)?,
            },
            VTy::IWf { sig, index } => Type::IWf {
                sig: Rc::new(IWfSig {
                    level: sig.level.clone(),
                    idx_level: sig.idx_level.clone(),
                    idx: self.ty(&sig.idx, 0)?,
                    shape: self.ty(&sig.shape, 0)?,
                    arity: self.tm(&sig.arity, 1)?,
                    out: self.tm(&sig.out, 1)?,
                    child: self.tm(&sig.child, 2)?,
                }),
                index: self.tm(index, 0)?,
            },
            VTy::UPi { .. }
            | VTy::CtxPi { .. }
            | VTy::TyPi { .. }
            | VTy::CodeTy { .. }
            | VTy::CodeTm { .. }
            | VTy::Neutral(_) => return None,
        })
    }

    /// A type closure under `k` pending local binders, as syntax over
    /// `Γ, k binders`.
    fn ty(&mut self, c: &'v TyClo<'v>, k: u32) -> Option<Rc<Type>> {
        match c {
            TyClo::Syn { env, body } => {
                let sigma = self.subst(env, local_bound_ty(body).saturating_sub(k))?;
                let body = shifted_ty(body, env);
                Some(Rc::new(under_ty(&body, k, &sigma)))
            }
            TyClo::El { level, tm } => Some(Rc::new(Type::El { level: (*level).clone(), tm: self.tm(tm, k)? })),
            TyClo::Val(v) if k == 0 => Some(Rc::new(self.head(v)?)),
            TyClo::Vec { level, elem, len } if k == 0 => Some(Rc::new(Type::Vec {
                level: (*level).clone(),
                elem: self.ty(elem, 0)?,
                len: self.tm(len, 0)?,
            })),
            _ => None,
        }
    }

    /// A term closure under `k` pending local binders.
    fn tm(&mut self, c: &'v TmClo<'v>, k: u32) -> Option<Rc<Term>> {
        match c {
            TmClo::Syn { env, body } => {
                let sigma = self.subst(env, local_bound(body).saturating_sub(k))?;
                let body = shifted_tm(body, env);
                Some(Rc::new(under_tm(&body, k, &sigma)))
            }
            TmClo::Val(v) if k == 0 => Some(Rc::new(self.val(v)?)),
            TmClo::Elim { head, elim } if k == 0 => {
                let head = self.tm(head, 0)?;
                Some(Rc::new(self.elim(head, elim)?))
            }
            _ => None,
        }
    }

    /// A captured environment entry, read back once per readback.
    fn entry(&mut self, c: &'v TmClo<'v>) -> Option<Rc<Term>> {
        let key = c as *const TmClo<'v>;
        if let Some(hit) = self.entries.get(&key) {
            return Some(Rc::clone(hit));
        }
        let out = self.tm(c, 0)?;
        self.entries.insert(key, Rc::clone(&out));
        Some(out)
    }

    /// A value the machine computed rather than captured: a local of Γ (the
    /// identity environment every query starts from), a literal's
    /// predecessor, an eliminator's induction hypothesis, and a neutral
    /// spine over those. Anything else declines.
    fn val(&mut self, v: &Val<'v>) -> Option<Term> {
        match v {
            Val::Neutral(n) if n.spine.is_empty() => match n.head {
                Head::Var(level) if level < self.len => Some(Term::Var(LocalVar(self.len - 1 - level))),
                _ => None,
            },
            Val::Zero => Some(Term::Zero),
            // A literal's predecessor: the run over `0` is the literal the
            // reducer's `nat_lit_pred` spells.
            Val::NatRun { program, tail } => {
                let count = ContextProgram::repetition_count_up_to(program, u64::MAX)?;
                match &*self.tm(tail, 0)? {
                    Term::Zero => Some(Term::NatLit(Numeral::from_u64(count))),
                    _ => None,
                }
            }
            Val::WfIh { elim, label, children } => self.wf_ih(elim, label, children),
            // An `elim_W` β's induction hypothesis, `λ y. elim_W(…; f y)`:
            // the machine builds it as a λ over the step's environment
            // (`Eval::fire_elim_w`), whose two closures are the syntax the
            // reducer's β substitutes, so it reads back as that λ.
            Val::Lam { dom_level, cod_level, dom, body } => Some(Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: self.ty(dom, 0)?,
                body: self.tm(body, 1)?,
            }),
            Val::Neutral(n) => {
                let mut out = match &n.head {
                    Head::Var(level) if *level < self.len => Term::Var(LocalVar(self.len - 1 - level)),
                    Head::Global { var, subst } => {
                        let mut terms = Vec::with_capacity(subst.terms.len());
                        for t in &subst.terms {
                            terms.push(Rc::new(self.val(t)?));
                        }
                        let tail = match subst.tail {
                            VTail::Empty(base) => SubstTail::Empty { len: self.len, base },
                            VTail::Wk(ctx_var) => SubstTail::Wk { len: self.len, ctx_var },
                        };
                        Term::GlobalTm { var: *var, subst: LocalSubst { tail, terms } }
                    }
                    _ => return None,
                };
                let mut spine: Vec<_> = n.spine.iter_rev().collect();
                spine.reverse();
                for e in spine {
                    out = self.elim(Rc::new(out), e)?;
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// A pending elimination of `head`, spelled as the reducer spells the
    /// redex it would leave there (an eliminator's induction hypothesis).
    fn elim(&mut self, head: Rc<Term>, e: &Elim<'v>) -> Option<Term> {
        Some(match e {
            Elim::App { ann: None, arg } => Term::AppAt { fun: head, arg: self.tm(arg, 0)? },
            Elim::App { ann: Some(a), arg } => Term::App {
                fun: head,
                dom_level: a.dom_level.clone(),
                cod_level: a.cod_level.clone(),
                dom: self.ty(a.dom, 0)?,
                cod: self.ty(a.cod, 1)?,
                arg: self.tm(arg, 0)?,
            },
            Elim::Fst { ann: None } => Term::FstAt { pair: head },
            Elim::Snd { ann: None } => Term::SndAt { pair: head },
            Elim::Fst { ann: Some(a) } => Term::Fst {
                fst_level: a.fst_level.clone(),
                snd_level: a.snd_level.clone(),
                fst_ty: self.ty(a.fst_ty, 0)?,
                snd_ty: self.ty(a.snd_ty, 1)?,
                pair: head,
            },
            Elim::Snd { ann: Some(a) } => Term::Snd {
                fst_level: a.fst_level.clone(),
                snd_level: a.snd_level.clone(),
                fst_ty: self.ty(a.fst_ty, 0)?,
                snd_ty: self.ty(a.snd_ty, 1)?,
                pair: head,
            },
            Elim::ElimNat { level, motive, base, step } => Term::ElimNat {
                level: level.clone(),
                motive: self.ty(motive, 1)?,
                base: self.tm(base, 0)?,
                step: self.tm(step, 2)?,
                scrut: head,
            },
            Elim::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r } => Term::Case {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                motive_level: motive_level.clone(),
                lhs: self.ty(lhs, 0)?,
                rhs: self.ty(rhs, 0)?,
                motive: self.ty(motive, 1)?,
                case_l: self.tm(case_l, 1)?,
                case_r: self.tm(case_r, 1)?,
                scrut: head,
            },
            _ => return None,
        })
    }

    /// `elim_Wf`'s induction hypothesis, which the machine holds as a value
    /// ([`Val::WfIh`]): the λ the reducer's β builds around the recursive
    /// call (`reduce.rs`, `elim_Wf (sup_f(…; a; cs))`), built here the same
    /// way from the eliminator's and the scrutinee's syntax.
    fn wf_ih(&mut self, e: &Elim<'v>, label: &'v TmClo<'v>, children: &'v TmClo<'v>) -> Option<Term> {
        let Elim::ElimWf { level, motive_level, shape, arity, motive, step, .. } = e else {
            return None;
        };
        let shape = self.ty(shape, 0)?;
        let arity = self.tm(arity, 1)?;
        let motive = self.ty(motive, 1)?;
        let step = self.tm(step, 3)?;
        let label = self.tm(label, 0)?;
        let children = self.tm(children, 0)?;
        let arity_at = arity.apply_local(&LocalSubst::id(self.gamma).extended(label));
        let wf = Type::Wf { level: level.clone(), shape: Rc::clone(&shape), arity: Rc::clone(&arity) };
        let template = Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape,
            arity,
            motive,
            step,
            scrut: Rc::new(Term::Zero),
        }
        .shift_local(1);
        let Term::ElimWf { shape: s1, arity: n1, motive: m1, step: st1, .. } = template else {
            unreachable!("shifting an elim_Wf yields an elim_Wf")
        };
        let child = nth(
            level,
            &Rc::new(wf.shift_local(1)),
            &Rc::new(arity_at.shift_local(1)),
            Rc::new(children.shift_local(1)),
            Rc::new(Term::Var(LocalVar(0))),
        );
        let rec = Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: s1,
            arity: n1,
            motive: m1,
            step: st1,
            scrut: Rc::new(child),
        };
        Some(Term::Lam {
            dom_level: Level::Zero,
            cod_level: motive_level.clone(),
            dom: Rc::new(Type::Fin { len: Rc::new(arity_at) }),
            body: Rc::new(rec),
        })
    }

    /// The substitution an environment stands for: its entries, outermost
    /// first, as terms over Γ. Only the `used` innermost entries are read
    /// back — the body's free indices reach no further (`local_bound`) —
    /// and the rest hold a placeholder the substitution never inserts: an
    /// outer entry can be a closure over most of the evaluation so far.
    fn subst(&mut self, env: &Env<'v>, used: u32) -> Option<LocalSubst> {
        let entries = env.to_vec();
        let len = entries.len();
        let unused = Rc::new(Term::Zero);
        let mut terms = Vec::with_capacity(len);
        for (p, entry) in entries.into_iter().enumerate() {
            let index = (len - 1 - p) as u32;
            terms.push(if index < used { self.entry(entry)? } else { Rc::clone(&unused) });
        }
        Some(LocalSubst { tail: LocalSubst::id(self.gamma).tail, terms })
    }
}

/// A closure body's globals, at the ambient offset (`Env::gshift`).
fn shifted_ty(body: &Rc<Type>, env: &Env<'_>) -> Rc<Type> {
    match env.gshift() {
        0 => Rc::clone(body),
        by => Rc::new(body.shift_global(by)),
    }
}

fn shifted_tm(body: &Rc<Term>, env: &Env<'_>) -> Rc<Term> {
    match env.gshift() {
        0 => Rc::clone(body),
        by => Rc::new(body.shift_global(by)),
    }
}

/// `body[σ]` with its `k` innermost variables left bound: the substitution is
/// applied through `k` placeholder binders, so the kernel's own lifting (and
/// its payload shifting) is the one used.
fn under_ty(body: &Rc<Type>, k: u32, sigma: &LocalSubst) -> Type {
    let mut wrapped = (**body).clone();
    for _ in 0..k {
        wrapped = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(wrapped),
        };
    }
    let mut out = wrapped.apply_local(sigma);
    for _ in 0..k {
        let Type::Pi { cod, .. } = out else { unreachable!("a placeholder binder survives substitution") };
        out = Rc::unwrap_or_clone(cod);
    }
    out
}

fn under_tm(body: &Rc<Term>, k: u32, sigma: &LocalSubst) -> Term {
    let mut wrapped = (**body).clone();
    for _ in 0..k {
        wrapped = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(wrapped),
        };
    }
    let mut out = wrapped.apply_local(sigma);
    for _ in 0..k {
        let Term::Lam { body, .. } = out else { unreachable!("a placeholder binder survives substitution") };
        out = Rc::unwrap_or_clone(body);
    }
    out
}

/// The debug-build check that a readback is the reducer's spelling, sampled
/// at the kernel's slow-check rate (`heather_kernel::checks`: one in
/// [`SAMPLE_EVERY`] by default, every one under `Full`). A disagreement is
/// not unsound — the kernel re-checks every term — but the elaborator
/// anchors on spellings in places (docs/nbe-conversion-design.md §7), so a
/// readback that respells is a defect here and fails loudly.
#[cfg(debug_assertions)]
pub(crate) fn verify(ty: &Type, gamma: &LocalCtx, defs: Defs<'_>, fuel: u64, read: &Type) {
    use std::cell::Cell;
    use heather_kernel::checks::{skip_verification, SkipVerification, SAMPLE_EVERY};
    thread_local! {
        static SAMPLE: Cell<u32> = const { Cell::new(0) };
    }
    let run = match skip_verification() {
        SkipVerification::Off => false,
        SkipVerification::Full => true,
        SkipVerification::Sampled => SAMPLE.with(|n| {
            let k = n.get().wrapping_add(1);
            n.set(k);
            k % SAMPLE_EVERY == 0
        }),
    };
    if !run {
        return;
    }
    if let Ok(spelled) = heather_kernel::reduce::whnf_type_delta(ty, gamma, defs, fuel) {
        assert!(
            spelled == *read,
            "readback respelled a weak head reduct\n  reducer: {spelled:?}\n  readback: {read:?}"
        );
    }
}

#[cfg(test)]
mod tests {
    use heather_kernel::eval;
    use heather_kernel::layer::Layer;
    use heather_kernel::reduce::{self, Defs};
    use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar};
    use heather_kernel::value::ValueArena;

    use super::*;

    /// `Q : Π(Nat). Ty 0 := λ n. elim_Nat(n; «Nat»; λ m ih. «Π(Nat). El ih»)`:
    /// a family computed by a `match` whose arm is a former over the arm's
    /// own binders — the induction hypothesis under the Π's binder, which
    /// the reducer spells as a pending `elim_Nat` at the predecessor.
    fn pi_world() -> GlobalCtx {
        let body = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::constant(1),
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::ElimNat {
                level: Level::constant(1),
                motive: Rc::new(Type::Ty(Level::Zero)),
                base: Rc::new(Term::TmNat),
                step: Rc::new(Term::TmPi {
                    dom_level: Level::Zero,
                    cod_level: Level::Zero,
                    dom: Rc::new(Term::TmNat),
                    // Under the Π's binder: `ih` is one further out.
                    cod: Rc::new(Term::Var(LocalVar(1))),
                }),
                scrut: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        GlobalCtx::new(vec![GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::constant(1),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Ty(Level::Zero)),
            }),
            level: Level::constant(1),
            body: Some(Rc::new(body)),
        }])
    }

    /// `Γ = x : Nat`.
    fn one_nat() -> LocalCtx {
        LocalCtx::nil().extended(Rc::new(Type::Nat), Level::Zero)
    }

    /// `El^0 (Q arg)` in `Γ = x : Nat`.
    fn q_of(arg: Term) -> Type {
        Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::App {
                fun: Rc::new(Term::GlobalTm { var: GlobalVar(0), subst: LocalSubst::id(&one_nat()) }),
                dom_level: Level::Zero,
                cod_level: Level::constant(1),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Ty(Level::Zero)),
                arg: Rc::new(arg),
            }),
        }
    }

    const FUEL: u64 = 1 << 20;

    /// The readback of a computed former is the reducer's reduct, node for
    /// node, over each kind of predecessor the machine holds differently: a
    /// literal's (a run), a local's (an identity entry) and a constructor's
    /// (captured syntax).
    #[test]
    fn a_computed_former_reads_back_as_the_reducers_reduct() {
        let world = pi_world();
        let defs = Defs::transparent(&world);
        let x = || Rc::new(Term::Var(LocalVar(0)));
        for arg in [
            Term::NatLit(3u64.into()),
            Term::Succ(x()),
            Term::Succ(Rc::new(Term::Succ(x()))),
        ] {
            let ty = q_of(arg);
            let arena = ValueArena::new();
            let value = eval::whnf_value_ty(&arena, &Rc::new(ty.clone()), &one_nat(), defs, FUEL).unwrap();
            let read = Readback::new(&one_nat()).head(&value).expect("every child is a form read back here");
            let reducer = reduce::whnf_type_delta(&ty, &one_nat(), defs, FUEL).unwrap();
            assert!(matches!(read, Type::Pi { .. }));
            assert_eq!(read, reducer);
        }
    }

    /// A family computed by recursion over a tier-2 (W-lowered) inductive:
    /// the arm's former sits in the step's environment, which holds the
    /// `elim_W` β's induction hypothesis — a λ the machine builds over that
    /// environment (`Eval::fire_elim_w`) — so the readback reads that λ back
    /// rather than declining to the reducer, and spells what the reducer
    /// spells.
    #[test]
    fn an_elim_w_induction_hypothesis_reads_back_as_the_reducers_lambda() {
        let mut el = crate::Elaborator::with_prelude().expect("prelude");
        el.elab_source(
            "inductive Tree { Leaf, Node(k: Nat -> Tree) }
             fn F(t: Tree) -> Type { match t { Leaf => Nat, Node(k) => Nat -> F(k(0)) } }
             fn probe() -> F(Node(λ n => Node(λ m => Leaf))) { λ a b => 0 }",
        )
        .expect("the declarations elaborate");
        let GlobalBinding::Tm { ty, .. } = el.psi.bindings.last().expect("a binding") else {
            panic!("a `fn` is a term binding")
        };
        // Minted against the Ψ before its own binding; re-key it into today's.
        let ty = ty.shift_global(1);
        let gamma = LocalCtx::nil();
        let defs = Defs::transparent(&el.psi);
        let arena = ValueArena::new();
        let value = eval::whnf_value_ty(&arena, &Rc::new(ty.clone()), &gamma, defs, FUEL).unwrap();
        let read = Readback::new(&gamma).head(&value).expect("the ih is a form read back here");
        let reducer = reduce::whnf_type_delta(&ty, &gamma, defs, FUEL).unwrap();
        assert!(matches!(read, Type::Pi { .. }));
        assert_eq!(read, reducer);
    }

    /// A stuck head has no former to read: the caller keeps the reducer.
    #[test]
    fn a_neutral_head_declines() {
        let world = pi_world();
        let ty = q_of(Term::Var(LocalVar(0)));
        let arena = ValueArena::new();
        let value =
            eval::whnf_value_ty(&arena, &Rc::new(ty), &one_nat(), Defs::transparent(&world), FUEL).unwrap();
        assert!(Readback::new(&one_nat()).head(&value).is_none());
    }
}
