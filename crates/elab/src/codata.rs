//! Codata: a `codata` declaration lowered onto the kernel's negative `M`
//! former (docs/codata-elaborator-design.md; the former itself is
//! docs/kernel-coinduction-design.md's). The section numbers below are the
//! first document's.
//!
//! ```text
//! ⟦D⟧ = M(I := Unit; _. S; _ s. P(s); _ _ _. ⟨⟩)(⟨⟩)            §2
//! ```
//!
//! `S` is tier 1's shape (every constructor's payload under the nominal tag),
//! and `P(s)` the positions of constructor `s`'s children: a code for `Unit`
//! per plain child and for `A` per function child `A -> D`, right-nested
//! sums of those when there are several and `Empty` when there are none.
//!
//! A constructor is the apomorphism's `in` (§3): a `corec` over `Unit` whose
//! one step exits at every child, so `out` gives the written children back
//! exactly. A `match` cases on `fst(out s)` with a motive that does not depend
//! on the scrutinee (§4). A function whose result is codata and which calls
//! itself is compiled into one `corec` whose carrier is the tuple of its
//! varying parameters (§5): its body is elaborated against the *step type*,
//! and the two positions the step type has — a node and a child — are
//! recognized by [`Elaborator::corec_check`], which every checking-mode
//! elaboration passes through while a corecursive body is open.
//!
//! Scoping convention, as `infinitary.rs`'s: `k` counts the binders pushed
//! since the context [`MParts`] was read in, and every term argument is
//! already scoped at that depth.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, LocalCtx, LocalSubst, LocalVar, MSig, Term, Type, m_out_ty, m_step_ty};
use heather_syntax::{Arm, Expr, ExprKind, Span, TyKind};

use crate::gendefs::GenDef;
use crate::inductive::{FieldKind, Inductive, Spine, decoded, inject, tag_type, tag_value};
use crate::recursion::{SelfRef, surface_self_call};
use crate::spelling::checked_app;
use crate::{Alias, Cx, Elaborator, R, embed, err};

fn var(i: u32) -> Rc<Term> {
    Rc::new(Term::Var(LocalVar(i)))
}

fn app_at(fun: Rc<Term>, arg: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::AppAt { fun, arg })
}

/// Component `r` of an `nv`-tuple `t` (right-nested pairs; the value itself
/// when there is one component).
fn tuple_proj(nv: usize, r: usize, t: Term) -> Term {
    if nv == 1 {
        return t;
    }
    let mut t = t;
    for _ in 0..r {
        t = Term::SndAt { pair: Rc::new(t) };
    }
    if r + 1 < nv { Term::FstAt { pair: Rc::new(t) } } else { t }
}

/// The index of every unindexed `M`: `⟨⟩ : Unit⁰`.
fn triv() -> Rc<Term> {
    Rc::new(Term::Triv { level: Level::Zero })
}

/// A codata term in the kernel's **checked spelling**
/// (`docs/codata-named-signature-design.md` §5): an intro in a checking
/// position loses its annotation (`pair@`, `inl@`, `inr@`), a projection or
/// application whose receiver infers is spelled `fst@`/`snd@`/`app@`. The
/// lowering writes every node annotated, since that is what its readers
/// take apart; the annotations are then nearly all of the term the kernel is
/// handed, so the three entry points (constructor, `match`, corecursive
/// close) hand back this instead. `check` is whether `t` sits in a checking
/// position. Only the formers below are rewritten — their checking positions
/// are the kernel's own (`typing.rs`) — and every other node is kept whole.
fn slim(t: &Rc<Term>, check: bool) -> Rc<Term> {
    let c = |t: &Rc<Term>| slim(t, true);
    let i = |t: &Rc<Term>| slim(t, false);
    Rc::new(match &**t {
        Term::Pair { fst, snd, .. } if check => Term::PairAt { ty: None, fst: c(fst), snd: c(snd) },
        Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Term::Pair {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: slim_ty(fst_ty),
            snd_ty: slim_ty(snd_ty),
            fst: c(fst),
            snd: c(snd),
        },
        Term::Inl { val, .. } if check => Term::InlAt { ty: None, val: c(val) },
        Term::Inr { val, .. } if check => Term::InrAt { ty: None, val: c(val) },
        Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => Term::Inl {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: slim_ty(lhs),
            rhs: slim_ty(rhs),
            val: c(val),
        },
        Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => Term::Inr {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: slim_ty(lhs),
            rhs: slim_ty(rhs),
            val: c(val),
        },
        Term::PairAt { ty, fst, snd } => Term::PairAt { ty: ty.as_ref().map(slim_ty), fst: c(fst), snd: c(snd) },
        Term::InlAt { ty, val } => Term::InlAt { ty: ty.as_ref().map(slim_ty), val: c(val) },
        Term::InrAt { ty, val } => Term::InrAt { ty: ty.as_ref().map(slim_ty), val: c(val) },
        // A receiver that only checks (an intro the lowering wrote bare) keeps
        // the annotated projection, which checks it.
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } | Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
            let p = i(pair);
            match (infers(&p), matches!(&**t, Term::Fst { .. })) {
                (true, true) => Term::FstAt { pair: p },
                (true, false) => Term::SndAt { pair: p },
                (false, first) => {
                    let (fst_level, snd_level, fst_ty, snd_ty, pair) =
                        (fst_level.clone(), snd_level.clone(), slim_ty(fst_ty), slim_ty(snd_ty), c(pair));
                    if first {
                        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair }
                    } else {
                        Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair }
                    }
                }
            }
        }
        Term::FstAt { pair } => Term::FstAt { pair: i(pair) },
        Term::SndAt { pair } => Term::SndAt { pair: i(pair) },
        // A head that does not infer — a `λ` (a β-redex), or an intro written
        // bare — keeps the annotations it is checked against.
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
            let f = i(fun);
            if !matches!(&**fun, Term::Lam { .. }) && infers(&f) {
                Term::AppAt { fun: f, arg: c(arg) }
            } else {
                Term::App {
                    fun: c(fun),
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: slim_ty(dom),
                    cod: slim_ty(cod),
                    arg: c(arg),
                }
            }
        }
        Term::AppAt { fun, arg } => Term::AppAt { fun: i(fun), arg: c(arg) },
        Term::Lam { dom_level, cod_level, dom, body } => Term::Lam {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: slim_ty(dom),
            body: slim(body, check),
        },
        Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, scrut } => Term::Case {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            motive_level: motive_level.clone(),
            lhs: slim_ty(lhs),
            rhs: slim_ty(rhs),
            motive: slim_ty(motive),
            case_l: c(case_l),
            case_r: c(case_r),
            scrut: c(scrut),
        },
        Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => Term::J {
            ty_level: ty_level.clone(),
            motive_level: motive_level.clone(),
            ty: slim_ty(ty),
            lhs: c(lhs),
            motive: slim_ty(motive),
            case: c(case),
            rhs: c(rhs),
            proof: c(proof),
        },
        Term::Corec { sig, carrier_level, carrier, step, index, seed } => Term::Corec {
            sig: Rc::clone(sig),
            carrier_level: carrier_level.clone(),
            carrier: slim_ty(carrier),
            step: c(step),
            index: c(index),
            seed: c(seed),
        },
        Term::Out { sig, index, scrut } => Term::Out { sig: Rc::clone(sig), index: c(index), scrut: c(scrut) },
        Term::ElimEmpty { level, scrut_level, motive, scrut } => Term::ElimEmpty {
            level: level.clone(),
            scrut_level: scrut_level.clone(),
            motive: slim_ty(motive),
            scrut: c(scrut),
        },
        Term::Refl { level, ty, tm } => Term::Refl { level: level.clone(), ty: slim_ty(ty), tm: c(tm) },
        _ => return Rc::clone(t),
    })
}

/// Whether the kernel can infer `t`'s type, conservatively: [`slim`] only
/// drops a projection's or an application's annotations when it can.
fn infers(t: &Term) -> bool {
    match t {
        Term::Var(_) | Term::GlobalTm { .. } | Term::Triv { .. } | Term::Zero => true,
        Term::Pair { .. } | Term::Inl { .. } | Term::Inr { .. } | Term::Fst { .. } | Term::Snd { .. } => true,
        Term::App { .. } | Term::Corec { .. } | Term::Out { .. } | Term::Case { .. } | Term::J { .. } => true,
        Term::Refl { .. } | Term::ElimEmpty { .. } => true,
        Term::PairAt { ty, .. } | Term::InlAt { ty, .. } | Term::InrAt { ty, .. } => ty.is_some(),
        Term::FstAt { pair } | Term::SndAt { pair } => infers(pair),
        Term::AppAt { fun, .. } => infers(fun),
        Term::Lam { body, .. } => infers(body),
        _ => false,
    }
}

/// [`slim`] in a type's term slots, every one of which the kernel checks.
fn slim_ty(t: &Rc<Type>) -> Rc<Type> {
    let c = |t: &Rc<Term>| slim(t, true);
    Rc::new(match &**t {
        Type::Pi { dom_level, cod_level, dom, cod } => Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: slim_ty(dom),
            cod: slim_ty(cod),
        },
        Type::Sigma { fst_level, snd_level, fst, snd } => Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: slim_ty(fst),
            snd: slim_ty(snd),
        },
        Type::Sum { lhs_level, rhs_level, lhs, rhs } => Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: slim_ty(lhs),
            rhs: slim_ty(rhs),
        },
        Type::El { level, tm } => Type::El { level: level.clone(), tm: c(tm) },
        Type::Id { level, ty, lhs, rhs } => Type::Id { level: level.clone(), ty: slim_ty(ty), lhs: c(lhs), rhs: c(rhs) },
        Type::M { sig, index } => Type::M { sig: Rc::clone(sig), index: c(index) },
        _ => return Rc::clone(t),
    })
}

/// One child of a constructor, as its positions see it (§2).
/// The first corecursive call inside `e`, which is not itself one: a call
/// under a *second* constructor needs a carrier that remembers the pending
/// constructor, which this round's one-step `corec` does not build
/// (issues/codata-nested-guards.md).
fn nested_self_call(selfref: &SelfRef, e: &Expr) -> Option<Span> {
    let mut nested = None;
    crate::surface::walk_expr(e, &mut |x| {
        if nested.is_none() && surface_self_call(selfref, x).is_some() {
            nested = Some(x.span);
        }
    });
    nested
}

fn nested_guard_msg(name: &str) -> String {
    format!(
        "this call to `{name}` sits under a second constructor: a corecursive call \
         must be a *direct* child of the constructor the step returns, and nesting \
         one constructor inside another before the call is not supported yet — \
         name the inner layer as a seed state of its own instead \
         (issues/codata-nested-guards.md)"
    )
}

enum Kid {
    /// `t: D` — one position, `Unit`.
    Plain,
    /// `k: A -> D` — the domain's code, scoped over `(Γ, #tag, p₀, …,
    /// p_{j-1})`, and that `j`.
    Fn(Rc<Term>, usize),
}

/// The components of `⟦D⟧ = M(I; i. S; i s. P; i s p. o)(j)`, scoped in `g`,
/// with the index binder instantiated at `j` (`⟨⟩` for an unindexed
/// declaration, docs/codata-indexed-design.md §3 for an indexed one).
pub(crate) struct MParts {
    g: LocalCtx,
    sig: Rc<MSig>,
    /// `j`, in `g`.
    index: Rc<Term>,
    pub ls: Level,
    pub lp: Level,
    /// The family's level, `ls ⊔ lp ⊔ li` — the kernel's `family_level`.
    pub lw: Level,
    /// `S` at `j` as emitted: `El(D#mshape ā j)` for a named signature.
    pub shape: Rc<Type>,
    /// `P`, over `(g, s : S)`.
    pos: Rc<Type>,
    /// The signature inline, for the structural readers (the spine,
    /// [`Self::pos_code`]): unfolded on first use, since most reads (every
    /// checking site of a corecursive body asks for one) never need it, and
    /// unfolding moves each definition's whole body into scope.
    inline: std::cell::OnceCell<Option<Rc<MSig>>>,
    /// `o`, over `(g, s : S, p : P)`.
    next: Rc<Term>,
    /// The index type is not `Unit`.
    pub indexed: bool,
}

impl MParts {
    /// Read a lowered `⟦D⟧` back.
    pub(crate) fn read(ty: &Type, g: &LocalCtx) -> Option<MParts> {
        let ty = decoded(ty);
        let Type::M { sig, index } = &*ty else {
            return None;
        };
        let indexed = !matches!(&*decoded(&sig.idx), Type::Unit { .. });
        Some(MParts {
            g: g.clone(),
            sig: Rc::clone(sig),
            index: Rc::clone(index),
            ls: sig.level.clone(),
            lp: sig.pos_level.clone(),
            lw: sig.family_level(),
            shape: Rc::new(sig.shape_at(index)),
            pos: Rc::new(sig.pos_at(index)),
            inline: std::cell::OnceCell::new(),
            next: Rc::new(sig.next_at(index)),
            indexed,
        })
    }

    fn inline(&self, el: &Elaborator) -> Option<&Rc<MSig>> {
        self.inline.get_or_init(|| el.m_sig_inline(&self.sig, &self.g)).as_ref()
    }

    /// `S` at `j` inline, for the spine.
    pub(crate) fn shape_inline(&self, el: &Elaborator, span: Span) -> R<Type> {
        match self.inline(el) {
            Some(sig) => Ok(sig.shape_at(&self.index)),
            None => err("internal: a codata signature's named shape did not unfold", span),
        }
    }

    /// `⟦D⟧` itself — at this index — at depth `k`.
    pub(crate) fn d_at(&self, k: u32) -> Type {
        self.sig.shift_local(k).at(Rc::new(self.index.shift_local(k)))
    }

    /// The family at another index `idx`, scoped at depth `k`.
    fn d_of(&self, k: u32, idx: Rc<Term>) -> Type {
        self.sig.shift_local(k).at(idx)
    }

    /// `o(j, label, pos)`, the index of the child at `pos`, at depth `k`.
    fn next_tm(&self, k: u32, label: Rc<Term>, pos: Rc<Term>) -> Rc<Term> {
        if !self.indexed {
            return triv();
        }
        Rc::new(self.next.apply_local(&embed(&self.g, k).extended(label).extended(pos)))
    }

    /// The child at `pos`'s type, `⟦D⟧(o(j, label, pos))`, at depth `k`.
    fn child_ty(&self, k: u32, label: Rc<Term>, pos: Rc<Term>) -> Type {
        self.d_of(k, self.next_tm(k, label, pos))
    }

    fn shape_at(&self, k: u32) -> Type {
        self.shape.shift_local(k)
    }

    /// `P(label)`.
    fn pos_at(&self, k: u32, label: Rc<Term>) -> Type {
        self.pos.apply_local(&embed(&self.g, k).extended(label))
    }

    /// `Π(p : P label). ⟦D⟧(o(j, label, p))` — the children's type, as `out`
    /// hands them over.
    fn kids_ty(&self, k: u32, label: Rc<Term>) -> Type {
        Type::Pi {
            dom_level: self.lp.clone(),
            cod_level: self.lw.clone(),
            dom: Rc::new(self.pos_at(k, Rc::clone(&label))),
            cod: Rc::new(self.child_ty(k + 1, Rc::new(label.shift_local(1)), var(0))),
        }
    }

    fn lf(&self) -> Level {
        Level::join(self.lp.clone(), self.lw.clone())
    }

    /// `out`'s type, `Σ(s : S). Π(p : P s). ⟦D⟧(o(j, s, p))` (the kernel's
    /// `m_out_ty`).
    fn out_ty(&self, k: u32) -> Type {
        Type::Sigma {
            fst_level: self.ls.clone(),
            snd_level: self.lw.clone(),
            fst: Rc::new(self.shape_at(k)),
            snd: Rc::new(self.kids_ty(k + 1, var(0))),
        }
    }

    fn out(&self, k: u32, t: Rc<Term>) -> Term {
        Term::Out { sig: self.sig.shift_local(k), index: Rc::new(self.index.shift_local(k)), scrut: t }
    }

    fn out_fst(&self, k: u32, o: Rc<Term>) -> Term {
        Term::Fst {
            fst_level: self.ls.clone(),
            snd_level: self.lw.clone(),
            fst_ty: Rc::new(self.shape_at(k)),
            snd_ty: Rc::new(self.kids_ty(k + 1, var(0))),
            pair: o,
        }
    }

    fn out_snd(&self, k: u32, o: Rc<Term>) -> Term {
        Term::Snd {
            fst_level: self.ls.clone(),
            snd_level: self.lw.clone(),
            fst_ty: Rc::new(self.shape_at(k)),
            snd_ty: Rc::new(self.kids_ty(k + 1, var(0))),
            pair: o,
        }
    }

    /// The code `P(label)` decodes from at a constructor's label, with the
    /// case on the label's injection taken (`infinitary.rs`'s `pos_shown`):
    /// `π₀ + (π₁ + …)` as written by [`Elaborator::lower_instance_m`].
    /// `gamma` is the context `label` is scoped in.
    fn pos_code(&self, el: &Elaborator, k: u32, gamma: &LocalCtx, label: Rc<Term>) -> Rc<Term> {
        let inline = self.inline(el).expect("the spine was read, so the signature unfolds");
        let Type::El { tm, .. } = inline.pos_at(&self.index).apply_local(&embed(&self.g, k).extended(label)) else {
            unreachable!("the positions are `El` of a case tree")
        };
        let mut tm = tm;
        loop {
            let next = match &*tm {
                Term::Case { case_l, case_r, scrut, .. } => match crate::spelling::inj_of(scrut) {
                    Some((left, val)) => {
                        let body = if left { case_l } else { case_r };
                        body.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(val)))
                    }
                    None => break,
                },
                _ => break,
            };
            tm = Rc::new(next);
        }
        tm
    }

    /// A constructor's positions taken apart, in `gamma` (where `label` is
    /// scoped): for `m` children, the `m` component types and the `m - 1`
    /// right tails of the sum (`P(label) ≡ C₀ + (C₁ + …)`). One child's
    /// positions are the whole of `P(label)`; none is `Empty`.
    fn components(&self, el: &Elaborator, k: u32, gamma: &LocalCtx, label: Rc<Term>, m: usize) -> (Vec<Type>, Vec<Type>) {
        let dec = |tm: &Rc<Term>| decoded(&Type::El { level: self.lp.clone(), tm: Rc::clone(tm) }).into_owned();
        let mut comps = Vec::with_capacity(m);
        let mut tails = Vec::with_capacity(m.saturating_sub(1));
        let mut cur = self.pos_code(el, k, gamma, label);
        for _ in 0..m.saturating_sub(1) {
            let Term::TmSum { lhs, rhs, .. } = &*cur else {
                unreachable!("a constructor with several children has sum positions")
            };
            comps.push(dec(lhs));
            tails.push(dec(rhs));
            let next = Rc::clone(rhs);
            cur = next;
        }
        if m > 0 {
            comps.push(dec(&cur));
        }
        (comps, tails)
    }

    /// [`position`] at this declaration's position level.
    fn position(&self, comps: &[Type], tails: &[Type], k: u32, r: usize, payload: Rc<Term>) -> Rc<Term> {
        position(&self.lp, comps, tails, k, r, payload)
    }

    /// `λ(p : P label). kids(p)` at a target type over the positions: a case
    /// tree on `p` down the sum, child `r`'s value at each leaf. `value(r, d,
    /// y, pos)` is child `r` at depth `d` (past `g`), `y` the position's
    /// payload there (a function child's argument; a plain child ignores it)
    /// and `pos` the whole position. `target(d, pos)` is the children's type
    /// at depth `d` and position `pos`.
    #[allow(clippy::too_many_arguments)]
    fn kids_lam(
        &self,
        k: u32,
        label: Rc<Term>,
        comps: &[Type],
        tails: &[Type],
        target: &dyn Fn(u32, Rc<Term>) -> Type,
        tlvl: &Level,
        value: &mut dyn FnMut(usize, u32, Rc<Term>, Rc<Term>) -> R<Term>,
    ) -> R<Term> {
        let body = pos_cases(&self.lp, comps, tails, k + 1, target, tlvl, value)?;
        Ok(Term::Lam {
            dom_level: self.lp.clone(),
            cod_level: tlvl.clone(),
            dom: Rc::new(self.pos_at(k, label)),
            body: Rc::new(body),
        })
    }
}

/// `inr` over the first `r` components of a constructor's position sum,
/// around `z` (a position into the `r`-th tail): the whole position. `comps`
/// and `tails` are scoped at depth 0, the result at depth `k`.
fn wrap_inr(lp: &Level, comps: &[Type], tails: &[Type], k: u32, r: usize, z: Rc<Term>) -> Rc<Term> {
    let mut t = z;
    for j in (0..r).rev() {
        t = Rc::new(Term::Inr {
            lhs_level: lp.clone(),
            rhs_level: lp.clone(),
            lhs: Rc::new(comps[j].shift_local(k)),
            rhs: Rc::new(tails[j].shift_local(k)),
            val: t,
        });
    }
    t
}

/// Child `r` of `m`'s position at `payload` (the `⟨⟩` of a plain child or
/// the argument of a function child): `inr^r(inl(payload))`, or
/// `inr^{m-1}(payload)` for the last. `comps`/`tails` are
/// [`MParts::components`]', scoped at depth 0, the result at depth `k`.
fn position(lp: &Level, comps: &[Type], tails: &[Type], k: u32, r: usize, payload: Rc<Term>) -> Rc<Term> {
    let m = comps.len();
    let mut t = payload;
    if r + 1 < m {
        t = Rc::new(Term::Inl {
            lhs_level: lp.clone(),
            rhs_level: lp.clone(),
            lhs: Rc::new(comps[r].shift_local(k)),
            rhs: Rc::new(tails[r].shift_local(k)),
            val: t,
        });
    }
    wrap_inr(lp, comps, tails, k, r, t)
}

/// The case tree down a position sum, the position binder `Var(0)` at depth
/// `d0` (past the depth `comps` and `tails` are scoped at):
/// [`MParts::kids_lam`]'s body, and the child index's (§3 of
/// docs/codata-indexed-design.md).
#[allow(clippy::too_many_arguments)]
fn pos_cases(
    lp: &Level,
    comps: &[Type],
    tails: &[Type],
    d0: u32,
    target: &dyn Fn(u32, Rc<Term>) -> Type,
    tlvl: &Level,
    value: &mut dyn FnMut(usize, u32, Rc<Term>, Rc<Term>) -> R<Term>,
) -> R<Term> {
    let m = comps.len();
    // Level `r`: `scrut` (at depth `d`) is a position into the `r`-th tail.
    #[allow(clippy::too_many_arguments)]
    fn down(
        lp: &Level,
        comps: &[Type],
        tails: &[Type],
        target: &dyn Fn(u32, Rc<Term>) -> Type,
        tlvl: &Level,
        value: &mut dyn FnMut(usize, u32, Rc<Term>, Rc<Term>) -> R<Term>,
        r: usize,
        d: u32,
        scrut: Rc<Term>,
    ) -> R<Term> {
        let m = comps.len();
        if r + 1 == m {
            let pos = wrap_inr(lp, comps, tails, d, r, Rc::clone(&scrut));
            return value(r, d, scrut, pos);
        }
        let y = var(0);
        let pos_l = position(lp, comps, tails, d + 1, r, Rc::clone(&y));
        let case_l = value(r, d + 1, y, pos_l)?;
        let case_r = down(lp, comps, tails, target, tlvl, value, r + 1, d + 1, var(0))?;
        Ok(Term::Case {
            lhs_level: lp.clone(),
            rhs_level: lp.clone(),
            motive_level: tlvl.clone(),
            lhs: Rc::new(comps[r].shift_local(d)),
            rhs: Rc::new(tails[r].shift_local(d)),
            motive: Rc::new(target(d + 1, wrap_inr(lp, comps, tails, d + 1, r, var(0)))),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }
    if m == 0 {
        return Ok(Term::ElimEmpty {
            level: tlvl.clone(),
            scrut_level: lp.clone(),
            motive: Rc::new(target(d0 + 1, var(0))),
            scrut: var(0),
        });
    }
    down(lp, comps, tails, target, tlvl, value, 0, d0, var(0))
}

/// A child's value, as [`MParts::kids_lam`]'s leaves need it.
enum KidVal {
    /// Already at the children's type, scoped at depth `k`.
    Tm(Rc<Term>),
    /// A function into the children's type, `Π(y : A). T`, scoped at `k`.
    Fn(Rc<Term>, Rc<Type>),
}

/// A `corec` carrier as a family `X(i)` over `(g, i)`. An unindexed carrier
/// is a constant family (the type weakened past `i`).
#[derive(Clone)]
struct Carrier {
    fam: Type,
    level: Level,
}

impl Carrier {
    /// `X(idx)`, for `idx` at depth `d` past `g`.
    fn at(&self, d: u32, idx: &Term) -> Type {
        self.fam.inst_top(d, idx)
    }

    /// The family over `(g, Δ, i)` with `|Δ| = by`.
    fn under(&self, by: u32) -> Carrier {
        Carrier { fam: self.fam.shift_local_above(by, 1), level: self.level.clone() }
    }
}

/// A corecursive definition in progress (§5): what [`Elaborator::corec_check`]
/// recognizes and what a corecursive call's seed is built against. Every type
/// is scoped at `depth`, the body's own context (the declaration's whole
/// telescope).
pub(crate) struct CorecSite {
    pub(crate) selfref: Rc<SelfRef>,
    depth: usize,
    ind: Rc<Inductive>,
    /// `⟦D⟧(g)`, the result type (`g = ⟨⟩` unindexed).
    d_ty: Type,
    /// The varying parameters' tuple `V`.
    vtuple: Type,
    vtuple_level: Level,
    /// The carrier: `V` unindexed, `Σ(v : V). Id(I; g[v]; i)` indexed
    /// (docs/codata-indexed-design.md §6).
    carrier: Carrier,
    /// `Σ(s : S). Π(p : P s). X(o) + ⟦D⟧(o)` at `g` — a node.
    step_ty: Type,
    step_level: Level,
    /// `X(o) + ⟦D⟧(o)`'s level — a child.
    child_level: Level,
    /// Per parameter (after the type parameters): `None` when it is passed
    /// unchanged by every corecursive call (it stays an outer binder),
    /// `Some(r)` when it is the carrier's `r`-th component.
    rank: Vec<Option<usize>>,
    /// Each parameter's name, for diagnostics.
    names: Vec<String>,
}

impl CorecSite {
    fn by(&self, cx: &Cx) -> u32 {
        (cx.names.len() - self.depth) as u32
    }

    fn varying(&self) -> usize {
        self.rank.iter().filter(|r| r.is_some()).count()
    }
}

impl Elaborator {
    // -- the type (§2) ------------------------------------------------------

    /// `⟦D<args>⟧` for a `codata` declaration (§2), at `index` when it is
    /// indexed (docs/codata-indexed-design.md §3; `index` scoped in `cx`).
    pub(crate) fn lower_instance_m(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        index: Option<Term>,
        span: Span,
    ) -> R<(Type, Level)> {
        let n = ind.ctors.len();
        let indexed = !ind.co_index.is_empty();
        let index = match (indexed, index) {
            (false, _) => None,
            (true, Some(j)) => Some(j),
            (true, None) => {
                return err(
                    format!(
                        "`{}` is an indexed family and needs its index: write `{}{}(…)`",
                        ind.name,
                        ind.name,
                        if ind.params.is_empty() { "" } else { "<…>" }
                    ),
                    span,
                );
            }
        };
        // A declaration that named its signature is spelled with it (§2 of
        // docs/codata-named-signature-design.md): nothing below is elaborated.
        if let Some(sig) = self.m_sig_named(cx, ind, args, vargs, span)? {
            let lw = sig.family_level();
            return Ok((sig.at(index.map(Rc::new).unwrap_or_else(triv)), lw));
        }
        // The base every piece is scoped over: `Γ` unindexed, `(Γ, i)` indexed,
        // where the index binders are aliases of `i`'s projections.
        let (bcx, ity, args_b, vargs_b, extra) = if indexed {
            let (ity, li) = self.codata_index_ty(cx, ind, args, vargs, span)?;
            let mut icx = cx.clone();
            icx.push("#i".into(), ity.clone(), li.clone());
            let extra = self.index_aliases(ind, &ity, &li, icx.names.len());
            let args_b: Vec<(Type, Level)> = args.iter().map(|(t, l)| (t.shift_local(1), l.clone())).collect();
            let vargs_b: Vec<(Term, Type, Level)> =
                vargs.iter().map(|(t, ty, l)| (t.shift_local(1), ty.shift_local(1), l.clone())).collect();
            (icx, Some((ity, li)), args_b, vargs_b, extra)
        } else {
            (cx.clone(), None, args.to_vec(), vargs.to_vec(), Vec::new())
        };
        let mut parts = Vec::with_capacity(n);
        let mut all_doms = Vec::with_capacity(n);
        for i in 0..n {
            let (t, l, doms) = self.lower_ctor_with_domains_at(&bcx, ind, i, &args_b, &vargs_b, &extra, span)?;
            parts.push((t, l));
            all_doms.push(doms);
        }
        let (shape, ls) = match parts.pop() {
            None => (Type::Empty { level: Level::Zero }, Level::Zero),
            Some((mut acc, mut acc_lvl)) => {
                for (ty, lvl) in parts.into_iter().rev() {
                    acc = Type::Sum { lhs_level: lvl.clone(), rhs_level: acc_lvl.clone(), lhs: Rc::new(ty), rhs: Rc::new(acc) };
                    acc_lvl = Level::max(lvl, acc_lvl).normalize().canonical();
                }
                (acc, acc_lvl)
            }
        };
        let mut kids: Vec<Vec<Kid>> = Vec::with_capacity(n);
        let mut lp: Option<(Level, String)> = None;
        for (ctor, doms) in ind.ctors.iter().zip(all_doms) {
            let mut doms = doms.into_iter();
            let mut row = Vec::new();
            for kind in &ctor.kind {
                match kind {
                    FieldKind::Plain => row.push(Kid::Plain),
                    FieldKind::FnChild => {
                        let Some((a, la, j)) = doms.next() else {
                            return err("internal: a function field lowered no domain", span);
                        };
                        let Some(code) = crate::code::code_of(&a) else {
                            return err(
                                format!(
                                    "the domain of a function field of `{}` has no code, so `{}` \
                                     cannot index its children by it (docs/codata-elaborator-design.md §2)",
                                    ctor.name, ind.name
                                ),
                                span,
                            );
                        };
                        match &lp {
                            Some((l, first)) if !l.equiv(&la) => {
                                return err(
                                    format!(
                                        "the function fields of `{first}` and `{}` have domains at \
                                         different universe levels; `{}` needs one level for all of \
                                         them (docs/codata-elaborator-design.md §2)",
                                        ctor.name, ind.name
                                    ),
                                    span,
                                );
                            }
                            Some(_) => {}
                            None => lp = Some((la, ctor.name.clone())),
                        }
                        row.push(Kid::Fn(Rc::new(code), j));
                    }
                    _ => {}
                }
            }
            kids.push(row);
        }
        let lp = lp.map(|(l, _)| l).unwrap_or(Level::Zero);
        let spine = self.spine(&shape, &ls, n, span)?;
        let tag = Rc::new(tag_value(&tag_type(ind.tag)));
        // A branch's position codes, at its depth `d` past the base.
        let codes_at = |bcx2: &Cx, i: usize, d: u32, value: &Rc<Term>| -> R<Vec<Term>> {
            let mut codes = Vec::with_capacity(kids[i].len());
            for kid in &kids[i] {
                codes.push(match kid {
                    Kid::Plain => Term::TmUnit { level: lp.clone() },
                    Kid::Fn(code, j) => {
                        // The domain's binders are the tag and the payload
                        // fields before it; here they are the branch value's
                        // projections (the tag by its canonical inhabitant).
                        let ctor_ty = spine.ctors[i].0.shift_local(d);
                        let mut subst = embed(&bcx.gamma, d).extended(Rc::clone(&tag));
                        for m in 0..*j {
                            let (proj, _, _) = self.projection(bcx2, &ctor_ty, value, m, span)?;
                            subst = subst.extended(proj);
                        }
                        code.apply_local(&subst)
                    }
                });
            }
            Ok(codes)
        };
        let sum_codes = |mut codes: Vec<Term>| -> Term {
            let Some(mut acc) = codes.pop() else {
                return Term::TmEmpty { level: lp.clone() };
            };
            while let Some(c) = codes.pop() {
                acc = Term::TmSum { lhs_level: lp.clone(), rhs_level: lp.clone(), lhs: Rc::new(c), rhs: Rc::new(acc) };
            }
            acc
        };
        // P over (base, x : S): a constant-motive case tree into `Ty lp`.
        let mut xcx = self.field_scope_cx(&bcx, ind, &args_b, &vargs_b);
        xcx.aliases.extend(extra.iter().cloned());
        xcx.push("#x".into(), shape.clone(), ls.clone());
        let ptree = if n == 0 {
            // No constructors: `S` is `Empty`, and so are the positions.
            Term::ElimEmpty {
                level: Level::succ(lp.clone()),
                scrut_level: ls.clone(),
                motive: Rc::new(Type::Ty(lp.clone())),
                scrut: var(0),
            }
        } else {
            self.w_case_tree(
                &xcx,
                &spine,
                n,
                0,
                Type::Ty(lp.clone()),
                &Level::succ(lp.clone()),
                var(0),
                1,
                &mut |bcx2, i, d, value| Ok(sum_codes(codes_at(bcx2, i, d, &value)?)),
            )?
        };
        let pos = Type::El { level: lp.clone(), tm: Rc::new(ptree) };
        let Some((ity, li)) = ity else {
            // Unindexed: the index binder `i : Unit` goes under everything:
            // the shape binds it, the positions bind `i, s`, the child index
            // `i, s, p`.
            let sig = Rc::new(MSig {
                level: ls,
                pos_level: lp,
                idx_level: Level::Zero,
                idx: Rc::new(Type::Unit { level: Level::Zero }),
                shape: Rc::new(shape.shift_local(1)),
                pos: Rc::new(pos.shift_local_above(1, 1)),
                next: triv(),
            });
            let lw = sig.family_level();
            return Ok((sig.at(triv()), lw));
        };
        // o over (Γ, i, x : S, p : P(i, x)): a case on the label into
        // `Π(p : P(i, z)). I`, applied to `p` (docs/codata-indexed-design.md §3).
        let next = if n == 0 {
            Term::ElimEmpty {
                level: li.clone(),
                scrut_level: ls.clone(),
                motive: Rc::new(ity.shift_local(4)),
                scrut: var(1),
            }
        } else {
            let motive = Type::Pi {
                dom_level: lp.clone(),
                cod_level: li.clone(),
                dom: Rc::new(pos.shift_local_above(1, 1)),
                cod: Rc::new(ity.shift_local(4)),
            };
            let tree = self.w_case_tree(
                &xcx,
                &spine,
                n,
                0,
                motive,
                &Level::join(lp.clone(), li.clone()),
                var(0),
                1,
                &mut |bcx2, i, d, value| {
                    let codes = codes_at(bcx2, i, d, &value)?;
                    let el = |tm: Term| decoded(&Type::El { level: lp.clone(), tm: Rc::new(tm) }).into_owned();
                    let m = codes.len();
                    let comps: Vec<Type> = codes.iter().cloned().map(el).collect();
                    let tails: Vec<Type> = (1..m).map(|r| el(sum_codes(codes[r..].to_vec()))).collect();
                    // `comps`/`tails` are scoped at `bcx2`, which is depth `d`
                    // past the base; `pos_cases` counts from there.
                    let base_len = bcx2.names.len();
                    let mut lam_cx = bcx2.clone();
                    lam_cx.push("#p".into(), el(sum_codes(codes.clone())), lp.clone());
                    let body = pos_cases(
                        &lp,
                        &comps,
                        &tails,
                        1,
                        &|dd, _| ity.shift_local(d + dd + 1),
                        &li,
                        &mut |r, dd, y, _| {
                            self.child_index_at(&lam_cx, ind, i, r, &spine, &value, d, dd, &comps, &tails, y, &ity, &li, &lp, base_len, span)
                        },
                    )?;
                    Ok(Term::Lam {
                        dom_level: lp.clone(),
                        cod_level: li.clone(),
                        dom: Rc::new(el(sum_codes(codes))),
                        body: Rc::new(body),
                    })
                },
            )?;
            Term::AppAt { fun: Rc::new(tree.shift_local(1)), arg: var(0) }
        };
        let sig = Rc::new(MSig {
            level: ls,
            pos_level: lp,
            idx_level: li,
            idx: Rc::new(ity),
            shape: Rc::new(shape),
            pos: Rc::new(pos),
            next: Rc::new(next),
        });
        let lw = sig.family_level();
        Ok((sig.at(Rc::new(index.expect("indexed"))), lw))
    }

    // -- the named signature (docs/codata-named-signature-design.md) -----------

    /// `D#mshape`, `D#mpos` and (indexed) `D#mnext` at declaration time: the
    /// inline signature [`Self::lower_instance_m`] builds over
    /// [`Self::tycode_fn_telescope`]'s all-`Ty 0` telescope, abstracted over
    /// it and the index binder. From then on every instance at that profile
    /// is spelled with them (§2). Best-effort like every generated
    /// definition: a refusal leaves the declaration inline.
    pub(crate) fn register_m_sig(&mut self, ind: &Rc<Inductive>, span: Span) {
        if self.types.gdefs().abs_for(&GenDef::MShape(ind.tag)).is_some() {
            return;
        }
        let Some((cx, binders, targs, vargs)) = self.tycode_fn_telescope(ind, span) else {
            return;
        };
        let indexed = !ind.co_index.is_empty();
        let (ity, li) = if indexed {
            match self.codata_index_ty(&cx, ind, &targs, &vargs, span) {
                Ok(i) => i,
                Err(_) => return,
            }
        } else {
            (Type::Unit { level: Level::Zero }, Level::Zero)
        };
        let Ok((d_ty, _)) = self.lower_instance_m(&cx, ind, &targs, &vargs, indexed.then(|| Term::Triv { level: Level::Zero }), span) else {
            return;
        };
        let Type::M { sig, .. } = d_ty else {
            return;
        };
        let (ls, lp) = (sig.level.clone(), sig.pos_level.clone());
        let tel = self.emitted_tel(&binders);
        let n = tel.len() as u32;
        let tel_vars: Vec<Rc<Term>> = (0..n).map(|k| var(n - 1 - k)).collect();
        let mut icx = cx.clone();
        icx.push("#i".into(), ity.clone(), li.clone());
        // The shape in the emission spelling, so that what one δ exposes
        // already names the declarations its fields mention.
        let shape_q = self.annotation_type(&icx, &sig.shape, 0);
        let Some(shape_code) = crate::code::code_of(&shape_q) else {
            return;
        };
        let ity = Rc::new(ity);
        let ty_ls = Type::Ty(ls.clone());
        let shape_stmt = Type::Pi { dom_level: li.clone(), cod_level: Level::succ(ls.clone()), dom: Rc::clone(&ity), cod: Rc::new(ty_ls) };
        let shape_body = Term::Lam { dom_level: li.clone(), cod_level: Level::succ(ls.clone()), dom: Rc::clone(&ity), body: Rc::new(shape_code) };
        let lvl1 = Level::max(li.clone(), Level::succ(ls.clone())).normalize().canonical();
        if !self.push_m_def(GenDef::MShape(ind.tag), ind, &tel, shape_stmt, lvl1, shape_body, span) {
            return;
        }
        // `El(D#mshape ā i)` over `(tel, i)`.
        let Some(s_ref) = self.m_ref_app(&cx, GenDef::MShape(ind.tag), &tel_vars, 1) else {
            return;
        };
        let s_ty = Rc::new(Type::El { level: ls.clone(), tm: s_ref });
        // Every push moves the globals the pieces built before it mention one
        // further out (`ty_code_fn_at`'s frame rule), so each later piece is
        // read past the pushes made since: one for the positions, two for the
        // child index.
        let Type::El { tm: ptree, .. } = &*sig.pos else {
            return;
        };
        let tel1: Vec<(Type, Level)> = tel.iter().map(|(t, l)| (t.shift_global(1), l.clone())).collect();
        let ity1 = Rc::new(ity.shift_global(1));
        let pos_cod = Type::Pi { dom_level: ls.clone(), cod_level: Level::succ(lp.clone()), dom: Rc::clone(&s_ty), cod: Rc::new(Type::Ty(lp.clone())) };
        let lvl_s = Level::max(ls.clone(), Level::succ(lp.clone())).normalize().canonical();
        let pos_stmt = Type::Pi { dom_level: li.clone(), cod_level: lvl_s.clone(), dom: Rc::clone(&ity1), cod: Rc::new(pos_cod) };
        let pos_body = Term::Lam {
            dom_level: li.clone(),
            cod_level: lvl_s.clone(),
            dom: Rc::clone(&ity1),
            body: Rc::new(Term::Lam { dom_level: ls.clone(), cod_level: Level::succ(lp.clone()), dom: Rc::clone(&s_ty), body: Rc::new(ptree.shift_global(1)) }),
        };
        let lvl2 = Level::max(li.clone(), lvl_s).normalize().canonical();
        if !self.push_m_def(GenDef::MPos(ind.tag), ind, &tel1, pos_stmt, lvl2, pos_body, span) || !indexed {
            return;
        }
        // `El(D#mshape ā i)` and `El(D#mpos ā i s)` over `(tel, i)` and `(tel,
        // i, s)`, both minted now.
        let (Some(s_ref), Some(p_ref)) = (
            self.m_ref_app(&cx, GenDef::MShape(ind.tag), &tel_vars, 1),
            self.m_ref_app(&cx, GenDef::MPos(ind.tag), &tel_vars, 2),
        ) else {
            return;
        };
        let s_ty = Rc::new(Type::El { level: ls.clone(), tm: s_ref });
        let p_ty = Rc::new(Type::El { level: lp.clone(), tm: p_ref });
        let tel2: Vec<(Type, Level)> = tel.iter().map(|(t, l)| (t.shift_global(2), l.clone())).collect();
        let ity2 = Rc::new(ity.shift_global(2));
        let i3 = Rc::new(ity2.shift_local(3));
        let next_p = Type::Pi { dom_level: lp.clone(), cod_level: li.clone(), dom: Rc::clone(&p_ty), cod: Rc::clone(&i3) };
        let lvl_p = Level::max(lp.clone(), li.clone()).normalize().canonical();
        let next_s = Type::Pi { dom_level: ls.clone(), cod_level: lvl_p.clone(), dom: Rc::clone(&s_ty), cod: Rc::new(next_p) };
        let lvl_sp = Level::max(ls.clone(), lvl_p.clone()).normalize().canonical();
        let next_stmt = Type::Pi { dom_level: li.clone(), cod_level: lvl_sp.clone(), dom: Rc::clone(&ity2), cod: Rc::new(next_s) };
        let next_body = Term::Lam {
            dom_level: li.clone(),
            cod_level: lvl_sp.clone(),
            dom: Rc::clone(&ity2),
            body: Rc::new(Term::Lam {
                dom_level: ls.clone(),
                cod_level: lvl_p.clone(),
                dom: Rc::clone(&s_ty),
                body: Rc::new(Term::Lam { dom_level: lp.clone(), cod_level: li.clone(), dom: p_ty, body: Rc::new(sig.next.shift_global(2)) }),
            }),
        };
        let lvl3 = Level::max(li, lvl_sp).normalize().canonical();
        let _ = self.push_m_def(GenDef::MNext(ind.tag), ind, &tel2, next_stmt, lvl3, next_body, span);
    }

    /// Close `ty`/`body` (scoped over the telescope) over it and push the
    /// definition; whether it was pushed.
    #[allow(clippy::too_many_arguments)]
    fn push_m_def(&mut self, key: GenDef, ind: &Inductive, tel: &[(Type, Level)], ty: Type, level: Level, body: Term, span: Span) -> bool {
        let (mut ty, mut level, mut body) = (ty, level, body);
        for (dom, dom_level) in tel.iter().rev() {
            body = Term::Lam { dom_level: dom_level.clone(), cod_level: level.clone(), dom: Rc::new(dom.clone()), body: Rc::new(body) };
            ty = Type::Pi { dom_level: dom_level.clone(), cod_level: level.clone(), dom: Rc::new(dom.clone()), cod: Rc::new(ty) };
            level = Level::max(dom_level.clone(), level).normalize().canonical();
        }
        self.push_gen_def(key, &ind.name, ty, level, body, span).is_ok()
    }

    /// The result universe of a registered code function's statement, past its
    /// first `n` binders.
    fn gen_stmt_level(&self, key: GenDef, n: usize) -> Option<Level> {
        let abs = *self.types.gdefs().abs_for(&key)?;
        let GlobalBinding::Tm { ty, .. } = self.psi.bindings.get(abs as usize)? else {
            return None;
        };
        let mut cod: &Type = ty;
        for _ in 0..n {
            let Type::Pi { cod: next, .. } = cod else {
                return None;
            };
            cod = next;
        }
        match cod {
            Type::Ty(l) => Some(l.clone()),
            _ => None,
        }
    }

    /// `app(key^δ; tel, x₁, …, x_k)` `k` binders past `cx`, the binders
    /// applied in order (`tel` is scoped in `cx`).
    fn m_ref_app(&self, cx: &Cx, key: GenDef, tel: &[Rc<Term>], k: u32) -> Option<Rc<Term>> {
        let mut t = Rc::new(self.gen_ref_deeper(cx, key, k)?);
        for a in tel {
            t = app_at(t, Rc::new(a.shift_local(k)));
        }
        for v in (0..k).rev() {
            t = app_at(t, var(v));
        }
        Some(t)
    }

    /// The named signature of an instance (§2): `None` when the declaration
    /// registered none, or the instance is not at the registered profile
    /// (every type argument at `Ty 0`), or a type argument has no code —
    /// [`Self::lower_instance_m`] then spells it inline.
    fn m_sig_named(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<Option<Rc<MSig>>> {
        let shape_key = GenDef::MShape(ind.tag);
        if self.types.gdefs().abs_for(&shape_key).is_none() || args.iter().any(|(_, l)| !l.equiv(&Level::Zero)) {
            return Ok(None);
        }
        let mut tel = Vec::with_capacity(args.len() + vargs.len());
        for (a, _) in args {
            let Some(c) = crate::code::code_of(a) else {
                return Ok(None);
            };
            tel.push(Rc::new(c));
        }
        tel.extend(vargs.iter().map(|(v, _, _)| Rc::new(v.clone())));
        let n = tel.len();
        let indexed = !ind.co_index.is_empty();
        let (Some(ls), Some(lp)) =
            (self.gen_stmt_level(shape_key, n + 1), self.gen_stmt_level(GenDef::MPos(ind.tag), n + 2))
        else {
            return Ok(None);
        };
        let (Some(shape), Some(pos)) =
            (self.m_ref_app(cx, shape_key, &tel, 1), self.m_ref_app(cx, GenDef::MPos(ind.tag), &tel, 2))
        else {
            return Ok(None);
        };
        let (ity, li, next) = if indexed {
            let Some(next) = self.m_ref_app(cx, GenDef::MNext(ind.tag), &tel, 3) else {
                return Ok(None);
            };
            let (ity, li) = self.codata_index_ty(cx, ind, args, vargs, span)?;
            (ity, li, next)
        } else {
            (Type::Unit { level: Level::Zero }, Level::Zero, triv())
        };
        Ok(Some(Rc::new(MSig {
            level: ls.clone(),
            pos_level: lp.clone(),
            idx_level: li,
            idx: Rc::new(ity),
            shape: Rc::new(Type::El { level: ls, tm: shape }),
            pos: Rc::new(Type::El { level: lp, tm: pos }),
            next,
        })))
    }

    /// A signature with its named components unfolded (§3), the signature
    /// itself when it is inline. `g` is the context the signature is scoped
    /// in. `None` only for a named signature whose definitions do not unfold,
    /// which no lowering writes.
    pub(crate) fn m_sig_inline(&self, sig: &Rc<MSig>, g: &LocalCtx) -> Option<Rc<MSig>> {
        let Type::El { tm, .. } = &*sig.shape else {
            return Some(Rc::clone(sig));
        };
        let Some((GenDef::MShape(tag), args)) = self.gen_app_of(tm) else {
            return Some(Rc::clone(sig));
        };
        let len = g.entries.len() as u32;
        let shape = self.unfold_gen_app(GenDef::MShape(tag), &args, len + 1, g.base)?;
        let Type::El { tm: ptm, .. } = &*sig.pos else {
            return None;
        };
        let (_, pargs) = self.gen_app_of(ptm)?;
        let pos = self.unfold_gen_app(GenDef::MPos(tag), &pargs, len + 2, g.base)?;
        let next = match self.gen_app_of(&sig.next) {
            Some((GenDef::MNext(t), nargs)) if t == tag => {
                Rc::new(self.unfold_gen_app(GenDef::MNext(tag), &nargs, len + 3, g.base)?)
            }
            _ => Rc::clone(&sig.next),
        };
        Some(Rc::new(MSig {
            level: sig.level.clone(),
            pos_level: sig.pos_level.clone(),
            idx_level: sig.idx_level.clone(),
            idx: Rc::clone(&sig.idx),
            shape: Rc::new(Type::El { level: sig.level.clone(), tm: Rc::new(shape) }),
            pos: Rc::new(Type::El { level: sig.pos_level.clone(), tm: Rc::new(pos) }),
            next,
        }))
    }

    /// The declaration a named signature belongs to, by its shape's head.
    pub(crate) fn m_sig_tag(&self, sig: &MSig) -> Option<u32> {
        let Type::El { tm, .. } = &*sig.shape else {
            return None;
        };
        match self.gen_app_of(tm)? {
            (GenDef::MShape(tag), _) => Some(tag),
            _ => None,
        }
    }

    /// Child `r` of constructor `i`'s written index, at a leaf of the child
    /// index's case tree (docs/codata-indexed-design.md §3): `lam_cx` is the
    /// branch's context with the position binder pushed, `value` the branch
    /// value at depth `d` past the base, the leaf at `dd` past `lam_cx`'s
    /// branch (so `d + dd` past the base), `y` the position's payload there.
    #[allow(clippy::too_many_arguments)]
    fn child_index_at(
        &self,
        lam_cx: &Cx,
        ind: &Inductive,
        i: usize,
        r: usize,
        spine: &crate::inductive::Spine,
        value: &Rc<Term>,
        d: u32,
        dd: u32,
        comps: &[Type],
        tails: &[Type],
        y: Rc<Term>,
        ity: &Type,
        li: &Level,
        lp: &Level,
        base_len: usize,
        span: Span,
    ) -> R<Term> {
        let _scope = self.use_inductive_scope(ind);
        let ctor = &ind.ctors[i];
        let m = comps.len();
        // The case binders between the position binder and the leaf: `r`
        // right tails, then the left component unless `r` is the last.
        let mut lcx = lam_cx.clone();
        for j in 0..r {
            lcx.push("#rest".into(), tails[j].shift_local(lcx.names.len() as u32 - base_len as u32), lp.clone());
        }
        if r + 1 < m {
            lcx.push("#y".into(), comps[r].shift_local(lcx.names.len() as u32 - base_len as u32), lp.clone());
        }
        let at = lcx.names.len();
        debug_assert_eq!(at - base_len, dd as usize);
        // The payload fields declared before this child, by name; and a
        // function child's own binder.
        let ctor_ty = spine.ctors[i].0.shift_local(d + dd);
        let here = Rc::new(value.shift_local(dd));
        let mut seen = 0usize;
        let mut payload_k = 0usize;
        let mut field = None;
        for (k, kind) in ctor.kind.iter().enumerate() {
            match kind {
                FieldKind::Payload => {
                    if let Some(name) = &ctor.fields[k].0 {
                        let (term, ty, level) = self.projection(&lcx, &ctor_ty, &here, payload_k, span)?;
                        lcx.aliases.push(Rc::new(Alias { skel: None, name: name.clone(), depth: at, term, ty, level, spliced: None, shifted: Default::default() }));
                    }
                    payload_k += 1;
                }
                _ if kind.is_child() => {
                    if seen == r {
                        field = Some(k);
                        break;
                    }
                    seen += 1;
                }
                _ => {}
            }
        }
        let Some(k) = field else {
            return err("internal: an indexed codata child was not found", span);
        };
        if ctor.kind[k] == FieldKind::FnChild
            && let TyKind::Fn { binder: Some(b), .. } = &ctor.fields[k].1.kind
        {
            lcx.aliases.push(Rc::new(Alias {
                skel: None,
                name: b.clone(),
                depth: at,
                term: y,
                ty: comps[r].shift_local(at as u32 - base_len as u32),
                level: lp.clone(),
                spliced: None,
                shifted: Default::default(),
            }));
        }
        let Some(Some(exprs)) = ctor.child_index.get(k) else {
            return err("internal: an indexed codata child has no written index", span);
        };
        let exprs: Vec<&Expr> = exprs.iter().collect();
        self.index_tuple(&lcx, &ity.shift_local(at as u32 - base_len as u32 + d + 1), li, &exprs, span)
    }

    /// The index type `I` of an indexed `codata` instance, in `cx`: the
    /// telescope's right-nested `Σ` (docs/codata-indexed-design.md §3).
    pub(crate) fn codata_index_ty(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        let _scope = self.use_inductive_scope(ind);
        let mut tcx = self.field_scope_cx(cx, ind, args, vargs);
        let mut tys = Vec::with_capacity(ind.co_index.len());
        for (name, ty) in &ind.co_index {
            let (t, l) = self.elab_ty(&tcx, ty)?;
            if crate::code::code_of(&t).is_none() {
                return err(
                    format!(
                        "the index `{name}` of `{}` has a type with no code; an index type is \
                         one the kernel can quote (docs/codata-indexed-design.md §2)",
                        ind.name
                    ),
                    span,
                );
            }
            tcx.push(name.clone(), t.clone(), l.clone());
            tys.push((t, l));
        }
        let (mut acc, mut acc_lvl) = tys.pop().expect("an index telescope is nonempty");
        while let Some((t, l)) = tys.pop() {
            acc = Type::Sigma { fst_level: l.clone(), snd_level: acc_lvl.clone(), fst: Rc::new(t), snd: Rc::new(acc) };
            acc_lvl = Level::max(l, acc_lvl).normalize().canonical();
        }
        Ok((acc, acc_lvl))
    }

    /// The index binders as aliases of `i`'s projections, `i` the newest
    /// binder at `depth` and of type `ity` (scoped below it).
    fn index_aliases(&self, ind: &Inductive, ity: &Type, li: &Level, depth: usize) -> Vec<Rc<Alias>> {
        let n = ind.co_index.len();
        let mut out = Vec::with_capacity(n);
        let mut ty = ity.shift_local(1);
        let mut lvl = li.clone();
        let mut tm = var(0);
        for (k, (name, _)) in ind.co_index.iter().enumerate() {
            if k + 1 == n {
                out.push(Rc::new(Alias { skel: None, name: name.clone(), depth, term: tm, ty, level: lvl, spliced: None, shifted: Default::default() }));
                break;
            }
            let Type::Sigma { fst_level, snd_level, fst, snd } = ty else {
                unreachable!("an index telescope of several binders is a Σ")
            };
            let first = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&snd),
                pair: Rc::clone(&tm),
            });
            out.push(Rc::new(Alias {
                skel: None,
                name: name.clone(),
                depth,
                term: Rc::clone(&first),
                ty: (*fst).clone(),
                level: fst_level.clone(),
                spliced: None,
                shifted: Default::default(),
            }));
            tm = Rc::new(Term::Snd {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&snd),
                pair: tm,
            });
            ty = snd.inst_top(0, &first);
            lvl = snd_level;
        }
        out
    }

    /// The tuple of `exprs` at the index type `ity` (in `cx`), each component
    /// checked with the earlier ones substituted.
    fn index_tuple(&self, cx: &Cx, ity: &Type, li: &Level, exprs: &[&Expr], span: Span) -> R<Term> {
        let n = exprs.len();
        let mut parts = Vec::with_capacity(n);
        let mut cur = ity.clone();
        let mut lvl = li.clone();
        for (k, e) in exprs.iter().enumerate() {
            if k + 1 == n {
                let mut acc = Rc::new(self.elab_check(cx, e, &cur, &lvl)?);
                while let Some((fl, sl, f, s, v)) = parts.pop() {
                    acc = Rc::new(Term::Pair { fst_level: fl, snd_level: sl, fst_ty: f, snd_ty: s, fst: v, snd: acc });
                }
                return Ok((*acc).clone());
            }
            let Type::Sigma { fst_level, snd_level, fst, snd } = cur else {
                return err("internal: an index telescope of several binders is not a Σ", span);
            };
            let v = Rc::new(self.elab_check(cx, e, &fst, &fst_level)?);
            cur = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&v)));
            lvl = snd_level.clone();
            parts.push((fst_level, snd_level, fst, snd, v));
        }
        err("internal: an empty index", span)
    }

    /// `D<ā>(v̄, ī)` for an indexed `codata` declaration
    /// (docs/codata-indexed-design.md §2): the value arguments, then the
    /// indices, in one list. `None` for every other expression.
    pub(crate) fn try_codata_indexed_ty(&self, cx: &Cx, e: &Expr, span: Span) -> R<Option<(Type, Level)>> {
        let ExprKind::App { head, args, .. } = &e.kind else {
            return Ok(None);
        };
        let Some((name, targs)) = crate::inductive::named_head(head) else {
            return Ok(None);
        };
        if self.shadowed(cx, name) {
            return Ok(None);
        }
        let Some(ind) = self.lookup_inductive(name).cloned() else {
            return Ok(None);
        };
        if ind.co_index.is_empty() {
            return Ok(None);
        }
        let nv = ind.valparams.len();
        let ni = ind.co_index.len();
        if args.len() != nv + ni {
            return err(
                format!(
                    "`{name}` takes {nv} value argument(s) and then {ni} index argument(s), \
                     found {} argument(s) (docs/codata-indexed-design.md §2)",
                    args.len()
                ),
                span,
            );
        }
        if targs.len() != ind.params.len() {
            return err(
                format!("`{name}` takes {} type argument(s), found {}", ind.params.len(), targs.len()),
                span,
            );
        }
        let mut lowered = Vec::with_capacity(targs.len());
        for a in targs {
            lowered.push(self.elab_ty(cx, a)?);
        }
        let vargs = self.valparam_args(cx, &ind, &lowered, &args[..nv], span)?;
        let (ity, li) = self.codata_index_ty(cx, &ind, &lowered, &vargs, span)?;
        let idx: Vec<&Expr> = args[nv..].iter().collect();
        let index = self.index_tuple(cx, &ity, &li, &idx, span)?;
        self.lower_instance_m(cx, &ind, &lowered, &vargs, Some(index), span).map(Some)
    }

    // -- constructors (§3) ----------------------------------------------------

    /// `⟦Cᵢ(ā)⟧` at the expected `⟦D⟧`: the apomorphism's `in`, every child an
    /// exit. Unindexed, `corec(…; _. Unit; _ _. ⟨ℓᵢ, λp. inr(kids p)⟩; ⟨⟩;
    /// ⟨⟩)`; indexed, the out type is the carrier and the node the seed
    /// (docs/codata-indexed-design.md §4).
    pub(crate) fn build_ctor_m(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[&Expr],
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        let t = self.build_ctor_m_annotated(cx, ind, i, args, expected, span)?;
        Ok((*slim(&Rc::new(t), false)).clone())
    }

    fn build_ctor_m_annotated(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[&Expr],
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let ty = self.whnf(cx, expected, span)?;
        match self.tag_of(&ty) {
            Some(found) if found.tag == ind.tag => {}
            _ => {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, which is not the expected type here",
                        ctor.name, ind.name
                    ),
                    span,
                );
            }
        }
        let Some(p) = MParts::read(&ty, &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", span);
        };
        let (label, comps, tails, children) = self.ctor_parts(cx, ind, i, &p, args, &mut |cx, arg, at| {
            Ok(Rc::new(self.elab_check(cx, arg, at, &p.lw)?))
        }, &|d, label, pos| p.child_ty(d, label, pos), &p.lw, span)?;
        if p.indexed {
            return Ok(self.ctor_m_indexed(&p, label, &comps, &tails, children)?);
        }
        // In (Γ, i, x): the node, every child an existing tree.
        let unit = Carrier { fam: Type::Unit { level: Level::Zero }, level: Level::Zero };
        let lab2 = Rc::new(label.shift_local(2));
        let target = |d: u32, pos: Rc<Term>| {
            self.child_sum(&p, &unit, d, p.next_tm(d, Rc::new(label.shift_local(d)), pos))
        };
        let tlvl = Level::join(Level::Zero, p.lw.clone());
        let kids = p.kids_lam(2, Rc::clone(&lab2), &comps, &tails, &target, &tlvl, &mut |r, d, y, pos| {
            // `d` is past Γ; the children are scoped in Γ.
            let tree = self.kid_at(&p, &children[r], d, &label, y, &comps, &tails, r);
            Ok(Term::Inr {
                lhs_level: Level::Zero,
                rhs_level: p.lw.clone(),
                lhs: Rc::new(Type::Unit { level: Level::Zero }),
                rhs: Rc::new(p.child_ty(d, Rc::new(label.shift_local(d)), pos)),
                val: tree,
            })
        })?;
        let step = self.step_pair(&p, 2, lab2, &unit, kids);
        Ok(Term::Corec {
            sig: Rc::clone(&p.sig),
            carrier_level: Level::Zero,
            carrier: Rc::new(Type::Unit { level: Level::Zero }),
            step: Rc::new(step),
            index: triv(),
            seed: triv(),
        })
    }

    /// A child's tree at depth `d` past Γ (a function child applied to the
    /// position's payload `y`), as the children function's leaves need it.
    #[allow(clippy::too_many_arguments)]
    fn kid_at(
        &self,
        p: &MParts,
        kid: &KidVal,
        d: u32,
        label: &Term,
        y: Rc<Term>,
        comps: &[Type],
        tails: &[Type],
        r: usize,
    ) -> Rc<Term> {
        match kid {
            KidVal::Tm(t) => Rc::new(t.shift_local(d)),
            KidVal::Fn(f, dom) => Rc::new(checked_app(
                Rc::new(f.shift_local(d)),
                p.lp.clone(),
                p.lw.clone(),
                Rc::new(dom.shift_local(d)),
                Rc::new(p.child_ty(
                    d + 1,
                    Rc::new(label.shift_local(d + 1)),
                    p.position(comps, tails, d + 1, r, var(0)),
                )),
                y,
            )),
        }
    }

    /// The indexed `in` (docs/codata-indexed-design.md §4):
    /// `corec(sig; i. Out(i); i x. ⟨fst x, λp. inr(snd x p)⟩; j; ⟨ℓ, kids⟩)`.
    fn ctor_m_indexed(
        &self,
        p: &MParts,
        label: Term,
        comps: &[Type],
        tails: &[Type],
        children: Vec<KidVal>,
    ) -> R<Term> {
        let lw = p.lw.clone();
        // The carrier, over (Γ, i): the out type at `i`.
        let out_fam = m_out_ty(&p.sig.shift_local(1), &Term::Var(LocalVar(0)));
        let carrier = Carrier { fam: out_fam.clone(), level: lw.clone() };
        // The step, over (Γ, i, x).
        let Type::Sigma { fst_level: ofl, snd_level: osl, fst: ofst, snd: osnd } = out_fam.shift_local(1) else {
            unreachable!("m_out_ty builds a Σ")
        };
        let fst_x = Rc::new(Term::Fst {
            fst_level: ofl.clone(),
            snd_level: osl.clone(),
            fst_ty: Rc::clone(&ofst),
            snd_ty: Rc::clone(&osnd),
            pair: var(0),
        });
        let snd_x = Rc::new(Term::Snd {
            fst_level: ofl,
            snd_level: osl,
            fst_ty: ofst,
            snd_ty: Rc::clone(&osnd),
            pair: var(0),
        });
        let Type::Pi { dom: kdom, cod: kcod, .. } = osnd.inst_top(0, &fst_x) else {
            unreachable!("the out type's second component is a Π")
        };
        let step_ty = m_step_ty(&p.sig, &lw, &carrier.fam).shift_local(1);
        let Type::Sigma { fst_level: sfl, snd_level: ssl, fst: sfst, snd: ssnd } = step_ty else {
            unreachable!("m_step_ty builds a Σ")
        };
        let Type::Pi { cod: scod, .. } = ssnd.inst_top(0, &fst_x) else {
            unreachable!("the step type's second component is a Π")
        };
        let Type::Sum { lhs_level, rhs_level, lhs, rhs } = (*scod).clone() else {
            unreachable!("a step's child is a sum")
        };
        let body = Term::Inr {
            lhs_level,
            rhs_level,
            lhs,
            rhs,
            val: Rc::new(checked_app(
                Rc::new(snd_x.shift_local(1)),
                p.lp.clone(),
                lw.clone(),
                Rc::new(kdom.shift_local(1)),
                Rc::new(kcod.shift_local_above(1, 1)),
                var(0),
            )),
        };
        let step = Term::Pair {
            fst_level: sfl,
            snd_level: ssl.clone(),
            fst_ty: sfst,
            snd_ty: ssnd,
            fst: fst_x,
            snd: Rc::new(Term::Lam { dom_level: p.lp.clone(), cod_level: ssl, dom: kdom, body: Rc::new(body) }),
        };
        // The seed: the node at `j`, every child as written.
        let label = Rc::new(label);
        let target = |d: u32, pos: Rc<Term>| p.child_ty(d, Rc::new(label.shift_local(d)), pos);
        let kids = p.kids_lam(0, Rc::clone(&label), comps, tails, &target, &lw, &mut |r, d, y, _| {
            Ok((*self.kid_at(p, &children[r], d, &label, y, comps, tails, r)).clone())
        })?;
        let Type::Sigma { fst_level, snd_level, fst, snd } = p.out_ty(0) else {
            unreachable!("the out type is a Σ")
        };
        let seed = Term::Pair { fst_level, snd_level, fst_ty: fst, snd_ty: snd, fst: label, snd: Rc::new(kids) };
        Ok(Term::Corec {
            sig: Rc::clone(&p.sig),
            carrier_level: lw,
            carrier: Rc::new(carrier.fam),
            step: Rc::new(step),
            index: Rc::clone(&p.index),
            seed: Rc::new(seed),
        })
    }

    /// The pieces every node is built from, in `cx` (which is `p`'s
    /// context): the label from the payload arguments, the positions taken
    /// apart, and each child checked by `child` — a plain one at
    /// `child_at(0, label, pos)`, a function one at `Π(y : A). child_at(1,
    /// label, pos(y))` with `A` the position read off the label.
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn ctor_parts(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        p: &MParts,
        args: &[&Expr],
        child: &mut dyn FnMut(&Cx, &Expr, &Type) -> R<Rc<Term>>,
        child_at: &dyn Fn(u32, Rc<Term>, Rc<Term>) -> Type,
        plain_level: &Level,
        span: Span,
    ) -> R<(Term, Vec<Type>, Vec<Type>, Vec<KidVal>)> {
        let ctor = &ind.ctors[i];
        if args.len() != ctor.fields.len() {
            return err(
                format!("`{}` takes {} argument(s), found {}", ctor.name, ctor.fields.len(), args.len()),
                span,
            );
        }
        let n = ind.ctors.len();
        let spine = self.spine(&p.shape_inline(self, span)?, &p.ls, n, span)?;
        let payload: Vec<&Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(a, _)| *a)
            .collect();
        let fields = self.build_fields(cx, &spine.ctors[i].0, &payload, true, span)?;
        let label = inject(&spine, i, n, fields, 0);
        let m = ctor.kind.iter().filter(|k| k.is_child()).count();
        let (comps, tails) = p.components(self, 0, &cx.gamma, Rc::new(label.clone()), m);
        let lab = Rc::new(label.clone());
        let mut children = Vec::with_capacity(m);
        let mut r = 0usize;
        for (k, kind) in ctor.kind.iter().enumerate() {
            match kind {
                FieldKind::Plain => {
                    let pos = p.position(&comps, &tails, 0, r, Rc::new(Term::Triv { level: p.lp.clone() }));
                    children.push(KidVal::Tm(child(cx, args[k], &child_at(0, Rc::clone(&lab), pos))?));
                    r += 1;
                }
                FieldKind::FnChild => {
                    let dom = Rc::new(comps[r].clone());
                    let pos = p.position(&comps, &tails, 1, r, var(0));
                    let k_ty = Type::Pi {
                        dom_level: p.lp.clone(),
                        cod_level: plain_level.clone(),
                        dom: Rc::clone(&dom),
                        cod: Rc::new(child_at(1, Rc::new(label.shift_local(1)), pos)),
                    };
                    children.push(KidVal::Fn(child(cx, args[k], &k_ty)?, dom));
                    r += 1;
                }
                _ => {}
            }
        }
        Ok((label, comps, tails, children))
    }

    /// `X(idx) + ⟦D⟧(idx)` at depth `d`, `idx` scoped there.
    fn child_sum(&self, p: &MParts, carrier: &Carrier, d: u32, idx: Rc<Term>) -> Type {
        Type::Sum {
            lhs_level: carrier.level.clone(),
            rhs_level: p.lw.clone(),
            lhs: Rc::new(carrier.at(d, &idx)),
            rhs: Rc::new(p.d_of(d, idx)),
        }
    }

    /// `Π(p : P s). X(o) + ⟦D⟧(o)` over `s = Var(0)` at depth `k + 1`.
    fn step_kids_ty(&self, p: &MParts, k: u32, carrier: &Carrier) -> Type {
        let kf = Level::join(carrier.level.clone(), p.lw.clone());
        Type::Pi {
            dom_level: p.lp.clone(),
            cod_level: kf,
            dom: Rc::new(p.pos_at(k + 1, var(0))),
            cod: Rc::new(self.child_sum(p, carrier, k + 2, p.next_tm(k + 2, var(1), var(0)))),
        }
    }

    /// `⟨label, kids⟩` at the step type `Σ(s : S). Π(p : P s). X(o) + ⟦D⟧(o)`,
    /// at depth `k`, in the kernel's `m_step_ty` levels.
    fn step_pair(&self, p: &MParts, k: u32, label: Rc<Term>, carrier: &Carrier, kids: Term) -> Term {
        let kf = Level::join(carrier.level.clone(), p.lw.clone());
        Term::Pair {
            fst_level: p.ls.clone(),
            snd_level: kf,
            fst_ty: Rc::new(p.shape_at(k)),
            snd_ty: Rc::new(self.step_kids_ty(p, k, carrier)),
            fst: label,
            snd: Rc::new(kids),
        }
    }

    /// The step type at depth `k`.
    fn step_ty(&self, p: &MParts, k: u32, carrier: &Carrier) -> Type {
        let kf = Level::join(carrier.level.clone(), p.lw.clone());
        Type::Sigma {
            fst_level: p.ls.clone(),
            snd_level: kf,
            fst: Rc::new(p.shape_at(k)),
            snd: Rc::new(self.step_kids_ty(p, k, carrier)),
        }
    }

    // -- match (§4) -----------------------------------------------------------

    /// `match s ≡ (λo. (case fst o of Q) (snd o)) (out s)`, with `Q(v) =
    /// Π(f : Π(p : P v). ⟦D⟧). M[s]`: the motive is the expected type at the
    /// scrutinee itself, never at the constructor form, since a value of `M`
    /// has no dependent elimination (kernel design §1.2).
    ///
    /// `arms` are in declaration order, checked by the tier-0 entry point;
    /// `motive` is over `(cx.gamma, z : ⟦D⟧)`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_m(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[&Arm],
        scrut: Term,
        scrut_ty: &Type,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let t = self.elab_match_m_annotated(cx, ind, arms, scrut, scrut_ty, motive, mlvl, span)?;
        Ok((*slim(&Rc::new(t), false)).clone())
    }

    #[allow(clippy::too_many_arguments)]
    fn elab_match_m_annotated(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[&Arm],
        scrut: Term,
        scrut_ty: &Type,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let Some(p) = MParts::read(scrut_ty, &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", span);
        };
        let scrut = Rc::new(scrut);
        let result = motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut)));
        let n = ind.ctors.len();
        let lf = p.lf();
        let o_ty = Rc::new(p.out_ty(0));
        if n == 0 {
            return Ok(Term::ElimEmpty {
                level: mlvl,
                scrut_level: p.ls.clone(),
                motive: Rc::new(result.shift_local(1)),
                scrut: Rc::new(p.out_fst(0, Rc::new(p.out(0, scrut)))),
            });
        }
        let spine = self.spine(&p.shape_inline(self, span)?, &p.ls, n, span)?;
        let lq = Level::join(lf.clone(), mlvl.clone());
        // Q(v), over (Γ, o, v) at depth `k` = 2.
        let q = |k: u32, v: Rc<Term>| Type::Pi {
            dom_level: lf.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(p.kids_ty(k, v)),
            cod: Rc::new(result.shift_local(k + 1)),
        };
        let mut ocx = cx.clone();
        ocx.push("#out".into(), (*o_ty).clone(), p.lw.clone());
        ocx.codata_match = Some(ind.name.as_str().into());
        let cased = self.w_case_tree(
            &ocx,
            &spine,
            n,
            0,
            q(2, var(0)),
            &lq,
            Rc::new(p.out_fst(1, var(0))),
            1,
            &mut |bcx, i, d, value| {
                let ctor = &ind.ctors[i];
                let arm = arms[i];
                let inj = Rc::new(inject(&spine, i, n, (*value).clone(), d));
                let kids_ty = p.kids_ty(d, Rc::clone(&inj));
                let mut acx = bcx.clone();
                acx.push("#kids".into(), kids_ty.clone(), lf.clone());
                // In the arm: the children function is `Var(0)`.
                let db = d + 1;
                let value_here = Rc::new(value.shift_local(1));
                let ctor_ty = spine.ctors[i].0.shift_local(db);
                let m = ctor.kind.iter().filter(|k| k.is_child()).count();
                // The positions at the label are read in Γ: the label at depth
                // `d` mentions the branch binders, so take the components there
                // and shift.
                let (comps, tails) = p.components(self, d, &bcx.gamma, Rc::clone(&inj), m);
                let mut payload_k = 0usize;
                let mut r = 0usize;
                for (k, name) in arm.binders.iter().map(|b| b.name().to_string()).enumerate() {
                    let (term, ty, level) = match ctor.kind[k] {
                        FieldKind::Plain => {
                            let at = p.position(&comps, &tails, 1, r, Rc::new(Term::Triv { level: p.lp.clone() }));
                            r += 1;
                            let ty = p.child_ty(db, Rc::new(inj.shift_local(1)), Rc::clone(&at));
                            (app_at(var(0), at), ty, p.lw.clone())
                        }
                        FieldKind::FnChild => {
                            let dom = Rc::new(comps[r].shift_local(1));
                            let at = p.position(&comps, &tails, 2, r, var(0));
                            r += 1;
                            let cod = p.child_ty(db + 1, Rc::new(inj.shift_local(2)), Rc::clone(&at));
                            let term = Rc::new(Term::Lam {
                                dom_level: p.lp.clone(),
                                cod_level: p.lw.clone(),
                                dom: Rc::clone(&dom),
                                body: app_at(var(1), at),
                            });
                            let ty = Type::Pi {
                                dom_level: p.lp.clone(),
                                cod_level: p.lw.clone(),
                                dom,
                                cod: Rc::new(cod),
                            };
                            (term, ty, lf.clone())
                        }
                        _ => {
                            let r = if self.emits_at_forms(&acx) {
                                self.projection_at(&acx, &ctor_ty, &value_here, payload_k, span)?
                            } else {
                                self.projection(&acx, &ctor_ty, &value_here, payload_k, span)?
                            };
                            payload_k += 1;
                            r
                        }
                    };
                    acx.aliases.push(Rc::new(Alias {
                        skel: None,
                        name,
                        depth: acx.names.len(),
                        term,
                        ty,
                        level,
                        spliced: None,
                        shifted: Default::default(),
                    }));
                }
                let body = self.elab_check(&acx, &arm.body, &result.shift_local(db), &mlvl)?;
                Ok(Term::Lam {
                    dom_level: lf.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(kids_ty),
                    body: Rc::new(body),
                })
            },
        )?;
        // In (Γ, o): the case tree applied to the children.
        let applied = checked_app(
            Rc::new(cased),
            lf.clone(),
            mlvl.clone(),
            Rc::new(p.kids_ty(1, Rc::new(p.out_fst(1, var(0))))),
            Rc::new(result.shift_local(2)),
            Rc::new(p.out_snd(1, var(0))),
        );
        Ok(Term::App {
            fun: Rc::new(Term::Lam {
                dom_level: p.lw.clone(),
                cod_level: mlvl.clone(),
                dom: Rc::clone(&o_ty),
                body: Rc::new(applied),
            }),
            dom_level: p.lw.clone(),
            cod_level: mlvl,
            dom: o_ty,
            cod: Rc::new(result.shift_local(1)),
            arg: Rc::new(p.out(0, scrut)),
        })
    }

    // -- no-confusion (§4.2) --------------------------------------------------

    /// A constant-motive case tree over the label of `out(scrut)` — tier 0's
    /// disjointness and payload-injectivity predicates, read through `out`.
    /// `d_ty` and `spine` are scoped two binders below `mcx` (a `J` motive's
    /// `y` and `p`), `motive` and `scrut` in `mcx`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn const_out_m(
        &self,
        mcx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        spine: &Spine,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &crate::inductive::ConstBody,
        span: Span,
    ) -> R<Term> {
        let g = mcx.gamma.prefix(mcx.gamma.len() - 2);
        let Some(p) = MParts::read(d_ty, &g) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", span);
        };
        let label = Rc::new(p.out_fst(2, Rc::new(p.out(2, scrut))));
        self.const_case_tree(mcx, spine, ind.ctors.len(), motive, mlvl, label, body, 0, 2, span)
    }

    // -- corecursion (§5) -------------------------------------------------------

    /// Plan a corecursive definition, if this is one: the result type is
    /// codata and the body calls the declaration. `cx` is the body's context
    /// (the whole telescope), `n_tyvars` of it type parameters; `params` the
    /// written value parameters.
    pub(crate) fn corec_plan(
        &self,
        cx: &Cx,
        decl: &heather_syntax::Decl,
        selfref: &Rc<SelfRef>,
        res_ty: &Type,
        span: Span,
    ) -> R<Option<Rc<CorecSite>>> {
        let body = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
        let mut calls: Vec<Vec<Option<String>>> = Vec::new();
        crate::surface::walk_expr(&body, &mut |e| {
            if let Some((args, _)) = surface_self_call(selfref, e) {
                calls.push(
                    args.iter()
                        .map(|a| match &a.kind {
                            ExprKind::Var(v) => Some(v.clone()),
                            _ => None,
                        })
                        .collect(),
                );
            }
        });
        if calls.is_empty() {
            return Ok(None);
        }
        let head = self.whnf(cx, res_ty, span)?;
        let Some(ind) = self.tag_of(&head).filter(|i| i.codata) else {
            return Ok(None);
        };
        let Some(p) = MParts::read(&head, &cx.gamma) else {
            return Ok(None);
        };
        if let Some(q) = decl.params.iter().find(|q| q.implicit) {
            return err(
                format!(
                    "`{}` is corecursive and has the implicit parameter `{}`: a corecursive \
                     definition takes its parameters explicitly this round \
                     (docs/codata-elaborator-design.md §5)",
                    decl.name, q.name
                ),
                q.span,
            );
        }
        let n_ty = decl.tyvars.len();
        let n = decl.params.len();
        let names: Vec<String> = decl.params.iter().map(|q| q.name.clone()).collect();
        // A parameter every call passes as itself stays an outer binder; the
        // rest are the carrier. The call's own argument is checked against
        // this again when its seed is built, so a shadowing binder cannot
        // make the syntactic test lie.
        let fixed: Vec<bool> = (0..n)
            .map(|j| calls.iter().all(|c| c.get(j).and_then(|a| a.as_deref()) == Some(names[j].as_str())))
            .collect();
        let depth = cx.names.len();
        // The parameters' binders, outermost first: position `n_ty + j`.
        let param_ty = |j: usize| -> (Type, Level) {
            let e = &cx.gamma.entries[n_ty + j];
            ((*e.ty).clone(), e.level.clone())
        };
        // The varying tuple, built in the body's context: component `r` is
        // the `r`-th varying parameter's type, its earlier parameters replaced
        // by the outer binder (fixed) or the Σ binder (varying).
        let mut rank = Vec::with_capacity(n);
        let mut comps: Vec<(Type, Level)> = Vec::new();
        for j in 0..n {
            if fixed[j] {
                rank.push(None);
                continue;
            }
            let r = comps.len();
            rank.push(Some(r));
            let (ty, lvl) = param_ty(j);
            // `ty` is scoped over (Γ_t, x₀, …, x_{j-1}); the target is the
            // body's context plus the `r` Σ binders before this component.
            let base = cx.gamma.prefix(n_ty);
            let mut subst = embed(&base, (n + r) as u32);
            for (i, ri) in rank.iter().enumerate().take(j) {
                let t = match ri {
                    None => Term::Var(LocalVar((n - 1 - i + r) as u32)),
                    Some(ri) => Term::Var(LocalVar((r - 1 - ri) as u32)),
                };
                subst = subst.extended(Rc::new(t));
            }
            comps.push((ty.apply_local(&subst), lvl));
        }
        let nv = comps.len();
        let (vtuple, vtuple_level) = match comps.len() {
            0 => (Type::Unit { level: Level::Zero }, Level::Zero),
            _ => {
                let (mut acc, mut lvl) = comps.pop().expect("nonempty");
                while let Some((c, l)) = comps.pop() {
                    acc = Type::Sigma { fst_level: l.clone(), snd_level: lvl.clone(), fst: Rc::new(c), snd: Rc::new(acc) };
                    lvl = Level::max(l, lvl).normalize().canonical();
                }
                (acc, lvl)
            }
        };
        // Unindexed, the result type may mention only the fixed parameters:
        // it is the signature of the one `corec`, which sits outside the
        // carrier. Indexed, the *index* may mention any of them (the carrier
        // carries the equation, docs/codata-indexed-design.md §6), and the
        // signature still only the fixed ones.
        let sig_only = p.sig.at(Rc::new(Term::Zero));
        for (j, r) in rank.iter().enumerate() {
            let at = if p.indexed { &sig_only } else { &head };
            if r.is_some() && crate::mentions_binder(at, depth as u32, (n - 1 - j) as u32) {
                return err(
                    if p.indexed {
                        format!(
                            "the result type of the corecursive `{}` has a type or value argument \
                             mentioning `{}`, which a corecursive call changes: only its index may \
                             (docs/codata-indexed-design.md §6)",
                            decl.name, names[j]
                        )
                    } else {
                        format!(
                            "the result type of the corecursive `{}` mentions `{}`, which a \
                             corecursive call changes: the result type may mention only parameters \
                             every call passes unchanged (docs/codata-elaborator-design.md §5)",
                            decl.name, names[j]
                        )
                    },
                    span,
                );
            }
        }
        let carrier = if p.indexed {
            // X(i) = Σ(v : V). Id(I; g[v]; i), over (body, i).
            let base = cx.gamma.prefix(n_ty);
            let mut subst = embed(&base, (n + 2) as u32);
            for (j, r) in rank.iter().enumerate() {
                let t = match r {
                    None => Term::Var(LocalVar((n - 1 - j + 2) as u32)),
                    Some(r) => tuple_proj(nv, *r, Term::Var(LocalVar(0))),
                };
                subst = subst.extended(Rc::new(t));
            }
            let li = p.sig.idx_level.clone();
            let fam = Type::Sigma {
                fst_level: vtuple_level.clone(),
                snd_level: li.clone(),
                fst: Rc::new(vtuple.shift_local(1)),
                snd: Rc::new(Type::Id {
                    level: li.clone(),
                    ty: Rc::new(p.sig.idx.shift_local(2)),
                    lhs: Rc::new(p.index.apply_local(&subst)),
                    rhs: var(1),
                }),
            };
            Carrier { fam, level: Level::max(vtuple_level.clone(), li).normalize().canonical() }
        } else {
            Carrier { fam: vtuple.shift_local(1), level: vtuple_level.clone() }
        };
        let step_ty = self.step_ty(&p, 0, &carrier);
        let kf = Level::join(carrier.level.clone(), p.lw.clone());
        Ok(Some(Rc::new(CorecSite {
            selfref: Rc::clone(selfref),
            depth,
            ind: Rc::clone(&ind),
            d_ty: head,
            vtuple,
            vtuple_level,
            carrier,
            step_ty,
            step_level: Level::join(p.ls.clone(), Level::join(p.lp.clone(), kf.clone())),
            child_level: kf,
            rank,
            names,
        })))
    }

    /// The body's expected type and level under `site`.
    pub(crate) fn corec_body_ty(site: &CorecSite) -> (Type, Level) {
        (site.step_ty.clone(), site.step_level.clone())
    }

    /// The definition's term from its step `b` (scoped in the body's
    /// context), in the body's context. Unindexed, `corec(sig; _. V; _ x.
    /// b[varying ↦ projections of x]; ⟨⟩; ⟨varying parameters⟩)`; indexed, the
    /// step moves `b` from `g` to `i` along the carrier's equation
    /// (docs/codata-indexed-design.md §6).
    pub(crate) fn corec_close(&self, cx: &Cx, n_ty: usize, site: &CorecSite, b: Term, span: Span) -> R<Term> {
        let t = self.corec_close_annotated(cx, n_ty, site, b, span)?;
        Ok((*slim(&Rc::new(t), false)).clone())
    }

    fn corec_close_annotated(&self, cx: &Cx, n_ty: usize, site: &CorecSite, b: Term, span: Span) -> R<Term> {
        let Some(p) = MParts::read(&site.d_ty, &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", span);
        };
        let n = site.rank.len();
        let nv = site.varying();
        // In (body, i, x): the varying parameters are the carrier's
        // components (of `fst x` when indexed), the fixed ones the outer
        // binders.
        let tuple = if p.indexed { Term::FstAt { pair: var(0) } } else { Term::Var(LocalVar(0)) };
        let base = cx.gamma.prefix(n_ty);
        let mut subst = embed(&base, (n + 2) as u32);
        for (j, r) in site.rank.iter().enumerate() {
            let t = match r {
                None => Term::Var(LocalVar((n - 1 - j + 2) as u32)),
                Some(r) => tuple_proj(nv, *r, tuple.clone()),
            };
            subst = subst.extended(Rc::new(t));
        }
        let mut step = b.apply_local(&subst);
        let vt = self.carrier_tuple(&site.vtuple, nv, &mut |r| {
            let j = site.rank.iter().position(|x| *x == Some(r)).expect("a varying parameter");
            Ok(Rc::new(Term::Var(LocalVar((n - 1 - j) as u32))))
        })?;
        let seed = if p.indexed {
            let li = p.sig.idx_level.clone();
            step = Term::J {
                ty_level: li.clone(),
                motive_level: site.step_level.clone(),
                ty: Rc::new(p.sig.idx.shift_local(2)),
                lhs: Rc::new(p.index.apply_local(&subst)),
                motive: Rc::new(m_step_ty(&p.sig, &site.carrier.level, &site.carrier.fam).inst_top(4, &Term::Var(LocalVar(1)))),
                case: Rc::new(step),
                rhs: var(1),
                proof: Rc::new(Term::SndAt { pair: var(0) }),
            };
            let Type::Sigma { fst_level, snd_level, fst, snd } = site.carrier.at(0, &p.index) else {
                unreachable!("an indexed carrier is a Σ")
            };
            Term::Pair {
                fst_level,
                snd_level,
                fst_ty: fst,
                snd_ty: snd,
                fst: Rc::new(vt),
                snd: Rc::new(Term::Refl { level: li, ty: Rc::clone(&p.sig.idx), tm: Rc::clone(&p.index) }),
            }
        } else {
            vt
        };
        Ok(Term::Corec {
            sig: Rc::clone(&p.sig),
            carrier_level: site.carrier.level.clone(),
            carrier: Rc::new(site.carrier.fam.clone()),
            step: Rc::new(step),
            index: Rc::clone(&p.index),
            seed: Rc::new(seed),
        })
    }

    /// A value of the carrier from its `nv` components, `component(r)`
    /// scoped where `carrier` is. Driven by the count, not the type: a
    /// component may itself be a `Σ`.
    fn carrier_tuple(&self, carrier: &Type, nv: usize, component: &mut dyn FnMut(usize) -> R<Rc<Term>>) -> R<Term> {
        if nv == 0 {
            return Ok(Term::Triv { level: Level::Zero });
        }
        let mut parts = Vec::new();
        let mut cur = carrier.clone();
        for r in 0..nv - 1 {
            let Type::Sigma { fst_level, snd_level, fst, snd } = &cur else {
                unreachable!("a carrier of several components is a Σ")
            };
            let v = component(r)?;
            let next = snd.inst_top(0, &v);
            parts.push((fst_level.clone(), snd_level.clone(), Rc::clone(fst), Rc::clone(snd), v));
            cur = next;
        }
        let mut acc = component(nv - 1)?;
        while let Some((fl, sl, f, s, v)) = parts.pop() {
            acc = Rc::new(Term::Pair { fst_level: fl, snd_level: sl, fst_ty: f, snd_ty: s, fst: v, snd: acc });
        }
        Ok((*acc).clone())
    }

    /// Whether `expected`, scoped `d` binders past `p`'s context (`cx` is
    /// that context), is a child position, and the child's index there: one
    /// fixed type unindexed, `X(e) + ⟦D⟧(e)` at the child's own `e` indexed.
    fn corec_child_index(&self, cx: &Cx, p: &MParts, carrier: &Carrier, d: u32, expected: &Type, span: Span) -> Option<Rc<Term>> {
        if !p.indexed {
            let want = self.child_sum(p, carrier, d, triv());
            let lvl = Level::join(carrier.level.clone(), p.lw.clone());
            let ok = *expected == want || {
                let head = self.whnf(cx, expected, span).ok();
                matches!(head, Some(Type::Sum { .. })) && self.conv_types(cx, expected, &want, &lvl)
            };
            return ok.then(triv);
        }
        match self.whnf(cx, expected, span).ok() {
            Some(Type::Sum { lhs, rhs, .. }) => match &*decoded(&rhs) {
                Type::M { sig, index } if **sig == *p.sig.shift_local(d)
                    && self.conv_types(cx, &lhs, &carrier.at(d, index), &carrier.level) =>
                {
                    Some(Rc::clone(index))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The checking-mode hook while a corecursive body is open (§5.2):
    /// `Some(term)` when `e`, checked at `expected`, is one of the step's two
    /// positions and this function built it; `None` to elaborate it as usual.
    pub(crate) fn corec_check(&self, cx: &Cx, site: &CorecSite, e: &Expr, expected: &Type, lvl: &Level) -> R<Option<Term>> {
        let by = site.by(cx);
        let Some(p) = MParts::read(&site.d_ty.shift_local(by), &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", e.span);
        };
        let carrier = site.carrier.under(by);
        let step_here = site.step_ty.shift_local(by);
        let at = |want: &Type, wlvl: &Level| -> bool {
            *expected == *want || {
                let head = self.whnf(cx, expected, e.span).ok();
                matches!(head, Some(Type::Sigma { .. } | Type::Sum { .. }))
                    && self.conv_types(cx, expected, want, wlvl)
            }
        };
        let _ = lvl;
        let child_idx = self.corec_child_index(cx, &p, &carrier, 0, expected, e.span);
        let self_call = surface_self_call(&site.selfref, e);
        if let Some((args, _)) = self_call {
            let Some(idx) = child_idx else {
                return err(
                    format!(
                        "this call to `{}` is not guarded: a corecursive call must be a child of the \
                         constructor the definition returns — `C(…, {}(…), …)` or `C(…, λ y => {}(…), …)` \
                         (docs/codata-elaborator-design.md §5)",
                        site.selfref.written_name, site.selfref.written_name, site.selfref.written_name
                    ),
                    e.span,
                );
            };
            if let ExprKind::App { head, .. } = &e.kind
                && matches!(head.kind, ExprKind::TyApp { .. })
            {
                return err(
                    "a corecursive call takes no type arguments: they are the definition's own",
                    e.span,
                );
            }
            let seed = self.corec_seed(cx, site, &p, &carrier, &idx, &args, e.span)?;
            return Ok(Some(Term::Inl {
                lhs_level: carrier.level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(carrier.at(0, &idx)),
                rhs: Rc::new(p.d_of(0, idx)),
                val: Rc::new(seed),
            }));
        }
        let control = matches!(e.kind, ExprKind::Match { .. } | ExprKind::Block(..));
        if let Some(idx) = child_idx {
            if control {
                return Ok(None);
            }
            // An existing tree — which must not itself corecurse: a self-call
            // under a *second* constructor needs a carrier that remembers
            // the pending constructor, which this round's one-step `corec`
            // does not build (issues/codata-nested-guards.md).
            if let Some(at) = nested_self_call(&site.selfref, e) {
                return err(nested_guard_msg(&site.selfref.written_name), at);
            }
            let d_here = p.d_of(0, Rc::clone(&idx));
            let t = self.elab_check(cx, e, &d_here, &p.lw)?;
            return Ok(Some(Term::Inr {
                lhs_level: carrier.level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(carrier.at(0, &idx)),
                rhs: Rc::new(d_here),
                val: Rc::new(t),
            }));
        }
        // A function child given as a function rather than a λ, `C(…, k, …)`
        // with `k : (y: A) → D(e(y))` an existing one: the child is its
        // η-expansion `λ y. inr(k y)`. A λ goes the ordinary way, its body
        // meeting the child position above.
        if !control
            && !matches!(e.kind, ExprKind::Lam { .. })
            && let Some(Type::Pi { dom_level, dom, cod, .. }) = self.whnf(cx, expected, e.span).ok()
        {
            let mut cy = cx.clone();
            cy.push("#y".into(), (*dom).clone(), dom_level.clone());
            if let Some(idx) = self.corec_child_index(&cy, &p, &carrier, 1, &cod, e.span) {
                if let Some(at) = nested_self_call(&site.selfref, e) {
                    return err(nested_guard_msg(&site.selfref.written_name), at);
                }
                let d_here = p.d_of(1, Rc::clone(&idx));
                let fn_level = Level::join(dom_level.clone(), p.lw.clone());
                let fn_ty = Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: p.lw.clone(),
                    dom: Rc::clone(&dom),
                    cod: Rc::new(d_here.clone()),
                };
                let f = self.elab_check(cx, e, &fn_ty, &fn_level)?;
                let applied = match f {
                    Term::Lam { body, .. } => body,
                    f => Rc::new(Term::AppAt { fun: Rc::new(f.shift_local(1)), arg: var(0) }),
                };
                return Ok(Some(Term::Lam {
                    dom_level,
                    cod_level: site.child_level.clone(),
                    dom,
                    body: Rc::new(Term::Inr {
                        lhs_level: carrier.level.clone(),
                        rhs_level: p.lw.clone(),
                        lhs: Rc::new(carrier.at(1, &idx)),
                        rhs: Rc::new(d_here),
                        val: applied,
                    }),
                }));
            }
        }
        if !at(&step_here, &site.step_level) {
            return Ok(None);
        }
        if control {
            return Ok(None);
        }
        let tlvl = site.child_level.clone();
        let child_at = |d: u32, label: Rc<Term>, pos: Rc<Term>| {
            self.child_sum(&p, &carrier, d, p.next_tm(d, label, pos))
        };
        // A node: a constructor of the declaration itself.
        if let Some((i, args)) = self.codata_ctor_app(cx, &site.ind, e) {
            let (label, comps, tails, children) = self.ctor_parts(
                cx,
                &site.ind,
                i,
                &p,
                &args,
                &mut |cx, arg, at| Ok(Rc::new(self.elab_check(cx, arg, at, &tlvl)?)),
                &child_at,
                &tlvl,
                e.span,
            )?;
            let label = Rc::new(label);
            let target = |d: u32, pos: Rc<Term>| child_at(d, Rc::new(label.shift_local(d)), pos);
            let kids = p.kids_lam(0, Rc::clone(&label), &comps, &tails, &target, &tlvl, &mut |r, d, y, _| {
                Ok(match &children[r] {
                    KidVal::Tm(t) => t.shift_local(d),
                    KidVal::Fn(f, dom) => checked_app(
                        Rc::new(f.shift_local(d)),
                        p.lp.clone(),
                        tlvl.clone(),
                        Rc::new(dom.shift_local(d)),
                        Rc::new(target(d + 1, p.position(&comps, &tails, d + 1, r, var(0)))),
                        y,
                    ),
                })
            })?;
            return Ok(Some(self.step_pair(&p, 0, label, &carrier, kids)));
        }
        // Anything else is a tree that already exists, and the node is its
        // first one: `(λo. ⟨fst o, λq. inr(snd o q)⟩) (out t)`.
        let t = Rc::new(self.elab_check(cx, e, &p.d_at(0), &p.lw)?);
        let o_ty = Rc::new(p.out_ty(0));
        let kf = Level::join(carrier.level.clone(), p.lw.clone());
        let lab = Rc::new(p.out_fst(1, var(0)));
        let child_idx = p.next_tm(2, Rc::new(lab.shift_local(1)), var(0));
        let kids = Term::Lam {
            dom_level: p.lp.clone(),
            cod_level: kf.clone(),
            dom: Rc::new(p.pos_at(1, Rc::clone(&lab))),
            body: Rc::new(Term::Inr {
                lhs_level: carrier.level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(carrier.at(2, &child_idx)),
                rhs: Rc::new(p.d_of(2, Rc::clone(&child_idx))),
                val: Rc::new(checked_app(
                    Rc::new(p.out_snd(2, var(1))),
                    p.lp.clone(),
                    p.lw.clone(),
                    Rc::new(p.pos_at(2, Rc::new(p.out_fst(2, var(1))))),
                    Rc::new(p.child_ty(3, Rc::new(p.out_fst(3, var(2))), var(0))),
                    var(0),
                )),
            }),
        };
        let node = self.step_pair(&p, 1, lab, &carrier, kids);
        Ok(Some(Term::App {
            fun: Rc::new(Term::Lam {
                dom_level: p.lw.clone(),
                cod_level: site.step_level.clone(),
                dom: Rc::clone(&o_ty),
                body: Rc::new(node),
            }),
            dom_level: p.lw.clone(),
            cod_level: site.step_level.clone(),
            dom: o_ty,
            cod: Rc::new(step_here.shift_local(1)),
            arg: Rc::new(p.out(0, t)),
        }))
    }

    /// A corecursive call's seed at a child of index `idx` (scoped at `cx`):
    /// the varying arguments as a carrier value, each fixed argument checked
    /// to be its own parameter. Indexed, the seed carries `refl` of the
    /// call's index, which must be the child's (docs/codata-indexed-design.md
    /// §6).
    #[allow(clippy::too_many_arguments)]
    fn corec_seed(
        &self,
        cx: &Cx,
        site: &CorecSite,
        p: &MParts,
        carrier: &Carrier,
        idx: &Rc<Term>,
        args: &[&Expr],
        span: Span,
    ) -> R<Term> {
        let n = site.rank.len();
        if args.len() != n {
            return err(
                format!("`{}` takes {} argument(s), found {}", site.selfref.written_name, n, args.len()),
                span,
            );
        }
        let by = site.by(cx);
        // Parameter `j`'s binder, seen from here.
        let binder = |j: usize| Term::Var(LocalVar((n - 1 - j) as u32 + by));
        for (j, r) in site.rank.iter().enumerate() {
            if r.is_none() {
                let (t, _, _) = self.elab_infer(cx, args[j])?;
                if t != binder(j) {
                    return err(
                        format!(
                            "`{}` passes `{}` unchanged in every other corecursive call, so it is not \
                             part of the state; here the argument is something else (a shadowing \
                             binder?). Rename the binder (docs/codata-elaborator-design.md §5)",
                            site.selfref.written_name, site.names[j]
                        ),
                        args[j].span,
                    );
                }
            }
        }
        if !p.indexed {
            return self.corec_seed_checked(cx, site, args, &carrier.at(0, idx));
        }
        let Type::Sigma { fst_level, snd_level, fst, snd } = carrier.at(0, idx) else {
            return err("internal: an indexed corecursive carrier is not a Σ", span);
        };
        let tuple = Rc::new(self.corec_seed_checked(cx, site, args, &fst)?);
        let eq = snd.inst_top(0, &tuple);
        let Type::Id { level, ty, lhs, .. } = &eq else {
            return err("internal: an indexed corecursive carrier carries no equation", span);
        };
        let call_at = p.d_of(0, Rc::clone(lhs));
        let child_at = p.d_of(0, Rc::clone(idx));
        if !self.conv_types(cx, &call_at, &child_at, &p.lw) {
            return err(
                format!(
                    "this call to `{}` is at `{}`, but the child it stands for is at `{}`: a \
                     corecursive call's result index must be the child's \
                     (docs/codata-indexed-design.md §6)",
                    site.selfref.written_name,
                    self.display_type(cx, &call_at),
                    self.display_type(cx, &child_at)
                ),
                span,
            );
        }
        Ok(Term::Pair {
            fst_level,
            snd_level,
            fst_ty: fst,
            snd_ty: Rc::clone(&snd),
            fst: tuple,
            snd: Rc::new(Term::Refl { level: level.clone(), ty: Rc::clone(ty), tm: Rc::clone(lhs) }),
        })
    }

    /// [`Self::corec_seed`]'s tuple at `vtuple` (the varying parameters'
    /// tuple type, here), each component checked at its type with the earlier
    /// components substituted.
    fn corec_seed_checked(&self, cx: &Cx, site: &CorecSite, args: &[&Expr], vtuple: &Type) -> R<Term> {
        let varying: Vec<usize> = (0..site.rank.len()).filter(|&j| site.rank[j].is_some()).collect();
        let mut parts = Vec::new();
        let mut cur = vtuple.clone();
        for (r, &j) in varying.iter().enumerate() {
            if r + 1 == varying.len() {
                let mut acc = Rc::new(self.elab_check(cx, args[j], &cur, &site.vtuple_level)?);
                while let Some((fl, sl, f, s, v)) = parts.pop() {
                    acc = Rc::new(Term::Pair { fst_level: fl, snd_level: sl, fst_ty: f, snd_ty: s, fst: v, snd: acc });
                }
                return Ok((*acc).clone());
            }
            let head = self.whnf(cx, &cur, args[j].span)?;
            let Type::Sigma { fst_level, snd_level, fst, snd } = head else {
                return err("internal: a corecursive carrier is not a tuple", args[j].span);
            };
            let v = Rc::new(self.elab_check(cx, args[j], &fst, &fst_level)?);
            cur = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&v)));
            parts.push((fst_level, snd_level, fst, snd, v));
        }
        Ok(Term::Triv { level: Level::Zero })
    }

    /// `e` as an application of one of `ind`'s constructors, with its
    /// arguments; `None` for anything else (including a local that shadows
    /// the constructor's name).
    fn codata_ctor_app<'e>(&self, cx: &Cx, ind: &Inductive, e: &'e Expr) -> Option<(usize, Vec<&'e Expr>)> {
        let (head, args): (&Expr, Vec<&Expr>) = match &e.kind {
            ExprKind::App { head, args, named, .. } if named.is_empty() => (head, args.iter().collect()),
            ExprKind::Var(_) => (e, Vec::new()),
            _ => return None,
        };
        let head = match &head.kind {
            ExprKind::TyApp { head, .. } => head,
            _ => head,
        };
        let ExprKind::Var(name) = &head.kind else {
            return None;
        };
        if cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| &a.name == name) {
            return None;
        }
        let (found, i) = self.lookup_ctor(name)?;
        (found.tag == ind.tag).then_some((i, args))
    }
}
