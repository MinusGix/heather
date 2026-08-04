//! Indexed families, route 2b: the family by **fording** over an irrelevant
//! `sEq`.
//!
//! This module is the mechanization of `docs/inductive-fording-lowering.md`,
//! and is meant to be read against it — the section numbers in the comments
//! are that document's, and `crates/elab/tests/indexed_route_2b_wf.rs` is the
//! hand prototype whose terms this generator emits. The doctrine is the
//! tiers' (`inductive.rs`): the lowering is untrusted, the kernel re-checks
//! every emitted term, and a bug here produces a checked theorem about a type
//! the user did not write — so no clever shortcuts, and annotations are read
//! off the type being eliminated wherever one exists.
//!
//! The scheme in four lines (§4–§8):
//!
//! ```text
//! Skel        = the declaration with its indices erased, by the unindexed tiers
//! μ           = elim_Skel at motive I, each branch the ctor's written result index
//! ⟦D<ā>(m)⟧   = Σ^{l,li}(s : Skel). sEq^{li}(I; μ s; m)
//! ⟦c(b̄)⟧      = ⟨ skel_c(stored b̄; fst v̄) , the transp chain of §7 ⟩
//! ```
//!
//! and the eliminator recurses on the **skeleton** at the fording motive
//! `Q(σ) = Π(m'). Π(e' : sEq(I; μ σ; m')). M[m', ⟨σ, e'⟩]`, with each arm in
//! form A (index inversion, §8.2 — definitional β) or form B (one `transp` at
//! the arm's head, §8.3). Which form a constructor gets is §8.4's rule: form A
//! exactly when the constructor would have been route-1-eligible on its own.

use std::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_syntax::ast::{Arm, Expr, ExprKind, Span};

use crate::indexed::{set_scrut, wf_ih_at};
use crate::inductive::{inject, nat_lit, tag_value, FieldKind, IdxTy, Inductive};
use crate::wf::{fin_index, nth_child, Branches, Tel};
use crate::{embed, err, Alias, Cx, Elaborator, Guard, GuardKind, R};

/// A type in **forded form** (§6.3), read back into its parts: a `Type::Sigma`
/// whose `snd` is a `Type::SEq` whose `lhs` is the `μ` node applied at the Σ
/// binder.
///
/// The fingerprint is tag-anchored and therefore cheaper and more robust than
/// route 1's (§14.1): the declaration's identity is read by `tag_of` out of the
/// **skeleton**, where it already lives and where a `Wf` is already seen
/// through. A user cannot forge the shape, because `sEq` is generator-internal
/// by policy and unwritable at the surface.
pub(crate) struct FordedFam {
    /// `l` — the skeleton's level.
    pub level: Level,
    /// `li` — the index type's level.
    pub ilvl: Level,
    /// `I`, scoped in the ambient context.
    pub ity: Type,
    /// `⟦Skel<ā>⟧`, scoped in the ambient context.
    pub skel_ty: Type,
    /// `μ` as a whole node with a **closed placeholder** in its scrutinee slot
    /// — kept whole, never branch-by-branch, for the reason route 1 records at
    /// `IndexedFam::at`: a detached branch reads its own binders as free
    /// variables and a bare shift would move them.
    pub mu: Rc<Term>,
    /// The index the family is applied at.
    pub idx: Rc<Term>,
}

impl FordedFam {
    /// `l ⊔ li` — the forded family's own level (§6.2).
    pub fn lvl(&self) -> Level {
        Level::max(self.level.clone(), self.ilvl.clone())
    }

    /// `μ s`, with `s` and the result scoped `by` binders past the ambient
    /// context.
    pub fn mu_at(&self, s: Term, by: u32) -> Term {
        set_scrut(&self.mu.shift_local(by), Rc::new(s)).expect("a μ node has a scrutinee slot")
    }

    /// `sEq^{li}(I; μ s; m)` at `by`.
    pub fn eq_at(&self, s: Term, m: Term, by: u32) -> Type {
        Type::SEq {
            level: self.ilvl.clone(),
            ty: Rc::new(self.ity.shift_local(by)),
            lhs: Rc::new(self.mu_at(s, by)),
            rhs: Rc::new(m),
        }
    }

    /// `srefl^{li}(I; t)` at `by`.
    pub fn srefl_at(&self, t: Term, by: u32) -> Term {
        Term::SRefl {
            level: self.ilvl.clone(),
            ty: Rc::new(self.ity.shift_local(by)),
            tm: Rc::new(t),
        }
    }

    /// `Σ^{l,li}(s : Skel). sEq^{li}(I; μ s; m)` at `by`, with `m` scoped at
    /// `by` (the Σ's second component binds, so `m` moves out by one there).
    pub fn ty_at(&self, m: Term, by: u32) -> Type {
        Type::Sigma {
            fst_level: self.level.clone(),
            snd_level: self.ilvl.clone(),
            fst: Rc::new(self.skel_ty.shift_local(by)),
            snd: Rc::new(self.eq_at(
                Term::Var(LocalVar(0)),
                m.shift_local(1),
                by + 1,
            )),
        }
    }

    fn parts_at(&self, m: Term, by: u32) -> (Level, Level, Rc<Type>, Rc<Type>) {
        let Type::Sigma { fst_level, snd_level, fst, snd } = self.ty_at(m, by) else {
            unreachable!("ty_at builds a Σ")
        };
        (fst_level, snd_level, fst, snd)
    }

    pub fn fst_at(&self, m: Term, x: Term, by: u32) -> Term {
        let (fst_level, snd_level, fst_ty, snd_ty) = self.parts_at(m, by);
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair: Rc::new(x) }
    }

    pub fn snd_at(&self, m: Term, x: Term, by: u32) -> Term {
        let (fst_level, snd_level, fst_ty, snd_ty) = self.parts_at(m, by);
        Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair: Rc::new(x) }
    }

    pub fn pair_at(&self, m: Term, s: Term, e: Term, by: u32) -> Term {
        let (fst_level, snd_level, fst_ty, snd_ty) = self.parts_at(m, by);
        Term::Pair {
            fst_level,
            snd_level,
            fst_ty,
            snd_ty,
            fst: Rc::new(s),
            snd: Rc::new(e),
        }
    }
}

/// Which of §8's two arm shapes a constructor gets, and why (§8.2's rule:
/// *inside 2b, a constructor gets definitional open-data β exactly when it
/// would have been route-1-eligible on its own*).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    /// `e_c = 0` with no children: the motive's index is inverted by
    /// `elim_Nat` and the stored proof is consulted nowhere.
    AZero,
    /// `e_c = Succ(x)` with `x` the index variable of this constructor's one
    /// child: the same inversion, with the tail's proof re-derived at `pred`.
    ASucc,
    /// Everything else: §8.3's `transp` at the arm's head.
    B,
}

/// `pred`, and the two no-confusion codes of §8.2's form A, at `Nat`. Form A
/// is generated at a `Nat` index only this round (§14.4: the pieces for a
/// declared index exist in `wf.rs` but have never been composed).
fn nat_elim(motive: Type, level: Level, base: Term, step: Term, scrut: Term) -> Term {
    Term::ElimNat {
        level,
        motive: Rc::new(motive),
        base: Rc::new(base),
        step: Rc::new(step),
        scrut: Rc::new(scrut),
    }
}

fn pred(n: Term) -> Term {
    nat_elim(Type::Nat, Level::constant(0), Term::Zero, Term::Var(LocalVar(1)), n)
}

/// `⌜Unit⌝` at `0`, `⌜Empty⌝` at `S _` — and the mirror image.
fn tag_pred(n: Term, unit_at_zero: bool) -> Term {
    let u = Term::TmUnit { level: Level::Zero };
    let e = Term::TmEmpty { level: Level::Zero };
    let (base, step) = if unit_at_zero { (u, e) } else { (e, u) };
    nat_elim(Type::Ty(Level::constant(0)), Level::constant(1), base, step, n)
}

impl Elaborator {
    // -- reading the form back (§6.3) ---------------------------------------

    /// Read a type back as a forded family. `None` for everything else.
    pub(crate) fn forded_of(&self, cx: &Cx, ty: &Type) -> Option<(Rc<Inductive>, FordedFam)> {
        let d = crate::inductive::decoded(ty);
        let Type::Sigma { fst_level, fst, snd, .. } = &*d else { return None };
        let (fst_level, fst, snd) = (fst_level.clone(), Rc::clone(fst), Rc::clone(snd));
        drop(d);
        let sd = crate::inductive::decoded(&snd);
        let Type::SEq { level, ty: ity, lhs, rhs } = &*sd else { return None };
        let (ilvl, ity, lhs, rhs) =
            (level.clone(), (**ity).clone(), Rc::clone(lhs), Rc::clone(rhs));
        drop(sd);
        // The tag comes out of the *skeleton*, where `tag_of` already looks.
        let skel = self.tag_of(&fst)?;
        let ind = Rc::clone(self.forded_by_skel.get(&skel.tag)?);
        let node = set_scrut(&lhs, Rc::new(Term::Zero))?;
        // The Σ's second component is scoped under the binder; `μ`, `I` and the
        // index all mention it nowhere, so substituting a closed term for it is
        // exactly the un-shift back to the ambient context.
        let down = LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero));
        Some((
            ind,
            FordedFam {
                level: fst_level,
                ilvl,
                ity: ity.apply_local(&down),
                skel_ty: (*fst).clone(),
                mu: Rc::new(node.apply_local(&down)),
                idx: Rc::new(rhs.apply_local(&down)),
            },
        ))
    }

    /// [`Self::forded_of`] with reduction behind it, for a family that arrived
    /// through an `I -> Type` **function value**. The structural read comes
    /// first and unchanged, so nothing that resolved before pays anything new;
    /// unlike route 1's, over-reduction is harmless here, because a Σ *is* a
    /// whnf and the read succeeds the moment the wrapper is peeled (§14.3).
    pub(crate) fn forded_of_at(
        &self,
        cx: &Cx,
        ty: &Type,
    ) -> Option<(Rc<Inductive>, FordedFam)> {
        if let Some(r) = self.forded_of(cx, ty) {
            return Some(r);
        }
        let Type::El { level, tm } = ty else { return None };
        let mut tm = Rc::clone(tm);
        for _ in 0..self.fuel.min(1024) {
            let next = heather_kernel::reduce::step_term_delta(
                &tm,
                &cx.gamma,
                heather_kernel::reduce::Defs::transparent(&self.delta_psi),
            )?;
            tm = Rc::new(next);
            let cand = Type::El { level: level.clone(), tm: Rc::clone(&tm) };
            if let Some(r) = self.forded_of(cx, &cand) {
                return Some(r);
            }
        }
        None
    }

    // -- the type (§4–§6) ---------------------------------------------------

    /// `⟦D<ā>(m)⟧ = Σ^{l,li}(s : ⟦Skel<ā>⟧). sEq^{li}(I; μ s; m)` (§6).
    pub(crate) fn lower_forded_instance(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        idx: Term,
        span: Span,
    ) -> R<(Type, Level)> {
        let fam = self.forded_fam(cx, ind, args, idx, span)?;
        Ok((fam.ty_at((*fam.idx).clone(), 0), fam.lvl()))
    }

    /// The pieces of §6, gathered: the skeleton, the index type, and `μ`.
    fn forded_fam(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        idx: Term,
        span: Span,
    ) -> R<FordedFam> {
        let skel = ind.skel.as_ref().expect("a forded declaration has a skeleton");
        // §4.1: the skeleton takes the *ordinary* shape test — `Wf` when some
        // constructor has a child, tier 0's sum-of-Σs otherwise.
        let (skel_ty, l) = self.lower_instance(cx, skel, args, &[], span)?;
        let (ity, ilvl) = self.index_type_of(cx, ind, span)?;
        let mu = self.build_mu(cx, ind, skel, &skel_ty, &l, &ity, &ilvl, span)?;
        Ok(FordedFam {
            level: l,
            ilvl,
            ity,
            skel_ty,
            mu: Rc::new(mu),
            idx: Rc::new(idx),
        })
    }

    /// `μ : ⟦Skel<ā>⟧ → I` (§5), as a node with a placeholder scrutinee.
    ///
    /// Each branch is the constructor's **own written result index**, with each
    /// child-index variable replaced by the recursion at that child and each
    /// payload variable by its projection out of the label. Nothing about the
    /// index expression is inspected, which is why §3.2 has no condition on its
    /// shape.
    #[allow(clippy::too_many_arguments)]
    fn build_mu(
        &self,
        cx: &Cx,
        ind: &Inductive,
        skel: &Rc<Inductive>,
        skel_ty: &Type,
        l: &Level,
        ity: &Type,
        ilvl: &Level,
        span: Span,
    ) -> R<Term> {
        let n = ind.ctors.len();
        if skel.recursive {
            // `wf.rs`'s recursor device at a new motive — its third client, and
            // it needs no new machinery (§5 fact 2).
            let body = |bcx: &Cx,
                        tel: &Tel,
                        k: usize,
                        value: &Rc<Term>,
                        d_body: u32,
                        _e: &Type|
             -> R<Term> {
                let acx = self.mu_branch_cx(bcx, ind, Some(tel), k, value, d_body, ity, ilvl, span)?;
                self.elab_check(&acx, self.res_expr(ind, k), &ity.shift_local(d_body), ilvl)
            };
            self.build_elim_wf(
                cx,
                skel,
                skel_ty,
                ity.shift_local(1),
                ilvl.clone(),
                Term::Zero,
                &Branches::Custom(&body),
                None,
                span,
            )
        } else {
            // A non-recursive skeleton has no children, so no constructor has a
            // child-index field and every branch reads payload only.
            let spine = self.spine(skel_ty, l, n, span)?;
            let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _e: &Type| -> R<Term> {
                let acx = self.mu_branch_cx(bcx, ind, None, k, value, d, ity, ilvl, span)?;
                self.elab_check(&acx, self.res_expr(ind, k), &ity.shift_local(d), ilvl)
            };
            self.idx_case_tree(
                cx,
                &spine,
                n,
                0,
                ity.shift_local(1),
                ilvl,
                Rc::new(Term::Zero),
                0,
                &body,
            )
        }
    }

    /// The constructor's written result index (§2). Present on every
    /// constructor of a forded declaration, by construction.
    fn res_expr<'a>(&self, ind: &'a Inductive, k: usize) -> &'a Expr {
        ind.ctors[k].res_expr.as_ref().expect("a forded ctor carries its result index")
    }

    /// One branch's context for `μ` (§5): the child-index variables bound to
    /// the recursion at their children, the payload variables to their
    /// projections out of the label.
    #[allow(clippy::too_many_arguments)]
    fn mu_branch_cx(
        &self,
        bcx: &Cx,
        ind: &Inductive,
        tel: Option<&Tel>,
        k: usize,
        value: &Rc<Term>,
        d_body: u32,
        ity: &Type,
        ilvl: &Level,
        span: Span,
    ) -> R<Cx> {
        let ctor = &ind.ctors[k];
        let m = ctor.arity();
        let mut acx = bcx.clone();
        acx.selfref = None;
        acx.guard = None;
        let depth = acx.names.len();
        let ctor_ty = match tel {
            Some(tel) => tel.spine.ctors[k].0.shift_local(d_body),
            None => self.ctor_spine_at(bcx, ind, k, d_body, span)?,
        };
        let mut p = 0usize;
        for (j, (name, _)) in ctor.fields.iter().enumerate() {
            let Some(name) = name.clone() else {
                if ctor.kind[j] == FieldKind::Payload {
                    p += 1;
                }
                continue;
            };
            match ctor.kind[j] {
                FieldKind::Plain => {}
                FieldKind::IndexVar => {
                    // `n` **is** `μ(child)`, definitionally (§4.2).
                    let child = ctor
                        .rec_at
                        .iter()
                        .position(|a| *a == Some(j))
                        .expect("an index variable indexes some child");
                    let ct = ctor.kind[..child]
                        .iter()
                        .filter(|k| **k == FieldKind::Plain)
                        .count();
                    let tel = tel.expect("a child-index field only occurs at a `Wf` skeleton");
                    acx.aliases.push(Rc::new(Alias {
                        name,
                        depth,
                        term: Rc::new(wf_ih_at(tel, m, ct, d_body)),
                        ty: ity.shift_local(d_body),
                        level: ilvl.clone(),
                    }));
                }
                _ => {
                    let (term, ty, level) = self.projection(&acx, &ctor_ty, value, p, span)?;
                    acx.aliases.push(Rc::new(Alias { name, depth, term, ty, level }));
                    p += 1;
                }
            }
        }
        Ok(acx)
    }

    /// `⟦c_k⟧` of the **skeleton**, at a non-recursive skeleton, weakened by
    /// `d`.
    fn ctor_spine_at(
        &self,
        cx: &Cx,
        ind: &Inductive,
        k: usize,
        d: u32,
        span: Span,
    ) -> R<Type> {
        let skel = ind.skel.as_ref().expect("forded");
        let (ty, l) = self.lower_instance(cx, skel, &[], &[], span)?;
        let spine = self.spine(&ty, &l, ind.ctors.len(), span)?;
        Ok(spine.ctors[k].0.shift_local(d))
    }

    // -- constructors (§7) --------------------------------------------------

    /// The written result index `e_c` at a constructor's *arguments* — what
    /// §7's index check compares against the expected family's index, and what
    /// [`Elaborator::infer_ctor`] needs to build the family at all.
    pub(crate) fn forded_ctor_index(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (ity, ilvl) = self.index_type_of(cx, ind, span)?;
        let acx = self.res_arg_cx(cx, ind, i, args, &ity, &ilvl, &[])?;
        let t = self.elab_check(&acx, self.res_expr(ind, i), &ity, &ilvl)?;
        let _ = span;
        Ok((t, ity, ilvl))
    }

    /// A context binding a constructor's child-index and payload fields to the
    /// terms the *written arguments* denote. `pays` overrides the payload
    /// values when the caller already has them typed (the checking path);
    /// otherwise a payload the index mentions is inferred.
    #[allow(clippy::too_many_arguments)]
    fn res_arg_cx(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[Expr],
        ity: &Type,
        ilvl: &Level,
        pays: &[(usize, Rc<Term>, Type, Level)],
    ) -> R<Cx> {
        let ctor = &ind.ctors[i];
        let mut acx = cx.clone();
        acx.selfref = None;
        acx.guard = None;
        let depth = acx.names.len();
        let e = self.res_expr(ind, i);
        for (k, (name, _)) in ctor.fields.iter().enumerate() {
            let Some(name) = name.clone() else { continue };
            match ctor.kind[k] {
                FieldKind::IndexVar => {
                    let term = self.elab_check(cx, &args[k], ity, ilvl)?;
                    acx.aliases.push(Rc::new(Alias {
                        name,
                        depth,
                        term: Rc::new(term),
                        ty: ity.clone(),
                        level: ilvl.clone(),
                    }));
                }
                FieldKind::Payload => {
                    if let Some((_, term, ty, level)) = pays.iter().find(|(j, ..)| *j == k) {
                        acx.aliases.push(Rc::new(Alias {
                            name,
                            depth,
                            term: Rc::clone(term),
                            ty: ty.clone(),
                            level: level.clone(),
                        }));
                    } else if crate::inductive::expr_mentions(e, &name) {
                        let (term, ty, level) = self.elab_infer(cx, &args[k])?;
                        acx.aliases.push(Rc::new(Alias {
                            name,
                            depth,
                            term: Rc::new(term),
                            ty,
                            level,
                        }));
                    }
                }
                _ => {}
            }
        }
        Ok(acx)
    }

    /// `⟦c(b̄)⟧ = ⟨ skel_c(stored b̄ ; fst v̄) , π_c ⟩` (§7).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_forded_ctor(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[Expr],
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let Some((found, fam)) = self.forded_of_at(cx, expected) else {
            return err(
                format!(
                    "`{}` constructs the forded family `{}(i)`, but the expected type \
                     here is not in that family form \
                     (docs/inductive-fording-lowering.md §6)",
                    ctor.name, ind.name
                ),
                span,
            );
        };
        if found.tag != ind.tag {
            return err(
                format!(
                    "`{}` is a constructor of `{}`, which is not the expected type here",
                    ctor.name, ind.name
                ),
                span,
            );
        }
        let _ = expected_lvl;
        let skel = ind.skel.as_ref().expect("forded");
        let spine = self.spine(&fam.skel_ty, &fam.level, ind.ctors.len(), span)?;
        // The label: the tag and the stored (payload) arguments, tier 0 §4
        // verbatim — with the field values kept, because the written result
        // index may mention them.
        let payload: Vec<Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(a, _)| a.clone())
            .collect();
        let mut pay_vals: Vec<(Rc<Term>, Type, Level)> = Vec::new();
        let label_fields =
            self.build_fields_collect(cx, &spine.ctors[i].0, &payload, true, &mut pay_vals, span)?;
        let label = inject(&spine, i, ind.ctors.len(), label_fields, 0);
        let pays: Vec<(usize, Rc<Term>, Type, Level)> = ctor
            .kind
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(k, _)| k)
            .zip(pay_vals)
            .map(|(k, (t, ty, lv))| (k, t, ty, lv))
            .collect();
        // The children's index arguments, and the children themselves — each
        // checked at the family instance its own written index names.
        let mut xs: Vec<Term> = Vec::new();
        let mut kids: Vec<Term> = Vec::new();
        for (k, kind) in ctor.kind.iter().enumerate() {
            if *kind != FieldKind::Plain {
                continue;
            }
            let ix = ctor.rec_at[k].expect("a child records its index variable");
            let x = self.elab_check(cx, &args[ix], &fam.ity, &fam.ilvl)?;
            let child_ty = fam.ty_at(x.clone(), 0);
            let v = self.elab_check(cx, &args[k], &child_ty, &fam.lvl())?;
            xs.push(x);
            kids.push(v);
        }
        let skel_tm = if skel.recursive {
            let Type::Wf { level, shape, arity } = &fam.skel_ty else {
                return err("internal: a recursive skeleton did not lower to a `Wf`", span);
            };
            let mut acc = Term::Triv { level: level.clone() };
            let mut tail_len = Term::Zero;
            for (t, v) in kids.iter().enumerate().rev() {
                let child = fam.fst_at(xs[t].clone(), v.clone(), 0);
                let tail = tail_len.clone();
                acc = Term::Pair {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst_ty: Rc::new(fam.skel_ty.clone()),
                    snd_ty: Rc::new(Type::Vec {
                        level: level.clone(),
                        elem: Rc::new(fam.skel_ty.shift_local(1)),
                        len: Rc::new(tail.shift_local(1)),
                    }),
                    fst: Rc::new(child),
                    snd: Rc::new(acc),
                };
                tail_len = Term::Succ(Rc::new(tail_len));
            }
            Term::Supf {
                level: level.clone(),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
                label: Rc::new(label),
                children: Rc::new(acc),
            }
        } else {
            label
        };
        // §7's index check, one conversion, exactly as route 1 does.
        let acx = self.res_arg_cx(cx, ind, i, args, &fam.ity, &fam.ilvl, &pays)?;
        let target = self.elab_check(&acx, self.res_expr(ind, i), &fam.ity, &fam.ilvl)?;
        if conv_term(
            self.psi(),
            &cx.gamma,
            Layer::Prog,
            &target,
            &fam.idx,
            &fam.ity,
            &fam.ilvl,
            self.fuel,
        )
        .is_err()
        {
            return err(
                format!(
                    "`{}` constructs `{}` at its written result index, which is not the \
                     expected index",
                    ctor.name, ind.name
                ),
                span,
            );
        }
        // §7's `π_c`: `srefl` at the innermost motive instance, then one
        // `transp` per child rewriting that child's measure to the index the
        // user wrote. Every proof here sits at `sEq`, where the irrelevance arm
        // erases it — §9's cast rule does not bind (rule 2).
        let mu_s = fam.mu_at(skel_tm.clone(), 0);
        let mut proof = fam.srefl_at(mu_s.clone(), 0);
        for t in (0..kids.len()).rev() {
            // The motive: the written index with children `< t` still at their
            // measures, child `t` at the bound `z`, and children `> t` already
            // at what the user wrote.
            let mut zcx = cx.clone();
            zcx.push("#z".into(), fam.ity.clone(), fam.ilvl.clone());
            let motive_idx = {
                let mut binds: Vec<(usize, Rc<Term>, Type, Level)> = pays.clone();
                let mut seen = 0usize;
                for (k, kind) in ctor.kind.iter().enumerate() {
                    if *kind != FieldKind::Plain {
                        continue;
                    }
                    let ix = ctor.rec_at[k].expect("a child records its index variable");
                    let term = match seen.cmp(&t) {
                        std::cmp::Ordering::Less => {
                            Rc::new(fam.mu_at(fam.fst_at(xs[seen].clone(), kids[seen].clone(), 0), 0))
                        }
                        std::cmp::Ordering::Equal => Rc::new(Term::Var(LocalVar(0))),
                        std::cmp::Ordering::Greater => Rc::new(xs[seen].clone()),
                    };
                    binds.push((ix, term, fam.ity.clone(), fam.ilvl.clone()));
                    seen += 1;
                }
                self.res_index_bound(&zcx, cx, ind, i, &binds, &fam)?
            };
            let child = fam.fst_at(xs[t].clone(), kids[t].clone(), 0);
            proof = Term::Transp {
                ty_level: fam.ilvl.clone(),
                motive_level: fam.ilvl.clone(),
                ty: Rc::new(fam.ity.clone()),
                motive: Rc::new(Type::SEq {
                    level: fam.ilvl.clone(),
                    ty: Rc::new(fam.ity.shift_local(1)),
                    lhs: Rc::new(mu_s.shift_local(1)),
                    rhs: Rc::new(motive_idx),
                }),
                lhs: Rc::new(fam.mu_at(child.clone(), 0)),
                rhs: Rc::new(xs[t].clone()),
                proof: Rc::new(fam.snd_at(xs[t].clone(), kids[t].clone(), 0)),
                tm: Rc::new(proof),
            };
        }
        Ok(fam.pair_at(target, skel_tm, proof, 0))
    }

    /// The written result index elaborated one binder deeper, with each field
    /// bound to a chosen term — §7's `e_c[x_t ↦ z]`. The aliases are given at
    /// the *ambient* depth, so an `Alias`'s own `depth` shifts them past the
    /// binder; the one at the bound variable is given at the deeper depth.
    #[allow(clippy::too_many_arguments)]
    fn res_index_bound(
        &self,
        zcx: &Cx,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        binds: &[(usize, Rc<Term>, Type, Level)],
        fam: &FordedFam,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let mut acx = zcx.clone();
        acx.selfref = None;
        acx.guard = None;
        for (k, term, ty, level) in binds {
            let Some(name) = ctor.fields[*k].0.clone() else { continue };
            // A bound `z` is already scoped in `zcx`; everything else is
            // scoped in `cx` and moves out by one.
            let bound = matches!(&**term, Term::Var(LocalVar(0)));
            acx.aliases.push(Rc::new(Alias {
                name,
                depth: if bound { zcx.names.len() } else { cx.names.len() },
                term: Rc::clone(term),
                ty: ty.clone(),
                level: level.clone(),
            }));
        }
        self.elab_check(&acx, self.res_expr(ind, i), &fam.ity.shift_local(1), &fam.ilvl)
    }

    /// [`Elaborator::build_fields`], keeping each field's value: §7 needs the
    /// payload terms twice, once in the label and once in the written result
    /// index.
    fn build_fields_collect(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        args: &[Expr],
        tag: bool,
        out: &mut Vec<(Rc<Term>, Type, Level)>,
        span: Span,
    ) -> R<Term> {
        let head = self.whnf(cx, ctor_ty, span)?;
        let Type::Sigma { fst_level, snd_level, fst, snd } = head else {
            if let Type::Unit { level } = &head
                && args.is_empty()
            {
                return Ok(Term::Triv { level: level.clone() });
            }
            return err("internal: malformed constructor encoding", span);
        };
        let value = if tag {
            Rc::new(tag_value(&fst))
        } else {
            let (arg, _) = args
                .split_first()
                .ok_or(crate::ElabError::Elab { msg: "too few arguments".into(), span })?;
            let v = Rc::new(self.elab_check(cx, arg, &fst, &fst_level)?);
            out.push((Rc::clone(&v), (*fst).clone(), fst_level.clone()));
            v
        };
        let rest = if tag { args } else { &args[1..] };
        let tail = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&value)));
        let tail_tm = self.build_fields_collect(cx, &tail, rest, false, out, span)?;
        Ok(Term::Pair {
            fst_level,
            snd_level,
            fst_ty: fst,
            snd_ty: snd,
            fst: value,
            snd: Rc::new(tail_tm),
        })
    }

    // -- the eliminator (§8) ------------------------------------------------

    /// `match` on a forded family (§8): one recursion on the **skeleton** at
    /// the fording motive `Q`, with the index and the stored proof consumed by
    /// the two trailing applications.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_forded(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &FordedFam,
        arms: &[Arm],
        scrut: Term,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let n = ind.ctors.len();
        let mut ordered: Vec<Option<&Arm>> = vec![None; n];
        for a in arms {
            let Some(i) = ind.ctors.iter().position(|c| c.name == a.ctor) else {
                return err(
                    format!("`{}` is not a constructor of `{}`", a.ctor, ind.name),
                    a.span,
                );
            };
            if ordered[i].replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
            if a.binders.len() != ind.ctors[i].fields.len() {
                return err(
                    format!(
                        "`{}` binds {} field(s), found {}",
                        a.ctor,
                        ind.ctors[i].fields.len(),
                        a.binders.len()
                    ),
                    a.span,
                );
            }
        }
        let missing: Vec<&str> = ordered
            .iter()
            .enumerate()
            .filter(|(_, a)| a.is_none())
            .map(|(i, _)| ind.ctors[i].name.as_str())
            .collect();
        if !missing.is_empty() {
            return err(
                format!("`match` is missing an arm for `{}`", missing.join("`, `")),
                span,
            );
        }

        let skel = ind.skel.as_ref().expect("forded");
        let l = fam.level.clone();
        let li = fam.ilvl.clone();
        let ql = Level::max(li.clone(), mlvl.clone());
        let gamma0 = cx.gamma.clone();
        let mot_at = |m: Term, z: Term, extra: u32| -> Type {
            motive.apply_local(&embed(&gamma0, extra).extended(Rc::new(m)).extended(Rc::new(z)))
        };

        // Q(σ) = Π(m' : I). Π(e' : sEq(I; μ σ; m')). M[m', ⟨σ, e'⟩], over (Γ, σ).
        let q = Type::Pi {
            dom_level: li.clone(),
            cod_level: ql.clone(),
            dom: Rc::new(fam.ity.shift_local(1)),
            cod: Rc::new(Type::Pi {
                dom_level: li.clone(),
                cod_level: mlvl.clone(),
                dom: Rc::new(fam.eq_at(
                    Term::Var(LocalVar(1)),
                    Term::Var(LocalVar(0)),
                    2,
                )),
                cod: Rc::new(mot_at(
                    Term::Var(LocalVar(1)),
                    fam.pair_at(
                        Term::Var(LocalVar(1)),
                        Term::Var(LocalVar(2)),
                        Term::Var(LocalVar(0)),
                        3,
                    ),
                    3,
                )),
            }),
        };
        let dec = self.descends_on_param(cx, &scrut);
        let idx_param = match (&dec, &*fam.idx) {
            (Some(_), Term::Var(LocalVar(i))) => {
                let pos = cx.names.len() - 1 - *i as usize;
                cx.selfref.as_ref().filter(|s| pos < s.params.len()).map(|_| pos)
            }
            _ => None,
        };
        let env = ArmEnv {
            ind,
            fam,
            ordered: &ordered,
            motive: &motive,
            gamma0: &gamma0,
            mlvl: &mlvl,
            ql: &ql,
            li: &li,
            q: &q,
            dec,
            idx_param,
            outer_guard: cx.guard.clone(),
        };

        let s_val = fam.fst_at((*fam.idx).clone(), scrut.clone(), 0);
        let recursion = if skel.recursive {
            let body = |bcx: &Cx,
                        tel: &Tel,
                        k: usize,
                        value: &Rc<Term>,
                        d_body: u32,
                        _e: &Type|
             -> R<Term> {
                let Type::Wf { level, shape, arity } = fam.skel_ty.shift_local(d_body) else {
                    return err("internal: a recursive skeleton did not lower to a `Wf`", span);
                };
                let sh = Term::Supf {
                    level,
                    shape,
                    arity,
                    label: Rc::new(inject(
                        &tel.spine,
                        k,
                        ind.ctors.len(),
                        (**value).clone(),
                        d_body,
                    )),
                    children: Rc::new(Term::Var(LocalVar(1))),
                };
                self.forded_arm(bcx, &env, k, Some(tel), value, d_body, &sh)
            };
            self.build_elim_wf(
                cx,
                skel,
                &fam.skel_ty,
                q.clone(),
                ql.clone(),
                s_val.clone(),
                &Branches::Custom(&body),
                None,
                span,
            )?
        } else {
            let spine = self.spine(&fam.skel_ty, &l, n, span)?;
            let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _e: &Type| -> R<Term> {
                let sh = inject(&spine, k, n, (**value).clone(), d);
                self.forded_arm(bcx, &env, k, None, value, d, &sh)
            };
            self.idx_case_tree(
                cx,
                &spine,
                n,
                0,
                q.clone(),
                &ql,
                Rc::new(s_val.clone()),
                0,
                &body,
            )?
        };
        // …applied at the index and the stored proof.
        let r1 = Term::App {
            fun: Rc::new(recursion),
            dom_level: li.clone(),
            cod_level: ql.clone(),
            dom: Rc::new(fam.ity.clone()),
            cod: Rc::new(Type::Pi {
                dom_level: li.clone(),
                cod_level: mlvl.clone(),
                dom: Rc::new(fam.eq_at(s_val.shift_local(1), Term::Var(LocalVar(0)), 1)),
                cod: Rc::new(mot_at(
                    Term::Var(LocalVar(1)),
                    fam.pair_at(
                        Term::Var(LocalVar(1)),
                        s_val.shift_local(2),
                        Term::Var(LocalVar(0)),
                        2,
                    ),
                    2,
                )),
            }),
            arg: Rc::clone(&fam.idx),
        };
        Ok(Term::App {
            fun: Rc::new(r1),
            dom_level: li,
            cod_level: mlvl,
            dom: Rc::new(fam.eq_at(s_val.clone(), (*fam.idx).clone(), 0)),
            cod: Rc::new(mot_at(
                fam.idx.shift_local(1),
                fam.pair_at(
                    fam.idx.shift_local(1),
                    s_val.shift_local(1),
                    Term::Var(LocalVar(0)),
                    1,
                ),
                1,
            )),
            arg: Rc::new(fam.snd_at((*fam.idx).clone(), scrut, 0)),
        })
    }

    /// One arm of §8, in whichever form §8.2's rule gives its constructor.
    #[allow(clippy::too_many_arguments)]
    fn forded_arm(
        &self,
        bcx: &Cx,
        env: &ArmEnv,
        k: usize,
        tel: Option<&Tel>,
        value: &Rc<Term>,
        d: u32,
        sh: &Term,
    ) -> R<Term> {
        match self.arm_form(env.ind, k) {
            Form::B => self.forded_arm_b(bcx, env, k, tel, value, d, sh),
            f => self.forded_arm_a(bcx, env, k, tel, value, d, sh, f),
        }
    }

    /// §8.2's rule, mechanized: form A exactly when the constructor would have
    /// been route-1-eligible on its own — `e_c = 0` with no children, or
    /// `e_c = Succ(x)` with `x` the index variable of its one child. `Nat`
    /// only this round (§14.4).
    fn arm_form(&self, ind: &Inductive, k: usize) -> Form {
        if !matches!(ind.index_ty, Some(IdxTy::Nat)) {
            return Form::B;
        }
        let ctor = &ind.ctors[k];
        let kids = ctor.arity();
        let e = self.res_expr(ind, k);
        match &e.kind {
            ExprKind::Num(0) if kids == 0 => Form::AZero,
            ExprKind::Var(v) if v == "Zero" && kids == 0 => Form::AZero,
            ExprKind::App { head, args, .. }
                if kids == 1 && matches!(&head.kind, ExprKind::Var(s) if s == "Succ") =>
            {
                match args.as_slice() {
                    [Expr { kind: ExprKind::Var(v), .. }] => {
                        let at = ctor
                            .fields
                            .iter()
                            .position(|(n, _)| n.as_deref() == Some(v.as_str()));
                        match at {
                            Some(j)
                                if ctor.kind[j] == FieldKind::IndexVar
                                    && ctor.rec_at.contains(&Some(j)) =>
                            {
                                Form::ASucc
                            }
                            _ => Form::B,
                        }
                    }
                    _ => Form::B,
                }
            }
            _ => Form::B,
        }
    }

    /// §8.3, the transp arm — the form available at any index.
    ///
    /// ```text
    /// λ(m'). λ(e'). transp(I; z. Π(e₀ : sEq(I; μ ŝ; z)). M[z, ⟨ŝ, e₀⟩];
    ///                      μ ŝ; m'; e'; λ(e₀). ⟦arm body⟧) e'
    /// ```
    ///
    /// The `Π`-motive is not decoration: `M[z, ⟨ŝ, ?⟩]` alone is unstateable,
    /// because the pair's second component's type depends on `z`.
    #[allow(clippy::too_many_arguments)]
    fn forded_arm_b(
        &self,
        bcx: &Cx,
        env: &ArmEnv,
        k: usize,
        tel: Option<&Tel>,
        value: &Rc<Term>,
        d: u32,
        sh: &Term,
    ) -> R<Term> {
        let fam = env.fam;
        let mu_s = |j: u32| fam.mu_at(sh.shift_local(j), d + j);
        let mut mcx = bcx.clone();
        mcx.push("#idx".into(), fam.ity.shift_local(d), env.li.clone());
        let mut ecx = mcx.clone();
        ecx.push(
            "#eq".into(),
            fam.eq_at(sh.shift_local(1), Term::Var(LocalVar(0)), d + 1),
            env.li.clone(),
        );
        let mut zcx = ecx.clone();
        zcx.push(
            "#eq0".into(),
            fam.eq_at(sh.shift_local(2), mu_s(2), d + 2),
            env.li.clone(),
        );
        let body = self.forded_arm_body(
            &zcx,
            env,
            k,
            tel,
            value,
            d,
            sh,
            3,
            mu_s(3),
            Term::Var(LocalVar(0)),
            None,
        )?;
        let motive = Type::Pi {
            dom_level: env.li.clone(),
            cod_level: env.mlvl.clone(),
            dom: Rc::new(fam.eq_at(sh.shift_local(3), Term::Var(LocalVar(0)), d + 3)),
            cod: Rc::new(env.mot_at(
                Term::Var(LocalVar(1)),
                fam.pair_at(
                    Term::Var(LocalVar(1)),
                    sh.shift_local(4),
                    Term::Var(LocalVar(0)),
                    d + 4,
                ),
                d + 4,
            )),
        };
        let tm = Term::Lam {
            dom_level: env.li.clone(),
            cod_level: env.mlvl.clone(),
            dom: Rc::new(fam.eq_at(sh.shift_local(2), mu_s(2), d + 2)),
            body: Rc::new(body),
        };
        let transp = Term::Transp {
            ty_level: env.li.clone(),
            motive_level: env.ql.clone(),
            ty: Rc::new(fam.ity.shift_local(d + 2)),
            motive: Rc::new(motive),
            lhs: Rc::new(mu_s(2)),
            rhs: Rc::new(Term::Var(LocalVar(1))),
            proof: Rc::new(Term::Var(LocalVar(0))),
            tm: Rc::new(tm),
        };
        Ok(Term::Lam {
            dom_level: env.li.clone(),
            cod_level: env.ql.clone(),
            dom: Rc::new(fam.ity.shift_local(d)),
            body: Rc::new(Term::Lam {
                dom_level: env.li.clone(),
                cod_level: env.mlvl.clone(),
                dom: Rc::new(fam.eq_at(sh.shift_local(1), Term::Var(LocalVar(0)), d + 1)),
                body: Rc::new(Term::App {
                    fun: Rc::new(transp),
                    dom_level: env.li.clone(),
                    cod_level: env.mlvl.clone(),
                    dom: Rc::new(fam.eq_at(
                        sh.shift_local(2),
                        Term::Var(LocalVar(1)),
                        d + 2,
                    )),
                    cod: Rc::new(env.mot_at(
                        Term::Var(LocalVar(2)),
                        fam.pair_at(
                            Term::Var(LocalVar(2)),
                            sh.shift_local(3),
                            Term::Var(LocalVar(0)),
                            d + 3,
                        ),
                        d + 3,
                    )),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                }),
            }),
        })
    }

    /// §8.2, index inversion — the arm inverts the *motive's* index instead of
    /// consuming the stored proof, which is what makes β definitional on open
    /// data. The `j ≠ k` branch is no-confusion: `μ ŝ` is `I_k`-headed and the
    /// branch's index is not, so transporting the equation through the tag
    /// predicate lands in `Empty`.
    #[allow(clippy::too_many_arguments)]
    fn forded_arm_a(
        &self,
        bcx: &Cx,
        env: &ArmEnv,
        k: usize,
        tel: Option<&Tel>,
        value: &Rc<Term>,
        d: u32,
        sh: &Term,
        form: Form,
    ) -> R<Term> {
        let fam = env.fam;
        let mu_s = |j: u32| fam.mu_at(sh.shift_local(j), d + j);
        let mut mcx = bcx.clone();
        mcx.push("#idx".into(), fam.ity.shift_local(d), env.li.clone());
        // The `elim_Nat` motive, over (…, m', ẑ).
        let nmot = Type::Pi {
            dom_level: env.li.clone(),
            cod_level: env.mlvl.clone(),
            dom: Rc::new(fam.eq_at(sh.shift_local(2), Term::Var(LocalVar(0)), d + 2)),
            cod: Rc::new(env.mot_at(
                Term::Var(LocalVar(1)),
                fam.pair_at(
                    Term::Var(LocalVar(1)),
                    sh.shift_local(3),
                    Term::Var(LocalVar(0)),
                    d + 3,
                ),
                d + 3,
            )),
        };
        // The absurd branch: `elim_Empty` at the equation transported through
        // the tag predicate.
        let absurd_branch = |unit_at_zero: bool, at: Term, by: u32, goal: Type| -> Term {
            Term::ElimEmpty {
                level: env.mlvl.clone(),
                scrut_level: Level::Zero,
                motive: Rc::new(goal.shift_local(1)),
                scrut: Rc::new(Term::Transp {
                    ty_level: env.li.clone(),
                    motive_level: Level::constant(0),
                    ty: Rc::new(Type::Nat),
                    motive: Rc::new(Type::El {
                        level: Level::constant(0),
                        tm: Rc::new(tag_pred(Term::Var(LocalVar(0)), unit_at_zero)),
                    }),
                    lhs: Rc::new(mu_s(by)),
                    rhs: Rc::new(at),
                    proof: Rc::new(Term::Var(LocalVar(0))),
                    tm: Rc::new(Term::Triv { level: Level::Zero }),
                }),
            }
        };

        // -- the Zero branch, at depth d+2 (m', e') ---------------------------
        let base = {
            let mut ecx = mcx.clone();
            ecx.push(
                "#eq".into(),
                fam.eq_at(sh.shift_local(1), Term::Zero, d + 1),
                env.li.clone(),
            );
            let inner = if form == Form::AZero {
                self.forded_arm_body(
                    &ecx,
                    env,
                    k,
                    tel,
                    value,
                    d,
                    sh,
                    2,
                    Term::Zero,
                    Term::Var(LocalVar(0)),
                    None,
                )?
            } else {
                let goal = env.mot_at(
                    Term::Zero,
                    fam.pair_at(
                        Term::Zero,
                        sh.shift_local(2),
                        Term::Var(LocalVar(0)),
                        d + 2,
                    ),
                    d + 2,
                );
                absurd_branch(false, Term::Zero, 2, goal)
            };
            Term::Lam {
                dom_level: env.li.clone(),
                cod_level: env.mlvl.clone(),
                dom: Rc::new(fam.eq_at(sh.shift_local(1), Term::Zero, d + 1)),
                body: Rc::new(inner),
            }
        };

        // -- the Succ branch, at depth d+4 (m', kk, ihN, e') ------------------
        let step = {
            let mut scx = mcx.clone();
            scx.push("#pred".into(), Type::Nat, Level::Zero);
            scx.push("#ihN".into(), nmot.shift_local(0), env.mlvl.clone());
            let succ_k = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
            let mut ecx = scx.clone();
            ecx.push(
                "#eq".into(),
                fam.eq_at(sh.shift_local(3), succ_k.clone(), d + 3),
                env.li.clone(),
            );
            let inner = if form == Form::ASucc {
                self.forded_arm_body(
                    &ecx,
                    env,
                    k,
                    tel,
                    value,
                    d,
                    sh,
                    4,
                    // The branch stands at `m' = Succ(k)`, so the motive is
                    // instantiated there — **not** at the predecessor `k`,
                    // which is what the arm's index *binder* denotes. The two
                    // coincide nowhere, and a constant motive hides the
                    // difference completely. (`succ_k` is scoped at `d+3`;
                    // the body sits one binder deeper, under `e'`.)
                    succ_k.shift_local(1),
                    Term::Var(LocalVar(0)),
                    Some(()),
                )?
            } else {
                let succ2 = Term::Succ(Rc::new(Term::Var(LocalVar(2))));
                let goal = env.mot_at(
                    succ2.clone(),
                    fam.pair_at(
                        succ2.clone(),
                        sh.shift_local(4),
                        Term::Var(LocalVar(0)),
                        d + 4,
                    ),
                    d + 4,
                );
                absurd_branch(true, succ2, 4, goal)
            };
            Term::Lam {
                dom_level: env.li.clone(),
                cod_level: env.mlvl.clone(),
                dom: Rc::new(fam.eq_at(sh.shift_local(3), succ_k, d + 3)),
                body: Rc::new(inner),
            }
        };

        Ok(Term::Lam {
            dom_level: env.li.clone(),
            cod_level: env.ql.clone(),
            dom: Rc::new(fam.ity.shift_local(d)),
            body: Rc::new(nat_elim(
                nmot,
                env.ql.clone(),
                base,
                step,
                Term::Var(LocalVar(0)),
            )),
        })
    }

    /// The arm body itself (§8.1's table): the payload fields at their
    /// projections, each child-index field at its child's measure (or, in form
    /// A's `Succ` branch, at the inverted `k`), each child at
    /// `⟨child, proof⟩`, and a self-call at `ihQ_t index proof`.
    ///
    /// `j` is how many binders past the branch body this sits (form B: 3, form
    /// A: 2 or 4), `at_m` the index the motive is instantiated at, `at_e` the
    /// proof term in scope, and `inverted` marks form A's `Succ` branch — where
    /// the child's index binder is the `elim_Nat` predecessor and its proof is
    /// re-derived at `pred` rather than being `srefl`.
    #[allow(clippy::too_many_arguments)]
    fn forded_arm_body(
        &self,
        acx0: &Cx,
        env: &ArmEnv,
        k: usize,
        tel: Option<&Tel>,
        value: &Rc<Term>,
        d: u32,
        sh: &Term,
        j: u32,
        at_m: Term,
        at_e: Term,
        inverted: Option<()>,
    ) -> R<Term> {
        let fam = env.fam;
        let ind = env.ind;
        let ctor = &ind.ctors[k];
        let arm = env.ordered[k].expect("checked at entry");
        let span = arm.span;
        let dd = d + j;
        let m = ctor.arity();
        let mut acx = acx0.clone();
        let depth = acx.names.len();
        let ctor_ty = match tel {
            Some(tel) => tel.spine.ctors[k].0.shift_local(dd),
            None => self.ctor_spine_at(acx0, ind, k, dd, span)?,
        };
        let value_here = Rc::new(value.shift_local(j));
        // The `t`-th child of the skeleton: `nth(Skel; m; cs'; ι_t)` with `cs'`
        // at `Var(1 + j)` — the branch convention, `j` binders out.
        let child_of = |t: usize, extra: u32| -> Term {
            nth_child(
                &fam.level,
                &Rc::new(fam.skel_ty.shift_local(dd + extra)),
                m,
                t,
                Rc::new(Term::Var(LocalVar(1 + j + extra))),
                &Term::Zero,
            )
        };
        let mut children: Vec<(Rc<Term>, Rc<Term>, Type, Level)> = Vec::new();
        let mut rebind: Vec<Rc<Term>> = Vec::new();
        let (mut t, mut p) = (0usize, 0usize);
        // Two passes: the child-index fields first, since a child's own value
        // is stated at the index its variable denotes.
        let mut idx_of_child: Vec<Term> = Vec::with_capacity(m);
        let mut proof_of_child: Vec<Term> = Vec::with_capacity(m);
        for _ in 0..m {
            idx_of_child.push(Term::Zero);
            proof_of_child.push(Term::Zero);
        }
        {
            let mut ct = 0usize;
            for kind in &ctor.kind {
                if *kind != FieldKind::Plain {
                    continue;
                }
                let child = child_of(ct, 0);
                if inverted.is_some() {
                    // §8.2: the tail's proof is re-derived by `transp` at the
                    // `pred` motive; the stored proof is consulted nowhere.
                    let e_tail = Term::Transp {
                        ty_level: env.li.clone(),
                        motive_level: env.li.clone(),
                        ty: Rc::new(Type::Nat),
                        motive: Rc::new(Type::SEq {
                            level: env.li.clone(),
                            ty: Rc::new(Type::Nat),
                            lhs: Rc::new(fam.mu_at(child_of(ct, 1), dd + 1)),
                            rhs: Rc::new(pred(Term::Var(LocalVar(0)))),
                        }),
                        lhs: Rc::new(fam.mu_at(sh.shift_local(j), dd)),
                        rhs: Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(2))))),
                        proof: Rc::new(Term::Var(LocalVar(0))),
                        tm: Rc::new(fam.srefl_at(fam.mu_at(child.clone(), dd), dd)),
                    };
                    idx_of_child[ct] = Term::Var(LocalVar(2));
                    proof_of_child[ct] = e_tail;
                } else {
                    let mu_c = fam.mu_at(child.clone(), dd);
                    idx_of_child[ct] = mu_c.clone();
                    proof_of_child[ct] = fam.srefl_at(mu_c, dd);
                }
                ct += 1;
            }
        }

        for (fi, _) in ctor.fields.iter().enumerate() {
            let kind = ctor.kind[fi];
            let bname = arm.binders[fi].clone();
            match kind {
                FieldKind::IndexVar => {
                    let child = ctor
                        .rec_at
                        .iter()
                        .position(|a| *a == Some(fi))
                        .expect("an index variable indexes some child");
                    let ct = ctor.kind[..child]
                        .iter()
                        .filter(|x| **x == FieldKind::Plain)
                        .count();
                    acx.aliases.push(Rc::new(Alias {
                        name: bname,
                        depth,
                        term: Rc::new(idx_of_child[ct].clone()),
                        ty: fam.ity.shift_local(dd),
                        level: env.li.clone(),
                    }));
                }
                FieldKind::Plain => {
                    let child = child_of(t, 0);
                    let at = idx_of_child[t].clone();
                    let pf = proof_of_child[t].clone();
                    let val = fam.pair_at(at.clone(), child.clone(), pf.clone(), dd);
                    let ih = self.forded_ih(env, m, t, j, dd, at.clone(), pf);
                    let ih_ty = env.mot_at(at.clone(), val.clone(), dd);
                    acx.aliases.push(Rc::new(Alias {
                        name: bname,
                        depth,
                        term: Rc::new(val.clone()),
                        ty: fam.ty_at(at.clone(), dd),
                        level: fam.lvl(),
                    }));
                    children.push((
                        Rc::new(val),
                        Rc::new(ih),
                        ih_ty,
                        env.mlvl.clone(),
                    ));
                    rebind.push(Rc::new(at));
                    t += 1;
                }
                _ => {
                    let (term, ty, level) =
                        self.projection(&acx, &ctor_ty, &value_here, p, span)?;
                    acx.aliases.push(Rc::new(Alias { name: bname, depth, term, ty, level }));
                    p += 1;
                }
            }
        }
        if !children.is_empty() {
            acx.guard = env
                .dec
                .map(|dec| {
                    Rc::new(Guard {
                        dec,
                        kind: GuardKind::Wf { depth: acx.names.len(), children, container: None },
                        rebind: env.idx_param.map(|p| (p, rebind)),
                    })
                })
                .or_else(|| env.outer_guard.clone());
        }
        let goal = env.mot_at(
            at_m.clone(),
            fam.pair_at(at_m, sh.shift_local(j), at_e, dd),
            dd,
        );
        self.elab_check(&acx, &arm.body, &goal, env.mlvl)
    }

    /// `ihQ_t at proof` (§8.1's table): the ih the arm hands the user's case.
    #[allow(clippy::too_many_arguments)]
    fn forded_ih(
        &self,
        env: &ArmEnv,
        m: usize,
        t: usize,
        j: u32,
        dd: u32,
        at: Term,
        proof: Term,
    ) -> Term {
        let fam = env.fam;
        let len = Rc::new(nat_lit(m));
        let q_at = |x: Term, extra: u32| -> Type {
            env.q.apply_local(&embed(env.gamma0, extra).extended(Rc::new(x)))
        };
        let child_at = |extra: u32| -> Term {
            nth_child(
                &fam.level,
                &Rc::new(fam.skel_ty.shift_local(dd + extra)),
                m,
                t,
                Rc::new(Term::Var(LocalVar(1 + j + extra))),
                &Term::Zero,
            )
        };
        // `ih' ι_t : Q[child_t]`. The codomain is `ih'`'s own, so it mentions
        // the **bound** index (Var 0), not `ι_t`.
        let ihq = Term::App {
            fun: Rc::new(Term::Var(LocalVar(j))),
            dom_level: Level::Zero,
            cod_level: env.ql.clone(),
            dom: Rc::new(Type::Fin { len: Rc::clone(&len) }),
            cod: Rc::new(q_at(
                heather_kernel::term::nth(
                    &fam.level,
                    &Rc::new(fam.skel_ty.shift_local(dd + 1)),
                    &len,
                    Rc::new(Term::Var(LocalVar(1 + j + 1))),
                    Rc::new(Term::Var(LocalVar(0))),
                ),
                dd + 1,
            )),
            arg: Rc::new(fin_index(t, m, &Term::Zero)),
        };
        let child = child_at(0);
        let inner = Term::App {
            fun: Rc::new(ihq),
            dom_level: env.li.clone(),
            cod_level: env.ql.clone(),
            dom: Rc::new(fam.ity.shift_local(dd)),
            cod: Rc::new(Type::Pi {
                dom_level: env.li.clone(),
                cod_level: env.mlvl.clone(),
                dom: Rc::new(fam.eq_at(child_at(1), Term::Var(LocalVar(0)), dd + 1)),
                cod: Rc::new(env.mot_at(
                    Term::Var(LocalVar(1)),
                    fam.pair_at(
                        Term::Var(LocalVar(1)),
                        child_at(2),
                        Term::Var(LocalVar(0)),
                        dd + 2,
                    ),
                    dd + 2,
                )),
            }),
            arg: Rc::new(at.clone()),
        };
        Term::App {
            fun: Rc::new(inner),
            dom_level: env.li.clone(),
            cod_level: env.mlvl.clone(),
            dom: Rc::new(fam.eq_at(child.clone(), at.clone(), dd)),
            cod: Rc::new(env.mot_at(
                at.shift_local(1),
                fam.pair_at(
                    at.shift_local(1),
                    child.shift_local(1),
                    Term::Var(LocalVar(0)),
                    dd + 1,
                ),
                dd + 1,
            )),
            arg: Rc::new(proof),
        }
    }
}

/// Everything an arm needs beyond its own binders, gathered once.
struct ArmEnv<'a> {
    ind: &'a Inductive,
    fam: &'a FordedFam,
    ordered: &'a [Option<&'a Arm>],
    motive: &'a Type,
    gamma0: &'a LocalCtx,
    mlvl: &'a Level,
    ql: &'a Level,
    li: &'a Level,
    q: &'a Type,
    dec: Option<usize>,
    idx_param: Option<usize>,
    outer_guard: Option<Rc<Guard>>,
}

impl ArmEnv<'_> {
    /// `M[m, z]`, with `m`/`z` scoped `extra` binders past Γ.
    fn mot_at(&self, m: Term, z: Term, extra: u32) -> Type {
        self.motive
            .apply_local(&embed(self.gamma0, extra).extended(Rc::new(m)).extended(Rc::new(z)))
    }
}
