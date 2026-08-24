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

#[cfg(test)]
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_syntax::ast::{Arm, Expr, ExprKind, MatchForm, Span};

use crate::gendefs::GenDef;
use crate::indexed::{set_scrut, wf_ih_at};
use crate::inductive::{
    inject, nat_lit, tag_value, ConstBody, FieldKind, IdxTy, Inductive, Spine,
};
use crate::wf::{fin_index, nth_child, Branches, Tel};
use crate::recursion::{Guard, GuardKind};
use crate::{embed, err, Alias, Cx, Elaborator, R};

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
    /// `El (D#code^δ)` — the **reference** spelling of `⟦Skel⟧`, present when
    /// the skeleton's code definition was registered
    /// (`docs/family-type-code-defs-design.md` §1.4/§3.1). Emission uses it;
    /// every structural read keeps operating on the inline `skel_ty`.
    pub skel_ref: Option<Type>,
    /// `El (I#icode^δ)` — the reference spelling of `I`, same contract.
    pub ity_ref: Option<Type>,
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

    /// `⟦Skel⟧` as **emitted** at `by`: the `El (D#code^δ)` reference when the
    /// definition exists, the inline copy otherwise (design §3.1's line —
    /// structure is read from `skel_ty`; the reference exists only in what
    /// gets emitted).
    pub fn skel_emit(&self, by: u32) -> Type {
        self.skel_ref.as_ref().unwrap_or(&self.skel_ty).shift_local(by)
    }

    /// `I` as emitted at `by`, same contract as [`Self::skel_emit`].
    pub fn ity_emit(&self, by: u32) -> Type {
        self.ity_ref.as_ref().unwrap_or(&self.ity).shift_local(by)
    }

    /// `sEq^{li}(I; μ s; m)` at `by`.
    pub fn eq_at(&self, s: Term, m: Term, by: u32) -> Type {
        Type::SEq {
            level: self.ilvl.clone(),
            ty: Rc::new(self.ity_emit(by)),
            lhs: Rc::new(self.mu_at(s, by)),
            rhs: Rc::new(m),
        }
    }

    /// `srefl^{li}(I; t)` at `by`.
    pub fn srefl_at(&self, t: Term, by: u32) -> Term {
        Term::SRefl {
            level: self.ilvl.clone(),
            ty: Rc::new(self.ity_emit(by)),
            tm: Rc::new(t),
        }
    }

    /// `Σ^{l,li}(s : Skel). sEq^{li}(I; μ s; m)` at `by`, with `m` scoped at
    /// `by` (the Σ's second component binds, so `m` moves out by one there).
    pub fn ty_at(&self, m: Term, by: u32) -> Type {
        Type::Sigma {
            fst_level: self.level.clone(),
            snd_level: self.ilvl.clone(),
            fst: Rc::new(self.skel_emit(by)),
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
#[derive(Clone, PartialEq, Eq)]
enum Form {
    /// `e_c = 0` with no children: the motive's index is inverted by
    /// `elim_Nat` and the stored proof is consulted nowhere.
    AZero,
    /// `e_c = Succ(x)` with `x` the index variable of this constructor's one
    /// child: the same inversion, with the tail's proof re-derived at `pred`.
    ASucc,
    /// `e_c = I_k(x̄)` at a **declared** index, with `x̄` distinct child-index
    /// variables filling *all* of `I_k`'s arguments (§8.2, generated since
    /// 2026-08-04): the motive's index is inverted by the index type's own
    /// eliminator — a `Case` tree at a flat index, `elim_Wf` at a recursive
    /// one — the `j ≠ k` branches land in `Empty` through `wf.rs` §7.1's tag
    /// predicate, and each child's index binder is the *index constructor's*
    /// own argument, its equation re-derived through §7.2's `child_projection`.
    ///
    /// `at` is the index constructor, and `args[t]` which of its arguments
    /// child `t` sits at.
    ADecl { at: usize, args: Vec<usize> },
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
        // The Σ's first component is either the inline skeleton — the tag
        // comes out of it, where `tag_of` already looks — or, since
        // `docs/family-type-code-defs-design.md`, the **reference**
        // `El (D#code^δ)`. A reference is identified *only* by resolving
        // through the registry to this declaration's `SkelCode` — a lookup,
        // not a reduction: an `El` of any *other* global (another
        // declaration's code, a user-written global with a byte-identical
        // body) is `None` here, which is `mod fingerprint`'s look-alike
        // discipline extended to types (design §3.1, §4).
        let referenced = |t: &Type| -> Option<GenDef> {
            let Type::El { tm, .. } = t else { return None };
            let Term::GlobalTm { var, .. } = &**tm else { return None };
            self.gen_def_of(*var)
        };
        let el_of_global = |t: &Type| -> bool {
            matches!(t, Type::El { tm, .. } if matches!(&**tm, Term::GlobalTm { .. }))
        };
        let fst_is_ref = el_of_global(&fst);
        let ind = if fst_is_ref {
            let GenDef::SkelCode(tag) = referenced(&fst)? else { return None };
            Rc::clone(self.types.by_tag(tag)?)
        } else {
            let skel = self.tag_of(&fst)?;
            Rc::clone(self.types.forded_by_skeleton(skel.tag)?)
        };
        // The `sEq`'s `ty` slot, same rule: an `El`-of-global there must be
        // **this** declaration's index-type code and nothing else. An inline
        // `I` (a `Nat` index, a pre-unfolded occurrence, a parameterized
        // family) takes the structural path unchanged — §14.12's coexistence
        // rule, extended.
        let ity_is_ref = el_of_global(&ity);
        if ity_is_ref {
            let GenDef::IdxCode(itag) = referenced(&ity)? else { return None };
            let Some(IdxTy::Decl(iind)) = ind.index_ty.as_ref() else { return None };
            if iind.tag != itag {
                return None;
            }
        }
        // …and the `μ` slot is checked by **name** (§14.1, re-keyed
        // 2026-08-04 by `issues/generated-term-defs.md`): where the
        // declaration has a registered `μ_D`, the `sEq`'s left-hand side must
        // be that definition applied to the Σ binder, and nothing else — not
        // another global, not a look-alike written out by hand. Where it has
        // none (a parameterized family keeps its inlined `μ`, `gendefs.rs`)
        // the old structural read stands, unchanged.
        let key = GenDef::Mu(ind.tag);
        if self.gen_ref(cx, key).is_some() {
            let Term::App { fun, .. } = &*lhs else { return None };
            if !self.is_gen_ref(fun, key) {
                return None;
            }
        }
        // The Σ's second component is scoped under the binder; `μ`, `I` and the
        // index all mention it nowhere, so substituting a closed term for it is
        // exactly the un-shift back to the ambient context.
        let down = LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero));
        if fst_is_ref || ity_is_ref {
            // A reference-spelled component means the `skel_ty`/`ity` just
            // read are *not* the inline types every structural consumer
            // downstream (`spine`, the `Wf` destructurings) operates on. The
            // declaration is known and unparameterized (a code definition
            // exists only for one — gendefs.rs), so rebuild through the
            // generator's own builder: conservative by design §1.3, because
            // δ plus full decode of the reference is exactly what
            // `forded_fam` builds inline.
            let idx = rhs.apply_local(&down);
            let fam = self
                .forded_fam(cx, &ind, &[], idx, Span { start: 0, end: 0 })
                .ok()?;
            return Some((ind, fam));
        }
        let node = set_scrut(&lhs, Rc::new(Term::Zero))?;
        // A pre-unfolded occurrence (design §4's free case) still gets the
        // reference spellings for whatever it *emits*, when the defs exist.
        let skel_ref = self.gen_type_ref(cx, GenDef::SkelCode(ind.tag), &fst_level);
        let ity_ref = match ind.index_ty.as_ref() {
            Some(IdxTy::Decl(iind)) => {
                self.gen_type_ref(cx, GenDef::IdxCode(iind.tag), &ilvl)
            }
            _ => None,
        };
        Some((
            ind,
            FordedFam {
                level: fst_level,
                ilvl,
                ity: ity.apply_local(&down),
                skel_ty: (*fst).clone(),
                mu: Rc::new(node.apply_local(&down)),
                idx: Rc::new(rhs.apply_local(&down)),
                skel_ref,
                ity_ref,
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
        let oracle = self.semantic_oracle();
        for tm in oracle.term_reducts(&cx.gamma, tm, 1024) {
            let tm = Rc::new(tm);
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
        let _scope = self.use_inductive_scope(ind);
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
        // The two **code** references (design §1.4): `El (D#code^δ)` for the
        // skeleton, `El (I#icode^δ)` for a declared index type. `None` — a
        // parameterized declaration, or a registration that was skipped —
        // means every emission site below falls back to the inline copy.
        let skel_ref = self.gen_type_ref(cx, GenDef::SkelCode(ind.tag), &l);
        let ity_ref = match ind.index_ty.as_ref() {
            Some(IdxTy::Decl(iind)) => {
                self.gen_type_ref(cx, GenDef::IdxCode(iind.tag), &ilvl)
            }
            _ => None,
        };
        // §14.2, closed: `μ` is a Ψ definition, referenced rather than written
        // out. `mu` is still "the node with a placeholder scrutinee" — the
        // node is now `μ_D^δ □` and the placeholder is its argument — so
        // everything downstream (`mu_at`, `eq_at`, the recognizer) is
        // unchanged. Where no definition was registered (a *parameterized*
        // forded family, `gendefs.rs`'s boundary note) the old inlined node is
        // built exactly as before. The application's `dom`/`cod` annotations
        // are emitted at every μ mention, so they take the references too.
        let mu = match self.gen_ref(cx, GenDef::Mu(ind.tag)) {
            Some(f) => Self::gen_app(
                f,
                &l,
                &ilvl,
                skel_ref.as_ref().unwrap_or(&skel_ty),
                ity_ref.as_ref().unwrap_or(&ity),
                Term::Zero,
            ),
            None => self.build_mu(cx, ind, skel, &skel_ty, &l, &ity, &ilvl, span)?,
        };
        Ok(FordedFam {
            level: l,
            ilvl,
            ity,
            skel_ty,
            mu: Rc::new(mu),
            idx: Rc::new(idx),
            skel_ref,
            ity_ref,
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
    pub(crate) fn build_mu(
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
        let _scope = self.use_inductive_scope(ind);
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
                let acx =
                    self.mu_branch_cx(bcx, ind, Some(tel), None, k, value, d_body, ity, ilvl, span)?;
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
                let acx =
                    self.mu_branch_cx(bcx, ind, None, Some(&spine), k, value, d, ity, ilvl, span)?;
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
        flat: Option<&Spine>,
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
        // Whichever of the two the caller has, the skeleton's tag spine is one
        // the caller **already lowered** — see [`Self::ctor_spine_at`] for why
        // it is not re-lowered here.
        let ctor_ty = match (tel, flat) {
            (Some(tel), _) => tel.spine.ctors[k].0.shift_local(d_body),
            (None, Some(spine)) => spine.ctors[k].0.shift_local(d_body),
            (None, None) => {
                return err("internal: a non-recursive skeleton branch has no spine", span)
            }
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
                    acx.aliases.push(Rc::new(Alias { skel: None,
                        name,
                        depth,
                        term: Rc::new(wf_ih_at(tel, m, ct, d_body)),
                        ty: ity.shift_local(d_body),
                        level: ilvl.clone(),
                    }));
                }
                _ => {
                    let (term, ty, level) = self.projection(&acx, &ctor_ty, value, p, span)?;
                    acx.aliases.push(Rc::new(Alias { skel: None, name, depth, term, ty, level }));
                    p += 1;
                }
            }
        }
        Ok(acx)
    }

    /// `⟦c_k⟧` of the **skeleton**, at a non-recursive skeleton, weakened by
    /// `d` — read out of `fam`'s *already lowered* `skel_ty`.
    ///
    /// It used to re-lower the skeleton here, `lower_instance(cx, skel, &[],
    /// …)`. That is right only for a monomorphic declaration: a skeleton
    /// inherits the family's type parameters, and lowering it at **no** type
    /// arguments leaves a field spelled `A` looking for a type variable that
    /// the fresh instantiation never bound. The leak was an "unknown type
    /// `A`" — a name-resolution message, from inside the generator, on the
    /// *first use of any constructor* of a parameterized forded family whose
    /// skeleton is non-recursive. Only that corner: a recursive skeleton goes
    /// through `tel.spine`, which the caller lowered at the right arguments,
    /// and a monomorphic one has nothing to lose. Found while writing the
    /// axis-2 control for `idx_case_tree`
    /// (`issues/dependent-motive-crossing-sweep.md`, 2026-08-05) — the control
    /// *is* "an open payload on a non-recursive forded skeleton", so the axis
    /// could not be varied until this was fixed.
    fn ctor_spine_at(&self, fam: &FordedFam, n: usize, k: usize, d: u32, span: Span) -> R<Type> {
        let spine = self.spine(&fam.skel_ty, &fam.level, n, span)?;
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
        let t = {
            let _scope = self.use_inductive_scope(ind);
            self.elab_check(&acx, self.res_expr(ind, i), &ity, &ilvl)?
        };
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
                    acx.aliases.push(Rc::new(Alias { skel: None,
                        name,
                        depth,
                        term: Rc::new(term),
                        ty: ity.clone(),
                        level: ilvl.clone(),
                    }));
                }
                FieldKind::Payload => {
                    if let Some((_, term, ty, level)) = pays.iter().find(|(j, ..)| *j == k) {
                        acx.aliases.push(Rc::new(Alias { skel: None,
                            name,
                            depth,
                            term: Rc::clone(term),
                            ty: ty.clone(),
                            level: level.clone(),
                        }));
                    } else if crate::inductive::expr_mentions(e, &name) {
                        let (term, ty, level) = self.elab_infer(cx, &args[k])?;
                        acx.aliases.push(Rc::new(Alias { skel: None,
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
                    fst_ty: Rc::new(fam.skel_emit(0)),
                    snd_ty: Rc::new(Type::Vec {
                        level: level.clone(),
                        elem: Rc::new(fam.skel_emit(1)),
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
        let target = {
            let _scope = self.use_inductive_scope(ind);
            self.elab_check(&acx, self.res_expr(ind, i), &fam.ity, &fam.ilvl)?
        };
        if self.committed_oracle().convert_term(
            &cx.gamma,
            Layer::Prog,
            &target,
            &fam.idx,
            &fam.ity,
            &fam.ilvl,
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
                ty: Rc::new(fam.ity_emit(0)),
                motive: Rc::new(Type::SEq {
                    level: fam.ilvl.clone(),
                    ty: Rc::new(fam.ity_emit(1)),
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
            acx.aliases.push(Rc::new(Alias { skel: None,
                name,
                depth: if bound { zcx.names.len() } else { cx.names.len() },
                term: Rc::clone(term),
                ty: ty.clone(),
                level: level.clone(),
            }));
        }
        let _scope = self.use_inductive_scope(ind);
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
        form: MatchForm,
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
            let Some(i) = crate::inductive::arm_ctor_index(ind, &a.ctor) else {
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
                format!(
                    "`{}` is missing an arm for `{}`",
                    form.keyword(),
                    missing.join("`, `")
                ),
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
            dom: Rc::new(fam.ity_emit(1)),
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
        let dec = crate::recursion::descends_on_param(cx, &scrut);
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
            dom: Rc::new(fam.ity_emit(0)),
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
            Form::ADecl { at, args } => {
                self.forded_arm_a_decl(bcx, env, k, tel, value, d, sh, at, &args)
            }
            f => self.forded_arm_a(bcx, env, k, tel, value, d, sh, f),
        }
    }

    /// §8.2's rule, mechanized: form A exactly when the constructor would have
    /// been route-1-eligible on its own — `e_c = 0` with no children,
    /// `e_c = Succ(x)` with `x` the index variable of its one child, or (at a
    /// declared index) `e_c = I_k(x̄)` with `x̄` distinct child-index variables
    /// at all of `I_k`'s arguments.
    fn arm_form(&self, ind: &Inductive, k: usize) -> Form {
        match ind.index_ty.as_ref() {
            Some(IdxTy::Nat) => self.arm_form_nat(ind, k),
            Some(IdxTy::Decl(iind)) => self.arm_form_decl(ind, k, iind),
            None => Form::B,
        }
    }

    /// [`Self::arm_form`] at `Nat`, unchanged since the generator round: the
    /// two primitive constructors, by shape.
    fn arm_form_nat(&self, ind: &Inductive, k: usize) -> Form {
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

    /// [`Self::arm_form`] at a **declared** index (§8.2, 2026-08-04): the
    /// result index is that index type's own constructor applied to distinct
    /// child-index variables, one per argument.
    ///
    /// Two conditions here are narrower than "route-1-eligible on its own",
    /// and both are recorded rather than assumed:
    ///
    /// - **every argument of `I_k` must be a recursive one.** A pattern
    ///   variable at a *payload* argument (`TS(n, x) : Tg(CS(n))`) is
    ///   route-1-eligible, but under fording that field is *stored in the
    ///   skeleton* (§4.2 stores only child indices nowhere), so the arm would
    ///   have to choose between the stored value and the inverted one, which
    ///   are related only by the irrelevant `sEq`. That is a scheme question,
    ///   not plumbing, so such a constructor takes form B;
    /// - **every child's index variable must appear in `e_c`.** Otherwise the
    ///   inversion binds nothing for it, and the constructor is not
    ///   route-1-eligible either (its child sits at no pattern variable).
    fn arm_form_decl(&self, ind: &Inductive, k: usize, iind: &Inductive) -> Form {
        let ctor = &ind.ctors[k];
        let e = self.res_expr(ind, k);
        let (name, args): (&str, &[Expr]) = match &e.kind {
            ExprKind::Var(v) => (v.as_str(), &[]),
            ExprKind::App { head, args, .. } => match &head.kind {
                ExprKind::Var(v) => (v.as_str(), args.as_slice()),
                _ => return Form::B,
            },
            _ => return Form::B,
        };
        let Some(at) = iind.ctors.iter().position(|c| c.name == name) else {
            return Form::B;
        };
        let ic = &iind.ctors[at];
        if ic.fields.len() != args.len() || ctor.arity() != args.len() {
            return Form::B;
        }
        if ic.kind.iter().any(|f| *f != FieldKind::Plain) {
            return Form::B;
        }
        // Which field of `c` fills each argument of `I_k`: a child-index
        // variable, and a different one each time (§8.2's "distinct").
        let mut fills: Vec<usize> = Vec::with_capacity(args.len());
        for a in args {
            let ExprKind::Var(v) = &a.kind else { return Form::B };
            let Some(fi) = ctor.fields.iter().position(|(n, _)| n.as_deref() == Some(v.as_str()))
            else {
                return Form::B;
            };
            if ctor.kind[fi] != FieldKind::IndexVar || fills.contains(&fi) {
                return Form::B;
            }
            fills.push(fi);
        }
        // …and, per child, which argument of `I_k` its index variable fills.
        let mut per_child = Vec::with_capacity(ctor.arity());
        for (f, kind) in ctor.kind.iter().enumerate() {
            if *kind != FieldKind::Plain {
                continue;
            }
            let ix = ctor.rec_at[f].expect("a child records its index variable");
            let Some(a) = fills.iter().position(|x| *x == ix) else { return Form::B };
            per_child.push(a);
        }
        Form::ADecl { at, args: per_child }
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
            ty: Rc::new(fam.ity_emit(d + 2)),
            motive: Rc::new(motive),
            lhs: Rc::new(mu_s(2)),
            rhs: Rc::new(Term::Var(LocalVar(1))),
            proof: Rc::new(Term::Var(LocalVar(0))),
            tm: Rc::new(tm),
        };
        Ok(Term::Lam {
            dom_level: env.li.clone(),
            cod_level: env.ql.clone(),
            dom: Rc::new(fam.ity_emit(d)),
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

    /// §8.2's tag predicate at a **declared** index: `is_k : I → Ty 0`, the
    /// code of `Unit` at index constructor `k` and of `Empty` at every other.
    ///
    /// This is `wf.rs` §7.1's device — `ConstBody::TagCode` under a
    /// constant-motive elimination — at a new client. `ity` and `spine` are
    /// scoped in the context the caller read them back in and `d` counts the
    /// binders pushed since; `scrut` is scoped in `cx`.
    #[allow(clippy::too_many_arguments)]
    fn idx_tag_pred(
        &self,
        cx: &Cx,
        iind: &Inductive,
        ity: &Type,
        ilvl: &Level,
        spine: &Spine,
        k: usize,
        scrut: Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Term> {
        let ty0 = Type::Ty(Level::Zero);
        let l1 = Level::succ(Level::Zero);
        // §14.9, closed: one definition per index constructor, shared by every
        // family over that index, instead of a whole `elim_Wf` per *other*
        // index constructor per arm.
        if let Some(f) = self.gen_ref(cx, GenDef::IdxTag(iind.tag, k)) {
            // The application's `dom` annotation is a copy of `I` per
            // no-confusion branch; spell it as the code reference where the
            // index type has one (design §1.4). `cx` is the innermost
            // context here, so the reference needs no further shift.
            let dom = self
                .gen_type_ref(cx, GenDef::IdxCode(iind.tag), ilvl)
                .unwrap_or_else(|| ity.shift_local(d));
            return Ok(Self::gen_app(f, ilvl, &l1, &dom, &ty0, (*scrut).clone()));
        }
        if iind.recursive {
            self.const_elim_wf(
                cx,
                iind,
                ity,
                spine,
                &ty0,
                &l1,
                scrut,
                &ConstBody::TagCode(k),
                d,
                span,
            )
        } else {
            self.const_case_tree(
                cx,
                spine,
                iind.ctors.len(),
                &ty0,
                &l1,
                scrut,
                &ConstBody::TagCode(k),
                0,
                d,
                span,
            )
        }
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
            // The one child's index binder is the `elim_Nat` predecessor, and
            // its equation is re-derived at `pred` — `Nat`'s instance of the
            // (index binder, child projection) pair every form-A branch owes.
            let inv = [(Term::Var(LocalVar(2)), pred(Term::Var(LocalVar(0))))];
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
                    Some(&inv),
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
            dom: Rc::new(fam.ity_emit(d)),
            body: Rc::new(nat_elim(
                nmot,
                env.ql.clone(),
                base,
                step,
                Term::Var(LocalVar(0)),
            )),
        })
    }

    /// §8.2 at a **declared** index (2026-08-04, §14.4's seam closed): the same
    /// inversion, carried by the index type's *own* eliminator.
    ///
    /// ```text
    /// arm_c = λ(m' : I). elim_I( ẑ. Π(e' : sEq(I; μ ŝ; ẑ)). M[ẑ, ⟨ŝ, e'⟩]
    ///                          ; branch k ↦ λe'. ⟦arm body⟧
    ///                          ; branch j ↦ λe'. elim_Empty(…; transp(…is_k…))
    ///                          ) (m')
    /// ```
    ///
    /// Which eliminator carries it is the index type's business and nothing
    /// else's — a `Case` tree at a flat index, `elim_Wf` at a recursive one —
    /// which is the same dispatch `indexed.rs` makes for the route-1 family
    /// (§8.2 of that document). Inside the matching branch the child-index
    /// binders are the index constructor's own arguments (`nth(cs'_I; ι_a)`,
    /// where route 1's *family* uses the very same term) and each child's
    /// equation is re-derived through `child_projection` at that argument.
    #[allow(clippy::too_many_arguments)]
    fn forded_arm_a_decl(
        &self,
        bcx: &Cx,
        env: &ArmEnv,
        k: usize,
        tel: Option<&Tel>,
        value: &Rc<Term>,
        d: u32,
        sh: &Term,
        at: usize,
        cargs: &[usize],
    ) -> R<Term> {
        let fam = env.fam;
        let span = env.ordered[k].expect("checked at entry").span;
        let Some(IdxTy::Decl(iind)) = env.ind.index_ty.as_ref() else {
            return err("internal: form A at a declared index without one", span);
        };
        let n_i = iind.ctors.len();
        let mut mcx = bcx.clone();
        mcx.push("#idx".into(), fam.ity.shift_local(d), env.li.clone());
        // The inversion motive, over (…, m', ẑ) — identical to `Nat`'s, which
        // is the point: the fording layer never inspects the index's recursion.
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
        // The index type's tag spine, scoped where `fam.ity` is: in Γ.
        let ispine = self.spine(&fam.ity, &fam.ilvl, n_i, span)?;
        if iind.recursive {
            let body = |bcx2: &Cx,
                        itel: &Tel,
                        jj: usize,
                        ivalue: &Rc<Term>,
                        d_body: u32,
                        _e: &Type|
             -> R<Term> {
                // `dz` is the branch body's depth past Γ: `mcx` sits at `d+1`.
                let dz = d + 1 + d_body;
                let Type::Wf { level, shape, arity } = fam.ity.shift_local(dz) else {
                    return err("internal: a recursive index did not lower to a `Wf`", span);
                };
                // ẑ_j = sup_f(ι_j(label); cs'_I), rebuilt from the branch's own
                // binders; its identity with the declared constructor is `Unit`
                // η, which conversion pays (route 1 §8.2 fact 2).
                // Its two slots take the shape/arity references where the index
                // type has them registered (`docs/wf-shape-code-design.md`
                // §4's last bullet): this is [[wf-shape-annotation-slots]]'s
                // *original* site — the `sup_f` an inversion rebuilds per index
                // branch, instantiated several times per branch across Θ(n)
                // branches. Not a measured workload of that round, so no claim
                // is made about the fixtures' exponent; the spelling is the
                // same one every other `Supf` takes.
                let (shape, arity) = match self.wf_slot_refs(bcx2, &shape, &arity) {
                    Some((s, a)) => (Rc::new(s), Rc::new(a)),
                    None => (shape, arity),
                };
                let zj = Term::Supf {
                    level,
                    shape,
                    arity,
                    label: Rc::new(inject(&itel.spine, jj, n_i, (**ivalue).clone(), d_body)),
                    children: Rc::new(Term::Var(LocalVar(1))),
                };
                self.forded_inv_branch(
                    bcx2, env, k, tel, value, d, sh, at, cargs, iind, &ispine, jj, dz, &zj,
                )
            };
            self.build_elim_wf(
                &mcx,
                iind,
                &fam.ity.shift_local(d + 1),
                nmot,
                env.ql.clone(),
                Term::Var(LocalVar(0)),
                &Branches::Custom(&body),
                None,
                span,
            )
            .map(|elim| self.idx_lam(env, fam, d, elim))
        } else {
            // A flat index: no children anywhere (an enum constructor has no
            // recursive argument), so the branch bodies are the arm body and
            // the no-confusion branches, and nothing projects.
            let body = |bcx2: &Cx, jj: usize, ivalue: &Rc<Term>, dz: u32, _e: &Type| -> R<Term> {
                let zj = inject(&ispine, jj, n_i, (**ivalue).clone(), dz);
                self.forded_inv_branch(
                    bcx2, env, k, tel, value, d, sh, at, cargs, iind, &ispine, jj, dz, &zj,
                )
            };
            self.idx_case_tree(
                &mcx,
                &ispine,
                n_i,
                0,
                nmot,
                &env.ql.clone(),
                Rc::new(Term::Var(LocalVar(0))),
                d + 1,
                &body,
            )
            .map(|elim| self.idx_lam(env, fam, d, elim))
        }
    }

    /// `λ(m' : I). …` — form A's outer binder, the one the inversion
    /// scrutinizes.
    fn idx_lam(&self, env: &ArmEnv, fam: &FordedFam, d: u32, body: Term) -> Term {
        Term::Lam {
            dom_level: env.li.clone(),
            cod_level: env.ql.clone(),
            dom: Rc::new(fam.ity_emit(d)),
            body: Rc::new(body),
        }
    }

    /// One branch of §8.2's inversion at a declared index: `λ(e'). …`, with
    /// the arm body at the constructor's own index constructor and
    /// no-confusion at every other.
    ///
    /// `dz` is the branch body's depth past Γ and `zj` the index it stands at,
    /// scoped there.
    #[allow(clippy::too_many_arguments)]
    fn forded_inv_branch(
        &self,
        bcx2: &Cx,
        env: &ArmEnv,
        k: usize,
        tel: Option<&Tel>,
        value: &Rc<Term>,
        d: u32,
        sh: &Term,
        at: usize,
        cargs: &[usize],
        iind: &Rc<Inductive>,
        ispine: &Spine,
        jj: usize,
        dz: u32,
        zj: &Term,
    ) -> R<Term> {
        let fam = env.fam;
        let span = env.ordered[k].expect("checked at entry").span;
        let eq = fam.eq_at(sh.shift_local(dz - d), zj.clone(), dz);
        let mut ecx = bcx2.clone();
        ecx.push("#eq".into(), eq.clone(), env.li.clone());
        // The arm body sits `j` binders past the *skeleton's* branch body.
        let j = dz + 1 - d;
        let inner = if jj == at {
            // Per child: the index binder — the index constructor's own
            // argument — and the projection that recovers it from a bound `z`.
            let m_i = iind.ctors[jj].arity();
            let mut inv: Vec<(Term, Term)> = Vec::with_capacity(cargs.len());
            let mut zcx = ecx.clone();
            zcx.push("#z".into(), fam.ity.shift_local(dz + 1), env.li.clone());
            for a in cargs {
                let bind = nth_child(
                    &fam.ilvl,
                    &Rc::new(fam.ity_emit(dz + 1)),
                    m_i,
                    *a,
                    // `cs'_I` is `Var 1` at the index branch body, so `Var 2`
                    // under `e'`.
                    Rc::new(Term::Var(LocalVar(2))),
                    &Term::Zero,
                );
                // §14.9, closed: the projection is a Ψ definition abstracted
                // over its default, so one `elim_Wf` serves every child of
                // every arm of every family over this index instead of one
                // per occurrence. The default below is still the *bound* `z`
                // and is passed as the definition's first argument.
                let proj = match self.gen_ref(&zcx, GenDef::IdxChild(iind.tag, jj, *a)) {
                    Some(f) => {
                        let ity = fam.ity_emit(dz + 2);
                        let inner = Type::Pi {
                            dom_level: fam.ilvl.clone(),
                            cod_level: fam.ilvl.clone(),
                            dom: Rc::new(ity.shift_local(1)),
                            cod: Rc::new(ity.shift_local(2)),
                        };
                        let applied = Term::App {
                            fun: Rc::new(f),
                            dom_level: fam.ilvl.clone(),
                            cod_level: fam.ilvl.clone(),
                            dom: Rc::new(ity.clone()),
                            cod: Rc::new(inner),
                            arg: Rc::new(Term::Var(LocalVar(0))),
                        };
                        Self::gen_app(
                            applied,
                            &fam.ilvl,
                            &fam.ilvl,
                            &ity,
                            &ity,
                            Term::Var(LocalVar(0)),
                        )
                    }
                    None => self.child_projection(
                    &zcx,
                    iind,
                    &fam.ity.shift_local(dz + 2),
                    &fam.ilvl,
                    jj,
                    *a,
                    // The default is reached at no index this arm ever sees —
                    // `μ ŝ` and `ẑ` are both `I_at`-headed — so any term of
                    // type `I` in scope will do, and the *bound* `z` is the
                    // cheapest one there is. `μ ŝ` would also type, and costs a
                    // whole inlined `μ` per off-branch of every projection of
                    // every child (§14.2): measured as `OutOfFuel` on the very
                    // first three-constructor index, not as a slow test.
                    Rc::new(Term::Var(LocalVar(0))),
                    Term::Var(LocalVar(0)),
                    span,
                    )?,
                };
                inv.push((bind, proj));
            }
            self.forded_arm_body(
                &ecx,
                env,
                k,
                tel,
                value,
                d,
                sh,
                j,
                zj.shift_local(1),
                Term::Var(LocalVar(0)),
                Some(&inv),
            )?
        } else {
            // No-confusion: `μ ŝ` is `I_at`-headed and this branch's index is
            // `I_jj`-headed, so the equation transports `⟨⟩` into `Empty`.
            let goal = env.mot_at(
                zj.shift_local(1),
                fam.pair_at(
                    zj.shift_local(1),
                    sh.shift_local(j),
                    Term::Var(LocalVar(0)),
                    dz + 1,
                ),
                dz + 1,
            );
            let mut zcx = ecx.clone();
            zcx.push("#z".into(), fam.ity.shift_local(dz + 1), env.li.clone());
            let tag = self.idx_tag_pred(
                &zcx,
                iind,
                &fam.ity,
                &fam.ilvl,
                ispine,
                at,
                Rc::new(Term::Var(LocalVar(0))),
                dz + 2,
                span,
            )?;
            Term::ElimEmpty {
                level: env.mlvl.clone(),
                scrut_level: Level::Zero,
                motive: Rc::new(goal.shift_local(1)),
                scrut: Rc::new(Term::Transp {
                    ty_level: env.li.clone(),
                    motive_level: Level::constant(0),
                    ty: Rc::new(fam.ity_emit(dz + 1)),
                    motive: Rc::new(Type::El {
                        level: Level::constant(0),
                        tm: Rc::new(tag),
                    }),
                    lhs: Rc::new(fam.mu_at(sh.shift_local(j), dz + 1)),
                    rhs: Rc::new(zj.shift_local(1)),
                    proof: Rc::new(Term::Var(LocalVar(0))),
                    tm: Rc::new(Term::Triv { level: Level::Zero }),
                }),
            }
        };
        Ok(Term::Lam {
            dom_level: env.li.clone(),
            cod_level: env.mlvl.clone(),
            dom: Rc::new(eq),
            body: Rc::new(inner),
        })
    }

    /// The arm body itself (§8.1's table): the payload fields at their
    /// projections, each child-index field at its child's measure (or, in a
    /// form-A branch, at the inverted index binder), each child at
    /// `⟨child, proof⟩`, and a self-call at `ihQ_t index proof`.
    ///
    /// `j` is how many binders past the branch body this sits, `at_m` the index
    /// the motive is instantiated at, `at_e` the proof term in scope, and
    /// `inverted` is form A's per-child pair: the index binder (scoped at
    /// `d + j`) and the child projection at a bound `z` (one deeper), through
    /// which the child's equation is re-derived rather than being `srefl`.
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
        inverted: Option<&[(Term, Term)]>,
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
            None => self.ctor_spine_at(fam, ind.ctors.len(), k, dd, span)?,
        };
        let value_here = Rc::new(value.shift_local(j));
        // The `t`-th child of the skeleton: `nth(Skel; m; cs'; ι_t)` with `cs'`
        // at `Var(1 + j)` — the branch convention, `j` binders out.
        let child_of = |t: usize, extra: u32| -> Term {
            nth_child(
                &fam.level,
                &Rc::new(fam.skel_emit(dd + extra)),
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
                if let Some(inv) = inverted {
                    // §8.2: the child's index binder is the *inverted* one, and
                    // its proof is re-derived by `transp` at that argument's
                    // projection — `pred` at `Nat`, `child_projection` at a
                    // declared index. The stored proof is consulted nowhere,
                    // which is what makes β definitional on open data.
                    let (bind, proj) = &inv[ct];
                    let e_child = Term::Transp {
                        ty_level: env.li.clone(),
                        motive_level: env.li.clone(),
                        ty: Rc::new(fam.ity_emit(dd)),
                        motive: Rc::new(Type::SEq {
                            level: env.li.clone(),
                            ty: Rc::new(fam.ity_emit(dd + 1)),
                            lhs: Rc::new(fam.mu_at(child_of(ct, 1), dd + 1)),
                            rhs: Rc::new(proj.clone()),
                        }),
                        lhs: Rc::new(fam.mu_at(sh.shift_local(j), dd)),
                        rhs: Rc::new(at_m.clone()),
                        proof: Rc::new(Term::Var(LocalVar(0))),
                        tm: Rc::new(fam.srefl_at(fam.mu_at(child.clone(), dd), dd)),
                    };
                    idx_of_child[ct] = bind.clone();
                    proof_of_child[ct] = e_child;
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
            let bname = arm.binders[fi].name().to_string();
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
                    acx.aliases.push(Rc::new(Alias { skel: None,
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
                    acx.aliases.push(Rc::new(Alias { skel: None,
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
                    acx.aliases.push(Rc::new(Alias { skel: None, name: bname, depth, term, ty, level }));
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
                &Rc::new(fam.skel_emit(dd + extra)),
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
                    &Rc::new(fam.skel_emit(dd + 1)),
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
            dom: Rc::new(fam.ity_emit(dd)),
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

#[cfg(test)]
mod decl_inversion {
    //! §8.2's inversion at a **declared** index, hand-composed against the real
    //! kernel — the tier discipline's prototype step for the round that made
    //! form A fire there (§14.4's seam).
    //!
    //! What is hand-composed here is the pair of *obligations* the arm builder
    //! then has to meet, and nothing else: the generator's own de Bruijn
    //! plumbing is §13.2's business and is exercised end to end from the
    //! surface in `crates/elab/tests/indexed_route_2b_gen.rs`.
    //!
    //!  1. **no-confusion at a declared index** — with `e` an `sEq` between two
    //!     *different* index constructors, transporting `⟨⟩` through the tag
    //!     predicate lands in `Empty`, so `elim_Empty` eliminates into anything.
    //!     At `Nat` this is `zero_pred`/`is_succ`; here it is `ConstBody::TagCode`
    //!     under `const_elim_wf`, which had never been used for this purpose;
    //!  2. **child-index recovery** — with `e : sEq(I; I_k(ā); I_k(x̄))`,
    //!     transporting `srefl` through `wf.rs` §7.2's `child_projection` at
    //!     argument `t` gives `sEq(I; a_t; x_t)`, which is the equation the arm's
    //!     child value needs. This is the step that replaces route 1's
    //!     `nth(cs'; ι)` *inside the equation*, and the one the doc called
    //!     unbuilt.
    //!
    //! Both are stated over an index type with **three** constructors and at
    //! **open** subjects (`docs/testing-generated-terms.md` axes 2 and 6): a
    //! two-constructor index emits no inner `Case`, and a closed subject makes
    //! every projection compute for the wrong reason.

    use super::*;
    use heather_kernel::term::GlobalCtx;
    use heather_kernel::typing::check_term;
    use heather_syntax::ast::Expr;

    const SPAN: Span = Span { start: 0, end: 0 };
    const SHAPE: &str = "inductive Shape { SLeaf, SBud(s: Shape), SNode(l: Shape, r: Shape) }";

    fn var(name: &str) -> Expr {
        Expr { kind: ExprKind::Var(name.into()), span: SPAN }
    }

    struct Proto {
        el: Elaborator,
        ind: Rc<Inductive>,
        ity: Type,
        ilvl: Level,
        spine: Spine,
        cx: Cx,
    }

    /// `Γ = (a, b, l, r : Shape)` — every subject open.
    fn proto() -> Proto {
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(SHAPE).expect("the index declaration elaborates");
        let ind = Rc::clone(el.types.inductive(&crate::names::qkey("main", "Shape")).expect("declared"));
        let cx0 = Cx::empty();
        let (ity, ilvl) = el.lower_instance(&cx0, &ind, &[], &[], SPAN).expect("lowers");
        let spine = el.spine(&ity, &ilvl, ind.ctors.len(), SPAN).expect("spine");
        let mut cx = cx0;
        for n in ["a", "b", "l", "r"] {
            cx.push(n.into(), ity.clone(), ilvl.clone());
        }
        Proto { el, ind, ity, ilvl, spine, cx }
    }

    impl Proto {
        /// `c(args)` at `Shape`, in `cx`.
        fn ctor(&self, i: usize, args: &[Expr]) -> Term {
            self.el
                .build_ctor(&self.cx, &self.ind, i, args, &self.ity, &self.ilvl, SPAN)
                .expect("a Shape constructor builds")
        }

        fn with(&self, name: &str, ty: Type, level: Level) -> Cx {
            let mut cx = self.cx.clone();
            cx.push(name.into(), ty, level);
            cx
        }

        fn check(&self, cx: &Cx, tm: &Term, ty: &Type, level: &Level) {
            check_term(
                self.el.psi(),
                0,
                Layer::Prog,
                &cx.gamma,
                tm,
                ty,
                level,
                self.el.fuel,
            )
            .unwrap_or_else(|e| panic!("does not check: {e:?}"));
        }

        fn conv(&self, cx: &Cx, a: &Term, b: &Term, ty: &Type, level: &Level) {
            conv_term(self.el.psi(), &cx.gamma, Layer::Prog, a, b, ty, level, self.el.fuel)
                .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
        }

        fn seq(&self, lhs: Term, rhs: Term, by: u32) -> Type {
            Type::SEq {
                level: self.ilvl.clone(),
                ty: Rc::new(self.ity.shift_local(by)),
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
            }
        }
    }

    // -- the two ingredients, separately ------------------------------------

    #[test]
    fn the_tag_predicate_separates_three_index_constructors() {
        let p = proto();
        let node = p.ctor(2, &[var("l"), var("r")]);
        let bud = p.ctor(1, &[var("a")]);
        let leaf = p.ctor(0, &[]);
        let ty0 = Type::Ty(Level::Zero);
        let l1 = Level::succ(Level::Zero);
        let unit = Term::TmUnit { level: Level::Zero };
        let empty = Term::TmEmpty { level: Level::Zero };
        // Nine cells: every predicate against every constructor, so a
        // projection that is off by one `Case` fails here and not three layers
        // up. `SNode`'s subjects are open throughout.
        for k in 0..3usize {
            for (j, subject) in [(0usize, &leaf), (1, &bud), (2, &node)] {
                let pred = p
                    .el
                    .idx_tag_pred(
                        &p.cx,
                        &p.ind,
                        &p.ity,
                        &p.ilvl,
                        &p.spine,
                        k,
                        Rc::new((*subject).clone()),
                        0,
                        SPAN,
                    )
                    .expect("the tag predicate builds");
                let want = if j == k { &unit } else { &empty };
                p.conv(&p.cx, &pred, want, &ty0, &l1);
            }
        }
    }

    #[test]
    fn the_child_projection_recovers_an_open_argument() {
        let p = proto();
        let node = p.ctor(2, &[var("l"), var("r")]);
        let bud = p.ctor(1, &[var("a")]);
        for (t, want) in [(0usize, "l"), (1, "r")] {
            let proj = p
                .el
                .child_projection(
                    &p.cx,
                    &p.ind,
                    &p.ity,
                    &p.ilvl,
                    2,
                    t,
                    Rc::new(bud.clone()),
                    node.clone(),
                    SPAN,
                )
                .expect("the child projection builds");
            // `l` is Var 1 and `r` is Var 0 of `(a, b, l, r)`.
            let v = Term::Var(LocalVar(if want == "l" { 1 } else { 0 }));
            p.conv(&p.cx, &proj, &v, &p.ity, &p.ilvl);
        }
    }

    // -- the two obligations the arm builder has to meet ---------------------

    #[test]
    fn no_confusion_at_a_declared_index_lands_in_empty() {
        // §8.2's `j ≠ k` branch: `μ ŝ` is `SBud`-headed, the branch's index is
        // `SNode`-headed, and the stored equation between them is absurd.
        let p = proto();
        let bud = p.ctor(1, &[var("a")]);
        let node = p.ctor(2, &[var("l"), var("r")]);
        let ecx = p.with("#e", p.seq(bud.clone(), node.clone(), 0), p.ilvl.clone());
        let zcx = {
            let mut cx = ecx.clone();
            cx.push("#z".into(), p.ity.clone(), p.ilvl.clone());
            cx
        };
        let tag = p
            .el
            .idx_tag_pred(
                &zcx,
                &p.ind,
                &p.ity,
                &p.ilvl,
                &p.spine,
                1,
                Rc::new(Term::Var(LocalVar(0))),
                2,
                SPAN,
            )
            .expect("builds");
        let absurd = Term::Transp {
            ty_level: p.ilvl.clone(),
            motive_level: Level::constant(0),
            ty: Rc::new(p.ity.shift_local(1)),
            motive: Rc::new(Type::El { level: Level::constant(0), tm: Rc::new(tag) }),
            lhs: Rc::new(bud.shift_local(1)),
            rhs: Rc::new(node.shift_local(1)),
            proof: Rc::new(Term::Var(LocalVar(0))),
            tm: Rc::new(Term::Triv { level: Level::Zero }),
        };
        let elim = Term::ElimEmpty {
            level: Level::Zero,
            scrut_level: Level::Zero,
            motive: Rc::new(Type::Nat),
            scrut: Rc::new(absurd),
        };
        p.check(&ecx, &elim, &Type::Nat, &Level::Zero);
    }

    #[test]
    fn a_child_index_is_recovered_through_the_projection() {
        // §8.2's matching branch: from `e : sEq(I; SNode(a, b); SNode(l, r))`,
        // the equation the arm's *first* child needs is `sEq(I; a; l)`, and the
        // way to it is `transp` through the child projection — `pred` at `Nat`,
        // `child_projection` here. Both arguments are checked, because a
        // projection at the wrong `Fin` index is exactly the defect axis 6
        // exists for.
        let p = proto();
        let bud = p.ctor(1, &[var("a")]);
        let lhs = p.ctor(2, &[var("a"), var("b")]);
        let rhs = p.ctor(2, &[var("l"), var("r")]);
        let ecx = p.with("#e", p.seq(lhs.clone(), rhs.clone(), 0), p.ilvl.clone());
        let mut zcx = ecx.clone();
        zcx.push("#z".into(), p.ity.clone(), p.ilvl.clone());
        // In `ecx = (a, b, l, r, e)`: `a` is Var 4, `b` is 3, `l` is 2, `r` is 1.
        for (t, child, want) in [(0usize, 4u32, 2u32), (1, 3, 1)] {
            let proj = p
                .el
                .child_projection(
                    &zcx,
                    &p.ind,
                    &p.ity,
                    &p.ilvl,
                    2,
                    t,
                    Rc::new(bud.shift_local(2)),
                    Term::Var(LocalVar(0)),
                    SPAN,
                )
                .expect("builds");
            let motive = Type::SEq {
                level: p.ilvl.clone(),
                ty: Rc::new(p.ity.shift_local(1)),
                lhs: Rc::new(Term::Var(LocalVar(child + 1))),
                rhs: Rc::new(proj),
            };
            let tm = Term::Transp {
                ty_level: p.ilvl.clone(),
                motive_level: p.ilvl.clone(),
                ty: Rc::new(p.ity.clone()),
                motive: Rc::new(motive),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(rhs.shift_local(1)),
                proof: Rc::new(Term::Var(LocalVar(0))),
                tm: Rc::new(Term::SRefl {
                    level: p.ilvl.clone(),
                    ty: Rc::new(p.ity.clone()),
                    tm: Rc::new(Term::Var(LocalVar(child))),
                }),
            };
            let goal = Type::SEq {
                level: p.ilvl.clone(),
                ty: Rc::new(p.ity.clone()),
                lhs: Rc::new(Term::Var(LocalVar(child))),
                rhs: Rc::new(Term::Var(LocalVar(want))),
            };
            p.check(&ecx, &tm, &goal, &p.ilvl);
        }
        let _ = GlobalCtx::default();
    }
}

#[cfg(test)]
mod fingerprint {
    //! §14.1's seam, **closed 2026-08-04** by `issues/generated-term-defs.md`.
    //!
    //! `forded_of` used to read the `sEq`'s left-hand side purely
    //! structurally: anything with a scrutinee slot in that position was `μ`,
    //! and the declaration's identity came from the skeleton's tag alone. The
    //! seam list predicted that "any pass that normalizes or restructures
    //! emitted terms (a kernel `def`, …) breaks it, and the symptom is 'not a
    //! forded family' far from the cause" — and it also left the reader
    //! credulous in the other direction, since a Σ over the right skeleton
    //! with the *wrong* measure in the `μ` slot read back as the family.
    //!
    //! The key is now nominal: the slot must be **this declaration's** `μ_D`,
    //! the definition registered at its declaration (`gendefs.rs`). The two
    //! tests below are the two directions of that.

    use super::*;
    use heather_kernel::term::GlobalVar;

    const SPAN: Span = Span { start: 0, end: 0 };

    /// Two forded families over `Nat`, structurally identical apart from
    /// their nominal tags — which is what makes the negative below a genuine
    /// look-alike rather than a straw man.
    const SRC: &str = "
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
inductive F : (n: Nat) -> Type {
    F0                                : F(0),
    F1(n: Nat, x: Nat, t: F(n))       : F(Succ(add(n, 1))),
}
inductive G : (n: Nat) -> Type {
    G0                                : G(0),
    G1(n: Nat, x: Nat, t: G(n))       : G(Succ(add(n, 1))),
}
";

    struct Two {
        el: Elaborator,
        f: Rc<Inductive>,
        g: Rc<Inductive>,
        cx: Cx,
    }

    fn two() -> Two {
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(SRC).expect("two forded families elaborate");
        let f = Rc::clone(el.types.inductive(&crate::names::qkey("main", "F")).expect("declared"));
        let g = Rc::clone(el.types.inductive(&crate::names::qkey("main", "G")).expect("declared"));
        Two { el, f, g, cx: Cx::empty() }
    }

    /// `F`'s type as the generator emits it, taken apart.
    struct Parts {
        skel: Type,
        skel_level: Level,
        ity: Rc<Type>,
        ilvl: Level,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    }

    fn parts(t: &Two) -> Parts {
        let (ty, _) = t
            .el
            .lower_forded_instance(&t.cx, &t.f, &[], Term::Zero, SPAN)
            .expect("the family lowers");
        let Type::Sigma { fst_level, fst, snd, .. } = ty else {
            panic!("a forded family is a Σ")
        };
        let Type::SEq { level, ty: ity, lhs, rhs } = (*snd).clone() else {
            panic!("a forded family's second component is an sEq")
        };
        Parts { skel: (*fst).clone(), skel_level: fst_level, ity, ilvl: level, lhs, rhs }
    }

    /// Rebuild the family type with `fst` in the skeleton slot, everything
    /// else `F`'s own — the forgery constructor for the El-headed negatives
    /// (design §4's look-alike direction).
    fn with_fst(t: &Two, fst: Type) -> Type {
        let Parts { skel_level: fst_level, ity, ilvl, lhs, rhs, .. } = parts(t);
        Type::Sigma {
            fst_level,
            snd_level: ilvl.clone(),
            fst: Rc::new(fst),
            snd: Rc::new(Type::SEq { level: ilvl, ty: ity, lhs, rhs }),
        }
    }

    /// Rebuild the family type with `head` in the `μ` slot.
    fn with_head(t: &Two, head: Term) -> Type {
        let Parts { skel, skel_level: fst_level, ity, ilvl, lhs, rhs } = parts(t);
        let Term::App { dom_level, cod_level, dom, cod, arg, .. } = (*lhs).clone() else {
            panic!("after `issues/generated-term-defs.md` the μ slot is an application")
        };
        Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level: ilvl.clone(),
            fst: Rc::new(skel),
            snd: Rc::new(Type::SEq {
                level: ilvl,
                ty: ity,
                lhs: Rc::new(Term::App {
                    fun: Rc::new(head),
                    dom_level,
                    cod_level,
                    dom,
                    cod,
                    arg,
                }),
                rhs,
            }),
        }
    }

    #[test]
    fn the_family_is_recognized_through_its_mu_definition() {
        let t = two();
        let (ty, _) = t
            .el
            .lower_forded_instance(&t.cx, &t.f, &[], Term::Zero, SPAN)
            .expect("the family lowers");
        // The positive: what the generator emits still reads back, and reads
        // back as `F` — the whole point of a re-key is that it does not cost
        // recognition.
        let (ind, fam) = t.el.forded_of(&t.cx, &ty).expect("reads back as a forded family");
        assert_eq!(ind.tag, t.f.tag);
        // …and the μ node still fills at a scrutinee, which is what every
        // consumer downstream (`ty_at`, `eq_at`, the arm builders) needs.
        let filled = fam.mu_at(Term::Zero, 0);
        assert!(matches!(filled, Term::App { .. }));
        // The slot is really a *definition*, not an inlined eliminator.
        assert!(t.el.gen_ref(&t.cx, GenDef::Mu(t.f.tag)).is_some());
        // Since `docs/family-type-code-defs-design.md` the Σ's first
        // component is the **reference** `El (F#code^δ)` rather than the
        // inline `Wf` — and the recognizer handed back the *inline* copies
        // regardless, because every structural consumer downstream operates
        // on those (§3.1's line).
        let Type::Sigma { fst, .. } = &ty else { panic!("a forded family is a Σ") };
        let Type::El { tm, .. } = &**fst else {
            panic!("the skeleton slot is emitted as a code reference")
        };
        assert!(t.el.is_gen_ref(tm, GenDef::SkelCode(t.f.tag)));
        assert!(fam.skel_ref.is_some());
        assert!(matches!(&fam.skel_ty, Type::Wf { .. }));
    }

    #[test]
    fn a_structural_look_alike_is_not_the_family() {
        let t = two();
        // A Σ over **`F`'s skeleton** whose measure is **`G`'s** `μ`. Every
        // structural property the old fingerprint tested is satisfied — Σ,
        // `sEq`, a filled scrutinee slot, and `tag_of` on the first component
        // says `F#skel` — and it is not `F`, because `μ_G` is not `F`'s
        // measure. Under the pre-2026-08-04 reader this was accepted, and the
        // consumer would then have built a constructor of `F` whose equation
        // was about `G`.
        let mut scx = t.cx.clone();
        let p = parts(&t);
        scx.push("#s".into(), p.skel, p.skel_level);
        let mu_g = t.el.gen_ref(&scx, GenDef::Mu(t.g.tag)).expect("G has a μ definition");
        assert!(t.el.forded_of(&t.cx, &with_head(&t, mu_g)).is_none());

        // And a head that is no definition at all — the other half of "keyed
        // by name": an out-of-scope global resolves to no `GenDef`.
        let bogus = Term::GlobalTm {
            var: GlobalVar(u32::MAX),
            subst: LocalSubst {
                tail: heather_kernel::term::SubstTail::Empty {
                    len: 1,
                    base: heather_kernel::term::CtxBase::Nil,
                },
                terms: vec![],
            },
        };
        assert!(t.el.forded_of(&t.cx, &with_head(&t, bogus)).is_none());
    }

    // -- the El-headed direction (design §4, §9) -----------------------------

    #[test]
    fn el_of_the_wrong_declarations_code_is_not_the_family() {
        let t = two();
        // `G`'s code reference in `F`'s skeleton slot — the existing
        // look-alike construction, El-headed: two real declarations differing
        // only in their tags, every other component `F`'s own, including its
        // `μ_D`. The reference resolves through the registry — to *`G`'s*
        // `SkelCode` — so the components disagree nominally and the read
        // declines.
        let g_code = t
            .el
            .gen_ref(&t.cx, GenDef::SkelCode(t.g.tag))
            .expect("G has a code definition");
        let p = parts(&t);
        let forged = with_fst(
            &t,
            Type::El { level: p.skel_level, tm: Rc::new(g_code) },
        );
        assert!(t.el.forded_of(&t.cx, &forged).is_none());
    }

    #[test]
    fn el_of_a_byte_identical_user_global_is_not_the_family() {
        let mut t = two();
        // A bodied global whose statement, layer and body are byte-identical
        // to `F#code`'s, pushed outside the registry the way a user `fn` is.
        // Identity is the Ψ index, not the body: it does not read back as
        // `F`.
        let skel = Rc::clone(t.f.skel.as_ref().expect("forded"));
        let (skel_ty, l) = t
            .el
            .lower_instance(&t.cx, &skel, &[], &[], SPAN)
            .expect("the skeleton lowers");
        let code = crate::code::code_of(&skel_ty).expect("the skeleton has a code");
        let empty = heather_kernel::term::LocalCtx::nil();
        t.el.psi.push(heather_kernel::term::GlobalBinding::defined_tm(
            empty,
            Layer::Code,
            Rc::new(Type::Ty(l.clone())),
            Level::succ(l.clone()),
            Rc::new(code),
        ));
        t.el.refresh_delta_psi();
        // `gen_ref`'s numbering for the binding just pushed: abs = len − 1,
        // so the variable is `goal_base` — in scope, resolvable, and not in
        // the registry.
        let dup = Term::GlobalTm {
            var: GlobalVar(t.el.attempt.goal_arena.base()),
            subst: LocalSubst {
                tail: heather_kernel::term::SubstTail::Empty {
                    len: 0,
                    base: heather_kernel::term::CtxBase::Nil,
                },
                terms: vec![],
            },
        };
        let forged = with_fst(&t, Type::El { level: l, tm: Rc::new(dup) });
        assert!(t.el.forded_of(&t.cx, &forged).is_none());
    }

    /// A parameterized family keeps its inlined components (§14.12), and the
    /// coexistence has to hold in both directions: its structural read must
    /// not accept a reference component, and the reference must not smuggle
    /// the type over to the declaration it names.
    #[test]
    fn a_parameterized_structural_read_rejects_reference_components() {
        const PSRC: &str = "
inductive P<A> : (n: Nat) -> Type {
    PNil                                : P<A>(0),
    PCons(n: Nat, x: A, t: P<A>(n))     : P<A>(Succ(add(n, 1))),
}
";
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(&format!("{SRC}{PSRC}")).expect("elaborates");
        let f = Rc::clone(el.types.inductive(&crate::names::qkey("main", "F")).expect("declared"));
        let p = Rc::clone(el.types.inductive(&crate::names::qkey("main", "P")).expect("declared"));
        let cx = Cx::empty();
        // `P<Nat>` has no code definition (§14.12's boundary), so its own
        // type is emitted inline and reads back structurally, with no
        // reference spellings to hand out.
        let (pty, _) = el
            .lower_forded_instance(&cx, &p, &[(Type::Nat, Level::Zero)], Term::Zero, SPAN)
            .expect("the parameterized family lowers");
        let (ind, fam) = el.forded_of(&cx, &pty).expect("reads back structurally");
        assert_eq!(ind.tag, p.tag);
        assert!(fam.skel_ref.is_none() && fam.ity_ref.is_none());
        // …and `F`'s reference in its skeleton slot reads back as nothing:
        // not as `P` (a structural component is not a reference) and not as
        // `F` (the `μ` slot holds `P<Nat>`'s inlined measure, not `F`'s
        // `μ_D`).
        let Type::Sigma { fst_level, snd_level, snd, .. } = pty else {
            panic!("a forded family is a Σ")
        };
        let f_code = el
            .gen_ref(&cx, GenDef::SkelCode(f.tag))
            .expect("F has a code definition");
        let forged = Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level,
            fst: Rc::new(Type::El { level: fst_level, tm: Rc::new(f_code) }),
            snd,
        };
        assert!(el.forded_of(&cx, &forged).is_none());
    }

    /// Design §4's free case: a family type whnf'd back to the inline `Wf`
    /// (something δ-unfolded the `El`-references) is exactly yesterday's
    /// spelling, and the structural read — kept in place as the no-def
    /// fallback — recognizes it. And the two spellings convert, which is
    /// §1.3's conservativity stated as a kernel fact rather than a comment.
    #[test]
    fn a_pre_unfolded_occurrence_still_reads_back_and_converts() {
        let t = two();
        let (ty, lvl) = t
            .el
            .lower_forded_instance(&t.cx, &t.f, &[], Term::Zero, SPAN)
            .expect("the family lowers");
        let (_, fam) = t.el.forded_of(&t.cx, &ty).expect("reads back");
        // The unfold by hand: components at their inline types, the μ
        // reference intact (δ under `El` re-materializes the type; the μ
        // *term* stays a definition — reduce.rs's lazy decode discipline).
        let inline = Type::Sigma {
            fst_level: fam.level.clone(),
            snd_level: fam.ilvl.clone(),
            fst: Rc::new(fam.skel_ty.clone()),
            snd: Rc::new(Type::SEq {
                level: fam.ilvl.clone(),
                ty: Rc::new(fam.ity.shift_local(1)),
                lhs: Rc::new(fam.mu_at(Term::Var(LocalVar(0)), 1)),
                rhs: Rc::new(fam.idx.shift_local(1)),
            }),
        };
        let (ind, refam) = t
            .el
            .forded_of(&t.cx, &inline)
            .expect("the pre-unfolded spelling still reads back");
        assert_eq!(ind.tag, t.f.tag);
        // The structural read hands back the reference spellings for what it
        // will *emit* — the two-sided coexistence.
        assert!(refam.skel_ref.is_some());
        heather_kernel::conv::conv_type(
            t.el.psi(),
            &t.cx.gamma,
            Layer::Prog,
            &ty,
            &inline,
            &lvl,
            t.el.fuel,
        )
        .expect("the reference and inline spellings convert");
    }

    /// At a **declared** index both codes exist, and the emitted family
    /// carries both references — the `forded/declared-index-tags` family's
    /// whole win. `H` is forded (its second index pattern is two constructors
    /// deep, which route 1 rejects), so this is route 2b at a declared index.
    #[test]
    fn a_declared_index_family_references_both_codes() {
        const DSRC: &str = "
inductive Shp { SA, SB(s: Shp) }
inductive H : (s: Shp) -> Type {
    H0                   : H(SA),
    H1(s: Shp, t: H(s))  : H(SB(SB(s))),
}
";
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(DSRC).expect("elaborates");
        let h = Rc::clone(el.types.inductive(&crate::names::qkey("main", "H")).expect("declared"));
        let shp = Rc::clone(el.types.inductive(&crate::names::qkey("main", "Shp")).expect("declared"));
        let cx = Cx::empty();
        let (ity, ilvl) = el.lower_instance(&cx, &shp, &[], &[], SPAN).expect("lowers");
        let sa = el.build_ctor(&cx, &shp, 0, &[], &ity, &ilvl, SPAN).expect("SA builds");
        let (ty, _) = el.lower_forded_instance(&cx, &h, &[], sa, SPAN).expect("lowers");
        let Type::Sigma { fst, snd, .. } = &ty else { panic!("a forded family is a Σ") };
        let Type::El { tm, .. } = &**fst else { panic!("the skeleton slot is a reference") };
        assert!(el.is_gen_ref(tm, GenDef::SkelCode(h.tag)));
        let Type::SEq { ty: seq_ty, .. } = &**snd else {
            panic!("a forded family's second component is an sEq")
        };
        let Type::El { tm: ity_tm, .. } = &**seq_ty else {
            panic!("the index slot is a reference")
        };
        assert!(el.is_gen_ref(ity_tm, GenDef::IdxCode(shp.tag)));
        let (ind, fam) = el.forded_of(&cx, &ty).expect("reads back");
        assert_eq!(ind.tag, h.tag);
        assert!(fam.ity_ref.is_some() && fam.skel_ref.is_some());
    }
}
