//! Indexed families on the `IWf` route: the declaration lowered onto the
//! kernel's finitary indexed fixed point (`docs/iwf-former-design.md` §8).
//!
//! This replaced route 2b's fording (`docs/inductive-fording-lowering.md`,
//! superseded): a child's index is **stored** in the label rather than
//! recomputed from the child, so `match` needs no `transp` and β fires on
//! open data, and the fording fragment's F1–F3 are gone. A `match` at a
//! specific index inverts or abstracts it in the motive (§8.3,
//! [`Elaborator::iwf_match_motive`]). The doctrine is the
//! tiers' (`inductive.rs`): the lowering is untrusted, the kernel re-checks
//! every emitted term, and annotations are read off the type being
//! eliminated wherever one exists.
//!
//! The scheme (design §8):
//!
//! ```text
//! S            = the shape declaration, lowered by tier 0 (children deleted)
//! n(x)         = case x of c_k ⇒ (c_k's number of children)
//! o(x)         = case x of c_k(ȳ) ⇒ (c_k's written result index)[ȳ]
//! c(x, i)      = (case x of c_k(ȳ) ⇒ λi'. case i' of t ⇒ (child t's index)[ȳ]) i
//! ⟦D<ā>(m)⟧    = IWf(I; S; n; o; c)(m)
//! ⟦c_k(b̄)⟧     = sup_i(inj_k(stored b̄); ⟨children⟩)
//! match        = elim_IWf(…; j z. M; a cs ih. (case a of …) cs ih; m; t)
//! ```
//!
//! The step's case on the shape is a convoy: `cs` and `ih` are typed at `a`,
//! so the tree's motive re-abstracts them and the tree is applied to both.

use std::borrow::Borrow;
use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    IWfSig, LocalCtx, LocalSubst, LocalVar, Term, Type, dnth, dvec_succ_parts, fin_next, inst_motive2,
    iwf_children_ty, iwf_fam, iwf_step_telescope,
};
use heather_syntax::ast::{Arm, Expr, MatchForm, Span};

use crate::gendefs::GenDef;
use crate::inductive::{Ctor, FieldKind, Inductive, Spine, inject, nat_lit, tag_value};
use crate::recursion::{Guard, GuardKind};
use crate::wf::fin_index;
use crate::{Alias, Cx, Elaborator, R, embed, err};

/// The two spellings of an `IWf`-route family: the kernel's finitary
/// `IWf(sig)(m)`, or, for a family with a recursive function field, the
/// `W`-encoded `Σ(t : W₀). El(ok t m)` (docs/iwf-infinitary-design.md §5).
pub(crate) enum FamForm {
    IWf(Rc<IWfSig>),
    W(Rc<crate::iwf_w::IwSig>),
}

/// A type in `IWf` family form, read back: the signature, the index it is
/// applied at, and the index type (the signature's, kept apart for the
/// callers that build motives over it).
pub(crate) struct IwfFam {
    pub form: FamForm,
    /// The index the family is applied at.
    pub idx: Rc<Term>,
    /// `I`, scoped in the ambient context.
    pub ity: Type,
    /// `li`.
    pub ilvl: Level,
}

impl IwfFam {
    fn new(sig: Rc<IWfSig>, idx: Rc<Term>) -> IwfFam {
        let ity = (*sig.idx).clone();
        let ilvl = sig.idx_level.clone();
        IwfFam { form: FamForm::IWf(sig), idx, ity, ilvl }
    }

    fn new_w(sig: Rc<crate::iwf_w::IwSig>, idx: Rc<Term>) -> IwfFam {
        let ity = (*sig.ity).clone();
        let ilvl = sig.ilvl.clone();
        IwfFam { form: FamForm::W(sig), idx, ity, ilvl }
    }

    /// The family's own level: `l ⊔ li` on `IWf`, `lw ⊔ lk` on `W`.
    pub fn lvl(&self) -> Level {
        match &self.form {
            FamForm::IWf(sig) => sig.family_level(),
            FamForm::W(sig) => sig.lvl(),
        }
    }

    /// The family at `m`, with `m` and the result scoped `by` binders past
    /// the ambient context.
    pub fn ty_at(&self, m: Term, by: u32) -> Type {
        match &self.form {
            FamForm::IWf(sig) => sig.shift_local(by).at(Rc::new(m)),
            FamForm::W(sig) => sig.fam(by, &m),
        }
    }

    /// The shape declaration's lowering and its level, which both forms
    /// share: the constructors' payloads, read by the same spine.
    pub fn shape(&self) -> (&Type, &Level) {
        match &self.form {
            FamForm::IWf(sig) => (&sig.shape, &sig.level),
            FamForm::W(sig) => (&sig.shape, &sig.ls),
        }
    }
}

/// The number of children of constructor `k`.
fn children_of(ind: &Inductive, k: usize) -> usize {
    ind.ctors[k].kind.iter().filter(|f| **f == FieldKind::Plain).count()
}

/// The written result index (design §8.1). Present on every constructor of an
/// `IWf`-route declaration, by construction.
pub(crate) fn res_expr(ind: &Inductive, k: usize) -> &Expr {
    ind.ctors[k]
        .res_expr
        .as_ref()
        .expect("an IWf-route ctor carries its result index")
}

/// Constructor `k`'s children's written indices, in order.
fn child_exprs(ind: &Inductive, k: usize) -> Vec<&Expr> {
    let ctor = &ind.ctors[k];
    ctor.kind
        .iter()
        .enumerate()
        .filter(|(_, f)| **f == FieldKind::Plain)
        .map(|(j, _)| child_index(ctor, j))
        .collect()
}

/// The index an `IWf`-route constructor writes for its child at field `j`:
/// the route has one index binder, so the entry is a singleton.
pub(crate) fn child_index(ctor: &Ctor, j: usize) -> &Expr {
    match ctor.child_index.get(j) {
        Some(Some(es)) if es.len() == 1 => &es[0],
        _ => panic!("an IWf-route child carries its index"),
    }
}

impl Elaborator {
    // -- reading the form back ----------------------------------------------

    /// Read a type back as an `IWf`-route family. `None` for everything
    /// else. The declaration is identified by the shape's nominal tag, which
    /// belongs to its shape declaration and to nothing else; an `IWf` is not
    /// writable at the surface, so a look-alike cannot be forged.
    pub(crate) fn iwf_of(&self, ty: &Type) -> Option<(Rc<Inductive>, IwfFam)> {
        let d = crate::inductive::decoded(ty);
        let Type::IWf { sig, index } = &*d else {
            // The `W` encoding of a family with a function field
            // (docs/iwf-infinitary-design.md §5), found by the same shape.
            let (sig, idx) = crate::iwf_w::IwSig::read(&d)?;
            let shape = self.tag_of(&sig.shape)?;
            let ind = Rc::clone(self.types.iwf_by_shape(shape.tag)?);
            if !ind.iwf_infinitary() {
                return None;
            }
            return Some((ind, IwfFam::new_w(Rc::new(sig), idx)));
        };
        let shape = self.tag_of(&sig.shape)?;
        let ind = Rc::clone(self.types.iwf_by_shape(shape.tag)?);
        Some((ind, IwfFam::new(Rc::clone(sig), Rc::clone(index))))
    }

    /// [`Self::iwf_of`] with reduction behind it, for a family that arrived
    /// through an `I -> Type` function value. The structural read comes first
    /// and unchanged; an `IWf` is a whnf, so the read succeeds the moment the
    /// wrapper is peeled.
    pub(crate) fn iwf_of_at(&self, cx: &Cx, ty: &Type) -> Option<(Rc<Inductive>, IwfFam)> {
        if let Some(r) = self.iwf_of(ty) {
            return Some(r);
        }
        let Type::El { level, tm } = ty else {
            return None;
        };
        let oracle = self.semantic_oracle();
        for tm in oracle.term_reducts(&cx.gamma, tm, 1024) {
            let cand = Type::El {
                level: level.clone(),
                tm: Rc::new(tm),
            };
            if let Some(r) = self.iwf_of(&cand) {
                return Some(r);
            }
        }
        None
    }

    // -- the type -------------------------------------------------------------

    /// `⟦D<ā>(m)⟧ = IWf(I; S; n; o; c)(m)`.
    pub(crate) fn lower_iwf_instance(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        idx: Term,
        span: Span,
    ) -> R<(Type, Level)> {
        if ind.iwf_infinitary() {
            let sig = self.iw_sig(cx, ind, args, span)?;
            return Ok((sig.fam(0, &idx), sig.lvl()));
        }
        let sig = self.iwf_sig(cx, ind, args, span)?;
        let lvl = sig.family_level();
        Ok((sig.at(Rc::new(idx)), lvl))
    }

    /// `fresh`, a family's shape (`index` false, keyed by the shape
    /// declaration's tag) or index type (`index` true, by the family's), as
    /// the allocation an earlier signature used when it is that same type.
    ///
    /// Each mention of a family lowers both afresh, and they are sums of one
    /// summand per constructor (per member, for a mutual group's index), so
    /// two occurrences of the family shared no node below the root: every
    /// `D#iarity x` the kernel judged compared the shape at `x` with the
    /// definition's domain node by node, and every conversion of two
    /// instances walked both shapes in the value domain
    /// (`issues/iwf-shape-spine-comb-depth.md`). The guard is a structural
    /// `==`, the order of the lowering itself, so a hit is the same type in
    /// the same scope and which copy stands is a matter of sharing only, as
    /// for [`Self::share_registered_lowering`]. A miss (other arguments,
    /// other globals) replaces the entry.
    fn share_iwf_part(&self, tag: u32, index: bool, fresh: Type) -> Rc<Type> {
        let mut memo = self.memos.iwf_part_memo.borrow_mut();
        match memo.get(&(tag, index)) {
            Some(kept) if **kept == fresh => Rc::clone(kept),
            _ => {
                let fresh = Rc::new(fresh);
                memo.insert((tag, index), Rc::clone(&fresh));
                fresh
            }
        }
    }

    /// The family's signature at type arguments `args`, scoped in `cx`.
    pub(crate) fn iwf_sig(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        span: Span,
    ) -> R<Rc<IWfSig>> {
        let _scope = self.use_inductive_scope(ind);
        let shape_decl = ind
            .skel
            .as_ref()
            .expect("an IWf-route declaration has a shape declaration");
        let n = ind.ctors.len();
        let (shape, l) = self.lower_instance(cx, shape_decl, args, &[], span)?;
        let (ity, ilvl) = self.index_type_of(cx, ind, span)?;
        let shape_rc = self.share_iwf_part(shape_decl.tag, false, shape);
        let ity_rc = self.share_iwf_part(ind.tag, true, ity);
        if let Some(sig) = self.iwf_sig_named(cx, ind, args, &shape_rc, &l, &ity_rc, &ilvl) {
            return Ok(sig);
        }
        let shape = (*shape_rc).clone();
        let ity = (*ity_rc).clone();
        let spine = self.spine(&shape, &l, n, span)?;
        let mut xcx = cx.clone();
        xcx.selfref = None;
        xcx.guard = None;
        xcx.push("#x".into(), shape.clone(), l.clone());
        let x = Rc::new(Term::Var(LocalVar(0)));
        // n(x): a literal per constructor.
        let arity_body =
            |_: &Cx, k: usize, _: &Rc<Term>, _: u32, _: &Type| -> R<Term> {
                Ok(nat_lit(children_of(ind, k)))
            };
        let arity = self.idx_case_tree(
            &xcx,
            &spine,
            spine.root(),
            Type::Nat,
            &Level::Zero,
            Rc::clone(&x),
            1,
            &arity_body,
        )?;
        // o(x): the written result index over the stored fields.
        let out_body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _: &Type| -> R<Term> {
            let acx = self.decl_payload_cx(bcx, ind, &spine, k, value, d, span)?;
            self.elab_check(&acx, res_expr(ind, k), &ity.shift_local(d), &ilvl).map(index_value)
        };
        let out = self.idx_case_tree(
            &xcx,
            &spine,
            spine.root(),
            ity.shift_local(2),
            &ilvl,
            Rc::clone(&x),
            1,
            &out_body,
        )?;
        // c(x, i): a convoy — the position's type depends on the shape, so
        // the tree on `x` returns `Π(i' : Fin n[x]). I` and is applied to `i`.
        let child_body =
            |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _: &Type| -> R<Term> {
                let m = children_of(ind, k);
                let mut icx = self.decl_payload_cx(bcx, ind, &spine, k, value, d, span)?;
                let fin = Type::Fin {
                    len: Rc::new(nat_lit(m)),
                };
                icx.push("#i".into(), fin.clone(), Level::Zero);
                let exprs = child_exprs(ind, k);
                let body = self.fin_tree(&icx, &exprs, 0, &ity, &ilvl, d + 1)?;
                Ok(Term::Lam {
                    dom_level: Level::Zero,
                    cod_level: ilvl.clone(),
                    dom: Rc::new(fin),
                    body: Rc::new(body),
                })
            };
        let child_motive = Type::Pi {
            dom_level: Level::Zero,
            cod_level: ilvl.clone(),
            dom: Rc::new(Type::Fin {
                len: Rc::new(arity.shift_local_above(1, 1)),
            }),
            cod: Rc::new(ity.shift_local(3)),
        };
        let tree = self.idx_case_tree(
            &xcx,
            &spine,
            spine.root(),
            child_motive,
            &ilvl,
            x,
            1,
            &child_body,
        )?;
        let child = match tree {
            // One constructor: no case, and the λ's body is already in
            // `(Γ, x, i)`.
            Term::Lam { body, .. } => (*body).clone(),
            tree => Term::AppAt {
                fun: Rc::new(tree.shift_local(1)),
                arg: Rc::new(Term::Var(LocalVar(0))),
            },
        };
        Ok(Rc::new(IWfSig {
            level: l,
            idx_level: ilvl,
            idx: ity_rc,
            shape: shape_rc,
            arity: Rc::new(arity),
            out: Rc::new(out),
            child: Rc::new(child),
        }))
    }

    // -- the named signature (docs/iwf-named-signature-design.md) -----------

    /// `D#iarity`, `D#iout` and `D#ichild` at declaration time: the inline
    /// signature [`Self::iwf_sig`] builds over [`Self::tycode_fn_telescope`]'s
    /// all-`Ty 0` telescope, its three index functions abstracted over the
    /// telescope and their own binders. From then on every instance at that
    /// profile is spelled with them (§2). Best-effort like every generated
    /// definition: a refusal leaves the family inline.
    pub(crate) fn register_iwf_sig(&mut self, ind: &Rc<Inductive>, span: Span) {
        if ind.skel.is_none()
            || ind.iwf_infinitary()
            || !ind.valparams.is_empty()
            || self.types.gdefs().abs_for(&GenDef::IArity(ind.tag)).is_some()
        {
            return;
        }
        let Some((cx, binders, targs, _)) = self.tycode_fn_telescope(ind, span) else {
            return;
        };
        let Ok(sig) = self.iwf_sig(&cx, ind, &targs, span) else {
            return;
        };
        let tel = self.emitted_tel(&binders);
        let n = tel.len() as u32;
        let tel_vars: Vec<Rc<Term>> = (0..n).map(|k| Rc::new(Term::Var(LocalVar(n - 1 - k)))).collect();
        let (l, li) = (sig.level.clone(), sig.idx_level.clone());
        let lvl = |a: &Level, b: &Level| Level::max(a.clone(), b.clone());
        // n : Π(x : S). Nat.
        let ar_stmt = Type::Pi {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::clone(&sig.shape),
            cod: Rc::new(Type::Nat),
        };
        let ar_body = Term::Lam {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::clone(&sig.shape),
            body: Rc::clone(&sig.arity),
        };
        if !self.push_m_def(GenDef::IArity(ind.tag), ind, &tel, ar_stmt, l.clone(), ar_body, span) {
            return;
        }
        // Every push moves the globals the pieces built before it mention one
        // further out (`register_m_sig`'s frame rule): one for the output
        // index, two for the child index.
        let tel1: Vec<(Type, Level)> = tel.iter().map(|(t, l)| (t.shift_global(1), l.clone())).collect();
        let shape1 = Rc::new(sig.shape.shift_global(1));
        let out_stmt = Type::Pi {
            dom_level: l.clone(),
            cod_level: li.clone(),
            dom: Rc::clone(&shape1),
            cod: Rc::new(sig.idx.shift_global(1).shift_local(1)),
        };
        let out_body = Term::Lam {
            dom_level: l.clone(),
            cod_level: li.clone(),
            dom: shape1,
            body: Rc::new(sig.out.shift_global(1)),
        };
        if !self.push_m_def(GenDef::IOut(ind.tag), ind, &tel1, out_stmt, lvl(&l, &li), out_body, span) {
            return;
        }
        // `Fin(D#iarity ā x)` over `(tel, x)`, minted now.
        let Some(aref) = self.m_ref_app(&cx, GenDef::IArity(ind.tag), &tel_vars, 1) else {
            return;
        };
        let fin = Rc::new(Type::Fin { len: aref });
        let tel2: Vec<(Type, Level)> = tel.iter().map(|(t, l)| (t.shift_global(2), l.clone())).collect();
        let shape2 = Rc::new(sig.shape.shift_global(2));
        let i2 = Rc::new(sig.idx.shift_global(2).shift_local(2));
        let child_i = Type::Pi { dom_level: Level::Zero, cod_level: li.clone(), dom: Rc::clone(&fin), cod: i2 };
        let child_stmt = Type::Pi {
            dom_level: l.clone(),
            cod_level: li.clone(),
            dom: Rc::clone(&shape2),
            cod: Rc::new(child_i),
        };
        let child_body = Term::Lam {
            dom_level: l.clone(),
            cod_level: li.clone(),
            dom: shape2,
            body: Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: li.clone(),
                dom: fin,
                body: Rc::new(sig.child.shift_global(2)),
            }),
        };
        if !self.push_m_def(GenDef::IChild(ind.tag), ind, &tel2, child_stmt, lvl(&l, &li), child_body, span) {
            return;
        }
        // `dnth` over the children tuple, at the named signature built now: in
        // `(tel, a, cs, i)`, as `iwf_step_telescope` spells it.
        let Ok(nsig) = self.iwf_sig(&cx, ind, &targs, span) else {
            return;
        };
        let fl = nsig.family_level();
        let cs_ty = Rc::new(iwf_children_ty(&nsig.shift_local(1), &Term::Var(LocalVar(0))));
        let fam = nsig.shift_local(4).at(Rc::new(nsig.child.shift_local_above(2, 1)));
        let nth = dnth(
            &fl,
            &Rc::new(nsig.arity.shift_local(2)),
            &Rc::new(fam),
            Rc::new(Term::Var(LocalVar(1))),
            Rc::new(Term::Var(LocalVar(0))),
        );
        let res = Rc::new(nsig.shift_local(3).at(Rc::new(nsig.child.shift_local_above(1, 1))));
        let fin = Rc::new(Type::Fin { len: Rc::new(nsig.arity.shift_local(1)) });
        let at_i = Type::Pi { dom_level: Level::Zero, cod_level: fl.clone(), dom: Rc::clone(&fin), cod: Rc::clone(&res) };
        let at_cs = Type::Pi { dom_level: fl.clone(), cod_level: fl.clone(), dom: Rc::clone(&cs_ty), cod: Rc::new(at_i) };
        let stmt = Type::Pi { dom_level: l.clone(), cod_level: fl.clone(), dom: Rc::clone(&nsig.shape), cod: Rc::new(at_cs) };
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: fl.clone(),
            dom: Rc::clone(&nsig.shape),
            body: Rc::new(Term::Lam {
                dom_level: fl.clone(),
                cod_level: fl.clone(),
                dom: cs_ty,
                body: Rc::new(Term::Lam { dom_level: Level::Zero, cod_level: fl.clone(), dom: fin, body: Rc::new(nth) }),
            }),
        };
        let tel3: Vec<(Type, Level)> = tel.iter().map(|(t, l)| (t.shift_global(3), l.clone())).collect();
        let _ = self.push_m_def(GenDef::IDnth(ind.tag), ind, &tel3, stmt, lvl(&l, &fl), body, span);
    }

    /// [`iwf_step_telescope`] for a match in `cx`, with the ih type's `dnth`
    /// spelled as the family's `D#idnth` when its signature is named: the
    /// convoy repeats the telescope at every level of the case tree, and
    /// inline `dnth` carries the children's family several times over.
    fn iwf_match_telescope(&self, cx: &Cx, sig: &Rc<IWfSig>, mlvl: &Level, motive: &Type) -> (Type, Type, Type) {
        let (cs_ty, ih_ty, st_ty) = iwf_step_telescope(sig, mlvl, motive);
        let Some(nth) = self.iwf_named_dnth(cx, sig) else {
            return (cs_ty, ih_ty, st_ty);
        };
        let ih_ty = Type::Pi {
            dom_level: Level::Zero,
            cod_level: mlvl.clone(),
            dom: Rc::new(Type::Fin { len: Rc::new(sig.arity.shift_local(1)) }),
            cod: Rc::new(inst_motive2(motive, 3, &sig.child.shift_local_above(1, 1), &nth)),
        };
        (cs_ty, ih_ty, st_ty)
    }

    /// `D#idnth ā a cs i` in `(cx, a, cs, i)`, for a signature in `cx` whose
    /// arity is `D#iarity ā x`.
    fn iwf_named_dnth(&self, cx: &Cx, sig: &IWfSig) -> Option<Term> {
        let (GenDef::IArity(tag), args) = self.gen_app_of(&sig.arity)? else {
            return None;
        };
        let (last, tel) = args.split_last()?;
        if !matches!(**last, Term::Var(LocalVar(0))) {
            return None;
        }
        // The telescope's arguments, read out of the shape binder.
        let tel: Vec<Rc<Term>> = tel.iter().map(|a| Rc::new(a.inst_top(0, &Term::Zero))).collect();
        self.m_ref_app(cx, GenDef::IDnth(tag), &tel, 3).map(|t| (*t).clone())
    }

    /// The named signature of an instance (§2): `None` when the family
    /// registered none, or the instance is not at the registered profile
    /// (every type argument at `Ty 0` with a code); [`Self::iwf_sig`] then
    /// spells it inline. The shape and the index type are the inline ones,
    /// which the caller has built.
    #[allow(clippy::too_many_arguments)]
    fn iwf_sig_named(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        shape: &Rc<Type>,
        l: &Level,
        ity: &Rc<Type>,
        ilvl: &Level,
    ) -> Option<Rc<IWfSig>> {
        self.types.gdefs().abs_for(&GenDef::IChild(ind.tag))?;
        if args.iter().any(|(_, l)| !l.equiv(&Level::Zero)) {
            return None;
        }
        let mut tel = Vec::with_capacity(args.len());
        for (a, _) in args {
            tel.push(Rc::new(crate::code::code_of(a)?));
        }
        Some(Rc::new(IWfSig {
            level: l.clone(),
            idx_level: ilvl.clone(),
            idx: Rc::clone(ity),
            shape: Rc::clone(shape),
            arity: self.m_ref_app(cx, GenDef::IArity(ind.tag), &tel, 1)?,
            out: self.m_ref_app(cx, GenDef::IOut(ind.tag), &tel, 1)?,
            child: self.m_ref_app(cx, GenDef::IChild(ind.tag), &tel, 2)?,
        }))
    }

    /// One shape branch's context for the declaration's own index
    /// expressions: each stored field, under its **declared** name, aliased
    /// to its projection out of the branch's value. `d` counts the binders
    /// pushed since `spine` was read back.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn decl_payload_cx(
        &self,
        bcx: &Cx,
        ind: &Inductive,
        spine: &Spine,
        k: usize,
        value: &Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Cx> {
        let mut acx = bcx.clone();
        acx.selfref = None;
        acx.guard = None;
        let names: Vec<Option<String>> = ind.ctors[k].fields.iter().map(|(n, _)| n.clone()).collect();
        self.payload_aliases(&mut acx, ind, spine, k, value, d, &names, span)?;
        Ok(acx)
    }

    /// Alias each stored field of constructor `k`, under `names[field]`, to
    /// its projection out of `value` (the shape branch's tuple, scoped in
    /// `acx`, `d` binders past where `spine` was read back).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn payload_aliases(
        &self,
        acx: &mut Cx,
        ind: &Inductive,
        spine: &Spine,
        k: usize,
        value: &Rc<Term>,
        d: u32,
        names: &[Option<String>],
        span: Span,
    ) -> R<()> {
        let ctor = &ind.ctors[k];
        let ctor_ty = spine.ctors[k].0.shift_local(d);
        let depth = acx.names.len();
        let mut p = 0usize;
        for (fi, kind) in ctor.kind.iter().enumerate() {
            if *kind != FieldKind::Payload {
                continue;
            }
            if let Some(name) = names[fi].clone() {
                let (term, ty, level) = self.projection(acx, &ctor_ty, value, p, span)?;
                acx.aliases.push(Rc::new(Alias {
                    skel: None,
                    name,
                    depth,
                    term,
                    ty,
                    level,
                    spliced: None,
                    shifted: Default::default(),
                }));
            }
            p += 1;
        }
        Ok(())
    }

    /// `case i of t ⇒ e_t | t+1 ⇒ … | (none left) ⇒ elim_Empty`, with `i`
    /// the innermost binder of `cx`, at type `Fin(|exprs| - t)`. `ity` is
    /// scoped `depth` binders out from `cx`.
    fn fin_tree(
        &self,
        cx: &Cx,
        exprs: &[&Expr],
        t: usize,
        ity: &Type,
        ilvl: &Level,
        depth: u32,
    ) -> R<Term> {
        let m = exprs.len();
        let motive = Rc::new(ity.shift_local(depth + 1));
        if t == m {
            return Ok(Term::ElimEmpty {
                level: ilvl.clone(),
                // `Fin(0) ⇝ Empty^0` — `Fin` is declared at level 0.
                scrut_level: Level::Zero,
                motive,
                scrut: Rc::new(Term::Var(LocalVar(0))),
            });
        }
        let unit = Type::Unit { level: Level::Zero };
        let rest = Type::Fin {
            len: Rc::new(nat_lit(m - t - 1)),
        };
        let mut lcx = cx.clone();
        lcx.push("#here".into(), unit.clone(), Level::Zero);
        let case_l = index_value(self.elab_check(&lcx, exprs[t], &ity.shift_local(depth + 1), ilvl)?);
        let mut rcx = cx.clone();
        rcx.push("#later".into(), rest.clone(), Level::Zero);
        let case_r = self.fin_tree(&rcx, exprs, t + 1, ity, ilvl, depth + 1)?;
        Ok(Term::Case {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            motive_level: ilvl.clone(),
            lhs: Rc::new(unit),
            rhs: Rc::new(rest),
            motive,
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut: Rc::new(Term::Var(LocalVar(0))),
        })
    }

    // -- constructors ---------------------------------------------------------

    /// The written result index at a constructor's *arguments* — what the
    /// constructor's index check compares against the expected family's
    /// index, and what [`Elaborator::infer_ctor`] needs to build the family at
    /// all.
    pub(crate) fn iwf_ctor_index<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[A],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (ity, ilvl) = self.index_type_of(cx, ind, span)?;
        let acx = self.res_arg_cx(cx, ind, i, args, &[])?;
        let t = {
            let _scope = self.use_inductive_scope(ind);
            self.elab_check(&acx, res_expr(ind, i), &ity, &ilvl)?
        };
        Ok((t, ity, ilvl))
    }

    /// A context binding a constructor's stored fields to the terms the
    /// *written arguments* denote. `pays` gives the values when the caller
    /// already has them typed (the checking path); otherwise a field the
    /// result index mentions is inferred.
    fn res_arg_cx<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[A],
        pays: &[(usize, Rc<Term>, Type, Level)],
    ) -> R<Cx> {
        let ctor = &ind.ctors[i];
        let mut acx = cx.clone();
        acx.selfref = None;
        acx.guard = None;
        let depth = acx.names.len();
        let e = res_expr(ind, i);
        for (k, (name, _)) in ctor.fields.iter().enumerate() {
            let Some(name) = name.clone() else { continue };
            if ctor.kind[k] != FieldKind::Payload {
                continue;
            }
            if let Some((_, term, ty, level)) = pays.iter().find(|(j, ..)| *j == k) {
                acx.aliases.push(Rc::new(Alias {
                    skel: None,
                    name,
                    depth,
                    term: Rc::clone(term),
                    ty: ty.clone(),
                    level: level.clone(),
                    spliced: None,
                    shifted: Default::default(),
                }));
            } else if crate::inductive::expr_mentions(e, &name) {
                let (term, ty, level) = self.elab_infer(cx, args[k].borrow())?;
                acx.aliases.push(Rc::new(Alias {
                    skel: None,
                    name,
                    depth,
                    term: Rc::new(term),
                    ty,
                    level,
                    spliced: None,
                    shifted: Default::default(),
                }));
            }
        }
        Ok(acx)
    }

    /// `⟦c(b̄)⟧ = sup_i(inj_c(stored b̄); ⟨children⟩)`, each child checked at
    /// the family instance its written index names.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_iwf_ctor<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[A],
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let Some((found, fam)) = self.iwf_of_at(cx, expected) else {
            return err(
                format!(
                    "`{}` constructs the indexed family `{}(i)`, but the expected type \
                     here is not in that family form (docs/iwf-former-design.md §8)",
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
        let n = ind.ctors.len();
        let (shape, slvl) = fam.shape();
        let spine = self.spine(shape, slvl, n, span)?;
        // The label: the tag and the stored arguments, tier 0 verbatim — with
        // the field values kept, because the indices may mention them.
        let payload: Vec<&Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(a, _)| a.borrow())
            .collect();
        let mut pay_vals: Vec<(Rc<Term>, Type, Level)> = Vec::new();
        let label_fields =
            self.build_fields_collect(cx, &spine.ctors[i].0, &payload, true, &mut pay_vals, span)?;
        let label = inject(&spine, i, n, label_fields, 0);
        let pays: Vec<(usize, Rc<Term>, Type, Level)> = ctor
            .kind
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(k, _)| k)
            .zip(pay_vals)
            .map(|(k, (t, ty, lv))| (k, t, ty, lv))
            .collect();
        let acx = self.res_arg_cx(cx, ind, i, args, &pays)?;
        // The children, each at the index written for it. On the `W`
        // encoding they are checked after the index, by `build_iw_ctor`.
        let children = match &fam.form {
            FamForm::IWf(sig) => {
                let mut kids: Vec<Term> = Vec::new();
                for (k, kind) in ctor.kind.iter().enumerate() {
                    if *kind != FieldKind::Plain {
                        continue;
                    }
                    let e = child_index(ctor, k);
                    let x = {
                        let _scope = self.use_inductive_scope(ind);
                        self.elab_check(&acx, e, &fam.ity, &fam.ilvl)?
                    };
                    kids.push(self.elab_check(cx, args[k].borrow(), &fam.ty_at(x, 0), &fam.lvl())?);
                }
                Some(dvec_tuple(sig, &label, kids))
            }
            FamForm::W(_) => None,
        };
        // The index check, one conversion, exactly as route 1 does.
        let target = {
            let _scope = self.use_inductive_scope(ind);
            self.elab_check(&acx, res_expr(ind, i), &fam.ity, &fam.ilvl)?
        };
        if self
            .committed_oracle()
            .convert_term(
                &cx.gamma,
                Layer::Prog,
                &target,
                &fam.idx,
                &fam.ity,
                &fam.ilvl,
            )
            .is_err()
        {
            // A mutual group's constructor at another member is a different
            // type, not a different index (docs/mutual-inductive-design.md §3).
            if !ind.members.is_empty()
                && let Some(want) = self.iwf_member_at(cx, ind, &fam.idx, span)
                && ind.member_of_ctor(i) != Some(want)
            {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, and a `{}` is expected here",
                        ctor.name,
                        Self::member_name_of(ind, i),
                        ind.members[want].name
                    ),
                    span,
                );
            }
            return err(
                format!(
                    "`{}` constructs `{}` at its written result index, which is not the \
                     expected `{}`",
                    ctor.name,
                    self.display_type(cx, &fam.ty_at(target, 0)),
                    self.display_type(cx, expected)
                ),
                span,
            );
        }
        match (&fam.form, children) {
            (FamForm::IWf(sig), Some(children)) => Ok(sig.supi(Rc::new(label), Rc::new(children))),
            (FamForm::W(sig), _) => {
                let args: Vec<&Expr> = args.iter().map(|a| a.borrow()).collect();
                self.build_iw_ctor(cx, &acx, ind, i, &args, sig, label, &target, &fam.idx, span)
            }
            (FamForm::IWf(_), None) => err("internal: an IWf constructor built no children", span),
        }
    }

    /// [`Elaborator::build_fields`], keeping each field's value: the payload
    /// terms are needed twice, once in the label and once in the indices.
    fn build_fields_collect<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        args: &[A],
        tag: bool,
        out: &mut Vec<(Rc<Term>, Type, Level)>,
        span: Span,
    ) -> R<Term> {
        let head = self.whnf(cx, ctor_ty, span)?;
        let Type::Sigma {
            fst_level,
            snd_level,
            fst,
            snd,
        } = head
        else {
            if let Type::Unit { level } = &head
                && args.is_empty()
            {
                return Ok(Term::Triv {
                    level: level.clone(),
                });
            }
            return err("internal: malformed constructor encoding", span);
        };
        let value = if tag {
            Rc::new(tag_value(&fst))
        } else {
            let (arg, _) = args.split_first().ok_or(crate::ElabError::Elab {
                msg: "too few arguments".into(),
                span,
            })?;
            let v = Rc::new(self.elab_check(cx, arg.borrow(), &fst, &fst_level)?);
            out.push((Rc::clone(&v), (*fst).clone(), fst_level.clone()));
            v
        };
        let rest = if tag { args } else { &args[1..] };
        let tail = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&value)));
        let tail_tm = self.build_fields_collect(cx, &tail, rest, false, out, span)?;
        // The tuple's checked spelling, exactly as `build_fields_skel`'s
        // (`docs/intro-by-type-design.md` §4.1): no annotation, since every
        // layer is in checking position.
        if self.emits_at_forms() {
            return Ok(Term::PairAt {
                ty: None,
                fst: value,
                snd: Rc::new(tail_tm),
            });
        }
        Ok(Term::Pair {
            fst_level,
            snd_level,
            fst_ty: fst,
            snd_ty: snd,
            fst: value,
            snd: Rc::new(tail_tm),
        })
    }

    // -- the eliminator -------------------------------------------------------

    /// The `match` motive over `(Γ, j, z)` from the expected one over
    /// `(Γ, z)`, for a scrutinee at `fam.idx` (`docs/iwf-former-design.md`
    /// §8.3). A variable index is generalized as route 1's is. Otherwise,
    /// in order:
    ///
    /// - **Tier 1, inversion**: the index and every constructor's output
    ///   index are constructor-headed. The motive cases on `j` by the index
    ///   type's eliminator: `M` with the index's arguments abstracted at the
    ///   scrutinee's constructor, `Unit` at every other, so an arm that
    ///   cannot occur is `tt` and may be left out, and each other arm sees
    ///   its goal at its own index (`vtail : V(S n) → V(n)` needs exactly
    ///   this). At `j := e` the motive reduces to `M`, so β stays
    ///   definitional.
    /// - **Tier 2, abstraction**: `e` abstracted out of `M` wherever it is
    ///   written, Coq's `match … in D j`.
    ///
    /// Each candidate is kept only if the kernel accepts it as a type over
    /// `(Γ, j : I, z : D(j))`; the last resort is the motive with `j` unused.
    pub(crate) fn iwf_match_motive(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &IwfFam,
        motive: &Type,
        mlvl: &Level,
        span: Span,
    ) -> R<(Type, IndexMotive)> {
        let plain = self.generalize_index(cx, motive, &fam.idx);
        if matches!(&*fam.idx, Term::Var(_)) {
            return Ok((plain, IndexMotive::Plain));
        }
        let mut jcx = cx.clone();
        jcx.push("#j".into(), fam.ity.clone(), fam.ilvl.clone());
        jcx.push("#z".into(), fam.ty_at(Term::Var(LocalVar(0)), 1), fam.lvl());
        let psi = self.goal_psi();
        let fits = |m: &Type| {
            heather_kernel::typing::check_type(&psi, 0, Layer::Prog, &jcx.gamma, m, mlvl, self.policy.fuel)
                .is_ok()
        };
        if let Some(inv) = self.iwf_inverted_motive(cx, ind, fam, motive, mlvl, span)?
            && fits(&inv)
        {
            let unit = matches!(self.whnf(cx, motive, span), Ok(Type::Unit { .. }));
            return Ok((inv, IndexMotive::Inverted { unit }));
        }
        let pi = Type::Pi {
            dom_level: fam.lvl(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.ty_at((*fam.idx).clone(), 0)),
            cod: Rc::new(motive.clone()),
        };
        // A closed index is not abstracted, for the same reason a closed
        // inversion argument is not: its literals also spell the signature.
        let open = fam.idx.shift_local(1) != *fam.idx;
        if open
            && let Some(Type::Pi { cod, .. }) = pi.abstract_local(&fam.idx)
            && fits(&cod)
        {
            return Ok(((*cod).clone(), IndexMotive::Plain));
        }
        Ok((plain, IndexMotive::Plain))
    }

    /// Tier 1's motive, or `None` where inversion does not apply: the index
    /// or some constructor's output index is not constructor-headed, or `M`
    /// has no code to case into.
    ///
    /// Inversion is **per level** (docs/mutual-inductive-design.md §4): in
    /// the branch at the scrutinee's index constructor, each argument of it
    /// is, in turn, abstracted (a variable), inverted again by its own type's
    /// eliminator (constructor-headed, and so is the argument at that
    /// position of every constructor still possible there), or — open and
    /// neither — abstracted where written, tier 2's move one level down. A
    /// mutual group's `match` needs the second level whenever a member's own
    /// index is constructor-headed (`Even(Succ(n))`), and a single family
    /// gains the same depth.
    fn iwf_inverted_motive(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &IwfFam,
        motive: &Type,
        mlvl: &Level,
        span: Span,
    ) -> R<Option<Type>> {
        let Some(ity) = ind.index_ty.as_ref() else {
            return Ok(None);
        };
        let Some((j, args)) = self.index_head(cx, ity, &fam.idx, span) else {
            return Ok(None);
        };
        // Every constructor's output index, at a generic payload, read to its
        // head.
        let n = ind.ctors.len();
        let (shape, slvl) = fam.shape();
        let spine = self.spine(shape, slvl, n, span)?;
        let mut outs: Vec<Cx> = Vec::with_capacity(n);
        let mut live: Vec<(usize, Vec<Rc<Term>>)> = Vec::new();
        for k in 0..n {
            let mut pcx = cx.clone();
            pcx.push("#p".into(), (*spine.ctors[k].0).clone(), spine.ctors[k].1.clone());
            let dcx = self.decl_payload_cx(&pcx, ind, &spine, k, &Rc::new(Term::Var(LocalVar(0))), 1, span)?;
            let res = {
                let _scope = self.use_inductive_scope(ind);
                self.elab_check(&dcx, res_expr(ind, k), &fam.ity.shift_local(1), &fam.ilvl)?
            };
            let Some((h, sub)) = self.index_head(&dcx, ity, &res, span) else {
                return Ok(None);
            };
            if h == j {
                live.push((k, sub));
            }
            outs.push(dcx);
        }
        // `Π(z : D(e)). M`, in Γ: what the innermost branch re-spells with
        // the index's arguments abstracted.
        let fl = fam.lvl();
        let whole = Type::Pi {
            dom_level: fl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.ty_at((*fam.idx).clone(), 0)),
            cod: Rc::new(motive.clone()),
        };
        let code_lvl = Level::succ(mlvl.clone());
        let inv = Inversion {
            base: cx.names.len(),
            whole: &whole,
            outs: &outs,
            fl: fl.clone(),
            mlvl: mlvl.clone(),
            code_lvl: code_lvl.clone(),
            case_lvl: Level::max(fl.clone(), code_lvl.clone()),
            missing_code: std::cell::Cell::new(false),
            span,
        };
        let body = |bcx: &Cx, k: usize, branch: &crate::indexed::IdxBranch, e: &Type| -> R<Term> {
            if k != j {
                return inv.unit(e);
            }
            let d = (bcx.names.len() - cx.names.len()) as u32;
            let items: Vec<InvItem> = args
                .iter()
                .zip(&branch.pat)
                .enumerate()
                .map(|(i, (a, (p, pty, _)))| InvItem {
                    arg: Rc::new(a.shift_local(d)),
                    pat: Rc::clone(p),
                    ty: pty.clone(),
                    subs: live.iter().map(|(c, sub)| (*c, Rc::clone(&sub[i]))).collect(),
                    value: branch.value.clone(),
                })
                .collect();
            self.inverted_level(bcx, &inv, e, items, Vec::new())
        };
        // The case's motive over (Γ, j, j'): `Π(z : D(j')). Ty mlvl`.
        let case_motive = Type::Pi {
            dom_level: fl.clone(),
            cod_level: code_lvl.clone(),
            dom: Rc::new(fam.ty_at(Term::Var(LocalVar(0)), 2)),
            cod: Rc::new(Type::Ty(mlvl.clone())),
        };
        let mut hcx = cx.clone();
        hcx.push("#j".into(), fam.ity.clone(), fam.ilvl.clone());
        let case = self.index_case(
            &hcx,
            ity,
            case_motive,
            &inv.case_lvl,
            Term::Var(LocalVar(0)),
            span,
            &body,
        )?;
        if inv.missing_code.get() {
            return Ok(None);
        }
        Ok(Some(Type::El {
            level: mlvl.clone(),
            tm: Rc::new(Term::AppAt {
                fun: Rc::new(case.shift_local(1)),
                arg: Rc::new(Term::Var(LocalVar(0))),
            }),
        }))
    }

    /// One level of [`Self::iwf_inverted_motive`]'s branch at the scrutinee's
    /// index: `e` is the branch's expected `Π(z : D(…)). Ty`, `items` the
    /// index-constructor arguments still to treat, `pairs` the abstractions
    /// so far (argument, pattern), all scoped in `bcx`.
    fn inverted_level(
        &self,
        bcx: &Cx,
        inv: &Inversion,
        e: &Type,
        items: Vec<InvItem>,
        mut pairs: Vec<(Term, Term)>,
    ) -> R<Term> {
        let span = inv.span;
        let Some((item, rest)) = items.split_first() else {
            return inv.leaf(bcx, e, &pairs);
        };
        let rest = rest.to_vec();
        // A variable is abstracted: every arm sees its own index there.
        if matches!(&*item.arg, Term::Var(_)) {
            pairs.push(((*item.arg).clone(), (*item.pat).clone()));
            return self.inverted_level(bcx, inv, e, rest, pairs);
        }
        // Constructor-headed, and so is every still-possible constructor's
        // output at this position: invert again.
        if let Some(nity) = self.index_ty_of(&item.ty)
            && let Some((h, inner)) = self.index_head(bcx, &nity, &item.arg, span)
            && let Some(heads) = item
                .subs
                .iter()
                .map(|(c, sub)| {
                    self.index_head(&inv.outs[*c], &nity, sub, span)
                        .map(|(hc, args)| (*c, hc, args))
                })
                .collect::<Option<Vec<_>>>()
            && let Some(motive) = rebuilt_goal(bcx, e, item.value.as_ref()).abstract_local(&item.pat)
        {
            let survivors: Vec<(usize, Vec<Rc<Term>>)> = heads
                .into_iter()
                .filter(|(_, hc, _)| *hc == h)
                .map(|(c, _, args)| (c, args))
                .collect();
            let alive: Vec<usize> = survivors.iter().map(|(c, _)| *c).collect();
            let nested = |ncx: &Cx, kk: usize, branch: &crate::indexed::IdxBranch, ne: &Type| -> R<Term> {
                if kk != h {
                    return inv.unit(ne);
                }
                let dd = (ncx.names.len() - bcx.names.len()) as u32;
                let mut next: Vec<InvItem> = inner
                    .iter()
                    .zip(&branch.pat)
                    .enumerate()
                    .map(|(i, (a, (p, pty, _)))| InvItem {
                        arg: Rc::new(a.shift_local(dd)),
                        pat: Rc::clone(p),
                        ty: pty.clone(),
                        subs: survivors.iter().map(|(c, args)| (*c, Rc::clone(&args[i]))).collect(),
                        value: branch.value.clone(),
                    })
                    .collect();
                next.extend(rest.iter().map(|it| InvItem {
                    arg: Rc::new(it.arg.shift_local(dd)),
                    pat: Rc::new(it.pat.shift_local(dd)),
                    ty: it.ty.shift_local(dd),
                    subs: it.subs.iter().filter(|(c, _)| alive.contains(c)).cloned().collect(),
                    value: it.value.as_ref().map(|(v, r)| {
                        (Rc::new(v.shift_local(dd)), Rc::new(r.shift_local(dd)))
                    }),
                }));
                let pairs = pairs
                    .iter()
                    .map(|(a, p)| (a.shift_local(dd), p.shift_local(dd)))
                    .collect();
                self.inverted_level(ncx, inv, ne, next, pairs)
            };
            return self.index_case(
                bcx,
                &nity,
                motive,
                &inv.case_lvl,
                (*item.pat).clone(),
                span,
                &nested,
            );
        }
        // Open and neither: abstracted where the motive writes it. A closed
        // one is not — its literals also spell the signature.
        if item.arg.shift_local(1) != *item.arg {
            pairs.push(((*item.arg).clone(), (*item.pat).clone()));
        }
        self.inverted_level(bcx, inv, e, rest, pairs)
    }

    /// What an index argument of type `ty` is inverted by, if anything: `Nat`,
    /// or a declared inductive that could itself be an index type.
    fn index_ty_of(&self, ty: &Type) -> Option<crate::inductive::IdxTy> {
        if matches!(ty, Type::Nat) {
            return Some(crate::inductive::IdxTy::Nat);
        }
        let ind = self.tag_of(ty)?;
        let usable = ind.params.is_empty()
            && ind.valparams.is_empty()
            && ind.index.is_none()
            && ind.members.is_empty()
            && !ind.codata
            && !ind.infinitary()
            && ind.ctors.iter().all(|c| c.container().is_none());
        usable.then_some(crate::inductive::IdxTy::Decl(ind))
    }

    /// Which member of a mutual group's family an index selects
    /// (docs/mutual-inductive-design.md §2), if its weak head says.
    pub(crate) fn iwf_member_at(
        &self,
        cx: &Cx,
        ind: &Inductive,
        idx: &Term,
        span: Span,
    ) -> Option<usize> {
        let ity = ind.index_ty.as_ref()?;
        self.index_head(cx, ity, idx, span).map(|(k, _)| k)
    }

    /// The index constructor heading `t` and its arguments, if `t`'s weak
    /// head is one.
    pub(crate) fn index_head(
        &self,
        cx: &Cx,
        ity: &crate::inductive::IdxTy,
        t: &Term,
        span: Span,
    ) -> Option<(usize, Vec<Rc<Term>>)> {
        let w = self.whnf_tm(cx, t, span).ok()?;
        match ity {
            crate::inductive::IdxTy::Nat => match &*w {
                Term::Zero => Some((0, vec![])),
                Term::Succ(a) => Some((1, vec![Rc::clone(a)])),
                Term::NatLit(k) => {
                    let k = usize::try_from(k.as_u64()?).ok()?;
                    (k > 0).then(|| (1, vec![Rc::new(nat_lit(k - 1))]))
                }
                _ => None,
            },
            crate::inductive::IdxTy::Decl(iind) => {
                let (ty, l) = self.lower_instance(cx, iind, &[], &[], span).ok()?;
                let spine = self.spine(&ty, &l, iind.ctors.len(), span).ok()?;
                self.read_ctor(cx, iind, &spine, &w, true, span).ok()?
            }
        }
    }


    /// `match` on an `IWf`-route family: one `elim_IWf` at the motive over
    /// `(Γ, j, z)`, its step a convoy case tree on the shape. Each arm is
    /// typed at its constructor's own output index; under an inverted motive
    /// ([`Self::iwf_match_motive`]) an arm whose goal is `Unit` is `tt`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_iwf(
        &self,
        cx: &Cx,
        form: MatchForm,
        ind: &Inductive,
        fam: &IwfFam,
        arms: &[Arm],
        scrut: Term,
        motive: Type,
        mlvl: Level,
        how: IndexMotive,
        span: Span,
    ) -> R<Term> {
        let inverted = how != IndexMotive::Plain;
        let n = ind.ctors.len();
        // A mutual group's `match` is on one member, and only that member's
        // constructors have arms (docs/mutual-inductive-design.md §4).
        let member = if ind.members.is_empty() {
            None
        } else {
            self.iwf_member_at(cx, ind, &fam.idx, span)
        };
        let shown = member.map_or(ind.name.as_str(), |m| ind.members[m].name.as_str());
        let mut ordered: Vec<Option<&Arm>> = vec![None; n];
        for a in arms {
            let Some(i) = crate::inductive::arm_ctor_index(ind, &a.ctor) else {
                return err(
                    format!("`{}` is not a constructor of `{shown}`", a.ctor),
                    a.span,
                );
            };
            if let Some(m) = member
                && ind.member_of_ctor(i) != Some(m)
            {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, not of `{shown}`: a `{}` on a \
                         `{shown}` has an arm for each of `{shown}`'s constructors",
                        a.ctor,
                        Self::member_name_of(ind, i),
                        form.keyword()
                    ),
                    a.span,
                );
            }
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
        // Under index inversion an arm may be left out; whether it could be
        // is decided per arm, by its goal (`Self::iwf_arm`).
        if !missing.is_empty() && !inverted && member.is_some() {
            // The other members' constructors are told apart only by the
            // inverted motive, which cases into the result type's code.
            return err(
                format!(
                    "this `{}` on a `{shown}` cannot set the rest of its mutual group \
                     aside: that takes its result type as a code, and this one has none \
                     (docs/mutual-inductive-design.md §4)",
                    form.keyword()
                ),
                span,
            );
        }
        if !missing.is_empty() && !inverted {
            return err(
                format!(
                    "`{}` is missing an arm for `{}`",
                    form.keyword(),
                    missing.join("`, `")
                ),
                span,
            );
        }

        let (shape, slvl) = fam.shape();
        let spine = self.spine(shape, slvl, n, span)?;
        let dec = crate::recursion::guard_param(cx, &scrut, arms);
        // The index a recursion may vary: the family's own when it is a
        // parameter, or a member's, under its member constructor
        // (docs/mutual-inductive-design.md §5).
        let param_at = |t: &Term| match t {
            Term::Var(LocalVar(i)) => {
                let pos = cx.names.len() - 1 - *i as usize;
                cx.selfref
                    .as_ref()
                    .filter(|s| pos < s.params.len())
                    .map(|_| pos)
            }
            _ => None,
        };
        let member_index = member.and_then(|_| {
            let (_, args) = self.index_head(cx, ind.index_ty.as_ref()?, &fam.idx, span)?;
            match args.as_slice() {
                [arg] => Some(Rc::clone(arg)),
                _ => None,
            }
        });
        let (idx_param, rebind_inner) = match (&dec, &member_index) {
            (Some(_), Some(arg)) => (param_at(arg), true),
            (Some(_), None) => (param_at(&fam.idx), false),
            _ => (None, false),
        };
        let env = ArmEnv {
            ind,
            fam,
            spine: &spine,
            ordered: &ordered,
            motive: &motive,
            gamma0: &cx.gamma,
            mlvl: &mlvl,
            dec,
            idx_param,
            rebind_inner,
            outer_guard: cx.guard.clone(),
            keyword: form.keyword(),
            span,
            inverted,
            motive_unit: how == IndexMotive::Inverted { unit: true },
        };
        let sig = match &fam.form {
            FamForm::IWf(sig) => sig,
            // A family with a function field eliminates by `elim_W` and
            // carries its equations by `J` (docs/iwf-infinitary-design.md §7).
            FamForm::W(sig) => return self.iw_match(cx, &env, sig, scrut),
        };
        let fl = sig.family_level();
        // The step telescope, `cs` in (Γ, a), `ih` in (Γ, a, cs), the step's
        // type in (Γ, a, cs, ih).
        let (cs_ty, ih_ty, st_ty) = self.iwf_match_telescope(cx, sig, &mlvl, &motive);
        // The convoy's motive over (Γ, a, x): the three re-abstracted at `x`.
        let convoy = Type::Pi {
            dom_level: fl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(cs_ty.shift_local_above(1, 1)),
            cod: Rc::new(Type::Pi {
                dom_level: mlvl.clone(),
                cod_level: mlvl.clone(),
                dom: Rc::new(ih_ty.shift_local_above(1, 2)),
                cod: Rc::new(st_ty.shift_local_above(1, 3)),
            }),
        };
        let mut acx = cx.clone();
        acx.push("#a".into(), (*sig.shape).clone(), sig.level.clone());
        let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, e: &Type| -> R<Term> {
            self.iwf_arm(bcx, &env, k, value, d, e)
        };
        let tree = self.idx_case_tree(
            &acx,
            &spine,
            spine.root(),
            convoy,
            &Level::max(fl.clone(), mlvl.clone()),
            Rc::new(Term::Var(LocalVar(0))),
            1,
            &body,
        )?;
        // The step, in (Γ, a, cs, ih): the tree applied to `cs` and `ih`.
        let step = crate::spelling::checked_app(
            Rc::new(crate::spelling::checked_app(
                Rc::new(tree.shift_local(2)),
                fl,
                mlvl.clone(),
                Rc::new(cs_ty.shift_local(2)),
                Rc::new(Type::Pi {
                    dom_level: mlvl.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(ih_ty.shift_local_above(2, 1)),
                    cod: Rc::new(st_ty.shift_local_above(2, 2)),
                }),
                Rc::new(Term::Var(LocalVar(1))),
            )),
            mlvl.clone(),
            mlvl.clone(),
            Rc::new(ih_ty.shift_local(1)),
            Rc::new(st_ty.shift_local_above(1, 1)),
            Rc::new(Term::Var(LocalVar(0))),
        );
        Ok(Term::ElimIWf {
            sig: Rc::clone(sig),
            motive_level: mlvl,
            motive: Rc::new(motive),
            step: Rc::new(step),
            index: Rc::clone(&fam.idx),
            scrut: Rc::new(scrut),
        })
    }

    /// One arm: `λcs'. λih'. body`, with the stored fields aliased to their
    /// projections out of the shape, the children to their components of
    /// `cs'`, and each child's ih to `ih'` at the child's position.
    fn iwf_arm(
        &self,
        bcx: &Cx,
        env: &ArmEnv,
        k: usize,
        value: &Rc<Term>,
        d: u32,
        expected: &Type,
    ) -> R<Term> {
        let ind = env.ind;
        let fam = env.fam;
        let ctor = &ind.ctors[k];
        let span = env.ordered[k].map_or(env.span, |a| a.span);
        let Type::Pi { dom: cs_dom, cod, .. } = expected else {
            return err("internal: the IWf step's convoy motive is not a Π", span);
        };
        let Type::Pi { dom: ih_dom, .. } = &**cod else {
            return err("internal: the IWf step's convoy motive is not a Π", span);
        };
        let fl = fam.lvl();
        let mlvl = env.mlvl;
        let mut ccx = bcx.clone();
        ccx.push("#cs".into(), (**cs_dom).clone(), fl.clone());
        ccx.push("#ih".into(), (**ih_dom).clone(), mlvl.clone());
        let dd = d + 2;
        let value_here = Rc::new(value.shift_local(2));
        let FamForm::IWf(sig) = &fam.form else {
            return err("internal: an IWf arm on the W encoding", span);
        };
        let sig_here = sig.shift_local(dd);
        let ity_here = fam.ity.shift_local(dd);
        let label = inject(env.spine, k, ind.ctors.len(), (*value_here).clone(), dd);
        // The declaration's own index expressions, at this shape.
        let (res_term, kid_idx) = {
            let dcx = self.decl_payload_cx(&ccx, ind, env.spine, k, &value_here, dd, span)?;
            let _scope = self.use_inductive_scope(ind);
            let res = self.elab_check(&dcx, res_expr(ind, k), &ity_here, &fam.ilvl)?;
            let mut kids = Vec::new();
            for e in child_exprs(ind, k) {
                kids.push(self.elab_check(&dcx, e, &ity_here, &fam.ilvl)?);
            }
            (res, kids)
        };
        // Index inversion (design §8.3): an arm whose constructor cannot
        // build the scrutinee's index has the goal `Unit`, and is `tt`
        // whether or not it was written.
        let sup = sig_here.supi(Rc::new(label.clone()), Rc::new(Term::Var(LocalVar(1))));
        let goal = env.mot_at(res_term.clone(), sup.clone(), dd);
        let goal = if env.inverted {
            let g = self.whnf(&ccx, &goal, span)?;
            if let Type::Unit { level } = &g
                && !env.motive_unit
            {
                return Ok(lam2(fl, mlvl, cs_dom, ih_dom, Term::Triv { level: level.clone() }));
            }
            crate::inductive::decode_deep(&g).unwrap_or(g)
        } else {
            goal
        };
        let Some(arm) = env.ordered[k] else {
            return err(
                format!(
                    "`{}` is missing an arm for `{}`",
                    env.keyword, ctor.name
                ),
                span,
            );
        };
        let mut acx = ccx.clone();
        let names: Vec<Option<String>> = arm
            .binders
            .iter()
            .map(|b| Some(b.name().to_string()))
            .collect();
        self.payload_aliases(&mut acx, ind, env.spine, k, &value_here, dd, &names, span)?;
        // The children: `fst (snd^t cs')`, annotated at `DVec`'s successor
        // reducts at the literal length.
        let m = kid_idx.len();
        let depth = acx.names.len();
        let mut children: Vec<(Rc<Term>, Rc<Term>, Type, Level)> = Vec::new();
        let mut rebind: Vec<Rc<Term>> = Vec::new();
        let mut rest = Term::Var(LocalVar(1));
        let mut kfam = Rc::new(iwf_fam(&sig_here, &label));
        let mut t = 0usize;
        for (fi, kind) in ctor.kind.iter().enumerate() {
            if *kind != FieldKind::Plain {
                continue;
            }
            let pred = Rc::new(nat_lit(m - t - 1));
            let (head, tail) = dvec_succ_parts(&fl, &pred, &kfam);
            let (head, tail) = (Rc::new(head), Rc::new(tail));
            let child = Term::Fst {
                fst_level: fl.clone(),
                snd_level: fl.clone(),
                fst_ty: Rc::clone(&head),
                snd_ty: Rc::clone(&tail),
                pair: Rc::new(rest.clone()),
            };
            rest = Term::Snd {
                fst_level: fl.clone(),
                snd_level: fl.clone(),
                fst_ty: head,
                snd_ty: tail,
                pair: Rc::new(rest),
            };
            kfam = Rc::new(kfam.inst_top(
                1,
                &fin_next(Rc::new(pred.shift_local(1)), Rc::new(Term::Var(LocalVar(0)))),
            ));
            let at = kid_idx[t].clone();
            let ih = Term::AppAt {
                fun: Rc::new(Term::Var(LocalVar(0))),
                arg: Rc::new(fin_index(t, m, &Term::Zero)),
            };
            let ih_ty = env.mot_at(at.clone(), child.clone(), dd);
            acx.aliases.push(Rc::new(Alias {
                skel: None,
                name: arm.binders[fi].name().to_string(),
                depth,
                term: Rc::new(child.clone()),
                ty: sig_here.at(Rc::new(at.clone())),
                level: fl.clone(),
                spliced: None,
                shifted: Default::default(),
            }));
            children.push((Rc::new(child), Rc::new(ih), ih_ty, mlvl.clone()));
            // Under a member constructor the varying index is the member's
            // own, the constructor's one argument.
            let at = if env.rebind_inner {
                self.index_head(&acx, ind.index_ty.as_ref().expect("a member's family is indexed"), &at, span)
                    .and_then(|(_, args)| args.first().map(|a| (**a).clone()))
                    .unwrap_or(at)
            } else {
                at
            };
            rebind.push(Rc::new(at));
            t += 1;
        }
        if !children.is_empty() {
            acx.guard = env
                .dec
                .map(|dec| {
                    Rc::new(Guard {
                        dec,
                        kind: GuardKind::Wf {
                            depth: acx.names.len(),
                            children,
                            container: None,
                            fn_children: Vec::new(),
                            // An indexed family is not chain-shaped for the
                            // window's purposes.
                            cov: None,
                        },
                        rebind: env.idx_param.map(|p| (p, rebind)),
                        generalized: crate::generalize::guard_gen(&acx, dec, None),
                    })
                })
                .or_else(|| env.outer_guard.clone());
        }
        let body = self.elab_check(&acx, &arm.body, &goal, mlvl)?;
        Ok(lam2(fl, mlvl, cs_dom, ih_dom, body))
    }
}

/// `λcs. λih. body`, an arm of the step's convoy.
fn lam2(fl: Level, mlvl: &Level, cs_dom: &Rc<Type>, ih_dom: &Rc<Type>, body: Term) -> Term {
    Term::Lam {
        dom_level: fl,
        cod_level: mlvl.clone(),
        dom: Rc::clone(cs_dom),
        body: Rc::new(Term::Lam {
            dom_level: mlvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::clone(ih_dom),
            body: Rc::new(body),
        }),
    }
}

/// `⟨v_0, ⟨v_1, … ⟨⟩⟩⟩ : DVec(n[label]; k. IWf(…)(c[label, k]))`, annotated
/// at `DVec`'s successor reducts at the literal length.
fn dvec_tuple(sig: &Rc<IWfSig>, label: &Term, kids: Vec<Term>) -> Term {
    let fl = sig.family_level();
    let m = kids.len();
    // The family at each position, front to back.
    let mut fams = Vec::with_capacity(m);
    let mut kfam = Rc::new(iwf_fam(sig, label));
    for t in 0..m {
        let pred = Rc::new(nat_lit(m - t - 1));
        let next = Rc::new(kfam.inst_top(
            1,
            &fin_next(Rc::new(pred.shift_local(1)), Rc::new(Term::Var(LocalVar(0)))),
        ));
        fams.push((pred, kfam));
        kfam = next;
    }
    let mut acc = Term::Triv { level: fl.clone() };
    for (v, (pred, kfam)) in kids.into_iter().zip(fams).rev() {
        let (head, tail) = dvec_succ_parts(&fl, &pred, &kfam);
        acc = Term::Pair {
            fst_level: fl.clone(),
            snd_level: fl.clone(),
            fst_ty: Rc::new(head),
            snd_ty: Rc::new(tail),
            fst: Rc::new(v),
            snd: Rc::new(acc),
        };
    }
    acc
}

/// Everything an arm needs beyond its own binders, gathered once.
pub(crate) struct ArmEnv<'a> {
    pub(crate) ind: &'a Inductive,
    pub(crate) fam: &'a IwfFam,
    pub(crate) spine: &'a Spine,
    pub(crate) ordered: &'a [Option<&'a Arm>],
    /// `M`, over `(Γ, j, z)`.
    pub(crate) motive: &'a Type,
    pub(crate) gamma0: &'a LocalCtx,
    pub(crate) mlvl: &'a Level,
    pub(crate) dec: Option<usize>,
    pub(crate) idx_param: Option<usize>,
    /// The varying index is the member constructor's argument, not the
    /// family's index itself (docs/mutual-inductive-design.md §5).
    pub(crate) rebind_inner: bool,
    pub(crate) outer_guard: Option<Rc<Guard>>,
    pub(crate) keyword: &'static str,
    pub(crate) span: Span,
    /// The motive inverts the scrutinee's index (design §8.3, tier 1).
    pub(crate) inverted: bool,
    /// The written motive is itself `Unit`, so a `Unit` goal says nothing
    /// about whether an arm is reachable.
    pub(crate) motive_unit: bool,
}

/// How a `match`'s motive treats the scrutinee's index
/// (`docs/iwf-former-design.md` §8.3).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IndexMotive {
    /// Generalized: the index abstracted (tier 2), or the motive as given.
    Plain,
    /// Inverted by the index type's eliminator (tier 1); `unit` when the
    /// written motive is `Unit` itself.
    Inverted { unit: bool },
}

impl ArmEnv<'_> {
    /// `M[m, z]`, with `m`/`z` scoped `extra` binders past Γ.
    pub(crate) fn mot_at(&self, m: Term, z: Term, extra: u32) -> Type {
        self.motive.apply_local(
            &embed(self.gamma0, extra)
                .extended(Rc::new(m))
                .extended(Rc::new(z)),
        )
    }
}

/// The fixed part of one inverted motive ([`Elaborator::iwf_inverted_motive`]).
struct Inversion<'a> {
    /// `cx.names.len()` of the ambient context, Γ.
    base: usize,
    /// `Π(z : D(e)). M`, scoped in Γ.
    whole: &'a Type,
    /// Per family constructor: the context its generic output index is
    /// scoped in.
    outs: &'a [Cx],
    fl: Level,
    mlvl: Level,
    code_lvl: Level,
    /// The level of a case's motive, `Π(z : D(…)). Ty mlvl`.
    case_lvl: Level,
    missing_code: std::cell::Cell<bool>,
    span: Span,
}

impl Inversion<'_> {
    /// `λ(z : D(…)). code`, at the branch's expected `Π`.
    fn lam(&self, e: &Type, code: Term) -> R<Term> {
        let Type::Pi { dom, .. } = e else {
            return err("internal: the inversion's motive is not a Π", self.span);
        };
        Ok(Term::Lam {
            dom_level: self.fl.clone(),
            cod_level: self.code_lvl.clone(),
            dom: Rc::clone(dom),
            body: Rc::new(code),
        })
    }

    /// A branch no constructor reaches: `Unit`.
    fn unit(&self, e: &Type) -> R<Term> {
        self.lam(e, Term::TmUnit { level: self.mlvl.clone() })
    }

    /// The innermost branch: `M` with every abstraction made, as a code.
    fn leaf(&self, bcx: &Cx, e: &Type, pairs: &[(Term, Term)]) -> R<Term> {
        let d = (bcx.names.len() - self.base) as u32;
        let here = self.whole.shift_local(d);
        let shifted: Vec<(Term, Term)> =
            pairs.iter().map(|(a, p)| (a.clone(), p.shift_local(1))).collect();
        let here = match here.abstract_local_with_all(&shifted) {
            Some(t) => t.apply_local(&LocalSubst::id(&bcx.gamma).extended(Rc::new(Term::Zero))),
            None => here,
        };
        let Type::Pi { cod, .. } = here else {
            return err("internal: the inversion's branch is not a Π", self.span);
        };
        let code = match crate::code::code_of(&cod) {
            Some(c) => c,
            None => {
                self.missing_code.set(true);
                Term::TmUnit { level: self.mlvl.clone() }
            }
        };
        self.lam(e, code)
    }
}

/// One index-constructor argument still to treat at a level of the inverted
/// motive: the scrutinee's argument and the branch's pattern for it (both in
/// the branch's context), the pattern's type, and each still-possible
/// constructor's output at this position (in that constructor's context).
#[derive(Clone)]
struct InvItem {
    arg: Rc<Term>,
    pat: Rc<Term>,
    ty: Type,
    subs: Vec<(usize, Rc<Term>)>,
    /// The branch's payload value and its rebuilt spelling
    /// ([`crate::indexed::IdxBranch::value`]), for a pattern projected out
    /// of one.
    value: Option<(Rc<Term>, Rc<Term>)>,
}

/// The branch's goal with its payload value spelled by its projections, so
/// that a pattern projected out of it occurs in the goal and can be
/// abstracted. Equal to `e` by η; unchanged where the pattern is a binder.
fn rebuilt_goal(cx: &Cx, e: &Type, value: Option<&(Rc<Term>, Rc<Term>)>) -> Type {
    let Some((v, r)) = value else {
        return e.clone();
    };
    match e.abstract_local_with(v, &r.shift_local(1)) {
        Some(t) => t.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero))),
        None => e.clone(),
    }
}

/// A signature's index value — an arm of `o` or a leaf of `c` — without the
/// annotation on its outermost injection or tuple. The arm is checked
/// against the index type, so the annotation is a conversion the kernel pays
/// at every occurrence of the signature; and it names the index type's code
/// as a global, whose substitution records Γ's length, so a signature that
/// keeps it is never locally closed and is rebuilt under every binder
/// (`issues/mutual-group-recursion-gate-cost.md`).
fn index_value(t: Term) -> Term {
    match t {
        Term::InlAt { ty: Some(_), val } => Term::InlAt { ty: None, val },
        Term::InrAt { ty: Some(_), val } => Term::InrAt { ty: None, val },
        Term::PairAt { ty: Some(_), fst, snd } => Term::PairAt { ty: None, fst, snd },
        t => t,
    }
}

#[cfg(test)]
mod named_signature {
    //! `docs/iwf-named-signature-design.md`: an `IWf`-route family at the
    //! registered profile is spelled over `D#iarity`/`D#iout`/`D#ichild`, its
    //! `match` over `D#idnth`, and an instance off the profile stays inline.
    //! Each source also runs a `match` and a `refl` unfolding through the
    //! kernel, so the references are checked where they are used.

    use super::*;

    const SPAN: Span = Span { start: 0, end: 0 };

    const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n";

    fn declared(src: &str, name: &str) -> (Elaborator, Rc<Inductive>) {
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(&format!("{ADD}{src}")).expect("the source elaborates and checks");
        let ind = Rc::clone(el.types.inductive(&crate::names::qkey("main", name)).expect("declared"));
        (el, ind)
    }

    fn registered(el: &Elaborator, ind: &Inductive) {
        for key in [GenDef::IArity(ind.tag), GenDef::IOut(ind.tag), GenDef::IChild(ind.tag), GenDef::IDnth(ind.tag)] {
            assert!(el.types.gdefs().abs_for(&key).is_some(), "`{}` registered", key.name(&ind.name));
        }
    }

    /// Whether each index function of `sig` is the registered definition's
    /// application, `None` per component when it is spelled inline.
    fn heads(el: &Elaborator, sig: &IWfSig) -> [Option<GenDef>; 3] {
        [&sig.arity, &sig.out, &sig.child].map(|t| el.gen_app_of(t).map(|(key, _)| key))
    }

    /// A family indexed by a *recursive* type: its index values are
    /// constructor values whose `sup_f` slots name the index type's shape
    /// and arity definitions. Registration builds them after the index
    /// type's code was pushed in the same attempt, and the attempt's shared
    /// annotations were once keyed without the Ψ scope, so they named every
    /// global one too close and the kernel refused `V#iout`; the family then
    /// silently stayed inline.
    #[test]
    fn a_family_indexed_by_a_recursive_type_is_named() {
        let (el, v) = declared(
            "inductive Ty { TNat, TArr(a: Ty, b: Ty) }
             inductive V : (t: Ty) -> Type { A : V(TNat), C(a: Ty, v: V(a)) : V(TArr(a, a)) }
             fn depth(t: Ty, v: V(t)) -> Nat { match v { A => 0, C(a, w) => Succ(depth(a, w)) } }
             theorem depth_c(a: Ty, w: V(a)): depth(TArr(a, a), C(a, w)) = Succ(depth(a, w)) { refl }
             theorem depth_closed(): depth(TArr(TNat, TNat), C(TNat, A)) = 1 { refl }",
            "V",
        );
        registered(&el, &v);
        let sig = el.iwf_sig(&Cx::empty(), &v, &[], SPAN).expect("signature");
        let t = v.tag;
        assert_eq!(heads(&el, &sig), [Some(GenDef::IArity(t)), Some(GenDef::IOut(t)), Some(GenDef::IChild(t))]);
        let nth = el.iwf_named_dnth(&Cx::empty(), &sig).expect("the ih is spelled with `V#idnth`");
        assert!(matches!(el.gen_app_of(&nth), Some((GenDef::IDnth(k), _)) if k == t));
    }

    /// A mutual group's family, the case the round was for: one `IWf` over
    /// the generated member sum.
    #[test]
    fn a_mutual_group_family_is_named() {
        let (el, fam) = declared(
            "inductive M0 { L0, N0(a: M1, b: M0) }
             inductive M1 { L1, N1(a: M2, b: M1) }
             inductive M2 { L2, N2(a: M0, b: M2) }
             fn size0(t: M0) -> Nat { match t { L0 => 1, N0(a, b) => add(size1(a), size0(b)) } }
             fn size1(t: M1) -> Nat { match t { L1 => 1, N1(a, b) => add(size2(a), size1(b)) } }
             fn size2(t: M2) -> Nat { match t { L2 => 1, N2(a, b) => add(size0(a), size2(b)) } }
             theorem size_node(a: M1, b: M0): size0(N0(a, b)) = add(size1(a), size0(b)) { refl }",
            &crate::mutual_family::family_name("M0"),
        );
        registered(&el, &fam);
        let sig = el.iwf_sig(&Cx::empty(), &fam, &[], SPAN).expect("signature");
        let t = fam.tag;
        assert_eq!(heads(&el, &sig), [Some(GenDef::IArity(t)), Some(GenDef::IOut(t)), Some(GenDef::IChild(t))]);
    }

    /// A type parameter: the definitions abstract it, an instance at a
    /// `Ty 0` argument applies them to its code, and one at `Type` itself
    /// (`Ty 0`, a `Ty 1` argument) is off the profile and stays inline.
    #[test]
    fn a_parameter_at_the_profile_is_applied_and_one_off_it_stays_inline() {
        let (el, p) = declared(
            "inductive Ty { TNat, TArr(a: Ty, b: Ty) }
             inductive P<X> : (t: Ty) -> Type { PA(x: X) : P<X>(TNat), PC(a: Ty, v: P<X>(a)) : P<X>(TArr(a, a)) }
             fn count(t: Ty, v: P<Nat>(t)) -> Nat { match v { PA(x) => x, PC(a, w) => Succ(count(a, w)) } }
             theorem count_closed(): count(TArr(TNat, TNat), PC(TNat, PA(3))) = 4 { refl }",
            "P",
        );
        registered(&el, &p);
        let t = p.tag;
        let at_nat = el.iwf_sig(&Cx::empty(), &p, &[(Type::Nat, Level::Zero)], SPAN).expect("signature at Nat");
        assert_eq!(heads(&el, &at_nat), [Some(GenDef::IArity(t)), Some(GenDef::IOut(t)), Some(GenDef::IChild(t))]);
        let at_type = el
            .iwf_sig(&Cx::empty(), &p, &[(Type::Ty(Level::Zero), Level::succ(Level::Zero))], SPAN)
            .expect("signature at Type");
        assert_eq!(heads(&el, &at_type), [None, None, None]);
        assert!(el.iwf_named_dnth(&Cx::empty(), &at_type).is_none());
    }
}
