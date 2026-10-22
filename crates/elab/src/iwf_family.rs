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
    IWfSig, LocalCtx, LocalSubst, LocalVar, Term, Type, dvec_succ_parts, fin_next, iwf_fam,
    iwf_step_telescope,
};
use heather_syntax::ast::{Arm, Expr, MatchForm, Span};

use crate::inductive::{FieldKind, Inductive, Spine, inject, nat_lit, tag_value};
use crate::recursion::{Guard, GuardKind};
use crate::wf::fin_index;
use crate::{Alias, Cx, Elaborator, R, embed, err};

/// A type in `IWf` family form, read back: the signature, the index it is
/// applied at, and the index type (the signature's, kept apart for the
/// callers that build motives over it).
pub(crate) struct IwfFam {
    pub sig: Rc<IWfSig>,
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
        IwfFam { sig, idx, ity, ilvl }
    }

    /// `l ⊔ li` — the family's own level.
    pub fn lvl(&self) -> Level {
        self.sig.family_level()
    }

    /// `IWf(…)(m)` with `m` and the result scoped `by` binders past the
    /// ambient context.
    pub fn ty_at(&self, m: Term, by: u32) -> Type {
        self.sig.shift_local(by).at(Rc::new(m))
    }
}

/// The number of children of constructor `k`.
fn children_of(ind: &Inductive, k: usize) -> usize {
    ind.ctors[k].kind.iter().filter(|f| **f == FieldKind::Plain).count()
}

/// The written result index (design §8.1). Present on every constructor of an
/// `IWf`-route declaration, by construction.
fn res_expr(ind: &Inductive, k: usize) -> &Expr {
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
        .zip(&ctor.child_idx)
        .filter(|(f, _)| **f == FieldKind::Plain)
        .map(|(_, e)| e.as_ref().expect("an IWf-route child carries its index"))
        .collect()
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
            return None;
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
        let sig = self.iwf_sig(cx, ind, args, span)?;
        let lvl = sig.family_level();
        Ok((sig.at(Rc::new(idx)), lvl))
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
            n,
            0,
            Type::Nat,
            &Level::Zero,
            Rc::clone(&x),
            1,
            &arity_body,
        )?;
        // o(x): the written result index over the stored fields.
        let out_body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _: &Type| -> R<Term> {
            let acx = self.decl_payload_cx(bcx, ind, &spine, k, value, d, span)?;
            self.elab_check(&acx, res_expr(ind, k), &ity.shift_local(d), &ilvl)
        };
        let out = self.idx_case_tree(
            &xcx,
            &spine,
            n,
            0,
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
            n,
            0,
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
            idx: Rc::new(ity),
            shape: Rc::new(shape),
            arity: Rc::new(arity),
            out: Rc::new(out),
            child: Rc::new(child),
        }))
    }

    /// One shape branch's context for the declaration's own index
    /// expressions: each stored field, under its **declared** name, aliased
    /// to its projection out of the branch's value. `d` counts the binders
    /// pushed since `spine` was read back.
    #[allow(clippy::too_many_arguments)]
    fn decl_payload_cx(
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
    fn payload_aliases(
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
        let case_l = self.elab_check(&lcx, exprs[t], &ity.shift_local(depth + 1), ilvl)?;
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
        let sig = &fam.sig;
        let n = ind.ctors.len();
        let spine = self.spine(&sig.shape, &sig.level, n, span)?;
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
        // The children, each at the index written for it.
        let mut kids: Vec<Term> = Vec::new();
        for (k, kind) in ctor.kind.iter().enumerate() {
            if *kind != FieldKind::Plain {
                continue;
            }
            let e = ctor.child_idx[k]
                .as_ref()
                .expect("an IWf-route child carries its index");
            let x = {
                let _scope = self.use_inductive_scope(ind);
                self.elab_check(&acx, e, &fam.ity, &fam.ilvl)?
            };
            kids.push(self.elab_check(cx, args[k].borrow(), &fam.ty_at(x, 0), &fam.lvl())?);
        }
        let children = dvec_tuple(sig, &label, kids);
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
            return err(
                format!(
                    "`{}` constructs `{}` at its written result index, which is not the \
                     expected index",
                    ctor.name, ind.name
                ),
                span,
            );
        }
        Ok(sig.supi(Rc::new(label), Rc::new(children)))
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
        if self.emits_at_forms(cx) {
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
            heather_kernel::typing::check_type(&psi, 0, Layer::Prog, &jcx.gamma, m, mlvl, self.fuel)
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
        // Every constructor's output index, at a generic payload.
        let n = ind.ctors.len();
        let spine = self.spine(&fam.sig.shape, &fam.sig.level, n, span)?;
        for k in 0..n {
            let mut pcx = cx.clone();
            pcx.push("#p".into(), (*spine.ctors[k].0).clone(), spine.ctors[k].1.clone());
            let dcx = self.decl_payload_cx(&pcx, ind, &spine, k, &Rc::new(Term::Var(LocalVar(0))), 1, span)?;
            let res = {
                let _scope = self.use_inductive_scope(ind);
                self.elab_check(&dcx, res_expr(ind, k), &fam.ity.shift_local(1), &fam.ilvl)?
            };
            if self.index_head(&dcx, ity, &res, span).is_none() {
                return Ok(None);
            }
        }
        // `Π(z : D(e)). M`, in Γ: what the branch at `e`'s constructor
        // re-spells with the constructor's arguments abstracted.
        let fl = fam.lvl();
        let whole = Type::Pi {
            dom_level: fl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.ty_at((*fam.idx).clone(), 0)),
            cod: Rc::new(motive.clone()),
        };
        let code_lvl = Level::succ(mlvl.clone());
        let missing_code = std::cell::Cell::new(false);
        let body = |bcx: &Cx, k: usize, branch: &crate::indexed::IdxBranch, e: &Type| -> R<Term> {
            let Type::Pi { dom, .. } = e else {
                return err("internal: the inversion's motive is not a Π", span);
            };
            let d = (bcx.names.len() - cx.names.len()) as u32;
            let code = if k == j {
                // Only a *variable* argument is abstracted: a closed one
                // (the `0` of `V(1)`) would also be found inside the family's
                // signature, whose case trees spell their own literals.
                let pairs: Vec<(Term, Term)> = args
                    .iter()
                    .zip(&branch.pat)
                    .filter(|(a, _)| matches!(&***a, Term::Var(_)))
                    .map(|(a, (p, _, _))| (a.shift_local(d), p.shift_local(1)))
                    .collect();
                let here = whole.shift_local(d);
                let here = match here.abstract_local_with_all(&pairs) {
                    Some(t) => t.apply_local(&LocalSubst::id(&bcx.gamma).extended(Rc::new(Term::Zero))),
                    None => here,
                };
                let Type::Pi { cod, .. } = here else {
                    return err("internal: the inversion's branch is not a Π", span);
                };
                match crate::code::code_of(&cod) {
                    Some(c) => c,
                    None => {
                        missing_code.set(true);
                        Term::TmUnit { level: mlvl.clone() }
                    }
                }
            } else {
                Term::TmUnit { level: mlvl.clone() }
            };
            Ok(Term::Lam {
                dom_level: fl.clone(),
                cod_level: code_lvl.clone(),
                dom: Rc::clone(dom),
                body: Rc::new(code),
            })
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
            &Level::max(fl.clone(), code_lvl.clone()),
            Term::Var(LocalVar(0)),
            span,
            &body,
        )?;
        if missing_code.get() {
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

    /// The index constructor heading `t` and its arguments, if `t`'s weak
    /// head is one.
    fn index_head(
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
        // Under index inversion an arm may be left out; whether it could be
        // is decided per arm, by its goal (`Self::iwf_arm`).
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

        let sig = &fam.sig;
        let fl = sig.family_level();
        let spine = self.spine(&sig.shape, &sig.level, n, span)?;
        // The step telescope, `cs` in (Γ, a), `ih` in (Γ, a, cs), the step's
        // type in (Γ, a, cs, ih).
        let (cs_ty, ih_ty, st_ty) = iwf_step_telescope(sig, &mlvl, &motive);
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
        let dec = crate::recursion::descends_on_param(cx, &scrut);
        let idx_param = match (&dec, &*fam.idx) {
            (Some(_), Term::Var(LocalVar(i))) => {
                let pos = cx.names.len() - 1 - *i as usize;
                cx.selfref
                    .as_ref()
                    .filter(|s| pos < s.params.len())
                    .map(|_| pos)
            }
            _ => None,
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
            outer_guard: cx.guard.clone(),
            keyword: form.keyword(),
            span,
            inverted,
            motive_unit: how == IndexMotive::Inverted { unit: true },
        };
        let mut acx = cx.clone();
        acx.push("#a".into(), (*sig.shape).clone(), sig.level.clone());
        let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, e: &Type| -> R<Term> {
            self.iwf_arm(bcx, &env, k, value, d, e)
        };
        let tree = self.idx_case_tree(
            &acx,
            &spine,
            n,
            0,
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
        let sig_here = fam.sig.shift_local(dd);
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
            }));
            children.push((Rc::new(child), Rc::new(ih), ih_ty, mlvl.clone()));
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
struct ArmEnv<'a> {
    ind: &'a Inductive,
    fam: &'a IwfFam,
    spine: &'a Spine,
    ordered: &'a [Option<&'a Arm>],
    /// `M`, over `(Γ, j, z)`.
    motive: &'a Type,
    gamma0: &'a LocalCtx,
    mlvl: &'a Level,
    dec: Option<usize>,
    idx_param: Option<usize>,
    outer_guard: Option<Rc<Guard>>,
    keyword: &'static str,
    span: Span,
    /// The motive inverts the scrutinee's index (design §8.3, tier 1).
    inverted: bool,
    /// The written motive is itself `Unit`, so a `Unit` goal says nothing
    /// about whether an arm is reachable.
    motive_unit: bool,
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
    fn mot_at(&self, m: Term, z: Term, extra: u32) -> Type {
        self.motive.apply_local(
            &embed(self.gamma0, extra)
                .extended(Rc::new(m))
                .extended(Rc::new(z)),
        )
    }
}
