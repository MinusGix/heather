//! Tier 2: an inductive with a recursive **function** field, lowered on the
//! `W` former (docs/inductive-tier2-w-lowering.md). The section numbers below
//! are that document's.
//!
//! ```text
//! W₀   = W(x : S). P(x)                       S: tier 1's shape, P: §4
//! ⟦D⟧  = Σ(t : W₀). El(canon t)               canon: §2.4, §5
//! ```
//!
//! Everything a constructor or a `match` needs is read back off `⟦D⟧` itself
//! ([`WParts::read`]), never regenerated from the declaration — tier 0's
//! annotation discipline. The shape's spine is tier 0's, read through
//! [`Elaborator::spine`], and the case trees over it are tier 0 §6.1's
//! right-nested `Case` with the motive composed with the injection at each
//! depth ([`Elaborator::w_case_tree`]).
//!
//! Scoping convention, used by every [`WParts`] helper: `k` counts the
//! binders pushed since the context `⟦D⟧` was read back in (`g`), and every
//! term argument is already scoped at that depth.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Arm, Expr, Span};

use crate::gendefs::GenDef;
use crate::inductive::{FieldKind, Inductive, Spine, decoded, inject, tag_type, tag_value};
use crate::sum_layout::Child;
use crate::recursion::{FnChildIh, Guard, GuardKind};
use crate::spelling::checked_app;
use crate::{Alias, Cx, Elaborator, R, embed, err};
use crate::gendefs::GeneratedDefs;
use crate::inductive::Inductives;

fn var(i: u32) -> Rc<Term> {
    Rc::new(Term::Var(LocalVar(i)))
}

/// `f a` at a head that infers its own Π — a variable or an eliminator — so
/// the checked spelling needs no annotations.
fn app_at(fun: Rc<Term>, arg: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::AppAt { fun, arg })
}

/// `⟦D⟧`'s shape and its level, when `ty` is a tier-2 lowering: what
/// [`Elaborator::spine`] and [`Elaborator::tag_of`] read through.
pub(crate) fn w_of(ty: &Type) -> Option<(Rc<Type>, Level)> {
    let p = WParts::read(ty, &LocalCtx::nil())?;
    Some((p.shape, p.ls))
}

/// Whether `t` is an application spine whose head is a global: the named
/// leaf predicate, `app(D#canon^δ; ā, t)`. It always has at least the tree
/// as an argument.
fn canon_app(t: &Term) -> bool {
    let mut cur = t;
    let mut applied = false;
    while let Some((fun, _)) = crate::spelling::app_of(cur) {
        cur = fun;
        applied = true;
    }
    applied && matches!(cur, Term::GlobalTm { .. })
}

/// What a constructor contributes to the positions and the leaf predicate:
/// its recursive field's kind (§4).
enum Kind {
    Leaf,
    Plain,
    /// The function field's domain as a code, scoped over `(Γ, #tag, p₀, …,
    /// p_{j-1})`, and that `j`.
    Fn(Rc<Term>, usize),
}

/// The components of `⟦D⟧ = Σ(t : W(x:S). P). El(canon t)`, scoped in `g`.
pub(crate) struct WParts {
    g: LocalCtx,
    pub ls: Level,
    pub lp: Level,
    pub lw: Level,
    pub shape: Rc<Type>,
    /// `P`, over `(g, x : S)`.
    pub pos: Rc<Type>,
    /// `El(canon t)`, over `(g, t : W₀)`.
    canon: Rc<Type>,
}

impl WParts {
    /// Read a lowered `⟦D⟧` back. Context-free: it only takes the type apart.
    /// The `El(elim_W …)` check on the second component is what tells this
    /// encoding apart from a `Σ` that merely has a `W` first.
    pub(crate) fn read(ty: &Type, g: &LocalCtx) -> Option<WParts> {
        let ty = decoded(ty);
        let Type::Sigma { fst_level, fst, snd, .. } = &*ty else {
            return None;
        };
        let fst = decoded(fst);
        let Type::W { shape_level, pos_level, shape, pos } = &*fst else {
            return None;
        };
        // Inline, the predicate is an `elim_W`; named, an application of the
        // declaration's `D#canon` (`Elaborator::w_canon_ref`). Neither is read
        // further: the second component is reused exactly as it was found.
        match &**snd {
            Type::El { tm, .. } if matches!(&**tm, Term::ElimW { .. }) || canon_app(tm) => {}
            _ => return None,
        }
        Some(WParts {
            g: g.clone(),
            ls: shape_level.clone(),
            lp: pos_level.clone(),
            lw: fst_level.clone(),
            shape: Rc::clone(shape),
            pos: Rc::clone(pos),
            canon: Rc::clone(snd),
        })
    }

    /// `Π(y : P a). W₀`'s level, the leaf equation's.
    fn lf(&self) -> Level {
        Level::join(self.lp.clone(), self.lw.clone())
    }

    fn w0(&self) -> Type {
        Type::W {
            shape_level: self.ls.clone(),
            pos_level: self.lp.clone(),
            shape: Rc::clone(&self.shape),
            pos: Rc::clone(&self.pos),
        }
    }

    fn w0_at(&self, k: u32) -> Type {
        self.w0().shift_local(k)
    }

    /// `P(label)`.
    fn pos_at(&self, k: u32, label: Rc<Term>) -> Type {
        self.pos.apply_local(&embed(&self.g, k).extended(label))
    }

    /// `P` in a binder slot at depth `k` (the slot's own variable is `x`).
    fn pos_under(&self, k: u32) -> Type {
        self.pos_at(k + 1, var(0))
    }

    /// `El(canon t)`.
    fn canon_at(&self, k: u32, t: Rc<Term>) -> Type {
        self.canon.apply_local(&embed(&self.g, k).extended(t))
    }

    fn canon_under(&self, k: u32) -> Type {
        self.canon_at(k + 1, var(0))
    }

    /// `⟦D⟧` itself at depth `k`.
    fn d_at(&self, k: u32) -> Type {
        Type::Sigma {
            fst_level: self.lw.clone(),
            snd_level: self.lw.clone(),
            fst: Rc::new(self.w0_at(k)),
            snd: Rc::new(self.canon_under(k)),
        }
    }

    fn pair(&self, k: u32, t: Rc<Term>, c: Rc<Term>) -> Term {
        Term::Pair {
            fst_level: self.lw.clone(),
            snd_level: self.lw.clone(),
            fst_ty: Rc::new(self.w0_at(k)),
            snd_ty: Rc::new(self.canon_under(k)),
            fst: t,
            snd: c,
        }
    }

    fn fst(&self, k: u32, p: Rc<Term>) -> Term {
        Term::Fst {
            fst_level: self.lw.clone(),
            snd_level: self.lw.clone(),
            fst_ty: Rc::new(self.w0_at(k)),
            snd_ty: Rc::new(self.canon_under(k)),
            pair: p,
        }
    }

    fn snd(&self, k: u32, p: Rc<Term>) -> Term {
        Term::Snd {
            fst_level: self.lw.clone(),
            snd_level: self.lw.clone(),
            fst_ty: Rc::new(self.w0_at(k)),
            snd_ty: Rc::new(self.canon_under(k)),
            pair: p,
        }
    }

    fn sup(&self, k: u32, label: Rc<Term>, children: Rc<Term>) -> Term {
        Term::Sup {
            shape_level: self.ls.clone(),
            pos_level: self.lp.clone(),
            shape_ty: Rc::new(self.shape.shift_local(k)),
            pos_ty: Rc::new(self.pos_under(k)),
            label,
            children,
        }
    }

    /// `P(label)` as a **domain to show**: the case on the label's injection
    /// taken, and the branch's code decoded one step, but nothing unfolded —
    /// so a function field written `k: Resp(c) -> D` reads back as
    /// `Resp(c)` at the label's `c`, not as `Resp`'s body. A whnf would
    /// δ-unfold the domain's own head, which is right for conversion and
    /// wrong for every place a user reads it (a goal's context, an expected
    /// type). `gamma` is the context `label` is scoped in.
    fn pos_shown(&self, gamma: &LocalCtx, k: u32, label: Rc<Term>) -> Type {
        let Type::El { tm, .. } = self.pos_at(k, label) else {
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
        decoded(&Type::El { level: self.lp.clone(), tm }).into_owned()
    }

    /// `Π(y : P label). W₀` — the children's type.
    fn kids_ty(&self, k: u32, label: Rc<Term>) -> Type {
        Type::Pi {
            dom_level: self.lp.clone(),
            cod_level: self.lw.clone(),
            dom: Rc::new(self.pos_at(k, label)),
            cod: Rc::new(self.w0_at(k + 1)),
        }
    }

    /// `f₀ = λ(y : P label). elim_Empty(_. W₀; y)` — a leaf's children (§2.1).
    fn leaf_kids(&self, k: u32, label: Rc<Term>) -> Term {
        Term::Lam {
            dom_level: self.lp.clone(),
            cod_level: self.lw.clone(),
            dom: Rc::new(self.pos_at(k, label)),
            body: Rc::new(Term::ElimEmpty {
                level: self.lw.clone(),
                scrut_level: self.lp.clone(),
                motive: Rc::new(self.w0_at(k + 2)),
                scrut: var(0),
            }),
        }
    }
}

/// Infinitary families' part of the elaborator.
pub(crate) struct Infinitary<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Infinitary<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Infinitary<'_> {
    // -- the type (§3–§5) ---------------------------------------------------

    /// `⟦D<args>⟧` for a tier-2 declaration (§5).
    pub(crate) fn lower_instance_w(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        let n = ind.ctors.len();
        let (shape, ls) = Inductives(self).lower_shape(cx, ind, args, vargs, span)?;
        // §4: each constructor's recursive field, and the function domains'
        // one level `lp`.
        let mut kinds = Vec::with_capacity(n);
        let mut lp: Option<(Level, String)> = None;
        for (i, ctor) in ind.ctors.iter().enumerate() {
            if ctor.kind.contains(&FieldKind::FnChild) {
                let (_, _, dom) = Inductives(self).lower_ctor_with_domain(cx, ind, i, args, vargs, span)?;
                let Some((a, la, j)) = dom else {
                    return err("internal: a function field lowered no domain", span);
                };
                let Some(code) = crate::code::code_of(&a) else {
                    return err(
                        format!(
                            "the domain of `{}`'s recursive function field has no code, so `{}` \
                             cannot index its children by it (docs/inductive-tier2-w-lowering.md §1)",
                            ctor.name, ind.name
                        ),
                        span,
                    );
                };
                match &lp {
                    Some((l, first)) if !l.equiv(&la) => {
                        return err(
                            format!(
                                "the recursive function fields of `{first}` and `{}` have domains \
                                 at different universe levels; tier 2 needs one level for all of \
                                 them (docs/inductive-tier2-w-lowering.md §1)",
                                ctor.name
                            ),
                            span,
                        );
                    }
                    Some(_) => {}
                    None => lp = Some((la, ctor.name.clone())),
                }
                kinds.push(Kind::Fn(Rc::new(code), j));
            } else if ctor.kind.contains(&FieldKind::Plain) {
                kinds.push(Kind::Plain);
            } else {
                kinds.push(Kind::Leaf);
            }
        }
        let Some((lp, _)) = lp else {
            return err("internal: a tier-2 declaration has no function field", span);
        };
        let spine = self.spine(&shape, &ls, n, span)?;

        // P over (Γ, x : S): a constant-motive case tree into `Ty lp`.
        let mut xcx = cx.clone();
        xcx.push("#x".into(), shape.clone(), ls.clone());
        let tag = Rc::new(tag_value(&tag_type(ind.tag)));
        let ptree = self.w_case_tree(
            &xcx,
            &spine,
            spine.root(),
            Type::Ty(lp.clone()),
            &Level::succ(lp.clone()),
            var(0),
            1,
            &mut |bcx, i, d, value| {
                Ok(match &kinds[i] {
                    Kind::Leaf => Term::TmEmpty { level: lp.clone() },
                    Kind::Plain => Term::TmUnit { level: lp.clone() },
                    Kind::Fn(code, j) => {
                        // The domain's binders are the tag and the payload
                        // fields before it; here they are the branch value's
                        // projections (the tag by its canonical inhabitant).
                        let ctor_ty = spine.ctors[i].0.shift_local(d);
                        let mut subst = embed(&cx.gamma, d).extended(Rc::clone(&tag));
                        for m in 0..*j {
                            let (proj, _, _) = self.projection(bcx, &ctor_ty, &value, m, span)?;
                            subst = subst.extended(proj);
                        }
                        code.apply_local(&subst)
                    }
                })
            },
        )?;
        let pos = Type::El {
            level: lp.clone(),
            tm: Rc::new(ptree),
        };
        let lw = Level::join(ls.clone(), lp.clone());
        let mut p = WParts {
            g: cx.gamma.clone(),
            ls: ls.clone(),
            lp: lp.clone(),
            lw: lw.clone(),
            shape: Rc::new(shape.clone()),
            pos: Rc::new(pos),
            // Not read until `canon` exists: nothing below asks for it.
            canon: Rc::new(Type::Nat),
        };
        if crate::code::code_of(&p.w0()).is_none() {
            return err(
                format!(
                    "a field type of `{}` has no code, which the leaf predicate of a type with a \
                     recursive function field needs (docs/inductive-tier2-w-lowering.md §5)",
                    ind.name
                ),
                span,
            );
        }
        // Once the declaration has registered its leaf predicate, every
        // instance at the registered profile names it instead of spelling it
        // (`GenDef::WCanon`): inline it is nearly all of `⟦D⟧`.
        if let Some(canon) = self.w_canon_ref(ind, args, vargs, &lw) {
            p.canon = Rc::new(canon);
            return Ok((p.d_at(0), lw));
        }
        let lf = p.lf();
        let ty_lw = Type::Ty(lw.clone());
        let succ_lw = Level::succ(lw.clone());
        // `Π(y : P v). Ty lw`, the leaf predicate's ih.
        let ih_ty = |k: u32, v: Rc<Term>| Type::Pi {
            dom_level: lp.clone(),
            cod_level: succ_lw.clone(),
            dom: Rc::new(p.pos_at(k, v)),
            cod: Rc::new(ty_lw.clone()),
        };
        let lih = Level::join(lp.clone(), succ_lw.clone());
        let qin = Level::join(lih.clone(), succ_lw.clone());
        let lq = Level::join(lf.clone(), qin.clone());
        // Q(v) = Π(f' : Π(y : P v). W₀). Π(ih' : Π(y : P v). Ty lw). Ty lw
        let q = |k: u32, v: Rc<Term>| Type::Pi {
            dom_level: lf.clone(),
            cod_level: qin.clone(),
            dom: Rc::new(p.kids_ty(k, Rc::clone(&v))),
            cod: Rc::new(Type::Pi {
                dom_level: lih.clone(),
                cod_level: succ_lw.clone(),
                dom: Rc::new(ih_ty(k + 1, Rc::new(v.shift_local(1)))),
                cod: Rc::new(ty_lw.clone()),
            }),
        };
        // CANON over Γ₃ = (Γ, a : S, f, ih).
        let mut c3 = cx.clone();
        c3.push("#a".into(), shape.clone(), ls.clone());
        c3.push("#f".into(), p.kids_ty(1, var(0)), lf.clone());
        c3.push("#ih".into(), ih_ty(2, var(1)), lih.clone());
        let cased = self.w_case_tree(
            &c3,
            &spine,
            spine.root(),
            q(4, var(0)),
            &lq,
            var(2),
            3,
            &mut |_, i, d, value| {
                let inj = Rc::new(inject(&spine, i, n, (*value).clone(), d));
                // In the body: f' = 1, ih' = 0.
                let inj2 = Rc::new(inj.shift_local(2));
                let no_code = || crate::ElabError::Elab {
                    msg: "internal: the positions have no code".into(),
                    span,
                };
                let body = match &kinds[i] {
                    Kind::Leaf => Term::TmId {
                        level: lf.clone(),
                        ty: Rc::new(
                            crate::code::code_of(&p.kids_ty(d + 2, Rc::clone(&inj2)))
                                .ok_or_else(no_code)?,
                        ),
                        lhs: Rc::new(p.leaf_kids(d + 2, Rc::clone(&inj2))),
                        rhs: var(1),
                    },
                    Kind::Plain => Term::AppAt {
                        fun: var(0),
                        arg: Rc::new(Term::Triv { level: lp.clone() }),
                    },
                    Kind::Fn(..) => Term::TmPi {
                        dom_level: lp.clone(),
                        cod_level: lw.clone(),
                        dom: Rc::new(
                            crate::code::code_of(&p.pos_at(d + 2, Rc::clone(&inj2)))
                                .ok_or_else(no_code)?,
                        ),
                        cod: app_at(var(1), var(0)),
                    },
                };
                Ok(Term::Lam {
                    dom_level: lf.clone(),
                    cod_level: qin.clone(),
                    dom: Rc::new(p.kids_ty(d, Rc::clone(&inj))),
                    body: Rc::new(Term::Lam {
                        dom_level: lih.clone(),
                        cod_level: succ_lw.clone(),
                        dom: Rc::new(ih_ty(d + 1, Rc::new(inj.shift_local(1)))),
                        body: Rc::new(body),
                    }),
                })
            },
        )?;
        let at_f = checked_app(
            Rc::new(cased),
            lf.clone(),
            qin.clone(),
            Rc::new(p.kids_ty(3, var(2))),
            Rc::new(Type::Pi {
                dom_level: lih.clone(),
                cod_level: succ_lw.clone(),
                dom: Rc::new(ih_ty(4, var(3))),
                cod: Rc::new(ty_lw.clone()),
            }),
            var(1),
        );
        let step = checked_app(
            Rc::new(at_f),
            lih.clone(),
            succ_lw.clone(),
            Rc::new(ih_ty(3, var(2))),
            Rc::new(ty_lw.clone()),
            var(0),
        );
        // …moved under the `t` the leaf predicate is a type over.
        let step = step.apply_local(&embed(&cx.gamma, 4).extended(var(2)).extended(var(1)).extended(var(0)));
        let canon = Type::El {
            level: lw.clone(),
            tm: Rc::new(Term::ElimW {
                shape_level: ls.clone(),
                pos_level: lp.clone(),
                motive_level: succ_lw.clone(),
                shape: Rc::new(shape.shift_local(1)),
                pos: Rc::new(p.pos_under(1)),
                motive: Rc::new(ty_lw.clone()),
                step: Rc::new(step),
                scrut: var(0),
            }),
        };
        p.canon = Rc::new(canon);
        Ok((p.d_at(0), lw))
    }
}

impl Elaborator {
    // -- the leaf predicate as a generated definition ------------------------

    /// `D#canon := λ(A₁ : Ty 0)…(v_m : T_m). λ(t : W₀). canon t`, at
    /// declaration time ([`GenDef::WCanon`]). The telescope is
    /// [`GenDef::TyCodeFn`]'s, at the same all-`Ty 0` profile, and the body is
    /// the inline predicate [`Self::lower_instance_w`] builds there — inline
    /// because the key is not registered yet. Best-effort like every
    /// generated definition: no registration leaves every instance inline.
    pub(crate) fn register_w_canon(&mut self, ind: &Rc<Inductive>, span: Span) {
        let key = GenDef::WCanon(ind.tag);
        if self.types.gdefs().abs_for(&key).is_some() {
            return;
        }
        let Some((cx, binders, targs, vargs)) = GeneratedDefs(self).tycode_fn_telescope(ind, span) else {
            return;
        };
        let Ok((d_ty, lw)) = Infinitary(self).lower_instance_w(&cx, ind, &targs, &vargs, span) else {
            return;
        };
        let Some(p) = WParts::read(&d_ty, &cx.gamma) else {
            return;
        };
        let Type::El { tm, .. } = &*p.canon else {
            return;
        };
        let succ_lw = Level::succ(lw.clone());
        let w0 = Rc::new(p.w0());
        let mut body = Term::Lam {
            dom_level: lw.clone(),
            cod_level: succ_lw.clone(),
            dom: Rc::clone(&w0),
            body: Rc::clone(tm),
        };
        let mut ty = Type::Pi {
            dom_level: lw.clone(),
            cod_level: succ_lw.clone(),
            dom: w0,
            cod: Rc::new(Type::Ty(lw.clone())),
        };
        let mut ty_level = Level::max(lw, succ_lw);
        // The telescope's domains in the emission spelling, as
        // `register_ty_code_fn`'s: the statement and the λ read one list.
        for (dom, dom_level) in GeneratedDefs(self).emitted_tel(&binders).iter().rev() {
            body = Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: ty_level.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(body),
            };
            ty = Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: ty_level.clone(),
                dom: Rc::new(dom.clone()),
                cod: Rc::new(ty),
            };
            ty_level = Level::max(dom_level.clone(), ty_level);
        }
        let _ = self.push_gen_def(key, &ind.name, ty, ty_level, body, span);
    }
}

impl Infinitary<'_> {
    /// `El (app(D#canon^δ; ⌜A₁⌝, …, v̄, t))` over `(cx, t : W₀)` — the leaf
    /// predicate of the instance `args`/`vargs` as a reference, when the
    /// declaration registered one and the instance is at its profile: every
    /// type argument at `Ty 0`, and the predicate's level the registered one.
    /// `None` keeps the inline spelling.
    fn w_canon_ref(
        &self,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        lw: &Level,
    ) -> Option<Type> {
        let key = GenDef::WCanon(ind.tag);
        let abs = *self.types.gdefs().abs_for(&key)?;
        if args.iter().any(|(_, l)| !l.equiv(&Level::Zero)) {
            return None;
        }
        let GlobalBinding::Tm { ty, .. } = self.psi.bindings.get(abs as usize)? else {
            return None;
        };
        let mut cod = &**ty;
        for _ in 0..args.len() + vargs.len() + 1 {
            let Type::Pi { cod: next, .. } = cod else {
                return None;
            };
            cod = next;
        }
        match cod {
            Type::Ty(l) if l.equiv(lw) => {}
            _ => return None,
        }
        // One binder past `cx`: the tree's.
        let mut tm = Rc::new(self.gen_ref(key)?);
        for (a, _) in args {
            tm = app_at(tm, Rc::new(crate::code::code_of(a)?.shift_local(1)));
        }
        for (v, _, _) in vargs {
            tm = app_at(tm, Rc::new(v.shift_local(1)));
        }
        Some(Type::El {
            level: lw.clone(),
            tm: app_at(tm, var(0)),
        })
    }

    /// Tier 0 §6.1's case tree over the shape, a `Case` per `+` of the
    /// layout and the motive composed with the injection at each depth —
    /// `wf.rs`'s `wf_case_tree` with the branch as a parameter, since tier 2
    /// needs it three times (positions, leaf predicate, `match`).
    ///
    /// `cx` is the context the tree is built in, `d` binders past the one the
    /// spine is scoped in, `motive` is over `(cx, z : S_at)` for the subtree
    /// `at` being split (`spine.root()` from a caller), and `branch` is
    /// called with the branch's context, its constructor, its depth and its
    /// value (scoped there).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn w_case_tree(
        &self,
        cx: &Cx,
        spine: &Spine,
        at: Child,
        motive: Type,
        plvl: &Level,
        scrut: Rc<Term>,
        d: u32,
        branch: &mut dyn FnMut(&Cx, usize, u32, Rc<Term>) -> R<Term>,
    ) -> R<Term> {
        let j = match at {
            Child::Leaf(k) => return branch(cx, k, d, scrut),
            Child::Node(j) => j,
        };
        let node = *spine.layout.node(j);
        let (ctor_ty, ctor_lvl) = spine.lhs(j);
        let (tail_ty, tail_lvl) = spine.rhs(j);
        let mut cases = Vec::with_capacity(2);
        for (right, name, ty, lvl) in [(false, "#scrut", ctor_ty, ctor_lvl), (true, "#rest", tail_ty, tail_lvl)] {
            let mut scx = cx.clone();
            scx.push(name.into(), ty.shift_local(d), lvl.clone());
            cases.push(match node.side(right) {
                Child::Leaf(k) => branch(&scx, k, d + 1, var(0))?,
                inner_at @ Child::Node(_) => {
                    // Two binders past `cx`: the one this side binds and the
                    // inner `Case`'s own motive binder (`wf_case_tree`'s note).
                    let (lhs_level, rhs_level) = (ctor_lvl.clone(), tail_lvl.clone());
                    let (lhs, rhs) = (Rc::new(ctor_ty.shift_local(d + 2)), Rc::new(tail_ty.shift_local(d + 2)));
                    let inj = if right {
                        Term::Inr { lhs_level, rhs_level, lhs, rhs, val: var(0) }
                    } else {
                        Term::Inl { lhs_level, rhs_level, lhs, rhs, val: var(0) }
                    };
                    let inner = motive.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(inj)));
                    self.w_case_tree(&scx, spine, inner_at, inner, plvl, var(0), d + 1, branch)?
                }
            });
        }
        let case_r = cases.pop().expect("two sides");
        let case_l = cases.pop().expect("two sides");
        Ok(Term::Case {
            lhs_level: ctor_lvl.clone(),
            rhs_level: tail_lvl.clone(),
            motive_level: plvl.clone(),
            lhs: Rc::new(ctor_ty.shift_local(d)),
            rhs: Rc::new(tail_ty.shift_local(d)),
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    // -- no-confusion (§9) ---------------------------------------------------

    /// `elim_W` at a **constant** motive over `fst y`, its step tier 0's
    /// constant-motive case tree on the label: `wf.rs`'s `const_elim_wf` on
    /// the `W`. Neither half of no-confusion reads the children, so the step
    /// ignores `f` and `ih` and needs no generalization.
    ///
    /// `d_ty` and `spine` are scoped in the base context, two binders below
    /// `mcx` (a `J` motive's `y` and `p`); `motive` and `scrut` in `mcx`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn const_elim_w(
        &self,
        mcx: &Cx,
        d_ty: &Type,
        spine: &Spine,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &crate::inductive::ConstBody,
        span: Span,
    ) -> R<Term> {
        let g = mcx.gamma.prefix(mcx.gamma.len() - 2);
        let Some(p) = WParts::read(d_ty, &g) else {
            return err("internal: a tier-2 declaration did not lower to its `W` encoding", span);
        };
        let mut c3 = mcx.clone();
        c3.push("#a".into(), p.shape.shift_local(2), p.ls.clone());
        c3.push("#f".into(), p.kids_ty(3, var(0)), p.lf());
        c3.push(
            "#ih".into(),
            Type::Pi {
                dom_level: p.lp.clone(),
                cod_level: mlvl.clone(),
                dom: Rc::new(p.pos_at(4, var(1))),
                cod: Rc::new(motive.shift_local(3)),
            },
            Level::join(p.lp.clone(), mlvl.clone()),
        );
        let step = self.const_case_tree(
            &c3,
            spine,
            &motive.shift_local(3),
            mlvl,
            var(2),
            body,
            spine.root(),
            5,
            span,
        )?;
        Ok(Term::ElimW {
            shape_level: p.ls.clone(),
            pos_level: p.lp.clone(),
            motive_level: mlvl.clone(),
            shape: Rc::new(p.shape.shift_local(2)),
            pos: Rc::new(p.pos_under(2)),
            motive: Rc::new(motive.shift_local(1)),
            step: Rc::new(step),
            scrut: Rc::new(p.fst(2, scrut)),
        })
    }

    // -- constructors (§6) --------------------------------------------------

    /// `⟦Cᵢ(ā)⟧ = ⟨sup(ℓᵢ; fᵢ), qᵢ⟩` at the expected `⟦D⟧`.
    pub(crate) fn build_ctor_w(
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
        let Some(p) = WParts::read(&ty, &cx.gamma) else {
            return err("internal: a tier-2 declaration did not lower to its `W` encoding", span);
        };
        let n = ind.ctors.len();
        let spine = self.spine(&ty, &p.lw, n, span)?;
        let payload: Vec<&Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(a, _)| *a)
            .collect();
        let fields = self.build_fields(cx, &spine.ctors[i].0, &payload, true, span)?;
        let label = Rc::new(inject(&spine, i, n, fields, 0));
        let child = ctor.kind.iter().position(|k| k.is_child());
        // A child is bound once, `(λc. ⟨sup(ℓ; …c…), …c…⟩) child`, and the
        // tree and the proof both read the bound `c`: written into each
        // directly, the child was evaluated once for the tree and again for
        // the proof, and a `bind` nested to the left paid that at every
        // level (issues/tier2-left-nested-bind-cost.md). A function child's
        // two halves apply `c` to the same `y`, which the evaluator shares
        // (`Eval::eval_projected` in the kernel).
        let lab1 = || Rc::new(label.shift_local(1));
        let (child_ty, child_level, child_tm, kids, proof) = match child {
            None => {
                let kids = p.leaf_kids(0, Rc::clone(&label));
                let proof = Term::Refl {
                    level: p.lf(),
                    ty: Rc::new(p.kids_ty(0, Rc::clone(&label))),
                    tm: Rc::new(kids.clone()),
                };
                return Ok(p.pair(0, Rc::new(p.sup(0, label, Rc::new(kids))), Rc::new(proof)));
            }
            Some(k) if ctor.kind[k] == FieldKind::Plain => {
                let t = Rc::new(self.elab_check(cx, args[k], &ty, &p.lw)?);
                let kids = Term::Lam {
                    dom_level: p.lp.clone(),
                    cod_level: p.lw.clone(),
                    dom: Rc::new(p.pos_at(1, lab1())),
                    body: Rc::new(p.fst(2, var(1))),
                };
                (ty.clone(), p.lw.clone(), t, kids, p.snd(1, var(0)))
            }
            Some(k) => {
                // `k` is checked at `Π(y : A[ā]). ⟦D⟧`, `A[ā]` read off the
                // positions at the label (§6).
                let dom = p.pos_shown(&cx.gamma, 0, Rc::clone(&label));
                let k_ty = Type::Pi {
                    dom_level: p.lp.clone(),
                    cod_level: p.lw.clone(),
                    dom: Rc::new(dom.clone()),
                    cod: Rc::new(ty.shift_local(1)),
                };
                let kt = Rc::new(self.elab_check(cx, args[k], &k_ty, &p.lf())?);
                let at_y = Rc::new(checked_app(
                    var(1),
                    p.lp.clone(),
                    p.lw.clone(),
                    Rc::new(dom.shift_local(2)),
                    Rc::new(ty.shift_local(3)),
                    var(0),
                ));
                let lam = |body: Term| Term::Lam {
                    dom_level: p.lp.clone(),
                    cod_level: p.lw.clone(),
                    dom: Rc::new(p.pos_at(1, lab1())),
                    body: Rc::new(body),
                };
                (k_ty, p.lf(), kt, lam(p.fst(2, Rc::clone(&at_y))), lam(p.snd(2, at_y)))
            }
        };
        let body = p.pair(1, Rc::new(p.sup(1, lab1(), Rc::new(kids))), Rc::new(proof));
        let child_ty = Rc::new(child_ty);
        Ok(Term::App {
            fun: Rc::new(Term::Lam {
                dom_level: child_level.clone(),
                cod_level: p.lw.clone(),
                dom: Rc::clone(&child_ty),
                body: Rc::new(body),
            }),
            dom_level: child_level,
            cod_level: p.lw.clone(),
            dom: child_ty,
            cod: Rc::new(ty.shift_local(1)),
            arg: child_tm,
        })
    }

    // -- match (§7, §8) -----------------------------------------------------

    /// `match s ≡ elim_W(x:S. P; w. M'; a f ih. STEP; fst s) (snd s)`, with
    /// `M'(w) = Π(c : El(canon w)). M[⟨w, c⟩]`.
    ///
    /// `arms` are in declaration order, checked by the tier-0 entry point;
    /// `motive` is over `(cx.gamma, z : ⟦D⟧)`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_w(
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
        let dec = crate::recursion::guard_param(cx, &scrut, arms);
        let Some(p) = WParts::read(scrut_ty, &cx.gamma) else {
            return err("internal: a tier-2 declaration did not lower to its `W` encoding", span);
        };
        let n = ind.ctors.len();
        let spine = self.spine(scrut_ty, &p.lw, n, span)?;
        let g = &cx.gamma;
        let lf = p.lf();
        let lmp = Level::join(p.lw.clone(), mlvl.clone());
        // `M[⟨t, c⟩]` at depth `k`.
        let m_at = |k: u32, t: Rc<Term>, c: Rc<Term>| {
            motive.apply_local(&embed(g, k).extended(Rc::new(p.pair(k, t, c))))
        };
        // M' over (Γ, w).
        let m_prime = Type::Pi {
            dom_level: p.lw.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(p.canon_under(0)),
            cod: Rc::new(m_at(2, var(1), var(0))),
        };
        let mp_at = |k: u32, w: Rc<Term>| m_prime.apply_local(&embed(g, k).extended(w));
        // `Π(y : P v). M'(f y)`, the step's ih, with `f` scoped at `k`.
        let ihm_ty = |k: u32, v: Rc<Term>, f: Rc<Term>| Type::Pi {
            dom_level: p.lp.clone(),
            cod_level: lmp.clone(),
            dom: Rc::new(p.pos_at(k, v)),
            cod: Rc::new(mp_at(k + 1, app_at(Rc::new(f.shift_local(1)), var(0)))),
        };
        let msup = |k: u32, v: Rc<Term>, f: Rc<Term>| mp_at(k, Rc::new(p.sup(k, v, f)));
        let lihm = Level::join(p.lp.clone(), lmp.clone());
        let qmin = Level::join(lihm.clone(), lmp.clone());
        let lqm = Level::join(lf.clone(), qmin.clone());
        // Q_M(v) = Π(f'). Π(ih' : Π(y : P v). M'(f' y)). M'(sup(v; f'))
        let q_m = |k: u32, v: Rc<Term>| Type::Pi {
            dom_level: lf.clone(),
            cod_level: qmin.clone(),
            dom: Rc::new(p.kids_ty(k, Rc::clone(&v))),
            cod: Rc::new(Type::Pi {
                dom_level: lihm.clone(),
                cod_level: lmp.clone(),
                dom: Rc::new(ihm_ty(k + 1, Rc::new(v.shift_local(1)), var(0))),
                cod: Rc::new(msup(k + 2, Rc::new(v.shift_local(2)), var(1))),
            }),
        };
        let mut c3 = cx.clone();
        c3.push("#a".into(), (*p.shape).clone(), p.ls.clone());
        c3.push("#f".into(), p.kids_ty(1, var(0)), lf.clone());
        c3.push("#ih".into(), ihm_ty(2, var(1), var(0)), lihm.clone());
        let cased = self.w_case_tree(
            &c3,
            &spine,
            spine.root(),
            q_m(4, var(0)),
            &lqm,
            var(2),
            3,
            &mut |bcx, i, d, value| {
                let ctor = &ind.ctors[i];
                let arm = arms[i];
                let inj = Rc::new(inject(&spine, i, n, (*value).clone(), d));
                let sh = |t: &Rc<Term>, by: u32| Rc::new(t.shift_local(by));
                let mut acx = bcx.clone();
                acx.push("#f".into(), p.kids_ty(d, Rc::clone(&inj)), lf.clone());
                acx.push("#ih".into(), ihm_ty(d + 1, sh(&inj, 1), var(0)), lihm.clone());
                acx.push(
                    "#c".into(),
                    p.canon_at(d + 2, Rc::new(p.sup(d + 2, sh(&inj, 2), var(1)))),
                    p.lw.clone(),
                );
                // In the arm: f' = 2, ih' = 1, c = 0.
                let db = d + 3;
                let inj3 = sh(&inj, 3);
                let value_here = sh(&value, 3);
                let ctor_ty = spine.ctors[i].0.shift_local(db);
                let mut children = Vec::new();
                let mut fn_children = Vec::new();
                let mut payload_k = 0usize;
                for (k, name) in arm.binders.iter().map(|b| b.name().to_string()).enumerate() {
                    let (term, ty, level) = match ctor.kind[k] {
                        FieldKind::Plain => {
                            // t := ⟨f' ⟨⟩, c⟩, its ih `ih' ⟨⟩ c` (§7, §8).
                            let unit = Rc::new(Term::Triv { level: p.lp.clone() });
                            let t = Rc::new(p.pair(db, app_at(var(2), Rc::clone(&unit)), var(0)));
                            let ih = app_at(app_at(var(1), unit), var(0));
                            let ih_ty = motive.apply_local(&embed(g, db).extended(Rc::clone(&t)));
                            children.push((Rc::clone(&t), ih, ih_ty, mlvl.clone()));
                            (t, p.d_at(db), p.lw.clone())
                        }
                        FieldKind::FnChild => {
                            // k := λy. ⟨f' y, c y⟩, its ih `λy. ih' y (c y)`.
                            let dom = Rc::new(p.pos_shown(&acx.gamma, db, Rc::clone(&inj3)));
                            let k_term = Rc::new(Term::Lam {
                                dom_level: p.lp.clone(),
                                cod_level: p.lw.clone(),
                                dom: Rc::clone(&dom),
                                body: Rc::new(p.pair(db + 1, app_at(var(3), var(0)), app_at(var(1), var(0)))),
                            });
                            let ih = Rc::new(Term::Lam {
                                dom_level: p.lp.clone(),
                                cod_level: mlvl.clone(),
                                dom: Rc::clone(&dom),
                                body: app_at(app_at(var(2), var(0)), app_at(var(1), var(0))),
                            });
                            let at_y = Term::App {
                                fun: sh(&k_term, 1),
                                dom_level: p.lp.clone(),
                                cod_level: p.lw.clone(),
                                dom: sh_ty(&dom, 1),
                                cod: Rc::new(p.d_at(db + 2)),
                                arg: var(0),
                            };
                            let ih_ty = Type::Pi {
                                dom_level: p.lp.clone(),
                                cod_level: mlvl.clone(),
                                dom: Rc::clone(&dom),
                                cod: Rc::new(motive.apply_local(&embed(g, db + 1).extended(Rc::new(at_y)))),
                            };
                            fn_children.push(FnChildIh { fun: Rc::clone(&k_term), ih, ih_ty, rebind: None });
                            let ty = Type::Pi {
                                dom_level: p.lp.clone(),
                                cod_level: p.lw.clone(),
                                dom,
                                cod: Rc::new(p.d_at(db + 1)),
                            };
                            (k_term, ty, lf.clone())
                        }
                        _ => {
                            let r = self.projection(&acx, &ctor_ty, &value_here, payload_k, span)?;
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
                acx.guard = dec
                    .map(|dec| {
                        Rc::new(Guard {
                            dec,
                            kind: GuardKind::Wf {
                                depth: acx.names.len(),
                                children,
                                container: None,
                                fn_children,
                                cov: None,
                                shape: crate::recursion::WfShape::NoWindowRoute,
                            },
                            rebind: None,
                            generalized: crate::generalize::guard_gen(cx, dec, Some(span)),
                        })
                    })
                    .or_else(|| cx.guard.clone());
                let leaf = !ctor.kind.iter().any(|k| k.is_child());
                let body = if leaf {
                    // The arm is typed at the constructor form, `f₀` and its
                    // `refl`, and `J` carries it to the abstract `f'` (§2.4).
                    let f0 = Rc::new(p.leaf_kids(db, Rc::clone(&inj3)));
                    let kids_ty = Rc::new(p.kids_ty(db, Rc::clone(&inj3)));
                    let refl = Rc::new(Term::Refl {
                        level: lf.clone(),
                        ty: Rc::clone(&kids_ty),
                        tm: Rc::clone(&f0),
                    });
                    let at_f0 = m_at(db, Rc::new(p.sup(db, Rc::clone(&inj3), Rc::clone(&f0))), refl);
                    let arm_term = self.elab_check(&acx, &arm.body, &at_f0, &mlvl)?;
                    Term::J {
                        ty_level: lf.clone(),
                        motive_level: mlvl.clone(),
                        ty: kids_ty,
                        lhs: f0,
                        motive: Rc::new(m_at(
                            db + 2,
                            Rc::new(p.sup(db + 2, sh(&inj, 5), var(1))),
                            var(0),
                        )),
                        case: Rc::new(arm_term),
                        rhs: var(2),
                        proof: var(0),
                    }
                } else {
                    let at = m_at(db, Rc::new(p.sup(db, Rc::clone(&inj3), var(2))), var(0));
                    self.elab_check(&acx, &arm.body, &at, &mlvl)?
                };
                Ok(Term::Lam {
                    dom_level: lf.clone(),
                    cod_level: qmin.clone(),
                    dom: Rc::new(p.kids_ty(d, Rc::clone(&inj))),
                    body: Rc::new(Term::Lam {
                        dom_level: lihm.clone(),
                        cod_level: lmp.clone(),
                        dom: Rc::new(ihm_ty(d + 1, sh(&inj, 1), var(0))),
                        body: Rc::new(Term::Lam {
                            dom_level: p.lw.clone(),
                            cod_level: mlvl.clone(),
                            dom: Rc::new(p.canon_at(d + 2, Rc::new(p.sup(d + 2, sh(&inj, 2), var(1))))),
                            body: Rc::new(body),
                        }),
                    }),
                })
            },
        )?;
        // STEP = (case a of Q_M) f ih, over Γ₃: a = 2, f = 1, ih = 0.
        let at_f = checked_app(
            Rc::new(cased),
            lf.clone(),
            qmin.clone(),
            Rc::new(p.kids_ty(3, var(2))),
            Rc::new(Type::Pi {
                dom_level: lihm.clone(),
                cod_level: lmp.clone(),
                dom: Rc::new(ihm_ty(4, var(3), var(0))),
                cod: Rc::new(msup(5, var(4), var(1))),
            }),
            var(1),
        );
        let step = checked_app(
            Rc::new(at_f),
            lihm.clone(),
            lmp.clone(),
            Rc::new(ihm_ty(3, var(2), var(1))),
            Rc::new(msup(4, var(3), var(2))),
            var(0),
        );
        let scrut = Rc::new(scrut);
        let elim = Term::ElimW {
            shape_level: p.ls.clone(),
            pos_level: p.lp.clone(),
            motive_level: lmp.clone(),
            shape: Rc::clone(&p.shape),
            pos: Rc::clone(&p.pos),
            motive: Rc::new(m_prime.clone()),
            step: Rc::new(step),
            scrut: Rc::new(p.fst(0, Rc::clone(&scrut))),
        };
        Ok(Term::AppAt {
            fun: Rc::new(elim),
            arg: Rc::new(p.snd(0, scrut)),
        })
    }
}

fn sh_ty(t: &Rc<Type>, by: u32) -> Rc<Type> {
    Rc::new(t.shift_local(by))
}

#[cfg(test)]
mod canon {
    //! `D#canon`, the named leaf predicate ([`GenDef::WCanon`]). Emission is
    //! checked by elaborating real source (`crates/elab/tests/inductive_tier2.rs`
    //! runs every tier-2 acceptance test through it); what is checked here is
    //! the boundary: which declarations register one, which instances name it,
    //! and which keep the inline spelling.

    use super::*;

    const SPAN: Span = Span { start: 0, end: 0 };

    const SRC: &str = "
inductive Tree { Ret(n: Nat), Tau(t: Tree), Vis(c: Nat, k: Nat -> Tree), Cut }
inductive ITree<R>(m: Nat) { IRet(r: R), IVis(c: Nat, k: Nat -> ITree<R>(m)) }
inductive List1 { Nil1, Cons1(x: Nat, r: List1) }
";

    struct Env {
        el: Elaborator,
        cx: Cx,
    }

    fn env() -> Env {
        let mut el = Elaborator::with_prelude().expect("prelude");
        el.elab_source(SRC).expect("the declarations elaborate");
        Env { el, cx: Cx::empty() }
    }

    impl Env {
        fn ind(&self, name: &str) -> Rc<Inductive> {
            Rc::clone(
                self.el
                    .types
                    .inductive(&crate::names::qkey("main", name))
                    .unwrap_or_else(|| panic!("`{name}` was declared")),
            )
        }

        /// The leaf predicate of an instance, over `(cx, t)`.
        fn canon(&self, name: &str, args: &[(Type, Level)], vargs: &[(Term, Type, Level)]) -> Type {
            let (ty, _) = self
                .el
                .lower_instance(&self.cx, &self.ind(name), args, vargs, SPAN)
                .expect("the instance lowers");
            let p = WParts::read(&ty, &self.cx.gamma).expect("a tier-2 lowering");
            (*p.canon).clone()
        }
    }

    fn nat() -> (Type, Level) {
        (Type::Nat, Level::Zero)
    }

    fn two() -> (Term, Type, Level) {
        (Term::NatLit(2u64.into()), Type::Nat, Level::Zero)
    }

    #[test]
    fn a_tier2_declaration_registers_its_leaf_predicate_and_tier1_does_not() {
        let e = env();
        for name in ["Tree", "ITree"] {
            assert!(
                e.el.gen_ref(GenDef::WCanon(e.ind(name).tag)).is_some(),
                "`{name}` registers `{name}#canon`"
            );
        }
        assert!(e.el.gen_ref(GenDef::WCanon(e.ind("List1").tag)).is_none());
    }

    /// The reference is `D#canon` itself — the Ψ index, not a shape — applied
    /// to the instance's codes, its value arguments and the tree, in that
    /// order.
    #[test]
    fn an_instance_names_its_own_declarations_predicate() {
        let e = env();
        let tree = e.ind("Tree");
        let itree = e.ind("ITree");
        for (ind, args, vargs, other) in [
            (&tree, vec![], vec![], &itree),
            (&itree, vec![nat()], vec![two()], &tree),
        ] {
            let canon = e.canon(&ind.name, &args, &vargs);
            let Type::El { tm, .. } = &canon else {
                panic!("the predicate is a decoded code")
            };
            let (head, spine) = crate::spelling::app_spine(tm);
            assert!(GeneratedDefs(&e.el).is_gen_ref(head, GenDef::WCanon(ind.tag)), "`{}`'s own", ind.name);
            assert!(!GeneratedDefs(&e.el).is_gen_ref(head, GenDef::WCanon(other.tag)), "not `{}`'s", other.name);
            let mut want: Vec<Term> = args
                .iter()
                .map(|(a, _)| crate::code::code_of(a).unwrap().shift_local(1))
                .collect();
            want.extend(vargs.iter().map(|(v, _, _)| v.shift_local(1)));
            want.push(Term::Var(LocalVar(0)));
            let got: Vec<Term> = spine.iter().map(|a| (***a).clone()).collect();
            assert_eq!(got, want);
        }
    }

    /// The definition is registered at the all-`Ty 0` profile, so an instance
    /// at a type argument of another level cannot be an application of it,
    /// and keeps the predicate it always had.
    #[test]
    fn another_level_profile_keeps_the_inline_predicate() {
        let e = env();
        let ty0 = (Type::Ty(Level::Zero), Level::succ(Level::Zero));
        let Type::El { tm, .. } = e.canon("ITree", &[ty0], &[two()]) else {
            panic!("the predicate is a decoded code")
        };
        assert!(matches!(&*tm, Term::ElimW { .. }), "inline");
    }
}
