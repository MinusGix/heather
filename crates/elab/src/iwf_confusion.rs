//! No-confusion on the `IWf` route's families: `absurd` between two
//! constructors and `inj` at a payload field, on both of the route's forms —
//! the kernel's `IWf` (`docs/kernel/iwf-former-design.md`) and its `W` encoding for
//! families with a function field (`docs/kernel/iwf-infinitary-design.md` §13).
//!
//! The scheme is `docs/inductives/inductive-tier0-lowering.md` §6's, unchanged: a total
//! function of the family with a **constant** motive — the constructor's tag
//! code for `absurd`, a payload projection with the left side's own field as
//! the default for `inj` — transported along the equation by `J`. The only
//! new part is how such a function reaches the label: through `elim_IWf` on
//! the kernel form, through `elim_W` on the tree (`fst`) of the `W` form.
//! Both eliminate at any index and β on a constructor at any index, so the
//! `J`'s case computes at `y := lhs` exactly as tier 0's does.

use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type, iwf_step_telescope};
use heather_syntax::ast::Span;

use crate::inductive::{ConstBody, Inductive, Spine};
use crate::iwf_family::{FamForm, IwfFam};
use crate::{Cx, Elaborator, R, err};

/// An equation as `absurd`/`inj` read it: proof, carrier, level, endpoints.
type Equation = (Term, Type, Level, Rc<Term>, Rc<Term>);

fn var(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

/// Component `c` of a literal right-nested tuple, as written.
fn tuple_component(t: &Rc<Term>, c: usize) -> Option<Rc<Term>> {
    let mut cur = t;
    for _ in 0..c {
        cur = crate::spelling::pair_of(cur)?.1;
    }
    crate::spelling::pair_of(cur).map(|(fst, _)| Rc::clone(fst))
}

/// No-confusion for indexed families: its part of the elaborator.
pub(crate) struct IwfConfusion<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for IwfConfusion<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl IwfConfusion<'_> {
    /// A constant-motive function of a family value, inside a `J` motive:
    /// `mcx` is the ambient context plus the motive's two binders, `fam`,
    /// `spine` and `body`'s payloads are scoped in the ambient context, and
    /// `motive` and `scrut` in `mcx` ([`Inductives::const_predicate`](crate::inductive::Inductives::const_predicate)'s contract).
    #[allow(clippy::too_many_arguments)]
    fn fam_const(
        &self,
        mcx: &Cx,
        fam: &IwfFam,
        spine: &Spine,
        motive: &Type,
        mlvl: &Level,
        scrut: Term,
        body: &ConstBody,
        span: Span,
    ) -> R<Term> {
        let m = fam.idx.shift_local(2);
        match &fam.form {
            FamForm::IWf(sig) => {
                let sig = sig.shift_local(2);
                // The motive binds `j` and `z`, which it ignores.
                let mot = motive.shift_local(2);
                let (cs_ty, ih_ty, _) = iwf_step_telescope(&sig, mlvl, &mot);
                let mut c3 = mcx.clone();
                c3.push("#a".into(), (*sig.shape).clone(), sig.level.clone());
                c3.push("#cs".into(), cs_ty, sig.family_level());
                c3.push("#ih".into(), ih_ty, mlvl.clone());
                let step = self.const_case_tree(&c3, spine, &motive.shift_local(3), mlvl, Rc::new(var(2)), body, spine.root(), 5, span)?;
                Ok(Term::ElimIWf {
                    sig,
                    motive_level: mlvl.clone(),
                    motive: Rc::new(mot),
                    step: Rc::new(step),
                    index: Rc::new(m),
                    scrut: Rc::new(scrut),
                })
            }
            FamForm::W(sig) => {
                let mut c3 = mcx.clone();
                c3.push("#a".into(), sig.shape.shift_local(2), sig.ls.clone());
                c3.push("#f".into(), sig.kids_ty(3, &var(0)), Level::join(sig.lp.clone(), sig.lw.clone()));
                c3.push(
                    "#ih".into(),
                    Type::Pi {
                        dom_level: sig.lp.clone(),
                        cod_level: mlvl.clone(),
                        dom: Rc::new(sig.pos_at(4, &var(1))),
                        cod: Rc::new(motive.shift_local(3)),
                    },
                    Level::join(sig.lp.clone(), mlvl.clone()),
                );
                let step = self.const_case_tree(&c3, spine, &motive.shift_local(3), mlvl, Rc::new(var(2)), body, spine.root(), 5, span)?;
                Ok(Term::ElimW {
                    shape_level: sig.ls.clone(),
                    pos_level: sig.lp.clone(),
                    motive_level: mlvl.clone(),
                    shape: Rc::new(sig.shape.shift_local(2)),
                    pos: Rc::new(sig.pos.shift_local_above(2, 1)),
                    motive: Rc::new(motive.shift_local(1)),
                    step: Rc::new(step),
                    scrut: Rc::new(sig.fst(2, &m, scrut)),
                })
            }
        }
    }

    /// A family value read back as a constructor: its index and its shape
    /// branch's value (the payload tuple, or the neutral a `match` arm's
    /// motive is instantiated at, which the injection path still names).
    /// `t` is in whnf.
    fn fam_ctor(&self, ind: &Inductive, fam: &IwfFam, t: &Term) -> Option<(usize, Rc<Term>)> {
        let label = match (&fam.form, t) {
            (FamForm::IWf(_), Term::Supi { label, .. }) => label,
            (FamForm::W(_), _) => match crate::spelling::pair_of(t) {
                Some((fst, _)) => match &**fst {
                    Term::Sup { label, .. } => label,
                    _ => return None,
                },
                None => return None,
            },
            _ => return None,
        };
        let n = ind.ctors.len();
        let path = crate::spelling::inj_path(label, n);
        // A bare neutral at a multi-constructor family names no summand.
        if !path.injected && n > 1 && !crate::spelling::is_pair(path.at) {
            return None;
        }
        Some((path.ctor, Rc::clone(path.val.unwrap_or(label))))
    }

    /// Both sides of a family equation read as constructors.
    fn fam_sides(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &IwfFam,
        lhs: &Term,
        rhs: &Term,
        who: &str,
        span: Span,
    ) -> R<((usize, Rc<Term>), (usize, Rc<Term>))> {
        let l = self.whnf_tm(cx, &Rc::new(lhs.clone()), span)?;
        let r = self.whnf_tm(cx, &Rc::new(rhs.clone()), span)?;
        match (self.fam_ctor(ind, fam, &l), self.fam_ctor(ind, fam, &r)) {
            (Some(l), Some(r)) => Ok((l, r)),
            _ => err(
                format!("`{who}` needs both sides of the equation to be constructor applications"),
                span,
            ),
        }
    }

    /// `J`'s motive context over the family: `y : D(m)` and `p : lhs = y`.
    fn fam_motive_cx(cx: &Cx, sty: &Type, slvl: &Level, lhs: &Rc<Term>) -> Cx {
        let mut mcx = cx.clone();
        mcx.push("#y".into(), sty.clone(), slvl.clone());
        mcx.push(
            "#p".into(),
            Type::Id {
                level: slvl.clone(),
                ty: Rc::new(sty.shift_local(1)),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(var(0)),
            },
            slvl.clone(),
        );
        mcx
    }

    /// `absurd` at a family: tier 0's disjointness, the tag predicate built
    /// by [`Self::fam_const`].
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn fam_absurd(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &IwfFam,
        equation: Equation,
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let (proof, sty, slvl, lhs, rhs) = equation;
        let ((i, _), (j, _)) = self.fam_sides(cx, ind, fam, &lhs, &rhs, "absurd", span)?;
        if i == j {
            return err(
                format!(
                    "both sides of this equation are `{}`, so it is not absurd \
                     (use `inj` to get the field equations)",
                    ind.ctors[i].name
                ),
                span,
            );
        }
        let (shape, shape_lvl) = fam.shape();
        let spine = self.spine(shape, shape_lvl, ind.ctors.len(), span)?;
        let mcx = Self::fam_motive_cx(cx, &sty, &slvl, &lhs);
        let pred = self.fam_const(
            &mcx,
            fam,
            &spine,
            &Type::Ty(Level::Zero),
            &Level::succ(Level::Zero),
            var(1),
            &ConstBody::TagCode(i),
            span,
        )?;
        let absurd = Term::J {
            ty_level: slvl,
            motive_level: Level::Zero,
            ty: Rc::new(sty),
            lhs,
            motive: Rc::new(Type::El { level: Level::Zero, tm: Rc::new(pred) }),
            // `El⁰ (tag_i lhs) ⇝ Unit`, definitionally, at any index.
            case: Rc::new(Term::Triv { level: Level::Zero }),
            rhs,
            proof: Rc::new(proof),
        };
        // …and `El⁰ (tag_i rhs) ⇝ Empty^0`.
        Ok(Term::ElimEmpty {
            level: expected_lvl.clone(),
            scrut_level: Level::Zero,
            motive: Rc::new(expected.shift_local(1)),
            scrut: Rc::new(absurd),
        })
    }

    /// `inj` at field `k` of a family constructor: tier 0's injectivity at a
    /// payload field, the projection built by [`Self::fam_const`]. A
    /// recursive field is refused: its value is a child of the tree, not a
    /// component of the label (and on the `W` form a function child's
    /// injectivity would need funext, tier 2 §9).
    pub(crate) fn fam_inj(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &IwfFam,
        k: usize,
        equation: Equation,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (proof, sty, slvl, lhs, rhs) = equation;
        let ((i, lval), (j, rval)) = self.fam_sides(cx, ind, fam, &lhs, &rhs, "inj", span)?;
        if i != j {
            return err(
                format!(
                    "this equation is between `{}` and `{}`, which are different constructors \
                     (use `absurd`)",
                    ind.ctors[i].name, ind.ctors[j].name
                ),
                span,
            );
        }
        let ctor = &ind.ctors[i];
        if k >= ctor.fields.len() {
            return err(
                format!("`{}` has {} field(s), so there is no field {k}", ctor.name, ctor.fields.len()),
                span,
            );
        }
        if ctor.kind[k].is_child() {
            return err(
                format!(
                    "`inj` at the recursive field of `{}` is not supported: `{}` is an indexed \
                     family, whose children are its tree's subtrees rather than fields of the \
                     constructor's label (docs/kernel/iwf-infinitary-design.md §13)",
                    ctor.name, ind.name
                ),
                span,
            );
        }
        let p = ctor.kind[..k].iter().filter(|f| !f.is_child()).count();
        let (shape, shape_lvl) = fam.shape();
        let spine = self.spine(shape, shape_lvl, ind.ctors.len(), span)?;
        // Each side's field, reduced: a literal side's projection is the
        // written field itself, which is what the result type should spell.
        let (a_k, lty, llvl) = self.projection(cx, &spine.ctors[i].0, &lval, p, span)?;
        let (b_k, rty, _) = self.projection(cx, &spine.ctors[i].0, &rval, p, span)?;
        let field = |value: &Rc<Term>, proj: Rc<Term>| -> R<Rc<Term>> {
            match tuple_component(value, p + 1) {
                Some(f) => Ok(f),
                None => self.whnf_tm(cx, &proj, span),
            }
        };
        let (a_k, b_k) = (field(&lval, a_k)?, field(&rval, b_k)?);
        if self
            .committed_oracle()
            .convert_type(&cx.gamma, Layer::Prog, &lty, &rty, &llvl)
            .is_err()
        {
            return err(
                format!(
                    "field {k} of `{}` has a type that depends on an earlier field, so its \
                     injectivity is not derivable this way yet \
                     (docs/inductives/inductive-tier0-lowering.md §6.2)",
                    ctor.name
                ),
                span,
            );
        }
        let mcx = Self::fam_motive_cx(cx, &sty, &slvl, &lhs);
        let proj = self.fam_const(
            &mcx,
            fam,
            &spine,
            &lty.shift_local(2),
            &llvl,
            var(1),
            &ConstBody::Field { i, k: p, default: Rc::clone(&a_k) },
            span,
        )?;
        let term = Term::J {
            ty_level: slvl,
            motive_level: llvl.clone(),
            ty: Rc::new(sty),
            lhs,
            motive: Rc::new(Type::Id {
                level: llvl.clone(),
                ty: Rc::new(lty.shift_local(2)),
                lhs: Rc::new(a_k.shift_local(2)),
                rhs: Rc::new(proj),
            }),
            case: Rc::new(Term::Refl { level: llvl.clone(), ty: Rc::new(lty.clone()), tm: Rc::clone(&a_k) }),
            rhs,
            proof: Rc::new(proof),
        };
        let result = Type::Id { level: llvl.clone(), ty: Rc::new(lty), lhs: a_k, rhs: b_k };
        Ok((term, result, llvl))
    }
}
