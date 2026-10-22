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
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, MSig, Term, Type};
use heather_syntax::{Arm, Expr, ExprKind, Span};

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

/// The index of every unindexed `M`: `⟨⟩ : Unit⁰`.
fn triv() -> Rc<Term> {
    Rc::new(Term::Triv { level: Level::Zero })
}

/// One child of a constructor, as its positions see it (§2).
enum Kid {
    /// `t: D` — one position, `Unit`.
    Plain,
    /// `k: A -> D` — the domain's code, scoped over `(Γ, #tag, p₀, …,
    /// p_{j-1})`, and that `j`.
    Fn(Rc<Term>, usize),
}

/// The components of `⟦D⟧ = M(Unit; _. S; _ s. P; _ _ _. ⟨⟩)(⟨⟩)`, scoped in
/// `g`, with the index binder already instantiated away.
pub(crate) struct MParts {
    g: LocalCtx,
    sig: Rc<MSig>,
    pub ls: Level,
    pub lp: Level,
    /// The family's level, `ls ⊔ lp ⊔ 0` — the kernel's `family_level`.
    pub lw: Level,
    pub shape: Rc<Type>,
    /// `P`, over `(g, s : S)`.
    pos: Rc<Type>,
}

impl MParts {
    /// Read a lowered `⟦D⟧` back: an `M` whose index type is `Unit`.
    pub(crate) fn read(ty: &Type, g: &LocalCtx) -> Option<MParts> {
        let ty = decoded(ty);
        let Type::M { sig, .. } = &*ty else {
            return None;
        };
        if !matches!(&*decoded(&sig.idx), Type::Unit { .. }) {
            return None;
        }
        let t = Term::Triv { level: sig.idx_level.clone() };
        Some(MParts {
            g: g.clone(),
            sig: Rc::clone(sig),
            ls: sig.level.clone(),
            lp: sig.pos_level.clone(),
            lw: sig.family_level(),
            shape: Rc::new(sig.shape_at(&t)),
            pos: Rc::new(sig.pos_at(&t)),
        })
    }

    /// `⟦D⟧` itself at depth `k`.
    pub(crate) fn d_at(&self, k: u32) -> Type {
        self.sig.shift_local(k).at(triv())
    }

    fn shape_at(&self, k: u32) -> Type {
        self.shape.shift_local(k)
    }

    /// `P(label)`.
    fn pos_at(&self, k: u32, label: Rc<Term>) -> Type {
        self.pos.apply_local(&embed(&self.g, k).extended(label))
    }

    /// `Π(p : P label). ⟦D⟧` — the children's type, as `out` hands them over.
    fn kids_ty(&self, k: u32, label: Rc<Term>) -> Type {
        Type::Pi {
            dom_level: self.lp.clone(),
            cod_level: self.lw.clone(),
            dom: Rc::new(self.pos_at(k, label)),
            cod: Rc::new(self.d_at(k + 1)),
        }
    }

    fn lf(&self) -> Level {
        Level::join(self.lp.clone(), self.lw.clone())
    }

    /// `out`'s type, `Σ(s : S). Π(p : P s). ⟦D⟧` (the kernel's `m_out_ty` at
    /// the unit index).
    fn out_ty(&self, k: u32) -> Type {
        Type::Sigma {
            fst_level: self.ls.clone(),
            snd_level: self.lw.clone(),
            fst: Rc::new(self.shape_at(k)),
            snd: Rc::new(self.kids_ty(k + 1, var(0))),
        }
    }

    fn out(&self, k: u32, t: Rc<Term>) -> Term {
        Term::Out { sig: self.sig.shift_local(k), index: triv(), scrut: t }
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
    fn pos_code(&self, k: u32, gamma: &LocalCtx, label: Rc<Term>) -> Rc<Term> {
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
        tm
    }

    /// A constructor's positions taken apart, in `gamma` (where `label` is
    /// scoped): for `m` children, the `m` component types and the `m - 1`
    /// right tails of the sum (`P(label) ≡ C₀ + (C₁ + …)`). One child's
    /// positions are the whole of `P(label)`; none is `Empty`.
    fn components(&self, k: u32, gamma: &LocalCtx, label: Rc<Term>, m: usize) -> (Vec<Type>, Vec<Type>) {
        let el = |tm: &Rc<Term>| decoded(&Type::El { level: self.lp.clone(), tm: Rc::clone(tm) }).into_owned();
        let mut comps = Vec::with_capacity(m);
        let mut tails = Vec::with_capacity(m.saturating_sub(1));
        let mut cur = self.pos_code(k, gamma, label);
        for _ in 0..m.saturating_sub(1) {
            let Term::TmSum { lhs, rhs, .. } = &*cur else {
                unreachable!("a constructor with several children has sum positions")
            };
            comps.push(el(lhs));
            tails.push(el(rhs));
            let next = Rc::clone(rhs);
            cur = next;
        }
        if m > 0 {
            comps.push(el(&cur));
        }
        (comps, tails)
    }

    /// Child `r` of `m`'s position at `payload` (the `⟨⟩` of a plain child or
    /// the argument of a function child): `inr^r(inl(payload))`, or
    /// `inr^{m-1}(payload)` for the last. `comps`/`tails` are
    /// [`Self::components`]', scoped `k` binders below `payload`.
    fn position(&self, comps: &[Type], tails: &[Type], k: u32, r: usize, payload: Rc<Term>) -> Rc<Term> {
        let m = comps.len();
        let mut t = payload;
        if r + 1 < m {
            t = Rc::new(Term::Inl {
                lhs_level: self.lp.clone(),
                rhs_level: self.lp.clone(),
                lhs: Rc::new(comps[r].shift_local(k)),
                rhs: Rc::new(tails[r].shift_local(k)),
                val: t,
            });
        }
        for j in (0..r).rev() {
            t = Rc::new(Term::Inr {
                lhs_level: self.lp.clone(),
                rhs_level: self.lp.clone(),
                lhs: Rc::new(comps[j].shift_local(k)),
                rhs: Rc::new(tails[j].shift_local(k)),
                val: t,
            });
        }
        t
    }

    /// `λ(p : P label). kids(p)` at a target type over the positions: a case
    /// tree on `p` down the sum, child `r`'s value at each leaf. `value(r,
    /// d, y)` is child `r` at depth `d` (past the label's context), `y` the
    /// position's payload there (a function child's argument; a plain child
    /// ignores it). `target(d)` is the children's type at depth `d`.
    #[allow(clippy::too_many_arguments)]
    fn kids_lam(
        &self,
        k: u32,
        label: Rc<Term>,
        comps: &[Type],
        tails: &[Type],
        target: &dyn Fn(u32) -> Type,
        tlvl: &Level,
        value: &mut dyn FnMut(usize, u32, Rc<Term>) -> R<Term>,
    ) -> R<Term> {
        let m = comps.len();
        // Over (…, p): the case down the sum, scrut at depth `d`.
        #[allow(clippy::too_many_arguments)]
        fn down(
            p: &MParts,
            comps: &[Type],
            tails: &[Type],
            target: &dyn Fn(u32) -> Type,
            tlvl: &Level,
            value: &mut dyn FnMut(usize, u32, Rc<Term>) -> R<Term>,
            r: usize,
            d: u32,
            scrut: Rc<Term>,
        ) -> R<Term> {
            let m = comps.len();
            if r + 1 == m {
                return value(r, d, scrut);
            }
            let case_l = value(r, d + 1, var(0))?;
            let case_r = down(p, comps, tails, target, tlvl, value, r + 1, d + 1, var(0))?;
            Ok(Term::Case {
                lhs_level: p.lp.clone(),
                rhs_level: p.lp.clone(),
                motive_level: tlvl.clone(),
                lhs: Rc::new(comps[r].shift_local(d)),
                rhs: Rc::new(tails[r].shift_local(d)),
                motive: Rc::new(target(d + 1)),
                case_l: Rc::new(case_l),
                case_r: Rc::new(case_r),
                scrut,
            })
        }
        let body = if m == 0 {
            Term::ElimEmpty {
                level: tlvl.clone(),
                scrut_level: self.lp.clone(),
                motive: Rc::new(target(k + 2)),
                scrut: var(0),
            }
        } else {
            down(self, comps, tails, target, tlvl, value, 0, k + 1, var(0))?
        };
        Ok(Term::Lam {
            dom_level: self.lp.clone(),
            cod_level: tlvl.clone(),
            dom: Rc::new(self.pos_at(k, label)),
            body: Rc::new(body),
        })
    }
}

/// A child's value, as [`MParts::kids_lam`]'s leaves need it.
enum KidVal {
    /// Already at the children's type, scoped at depth `k`.
    Tm(Rc<Term>),
    /// A function into the children's type, `Π(y : A). T`, scoped at `k`.
    Fn(Rc<Term>, Rc<Type>),
}

/// A corecursive definition in progress (§5): what [`Elaborator::corec_check`]
/// recognizes and what a corecursive call's seed is built against. Every type
/// is scoped at `depth`, the body's own context (the declaration's whole
/// telescope).
pub(crate) struct CorecSite {
    pub(crate) selfref: Rc<SelfRef>,
    depth: usize,
    ind: Rc<Inductive>,
    /// `⟦D⟧`, the result type.
    d_ty: Type,
    /// The carrier `X`: the varying parameters' tuple.
    carrier: Type,
    carrier_level: Level,
    /// `X + ⟦D⟧` — a child: a new seed, or a tree that already exists.
    child_ty: Type,
    child_level: Level,
    /// `Σ(s : S). Π(p : P s). X + ⟦D⟧` — a node.
    step_ty: Type,
    step_level: Level,
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

    /// `⟦D<args>⟧` for a `codata` declaration (§2).
    pub(crate) fn lower_instance_m(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        let n = ind.ctors.len();
        let (shape, ls) = self.lower_shape(cx, ind, args, vargs, span)?;
        let mut kids: Vec<Vec<Kid>> = Vec::with_capacity(n);
        let mut lp: Option<(Level, String)> = None;
        for (i, ctor) in ind.ctors.iter().enumerate() {
            let doms = if ctor.kind.contains(&FieldKind::FnChild) {
                self.lower_ctor_with_domains(cx, ind, i, args, vargs, span)?.2
            } else {
                Vec::new()
            };
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
        // P over (Γ, x : S): a constant-motive case tree into `Ty lp`.
        let mut xcx = cx.clone();
        xcx.push("#x".into(), shape.clone(), ls.clone());
        let tag = Rc::new(tag_value(&tag_type(ind.tag)));
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
                &mut |bcx, i, d, value| {
                    let mut codes = Vec::with_capacity(kids[i].len());
                    for kid in &kids[i] {
                        codes.push(match kid {
                            Kid::Plain => Term::TmUnit { level: lp.clone() },
                            Kid::Fn(code, j) => {
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
                        });
                    }
                    let Some(mut acc) = codes.pop() else {
                        return Ok(Term::TmEmpty { level: lp.clone() });
                    };
                    while let Some(c) = codes.pop() {
                        acc = Term::TmSum {
                            lhs_level: lp.clone(),
                            rhs_level: lp.clone(),
                            lhs: Rc::new(c),
                            rhs: Rc::new(acc),
                        };
                    }
                    Ok(acc)
                },
            )?
        };
        let pos = Type::El { level: lp.clone(), tm: Rc::new(ptree) };
        // The index binder `i : Unit` goes under everything: the shape binds
        // it, the positions bind `i, s`, the child index `i, s, p`.
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
        Ok((sig.at(triv()), lw))
    }

    // -- constructors (§3) ----------------------------------------------------

    /// `⟦Cᵢ(ā)⟧ = corec(…; _. Unit; _ _. ⟨ℓᵢ, λp. inr(kids p)⟩; ⟨⟩; ⟨⟩)` at
    /// the expected `⟦D⟧`: the apomorphism's `in`, every child an exit.
    pub(crate) fn build_ctor_m(
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
        }, &|d| ty.shift_local(d), &p.lw, span)?;
        // In (Γ, i, x): the node, every child an existing tree.
        let unit = Type::Unit { level: Level::Zero };
        let target = |d: u32| self.child_sum(&p, &unit, &Level::Zero, d);
        let tlvl = Level::join(Level::Zero, p.lw.clone());
        let lab2 = Rc::new(label.shift_local(2));
        let kids = p.kids_lam(2, Rc::clone(&lab2), &comps, &tails, &target, &tlvl, &mut |r, d, y| {
            // `d` is past Γ; the children are scoped in Γ.
            let tree = match &children[r] {
                KidVal::Tm(t) => Rc::new(t.shift_local(d)),
                KidVal::Fn(f, dom) => Rc::new(checked_app(
                    Rc::new(f.shift_local(d)),
                    p.lp.clone(),
                    p.lw.clone(),
                    Rc::new(dom.shift_local(d)),
                    Rc::new(p.d_at(d + 1)),
                    y,
                )),
            };
            Ok(Term::Inr {
                lhs_level: Level::Zero,
                rhs_level: p.lw.clone(),
                lhs: Rc::new(unit.clone()),
                rhs: Rc::new(p.d_at(d)),
                val: tree,
            })
        })?;
        let step = self.step_pair(&p, 2, lab2, &unit, &Level::Zero, kids);
        Ok(Term::Corec {
            sig: Rc::clone(&p.sig),
            carrier_level: Level::Zero,
            carrier: Rc::new(unit.clone()),
            step: Rc::new(step),
            index: triv(),
            seed: triv(),
        })
    }

    /// The pieces every node is built from, in `cx` (which is `p`'s
    /// context): the label from the payload arguments, the positions taken
    /// apart, and each child checked by `child` — a plain one at
    /// `plain_ty(0)`, a function one at `Π(y : A). plain_ty(1)` with `A` the
    /// position read off the label.
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn ctor_parts(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        p: &MParts,
        args: &[&Expr],
        child: &mut dyn FnMut(&Cx, &Expr, &Type) -> R<Rc<Term>>,
        plain_ty: &dyn Fn(u32) -> Type,
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
        let ty = p.d_at(0);
        let spine = self.spine(&ty, &p.lw, n, span)?;
        let payload: Vec<&Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| **k == FieldKind::Payload)
            .map(|(a, _)| *a)
            .collect();
        let fields = self.build_fields(cx, &spine.ctors[i].0, &payload, true, span)?;
        let label = inject(&spine, i, n, fields, 0);
        let m = ctor.kind.iter().filter(|k| k.is_child()).count();
        let (comps, tails) = p.components(0, &cx.gamma, Rc::new(label.clone()), m);
        let mut children = Vec::with_capacity(m);
        let mut r = 0usize;
        for (k, kind) in ctor.kind.iter().enumerate() {
            match kind {
                FieldKind::Plain => {
                    children.push(KidVal::Tm(child(cx, args[k], &plain_ty(0))?));
                    r += 1;
                }
                FieldKind::FnChild => {
                    let dom = Rc::new(comps[r].clone());
                    let k_ty = Type::Pi {
                        dom_level: p.lp.clone(),
                        cod_level: plain_level.clone(),
                        dom: Rc::clone(&dom),
                        cod: Rc::new(plain_ty(1)),
                    };
                    children.push(KidVal::Fn(child(cx, args[k], &k_ty)?, dom));
                    r += 1;
                }
                _ => {}
            }
        }
        Ok((label, comps, tails, children))
    }

    /// `X + ⟦D⟧` at depth `d`, `X` scoped at depth 0.
    fn child_sum(&self, p: &MParts, carrier: &Type, carrier_level: &Level, d: u32) -> Type {
        Type::Sum {
            lhs_level: carrier_level.clone(),
            rhs_level: p.lw.clone(),
            lhs: Rc::new(carrier.shift_local(d)),
            rhs: Rc::new(p.d_at(d)),
        }
    }

    /// `⟨label, kids⟩` at the step type `Σ(s : S). Π(p : P s). X + ⟦D⟧`, at
    /// depth `k` (`X` scoped at depth 0), in the kernel's `m_step_ty`
    /// levels.
    fn step_pair(&self, p: &MParts, k: u32, label: Rc<Term>, carrier: &Type, carrier_level: &Level, kids: Term) -> Term {
        let kf = Level::join(carrier_level.clone(), p.lw.clone());
        Term::Pair {
            fst_level: p.ls.clone(),
            snd_level: kf.clone(),
            fst_ty: Rc::new(p.shape_at(k)),
            snd_ty: Rc::new(Type::Pi {
                dom_level: p.lp.clone(),
                cod_level: kf,
                dom: Rc::new(p.pos_at(k + 1, var(0))),
                cod: Rc::new(self.child_sum(p, carrier, carrier_level, k + 2)),
            }),
            fst: label,
            snd: Rc::new(kids),
        }
    }

    /// The step type at depth `k`, `X` scoped at depth 0.
    fn step_ty(&self, p: &MParts, k: u32, carrier: &Type, carrier_level: &Level) -> Type {
        let kf = Level::join(carrier_level.clone(), p.lw.clone());
        Type::Sigma {
            fst_level: p.ls.clone(),
            snd_level: kf.clone(),
            fst: Rc::new(p.shape_at(k)),
            snd: Rc::new(Type::Pi {
                dom_level: p.lp.clone(),
                cod_level: kf,
                dom: Rc::new(p.pos_at(k + 1, var(0))),
                cod: Rc::new(self.child_sum(p, carrier, carrier_level, k + 2)),
            }),
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
        let spine = self.spine(scrut_ty, &p.lw, n, span)?;
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
                let (comps, tails) = p.components(d, &bcx.gamma, Rc::clone(&inj), m);
                let mut payload_k = 0usize;
                let mut r = 0usize;
                for (k, name) in arm.binders.iter().map(|b| b.name().to_string()).enumerate() {
                    let (term, ty, level) = match ctor.kind[k] {
                        FieldKind::Plain => {
                            let at = p.position(&comps, &tails, 1, r, Rc::new(Term::Triv { level: p.lp.clone() }));
                            r += 1;
                            (app_at(var(0), at), p.d_at(db), p.lw.clone())
                        }
                        FieldKind::FnChild => {
                            let dom = Rc::new(comps[r].shift_local(1));
                            let at = p.position(&comps, &tails, 2, r, var(0));
                            r += 1;
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
                                cod: Rc::new(p.d_at(db + 1)),
                            };
                            (term, ty, lf.clone())
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
        // The carrier, built in the body's context: component `r` is the
        // `r`-th varying parameter's type, its earlier parameters replaced by
        // the outer binder (fixed) or the Σ binder (varying).
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
        let (carrier, carrier_level) = match comps.len() {
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
        // The result type may mention only the fixed parameters: it is the
        // signature of the one `corec`, which sits outside the carrier.
        for (j, r) in rank.iter().enumerate() {
            if r.is_some() && crate::mentions_binder(&head, depth as u32, (n - 1 - j) as u32) {
                return err(
                    format!(
                        "the result type of the corecursive `{}` mentions `{}`, which a corecursive \
                         call changes: the result type may mention only parameters every call passes \
                         unchanged (docs/codata-elaborator-design.md §5)",
                        decl.name, names[j]
                    ),
                    span,
                );
            }
        }
        let child_ty = self.child_sum(&p, &carrier, &carrier_level, 0);
        let step_ty = self.step_ty(&p, 0, &carrier, &carrier_level);
        let kf = Level::join(carrier_level.clone(), p.lw.clone());
        Ok(Some(Rc::new(CorecSite {
            selfref: Rc::clone(selfref),
            depth,
            ind: Rc::clone(&ind),
            d_ty: head,
            carrier,
            carrier_level: carrier_level.clone(),
            child_ty,
            child_level: kf.clone(),
            step_ty,
            step_level: Level::join(p.ls.clone(), Level::join(p.lp.clone(), kf)),
            rank,
            names,
        })))
    }

    /// The body's expected type and level under `site`.
    pub(crate) fn corec_body_ty(site: &CorecSite) -> (Type, Level) {
        (site.step_ty.clone(), site.step_level.clone())
    }

    /// The definition's term from its step `b` (scoped in the body's
    /// context): `corec(sig; _. X; _ x. b[varying ↦ projections of x]; ⟨⟩;
    /// ⟨varying parameters⟩)`, in the body's context.
    pub(crate) fn corec_close(&self, cx: &Cx, n_ty: usize, site: &CorecSite, b: Term, span: Span) -> R<Term> {
        let Some(p) = MParts::read(&site.d_ty, &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", span);
        };
        let n = site.rank.len();
        let nv = site.varying();
        // In (body, i, x): the varying parameters are the carrier's
        // components, the fixed ones the outer binders.
        let proj = |r: usize| -> Term {
            let mut t = Term::Var(LocalVar(0));
            if nv == 1 {
                return t;
            }
            for _ in 0..r {
                t = Term::SndAt { pair: Rc::new(t) };
            }
            if r + 1 < nv { Term::FstAt { pair: Rc::new(t) } } else { t }
        };
        let base = cx.gamma.prefix(n_ty);
        let mut subst = embed(&base, (n + 2) as u32);
        for (j, r) in site.rank.iter().enumerate() {
            let t = match r {
                None => Term::Var(LocalVar((n - 1 - j + 2) as u32)),
                Some(r) => proj(*r),
            };
            subst = subst.extended(Rc::new(t));
        }
        let step = b.apply_local(&subst);
        let seed = self.carrier_tuple(&site.carrier, nv, &mut |r| {
            let j = site.rank.iter().position(|x| *x == Some(r)).expect("a varying parameter");
            Ok(Rc::new(Term::Var(LocalVar((n - 1 - j) as u32))))
        })?;
        Ok(Term::Corec {
            sig: Rc::clone(&p.sig),
            carrier_level: site.carrier_level.clone(),
            carrier: Rc::new(site.carrier.shift_local(1)),
            step: Rc::new(step),
            index: triv(),
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

    /// The checking-mode hook while a corecursive body is open (§5.2):
    /// `Some(term)` when `e`, checked at `expected`, is one of the step's two
    /// positions and this function built it; `None` to elaborate it as usual.
    pub(crate) fn corec_check(&self, cx: &Cx, site: &CorecSite, e: &Expr, expected: &Type, lvl: &Level) -> R<Option<Term>> {
        let by = site.by(cx);
        let step_here = site.step_ty.shift_local(by);
        let child_here = site.child_ty.shift_local(by);
        let at = |want: &Type, wlvl: &Level| -> bool {
            *expected == *want || {
                let head = self.whnf(cx, expected, e.span).ok();
                matches!(head, Some(Type::Sigma { .. } | Type::Sum { .. }))
                    && self.conv_types(cx, expected, want, wlvl)
            }
        };
        let _ = lvl;
        let self_call = surface_self_call(&site.selfref, e);
        let is_child = at(&child_here, &site.child_level);
        if let Some((args, _)) = self_call {
            if !is_child {
                return err(
                    format!(
                        "this call to `{}` is not guarded: a corecursive call must be a child of the \
                         constructor the definition returns — `C(…, {}(…), …)` or `C(…, λ y => {}(…), …)` \
                         (docs/codata-elaborator-design.md §5)",
                        site.selfref.written_name, site.selfref.written_name, site.selfref.written_name
                    ),
                    e.span,
                );
            }
            if let ExprKind::App { head, .. } = &e.kind
                && matches!(head.kind, ExprKind::TyApp { .. })
            {
                return err(
                    "a corecursive call takes no type arguments: they are the definition's own",
                    e.span,
                );
            }
            let seed = self.corec_seed(cx, site, &args, e.span)?;
            let p = MParts::read(&site.d_ty, &LocalCtx::nil()).expect("planned at an M");
            return Ok(Some(Term::Inl {
                lhs_level: site.carrier_level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(site.carrier.shift_local(by)),
                rhs: Rc::new(site.d_ty.shift_local(by)),
                val: Rc::new(seed),
            }));
        }
        let control = matches!(e.kind, ExprKind::Match { .. } | ExprKind::Block(..));
        if is_child {
            if control {
                return Ok(None);
            }
            // An existing tree — which must not itself corecurse: a self-call
            // under a *second* constructor needs a carrier that remembers
            // the pending constructor, which this round's one-step `corec`
            // does not build (issues/codata-nested-guards.md).
            let mut nested = None;
            crate::surface::walk_expr(e, &mut |x| {
                if nested.is_none() && surface_self_call(&site.selfref, x).is_some() {
                    nested = Some(x.span);
                }
            });
            if let Some(at) = nested {
                let name = &site.selfref.written_name;
                return err(
                    format!(
                        "this call to `{name}` sits under a second constructor: a corecursive call \
                         must be a *direct* child of the constructor the step returns, and nesting \
                         one constructor inside another before the call is not supported yet — \
                         name the inner layer as a seed state of its own instead \
                         (issues/codata-nested-guards.md)"
                    ),
                    at,
                );
            }
            let d_here = site.d_ty.shift_local(by);
            let p = MParts::read(&site.d_ty, &LocalCtx::nil()).expect("planned at an M");
            let t = self.elab_check(cx, e, &d_here, &p.lw)?;
            return Ok(Some(Term::Inr {
                lhs_level: site.carrier_level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(site.carrier.shift_local(by)),
                rhs: Rc::new(d_here),
                val: Rc::new(t),
            }));
        }
        if !at(&step_here, &site.step_level) {
            return Ok(None);
        }
        if control {
            return Ok(None);
        }
        let Some(p) = MParts::read(&site.d_ty.shift_local(by), &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", e.span);
        };
        let carrier = site.carrier.shift_local(by);
        let tlvl = site.child_level.clone();
        // A node: a constructor of the declaration itself.
        if let Some((i, args)) = self.codata_ctor_app(cx, &site.ind, e) {
            let (label, comps, tails, children) = self.ctor_parts(
                cx,
                &site.ind,
                i,
                &p,
                &args,
                &mut |cx, arg, at| Ok(Rc::new(self.elab_check(cx, arg, at, &tlvl)?)),
                &|d| self.child_sum(&p, &carrier, &site.carrier_level, d),
                &tlvl,
                e.span,
            )?;
            let target = |d: u32| self.child_sum(&p, &carrier, &site.carrier_level, d);
            let kids = p.kids_lam(0, Rc::new(label.clone()), &comps, &tails, &target, &tlvl, &mut |r, d, y| {
                Ok(match &children[r] {
                    KidVal::Tm(t) => t.shift_local(d),
                    KidVal::Fn(f, dom) => checked_app(
                        Rc::new(f.shift_local(d)),
                        p.lp.clone(),
                        tlvl.clone(),
                        Rc::new(dom.shift_local(d)),
                        Rc::new(target(d + 1)),
                        y,
                    ),
                })
            })?;
            return Ok(Some(self.step_pair(&p, 0, Rc::new(label), &carrier, &site.carrier_level, kids)));
        }
        // Anything else is a tree that already exists, and the node is its
        // first one: `(λo. ⟨fst o, λq. inr(snd o q)⟩) (out t)`.
        let t = Rc::new(self.elab_check(cx, e, &p.d_at(0), &p.lw)?);
        let o_ty = Rc::new(p.out_ty(0));
        let kf = Level::join(site.carrier_level.clone(), p.lw.clone());
        let lab = Rc::new(p.out_fst(1, var(0)));
        let kids = Term::Lam {
            dom_level: p.lp.clone(),
            cod_level: kf.clone(),
            dom: Rc::new(p.pos_at(1, Rc::clone(&lab))),
            body: Rc::new(Term::Inr {
                lhs_level: site.carrier_level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(carrier.shift_local(2)),
                rhs: Rc::new(p.d_at(2)),
                val: Rc::new(checked_app(
                    Rc::new(p.out_snd(2, var(1))),
                    p.lp.clone(),
                    p.lw.clone(),
                    Rc::new(p.pos_at(2, Rc::new(p.out_fst(2, var(1))))),
                    Rc::new(p.d_at(3)),
                    var(0),
                )),
            }),
        };
        let node = self.step_pair(&p, 1, lab, &carrier, &site.carrier_level, kids);
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

    /// A corecursive call's seed: the varying arguments as a carrier value,
    /// each fixed argument checked to be its own parameter.
    fn corec_seed(&self, cx: &Cx, site: &CorecSite, args: &[&Expr], span: Span) -> R<Term> {
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
        self.corec_seed_checked(cx, site, args, &site.carrier.shift_local(by))
    }

    /// [`Self::corec_seed`]'s tuple, each component checked at its type with
    /// the earlier components substituted.
    fn corec_seed_checked(&self, cx: &Cx, site: &CorecSite, args: &[&Expr], carrier: &Type) -> R<Term> {
        let varying: Vec<usize> = (0..site.rank.len()).filter(|&j| site.rank[j].is_some()).collect();
        let mut parts = Vec::new();
        let mut cur = carrier.clone();
        for (r, &j) in varying.iter().enumerate() {
            if r + 1 == varying.len() {
                let mut acc = Rc::new(self.elab_check(cx, args[j], &cur, &site.carrier_level)?);
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
