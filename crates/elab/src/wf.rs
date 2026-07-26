//! Tier-1 inductive declarations: the lowering onto the `Wf` former.
//!
//! This module is the mechanization of `docs/inductive-tier1-wf-lowering.md`
//! and is meant to be read against it — the section numbers in the comments
//! are that document's. The doctrine is tier 0's
//! (`inductive.rs`, `issues/inductive-compiler.md`): untrusted like the rest
//! of the elaborator, but a bug here produces a *checked theorem about the
//! wrong type* rather than a rejection, so no clever shortcuts, one function
//! per numbered rule, and every annotation is read off the type being
//! eliminated rather than rebuilt.
//!
//! What is *shared* with tier 0 rather than copied: the shape is
//! `inductive.rs`'s sum-of-Σs with the recursive fields deleted, the arity is
//! its constant-motive case tree at the motive `Nat`, and the step's case
//! tree has the same right-nested shape as `case_tree`. What is shared with
//! the *kernel*: the three types of the step telescope come from
//! `term::wf_step_telescope`, which `typing.rs`, `conv.rs`, `rec.rs` and
//! `reduce.rs` also call. A fifth transcription here would be exactly the
//! drift that arrangement exists to prevent.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{nth, wf_step_telescope, LocalCtx, LocalVar, Term, Type};
use heather_syntax::{Arm, Expr, Span};

use crate::inductive::{inject, nat_lit, Inductive, Spine};
use crate::{embed, err, Alias, Cx, Elaborator, Guard, GuardKind, R};

/// The pieces every part of the lowering needs, gathered once so that the
/// recursion below carries one reference instead of eight arguments.
///
/// The three telescope types are the kernel's own (§6.1) and are scoped as
/// `wf_step_telescope` returns them:
///
/// ```text
/// cs_ty    over (Γ, a)             = Vec^l(⟦D⟧; n[a/x])
/// ih_ty    over (Γ, a, cs)         = Π(i : Fin n[a/x]). M[nth(…; cs; i)/z]
/// step_ty  over (Γ, a, cs, ih)     = M[sup_f(a; cs)/z]
/// ```
///
/// where `Γ` is `gamma0` — the *ambient* context of the `match`, which every
/// substitution below is expressed relative to.
struct Tel<'a> {
    /// The `match`'s ambient local context.
    gamma0: &'a LocalCtx,
    /// `⟦D⟧`, scoped in `gamma0`.
    d_ty: &'a Type,
    /// `l`: the declaration's level, which is also its shape's.
    level: Level,
    /// `l'`: the motive's level.
    mlvl: Level,
    /// `M`, over `(gamma0, z : ⟦D⟧)`.
    motive: Rc<Type>,
    cs_ty: Type,
    ih_ty: Type,
    step_ty: Type,
    /// The declaration's tag spine, scoped in `gamma0`.
    spine: Spine,
}

impl Tel<'_> {
    /// The Π-type of a branch body before its two λs: `P(v)` of §6.2, for a
    /// *fully injected* `v : S` scoped `d` binders past `gamma0`.
    ///
    /// The three instantiations differ only in how deep they sit, and each
    /// maps the telescope's own binders (`a`, `cs`, `ih`) to what stands for
    /// them here. Writing them out rather than folding them is deliberate:
    /// this is the de Bruijn arithmetic the issue's hazard list warns about.
    fn at(&self, inj: &Rc<Term>, d: u32) -> (Type, Type, Type) {
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        // cs' : cs_ty[v/a], in the branch context itself.
        let cs = self
            .cs_ty
            .apply_local(&embed(self.gamma0, d).extended(Rc::clone(inj)));
        // ih' : ih_ty[v/a, cs'/cs], one binder deeper (cs' is Var 0).
        let ih = self.ih_ty.apply_local(
            &embed(self.gamma0, d + 1)
                .extended(Rc::new(inj.shift_local(1)))
                .extended(var(0)),
        );
        // the body : step_ty[v/a, cs'/cs, ih'/ih], two binders deeper.
        let step = self.step_ty.apply_local(
            &embed(self.gamma0, d + 2)
                .extended(Rc::new(inj.shift_local(2)))
                .extended(var(1))
                .extended(var(0)),
        );
        (cs, ih, step)
    }
}

impl Elaborator {
    // -- constructors (§5) --------------------------------------------------

    /// The children tuple `(r₁, (r₂, … (r_m, ⟨⟩)))` at `Vec^l(⟦D⟧; m)`, built
    /// at the *literal* arity `m` rather than at `n[ℓᵢ/x]`. The two are
    /// convertible — the arity is a `Case` on an injection, so it β-reduces to
    /// the literal, and `Vec` reduces on the whnf of its length — and the
    /// literal is the one the kernel can unfold to a Σ-chain.
    ///
    /// `d_ty` is `⟦D⟧` (the whole `Wf`), scoped in `cx`.
    pub(crate) fn build_children(
        &self,
        cx: &Cx,
        d_ty: &Type,
        level: &Level,
        args: &[Expr],
        span: Span,
    ) -> R<Term> {
        let _ = span;
        // `Vec^l(T; 0) ⇝ Unit^l`, which carries the level since route (a) of
        // issues/unit-level-and-vec-preservation.md; a `Triv` at 0 here would
        // be exactly the defect that round closed.
        let mut acc = Term::Triv { level: level.clone() };
        for (k, arg) in args.iter().enumerate().rev() {
            let child = self.elab_check(cx, arg, d_ty, level)?;
            // What is left *after* this child: the tail's length.
            let tail = args.len() - 1 - k;
            acc = Term::Pair {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::new(d_ty.clone()),
                // `Vec(T; S k) ⇝ Σ(_ : T). Vec(T; k)` and a Σ's second
                // component *binds*, so the tail type sits one level deeper
                // than the ambient (§5).
                snd_ty: Rc::new(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(d_ty.shift_local(1)),
                    len: Rc::new(nat_lit(tail)),
                }),
                fst: Rc::new(child),
                snd: Rc::new(acc),
            };
        }
        Ok(acc)
    }

    // -- match (§6) ---------------------------------------------------------

    /// `match` on a tier-1 inductive: one `elim_Wf` whose step cases on the
    /// tag with `cs` and `ih` generalized (§6.2).
    ///
    /// `arms` is already permuted into declaration order and checked for
    /// completeness, duplication and binder arity by the tier-0 entry point;
    /// `scrut_ty` is the whnf'd `⟦D⟧`, and `motive` is scoped over
    /// `(cx.gamma, z : ⟦D⟧)`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_wf(
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
        let Type::Wf { level, shape, arity } = scrut_ty else {
            return err("internal: a recursive declaration did not lower to a `Wf`", span);
        };
        let motive = Rc::new(motive);
        let (cs_ty, ih_ty, step_ty) =
            wf_step_telescope(&cx.gamma, level, &mlvl, shape, arity, &motive);
        let tel = Tel {
            gamma0: &cx.gamma,
            d_ty: scrut_ty,
            level: level.clone(),
            mlvl: mlvl.clone(),
            motive: Rc::clone(&motive),
            spine: self.spine(scrut_ty, level, ind.ctors.len(), span)?,
            cs_ty,
            ih_ty,
            step_ty,
        };
        // Does this `match` descend on one of the enclosing declaration's own
        // parameters? If so, a self-call in an arm is the ih (§6.4).
        let dec = self.descends_on_param(cx, &scrut);

        // Γ₃ = (Γ, a : S, cs : cs_ty, ih : ih_ty) — the step's context, and
        // the kernel's, verbatim (typing.rs's `elim_Wf` rule).
        let mut cx3 = cx.clone();
        cx3.push("#a".into(), (**shape).clone(), tel.level.clone());
        cx3.push("#cs".into(), tel.cs_ty.clone(), tel.level.clone());
        cx3.push("#ih".into(), tel.ih_ty.clone(), tel.mlvl.clone());

        // The case motive `P`, over (Γ₃, z : S): the telescope re-abstracted
        // at `z` in place of `a`. It lives at `l ⊔ l'` — a Π at the max of
        // its ends, twice.
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        let (p_cs, p_ih, p_step) = {
            let cs = tel.cs_ty.apply_local(&embed(tel.gamma0, 4).extended(var(0)));
            let ih = tel.ih_ty.apply_local(
                &embed(tel.gamma0, 5).extended(var(1)).extended(var(0)),
            );
            let step = tel.step_ty.apply_local(
                &embed(tel.gamma0, 6).extended(var(2)).extended(var(1)).extended(var(0)),
            );
            (cs, ih, step)
        };
        let p_motive = Type::Pi {
            dom_level: tel.level.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(p_cs),
            cod: Rc::new(Type::Pi {
                dom_level: tel.mlvl.clone(),
                cod_level: tel.mlvl.clone(),
                dom: Rc::new(p_ih),
                cod: Rc::new(p_step),
            }),
        };
        let plvl = Level::max(tel.level.clone(), tel.mlvl.clone());

        let cased = self.wf_case_tree(
            &cx3, ind, arms, &tel, dec, 0, p_motive, &plvl, var(2), 3, span,
        )?;
        let step = self.apply_cs_ih(&tel, cased);

        Ok(Term::ElimWf {
            level: tel.level.clone(),
            motive_level: tel.mlvl.clone(),
            shape: Rc::clone(shape),
            arity: Rc::clone(arity),
            motive,
            step: Rc::new(step),
            scrut: Rc::new(scrut),
        })
    }

    /// `(P-case on a) cs ih` (§6.2): the two applications that re-connect the
    /// generalized `cs'`/`ih'` to the step's real ones. Both `cod`
    /// annotations **bind their own argument**, so they sit one level deeper
    /// than `Γ₃` — the de Bruijn slip both kernel acceptance tests made first.
    fn apply_cs_ih(&self, tel: &Tel, cased: Term) -> Term {
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        let g = tel.gamma0;
        // Domains, over Γ₃ itself: a = 2, cs = 1.
        let dom_cs = tel.cs_ty.apply_local(&embed(g, 3).extended(var(2)));
        let dom_ih = tel
            .ih_ty
            .apply_local(&embed(g, 3).extended(var(2)).extended(var(1)));
        // First `cod`, over (Γ₃, cs''): a = 3, cs = cs'' = 0.
        let cod1 = Type::Pi {
            dom_level: tel.mlvl.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(
                tel.ih_ty
                    .apply_local(&embed(g, 4).extended(var(3)).extended(var(0))),
            ),
            // …and its own cod, over (Γ₃, cs'', ih''): a = 4, cs = 1, ih = 0.
            cod: Rc::new(tel.step_ty.apply_local(
                &embed(g, 5).extended(var(4)).extended(var(1)).extended(var(0)),
            )),
        };
        // Second `cod`, over (Γ₃, ih''): a = 3, cs = 2 (the *real* one, since
        // the first application already consumed it), ih = ih'' = 0.
        let cod2 = tel.step_ty.apply_local(
            &embed(g, 4).extended(var(3)).extended(var(2)).extended(var(0)),
        );
        let at_cs = Term::App {
            fun: Rc::new(cased),
            dom_level: tel.level.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(dom_cs),
            cod: Rc::new(cod1),
            arg: var(1),
        };
        Term::App {
            fun: Rc::new(at_cs),
            dom_level: tel.mlvl.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(dom_ih),
            cod: Rc::new(cod2),
            arg: var(0),
        }
    }

    /// The step's case tree (§6.2). Structurally tier 0 §5.2's: right-nested
    /// `Case`, the motive composed with the injection at each depth, no
    /// `Case` at all at the last constructor. What differs is the branch — it
    /// is a pair of λs, not the arm body directly.
    ///
    /// `cx` is Γ₃ plus the `j` binders this recursion has pushed, `motive` is
    /// `P_j` over `(cx, z : R_j)`, `scrut` is the `R_j`-typed scrutinee, and
    /// `d` is how far the spine (scoped in `gamma0`) has to be weakened here.
    #[allow(clippy::too_many_arguments)]
    fn wf_case_tree(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[&Arm],
        tel: &Tel,
        dec: Option<usize>,
        j: usize,
        motive: Type,
        plvl: &Level,
        scrut: Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Term> {
        let n = arms.len();
        if j + 1 == n {
            return self.wf_branch(cx, ind, arms[j], tel, dec, j, scrut, d, span);
        }
        let ctor_lvl = tel.spine.ctors[j].1.clone();
        let tail_lvl = tel.spine.tails[j].1.clone();
        let ctor_ty = Rc::new(tel.spine.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(tel.spine.tails[j].0.shift_local(d));
        // case_l: binder `x : ⟦c_j⟧`, body at `P_j[inl x/z]`.
        let mut lcx = cx.clone();
        lcx.push("#scrut".into(), (*ctor_ty).clone(), ctor_lvl.clone());
        let case_l = self.wf_branch(
            &lcx,
            ind,
            arms[j],
            tel,
            dec,
            j,
            Rc::new(Term::Var(LocalVar(0))),
            d + 1,
            span,
        )?;
        // case_r: binder `y : R_{j+1}`; inside it, the next `Case`, whose
        // motive is `P_j` composed with `inr` and weakened past `y`.
        let mut rcx = cx.clone();
        rcx.push("#rest".into(), (*tail_ty).clone(), tail_lvl.clone());
        let inr = Term::Inr {
            lhs_level: ctor_lvl.clone(),
            rhs_level: tail_lvl.clone(),
            lhs: Rc::new(tel.spine.ctors[j].0.shift_local(d + 1)),
            rhs: Rc::new(tel.spine.tails[j].0.shift_local(d + 1)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let inner = motive.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(inr)));
        let case_r = self.wf_case_tree(
            &rcx,
            ind,
            arms,
            tel,
            dec,
            j + 1,
            inner,
            plvl,
            Rc::new(Term::Var(LocalVar(0))),
            d + 1,
            span,
        )?;
        Ok(Term::Case {
            lhs_level: ctor_lvl,
            rhs_level: tail_lvl,
            motive_level: plvl.clone(),
            lhs: ctor_ty,
            rhs: tail_ty,
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    /// One branch of the step (§6.3): `λ(cs'). λ(ih'). ⟦armᵢ⟧`, with the
    /// surface binders aliased to projections of the label and to `nth` of
    /// the children, and the guard set so that a self-call becomes `ih' ι_t`.
    ///
    /// `value : ⟦cᵢ⟧` is scoped in `cx`, which sits `d` binders past
    /// `gamma0`.
    #[allow(clippy::too_many_arguments)]
    fn wf_branch(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arm: &Arm,
        tel: &Tel,
        dec: Option<usize>,
        i: usize,
        value: Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let m = ctor.arity();
        // The value's full injection into `S`, which is what the telescope's
        // `a` stands for in this branch.
        let inj = Rc::new(inject(&tel.spine, i, ind.ctors.len(), (*value).clone(), d));
        let (cs_dom, ih_dom, body_ty) = tel.at(&inj, d);

        let mut bcx = cx.clone();
        bcx.push("#cs".into(), cs_dom.clone(), tel.level.clone());
        bcx.push("#ih".into(), ih_dom.clone(), tel.mlvl.clone());
        // In the body: cs' = Var 1, ih' = Var 0, and everything scoped in
        // `cx` has moved two binders out.
        let cs_var = Rc::new(Term::Var(LocalVar(1)));
        let d_body = d + 2;
        let d_ty_here = Rc::new(tel.d_ty.shift_local(d_body));
        let len = Rc::new(nat_lit(m));

        // The `t`-th child, `nth^l(⟦D⟧; m; cs'; ι_t)`. At a literal `m` this
        // β-reduces to the projections of `cs'` even though `cs'` is a
        // variable, which is what makes an arm binder behave like a field.
        let child = |t: usize| {
            Rc::new(nth(
                &tel.level,
                &d_ty_here,
                &len,
                Rc::clone(&cs_var),
                Rc::new(fin_index(t, m)),
            ))
        };

        let mut acx = bcx.clone();
        let ctor_ty = tel.spine.ctors[i].0.shift_local(d_body);
        let value_here = Rc::new(value.shift_local(2));
        let mut children = Vec::with_capacity(m);
        let (mut payload_k, mut rec_t) = (0usize, 0usize);
        for (k, name) in arm.binders.iter().enumerate() {
            if ctor.rec_field[k] {
                let c = child(rec_t);
                // The ih at this index, and the type it lands at: the
                // eliminator's `cod` binds `i`, so it is `M[nth(…; i)/z]`
                // one binder deeper, and instantiating it at `ι_t` gives
                // `M[child/z]` — which is the child term verbatim.
                let cod = tel.motive.apply_local(
                    &embed(tel.gamma0, d_body + 1).extended(Rc::new(nth(
                        &tel.level,
                        &Rc::new(tel.d_ty.shift_local(d_body + 1)),
                        &len,
                        Rc::new(Term::Var(LocalVar(2))),
                        Rc::new(Term::Var(LocalVar(0))),
                    ))),
                );
                let ih_at = Rc::new(Term::App {
                    fun: Rc::new(Term::Var(LocalVar(0))),
                    dom_level: Level::Zero,
                    cod_level: tel.mlvl.clone(),
                    dom: Rc::new(Type::Fin { len: Rc::clone(&len) }),
                    cod: Rc::new(cod),
                    arg: Rc::new(fin_index(rec_t, m)),
                });
                let ih_ty = tel
                    .motive
                    .apply_local(&embed(tel.gamma0, d_body).extended(Rc::clone(&c)));
                acx.aliases.push(Rc::new(Alias {
                    name: name.clone(),
                    depth: acx.names.len(),
                    term: Rc::clone(&c),
                    ty: tel.d_ty.shift_local(d_body),
                    level: tel.level.clone(),
                }));
                children.push((c, ih_at, ih_ty, tel.mlvl.clone()));
                rec_t += 1;
            } else {
                let (proj, ty, level) =
                    self.projection(&acx, &ctor_ty, &value_here, payload_k, span)?;
                acx.aliases.push(Rc::new(Alias {
                    name: name.clone(),
                    depth: acx.names.len(),
                    term: proj,
                    ty,
                    level,
                }));
                payload_k += 1;
            }
        }
        // A self-call in this arm is the ih (§6.4) — but only if the `match`
        // descends on one of the declaration's own parameters. If it does
        // not, an enclosing arm's guard, if any, still stands.
        acx.guard = dec
            .map(|dec| {
                Rc::new(Guard {
                    dec,
                    kind: GuardKind::Wf { depth: acx.names.len(), children },
                })
            })
            .or_else(|| cx.guard.clone());

        let body = self.elab_check(&acx, &arm.body, &body_ty, &tel.mlvl)?;
        Ok(Term::Lam {
            dom_level: tel.level.clone(),
            cod_level: tel.mlvl.clone(),
            dom: Rc::new(cs_dom),
            body: Rc::new(Term::Lam {
                dom_level: tel.mlvl.clone(),
                cod_level: tel.mlvl.clone(),
                dom: Rc::new(ih_dom),
                body: Rc::new(body),
            }),
        })
    }
}

/// The literal index `t` of `Fin m`: `inr^t (inl ⟨⟩)` (§6.3). Each tail is
/// annotated with `Fin` itself rather than its unfolded sum — `Fin(S k) ⇝
/// Unit⁰ + Fin(k)`, so the kernel converts the two, and the folded form is
/// what a goal reads back as.
fn fin_index(t: usize, m: usize) -> Term {
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let mut v = Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: unit(),
        rhs: Rc::new(Type::Fin { len: Rc::new(nat_lit(m - t - 1)) }),
        val: Rc::new(Term::Triv { level: Level::Zero }),
    };
    for k in (0..t).rev() {
        v = Term::Inr {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: Rc::new(Type::Fin { len: Rc::new(nat_lit(m - k - 1)) }),
            val: Rc::new(v),
        };
    }
    v
}
