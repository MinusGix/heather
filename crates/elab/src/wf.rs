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

use crate::inductive::{inject, ConstBody, FieldKind, Inductive, Spine};
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
pub(crate) struct Tel<'a> {
    /// The `match`'s ambient local context.
    pub gamma0: &'a LocalCtx,
    /// `⟦D⟧`, scoped in `gamma0`.
    pub d_ty: &'a Type,
    /// `l`: the declaration's level, which is also its shape's.
    pub level: Level,
    /// `l'`: the motive's level.
    pub mlvl: Level,
    /// `M`, over `(gamma0, z : ⟦D⟧)`.
    pub motive: Rc<Type>,
    cs_ty: Type,
    ih_ty: Type,
    step_ty: Type,
    /// The declaration's tag spine, scoped in `gamma0`.
    pub spine: Spine,
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

/// What a branch of the step's case tree computes. The two share the whole
/// eliminator — the telescope, the case tree, the `cs`/`ih` generalization
/// and the two trailing applications — and differ only in the body at each
/// constructor.
pub(crate) enum Branches<'a> {
    /// `match`: the surface arms, already in declaration order (§6.3).
    Arms(&'a [&'a Arm]),
    /// A body the caller builds, for an eliminator on this declaration that is
    /// not a `match` on it: the family over a declared index and its derived
    /// eliminator both case on the *index* type here
    /// (docs/inductive-indexed-lowering.md §8.2), so the branch body is an
    /// indexed-family thing and only the `cs`/`ih` threading is tier 1's.
    ///
    /// Called as `(bcx, tel, i, value, d_body, body_ty)` with `bcx` the branch
    /// context, `i` the constructor, `value : ⟦cᵢ⟧` and `d_body` its depth past
    /// `gamma0`, and `body_ty` the obligation. By the branch convention the
    /// refined `cs'` is `Var 1` and `ih'` is `Var 0` in `bcx`.
    #[allow(clippy::type_complexity)]
    Custom(&'a dyn Fn(&Cx, &Tel, usize, &Rc<Term>, u32, &Type) -> R<Term>),
    /// Injectivity at a recursive field (§7.2): the `t`-th child at
    /// constructor `i`, and the totality default elsewhere. It has to go
    /// through the generalization too — reading a child out of `cs` needs the
    /// *literal* arity, and outside a tag branch that arity is stuck on a
    /// variable.
    Child { i: usize, t: usize, default: Rc<Term> },
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
        container: Option<(&Expr, Rc<Term>)>,
        span: Span,
    ) -> R<Term> {
        let _ = span;
        // The tuple's terminator. Tier 1 ends with `⟨⟩ : Unit^l` — which
        // `Vec^l(T; 0) ⇝ Unit^l` makes the *zero* case of a container tail,
        // so the two are one code path (docs/container-fields.md §3.4).
        // (`Triv` carries the level since route (a) of
        // issues/unit-level-and-vec-preservation.md; a `Triv` at 0 here would
        // be exactly the defect that round closed.)
        let (mut acc, mut tail_len) = match &container {
            Some((arg, len)) => {
                let vec_ty = Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(d_ty.clone()),
                    len: Rc::clone(len),
                };
                (self.elab_check(cx, arg, &vec_ty, level)?, (**len).clone())
            }
            None => (Term::Triv { level: level.clone() }, Term::Zero),
        };
        for arg in args.iter().rev() {
            let child = self.elab_check(cx, arg, d_ty, level)?;
            let tail = tail_len.clone();
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
                    len: Rc::new(tail.shift_local(1)),
                }),
                fst: Rc::new(child),
                snd: Rc::new(acc),
            };
            tail_len = Term::Succ(Rc::new(tail_len));
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
        // Does this `match` descend on one of the enclosing declaration's own
        // parameters? If so, a self-call in an arm is the ih (§6.4).
        let dec = self.descends_on_param(cx, &scrut);
        self.build_elim_wf(
            cx,
            ind,
            scrut_ty,
            motive,
            mlvl,
            scrut,
            &Branches::Arms(arms),
            dec,
            span,
        )
    }

    /// The `t`-th child of constructor `i` as a *total* function of `⟦D⟧`
    /// (§7.2), for injectivity. `d_ty`, `default` and `scrut` are all scoped
    /// in `cx`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn child_projection(
        &self,
        cx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        level: &Level,
        i: usize,
        t: usize,
        default: Rc<Term>,
        scrut: Term,
        span: Span,
    ) -> R<Term> {
        // A constant motive at `⟦D⟧` — the projection is not an inductive
        // argument, so nothing here reads `ih`.
        self.build_elim_wf(
            cx,
            ind,
            d_ty,
            d_ty.shift_local(1),
            level.clone(),
            scrut,
            &Branches::Child { i, t, default },
            None,
            span,
        )
    }

    /// The match motive's **head**, for phase 3's "is this an equation?" test
    /// (docs/container-proofs.md §5).
    ///
    /// Structural first, exactly as `record_of_at`: a written `a = b` is
    /// already an `Id` and nothing is paid. Only a motive that arrived as a
    /// *code* — `El (Agree z)` for a named statement
    /// (`docs/types-as-expressions.md`), or `El` of a β-redex for one reached
    /// through a `Val -> Type` value (`docs/record-type-values.md` §6) —
    /// reduces, and then `whnf` is the right amount: `Id` is a weak-head
    /// normal form, so this cannot overshoot the shape it is looking for.
    ///
    /// The motive is scoped `(Γ₀, z : ⟦D⟧)`, which is not any context this
    /// walk carries, so it is rebuilt here from the two pieces `Tel` already
    /// holds. Failure is not an error: an unreducible motive is simply not an
    /// equation, which is the answer the caller wanted anyway.
    fn motive_head<'t>(&self, tel: &'t Tel<'_>) -> std::borrow::Cow<'t, Type> {
        if !matches!(&*tel.motive, Type::El { .. }) {
            return std::borrow::Cow::Borrowed(&tel.motive);
        }
        let mut gamma = tel.gamma0.clone();
        gamma.entries.push(heather_kernel::term::CtxEntry {
            ty: Rc::new(tel.d_ty.clone()),
            level: tel.level.clone(),
        });
        match heather_kernel::reduce::whnf_type_delta(
            &tel.motive,
            &gamma,
            heather_kernel::reduce::Defs::transparent(&self.delta_psi),
            self.fuel,
        ) {
            Ok(t) => std::borrow::Cow::Owned(t),
            Err(_) => std::borrow::Cow::Borrowed(&tel.motive),
        }
    }

    /// The eliminator both of the above are (§6.2): one `elim_Wf` whose step
    /// cases on the tag with `cs` and `ih` generalized in the case motive.
    /// Outside a tag branch the arity `n[a/x]` is stuck on a variable, so
    /// neither `Vec` nor `Fin` reduces and neither the children tuple nor the
    /// ih can be projected; inside branch `i` the arity is the literal `mᵢ`
    /// and everything unfolds. That is why the generalization is not
    /// stylistic.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_elim_wf(
        &self,
        cx: &Cx,
        ind: &Inductive,
        scrut_ty: &Type,
        motive: Type,
        mlvl: Level,
        scrut: Term,
        branches: &Branches,
        dec: Option<usize>,
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
            &cx3, ind, branches, &tel, dec, 0, p_motive, &plvl, var(2), 3, span,
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
        branches: &Branches,
        tel: &Tel,
        dec: Option<usize>,
        j: usize,
        motive: Type,
        plvl: &Level,
        scrut: Rc<Term>,
        d: u32,
        span: Span,
    ) -> R<Term> {
        let n = ind.ctors.len();
        if j + 1 == n {
            return self.wf_branch(cx, ind, branches, tel, dec, j, scrut, d, span);
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
            branches,
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
        // `inner = P_j[inr z']` over `(cx, y, z')` — **two** binders past `cx`,
        // not one: the `y` this branch binds *and* the inner `Case`'s own
        // motive binder. The substitution's `extra` says 2 and the injection's
        // annotations have to agree, or the spine's field types address `y`
        // where they mean an ambient variable.
        //
        // Invisible at a closed payload type (the annotations then mention no
        // ambient variable at all) and invisible with two constructors (there
        // is no inner `Case`); it took three constructors *and* an open payload
        // — `docs/testing-generated-terms.md` axis 2 — to make the index
        // escape, and then it is a kernel `LevelMismatch`, not a wrong answer.
        let inr = Term::Inr {
            lhs_level: ctor_lvl.clone(),
            rhs_level: tail_lvl.clone(),
            lhs: Rc::new(tel.spine.ctors[j].0.shift_local(d + 2)),
            rhs: Rc::new(tel.spine.tails[j].0.shift_local(d + 2)),
            val: Rc::new(Term::Var(LocalVar(0))),
        };
        let inner = motive.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(inr)));
        let case_r = self.wf_case_tree(
            &rcx,
            ind,
            branches,
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
        branches: &Branches,
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
        let ctor_ty_here = tel.spine.ctors[i].0.shift_local(d_body);
        let value_here = Rc::new(value.shift_local(2));
        // This branch's arity. Without a container it is the literal `m`;
        // with one it is `Succ^m(len)` for `len` projected out of the label,
        // which is the *same* term the `Wf`'s arity computes here
        // (docs/container-fields.md §3.3). `Succ`-headed either way, which is
        // what lets `Vec` unfold `m` times and `Fin` admit the `m` literal
        // indices below.
        let container_len = match ctor.container() {
            Some((_, p)) => {
                // `bcx`, not `cx`: both arguments have been shifted by
                // `d_body`, so they live under the two binders just pushed,
                // and `projection` substitutes with the identity of the
                // context it is *given*. Passing `cx` was two entries short.
                //
                // Invisible at a closed instantiation — the constructor
                // encoding's Σ tail then mentions no ambient variable at all,
                // so nothing ever addressed the missing entries. It took a
                // container field at an *open* element type
                // (`Rose<A>`) to make the index escape, which is axis 2 of
                // docs/testing-generated-terms.md, again.
                let (len, _, _) =
                    self.projection(&bcx, &ctor_ty_here, &value_here, p, span)?;
                Some(len)
            }
            None => None,
        };
        let base = match &container_len {
            Some(l) => (**l).clone(),
            None => Term::Zero,
        };
        let len = Rc::new(succ_n(m, &base));

        // The `t`-th child, `nth^l(⟦D⟧; m; cs'; ι_t)`. At a literal `m` this
        // β-reduces to the projections of `cs'` even though `cs'` is a
        // variable, which is what makes an arm binder behave like a field.
        let child =
            |t: usize| Rc::new(nth_child(&tel.level, &d_ty_here, m, t, Rc::clone(&cs_var), &base));

        let body = match branches {
            Branches::Custom(f) => f(&bcx, tel, i, &value_here, d_body, &body_ty)?,
            // §7.2: no binders, no guard — just the child, or the default at
            // every other constructor.
            Branches::Child { i: ci, t, default } => {
                if i == *ci {
                    nth_child(&tel.level, &d_ty_here, m, *t, cs_var, &base)
                } else {
                    default.shift_local(d_body)
                }
            }
            Branches::Arms(arms) => {
                let arm = arms[i];
                let mut acx = bcx.clone();
                let ctor_ty = ctor_ty_here.clone();
                let mut children = Vec::with_capacity(m);
                let mut container_ih: Option<crate::ContainerIh> = None;
                let (mut payload_k, mut rec_t) = (0usize, 0usize);
                for (k, name) in arm.binders.iter().enumerate() {
                    // The container binder is the *tail* of the children
                    // tuple — one `snd` per preceding plain child, no `nth`
                    // and no index arithmetic (docs/container-fields.md §3.5).
                    if let FieldKind::Container { .. } = ctor.kind[k] {
                        let tail_len = container_len
                            .clone()
                            .expect("a container field has a length");
                        let mut term = Rc::clone(&cs_var);
                        let mut left = m;
                        while left > 0 {
                            left -= 1;
                            let mut rest = (*tail_len).clone();
                            for _ in 0..left {
                                rest = Term::Succ(Rc::new(rest));
                            }
                            term = Rc::new(Term::Snd {
                                fst_level: tel.level.clone(),
                                snd_level: tel.level.clone(),
                                fst_ty: Rc::clone(&d_ty_here),
                                snd_ty: Rc::new(Type::Vec {
                                    level: tel.level.clone(),
                                    elem: Rc::new(tel.d_ty.shift_local(d_body + 1)),
                                    len: Rc::new(rest.shift_local(1)),
                                }),
                                pair: term,
                            });
                        }
                        acx.aliases.push(Rc::new(Alias {
                            name: name.clone(),
                            depth: acx.names.len(),
                            term: Rc::clone(&term),
                            ty: Type::Vec {
                                level: tel.level.clone(),
                                elem: Rc::clone(&d_ty_here),
                                len: Rc::clone(&tail_len),
                            },
                            level: tel.level.clone(),
                        }));
                        // What a self-call over this binder needs (§4.2). The
                        // motive is strengthened here rather than at the call:
                        // a container maps to a *vector* of results, which
                        // only types when the result is independent of the
                        // child (§4.3).
                        let result = crate::vec::strengthen(&tel.motive, tel.gamma0)
                            .map(|t| t.shift_local(d_body));
                        // Phase 3 (docs/container-proofs.md §5): a dependent
                        // motive that is an equation at a `z`-independent type
                        // still relates the children pointwise. The endpoints
                        // are wrapped as `λ(z : ⟦D⟧). …` so the call site can
                        // shift them like any other term.
                        //
                        // The equation is read through [`Self::motive_head`]:
                        // a *named* statement (`fn Agree(r: Rose) -> Type
                        // { … = … }`) arrives as `El` of a call, and the `Id`
                        // is one δ/β step below it
                        // (docs/record-type-values.md §6).
                        let motive = self.motive_head(tel);
                        let eq = match (&result, &*motive) {
                            (None, Type::Id { level, ty, lhs, rhs }) => {
                                crate::vec::strengthen(ty, tel.gamma0).map(|a| {
                                    let sigma = crate::embed(tel.gamma0, d_body + 1)
                                        .extended(Rc::new(Term::Var(LocalVar(0))));
                                    let lam = |t: &Rc<Term>| {
                                        Rc::new(Term::Lam {
                                            dom_level: tel.level.clone(),
                                            cod_level: level.clone(),
                                            dom: Rc::clone(&d_ty_here),
                                            body: Rc::new(t.apply_local(&sigma)),
                                        })
                                    };
                                    crate::EqSplit {
                                        level: level.clone(),
                                        ty: a.shift_local(d_body),
                                        lhs: lam(lhs),
                                        rhs: lam(rhs),
                                    }
                                })
                            }
                            _ => None,
                        };
                        container_ih = Some(crate::ContainerIh {
                            term,
                            len: tail_len,
                            ih: Rc::new(Term::Var(LocalVar(0))),
                            plain: m,
                            result,
                            eq,
                            // `ih_dom` is scoped where `#ih` is *pushed*, one
                            // binder before the body: `tel.at` builds it at
                            // `d + 1` and the body sits at `d + 2`.
                            ih_ty: ih_dom.shift_local(1),
                            elem: (*d_ty_here).clone(),
                            level: tel.level.clone(),
                            mlvl: tel.mlvl.clone(),
                        });
                        continue;
                    }
                    if ctor.kind[k] == FieldKind::Plain {
                        let c = child(rec_t);
                        // The ih at this index, and the type it lands at: the
                        // eliminator's `cod` binds `i`, so it is
                        // `M[nth(…; i)/z]` one binder deeper, and
                        // instantiating it at `ι_t` gives `M[child/z]` —
                        // which is the child term verbatim.
                        // Everything inside `cod` sits one binder deeper (the
                        // eliminator's `i`), *including the length* — which is
                        // a closed literal without a container and a projection
                        // out of the label with one, so a missing shift here is
                        // invisible until a container constructor carries a
                        // plain child through a proof.
                        let cod = tel.motive.apply_local(
                            &embed(tel.gamma0, d_body + 1).extended(Rc::new(nth(
                                &tel.level,
                                &Rc::new(tel.d_ty.shift_local(d_body + 1)),
                                &Rc::new(len.shift_local(1)),
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
                            arg: Rc::new(fin_index(rec_t, m, &base)),
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
                // A self-call in this arm is the ih (§6.4) — but only if the
                // `match` descends on one of the declaration's own
                // parameters. If it does not, an enclosing arm's guard, if
                // any, still stands.
                acx.guard = dec
                    .map(|dec| {
                        Rc::new(Guard {
                            dec,
                            kind: GuardKind::Wf {
                                depth: acx.names.len(),
                                children,
                                container: container_ih.clone(),
                            },
                            rebind: None,
                        })
                    })
                    .or_else(|| cx.guard.clone());
                self.elab_check(&acx, &arm.body, &body_ty, &tel.mlvl)?
            }
        };
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

impl Elaborator {
    // -- no-confusion (§7) --------------------------------------------------

    /// `elim_Wf` at a **constant** motive, with a constant-motive case tree on
    /// the tag as its step (§7). Both halves of no-confusion are this: the
    /// disjointness predicate is it at the motive `Ty 0`, and a field
    /// projection is it at the motive "that field's type". Neither is an
    /// inductive argument, so the step ignores `ih` entirely.
    ///
    /// Scoping follows tier 0 §6's convention, which is worth stating because
    /// it is mixed on purpose: `spine`, `d_ty` and the `ConstBody` payloads
    /// are scoped in the *base* context the caller read them back in, `d0`
    /// counts the binders pushed since (2, inside a `J` motive), and `motive`
    /// and `scrut` are scoped in `cx` — here and now.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn const_elim_wf(
        &self,
        cx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        spine: &Spine,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &ConstBody,
        d0: u32,
        span: Span,
    ) -> R<Term> {
        let Type::Wf { level, shape, arity } = d_ty.shift_local(d0) else {
            return err("internal: a recursive declaration did not lower to a `Wf`", span);
        };
        // The motive binds `z` and ignores it; the telescope needs it anyway,
        // since `ih_ty` and `step_ty` are stated in terms of it.
        let under_z = Rc::new(motive.shift_local(1));
        let (cs_ty, ih_ty, _) =
            wf_step_telescope(&cx.gamma, &level, mlvl, &shape, &arity, &under_z);
        let mut cx3 = cx.clone();
        cx3.push("#a".into(), (*shape).clone(), level.clone());
        cx3.push("#cs".into(), cs_ty, level.clone());
        cx3.push("#ih".into(), ih_ty, mlvl.clone());
        let step = self.const_case_tree(
            &cx3,
            spine,
            ind.ctors.len(),
            &motive.shift_local(3),
            mlvl,
            Rc::new(Term::Var(LocalVar(2))),
            body,
            0,
            d0 + 3,
            span,
        )?;
        Ok(Term::ElimWf {
            level,
            motive_level: mlvl.clone(),
            shape,
            arity,
            motive: under_z,
            step: Rc::new(step),
            scrut,
        })
    }
}

/// `nth^l(⟦D⟧; m; cs; ι_t)` — the `t`-th of `m` children of `cs` (§6.3).
/// Shared by the `match` arms, which bind it as an alias, and by
/// injectivity, which projects with it.
/// The `t`-th plain child, out of a children tuple whose length is
/// `Succ^m(base)`.
///
/// `base` is `Zero` for a constructor with no container field — recovering
/// tier 1's literal `m` exactly — and the container's length term otherwise
/// (docs/container-fields.md §3.3). Either way the length is `Succ`-headed
/// `m` times, which is all `nth` and `Fin` need in order to reduce down to
/// the `t`-th projection.
pub(crate) fn nth_child(
    level: &Level,
    d_ty: &Rc<Type>,
    m: usize,
    t: usize,
    cs: Rc<Term>,
    base: &Term,
) -> Term {
    nth(
        level,
        d_ty,
        &Rc::new(succ_n(m, base)),
        cs,
        Rc::new(fin_index(t, m, base)),
    )
}

/// `Succ^k(base)`.
fn succ_n(k: usize, base: &Term) -> Term {
    let mut acc = base.clone();
    for _ in 0..k {
        acc = Term::Succ(Rc::new(acc));
    }
    acc
}

/// The index `t` of `Fin(Succ^m(base))`: `inr^t (inl ⟨⟩)` (§6.3). Each tail is
/// annotated with `Fin` itself rather than its unfolded sum — `Fin(S k) ⇝
/// Unit⁰ + Fin(k)`, so the kernel converts the two, and the folded form is
/// what a goal reads back as.
pub(crate) fn fin_index(t: usize, m: usize, base: &Term) -> Term {
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let fin = |k: usize| Rc::new(Type::Fin { len: Rc::new(succ_n(k, base)) });
    let mut v = Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: unit(),
        rhs: fin(m - t - 1),
        val: Rc::new(Term::Triv { level: Level::Zero }),
    };
    for k in (0..t).rev() {
        v = Term::Inr {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: fin(m - k - 1),
            val: Rc::new(v),
        };
    }
    v
}
