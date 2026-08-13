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
    /// `⟦D⟧` **inline** — the `Type::Wf` itself, scoped in `gamma0`. This is
    /// the structural-read copy: `spine` reads the sum-of-Σs out of it and
    /// [`Elaborator::motive_head`] pushes it as a context entry. Never use it
    /// for an emitted annotation; that is [`Tel::d_emit`].
    pub d_ty: &'a Type,
    /// `⟦D⟧` as it is **written into emitted terms**: `El (D#tycode^δ)` where
    /// the declaration has a registered code, and the inline `Type::Wf`
    /// otherwise (`docs/family-type-code-defs-design.md`, 2026-08-12
    /// extension).
    ///
    /// The two are convertible by construction — the code is `code_of` of
    /// *this* type and [`Elaborator::ty_type_ref`] hands it out only after
    /// checking that — so every use below is a spelling choice and nothing
    /// else. The split is [[wf-field-conversion-cost]]'s whole fix: a tier-1
    /// `match` writes `⟦D⟧` out ~21 times per arm, and each copy carried every
    /// field type verbatim.
    pub d_emit: Type,
    /// `l`: the declaration's level, which is also its shape's.
    pub level: Level,
    /// `l'`: the motive's level.
    pub mlvl: Level,
    /// `M`, over `(gamma0, z : ⟦D⟧)`.
    pub motive: Rc<Type>,
    cs_ty: Type,
    ih_ty: Type,
    step_ty: Type,
    /// The declaration's tag spine, scoped in `gamma0`. The **structural-read**
    /// copy: `projection` reads a constructor's Σ components out of it and
    /// `build_fields` checks against them.
    pub spine: Spine,
    /// The same spine as it is **written into emitted terms**: every component
    /// that is a registered declaration's lowering replaced by its reference
    /// (`Elaborator::respell_spine`, the emission copy `build_ctor` has taken
    /// at constructor values since the component-respell round).
    ///
    /// The match lowering was left out of that round by its charter, and this
    /// round's counters are why it is in now: a `match` on a declaration whose
    /// constructors carry a `Wf`-lowered field wrote that field type verbatim
    /// into every `Case`, every `Inr` and every injection — Θ(arms²) copies of
    /// `⟦T⟧`, and most of a lowered body's node mass, measured
    /// (`docs/wf-shape-code-design.md` §3.4).
    pub spine_emit: Spine,
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
    /// `d_ty` is `⟦D⟧` (the whole `Wf`), scoped in `cx`; `tag` is the
    /// declaration's, used to look up its code.
    ///
    /// The two spellings are split here for the reason §3.1 gives: the
    /// children are **checked** against `⟦D⟧`, and a checking position is a
    /// structural read (`Cons(x, Cons(y, Nil))` resolves its inner
    /// constructor against the expected type), so `elab_check` keeps the
    /// inline `Wf`; the `Vec`/`Pair` annotations the tuple carries are pure
    /// emission and take the reference.
    pub(crate) fn build_children(
        &self,
        cx: &Cx,
        tag: u32,
        d_ty: &Type,
        level: &Level,
        args: &[Expr],
        container: Option<(&Expr, Rc<Term>)>,
        span: Span,
    ) -> R<Term> {
        let _ = span;
        let emit = self.ty_type_ref(cx, tag, d_ty).unwrap_or_else(|| d_ty.clone());
        // The tuple's terminator. Tier 1 ends with `⟨⟩ : Unit^l` — which
        // `Vec^l(T; 0) ⇝ Unit^l` makes the *zero* case of a container tail,
        // so the two are one code path (docs/container-fields.md §3.4).
        // (`Triv` carries the level since route (a) of
        // issues/unit-level-and-vec-preservation.md; a `Triv` at 0 here would
        // be exactly the defect that round closed.)
        let (mut acc, mut tail_len) = match &container {
            Some((arg, len)) => {
                // A **checking** position (the container argument is written
                // at the surface), so the element type stays inline: checking
                // a vector literal checks each element against it, and that is
                // a structural read.
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
                fst_ty: Rc::new(emit.clone()),
                // `Vec(T; S k) ⇝ Σ(_ : T). Vec(T; k)` and a Σ's second
                // component *binds*, so the tail type sits one level deeper
                // than the ambient (§5).
                snd_ty: Rc::new(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(emit.shift_local(1)),
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
        // argument, so nothing here reads `ih`. The motive is an emitted
        // annotation (it lands in the `ElimWf`'s motive slot), so it takes the
        // reference where one exists; `d_ty` itself stays inline because
        // `build_elim_wf` destructures it.
        let motive = self
            .ty_type_ref(cx, ind.tag, d_ty)
            .unwrap_or_else(|| d_ty.clone())
            .shift_local(1);
        self.build_elim_wf(
            cx,
            ind,
            d_ty,
            motive,
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
        // The *motive* is `⟦D'⟧` for whatever the arms return, and it is the
        // single largest occurrence site of all: it is instantiated once per
        // `Case` node of the tag tree, twice more per branch (the two λ
        // domains), and twice again in `apply_cs_ih`. Respelling it needs no
        // tag from the caller — `tag_of` reads it out of the type, and
        // `ty_type_ref` declines unless the type *is* that declaration's
        // registered lowering.
        //
        // The `shift_local(1)` is not cosmetic: the motive is scoped over
        // `(Γ₀, z : ⟦D⟧)`, one binder past `cx`, and `gen_ref` stamps the
        // reference's substitution tail with `cx`'s own length. Without it the
        // kernel answers `SubstMismatch` at every `match` — which is the good
        // failure mode, but a failure mode.
        //
        // **Component-wise**, not whole-type only: a `fn` returning a function
        // (`pick_arm(arms: Ir) -> Nat -> Ir`) has the motive `Π(Nat). ⟦Ir⟧`,
        // which is not itself any declaration's lowering, and the whole-type
        // respell declined on it — leaving the single largest type in the file
        // written out at every instantiation of the motive. `depth` is 1, the
        // motive's own `z` binder: `respell_ty_deep` shifts the *references* by
        // it rather than the result, which is why this is not the
        // `shift_local(1)` the whole-type version needed.
        let motive = Rc::new(self.respell_ty_deep(cx, &motive, 1).unwrap_or(motive));
        // The one lookup: `El (D#tycode^δ)` if this declaration has a code and
        // `scrut_ty` *is* the lowering it was minted from, the inline type
        // otherwise. Everything emitted below reads `tel.d_emit`; the
        // structural reads a line down read `scrut_ty`.
        let d_emit = self
            .ty_type_ref(cx, ind.tag, scrut_ty)
            .unwrap_or_else(|| scrut_ty.clone());
        // The `Wf` slot pair as it is **written into emitted terms**
        // (`docs/wf-shape-code-design.md` §3.2): `El (D#shape^δ)` and
        // `app(D#arity^δ; x₀)` where this declaration has the pair registered,
        // the inline slots otherwise. The structural reads a few lines down —
        // `cx3`'s `#a` entry, `spine` — take `shape`/`arity` themselves, per
        // §4's line.
        let (shape_e, arity_e) = match self.wf_slot_refs(cx, shape, arity) {
            Some((s, a)) => (Rc::new(s), Rc::new(a)),
            None => (Rc::clone(shape), Rc::clone(arity)),
        };
        let (cs_ty, ih_ty, step_ty) = heather_kernel::term::wf_step_telescope_at(
            &cx.gamma, level, &mlvl, shape, arity, &motive, &d_emit,
            Some((&shape_e, &arity_e)),
        );
        let spine = self.spine(scrut_ty, level, ind.ctors.len(), span)?;
        let spine_emit = self.respell_spine(cx, &spine);
        let tel = Tel {
            gamma0: &cx.gamma,
            d_ty: scrut_ty,
            d_emit,
            level: level.clone(),
            mlvl: mlvl.clone(),
            motive: Rc::clone(&motive),
            spine,
            spine_emit,
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
            shape: shape_e,
            arity: arity_e,
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
        // Emitted annotations (this `Case`'s two component types, the `Inr`
        // below) take the emission spine; the *binder* types pushed into the
        // elaborator's own context stay inline, so every structural read
        // inside the branch still sees `⟦T⟧` itself (§4's line).
        let ctor_ty = Rc::new(tel.spine_emit.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(tel.spine_emit.tails[j].0.shift_local(d));
        let ctor_ty_in = tel.spine.ctors[j].0.shift_local(d);
        let tail_ty_in = tel.spine.tails[j].0.shift_local(d);
        // case_l: binder `x : ⟦c_j⟧`, body at `P_j[inl x/z]`.
        let mut lcx = cx.clone();
        lcx.push("#scrut".into(), ctor_ty_in, ctor_lvl.clone());
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
        rcx.push("#rest".into(), tail_ty_in, tail_lvl.clone());
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
            lhs: Rc::new(tel.spine_emit.ctors[j].0.shift_local(d + 2)),
            rhs: Rc::new(tel.spine_emit.tails[j].0.shift_local(d + 2)),
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
        // The injection's own `Inl`/`Inr` annotations are emitted, so they take
        // the emission spine — the same choice `build_ctor` makes at a value.
        let inj = Rc::new(inject(&tel.spine_emit, i, ind.ctors.len(), (*value).clone(), d));
        let (cs_dom, ih_dom, body_ty) = tel.at(&inj, d);

        let mut bcx = cx.clone();
        bcx.push("#cs".into(), cs_dom.clone(), tel.level.clone());
        bcx.push("#ih".into(), ih_dom.clone(), tel.mlvl.clone());
        // In the body: cs' = Var 1, ih' = Var 0, and everything scoped in
        // `cx` has moved two binders out.
        let cs_var = Rc::new(Term::Var(LocalVar(1)));
        let d_body = d + 2;
        // Emission spelling for every annotation this branch writes; the
        // inline one only for the surface binders' *alias types*, which the
        // elaborator reads structurally (a nested `match` on a child binder,
        // `record_of`, `projection`) — §3.1's line, held per reader.
        let d_ty_here = Rc::new(tel.d_emit.shift_local(d_body));
        let d_inline_here = tel.d_ty.shift_local(d_body);
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
                for (k, name) in arm.binders.iter().map(|p| p.name().to_string()).enumerate() {
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
                                    elem: Rc::new(tel.d_emit.shift_local(d_body + 1)),
                                    len: Rc::new(rest.shift_local(1)),
                                }),
                                pair: term,
                            });
                        }
                        acx.aliases.push(Rc::new(Alias { skel: None,
                            name: name.clone(),
                            depth: acx.names.len(),
                            term: Rc::clone(&term),
                            ty: Type::Vec {
                                level: tel.level.clone(),
                                elem: Rc::new(d_inline_here.clone()),
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
                                &Rc::new(tel.d_emit.shift_local(d_body + 1)),
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
                        acx.aliases.push(Rc::new(Alias { skel: None,
                            name: name.clone(),
                            depth: acx.names.len(),
                            term: Rc::clone(&c),
                            ty: d_inline_here.clone(),
                            level: tel.level.clone(),
                        }));
                        children.push((c, ih_at, ih_ty, tel.mlvl.clone()));
                        rec_t += 1;
                    } else {
                        let (proj, ty, level) =
                            self.projection(&acx, &ctor_ty, &value_here, payload_k, span)?;
                        acx.aliases.push(Rc::new(Alias { skel: None,
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

// ---------------------------------------------------------------------------

#[cfg(test)]
mod tycode {
    //! The tier-1 `D#tycode` spelling
    //! (`docs/family-type-code-defs-design.md`, 2026-08-12 extension;
    //! `issues/wf-field-conversion-cost.md`).
    //!
    //! Two obligations, and they are different in kind. The **emission** side
    //! is checked by elaborating real source: a wrong spelling in an
    //! annotation slot is a kernel rejection at the declaration's own gate, so
    //! "it elaborates" *is* the assertion, and the four axes of
    //! `docs/testing-generated-terms.md` are what make that assertion cover
    //! anything (a literal and a neutral scrutinee, an open element type, a
    //! checking position, a negative control). The **recognition** side is
    //! checked structurally, with `forded.rs mod fingerprint`'s look-alike
    //! discipline: a reference must stand for the declaration it names and for
    //! nothing else, in both directions.

    use super::*;
    use crate::gendefs::GenDef;
    use heather_kernel::term::{
        CtxBase, GlobalBinding, GlobalVar, LocalSubst, SubstTail,
    };

    const SPAN: Span = Span { start: 0, end: 0 };

    /// Two tier-1 declarations that are structurally identical apart from
    /// their nominal tags (the look-alike pair, `mod fingerprint`'s
    /// construction), one non-recursive declaration — whose lowering is a bare
    /// sum-of-Σs and which gets a code all the same — and one *parameterized*
    /// declaration, which must not.
    const SRC: &str = "
inductive T { T0, T1(x: Nat, r: T), T2(y: Nat, r: T) }
inductive U { U0, U1(x: Nat, r: U), U2(y: Nat, r: U) }
inductive Flat { FA, FB(n: Nat), FC(m: Nat, k: Nat) }
inductive Box<A> { BNil, BCons(a: A, r: Box<A>) }
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
                    .inductives
                    .get(&crate::names::qkey("main", name))
                    .unwrap_or_else(|| panic!("`{name}` was declared")),
            )
        }
        fn lowered(&self, name: &str) -> (Type, Level) {
            self.el
                .lower_instance(&self.cx, &self.ind(name), &[], &[], SPAN)
                .expect("the declaration lowers")
        }
    }

    // -- registration boundary ----------------------------------------------

    #[test]
    fn a_closed_declaration_gets_a_code_and_a_parameterized_one_does_not() {
        let e = env();
        for name in ["T", "U", "Flat"] {
            let tag = e.ind(name).tag;
            assert!(
                e.el.gen_ref(&e.cx, GenDef::TyCode(tag)).is_some(),
                "`{name}` should have a `#tycode`"
            );
        }
        // §14.12's boundary, verbatim: `⟦Box<A>⟧` is monomorphized per
        // instantiation, so there is no one closed type to name.
        assert!(e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind("Box").tag)).is_none());
    }

    #[test]
    fn the_reference_is_el_of_the_declarations_own_code() {
        let e = env();
        let (t_ty, l) = e.lowered("T");
        let r = e.el.respell_ty(&e.cx, &t_ty).expect("T's lowering respells");
        let Type::El { level, tm } = &r else { panic!("the spelling is `El` of a code") };
        assert_eq!(*level, l);
        assert!(e.el.is_gen_ref(tm, GenDef::TyCode(e.ind("T").tag)));
        // Idempotent: `tag_of` goes through `decoded`, which leaves an `El` of
        // a neutral code alone, so a reference does not respell again.
        assert!(e.el.respell_ty(&e.cx, &r).is_none());
        // Conservativity (design §1.3): δ + decode of the reference is the
        // inline type, so the two convert.
        assert!(e.el.conv_types(&e.cx, &r, &t_ty, &l));
        assert!(e.el.conv_types(&e.cx, &t_ty, &r, &l));
    }

    // -- the look-alike negatives (design §4, §9) ---------------------------

    #[test]
    fn a_type_the_tag_read_routes_to_but_which_is_not_the_lowering_declines() {
        let e = env();
        // This is the guard the registry's inline copy exists for. `tag_of`
        // walks a `Sum` into its left summand to find a tag, so a type built
        // out of **T's first constructor** and something else names `T` — and
        // it is not `⟦T⟧`. Without the structural comparison the emission
        // sites would spell it `El (T#tycode^δ)`, which decodes to a
        // different type: not a rejection, a *wrong annotation*, which is the
        // failure mode this module's doctrine exists to prevent.
        let (t_ty, l) = e.lowered("T");
        let Type::Wf { shape, .. } = &t_ty else { panic!("T is recursive") };
        let Type::Sum { lhs, lhs_level, .. } = &**shape else {
            panic!("a tier-1 shape is a sum-of-Σs")
        };
        let forgery = Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: Level::Zero,
            lhs: Rc::clone(lhs),
            rhs: Rc::new(Type::Unit { level: Level::Zero }),
        };
        assert_eq!(e.el.tag_of(&forgery).map(|i| i.tag), Some(e.ind("T").tag));
        assert!(e.el.respell_ty(&e.cx, &forgery).is_none());
        // …and the same read keyed by hand at the tag declines too, which is
        // the property `respell_ty` inherits rather than adds.
        assert!(e.el.ty_type_ref(&e.cx, e.ind("T").tag, &forgery).is_none());
        let _ = l;
    }

    #[test]
    fn el_of_the_wrong_declarations_code_is_not_this_declaration() {
        let e = env();
        // `U`'s code — a real registered definition of a real declaration
        // that differs from `T` only in its tags — offered where `T`'s
        // lowering is expected.
        let (_, l) = e.lowered("T");
        let u_code = e
            .el
            .gen_ref(&e.cx, GenDef::TyCode(e.ind("U").tag))
            .expect("U has a code");
        let forged = Type::El { level: l, tm: Rc::new(u_code) };
        // Neither by tag…
        assert!(e.el.ty_type_ref(&e.cx, e.ind("T").tag, &forged).is_none());
        // …nor by the structural read, which does not follow a neutral code.
        assert!(e.el.respell_ty(&e.cx, &forged).is_none());
    }

    #[test]
    fn el_of_a_byte_identical_user_global_is_not_the_declaration() {
        let mut e = env();
        // Identity is the Ψ index, not the body: a bodied global whose
        // statement, layer and body are byte-identical to `T#tycode`'s, pushed
        // outside the registry the way a user `fn` is, resolves to no
        // `GenDef`.
        let (t_ty, l) = e.lowered("T");
        let code = crate::code::code_of(&t_ty).expect("T's lowering has a code");
        e.el.psi.push(GlobalBinding::defined_tm(
            LocalCtx::nil(),
            heather_kernel::layer::Layer::Code,
            Rc::new(Type::Ty(l.clone())),
            Level::succ(l.clone()),
            Rc::new(code),
        ));
        e.el.refresh_delta_psi();
        let dup = Term::GlobalTm {
            var: GlobalVar(e.el.goal_base),
            subst: LocalSubst {
                tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
                terms: vec![],
            },
        };
        assert!(e.el.gen_def_of(GlobalVar(e.el.goal_base)).is_none());
        let forged = Type::El { level: l, tm: Rc::new(dup) };
        assert!(e.el.ty_type_ref(&e.cx, e.ind("T").tag, &forged).is_none());
        assert!(e.el.respell_ty(&e.cx, &forged).is_none());
    }

    // -- emission: the four axes --------------------------------------------

    /// A `match` really does emit the reference — otherwise every "it
    /// elaborates" below would be vacuous.
    #[test]
    fn a_tier1_match_emits_the_reference_in_its_motive() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el
            .elab_source("fn drop2(t: T) -> T { match t { T0 => T0, T1(x, r) => r, T2(y, r) => r } }")
            .expect("elaborates");
        let GlobalBinding::Tm { body: Some(body), .. } =
            e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` is a bodied term binding")
        };
        let Term::Lam { body, .. } = &**body else { panic!("one parameter, one λ") };
        let Term::ElimWf { motive, .. } = &**body else { panic!("tier 1 lowers to `elim_Wf`") };
        let Type::El { tm, .. } = &**motive else {
            panic!("the motive is the reference, not the inline `Wf`")
        };
        // `GlobalVar` counts from the end of Ψ, so the reference the body
        // carries was minted against the Ψ *before* the declaration's own
        // binding; re-key it into today's Ψ before asking the registry, or the
        // nominal test silently reads one binding over.
        let grew = (e.el.psi.bindings.len() - before) as u32;
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::TyCode(e.ind("T").tag)));
    }

    /// Axes 1–4 on the tier-1 path, one source: a **neutral** scrutinee (the
    /// parameter `t`) and a **literal** one (`T1(1, T0)`), a **checking**
    /// position (`h`'s annotated result and the `refl`), and the computation
    /// pinned rather than merely built.
    #[test]
    fn the_four_axes_on_a_recursive_declaration() {
        let mut e = env();
        e.el
            .elab_source(
                "
fn depth(t: T) -> Nat { match t { T0 => 0, T1(x, r) => Succ(depth(r)), T2(y, r) => Succ(depth(r)) } }
fn peel(t: T) -> T { match t { T0 => T0, T1(x, r) => r, T2(y, r) => T1(y, r) } }
fn lit() -> T { match T1(1, T0) { T0 => T0, T1(x, r) => r, T2(y, r) => r } }
theorem lit_is_t0(): lit() = T0 { refl }
theorem peel_computes(): peel(T2(3, T1(1, T0))) = T1(3, T1(1, T0)) { refl }
theorem depth_computes(): depth(T1(1, T2(2, T0))) = 2 { refl }
",
            )
            .expect("the reference-spelled annotations check and compute");
    }

    /// Axis 2, the one that hid three of the five live defects: an **open**
    /// element type. `Box<A>` has no code (§14.12), so this is also the
    /// coexistence control — a parameterized declaration's `match` still
    /// elaborates with everything inline, beside declarations that do have
    /// codes.
    #[test]
    fn a_parameterized_declaration_still_lowers_inline() {
        let mut e = env();
        e.el
            .elab_source(
                "
fn blen<A>(b: Box<A>) -> Nat { match b { BNil => 0, BCons(a, r) => Succ(blen(r)) } }
fn bnat(b: Box<Nat>) -> Nat { match b { BNil => 7, BCons(a, r) => a } }
theorem bnat_computes(): bnat(BCons(4, BNil)) = 4 { refl }
",
            )
            .expect("a parameterized declaration keeps its inline lowering");
        assert!(e.el.gen_ref(&e.cx, GenDef::TyCode(e.ind("Box").tag)).is_none());
    }

    /// The tier-0 twin: a **non-recursive** declaration's `match` goes through
    /// `case_tree`, whose one Θ(arms)-copied whole type is the motive. Both
    /// scrutinee kinds, and a mixed pair — a recursive scrutinee at a
    /// non-recursive motive, which is the shape (`Ir -> CertOut`) that made
    /// the non-recursive registration worth having.
    #[test]
    fn the_tier0_motive_respell_checks_and_computes() {
        let mut e = env();
        e.el
            .elab_source(
                "
fn fnext(f: Flat) -> Flat { match f { FA => FB(1), FB(n) => FC(n, n), FC(m, k) => FA } }
fn tflat(t: T) -> Flat { match t { T0 => FA, T1(x, r) => FB(x), T2(y, r) => FC(y, y) } }
theorem fnext_computes(): fnext(FB(2)) = FC(2, 2) { refl }
theorem tflat_computes(): tflat(T1(5, T0)) = FB(5) { refl }
theorem tflat_neutral(): tflat(T0) = FA { refl }
",
            )
            .expect("the tier-0 motive respell checks and computes");
    }

    /// The Ψ-numbering regression this round found: a `meta fn`'s `Ctx`
    /// binders extend Ψ, and `gen_ref` used not to offset by them the way
    /// `resolve` always has. Nothing emitted a generated-definition reference
    /// from inside a meta body until the motive respell did, and the symptom
    /// was `WrongGlobalBinding` naming the context binder.
    #[test]
    fn a_reference_emitted_inside_a_meta_body_is_numbered_past_the_ctx_binder() {
        let mut e = env();
        e.el
            .elab_source(
                "meta fn mwalk(g: Ctx, t: T) -> Nat \
                 { match t { T0 => 0, T1(x, r) => 1, T2(y, r) => 2 } }",
            )
            .expect("a meta body's `match` on a coded declaration checks at layer m");
    }

    // -- the component respell (docs/annotation-component-respell-design.md) --

    /// `respell_ty_deep` replaces exactly the components that are registered
    /// lowerings, at the right depths: a `Π` over two coded declarations
    /// respells both sides, the binder-crossing side with its substitution
    /// tail one longer.
    #[test]
    fn the_deep_respell_replaces_components_at_their_depths() {
        let e = env();
        let (t_ty, tl) = e.lowered("T");
        let (f_ty, fl) = e.lowered("Flat");
        let pi = Type::Pi {
            dom_level: tl.clone(),
            cod_level: fl.clone(),
            dom: Rc::new(t_ty.clone()),
            cod: Rc::new(f_ty.clone()),
        };
        let r = e.el.respell_ty_deep(&e.cx, &pi, 0).expect("both components respell");
        let Type::Pi { dom, cod, .. } = &r else { panic!("the Π shell survives") };
        let Type::El { tm: dtm, .. } = &**dom else { panic!("dom is a reference") };
        let Type::El { tm: ctm, .. } = &**cod else { panic!("cod is a reference") };
        assert!(e.el.is_gen_ref(dtm, GenDef::TyCode(e.ind("T").tag)));
        assert!(e.el.is_gen_ref(ctm, GenDef::TyCode(e.ind("Flat").tag)));
        // The respelled Π still converts with the inline one — component
        // respelling is a spelling change, both directions.
        let lvl = Level::max(tl, fl);
        assert!(e.el.conv_types(&e.cx, &r, &pi, &lvl));
        assert!(e.el.conv_types(&e.cx, &pi, &r, &lvl));
        // Idempotent, like the whole-type respell.
        assert!(e.el.respell_ty_deep(&e.cx, &r, 0).is_none());
        // And a type with no registered component answers `None` — the
        // caller keeps its original.
        assert!(e.el.respell_ty_deep(&e.cx, &Type::Nat, 0).is_none());
    }

    /// The statement-side respell, pinned structurally rather than assumed: a
    /// declared `fn`'s Ψ statement carries the reference in its `Π` dom, and
    /// a *call* to it then emits an `App` whose `dom` annotation is that
    /// reference — the cascade that makes per-application respelling
    /// unnecessary (design §2.1).
    #[test]
    fn a_statement_respells_and_calls_inherit_it() {
        let mut e = env();
        e.el.elab_source("fn tid(t: T) -> T { t }").expect("elaborates");
        let GlobalBinding::Tm { ty, .. } = e.el.psi.bindings.last().expect("a binding") else {
            panic!("a `fn` is a term binding")
        };
        let Type::Pi { dom, cod, .. } = &**ty else { panic!("one parameter, one Π") };
        let Type::El { tm, .. } = &**dom else {
            panic!("the statement's dom is the reference, not the inline `Wf`")
        };
        assert!(e.el.is_gen_ref(&tm.shift_global(1), GenDef::TyCode(e.ind("T").tag)));
        let Type::El { .. } = &**cod else { panic!("the result respells too") };
        // The cascade: a later declaration's call reads its `App` annotations
        // off that statement.
        let before = e.el.psi.bindings.len();
        e.el.elab_source("fn call_it(t: T) -> T { tid(t) }").expect("elaborates");
        let GlobalBinding::Tm { body: Some(body), .. } =
            e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Lam { body, .. } = &**body else { panic!("one λ") };
        let Term::App { dom, .. } = &**body else { panic!("the body is the call") };
        let Type::El { tm, .. } = &**dom else {
            panic!("the call's dom annotation is the reference — the cascade")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::TyCode(e.ind("T").tag)));
    }

    /// A declaration with a coded declaration as a **field type**: the
    /// projection chains and the value tuple's `Pair`/`Inl`/`Inr` annotations
    /// carry `⟦T⟧` and now respell it (design §2.2/§2.3). Literal and neutral
    /// scrutinees, a checking position, computation pinned by `refl`, and the
    /// negative control on the same path.
    #[test]
    fn field_projections_and_values_respell_and_still_compute() {
        let mut e = env();
        e.el
            .elab_source(
                "
inductive P { MkP(t: T, n: Nat), NoP }
fn getp(p: P) -> T { match p { MkP(t, n) => t, NoP => T0 } }
fn wrap(t: T) -> P { MkP(t, 7) }
theorem getp_computes(): getp(MkP(T1(1, T0), 2)) = T1(1, T0) { refl }
theorem roundtrip(t: T): getp(wrap(t)) = t { refl }
",
            )
            .expect("field projections and values respell and still compute");
        let r = e.el.elab_source(
            "theorem wrong_field(): getp(MkP(T1(1, T0), 2)) = T0 { refl }",
        );
        assert!(r.is_err(), "a false field equation must still be refused");
    }

    /// Axis 2 crossed with the respell: a **parameterized** container at a
    /// coded instantiation. `Box<T>` itself has no code (§14.12), but its
    /// monomorphized lowering *contains* `⟦T⟧`, which the deep respell names
    /// component-wise — the `Wf`-shape recursion arm's one live case.
    #[test]
    fn a_monomorphized_container_of_a_coded_declaration_respells_inside() {
        let mut e = env();
        e.el
            .elab_source(
                "
fn bt_head(b: Box<T>) -> T { match b { BNil => T0, BCons(a, r) => a } }
theorem bt_computes(): bt_head(BCons(T1(3, T0), BNil)) = T1(3, T0) { refl }
",
            )
            .expect("a Box<T> match elaborates with component references");
    }

    /// The regression this round's respell surfaced (and whose fix lives in
    /// the kernel — `conv.rs tm_w`'s type-δ stage, pinned kernel-side in
    /// `crates/kernel/tests/definitions.rs`): an auto-`refl` hole (`{}`)
    /// converts two canonical values **at** `Id`'s type component, which a
    /// respelled statement now spells `El (T#tycode^δ)`. Before the fix the
    /// δ-stuck type sent both literals into the neutral-type arm and the
    /// hole went unsolved — every `{}` over a coded declaration's result
    /// type, `lib/list_algos.hthr`'s shape.
    #[test]
    fn an_auto_refl_hole_solves_at_a_respelled_result_type() {
        let mut e = env();
        e.el
            .elab_source(
                "
fn tz(t: T) -> T { T0 }
theorem tz_computes(t: T): tz(t) = T0 { {} }
",
            )
            .expect("a `{}` hole converts at the `El`-spelled Id component");
    }

    /// The negative control the four axes ask for: a wrong arm is still a
    /// failed `refl`. A spelling change must not make anything *more*
    /// convertible — δ + decode is conservative, not permissive.
    #[test]
    fn a_wrong_computation_is_still_refused() {
        let mut e = env();
        let r = e.el.elab_source(
            "
fn peel(t: T) -> T { match t { T0 => T0, T1(x, r) => r, T2(y, r) => T1(y, r) } }
theorem wrong(): peel(T1(1, T0)) = T1(1, T0) { refl }
",
        );
        assert!(r.is_err(), "a false equation must still be refused");
    }

    // -- the Wf slot pair (docs/wf-shape-code-design.md) --------------------

    /// The registration boundary of the pair, which is narrower than
    /// `TyCode`'s in one direction: a **non-recursive** declaration lowers to
    /// a bare sum-of-Σs and has no slots to name at all.
    #[test]
    fn a_recursive_declaration_gets_a_shape_and_an_arity_and_a_flat_one_does_not() {
        let e = env();
        for name in ["T", "U"] {
            let tag = e.ind(name).tag;
            assert!(
                e.el.gen_ref(&e.cx, GenDef::ShapeCode(tag)).is_some(),
                "`{name}` should have a `#shape`"
            );
            assert!(
                e.el.gen_ref(&e.cx, GenDef::ArityFn(tag)).is_some(),
                "`{name}` should have a `#arity`"
            );
        }
        // No `Wf`, no slots — `Flat` keeps its `#tycode` and nothing else.
        assert!(e.el.gen_ref(&e.cx, GenDef::ShapeCode(e.ind("Flat").tag)).is_none());
        assert!(e.el.gen_ref(&e.cx, GenDef::ArityFn(e.ind("Flat").tag)).is_none());
        // …and the monomorphization boundary is `TyCode`'s, inherited.
        assert!(e.el.gen_ref(&e.cx, GenDef::ShapeCode(e.ind("Box").tag)).is_none());
    }

    /// What the two references *are*, structurally, and that the `Wf` rebuilt
    /// from them is the declaration's lowering (design §6's conservativity, at
    /// the slots rather than the whole type).
    #[test]
    fn the_slot_references_are_the_shape_code_and_an_application_of_the_arity() {
        let e = env();
        let (t_ty, l) = e.lowered("T");
        let Type::Wf { shape, arity, .. } = &t_ty else { panic!("T is recursive") };
        let (sref, aref) = e
            .el
            .wf_slot_refs(&e.cx, shape, arity)
            .expect("T's slots respell");
        let Type::El { tm, .. } = &sref else { panic!("a shape slot takes `El` of a code") };
        assert!(e.el.is_gen_ref(tm, GenDef::ShapeCode(e.ind("T").tag)));
        // The arity is an *application* to the shape's own binder, because the
        // slot is read one binder deep — §2.1's asymmetry, pinned.
        let Term::App { fun, arg, .. } = &aref else {
            panic!("an arity slot takes an application, not a code")
        };
        assert!(e.el.is_gen_ref(fun, GenDef::ArityFn(e.ind("T").tag)));
        assert_eq!(**arg, Term::Var(LocalVar(0)));
        let respelled = Type::Wf {
            level: l.clone(),
            shape: Rc::new(sref),
            arity: Rc::new(aref),
        };
        assert!(e.el.conv_types(&e.cx, &respelled, &t_ty, &l));
        assert!(e.el.conv_types(&e.cx, &t_ty, &respelled, &l));
    }

    /// The **decode look-alike** (design §2.3), which is the copy a naive
    /// guard misses: `El (T#tycode^δ)` reduces to `Wf(El ⌜S⌝). n`, and a value
    /// built at that expected type carries *that* shape spelling. The guard
    /// must accept it, or the whole constructor-value site declines silently.
    #[test]
    fn the_decoded_shape_spelling_respells_too() {
        let e = env();
        let (t_ty, l) = e.lowered("T");
        let Type::Wf { shape, arity, .. } = &t_ty else { panic!("T is recursive") };
        let decoded_shape = Type::El {
            level: l.clone(),
            tm: Rc::new(crate::code::code_of(shape).expect("a shape has a code")),
        };
        // It really is the kernel's own reduct, not a hand-built look-alike.
        let whole = e
            .el
            .respell_ty(&e.cx, &t_ty)
            .expect("T's lowering respells");
        let stepped = heather_kernel::reduce::whnf_type_delta(
            &whole,
            &e.cx.gamma,
            heather_kernel::reduce::Defs::transparent(&e.el.psi),
            e.el.fuel,
        )
        .expect("the reference reduces");
        let Type::Wf { shape: s2, .. } = &stepped else { panic!("it reduces to a `Wf`") };
        assert_eq!(**s2, decoded_shape);
        assert!(e.el.wf_slot_refs(&e.cx, &decoded_shape, arity).is_some());
    }

    /// The look-alike negative, in this round's discipline: the shape names
    /// `T` but the arity is **not** `T`'s. Without the pair comparison the
    /// slots would be spelled with `T`'s references and the `Wf` would mean a
    /// different type — a wrong annotation, not a rejection.
    #[test]
    fn a_wf_with_the_wrong_arity_declines() {
        let e = env();
        let (t_ty, _) = e.lowered("T");
        let Type::Wf { shape, arity, .. } = &t_ty else { panic!("T is recursive") };
        // Every label gets one more child than it should.
        let bumped = Term::Succ(Rc::clone(arity));
        assert!(e.el.wf_slot_refs(&e.cx, shape, &bumped).is_none());
        // …and the mirror: `U`'s shape with `T`'s arity is not `U`'s pair.
        let (u_ty, _) = e.lowered("U");
        let Type::Wf { shape: ushape, .. } = &u_ty else { panic!("U is recursive") };
        assert!(e.el.wf_slot_refs(&e.cx, ushape, arity).is_none());
    }

    /// A constructor **value** carries the references — the site the
    /// 2026-08-13 re-attribution named, pinned structurally rather than
    /// assumed, at a *literal* value (axis 1's first half).
    #[test]
    fn a_constructor_value_carries_the_slot_references() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el.elab_source("fn mk() -> T { T1(1, T0) }").expect("elaborates");
        let GlobalBinding::Tm { body: Some(body), .. } =
            e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Supf { shape, arity, .. } = &**body else {
            panic!("a tier-1 value is a `sup_f`")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let Type::El { tm, .. } = &**shape else { panic!("the shape slot is the reference") };
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::ShapeCode(e.ind("T").tag)));
        let Term::App { fun, .. } = &**arity else {
            panic!("the arity slot is the application")
        };
        assert!(e.el.is_gen_ref(&fun.shift_global(grew), GenDef::ArityFn(e.ind("T").tag)));
    }

    /// …and a `match` carries them in its `elim_Wf`, over a **neutral**
    /// scrutinee (axis 1's second half).
    #[test]
    fn a_match_carries_the_slot_references_in_its_elim() {
        let mut e = env();
        let before = e.el.psi.bindings.len();
        e.el
            .elab_source("fn depth2(t: T) -> Nat { match t { T0 => 0, T1(x, r) => 1, T2(y, r) => 2 } }")
            .expect("elaborates");
        let GlobalBinding::Tm { body: Some(body), .. } =
            e.el.psi.bindings.last().expect("a binding")
        else {
            panic!("a `fn` keeps its body")
        };
        let Term::Lam { body, .. } = &**body else { panic!("one parameter, one λ") };
        let Term::ElimWf { shape, arity, .. } = &**body else {
            panic!("tier 1 lowers to `elim_Wf`")
        };
        let grew = (e.el.psi.bindings.len() - before) as u32;
        let Type::El { tm, .. } = &**shape else { panic!("the shape slot is the reference") };
        assert!(e.el.is_gen_ref(&tm.shift_global(grew), GenDef::ShapeCode(e.ind("T").tag)));
        let Term::App { fun, .. } = &**arity else { panic!("the arity slot is an application") };
        assert!(e.el.is_gen_ref(&fun.shift_global(grew), GenDef::ArityFn(e.ind("T").tag)));
    }

    /// The four axes with the slot spelling in place, including the one the
    /// slots are load-bearing for: a **container** field, whose branch arity is
    /// `Succ^m(len)` read out of the label — the one place the arity term is
    /// not a literal, so a mis-spelled arity slot shows up as a kernel
    /// rejection here and nowhere else.
    #[test]
    fn the_slot_spelling_checks_and_computes_across_the_axes() {
        let mut e = env();
        e.el
            .elab_source(
                "
inductive Rose { RNode(label: Nat, len: Nat, kids: [Rose; len]) }
fn rlabel(r: Rose) -> Nat { match r { RNode(label, len, kids) => label } }
fn rmk(n: Nat) -> Rose { RNode(n, 0, []) }
theorem rlabel_literal(): rlabel(RNode(4, 0, [])) = 4 { refl }
theorem rlabel_nonzero(): rlabel(RNode(4, 1, [RNode(1, 0, [])])) = 4 { refl }
theorem rlabel_neutral(n: Nat): rlabel(RNode(n, 0, [])) = n { refl }
theorem rmk_computes(): rlabel(rmk(9)) = 9 { refl }
",
            )
            .expect("a container declaration elaborates with slot references");
        let r = e.el.elab_source("theorem rlabel_wrong(): rlabel(RNode(4, 0, [])) = 5 { refl }");
        assert!(r.is_err(), "a false equation must still be refused");
    }
}
