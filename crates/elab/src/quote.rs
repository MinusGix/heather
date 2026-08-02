//! The quotation slice: `meta fn` declarations, `code { … }` quotes, and
//! `$` splices (docs/in-language-map-design.md).
//!
//! A `meta fn` is a layer-m function over code. Its `Ctx`/`TyCode` binders
//! are **Ψ-extending** (the kernel's `CtxLam`/`TyLam` bind global variables),
//! its `Code` binders are ordinary Π locals of contextual type, and its body
//! is pure quotation: one `code {}` payload with letbox-hoisted splices.
//! The declaration is kernel-checked at `Layer::Meta` against Ψ and then
//! registered **elaborator-side** (`meta_defs`), never pushed to Ψ — ch. 04
//! admits no layer-m term in a global context, and the kernel enforces it
//! (typing.rs `check_global_ctx`). All meta-level computation is static
//! (issues/box-synthesis-gap.md): the evaluation hook applies a registered
//! meta fn and reduces the application away at elaboration time.
//!
//! Everything here is level 0: code types live at universe 0, and the slice
//! has no level variables (issues/implicit-level-polymorphism.md).

use std::rc::Rc;

use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type,
};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::typing;
use heather_syntax::{Decl, DeclKind, Expr, ExprKind, Span, Stmt, Ty, TyKind};

use crate::{err, Alias, Cx, ElabError, Elaborator, MetaDef, R};

/// The meta-layer environment: the Ψ-extending binders currently in scope,
/// outermost first. Present in a [`Cx`] exactly while a `meta fn`'s body —
/// or a quote payload inside it — elaborates. The [`GlobalVar`] index of
/// entry `i` is `pushed.len() - 1 - i`.
///
/// Kept in step with [`Elaborator::meta_pushed`], the same list as
/// [`GlobalBinding`]s, which the whnf/conv oracles append to Ψ so that
/// meta-bound global references resolve to the right bindings (the goal
/// machinery's padding trick, one layer up).
#[derive(Clone, Default)]
pub(crate) struct MetaEnv {
    pub(crate) pushed: Vec<MetaBinder>,
}

/// One Ψ-extending binder. Kernel data (`ctx`, `ty`) is **prefix-scoped** —
/// under exactly the entries before it, the kernel's own convention for Ψ.
///
/// There is no `TyCode` binder: a `TyPi`-bound type is layer **p**, and the
/// binding invariant `i' ≤ i` (typing.rs `GlobalTy`/`GlobalTm` rules) makes
/// it unreferenceable from layer-c code — not even as a `Lam`/`App`
/// annotation inside a payload. Genericity inside code is code-level Π over
/// a universe (`fun (A: Type<0>) => …`), which is ordinary MLTT; `TyCode`
/// returns with the analysis story, whose code recursors are its consumer.
#[derive(Clone)]
pub(crate) enum MetaBinder {
    /// `g: Ctx` — a signature context binder (`CtxLam`).
    Ctx { name: String },
    /// A letbox-bound code global, pushed during quote assembly for one
    /// hoisted `$name` splice. (Its context is the quote's own — enforced at
    /// hoisting — so only the type needs carrying.)
    Code { name: String, ty: Rc<Type>, level: Level },
}

impl MetaEnv {
    /// The context binder `name`, as a [`LocalCtx`] scoped at the current
    /// depth (`pushed.len()` entries in scope).
    fn ctx_ref(&self, name: &str, span: Span) -> R<LocalCtx> {
        let n = self.pushed.len() as u32;
        for (pos, b) in self.pushed.iter().enumerate() {
            if let MetaBinder::Ctx { name: bn } = b
                && bn == name
            {
                return Ok(LocalCtx {
                    base: CtxBase::Var(GlobalVar(n - 1 - pos as u32)),
                    entries: vec![],
                });
            }
        }
        err(format!("`{name}` is not a `Ctx` binder in scope"), span)
    }

    /// Position of the binder named `name`, if any.
    fn find(&self, name: &str) -> Option<(usize, &MetaBinder)> {
        // Innermost wins, matching every other scope in the elaborator.
        self.pushed.iter().enumerate().rev().find(|(_, b)| {
            let (MetaBinder::Ctx { name: n } | MetaBinder::Code { name: n, .. }) = b;
            n == name
        })
    }
}

/// `wk^{|Γ|}_g` — the substitution a payload-scoped reference to a
/// `g`-scoped global rides on: it targets the bare context `g` from the
/// payload's current context (base `g`, `gamma.entries.len()` binders).
fn wk_to_base(gamma: &LocalCtx, span: Span) -> R<LocalSubst> {
    let CtxBase::Var(g) = gamma.base else {
        return err("a splice needs a quote context headed by a `Ctx` binder", span);
    };
    Ok(LocalSubst {
        tail: SubstTail::Wk { len: gamma.entries.len() as u32, ctx_var: g },
        terms: vec![],
    })
}

impl Elaborator {
    /// A `meta fn` declaration (docs/in-language-map-design.md §3): elaborate
    /// the modal signature and quotation body, kernel-check the whole thing
    /// at `Layer::Meta`, and register it in `meta_defs`.
    pub(crate) fn elab_meta_decl(&mut self, decl: &Decl) -> R<()> {
        debug_assert_eq!(decl.kind, DeclKind::Fn);
        let r = self.elab_meta_decl_inner(decl);
        // The oracle padding must not outlive the declaration, error or not.
        self.meta_pushed.borrow_mut().clear();
        r
    }

    fn elab_meta_decl_inner(&mut self, decl: &Decl) -> R<()> {
        if self.globals.contains_key(&decl.name) || self.meta_defs.contains_key(&decl.name) {
            return err(format!("duplicate name `{}`", decl.name), decl.span);
        }
        if !decl.tyvars.is_empty() {
            return err(
                "a `meta fn` has no `<A>` type parameters: type arguments are `TyCode` \
                 binders in this slice (docs/in-language-map-design.md §3)",
                decl.span,
            );
        }
        if crate::count_holes(decl) != 0 || !decl.body.ons.is_empty() {
            return err(
                "no goals inside a `meta fn`: a meta body is pure quotation in this slice",
                decl.span,
            );
        }

        // The signature. Global binders (`Ctx`, `TyCode`) extend Ψ and must
        // precede the `Code` locals — a global binder cannot be scoped under
        // a local one.
        let mut menv = MetaEnv::default();
        let mut cx = Cx::empty();
        enum Sig {
            Ctx,
            Code { ty: Type },
        }
        let mut sig: Vec<Sig> = Vec::new();
        let mut seen_local = false;
        for p in &decl.params {
            if p.implicit || p.is_self {
                return err("a `meta fn` parameter is neither implicit nor `self`", p.span);
            }
            if decl.params.iter().filter(|q| q.name == p.name).count() > 1 {
                return err(format!("duplicate parameter `{}`", p.name), p.span);
            }
            match &p.ty.kind {
                TyKind::Ctx if seen_local => {
                    return err(
                        "`Ctx` binders come before `Code` parameters: a context binder \
                         binds a global, which cannot sit under a local binder",
                        p.span,
                    );
                }
                TyKind::Ctx => {
                    menv.pushed.push(MetaBinder::Ctx { name: p.name.clone() });
                    self.meta_pushed.borrow_mut().push(GlobalBinding::Ctx);
                    sig.push(Sig::Ctx);
                }
                TyKind::TyCode { .. } => {
                    return err(
                        "`TyCode` is not in this slice: a `TyPi`-bound type is layer p \
                         and cannot appear inside layer-c code (the kernel's binding \
                         invariant) — a generic template binds its types *inside* the \
                         code instead, `Code(g |- (A: Type<0>) -> …)` \
                         (docs/in-language-map-design.md §3)",
                        p.span,
                    );
                }
                TyKind::Code { ctx, ty } => {
                    seen_local = true;
                    let code_ty = self.elab_code_ty(&cx, &menv, ctx, ty, p.span)?;
                    cx.push(p.name.clone(), code_ty.clone(), Level::Zero);
                    sig.push(Sig::Code { ty: code_ty });
                }
                _ => {
                    return err(
                        "a `meta fn` parameter is `Ctx` or `Code(g |- T)` in this slice",
                        p.span,
                    );
                }
            }
        }
        cx.meta = Some(Rc::new(menv.clone()));

        // The result: `Code(g |- T)`, elaborated at full signature depth.
        let TyKind::Code { ctx, ty } = &decl.result.kind else {
            return err(
                "a `meta fn` returns code: write `-> Code(g |- T)`",
                decl.result.span,
            );
        };
        let result_ty = self.elab_code_ty(&cx, &menv, ctx, ty, decl.result.span)?;

        // The body: `let`/`let code` aliases, then the quote, checked against
        // the result code type. An alias is inlined at its splice, exactly as
        // an ordinary `let` is at its use.
        for stmt in &decl.body.stmts {
            let (name, expr) = match stmt {
                Stmt::LetCode { name, expr, .. } => (name, expr),
                Stmt::Let { name, ty: None, expr, .. } => (name, expr),
                Stmt::Let { span, .. } => {
                    return err(
                        "an annotated `let` is not part of the meta slice yet; \
                         `let code x = …;` and `let x = …;` are",
                        *span,
                    )
                }
                Stmt::LetRecord { span, .. } => {
                    return err("`let { … }` is not part of the meta slice", *span)
                }
            };
            let (term, ty, level) = self.elab_infer(&cx, expr)?;
            cx.aliases.push(Rc::new(Alias {
                name: name.clone(),
                depth: cx.names.len(),
                term: Rc::new(term),
                ty,
                level,
            }));
        }
        let body =
            self.elab_check(&cx, &decl.body.result, &result_ty, &Level::Zero)?;

        // Close over the signature, inside out. Everything is level 0: code
        // types live at universe 0 and the slice fixes all levels there.
        let mut term = body;
        let mut stmt = result_ty;
        for b in sig.into_iter().rev() {
            match b {
                Sig::Code { ty } => {
                    term = Term::Lam {
                        dom_level: Level::Zero,
                        cod_level: Level::Zero,
                        dom: Rc::new(ty.clone()),
                        body: Rc::new(term),
                    };
                    stmt = Type::Pi {
                        dom_level: Level::Zero,
                        cod_level: Level::Zero,
                        dom: Rc::new(ty),
                        cod: Rc::new(stmt),
                    };
                }
                Sig::Ctx => {
                    term = Term::CtxLam { level: Level::Zero, body: Rc::new(term) };
                    stmt = Type::CtxPi { level: Level::Zero, body: Rc::new(stmt) };
                }
            }
        }

        // The kernel is the gate, at the meta layer.
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        typing::check_type(&self.psi, 0, Layer::Meta, &empty, &stmt, &Level::Zero, self.fuel)
            .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), span: decl.span, err: e })?;
        typing::check_term(
            &self.psi,
            0,
            Layer::Meta,
            &empty,
            &term,
            &stmt,
            &Level::Zero,
            self.fuel,
        )
        .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), span: decl.span, err: e })?;

        self.meta_defs
            .insert(decl.name.clone(), MetaDef { term: Rc::new(term), stmt: Rc::new(stmt) });
        Ok(())
    }

    /// `Code(g |- T)` in a `meta fn` signature: elaborate `T` at the payload
    /// scope — `Γ` is the context binder `g`, type splices resolve to
    /// `TyCode` binders — and wrap it in the kernel's `CodeTm`.
    fn elab_code_ty(
        &self,
        cx: &Cx,
        menv: &MetaEnv,
        ctx_name: &str,
        ty: &Ty,
        span: Span,
    ) -> R<Type> {
        let ctx_lc = menv.ctx_ref(ctx_name, span)?;
        let mut pcx = Cx::empty();
        pcx.gamma = ctx_lc.clone();
        pcx.meta = Some(Rc::new(menv.clone()));
        // A code type's payload type may not splice terms — a Π-bound code
        // argument is a local, and no local can be referenced from inside a
        // type index (there are no meta-functions over terms; see the design
        // doc's §3 correction). Term splices in `T` fail resolution below.
        let (t, lvl) = self.elab_ty(&pcx, ty)?;
        // The slice has no level *variables* (the surface cannot write one);
        // the payload type's own level is whatever it computes to — a generic
        // template quantifying over `Type<0>` genuinely lives at level 1.
        let _ = cx;
        Ok(Type::CodeTm { ctx: ctx_lc, ty: Rc::new(t), level: lvl })
    }

    /// A `code { … }` quote against an expected `Code(g |- T)`
    /// (docs/in-language-map-design.md §5): hoist one letbox per distinct
    /// `$name` term splice (first-occurrence order, outermost first), then
    /// elaborate the payload at the code scope and box it.
    pub(crate) fn elab_quote(
        &self,
        cx: &Cx,
        payload: &Expr,
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        let Some(menv) = cx.meta.as_ref() else {
            return err(
                "a `code { … }` quote lives inside a `meta fn` \
                 (docs/in-language-map-design.md §3)",
                span,
            );
        };
        let head = self.whnf(cx, expected, span)?;
        let Type::CodeTm { ctx: qctx, ty: qty, level: qlvl } = head else {
            return err(
                format!("a quote needs an expected `Code(g |- T)` type, found `{expected:?}`"),
                span,
            );
        };

        // The term splices, by first occurrence. `$a` for a `TyCode` binder
        // is a *type* splice and hoists nothing.
        let mut names: Vec<(String, Span)> = Vec::new();
        scan_splices(payload, menv, &mut names)?;

        // Hoist: elaborate each scrutinee at the meta level (scoped at the
        // current depth; letbox `i`'s fields are shifted under the `i`
        // earlier letboxes when the chain is assembled below).
        struct Hoist {
            term: Term,
            ctx: LocalCtx,
            ty: Rc<Type>,
            level: Level,
        }
        let mut hoists: Vec<Hoist> = Vec::new();
        let mut inner = MetaEnv { pushed: menv.pushed.clone() };
        for (name, nspan) in &names {
            let var = Expr { kind: ExprKind::Var(name.clone()), span: *nspan };
            let (t, t_ty, _) = self.elab_infer(cx, &var)?;
            let Type::CodeTm { ctx, ty, level } = self.whnf(cx, &t_ty, *nspan)? else {
                return err(
                    format!("`${name}` does not splice: `{name}` is not `Code`-typed"),
                    *nspan,
                );
            };
            if ctx != qctx {
                return err(
                    format!(
                        "`${name}` is code in a different context than this quote's — \
                         the slice has no context re-indexing"
                    ),
                    *nspan,
                );
            }
            // Binding data is **prefix-scoped**, the kernel's convention for
            // Ψ (a reference at index `v` shifts its binding's data by
            // `v + 1`, typing.rs's `GlobalTy` rule): splice `i`'s letbox sits
            // under the `i` earlier letboxes, so its site-scoped data is the
            // meta-depth data shifted by `i`.
            let i = hoists.len() as u32;
            let ctx_i = ctx.shift_global(i);
            let ty_i = Rc::new((*ty).clone().shift_global(i));
            hoists.push(Hoist { term: t, ctx: ctx.clone(), ty: Rc::clone(&ty), level: level.clone() });
            inner.pushed.push(MetaBinder::Code {
                name: name.clone(),
                ty: Rc::clone(&ty_i),
                level: level.clone(),
            });
            self.meta_pushed.borrow_mut().push(GlobalBinding::Tm {
                ctx: ctx_i,
                layer: Layer::Code,
                ty: ty_i,
                level,
                body: None,
            });
        }
        let n = hoists.len() as u32;

        // The payload: elaborated at the code scope — Γ is the quote's
        // context (shifted under the letbox globals), and nothing from the
        // meta level is visible except through splices.
        let mut pcx = Cx::empty();
        pcx.gamma = qctx.shift_global(n);
        pcx.meta = Some(Rc::new(inner));
        let expected_p = (*qty).clone().shift_global(n);
        let payload_t = self.elab_check(&pcx, payload, &expected_p, &qlvl);
        // The letbox padding must not outlive this quote, error or not.
        {
            let mut mp = self.meta_pushed.borrow_mut();
            let keep = mp.len() - n as usize;
            mp.truncate(keep);
        }
        let payload_t = payload_t?;

        // Assemble, innermost out. Letbox `i`'s fields are scoped under `i`
        // earlier letboxes; the motive is constant (the quote's own code
        // type — it has no free local variables, so no local shift arises).
        let mut term = Term::BoxTm(Rc::new(payload_t));
        for (i, h) in hoists.into_iter().enumerate().rev() {
            let i = i as u32;
            let result = Type::CodeTm {
                ctx: qctx.clone(),
                ty: Rc::clone(&qty),
                level: qlvl.clone(),
            };
            term = Term::LetBoxTm {
                motive_level: Level::Zero,
                code_level: h.level.clone(),
                ctx: h.ctx.shift_global(i),
                ty: Rc::new((*h.ty).clone().shift_global(i)),
                motive: Rc::new(result.shift_global(i)),
                body: Rc::new(term),
                scrut: Rc::new(h.term.shift_global(i)),
            };
        }
        Ok(term)
    }

    /// A `$name` splice in *term* position inside a payload: a reference to
    /// its letbox-bound global, `u^{wk^{|Γ|}_g}`.
    pub(crate) fn elab_splice(&self, cx: &Cx, inner: &Expr, span: Span) -> R<(Term, Type, Level)> {
        let Some(menv) = cx.meta.as_ref() else {
            return err("`$` splices live inside a `code { … }` quote", span);
        };
        let ExprKind::Var(name) = &inner.kind else {
            return err(
                "`${…}` compound splices are not in the slice: name the code with \
                 `let code x = …;` and splice `$x`",
                span,
            );
        };
        match menv.find(name) {
            Some((pos, MetaBinder::Code { ty, level, .. })) => {
                let idx = (menv.pushed.len() - 1 - pos) as u32;
                let delta = wk_to_base(&cx.gamma, span)?;
                // Binding data is prefix-scoped: a use at index `idx` shifts
                // it by `idx + 1` (the kernel's own `GlobalTy`-rule shift).
                let ty_here = (**ty).clone().shift_global(idx + 1).apply_local(&delta);
                Ok((
                    Term::GlobalTm { var: GlobalVar(idx), subst: delta },
                    ty_here,
                    level.clone(),
                ))
            }
            Some((_, MetaBinder::Ctx { .. })) => {
                err(format!("`{name}` is a context binder, not code"), span)
            }
            None => err(
                format!(
                    "`${name}` has nothing to splice: `{name}` is not a code binder in \
                     scope (splices are collected at the quote boundary)"
                ),
                span,
            ),
        }
    }

    /// The evaluation hook (docs/in-language-map-design.md §4): apply the
    /// registered template `name` to the use site's context, reduce the
    /// meta-layer application to a `box`, and apply the spliced payload to the
    /// use site's arguments — kernel computation mid-elaboration, replacing
    /// the corresponding Rust `vec` schema for the instances it covers.
    ///
    /// Every template in this family is a closed generic over two `Type<0>`
    /// binders (`map_code`, `fold_code`, …), so the shared part is: the two
    /// element/result levels and their Tarski codes, then whatever `rest` the
    /// use site supplies, in the template's own Π order. The name is the
    /// contract — the registration seam is issues/meta-def-registration.md.
    ///
    /// `Ok(None)` is an honest decline (a level the level-0 template cannot
    /// take, an element type with no Tarski code) and the caller falls back
    /// to the Rust path. A registered template whose evaluation goes neutral
    /// is an **error**, never a silent fallback — a half-reduced term must
    /// not be emitted.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn try_vec_code_hook(
        &self,
        cx: &Cx,
        name: &str,
        al: &Level,
        bl: &Level,
        a_ty: &Type,
        b_ty: &Type,
        rest: Vec<Term>,
        span: Span,
    ) -> R<Option<Term>> {
        let Some(md) = self.meta_defs.get(name) else {
            return Ok(None);
        };
        // The template binds `(A: Type<0>) (B: Type<0>)`: element types at a
        // higher level, or with no code in the Tarski universe, decline.
        let zero = Level::Zero.normalize();
        if al.normalize() != zero || bl.normalize() != zero {
            return Ok(None);
        }
        let (Some(code_a), Some(code_b)) = (crate::code::code_of(a_ty), crate::code::code_of(b_ty))
        else {
            return Ok(None);
        };

        // `name @ Γ`, reduced at the meta layer until the box surfaces.
        let applied = Term::CtxApp { fun: Rc::clone(&md.term), ctx: cx.gamma.clone() };
        let evaluated = self.whnf_tm(cx, &applied, span)?;
        let Term::BoxTm(payload) = &*evaluated else {
            return err(
                format!(
                    "`{name}` is registered but its evaluation went neutral instead of \
                     reaching a `box` — refusing to emit a half-reduced term \
                     (docs/in-language-map-design.md §6)"
                ),
                span,
            );
        };

        // Type the payload once, then apply the arguments down its Π spine,
        // annotating each `App` from the peeled domain.
        let psi = self.oracle_psi();
        let (mut ty, _) = typing::infer_term(
            &psi,
            0,
            heather_kernel::layer::Layer::Prog,
            &cx.gamma,
            payload,
            self.fuel,
        )
        .map_err(|_| ElabError::Elab {
            msg: format!(
                "`{name}`'s evaluated payload does not type at the use site — the \
                 template is wrong, not the caller"
            ),
            span,
        })?;
        let mut term = (**payload).clone();
        for arg in [code_a, code_b].into_iter().chain(rest) {
            let Type::Pi { dom_level, cod_level, dom, cod } = self.whnf(cx, &ty, span)? else {
                return err(
                    format!(
                        "`{name}`'s payload ran out of parameters — the template's shape \
                         does not match the hook's arguments"
                    ),
                    span,
                );
            };
            let arg = Rc::new(arg);
            term = Term::App {
                fun: Rc::new(term),
                dom_level,
                cod_level: cod_level.clone(),
                dom,
                cod: Rc::clone(&cod),
                arg: Rc::clone(&arg),
            };
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(arg));
        }
        Ok(Some(term))
    }

    /// A `$name` splice in *type* position. Out of the slice with `TyCode`
    /// (see [`MetaBinder`]); the arm stays so the diagnostic can say why.
    pub(crate) fn elab_ty_splice(&self, _cx: &Cx, name: &str, span: Span) -> R<(Type, Level)> {
        err(
            format!(
                "`${name}` cannot splice a type: type codes are layer p and cannot \
                 appear inside layer-c code — bind the type inside the quote instead \
                 (`fun (A: Type<0>) => …`, docs/in-language-map-design.md §3)"
            ),
            span,
        )
    }
}

/// Collect the distinct `$name` **term** splices of a payload, in first-
/// occurrence order — the letbox hoisting order. Type splices (`$a` for a
/// `TyCode` binder, and every `TyKind::Splice`) hoist nothing. A compound
/// `${…}` is out of the slice and is reported here, before elaboration.
fn scan_splices(e: &Expr, menv: &MetaEnv, out: &mut Vec<(String, Span)>) -> R<()> {
    fn walk_ty(t: &Ty, menv: &MetaEnv, out: &mut Vec<(String, Span)>) -> R<()> {
        match &t.kind {
            TyKind::Nat | TyKind::Univ { .. } | TyKind::Ctx | TyKind::TyCode { .. } => Ok(()),
            TyKind::Splice { .. } => Ok(()),
            TyKind::Eq(a, b) => {
                scan_splices(a, menv, out)?;
                scan_splices(b, menv, out)
            }
            TyKind::OfExpr(e) => scan_splices(e, menv, out),
            TyKind::Named { args, .. } => {
                args.iter().try_for_each(|a| walk_ty(a, menv, out))
            }
            TyKind::Vec { elem, len } => {
                walk_ty(elem, menv, out)?;
                scan_splices(len, menv, out)
            }
            TyKind::Fn { dom, cod, .. } => {
                walk_ty(dom, menv, out)?;
                walk_ty(cod, menv, out)
            }
            TyKind::Code { ty, .. } => walk_ty(ty, menv, out),
        }
    }
    match &e.kind {
        ExprKind::Splice(inner) => match &inner.kind {
            ExprKind::Var(name) => {
                if !out.iter().any(|(n, _)| n == name) {
                    out.push((name.clone(), e.span));
                }
                Ok(())
            }
            _ => err(
                "`${…}` compound splices are not in the slice: name the code with \
                 `let code x = …;` and splice `$x`",
                e.span,
            ),
        },
        ExprKind::Var(_)
        | ExprKind::Num(_)
        | ExprKind::Refl
        | ExprKind::Hole(_)
        | ExprKind::Univ { .. } => Ok(()),
        ExprKind::Quote(_) => err("quotes do not nest in this slice", e.span),
        ExprKind::Eq(a, b) => {
            scan_splices(a, menv, out)?;
            scan_splices(b, menv, out)
        }
        ExprKind::TyLit(t) => walk_ty(t, menv, out),
        ExprKind::App { head, args, .. } => {
            scan_splices(head, menv, out)?;
            args.iter().try_for_each(|a| scan_splices(a, menv, out))
        }
        ExprKind::TyApp { head, args } => {
            scan_splices(head, menv, out)?;
            args.iter().try_for_each(|t| walk_ty(t, menv, out))
        }
        ExprKind::Lam { binders, body } => {
            for b in binders {
                if let Some(t) = &b.ty {
                    walk_ty(t, menv, out)?;
                }
            }
            scan_splices(body, menv, out)
        }
        ExprKind::VecLit(elems) => elems.iter().try_for_each(|x| scan_splices(x, menv, out)),
        ExprKind::Match { scrut, motive, arms } => {
            scan_splices(scrut, menv, out)?;
            if let Some(m) = motive {
                scan_splices(m, menv, out)?;
            }
            arms.iter().try_for_each(|a| scan_splices(&a.body, menv, out))
        }
        ExprKind::Dot { recv, args, .. } => {
            scan_splices(recv, menv, out)?;
            args.iter().flatten().try_for_each(|a| scan_splices(a, menv, out))
        }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            tyargs.iter().try_for_each(|t| walk_ty(t, menv, out))?;
            fields.iter().try_for_each(|f| scan_splices(&f.expr, menv, out))
        }
        ExprKind::J { proof, motive, case } => {
            scan_splices(proof, menv, out)?;
            scan_splices(motive, menv, out)?;
            scan_splices(case, menv, out)
        }
    }
}
