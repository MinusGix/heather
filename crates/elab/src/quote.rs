//! The quotation slice: `meta fn` declarations, `code { … }` quotes, and
//! `$` splices (docs/in-language-map-design.md).
//!
//! A `meta fn` is a layer-m function over code. Its `Ctx`/`TyCode` binders
//! are **Ψ-extending** (the kernel's `CtxLam`/`TyLam` bind global variables),
//! its `Code` binders are ordinary Π locals of contextual type, and its body
//! is pure quotation: one `code {}` payload with letbox-hoisted splices.
//! The declaration is kernel-checked at `Layer::Meta` against Ψ and then
//! registered **elaborator-side** (`MetaPrograms`), never pushed to Ψ — ch. 04
//! admits no layer-m term in a global context, and the kernel enforces it
//! (typing.rs `check_global_ctx`). All meta-level computation is static
//! (issues/box-synthesis-gap.md): the evaluation hook applies a registered
//! meta fn and reduces the application away at elaboration time.
//!
//! Everything here is level 0: code types live at universe 0, and the slice
//! has no level variables (issues/implicit-level-polymorphism.md).

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rec;
use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type,
};
use heather_kernel::typing;
use heather_syntax::{Decl, DeclKind, Expr, ExprKind, SlotPath, Span, Stmt, Ty, TyKind};

use crate::names::NameKind;
use crate::slots::{self, Ingredient, IngredientKind, Slot, SlotSpec};
use crate::{Alias, Cx, ElabError, Elaborator, MetaDef, R, err};

/// One binder of a `meta fn`'s signature, in written order.
///
/// A `Local` binder is a `Code(g |- T)` parameter *or* an ordinary
/// program-layer one (`arity: Nat`), which layer m may bind because Π is
/// layer-generic and a Ψ global of layer c/p is referenceable at m (`i' ≤ i`).
/// The ordinary case is what an **analyzer** needs and a template never did
/// (docs/certgen-transcriber-in-language-design.md §9.1).
enum Sig {
    Ctx,
    Local { ty: Type, level: Level },
}

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
/// a universe (`fun (A: Type<0>) => …`), which is ordinary MLTT. The analysis
/// story's consumer arrived as predicted, but as an ordinary **local** of
/// type `CodeTy` ([`Sig::Local`], the `TyCode(g)` parameter of an analyzer),
/// which extends nothing — the Ψ-extending binder role stays out.
#[derive(Clone)]
pub(crate) enum MetaBinder {
    /// `g: Ctx` — a signature context binder (`CtxLam`).
    Ctx { name: String },
    /// A letbox-bound code global, pushed during quote assembly for one
    /// hoisted `$name` splice. (Its context is the quote's own — enforced at
    /// hoisting — so only the type needs carrying.)
    Code {
        name: String,
        ty: Rc<Type>,
        level: Level,
    },
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
                return Ok(LocalCtx::ctx_var(GlobalVar(n - 1 - pos as u32)));
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
        return err(
            "a splice needs a quote context headed by a `Ctx` binder",
            span,
        );
    };
    Ok(LocalSubst {
        tail: SubstTail::Wk {
            len: gamma.entries.len() as u32,
            ctx_var: g,
        },
        terms: vec![],
    })
}

impl Elaborator {
    /// A `meta fn` declaration (docs/in-language-map-design.md §3): elaborate
    /// the modal signature and quotation body, kernel-check the whole thing
    /// at `Layer::Meta`, and commit it to the meta-program registry.
    pub(crate) fn elab_meta_decl(&mut self, decl: &Decl) -> R<()> {
        debug_assert_eq!(decl.kind, DeclKind::Fn);
        let r = self.elab_meta_decl_inner(decl);
        // The oracle padding must not outlive the declaration, error or not.
        self.meta_pushed.borrow_mut().clear();
        r
    }

    /// A `meta fn`'s signature: the binder list and the result type, in the
    /// scope they build up. Shared by the declaration path and by analyzer-slot
    /// registration, whose expected type is *written in Heather* and has to
    /// mean there exactly what it means here.
    ///
    /// Pushes the `Ctx` binders onto the oracle padding; the caller owns
    /// unwinding it.
    fn meta_sig(&self, decl: &Decl) -> R<(MetaEnv, Cx, Vec<Sig>, Type, Level)> {
        // The signature. Global binders (`Ctx`, `TyCode`) extend Ψ and must
        // precede the `Code` locals — a global binder cannot be scoped under
        // a local one.
        let mut menv = MetaEnv::default();
        let mut cx = Cx::empty();
        let mut sig: Vec<Sig> = Vec::new();
        let mut seen_local = false;
        for p in &decl.params {
            if p.implicit || p.is_self {
                return err(
                    "a `meta fn` parameter is neither implicit nor `self`",
                    p.span,
                );
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
                    menv.pushed.push(MetaBinder::Ctx {
                        name: p.name.clone(),
                    });
                    self.meta_pushed.borrow_mut().push(GlobalBinding::Ctx);
                    sig.push(Sig::Ctx);
                }
                // `TyCode(g)` as an **ordinary parameter**: a code-of-a-type
                // value, kernel type `CodeTy { g, 0 }`, the analyzer input the
                // pull reflection API fills (docs/fn-signature-reflection-
                // design.md §3). This is not the Ψ-extending `TyCode` *binder*
                // (which would deliver `$a` type splices for building generic
                // code) — that role stays out: a `TyPi`-bound type is layer p
                // and cannot appear inside layer-c code, so a generic template
                // still binds its types *inside* the code
                // (docs/in-language-map-design.md §3). Level 0, like the
                // `Code` locals: the slice has no level variables.
                TyKind::TyCode { ctx } => {
                    seen_local = true;
                    let g = menv.ctx_ref(ctx, p.span)?;
                    let ty = Type::CodeTy {
                        ctx: g,
                        level: Level::Zero,
                    };
                    cx.push(p.name.clone(), ty.clone(), Level::Zero);
                    sig.push(Sig::Local {
                        ty,
                        level: Level::Zero,
                    });
                }
                TyKind::Code { ctx, ty } => {
                    seen_local = true;
                    let code_ty = self.elab_code_ty(&cx, &menv, ctx, ty, p.span)?;
                    cx.push(p.name.clone(), code_ty.clone(), Level::Zero);
                    sig.push(Sig::Local {
                        ty: code_ty,
                        level: Level::Zero,
                    });
                }
                _ => {
                    seen_local = true;
                    let (ty, level) = self.elab_ty(&cx, &p.ty)?;
                    cx.push(p.name.clone(), ty.clone(), level.clone());
                    sig.push(Sig::Local { ty, level });
                }
            }
        }
        cx.meta = Some(Rc::new(menv.clone()));

        // The result: a code type for a template, an ordinary type for an
        // analyzer (§9.1 — an analyzer's motive must be *context-free*, so its
        // result cannot be code).
        let (result_ty, result_lvl) = match &decl.result.kind {
            TyKind::Code { ctx, ty } => (
                self.elab_code_ty(&cx, &menv, ctx, ty, decl.result.span)?,
                Level::Zero,
            ),
            _ => self.elab_ty(&cx, &decl.result)?,
        };
        Ok((menv, cx, sig, result_ty, result_lvl))
    }

    /// The closed statement of a signature — `CtxPi`/`Π` over the binders,
    /// inside out. Levels are tracked rather than fixed at zero: code types
    /// live at universe 0, but an analyzer's parameters and result are
    /// ordinary types at whatever level they compute to.
    fn close_meta_ty(sig: &[Sig], result_ty: Type, result_lvl: Level) -> (Type, Level) {
        let mut stmt = result_ty;
        let mut lvl = result_lvl;
        for b in sig.iter().rev() {
            match b {
                Sig::Local { ty, level } => {
                    stmt = Type::Pi {
                        dom_level: level.clone(),
                        cod_level: lvl.clone(),
                        dom: Rc::new(ty.clone()),
                        cod: Rc::new(stmt),
                    };
                    lvl = Level::max(level.clone(), lvl);
                }
                Sig::Ctx => {
                    stmt = Type::CtxPi {
                        level: lvl.clone(),
                        body: Rc::new(stmt),
                    };
                }
            }
        }
        (stmt, lvl)
    }

    /// The same fold over the *term*, so the two cannot drift.
    fn close_meta_term(sig: &[Sig], body: Term, result_lvl: Level) -> Term {
        let mut term = body;
        let mut lvl = result_lvl;
        for b in sig.iter().rev() {
            match b {
                Sig::Local { ty, level } => {
                    term = Term::Lam {
                        dom_level: level.clone(),
                        cod_level: lvl.clone(),
                        dom: Rc::new(ty.clone()),
                        body: Rc::new(term),
                    };
                    lvl = Level::max(level.clone(), lvl);
                }
                Sig::Ctx => {
                    term = Term::CtxLam {
                        level: lvl.clone(),
                        body: Rc::new(term),
                    };
                }
            }
        }
        term
    }

    fn elab_meta_decl_inner(&mut self, decl: &Decl) -> R<()> {
        if self.own_declares(&decl.name, &[NameKind::Global, NameKind::Meta]) {
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

        let (_menv, mut cx, sig, result_ty, result_lvl) = self.meta_sig(decl)?;

        // The body: `let`/`let code` aliases, then the quote, checked against
        // the result code type. An alias is inlined at its splice, exactly as
        // an ordinary `let` is at its use.
        for stmt in &decl.body.stmts {
            let (name, expr) = match stmt {
                Stmt::LetCode { name, expr, .. } => (name, expr),
                // Refused by name: this loop only aliases, and aliasing a
                // `have` would drop the one thing it asks for
                // (docs/have-design.md §2).
                Stmt::Let { opaque: true, span, .. } => {
                    return err("`have` is not part of the meta slice; use `let`", *span);
                }
                Stmt::Let {
                    name,
                    ty: None,
                    expr,
                    ..
                } => (name, expr),
                Stmt::Let { span, .. } => {
                    return err(
                        "an annotated `let` is not part of the meta slice yet; \
                         `let code x = …;` and `let x = …;` are",
                        *span,
                    );
                }
                Stmt::LetRecord { span, .. } => {
                    return err("`let { … }` is not part of the meta slice", *span);
                }
            };
            let (term, ty, level) = self.elab_infer(&cx, expr)?;
            cx.aliases.push(Rc::new(Alias {
                skel: None,
                name: name.clone(),
                depth: cx.names.len(),
                term: Rc::new(term),
                ty,
                level,
            }));
        }
        let body = self.elab_check(&cx, &decl.body.result, &result_ty, &result_lvl)?;

        let (stmt, lvl) = Self::close_meta_ty(&sig, result_ty, result_lvl.clone());
        let term = Self::close_meta_term(&sig, body, result_lvl);

        // The kernel is the gate, at the meta layer. The same oracle seam as
        // the two Ψ sites (`gate.rs`) — this is where a `match code` shell's
        // 56-branch recursor check lives, the single most expensive gate in
        // `lib/certgen_code.hthr` — with `lands_in_psi: false` because a
        // `meta fn` registers in the meta-def table and Ψ never grows.
        let empty = LocalCtx::nil();
        {
            let item = crate::gate::GateItem {
                name: &decl.name,
                ctx: &empty,
                ty: &stmt,
                level: &lvl,
                body: &term,
                opaque: false,
                layer: Layer::Meta,
                lands_in_psi: false,
            };
            if !self
                .gate
                .as_ref()
                .is_some_and(|g| g.admits(&self.psi, &item))
            {
                crate::stats::time_kernel(|| {
                    self.kernel_check_type(&self.psi, Layer::Meta, &empty, &stmt, &lvl)
                })
                .map_err(|e| ElabError::Kernel {
                    decl: decl.name.clone(),
                    span: decl.span,
                    err: e,
                    note: None,
                })?;
                crate::stats::time_kernel(|| {
                    self.kernel_check_term(&self.psi, Layer::Meta, &empty, &term, &stmt, &lvl)
                })
                .map_err(|e| ElabError::Kernel {
                    decl: decl.name.clone(),
                    span: decl.span,
                    err: e,
                    note: None,
                })?;
                if let Some(g) = self.gate.as_ref() {
                    g.accepted(&self.psi, &item);
                }
            }
        }

        // The registration seam (docs/meta-def-registration-design.md §2.2):
        // a `for` clause claims a slot, and claiming it means *having its
        // type*. A `meta fn` without one registers and is never dispatched —
        // the clause, not the name, is what routes a use site.
        let claimed = match &decl.elaborates {
            // An analyzer slot is checked by whole-signature convertibility;
            // a template slot by its payload's Π spine (design doc §9.1 and
            // docs/meta-def-registration-design.md's extension section).
            Some(path) if slots::lookup_analyzer(path).is_some() => {
                let spec = slots::lookup_analyzer(path).expect("just looked up");
                self.register_analyzer(spec, decl, &stmt, &lvl)?;
                Some((spec.slot, Vec::new()))
            }
            Some(path) => {
                let (spec, order) = self.register_slot(decl, path, &stmt)?;
                Some((spec.slot, order))
            }
            None => None,
        };
        let (slot, order) = claimed
            .map(|(slot, order)| (Some(slot), order))
            .unwrap_or((None, Vec::new()));
        let module = self.names.module().to_string();
        let psi_len = self.psi.bindings.len() as u32;
        self.declare_name(&decl.name, NameKind::Meta, decl.span)?;
        let name = decl.name.clone();
        let definition = MetaDef {
            term: Rc::new(term),
            stmt: Rc::new(stmt),
            psi_len,
            order,
        };
        self.semantic_commit_meta(module, name, slot, definition);
        Ok(())
    }

    /// Registration-time validation of an **analyzer** slot: elaborate the
    /// slot's expected signature — written in Heather, in *this* file's scope,
    /// so it may name the library types an analyzer traffics in — and require
    /// the declared signature to be convertible with it.
    ///
    /// Whole-signature convertibility is the analyzer's answer to the question
    /// a template answers with its payload spine: it fixes the Π **order**
    /// outright, so the invoking Rust can build the application spine in the
    /// slot's canonical order without any call site knowing the template's
    /// shape. Not a soundness gate — it fixes the type, never the body, and
    /// everything the analyzer's output produces is kernel-checked downstream.
    fn register_analyzer(
        &self,
        spec: &'static slots::AnalyzerSpec,
        decl: &Decl,
        stmt: &Type,
        lvl: &Level,
    ) -> R<()> {
        if let Some((m, other)) = self.meta_programs.slot_owner(spec.slot) {
            let who = if m == self.names.module() {
                format!("`{other}`")
            } else {
                format!("`{other}`, in module `{m}`")
            };
            return err(
                format!(
                    "`{}` is already elaborated by {who}: one slot takes one template",
                    spec.path_str()
                ),
                decl.span,
            );
        }
        // The expected signature is parsed and elaborated here rather than
        // built in Rust: an inductive is *inlined*, not a Ψ global, so there is
        // no global for a Rust-built type to reference — and a name that the
        // declaring file has not declared has to fail loudly, right here.
        let file =
            heather_syntax::parse_file(spec.signature).expect("a slot's expected signature parses");
        let [heather_syntax::ast::Item::Decl(sig_decl)] = &file.items[..] else {
            unreachable!("a slot's expected signature is one declaration")
        };
        let saved = self.meta_pushed.replace(Vec::new());
        let elaborated = self.meta_sig(sig_decl);
        self.meta_pushed.replace(saved);
        let (_, _, sig, want_res, want_res_lvl) = elaborated.map_err(|e| ElabError::Elab {
            msg: format!(
                "`{}`'s expected signature does not elaborate in this file — it needs \
                 the library it analyses in scope ({e})",
                spec.path_str()
            ),
            span: decl.span,
        })?;
        let (want, want_lvl) = Self::close_meta_ty(&sig, want_res, want_res_lvl);
        if want_lvl.normalize() != lvl.normalize() {
            return err(
                format!(
                    "`{}` expects a signature at level {want_lvl:?}, and this one is at \
                     {lvl:?}",
                    spec.path_str()
                ),
                decl.span,
            );
        }
        let empty = LocalCtx::nil();
        self.semantic_oracle()
            .convert_type(&empty, Layer::Meta, stmt, &want, lvl)
            .map_err(|_| ElabError::Elab {
                msg: format!(
                    "this `meta fn` does not have `{}`'s signature. The slot's is\n  \
                     {want:?}\nand this one is\n  {stmt:?}",
                    spec.path_str()
                ),
                span: decl.span,
            })?;
        Ok(())
    }

    /// Registration-time validation of a `for family.name` clause: resolve the
    /// slot, read the template's Π **order** off its own signature, and check
    /// the signature *is* the slot's type
    /// (docs/meta-def-registration-design.md §2.2). Every failure here is
    /// loud and at the declaration — the class of errors the use site used to
    /// discover ("nothing stops a user meta fn of incompatible shape") is
    /// rejected where it is written, before any use site exists.
    ///
    /// Not a soundness gate: it fixes the template's *type*, never its body.
    /// A constant fold has `fold_code`'s type exactly, and is caught by the
    /// conversion cross-check against the Rust oracle, not by this.
    fn register_slot(
        &self,
        decl: &Decl,
        path: &SlotPath,
        stmt: &Type,
    ) -> R<(&'static SlotSpec, Vec<usize>)> {
        let Some(spec) = slots::lookup(path) else {
            return err(
                format!(
                    "no elaboration slot `{}.{}`; the slots are {}",
                    path.family,
                    path.name,
                    slots::known_paths()
                ),
                path.span,
            );
        };
        if let Some((m, other)) = self.meta_programs.slot_owner(spec.slot) {
            // One template per slot **across the program**: a slot is a
            // property of the elaborator, not of a file, so an import can
            // trigger this. The other template is named with its module
            // exactly when that module is not this one — a cross-module
            // conflict has to say where to look, and a local one would only
            // be noisier for it (docs/modules-design.md §4).
            let who = if m == self.names.module() {
                format!("`{other}`")
            } else {
                format!("`{other}`, in module `{m}`")
            };
            return err(
                format!(
                    "`{}` is already elaborated by {who}: one slot takes one \
                     template, so this is two templates for one site",
                    spec.path_str()
                ),
                path.span,
            );
        }
        // A dispatched template is `meta fn t(g: Ctx) for … -> Code(g |- …)`:
        // the hook applies it to the use site's context and then walks the
        // payload's Π spine, so there is no argument position for a `Code`
        // parameter to occupy.
        if !matches!(decl.params.as_slice(), [p] if matches!(p.ty.kind, TyKind::Ctx)) {
            return err(
                "a template takes exactly one `Ctx` binder and no `Code` parameters: \
                 the hook applies it to the use site's context and passes the slot's \
                 ingredients down the payload's own Π spine",
                decl.span,
            );
        }

        // The order, read off the *surface* signature — the binder names are
        // the argument protocol (§2.3), and they must be read from the source
        // and not from kernel display names, which are cosmetic.
        let TyKind::Code { ty: payload, .. } = &decl.result.kind else {
            unreachable!("a `meta fn`'s result was checked to be `Code(g |- T)`")
        };
        let mut rest: &Ty = payload;
        let mut order: Vec<usize> = Vec::new();
        for n in 0..spec.ingredients.len() {
            let TyKind::Fn {
                binder,
                implicit,
                dom,
                cod,
            } = &rest.kind
            else {
                return err(
                    format!(
                        "`{}` binds {n} of the slot's {} ingredients ({}): a template \
                         takes all of them, in whatever order its own signature fixes",
                        spec.path_str(),
                        spec.ingredients.len(),
                        spec.ingredient_names()
                    ),
                    rest.span,
                );
            };
            // Meta-layer signatures refuse implicit marks: the slice is pure
            // quotation and carries zero implicit machinery
            // (docs/implicit-binders-design.md §3.4).
            if *implicit {
                return err(crate::IMPLICIT_MARK_REFUSED, rest.span);
            }
            let Some(name) = binder else {
                return err(
                    format!(
                        "this parameter has no name, and a template's binder names are \
                         how a use site addresses it: write `(name: …)`, naming one of \
                         {}",
                        spec.ingredient_names()
                    ),
                    dom.span,
                );
            };
            let Some(pos) = spec.ingredients.iter().position(|i| i.name == *name) else {
                return err(
                    format!(
                        "`{name}` is not an ingredient of `{}`; it binds {}",
                        spec.path_str(),
                        spec.ingredient_names()
                    ),
                    dom.span,
                );
            };
            if order.contains(&pos) {
                return err(
                    format!("`{name}` is bound twice: each ingredient is one parameter"),
                    dom.span,
                );
            }
            order.push(pos);
            rest = cod;
        }

        // The type. Built from the spec in *this template's* order — which is
        // what makes a legally permuted template (design doc §4.3) register
        // with no per-permutation Rust — and compared by conversion, so a
        // definitional variant of the signature is the same signature.
        let (want, want_level) = spec.expected_payload_ty(&order);
        let Type::CtxPi { body, .. } = stmt else {
            unreachable!("a template's statement was closed over its `Ctx` binder")
        };
        let Type::CodeTm {
            ctx,
            ty: got,
            level,
        } = &**body
        else {
            unreachable!("a `meta fn`'s statement is a code type")
        };
        if level.normalize() != want_level.normalize() {
            return err(
                format!(
                    "`{}`'s payload lives at a different level than the slot's \
                     ({level:?} vs {want_level:?})",
                    spec.path_str()
                ),
                decl.result.span,
            );
        }
        self.semantic_oracle()
            .convert_type(ctx, Layer::Prog, got, &want, level)
            .map_err(|_| ElabError::Elab {
                msg: format!(
                    "this template does not have `{}`'s type. The slot's payload is\n  \
                 {want:?}\nand this one is\n  {got:?}\n(the binder *names* fix the \
                 order, so a permutation is fine — a different shape is not)",
                    spec.path_str()
                ),
                span: decl.result.span,
            })?;
        Ok((spec, order))
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
        Ok(Type::CodeTm {
            ctx: ctx_lc,
            ty: Rc::new(t),
            level: lvl,
        })
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
        let Type::CodeTm {
            ctx: qctx,
            ty: qty,
            level: qlvl,
        } = head
        else {
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
        let mut inner = MetaEnv {
            pushed: menv.pushed.clone(),
        };
        for (name, nspan) in &names {
            let var = Expr {
                kind: ExprKind::Var(name.clone()),
                span: *nspan,
            };
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
            hoists.push(Hoist {
                term: t,
                ctx: ctx.clone(),
                ty: Rc::clone(&ty),
                level: level.clone(),
            });
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
        // Inside a `box` the component forms stay the only spelling
        // (`docs/intro-by-type-design.md` §2.3): this payload is what the
        // code recursors range over.
        pcx.quoted = true;
        let expected_p = (*qty).clone().shift_global(n);
        self.quote_depth.set(self.quote_depth.get() + 1);
        let payload_t = self.elab_check(&pcx, payload, &expected_p, &qlvl);
        self.quote_depth.set(self.quote_depth.get() - 1);
        // The letbox padding must not outlive this quote, error or not.
        {
            let mut mp = self.meta_pushed.borrow_mut();
            let keep = mp.len() - n as usize;
            mp.truncate(keep);
        }
        let payload_t = payload_t?;
        // The quote boundary (`docs/intro-by-type-design.md` §2.3, amended):
        // a term built outside the quotation and pasted into it — a callee's
        // statement copied into an application's annotations, a solution —
        // may carry checked spellings, which a payload may not. Translate
        // them to the component forms; the `box` rule re-checks the result.
        let payload_t = {
            let oracle = self.semantic_oracle();
            match typing::spell_checked_in_code(
                oracle.world(),
                0,
                Layer::Code,
                &pcx.gamma,
                Rc::new(payload_t),
                &expected_p,
                &qlvl,
                self.fuel,
            ) {
                Ok(t) => (*t).clone(),
                Err(e) => {
                    return err(
                        format!(
                            "internal: this quotation's payload holds a checked spelling that \
                             could not be written in code form ({e:?})"
                        ),
                        span,
                    );
                }
            }
        };

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

    /// Explicitly run a context-only code template at an ordinary use site.
    /// Arguments to its payload remain ordinary, checked applications.
    pub(crate) fn elab_emit_code(
        &self,
        cx: &Cx,
        source: &Expr,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        if cx.meta.is_some() {
            return err("`emit_code` requires an ordinary program context", span);
        }
        let ExprKind::Var(name) = &source.kind else {
            return err("`emit_code` expects a named meta function", source.span);
        };
        if cx.names.iter().any(|local| local == name)
            || cx.aliases.iter().any(|local| local.name == *name)
            || cx.selfref.as_ref().is_some_and(|local| local.matches(name))
        {
            return err(
                "`emit_code` expects a meta function, not a local value",
                source.span,
            );
        }
        let md = self
            .key_of(name)
            .and_then(|key| self.meta_programs.by_key(&key))
            .ok_or_else(|| ElabError::Elab {
                msg: format!("`{name}` does not resolve to one visible meta function"),
                span: source.span,
            })?;
        let (term, stmt) = md.at(self.psi.bindings.len());
        if !matches!(&*stmt, Type::CtxPi { body, .. } if matches!(&**body, Type::CodeTm { .. })) {
            return err(
                "`emit_code` requires exactly one Ctx parameter and a Code result; put value parameters inside the code payload",
                source.span,
            );
        }
        let evaluated = self.whnf_tm(
            cx,
            &Term::CtxApp {
                fun: term,
                ctx: cx.gamma.clone(),
            },
            span,
        )?;
        let Term::BoxTm(payload) = &*evaluated else {
            return err("`emit_code` did not evaluate to a box", span);
        };
        let oracle = self.semantic_oracle();
        let (ty, level) = typing::infer_term(
            oracle.world(),
            0,
            Layer::Prog,
            &cx.gamma,
            payload,
            self.fuel,
        )
        .map_err(|_| ElabError::Elab {
            msg: "emitted code does not type at this use site".into(),
            span,
        })?;
        Ok(((**payload).clone(), ty, level))
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
                    Term::GlobalTm {
                        var: GlobalVar(idx),
                        subst: delta,
                    },
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

    /// The evaluation hook (docs/in-language-map-design.md §4, registration
    /// seam docs/meta-def-registration-design.md §2.3): if a template claims
    /// `slot`, apply it to the use site's context, reduce the meta-layer
    /// application to a `box`, and apply the spliced payload to the use site's
    /// ingredients — kernel computation mid-elaboration, replacing the
    /// corresponding Rust schema for the instances it covers.
    ///
    /// The use site hands over a **bag of named ingredients**, in whatever
    /// order suits the Rust that computed them. The Π order is the template's
    /// own, recorded at registration from its signature; the permutation and
    /// the Tarski coding of the `Type`-kind ingredients happen here, so no
    /// call site knows either. That is the whole point of the seam: the
    /// two-code prefix this hook used to assume is gone, and a slot with one
    /// type parameter (`vec.tabulate`) or four ingredients in a different
    /// order costs nothing here.
    ///
    /// `Ok(None)` is an honest decline — no template claims the slot, or a
    /// `Type` ingredient is above level 0 or has no Tarski code — and the
    /// caller falls back to the Rust path. Everything downstream of the first
    /// `CtxApp` is an **error**, never a silent fallback: a half-reduced term
    /// must not be emitted (design doc §5).
    pub(crate) fn try_code_template(
        &self,
        cx: &Cx,
        slot: Slot,
        args: &[(&'static str, Ingredient<'_>)],
        span: Span,
    ) -> R<Option<Term>> {
        let Some((name, md)) = self.meta_programs.for_slot(slot) else {
            return Ok(None);
        };
        let spec = slots::spec(slot);
        debug_assert_eq!(
            args.len(),
            spec.ingredients.len(),
            "a use site supplies exactly its slot's ingredients"
        );

        // Permute into the template's order and materialize. A `Type`
        // ingredient becomes its Tarski code wherever the order puts it —
        // however many there are — which is what the old two-code prefix
        // hard-coded.
        let zero = Level::Zero.normalize();
        let mut applied_args: Vec<Term> = Vec::with_capacity(md.order.len());
        for &pos in &md.order {
            let iname = spec.ingredients[pos].name;
            let Some((_, ing)) = args.iter().find(|(n, _)| *n == iname) else {
                unreachable!(
                    "`{iname}` is an ingredient of `{}` with no argument",
                    spec.path_str()
                )
            };
            match ing {
                Ingredient::Term(t) => {
                    debug_assert_eq!(spec.ingredients[pos].kind(), IngredientKind::Term);
                    applied_args.push(t.clone());
                }
                Ingredient::Type { level, ty } => {
                    debug_assert_eq!(spec.ingredients[pos].kind(), IngredientKind::Type);
                    // The template binds `(A: Type<0>)`: a type at a higher
                    // level, or with no code in the Tarski universe, is an
                    // instance this level-0 slice honestly cannot take.
                    if level.normalize() != zero {
                        return Ok(None);
                    }
                    let Some(code) = crate::code::code_of(ty) else {
                        return Ok(None);
                    };
                    applied_args.push(code);
                }
            }
        }

        // `name @ Γ`, reduced at the meta layer until the box surfaces. The
        // template is rescoped to the Ψ of *this* use site: it was elaborated
        // against a shorter one (`MetaDef::psi_len`).
        let (md_term, _) = md.at(self.psi.bindings.len());
        let applied = Term::CtxApp {
            fun: md_term,
            ctx: cx.gamma.clone(),
        };
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
        let oracle = self.semantic_oracle();
        let (mut ty, _) = typing::infer_term(
            oracle.world(),
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
        for arg in applied_args {
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = self.whnf(cx, &ty, span)?
            else {
                return err(
                    format!(
                        "`{name}`'s payload ran out of parameters — the template's shape \
                         does not match the hook's arguments"
                    ),
                    span,
                );
            };
            let arg = Rc::new(arg);
            term = crate::spelling::checked_app(
                Rc::new(term),
                dom_level,
                cod_level.clone(),
                dom,
                Rc::clone(&cod),
                Rc::clone(&arg),
            );
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(arg));
        }
        Ok(Some(term))
    }

    /// `match code e as T { branch(x, …) => …, _ => … }` — the surface of the
    /// kernel's code recursor (docs/certgen-transcriber-in-language-design.md
    /// §3). The elimination is `ElimCodeTm` on a term-code scrutinee and
    /// `ElimCodeTy` on a type-code one (docs/fn-signature-reflection-design.md
    /// §3), and the whole slice exists to make the 56 branches writable:
    ///
    /// - **the motive is constant**, so all 56 branches expect the *same* type
    ///   and one default term can fill the 46 nobody writes. It is elaborated
    ///   with no locals in scope, so "constant" is enforced by name resolution
    ///   rather than by a check after the fact;
    /// - **both motives are that same type**, so the eight `ty_*` branches and
    ///   the type-motive recursive results (`lam`'s domain, `elim_nat`'s
    ///   motive) need no separate spelling — this slice analyses terms;
    /// - **an arm binds only recursive results**, positionally, because a
    ///   branch's other binders (its universe variables, its context, its
    ///   sub-code globals) are not spellable at this surface anyway.
    pub(crate) fn elab_match_code(
        &self,
        cx: &Cx,
        scrut: &Expr,
        motive: &Ty,
        arms: &[heather_syntax::Arm],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        if cx.meta.is_none() {
            return err(
                "`match code` is layer-m machinery: it lives inside a `meta fn` \
                 (docs/certgen-transcriber-in-language-design.md §3)",
                span,
            );
        }
        let (scrut_t, scrut_ty, _) = self.elab_infer(cx, scrut)?;
        // A term code (`Code(g |- T)`) eliminates with `ElimCodeTm`; a type
        // code (`TyCode(g)`) with `ElimCodeTy` (docs/fn-signature-reflection-
        // design.md §3). Same motives, same 56 branches, same `rec_ga` gate —
        // the two recursors differ only in the scrutinee's judgment and in
        // which motive the conclusion instantiates, and a constant motive
        // erases the second difference.
        enum Scrutinee {
            Tm {
                ctx: heather_kernel::term::LocalCtx,
                ty: Rc<Type>,
                level: Level,
            },
            Ty {
                ctx: heather_kernel::term::LocalCtx,
                level: Level,
            },
        }
        let scrutinee = match self.whnf(cx, &scrut_ty, span)? {
            Type::CodeTm { ctx, ty, level } => Scrutinee::Tm { ctx, ty, level },
            Type::CodeTy { ctx, level } => Scrutinee::Ty { ctx, level },
            other => {
                return err(
                    format!(
                        "`match code` analyses a `Code(g |- T)` or `TyCode(g)` value; \
                         this scrutinee is `{other:?}`"
                    ),
                    scrut.span,
                );
            }
        };

        // The motive, in a context with no locals: a motive that mentioned one
        // could not be weakened into the branch telescopes that extend Γ, and
        // the recursive results of `lam`/`elim_nat` would land at *extended*
        // contexts with no way back down.
        let mut mcx = Cx::empty();
        mcx.meta = cx.meta.clone();
        let (m_ty, m_lvl) = self.elab_ty(&mcx, motive)?;
        // Motive scopes (rec.rs `motive_specs`): `M_Typ` under (ℓ; g),
        // `M_Trm` under (ℓ; g, U_T). A constant motive still has to be
        // *weakened* into them.
        // The kernel checks every branch against the motive, and a branch is
        // typically a call whose codomain is the emission spelling
        // (`El (D#tycode^δ)`): an inline motive made each such check walk
        // `⟦D⟧` against the reference — measured as the largest conversion-
        // miss row of `lib/certgen_code.hthr`'s `transcribe`
        // (`issues/recursive-spine-codes.md`, 2026-10-03). The elaborator's
        // own checks below keep the inline `m_ty`. Minted at the motive's
        // own local scope — the ambient Γ and the scrutinee binder `x` — since
        // a reference's substitution tail is that context, not `mcx`'s.
        let m_emit = self.annotation_type(cx, &m_ty, 1);
        let motives = Rc::new(heather_kernel::term::Motives {
            ty_motive: Rc::new(m_emit.shift_univ(1).shift_global(1)),
            tm_motive: Rc::new(m_emit.shift_univ(1).shift_global(2)),
        });
        let shapes = rec::branch_shapes(&motives, &m_lvl, &m_lvl, &cx.gamma);

        // The default arm is mandatory: the kernel recursor has no default,
        // and a surface that let one be omitted would be asking the elaborator
        // to invent 46 branch terms.
        let Some(default) = arms.iter().find(|a| a.default) else {
            return err(
                "`match code` needs a `_ => …` arm: the recursor has 56 branches and \
                 this is what fills the ones you did not write",
                span,
            );
        };
        if !arms.last().is_some_and(|a| a.default) || arms.iter().filter(|a| a.default).count() > 1
        {
            return err("the `_ => …` arm comes last, and there is one of it", span);
        }
        let d = self.elab_check(cx, &default.body, &m_ty, &m_lvl)?;
        // The default binds nothing, so weakening it into each telescope *is*
        // shifting it by that telescope's binder counts.
        let mut terms: Vec<Rc<Term>> = shapes
            .iter()
            .map(|s| {
                Rc::new(
                    d.shift_univ(s.univs)
                        .shift_global(s.globals.len() as u32)
                        .shift_local(s.locals.len() as u32),
                )
            })
            .collect();

        for arm in arms.iter().filter(|a| !a.default) {
            let Some(idx) = rec::BRANCH_NAMES.iter().position(|n| *n == arm.ctor) else {
                return err(
                    format!(
                        "`{}` is not a branch of the code recursor; the term branches are \
                         {}",
                        arm.ctor,
                        writable_branches()
                    ),
                    arm.span,
                );
            };
            if arms.iter().filter(|a| a.ctor == arm.ctor).count() > 1 {
                return err(format!("branch `{}` has two arms", arm.ctor), arm.span);
            }
            let shape = &shapes[idx];
            if arm.binders.len() != shape.locals.len() {
                return err(
                    format!(
                        "branch `{}` binds {} recursive result(s), not {}",
                        arm.ctor,
                        shape.locals.len(),
                        arm.binders.len()
                    ),
                    arm.span,
                );
            }
            if arm.binders.iter().any(|p| p.is_deep() || p.has_named()) {
                return err(
                    "a `match code` arm binds plain positional names: a recursive result \
                     is a value of the motive, not a constructor or named-field pattern",
                    arm.span,
                );
            }
            let mut acx = shift_cx(cx, shape.univs, shape.globals.len() as u32);
            for (pat, (lty, llvl)) in arm.binders.iter().zip(&shape.locals) {
                acx.push(pat.name().to_string(), (**lty).clone(), llvl.clone());
            }
            // The telescope's globals go into the oracle padding for the arm's
            // elaboration: nothing can *name* them, but every ambient global an
            // arm body does name is that many indices further out.
            self.meta_pushed
                .borrow_mut()
                .extend(shape.globals.iter().cloned());
            let arm_t = self.elab_check(&acx, &arm.body, &shape.ty, &shape.level);
            {
                let mut mp = self.meta_pushed.borrow_mut();
                let keep = mp.len() - shape.globals.len();
                mp.truncate(keep);
            }
            terms[idx] = Rc::new(arm_t?);
        }

        let branches: [Rc<Term>; 56] = terms.try_into().expect("one term per branch name");
        let branches = Rc::new(rec::branches_from(branches));
        let term = match scrutinee {
            Scrutinee::Tm { ctx, ty, level } => Term::ElimCodeTm {
                ty_motive_level: m_lvl.clone(),
                tm_motive_level: m_lvl.clone(),
                motives,
                branches,
                code_level: level,
                ctx,
                ty,
                scrut: Rc::new(scrut_t),
            },
            Scrutinee::Ty { ctx, level } => Term::ElimCodeTy {
                ty_motive_level: m_lvl.clone(),
                tm_motive_level: m_lvl.clone(),
                motives,
                branches,
                code_level: level,
                ctx,
                scrut: Rc::new(scrut_t),
            },
        };
        Ok((term, m_ty, m_lvl))
    }
}

/// The branch names an arm may use, for the unknown-branch diagnostic. Every
/// name in the kernel's table is legal; the six the fragment transcriber needs
/// lead, because they are the ones anyone writes.
fn writable_branches() -> String {
    let lead = [
        "tm_zero",
        "tm_succ",
        "tm_var",
        "tm_lam",
        "tm_app",
        "tm_elim_nat",
    ];
    let rest = rec::BRANCH_NAMES.len() - lead.len();
    format!(
        "{} (and {rest} more, all of `heather_kernel::rec::BRANCH_NAMES`)",
        lead.map(|n| format!("`{n}`")).join(", ")
    )
}

/// `cx` weakened under a branch telescope's universe and global binders. The
/// telescope's *locals* are pushed by the caller, so ambient local indices move
/// by the ordinary push path and are not touched here.
///
/// Aliases carry kernel terms and types, so they are weakened too: a `let` in a
/// `meta fn` body must mean the same thing inside an arm as outside it.
fn shift_cx(cx: &Cx, univs: u32, globals: u32) -> Cx {
    let mut out = cx.clone();
    out.dot_receiver = None;
    out.gamma = cx.gamma.shift_univ(univs).shift_global(globals);
    out.aliases = cx
        .aliases
        .iter()
        .map(|a| {
            Rc::new(Alias {
                skel: a.skel.clone(),
                name: a.name.clone(),
                depth: a.depth,
                term: Rc::new(a.term.shift_univ(univs).shift_global(globals)),
                ty: a.ty.shift_univ(univs).shift_global(globals),
                level: a.level.clone(),
            })
        })
        .collect();
    out
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
            TyKind::Named { args, .. } => args.iter().try_for_each(|a| walk_ty(a, menv, out)),
            TyKind::Vec { elem, len } => {
                walk_ty(elem, menv, out)?;
                scan_splices(len, menv, out)
            }
            // `Fin($k)`: the length is an expression, so a splice inside it
            // hoists like any other (docs/surface-fin-indexing-design.md §6).
            TyKind::Fin(len) => scan_splices(len, menv, out),
            TyKind::Squash(inner) => walk_ty(inner, menv, out),
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
        | ExprKind::OpSymbol { .. }
        | ExprKind::Num(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::ArgSlot(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_)
        | ExprKind::Univ { .. } => Ok(()),
        ExprKind::Quote(_) => err("quotes do not nest in this slice", e.span),
        // A block cannot reach here: the parser declines one as a quote
        // payload's top level (docs/let-and-blocks-design.md §7.2), and a
        // block nested deeper inside a payload would be the same unanalysed
        // question. An `err` rather than a recursive walk, so the answer stays
        // "filed", not "guessed" — a missed arm here is a silently non-hoisted
        // splice (issues/let-inside-quotation.md).
        // A `match code` inside a quote payload would be layer-m machinery
        // inside layer-c code: the payload is a program, and analysis is not
        // part of one.
        ExprKind::MatchCode { .. } => err(
            "`match code` cannot appear inside a `code { … }` payload: a payload is a              program at layer c, and analysis is layer-m machinery",
            e.span,
        ),
        ExprKind::Block(_) => err(
            "a block inside a quote payload is not in this slice: `let` inside \
             quotation is unanalysed (issues/let-inside-quotation.md)",
            e.span,
        ),
        ExprKind::Eq(a, b) => {
            scan_splices(a, menv, out)?;
            scan_splices(b, menv, out)
        }
        ExprKind::TyLit(t) => walk_ty(t, menv, out),
        ExprKind::App {
            head, args, named, ..
        } => {
            scan_splices(head, menv, out)?;
            args.iter().try_for_each(|a| scan_splices(a, menv, out))?;
            // A splice inside a named argument is still a splice.
            named
                .iter()
                .try_for_each(|a| scan_splices(&a.expr, menv, out))
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
        ExprKind::CollectionLit(elems) => elems.iter().try_for_each(|x| scan_splices(x, menv, out)),
        // `$xs[$i]` — both sides are ordinary expressions.
        ExprKind::Index { recv, idx } => {
            scan_splices(recv, menv, out)?;
            scan_splices(idx, menv, out)
        }
        // `eqbind` is a binding *name*, so there is nothing in it to splice.
        ExprKind::Match {
            scrut,
            motive,
            arms,
            eqbind: _,
            form: _,
            generated: _,
        } => {
            scan_splices(scrut, menv, out)?;
            if let Some(m) = motive {
                scan_splices(m, menv, out)?;
            }
            arms.iter()
                .try_for_each(|a| scan_splices(&a.body, menv, out))
        }
        ExprKind::Dot {
            recv, tyargs, args, named, ..
        } => {
            scan_splices(recv, menv, out)?;
            tyargs.iter().try_for_each(|t| walk_ty(t, menv, out))?;
            args.iter()
                .flatten()
                .try_for_each(|a| scan_splices(a, menv, out))?;
            named
                .iter()
                .try_for_each(|a| scan_splices(&a.expr, menv, out))
        }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            tyargs.iter().try_for_each(|t| walk_ty(t, menv, out))?;
            fields
                .iter()
                .try_for_each(|f| scan_splices(&f.expr, menv, out))
        }
        ExprKind::J {
            proof,
            motive,
            case,
        } => {
            scan_splices(proof, menv, out)?;
            scan_splices(motive, menv, out)?;
            scan_splices(case, menv, out)
        }
    }
}
