//! Machine-named Ψ **definitions** for generator-emitted artifacts
//! (`issues/generated-term-defs.md`).
//!
//! The kernel has had bodied globals with layer-indexed transparency since
//! `issues/simulate-conversion-cost.md`, and a user `fn` is Ψ-referenced
//! rather than inlined (`lib.rs`'s header). The *generator's own* artifacts
//! were not: `μ` — route 2b's index measure — was a whole `elim_Wf` written
//! out afresh in the family type, twice per Σ projection and several times
//! per eliminator arm, and form A at a declared index additionally wrote out
//! one tag predicate per *other* index constructor and one child projection
//! per child. That is `docs/inductive-fording-lowering.md` §14.2 and §14.9,
//! and this module is their fix.
//!
//! The shape is the `#skel` precedent (§14.6): **registered once, at
//! declaration time, under a name the surface cannot write, and never edited
//! afterwards.** Emitted terms reference the definition; δ-unfolding at the
//! computing layers recovers exactly the term that used to be inlined, so
//! nothing downstream changes meaning — only size.
//!
//! Two properties make this safe to do blindly:
//!
//! - **The definitions are closed.** An *index* type is unparameterized by
//!   `inductive.rs`'s own rule (a parameterized index is rejected at the
//!   declaration), so a tag predicate and a child projection are closed for
//!   every family that can exist. `μ` is closed exactly when the forded
//!   declaration itself has no type parameters — see [`Elaborator::mu_def`]
//!   and the boundary note there.
//! - **Registration is best-effort.** If any piece fails to build or fails
//!   the kernel gate here, nothing is pushed and the emission site falls back
//!   to writing the term out inline, exactly as before. A definition is a
//!   *size* optimization, never a semantic one, so the fallback is the old
//!   behavior verbatim rather than an error at a span the user never wrote.

use std::collections::HashMap;
use std::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    GlobalBinding, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_kernel::typing;
use heather_syntax::ast::Span;

use crate::inductive::{ConstBody, IdxTy, Inductive};
use crate::{Cx, Elaborator, R};

/// The key of a machine-named definition. Keys are **nominal**: a declaration
/// tag plus, where the device is per-constructor, its position. That is what
/// makes the recognizers of §6.3/§10.1 re-keyable — a reference to `μ_D` is
/// recognized by *being* `μ_D`, not by having `μ_D`'s shape.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum GenDef {
    /// `μ_D : ⟦Skel⟧ → I` for the forded declaration with this nominal tag
    /// (`docs/inductive-fording-lowering.md` §5).
    Mu(u32),
    /// `is_k : I → Type⁰`, the index type's tag predicate at constructor `k`
    /// (`docs/inductive-tier1-wf-lowering.md` §7.1). Keyed by the *index*
    /// type's tag, so every family over that index shares one.
    IdxTag(u32, usize),
    /// `proj_{k,t} : I → I → I`, the index type's `t`-th child projection at
    /// constructor `k`, abstracted over its default (§7.2). Keyed by the
    /// index type's tag, shared as above.
    IdxChild(u32, usize, usize),
    /// `I#icode : Trm_c(· ⊢ Ty l_I)` — the index type's **code**, consumed as
    /// `El (I#icode^δ)` (`docs/family-type-code-defs-design.md` §1). Keyed by
    /// the *index* type's tag, shared by every family over that index, exactly
    /// as `IdxTag`/`IdxChild`. An index type is unparameterized by
    /// `inductive.rs`'s own rule, so this has no closedness boundary at all.
    IdxCode(u32),
    /// `D#code : Trm_c(· ⊢ Ty l)` — the forded declaration's **skeleton
    /// code**, consumed as `El (D#code^δ)` (design §1). Keyed by the forded
    /// declaration's tag. Exists only for an unparameterized declaration —
    /// the same boundary as [`GenDef::Mu`], for the same reason (§14.12).
    SkelCode(u32),
    /// `D#fam : Trm_c(· ⊢ Π(i : I). Ty l)` — a **route-1** indexed
    /// declaration's family function, consumed as `El l (D#fam^δ i)` (design
    /// §6). Keyed by the indexed declaration's tag. Route 1's family *is* a
    /// type-valued eliminator, so unlike route 2b there is one definition and
    /// not two: naming the function names the whole family. Same closedness
    /// boundary as [`GenDef::Mu`] (§5).
    Fam(u32),
}

impl GenDef {
    /// The machine name, for diagnostics only — `#` is unwritable at the
    /// surface, the same convention `skeleton_of` uses.
    pub(crate) fn name(&self, owner: &str) -> String {
        match self {
            GenDef::Mu(_) => format!("{owner}#mu"),
            GenDef::IdxTag(_, k) => format!("{owner}#tag{k}"),
            GenDef::IdxChild(_, k, t) => format!("{owner}#child{k}.{t}"),
            GenDef::IdxCode(_) => format!("{owner}#icode"),
            GenDef::SkelCode(_) => format!("{owner}#code"),
            GenDef::Fam(_) => format!("{owner}#fam"),
        }
    }
}

/// The registry: the two directions, kept in step by [`Elaborator::push_gen_def`].
#[derive(Clone, Default)]
pub(crate) struct GenDefs {
    /// Key → absolute Ψ index (the `GlobalInfo::abs` convention).
    by_key: HashMap<GenDef, u32>,
    /// Absolute Ψ index → key. The recognizers' half.
    by_abs: HashMap<u32, GenDef>,
    /// Per route-1 declaration tag with a registered [`GenDef::Fam`], the two
    /// levels an occurrence needs to spell `El l (D#fam^δ i)`: the family's
    /// own level `l` and the index type's `l_I`. They are a property of the
    /// declaration, not of the use site — which holds only because the
    /// definition exists solely for an unparameterized declaration, where the
    /// two-pass level computation has one answer forever (design §5).
    fam_lvl: HashMap<u32, (Level, Level)>,
}

impl Elaborator {
    // -- registration -------------------------------------------------------

    /// Register everything `ind` owes, at its declaration. Errors are
    /// swallowed by design (see the module header): the emission sites all
    /// fall back to inlining.
    pub(crate) fn register_gen_defs(&mut self, ind: &Rc<Inductive>, span: Span) {
        if ind.skel.is_none() {
            // Route 1 (design §6): the family function, and the index type's
            // code for the `Π`'s domain. The index type's *devices* are route
            // 2b's inversion machinery and route 1 emits none of them, so
            // they are not registered here.
            if ind.index.is_some() {
                if let Some(IdxTy::Decl(iind)) = ind.index_ty.as_ref() {
                    let iind = Rc::clone(iind);
                    self.register_idx_code(&iind, span);
                }
                self.register_fam(ind, span);
            }
            return;
        }
        // The index type's devices first: they are closed for every family,
        // and shared across all families over the same index. The **code**
        // comes before the rest so that a later device's statement may
        // reference it (Ψ is a telescope — design §1.4, retro-spelling
        // deferred but the order is kept ready for it).
        if let Some(IdxTy::Decl(iind)) = ind.index_ty.as_ref() {
            let iind = Rc::clone(iind);
            self.register_idx_code(&iind, span);
            self.register_index_devices(&iind, span);
        }
        // The skeleton's code before `μ`, for the same telescope reason.
        self.register_skel_code(ind, span);
        let _ = self.register_mu(ind, span);
    }

    /// `I#icode := ⌜⟦I⟧⌝`, the index type's code (design §1.1). Best-effort:
    /// a `None` from `code_of` or a gate failure skips registration and every
    /// occurrence stays inline, exactly as before.
    fn register_idx_code(&mut self, iind: &Rc<Inductive>, span: Span) {
        let key = GenDef::IdxCode(iind.tag);
        if self.gdefs.by_key.contains_key(&key) {
            return;
        }
        let cx = Cx::empty();
        let Ok((ity, ilvl)) = self.lower_instance(&cx, iind, &[], &[], span) else {
            return;
        };
        let Some(body) = crate::code::code_of(&ity) else { return };
        let ty = Type::Ty(ilvl.clone());
        // A term of type `Ty l` lives at `1 + l` (the Tarski formation rule).
        let _ = self.push_gen_def(key, &iind.name, ty, Level::succ(ilvl), body, span);
    }

    /// `D#code := ⌜⟦Skel⟧⌝`, the forded declaration's skeleton code (design
    /// §1.1). Only an **unparameterized** declaration gets one — the same
    /// boundary as [`Elaborator::mu_def`], because `⟦Skel⟧` of a parameterized
    /// family is monomorphized per instantiation and a definition must be
    /// closed at declaration time (§14.12).
    fn register_skel_code(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::SkelCode(ind.tag);
        if self.gdefs.by_key.contains_key(&key) {
            return;
        }
        let Some(skel) = ind.skel.as_ref() else { return };
        let cx = Cx::empty();
        let Ok((skel_ty, l)) = self.lower_instance(&cx, skel, &[], &[], span) else {
            return;
        };
        let Some(body) = crate::code::code_of(&skel_ty) else { return };
        let ty = Type::Ty(l.clone());
        let _ = self.push_gen_def(key, &ind.name, ty, Level::succ(l), body, span);
    }

    /// `D#fam := λ(i : I). elim(…; i)`, a route-1 family function (design §6).
    /// Only an **unparameterized** declaration gets one, for
    /// [`Elaborator::mu_def`]'s reason: the family's branches mention the
    /// argument types, which are monomorphized per instantiation.
    fn register_fam(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::Fam(ind.tag);
        if self.gdefs.by_key.contains_key(&key) {
            return;
        }
        let Ok((ty, level, body, l, ilvl)) = self.fam_def(ind, span) else { return };
        if self.push_gen_def(key, &ind.name, ty, level, body, span).is_ok() {
            self.gdefs.fam_lvl.insert(ind.tag, (l, ilvl));
        }
    }

    /// §7.1's tag predicates and §7.2's child projections, per index
    /// constructor. Memoized on the *index* type's tag, so the second family
    /// over one index pays nothing.
    fn register_index_devices(&mut self, iind: &Rc<Inductive>, span: Span) {
        let n = iind.ctors.len();
        for k in 0..n {
            let key = GenDef::IdxTag(iind.tag, k);
            if !self.gdefs.by_key.contains_key(&key) {
                if let Ok((ty, lvl, body)) = self.tag_pred_def(iind, k, span) {
                    let _ = self.push_gen_def(key, &iind.name, ty, lvl, body, span);
                }
            }
            // A child projection only exists at a recursive index type: a flat
            // index constructor has no child to project.
            if !iind.recursive {
                continue;
            }
            for t in 0..iind.ctors[k].arity() {
                let key = GenDef::IdxChild(iind.tag, k, t);
                if self.gdefs.by_key.contains_key(&key) {
                    continue;
                }
                if let Ok((ty, lvl, body)) = self.child_proj_def(iind, k, t, span) {
                    let _ = self.push_gen_def(key, &iind.name, ty, lvl, body, span);
                }
            }
        }
    }

    fn register_mu(&mut self, ind: &Rc<Inductive>, span: Span) -> R<()> {
        let key = GenDef::Mu(ind.tag);
        if self.gdefs.by_key.contains_key(&key) {
            return Ok(());
        }
        let (ty, lvl, body) = self.mu_def(ind, span)?;
        self.push_gen_def(key, &ind.name, ty, lvl, body, span)
    }

    /// Kernel-check and push. The gate is the same one a `fn` passes
    /// (`elab_decl_inner`): statement at layer p, body at layer c, both in the
    /// empty local context — so a definition is a checked term like any other
    /// bodied global and its transparency is the kernel's layer-indexed rule,
    /// not anything configured here.
    fn push_gen_def(
        &mut self,
        key: GenDef,
        owner: &str,
        ty: Type,
        level: Level,
        body: Term,
        span: Span,
    ) -> R<()> {
        let empty = LocalCtx::nil();
        let name = key.name(owner);
        typing::check_type(&self.psi, 0, Layer::Prog, &empty, &ty, &level, self.fuel)
            .map_err(|err| crate::ElabError::Kernel { decl: name.clone(), span, err })?;
        typing::check_term(&self.psi, 0, Layer::Code, &empty, &body, &ty, &level, self.fuel)
            .map_err(|err| crate::ElabError::Kernel { decl: name, span, err })?;
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(GlobalBinding::defined_tm(
            empty,
            Layer::Code,
            Rc::new(ty),
            level,
            Rc::new(body),
        ));
        self.gdefs.by_key.insert(key, abs);
        self.gdefs.by_abs.insert(abs, key);
        self.refresh_delta_psi();
        Ok(())
    }

    // -- reference and read-back --------------------------------------------

    /// `u^δ` for a registered definition, out of the current `Γ`. `None` when
    /// the definition was not registered, which is every emission site's cue
    /// to inline instead.
    pub(crate) fn gen_ref(&self, cx: &Cx, key: GenDef) -> Option<Term> {
        let abs = *self.gdefs.by_key.get(&key)?;
        let len = self.psi.bindings.len() as u32;
        // Goals sit innermost, exactly as in `resolve`.
        let var = GlobalVar(len - 1 - abs + self.goal_base);
        Some(Term::GlobalTm {
            var,
            subst: LocalSubst {
                tail: SubstTail::Empty {
                    len: cx.gamma.entries.len() as u32,
                    base: cx.gamma.base,
                },
                terms: vec![],
            },
        })
    }

    /// `El (code^δ)` — the **type** occurrence of a registered code
    /// definition (`docs/family-type-code-defs-design.md` §1.3): composition
    /// of the existing `Type::El` former with [`Self::gen_ref`]. `level` is
    /// the coded type's own level (`El l ν` with `ν : Ty l`). `None` when the
    /// definition was not registered — every emission site's cue to inline.
    pub(crate) fn gen_type_ref(&self, cx: &Cx, key: GenDef, level: &Level) -> Option<Type> {
        self.gen_ref(cx, key)
            .map(|tm| Type::El { level: level.clone(), tm: Rc::new(tm) })
    }

    /// The inverse of [`Self::gen_ref`]'s numbering: which definition, if any,
    /// a `GlobalVar` occurring in a term denotes. This is the whole of the
    /// recognizers' new key — `forded_of` asks "is the head of this `μ`
    /// position *the* `μ_D`", not "does it have `μ`'s shape".
    pub(crate) fn gen_def_of(&self, var: GlobalVar) -> Option<GenDef> {
        let len = self.psi.bindings.len() as u32;
        // Fully checked: a `GlobalVar` reaching here can be anything the term
        // it came out of contains, including one that is out of scope.
        let abs = len
            .checked_add(self.goal_base)?
            .checked_sub(var.0.checked_add(1)?)?;
        self.gdefs.by_abs.get(&abs).copied()
    }

    /// Whether `t` is exactly `u^δ` for the definition `key` — the head test
    /// the recognizers use.
    pub(crate) fn is_gen_ref(&self, t: &Term, key: GenDef) -> bool {
        matches!(t, Term::GlobalTm { var, .. } if self.gen_def_of(*var) == Some(key))
    }

    /// A non-dependent application of a registered definition. `dom`/`cod` are
    /// the annotations the kernel's `App` carries; both are scoped where `arg`
    /// is, and `cod` is weakened under the (vacuous) binder for it.
    pub(crate) fn gen_app(
        fun: Term,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Type,
        cod: &Type,
        arg: Term,
    ) -> Term {
        Term::App {
            fun: Rc::new(fun),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(dom.clone()),
            cod: Rc::new(cod.shift_local(1)),
            arg: Rc::new(arg),
        }
    }

    // -- the bodies ---------------------------------------------------------

    /// `μ_D = λ(s : ⟦Skel⟧). μ-node[s]`, its type and level (§5).
    ///
    /// **Boundary.** Only a forded declaration with no type parameters gets
    /// one. `μ`'s body mentions the skeleton's lowering, which is
    /// monomorphized at each instantiation (`Cx::tyvars`), so a parameterized
    /// family's `μ` is not one closed term but one per instantiation — and a
    /// definition is registered at *declaration* time, where the
    /// instantiations are not yet known. Abstracting over the parameter would
    /// need a Π over `Type` in the definition's own statement and a
    /// `Type`-argument spine at every reference; that is a scheme change, not
    /// a registration detail. Parameterized forded families therefore keep
    /// today's inlined `μ` verbatim.
    fn mu_def(&self, ind: &Rc<Inductive>, span: Span) -> R<(Type, Level, Term)> {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return crate::err("internal: a parameterized forded family keeps its inlined μ", span);
        }
        let cx = Cx::empty();
        let skel = ind.skel.as_ref().expect("a forded declaration has a skeleton");
        let (skel_ty, l) = self.lower_instance(&cx, skel, &[], &[], span)?;
        let (ity, ilvl) = self.index_type_of(&cx, ind, span)?;
        let node = self.build_mu(&cx, ind, skel, &skel_ty, &l, &ity, &ilvl, span)?;
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(skel_ty.clone()),
            body: Rc::new(
                crate::indexed::set_scrut(
                    &node.shift_local(1),
                    Rc::new(Term::Var(LocalVar(0))),
                )
                .ok_or_else(|| {
                    crate::ElabError::Elab {
                        msg: "internal: a μ node has a scrutinee slot".into(),
                        span,
                    }
                })?,
            ),
        };
        let ty = Type::Pi {
            dom_level: l.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(skel_ty),
            cod: Rc::new(ity.shift_local(1)),
        };
        Ok((ty, Level::max(l, ilvl), body))
    }

    /// `D#fam = λ(i : I). elim(…; i) : Π(i : I). Ty l`, its statement, its
    /// level, and the two levels an occurrence needs (design §6).
    ///
    /// The two passes are [`Elaborator::lower_indexed_instance`]'s: the family
    /// is built once at a placeholder level to *read* `l` off its branches,
    /// then rebuilt at `l`. Both passes run at a closed placeholder index,
    /// because the λ's binder replaces the scrutinee afterwards — the same
    /// build-then-`set_scrut` motion [`Elaborator::mu_def`] uses.
    fn fam_def(&self, ind: &Inductive, span: Span) -> R<(Type, Level, Term, Level, Level)> {
        let cx = Cx::empty();
        let (ity, ilvl) = self.index_type_of(&cx, ind, span)?;
        let (_, l) = self.build_family(&cx, ind, &[], &Level::Zero, Term::Zero, span)?;
        let (fam, _) = self.build_family(&cx, ind, &[], &l, Term::Zero, span)?;
        let cod_level = Level::succ(l.clone());
        let body = Term::Lam {
            dom_level: ilvl.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(ity.clone()),
            body: Rc::new(
                crate::indexed::set_scrut(&fam.shift_local(1), Rc::new(Term::Var(LocalVar(0))))
                    .ok_or_else(|| crate::ElabError::Elab {
                        msg: "internal: a family node has a scrutinee slot".into(),
                        span,
                    })?,
            ),
        };
        // `Ty l` binds nothing, so the codomain needs no shift under the Π.
        let ty = Type::Pi {
            dom_level: ilvl.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(ity),
            cod: Rc::new(Type::Ty(l.clone())),
        };
        let level = Level::max(ilvl.clone(), cod_level);
        Ok((ty, level, body, l, ilvl))
    }

    /// `El l (D#fam^δ i)` — a route-1 family occurrence at `idx`, with the
    /// declaration's own level (design §6). `None` when no definition was
    /// registered, which is the emission site's cue to inline.
    pub(crate) fn fam_occurrence(
        &self,
        cx: &Cx,
        ind: &Inductive,
        idx: &Term,
        span: Span,
    ) -> Option<(Type, Level)> {
        let (l, ilvl) = self.gdefs.fam_lvl.get(&ind.tag)?.clone();
        let fun = self.gen_ref(cx, GenDef::Fam(ind.tag))?;
        // The Π's domain is an annotation like any other, so it takes the
        // index type's own code reference where one exists (design §1.4).
        let dom = match ind.index_ty.as_ref() {
            Some(IdxTy::Decl(iind)) => self
                .gen_type_ref(cx, GenDef::IdxCode(iind.tag), &ilvl)
                .or_else(|| self.index_type_of(cx, ind, span).ok().map(|(t, _)| t))?,
            _ => Type::Nat,
        };
        let tm = Self::gen_app(
            fun,
            &ilvl,
            &Level::succ(l.clone()),
            &dom,
            &Type::Ty(l.clone()),
            idx.clone(),
        );
        Some((Type::El { level: l.clone(), tm: Rc::new(tm) }, l))
    }

    /// `is_k = λ(z : I). Case-on-tag(z) { c_k ↦ ⌜Unit⌝ ; _ ↦ ⌜Empty⌝ }` (§7.1),
    /// at type `I → Type⁰`.
    fn tag_pred_def(
        &self,
        iind: &Rc<Inductive>,
        k: usize,
        span: Span,
    ) -> R<(Type, Level, Term)> {
        let cx = Cx::empty();
        let (ity, ilvl) = self.lower_instance(&cx, iind, &[], &[], span)?;
        let spine = self.spine(&ity, &ilvl, iind.ctors.len(), span)?;
        let ty0 = Type::Ty(Level::Zero);
        let l1 = Level::succ(Level::Zero);
        let mut zcx = cx.clone();
        zcx.push("#z".into(), ity.clone(), ilvl.clone());
        // `spine`/`ity` are read back in the *base* context (empty here) and
        // `d0` counts the binders pushed since — one, the λ's.
        let node = if iind.recursive {
            self.const_elim_wf(
                &zcx,
                iind,
                &ity,
                &spine,
                &ty0,
                &l1,
                Rc::new(Term::Var(LocalVar(0))),
                &ConstBody::TagCode(k),
                1,
                span,
            )?
        } else {
            self.const_case_tree(
                &zcx,
                &spine,
                iind.ctors.len(),
                &ty0,
                &l1,
                Rc::new(Term::Var(LocalVar(0))),
                &ConstBody::TagCode(k),
                0,
                1,
                span,
            )?
        };
        let body = Term::Lam {
            dom_level: ilvl.clone(),
            cod_level: l1.clone(),
            dom: Rc::new(ity.clone()),
            body: Rc::new(node),
        };
        let ty = Type::Pi {
            dom_level: ilvl.clone(),
            cod_level: l1.clone(),
            dom: Rc::new(ity),
            cod: Rc::new(ty0),
        };
        Ok((ty, Level::max(ilvl, l1), body))
    }

    /// `proj_{k,t} = λ(d : I). λ(z : I). elim_Wf(z) { c_k ↦ nth_t ; _ ↦ d }`
    /// (§7.2), at type `I → I → I`.
    ///
    /// The **default is abstracted** rather than baked in: it is the one thing
    /// that varies per use site (`forded_inv_branch` passes the bound `z`),
    /// and abstracting it is what lets one definition serve every occurrence.
    fn child_proj_def(
        &self,
        iind: &Rc<Inductive>,
        k: usize,
        t: usize,
        span: Span,
    ) -> R<(Type, Level, Term)> {
        let cx = Cx::empty();
        let (ity, ilvl) = self.lower_instance(&cx, iind, &[], &[], span)?;
        let mut zcx = cx.clone();
        zcx.push("#default".into(), ity.clone(), ilvl.clone());
        zcx.push("#z".into(), ity.clone(), ilvl.clone());
        let node = self.child_projection(
            &zcx,
            iind,
            &ity,
            &ilvl,
            k,
            t,
            Rc::new(Term::Var(LocalVar(1))),
            Term::Var(LocalVar(0)),
            span,
        )?;
        let body = Term::Lam {
            dom_level: ilvl.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(ity.clone()),
            body: Rc::new(Term::Lam {
                dom_level: ilvl.clone(),
                cod_level: ilvl.clone(),
                dom: Rc::new(ity.clone()),
                body: Rc::new(node),
            }),
        };
        let ty = Type::Pi {
            dom_level: ilvl.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(ity.clone()),
            cod: Rc::new(Type::Pi {
                dom_level: ilvl.clone(),
                cod_level: ilvl.clone(),
                dom: Rc::new(ity.clone()),
                cod: Rc::new(ity),
            }),
        };
        Ok((ty, ilvl, body))
    }
}
