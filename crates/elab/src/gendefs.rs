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
    /// `D#tycode : Trm_c(· ⊢ Ty l)` — an **unparameterized, unindexed**
    /// declaration's whole lowered type `⟦D⟧`, consumed as `El (D#tycode^δ)`
    /// (`docs/family-type-code-defs-design.md` §1, dated extension of
    /// 2026-08-12). Keyed by the declaration's tag. Recursive (a `Type::Wf`)
    /// or not (a sum-of-Σs) — both are Θ(n²) and both are copied Θ(arms)
    /// times by the two `match` lowerings.
    ///
    /// The sibling of [`GenDef::SkelCode`], and deliberately a *different*
    /// key: `SkelCode` names a forded declaration's **skeleton**, this names a
    /// declaration's **own** lowering. The two boundaries differ too — see
    /// [`Elaborator::register_ty_code`].
    TyCode(u32),
    /// `D#shape : Trm_c(· ⊢ Ty l)` — a **recursive** declaration's `Wf`
    /// **shape component** (the sum-of-Σs with the recursive fields deleted),
    /// consumed as `El (D#shape^δ)` in a `Supf`/`ElimWf`/`Type::Wf` shape slot
    /// (`docs/wf-shape-code-design.md` §2). Keyed by the declaration's tag.
    ///
    /// Deliberately *not* [`GenDef::TyCode`]: that names `⟦D⟧ = Wf(S). n`
    /// whole, and no reference to the whole can stand in a slot that holds the
    /// **component** — which is exactly why
    /// [[wf-shape-annotation-slots]] outlived the whole-type code round.
    ShapeCode(u32),
    /// `D#arity : Π(x : El (D#shape^δ)). Nat` — the same declaration's `Wf`
    /// **arity term**, λ-abstracted over the shape binder it is scoped under,
    /// consumed as `app(D#arity^δ; x₀)` in an arity slot (design §2).
    ///
    /// A *function*, not a code: the arity slot holds a `Term` in the extended
    /// context, and the only closed thing that can stand there and reduce back
    /// to `n` is an application of a definition to the binder. It is the
    /// larger of the two slots by several times, measured, which is why it is
    /// named at all rather than left as this issue's opening sentence had it.
    ArityFn(u32),
    /// `D#fam : Trm_c(· ⊢ Π(i : I). Ty l)` — a **route-1** indexed
    /// declaration's family function, consumed as `El l (D#fam^δ i)` (design
    /// §6). Keyed by the indexed declaration's tag. Route 1's family *is* a
    /// type-valued eliminator, so unlike route 2b there is one definition and
    /// not two: naming the function names the whole family. Same closedness
    /// boundary as [`GenDef::Mu`] (§5).
    Fam(u32),
    /// `D#projⱼ : Trm_c(· ⊢ Π(v : ⟦D⟧). Tⱼ)` — a **record**'s `j`-th field
    /// projection, keyed by the record's tag and the field's index
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// Unlike its siblings this one is not only a size optimization. `π_j` is
    /// `fst(sndʲ v)`, and every `fst`/`snd` node carries the Σ components at
    /// its level as annotations, so a later field's type — which mentions the
    /// earlier fields — inlines the earlier projections *with their
    /// annotations*, once per occurrence: the term is exponential in the
    /// field index. Naming each projection makes a field's type mention
    /// `D#projᵢ^δ v` (one node) instead, so the walk, the term it produces,
    /// and everything downstream of both stay linear.
    ///
    /// Same closedness boundary as [`GenDef::Mu`] and [`GenDef::TyCode`]: only
    /// an unparameterized record, whose lowering is one closed type.
    RecProj(u32, usize),
    /// `D#tailⱼ : Trm_c(· ⊢ Π(v : ⟦D⟧). Σ…)` — the same record's Σ spine past
    /// entry `j`, the companion [`GenDef::RecProj`] is read off
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// `π_j` is `fst` of a *tail*, and a raw `sndʲ` tail makes the kernel
    /// re-check the whole spine below it — carrying the whole remaining record
    /// type — once per level above. Naming each tail makes every one of those
    /// checks local: the pair a `fst`/`snd` is taken of has its Σ type
    /// straight out of Ψ. Registered with, and under the same boundary as,
    /// the projections.
    RecTail(u32, usize),
    /// `D#famⱼ : Trm_c(· ⊢ Π(v : ⟦D⟧). Π(x : Fⱼ). Ty l)` — the same record's
    /// Σ **tail family** at entry `j`, as a code
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// The annotation every projection and tail node carries is `El` of this,
    /// which is what keeps their gate checks local: a code is checked, not
    /// reduced, so the earlier projections it mentions stay folded until a
    /// conversion actually needs the type behind them.
    RecFam(u32, usize),
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
            GenDef::TyCode(_) => format!("{owner}#tycode"),
            GenDef::ShapeCode(_) => format!("{owner}#shape"),
            GenDef::ArityFn(_) => format!("{owner}#arity"),
            GenDef::Fam(_) => format!("{owner}#fam"),
            GenDef::RecProj(_, j) => format!("{owner}#proj{j}"),
            GenDef::RecTail(_, j) => format!("{owner}#tail{j}"),
            GenDef::RecFam(_, j) => format!("{owner}#fam{j}"),
        }
    }
}

/// The guard copies of one declaration's `Wf` slot pair
/// (`docs/wf-shape-code-design.md` §2.3).
#[derive(Clone)]
pub(crate) struct WfSlots {
    /// The shape as `lower_instance` writes it: the raw sum-of-Σs.
    shape: Rc<Type>,
    /// The shape as a *decode* of the whole-type code writes it —
    /// `El ⌜S⌝`, the lazy reduct of `El (D#tycode^δ)`
    /// (`reduce.rs`'s `TmWf` rule). A value built at a **respelled expected
    /// type** arrives with this spelling and no other, which is why the guard
    /// takes two copies and not one: with only the inline copy the whole
    /// constructor-value site — the one the measurement put first — declines
    /// silently. Measured: statements did not move at all until this was
    /// added.
    shape_decoded: Rc<Type>,
    /// The arity term, identical under both spellings (`code_of` keeps a
    /// term slot verbatim, and the decode hands it back unchanged).
    arity: Rc<Term>,
    /// The declaration's level, which is also its shape's.
    level: Level,
}

/// One append-only generated-definition delta. Its lookup views are sealed
/// together at the semantic-image boundary.
#[derive(Clone, Default)]
struct GenDefLayer {
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
    /// Per declaration tag with a registered [`GenDef::TyCode`], the
    /// **inline** `⟦D⟧` the code was minted from and its level.
    ///
    /// The inline copy is not a convenience: it is the use-site *guard*.
    /// [`Elaborator::ty_type_ref`] hands out the reference only when the type
    /// in front of it is structurally that exact lowering, so a reference can
    /// never stand for a type it does not decode to — the tag alone would be
    /// a nominal claim about a type the emission site read from somewhere
    /// else. (Tags are unique per declaration and codes are minted only for
    /// unparameterized declarations, so this can only ever *decline*; it costs
    /// one structural comparison per `match` and buys the property outright.)
    ty_code: HashMap<u32, (Rc<Type>, Level)>,
    /// Per declaration tag with a registered [`GenDef::ShapeCode`] **and**
    /// [`GenDef::ArityFn`], the **inline** `Wf` slot pair the two were minted
    /// from and the declaration's level.
    ///
    /// The pair is the use-site guard, exactly as [`GenDefs::ty_code`]'s copy
    /// is: [`Elaborator::wf_slot_refs`] hands out the references only when the
    /// slots in front of it are structurally *those* slots, so a reference can
    /// never stand for a shape it does not decode to. Both entries are written
    /// together or not at all — a spelled shape with an inline arity would be
    /// correct but is never useful, and the pairing is what lets every use
    /// site ask one question (design §2.3).
    wf_slots: HashMap<u32, WfSlots>,
}

/// The registry: immutable image layers plus one suffix delta. The two
/// directions remain in the same layer and are kept in step by
/// [`Elaborator::push_gen_def`].
#[derive(Clone, Default)]
pub(crate) struct GenDefs {
    sealed: Rc<Vec<Rc<GenDefLayer>>>,
    current: Rc<GenDefLayer>,
}

impl GenDefs {
    pub(crate) fn semantic_snapshot(&self) -> Self {
        let mut defs = self.clone();
        if !defs.current.by_key.is_empty() {
            Rc::make_mut(&mut defs.sealed).push(Rc::clone(&defs.current));
            defs.current = Rc::new(GenDefLayer::default());
        }
        defs
    }

    fn layers(&self) -> impl Iterator<Item = &GenDefLayer> {
        std::iter::once(self.current.as_ref()).chain(self.sealed.iter().rev().map(Rc::as_ref))
    }

    fn contains_key(&self, key: &GenDef) -> bool {
        self.layers().any(|layer| layer.by_key.contains_key(key))
    }

    fn abs_for(&self, key: &GenDef) -> Option<&u32> {
        self.layers().find_map(|layer| layer.by_key.get(key))
    }

    fn key_for_abs(&self, abs: &u32) -> Option<&GenDef> {
        self.layers().find_map(|layer| layer.by_abs.get(abs))
    }

    fn fam_levels(&self, tag: &u32) -> Option<&(Level, Level)> {
        self.layers().find_map(|layer| layer.fam_lvl.get(tag))
    }

    fn ty_code(&self, tag: &u32) -> Option<&(Rc<Type>, Level)> {
        self.layers().find_map(|layer| layer.ty_code.get(tag))
    }

    fn has_ty_codes(&self) -> bool {
        self.layers().any(|layer| !layer.ty_code.is_empty())
    }

    fn wf_slots(&self, tag: &u32) -> Option<&WfSlots> {
        self.layers().find_map(|layer| layer.wf_slots.get(tag))
    }

    fn has_wf_slots(&self) -> bool {
        self.layers().any(|layer| !layer.wf_slots.is_empty())
    }

    pub(crate) fn insert_ty_code(&mut self, tag: u32, value: (Rc<Type>, Level)) {
        Rc::make_mut(&mut self.current).ty_code.insert(tag, value);
    }

    pub(crate) fn insert_wf_slots(&mut self, tag: u32, value: WfSlots) {
        Rc::make_mut(&mut self.current).wf_slots.insert(tag, value);
    }

    pub(crate) fn insert_fam_levels(&mut self, tag: u32, value: (Level, Level)) {
        Rc::make_mut(&mut self.current).fam_lvl.insert(tag, value);
    }

    pub(crate) fn insert_binding(&mut self, key: GenDef, abs: u32) {
        let layer = Rc::make_mut(&mut self.current);
        layer.by_key.insert(key, abs);
        layer.by_abs.insert(abs, key);
    }

    #[cfg(test)]
    pub(crate) fn shares_sealed_with(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.sealed, &other.sealed)
    }
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
                return;
            }
            // Unindexed, tier 1 or tier 0: the declaration's own lowered type
            // gets a code, so that the `match` lowerings can *name* `⟦D⟧`
            // instead of writing it out ~21 times per arm
            // ([[wf-field-conversion-cost]], design §10).
            self.register_ty_code(ind, span);
            // …and a record's fields get their projections, which is the one
            // device here that a *user-written* term reaches directly.
            self.register_rec_projs(ind, span);
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
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let cx = Cx::empty();
        let Ok((ity, ilvl)) = self.lower_instance(&cx, iind, &[], &[], span) else {
            return;
        };
        let Some(body) = crate::code::code_of(&ity) else {
            return;
        };
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
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let Some(skel) = ind.skel.as_ref() else {
            return;
        };
        let cx = Cx::empty();
        let Ok((skel_ty, l)) = self.lower_instance(&cx, skel, &[], &[], span) else {
            return;
        };
        let Some(body) = crate::code::code_of(&skel_ty) else {
            return;
        };
        let ty = Type::Ty(l.clone());
        let _ = self.push_gen_def(key, &ind.name, ty, Level::succ(l), body, span);
    }

    /// `D#tycode := ⌜⟦D⟧⌝`, a declaration's own whole lowered type
    /// (design §1.1, §10.2 — the 2026-08-12 extension). Best-effort like every
    /// other piece here: no code means every occurrence stays inline, exactly
    /// as before.
    ///
    /// **Boundary — two conditions, each for its own reason.**
    ///
    /// - *Unparameterized* ([`Elaborator::mu_def`]'s reason, §14.12): `⟦D⟧` of
    ///   a parameterized declaration is monomorphized per instantiation
    ///   (`Cx::tyvars`), so it is not one closed type but one per
    ///   instantiation, and a definition is registered where the
    ///   instantiations are not yet known.
    /// - *Unindexed*: an indexed family's use-site type mentions the index, so
    ///   there is no single type to name (that is route 1's
    ///   [`GenDef::Fam`], which names the *function*). This function is
    ///   reached only off `register_gen_defs`'s unindexed branch.
    ///
    /// A **non-recursive** declaration gets one too, and that is deliberate
    /// rather than incidental: its lowering is a bare sum-of-Σs, which is
    /// exactly as large as a `Wf`'s and grows by the same quadratic law, and
    /// it is very often the *motive* of a `match` on something else
    /// (`cert_body : Ir -> CertOut` — the container is recursive, the answer
    /// is not). Restricting to recursive declarations left the single largest
    /// occurrence site in the round's own fixture untouched; measured.
    fn register_ty_code(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::TyCode(ind.tag);
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let cx = Cx::empty();
        let Ok((d_ty, l)) = self.lower_instance(&cx, ind, &[], &[], span) else {
            return;
        };
        // The recognizer's own precondition, checked here rather than assumed:
        // `respell_ty` finds this code by running `tag_of` over a type and
        // looking the answer up, so a lowering `tag_of` does not route back to
        // *this* declaration must not be registered — the reference would be
        // unreachable at best and, if some other declaration's `tag_of` landed
        // here, wrong. (`tag_of` also rejects the shapes with no tag at all,
        // which is the same set this used to exclude by hand.)
        if self.tag_of(&d_ty).map(|i| i.tag) != Some(ind.tag) {
            return;
        }
        let Some(body) = crate::code::code_of(&d_ty) else {
            return;
        };
        let ty = Type::Ty(l.clone());
        if self
            .push_gen_def(key, &ind.name, ty, Level::succ(l.clone()), body, span)
            .is_ok()
        {
            self.semantic_commit_gen_ty_code(ind.tag, Rc::new(d_ty.clone()), l.clone());
        }
        self.register_wf_slots(ind, &d_ty, &l, span);
    }

    /// `D#projⱼ := λ(v : ⟦D⟧). fst(sndʲ v)`, one per field of a **record**
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// This is [`Elaborator::project_field`]'s spine walk, run once at the
    /// declaration instead of once per use — and, crucially, run with each
    /// field's projection replaced by a *reference* to the definition just
    /// registered for it before it is substituted into the tail. That
    /// substitution is where the blow-up lived: the payload is a `fst` node
    /// carrying the Σ components at its level, so inlining it into a later
    /// field's type copies those annotations once per occurrence, and the
    /// annotations of *that* field are then the payload one level down. With
    /// a reference standing in, every payload is one node and the walk is
    /// linear — which is also what makes the definitions themselves small
    /// enough to gate one after another.
    ///
    /// Three definitions per spine entry, each naming one thing the walk
    /// would otherwise write out again at every entry above it:
    /// [`GenDef::RecFam`] the Σ tail family (as a code — see its own note),
    /// [`GenDef::RecProj`] the field, [`GenDef::RecTail`] the pair the entry
    /// above is taken of.
    ///
    /// **Boundaries.** An unparameterized record only, [`GenDef::TyCode`]'s
    /// reason verbatim: `⟦D⟧` of a parameterized one is monomorphized per
    /// instantiation, and a definition is registered where the instantiations
    /// are not yet known. A parameterized record keeps the inline walk (and
    /// its exponent) — see the issue's log. And a record whose spine is not
    /// *dependent* is left alone entirely
    /// ([`Elaborator::record_spine_is_dependent`]): its walk is linear
    /// already, so the definitions would be all cost.
    ///
    /// Best-effort, like everything here: a failure at field `j` stops the
    /// walk, leaves fields `< j` registered (they are correct and useful on
    /// their own), and every later field's projection is inlined as before.
    fn register_rec_projs(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.is_record || !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let nfields = ind.ctors[0].fields.len();
        if nfields == 0
            || self
                .types
                .gdefs()
                .contains_key(&GenDef::RecProj(ind.tag, 0))
        {
            return;
        }
        let cx = Cx::empty();
        let Ok((d_ty, l)) = self.lower_instance(&cx, ind, &[], &[], span) else {
            return;
        };
        // The use site finds these by the tag it read off the receiver's type,
        // exactly as `register_ty_code`'s reference does; a lowering whose tag
        // does not route back here must not be named.
        if self.tag_of(&d_ty).map(|i| i.tag) != Some(ind.tag) {
            return;
        }
        let mut d_ty = Rc::new(d_ty);
        // The definitions' own context: `·, v : ⟦D⟧`, which is where the whole
        // walk lives — the field types come out of it scoped exactly as a Π's
        // codomain needs them.
        let mut vcx = Cx::empty();
        vcx.push("v".to_string(), (*d_ty).clone(), l.clone());
        let mut cur = weaken(&d_ty, &vcx.gamma);
        if !self.record_spine_is_dependent(&vcx, &cur, nfields, span) {
            return;
        }
        let mut pair: Rc<Term> = Rc::new(Term::Var(LocalVar(0)));
        // Entry 0 of the Σ spine is the nominal tag (docs/surface-records.md
        // §3.3), so field `j` is entry `j + 1`.
        for step in 0..=nfields {
            let Ok(Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            }) = self.whnf(&vcx, &cur, span)
            else {
                return;
            };
            // The Σ's *tail family* — the whole rest of the record, as a type
            // family over this entry — named as a code, and the annotation
            // every node below carries is the decode of it. That is what keeps
            // the gate checks local: a type spelled `El (D#fam^δ v x)` is
            // checked by looking one binding up in Ψ, where the spelled-out
            // one is checked by walking the rest of the record and reducing
            // every reference it meets, once per entry of the spine.
            let Some(tail_fam) = self.push_tail_fam(
                ind, step, &d_ty, &l, &fst, &fst_level, &snd, &snd_level, &vcx, span,
            ) else {
                return;
            };
            d_ty = Rc::new(d_ty.shift_global(1));
            let fst = Rc::new(fst.shift_global(1));
            let snd = Rc::new(snd.shift_global(1));
            let pair_g = Rc::new(pair.shift_global(1));
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&tail_fam),
                pair: Rc::clone(&pair_g),
            });
            let rest = Rc::new(Term::Snd {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&tail_fam),
                pair: pair_g,
            });
            // The field's own projection. The tag (entry 0) is nobody's field
            // and gets none: it is a closed numeral, and nothing later refers
            // to it.
            let (payload, snd, rest, tail_fam) = if step == 0 {
                (proj, snd, rest, tail_fam)
            } else {
                let key = GenDef::RecProj(ind.tag, step - 1);
                let Some(payload) =
                    self.push_proj_def(key, ind, &d_ty, &l, &fst, &fst_level, &proj, &vcx, span)
                else {
                    return;
                };
                // Ψ just grew by one, so everything carried past the push is
                // one binding further out (`Defs::body`'s convention). The
                // walk is the only thing here that keeps terms across a push,
                // and this is what keeps the references inside them — the
                // families, projections and tails already registered —
                // pointing at what they did.
                d_ty = Rc::new(d_ty.shift_global(1));
                (
                    payload,
                    Rc::new(snd.shift_global(1)),
                    Rc::new(rest.shift_global(1)),
                    Rc::new(tail_fam.shift_global(1)),
                )
            };
            if step == nfields {
                return;
            }
            // The tail past this entry. Its statement is the family applied to
            // this entry's projection — one node, where the kernel's own `snd`
            // rule would produce the family's whole body with the projection
            // substituted through it.
            let cod = instantiate_fam(&tail_fam, &payload, &vcx.gamma);
            let key = GenDef::RecTail(ind.tag, step);
            let Some(next) =
                self.push_proj_def(key, ind, &d_ty, &l, &cod, &snd_level, &rest, &vcx, span)
            else {
                return;
            };
            d_ty = Rc::new(d_ty.shift_global(1));
            // The walk itself keeps the spelled-out tail: it is what the next
            // entry's components are read off, and reading them off the code
            // would only mean decoding it again.
            cur = snd
                .apply_local(&LocalSubst::id(&vcx.gamma).extended(payload))
                .shift_global(1);
            pair = next;
        }
    }

    /// Does any entry of the record's Σ spine occur in the entries after it?
    ///
    /// This is the whole precondition of the device. The inline walk in
    /// [`Elaborator::project_field`] duplicates its payload once per
    /// occurrence of the entry it substitutes, so a record whose later field
    /// types never mention the earlier fields has a walk that is already
    /// linear and gains nothing from a name — while every record pays the
    /// gate checks that registering the definitions costs. A plain data
    /// record is therefore left exactly as it was.
    ///
    /// Occurrence is decided by *doing* the substitution twice with two
    /// different payloads and comparing: the traversal rewrites a
    /// substitution's tails whatever it does with the variable, so comparing
    /// against the un-substituted tail would report every global reference as
    /// a use. The two payloads are closed and differ, so the results differ
    /// exactly where the binder occurs. Nothing here is type-checked — this
    /// is a syntactic question and both probes are thrown away.
    ///
    /// A wrong answer is only ever a wrong *choice*: `false` keeps the walk
    /// that has always been there, and `true` registers definitions that face
    /// the gate like everything else. That is what makes probing with terms
    /// of the wrong type acceptable here and nowhere else.
    fn record_spine_is_dependent(
        &self,
        vcx: &Cx,
        record_ty: &Type,
        nfields: usize,
        span: Span,
    ) -> bool {
        let mut cur = record_ty.clone();
        let probe =
            |t: &Rc<Type>, x: Term| t.apply_local(&LocalSubst::id(&vcx.gamma).extended(Rc::new(x)));
        for _ in 0..=nfields {
            let Ok(Type::Sigma { snd, .. }) = self.whnf(vcx, &cur, span) else {
                // Not a spine this walk understands: leave it to the walk that
                // will meet the same wall at the use site and report there.
                return false;
            };
            let one = probe(&snd, Term::Zero);
            if one != probe(&snd, Term::TmNat) {
                return true;
            }
            cur = one;
        }
        false
    }

    /// `D#famⱼ := λ(v : ⟦D⟧). λ(x : Fⱼ). ⌜Sⱼ⌝`, the Σ tail family at spine
    /// entry `j`, and the annotation that stands for `Sⱼ` afterwards:
    /// `El (D#famⱼ^δ v x)`, scoped in `·, v, x` exactly as `Sⱼ` was.
    ///
    /// A code and not a type, because a code is *checked* rather than
    /// *reduced*: `Sⱼ` mentions the earlier projections, and every kernel
    /// visit to a spelled-out `Sⱼ` reduces those references — down a chain as
    /// long as the spine, copying the annotations at every link. Behind a code
    /// they are terms in a body nobody unfolds until a conversion actually
    /// needs the type.
    #[allow(clippy::too_many_arguments)]
    fn push_tail_fam(
        &mut self,
        ind: &Rc<Inductive>,
        step: usize,
        d_ty: &Rc<Type>,
        l: &Level,
        fst: &Rc<Type>,
        fst_level: &Level,
        snd: &Rc<Type>,
        snd_level: &Level,
        vcx: &Cx,
        span: Span,
    ) -> Option<Rc<Type>> {
        let key = GenDef::RecFam(ind.tag, step);
        let code_ty = Type::Ty(snd_level.clone());
        let code_level = Level::succ(snd_level.clone());
        let inner_level = Level::max(fst_level.clone(), code_level.clone());
        // `Π(x : Fⱼ). Ty l'` — scoped in `·, v`, where `Fⱼ` is.
        let inner = Type::Pi {
            dom_level: fst_level.clone(),
            cod_level: code_level.clone(),
            dom: Rc::clone(fst),
            cod: Rc::new(code_ty.clone()),
        };
        let ty = Type::Pi {
            dom_level: l.clone(),
            cod_level: inner_level.clone(),
            dom: Rc::clone(d_ty),
            cod: Rc::new(inner.clone()),
        };
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: inner_level.clone(),
            dom: Rc::clone(d_ty),
            body: Rc::new(Term::Lam {
                dom_level: fst_level.clone(),
                cod_level: code_level.clone(),
                dom: Rc::clone(fst),
                body: Rc::new(crate::code::code_of(snd)?),
            }),
        };
        let level = Level::max(l.clone(), inner_level.clone());
        self.push_gen_def(key, &ind.name, ty, level, body, span)
            .ok()?;
        // The occurrence, scoped in `·, v, x` — one binder past `vcx`, which
        // is where the Σ's tail lives.
        let mut xcx = vcx.clone();
        xcx.push("x".to_string(), (**fst).clone(), fst_level.clone());
        let fun = self.gen_ref(&xcx, key)?;
        let at_v = Term::App {
            fun: Rc::new(fun),
            dom_level: l.clone(),
            cod_level: inner_level,
            dom: Rc::new(weaken(&d_ty.shift_global(1), &xcx.gamma)),
            cod: Rc::new(under_binder(&inner.shift_global(1), &xcx.gamma)),
            arg: Rc::new(Term::Var(LocalVar(1))),
        };
        Some(Rc::new(Type::El {
            level: snd_level.clone(),
            tm: Rc::new(Term::App {
                fun: Rc::new(at_v),
                dom_level: fst_level.clone(),
                cod_level: code_level,
                dom: Rc::new(fst.shift_global(1).shift_local(1)),
                cod: Rc::new(code_ty.shift_local(1)),
                arg: Rc::new(Term::Var(LocalVar(0))),
            }),
        }))
    }

    /// Push one `Π(v : ⟦D⟧). cod` definition whose body is `λ(v : ⟦D⟧). node`,
    /// and answer with `key^δ v` — the reference that stands for `node` in
    /// everything built afterwards. `None` if the gate refused it, which is
    /// [`Elaborator::register_rec_projs`]'s cue to stop and leave the rest
    /// inline.
    ///
    /// Everything handed in is scoped in `·, v` (or, for `dom`, in `·`) and in
    /// the Ψ *before* the push; the reference that comes back is scoped in the
    /// Ψ after it, so a caller that keeps anything else across the call has to
    /// [`shift_global`](Type::shift_global) it by one.
    #[allow(clippy::too_many_arguments)]
    fn push_proj_def(
        &mut self,
        key: GenDef,
        ind: &Rc<Inductive>,
        dom: &Rc<Type>,
        dom_level: &Level,
        cod: &Type,
        cod_level: &Level,
        node: &Rc<Term>,
        vcx: &Cx,
        span: Span,
    ) -> Option<Rc<Term>> {
        let ty = Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::new(cod.clone()),
        };
        let body = Term::Lam {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            body: Rc::clone(node),
        };
        let level = Level::max(dom_level.clone(), cod_level.clone());
        self.push_gen_def(key, &ind.name, ty, level, body, span)
            .ok()?;
        let fun = self.gen_ref(vcx, key)?;
        Some(Rc::new(Term::App {
            fun: Rc::new(fun),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(weaken(&dom.shift_global(1), &vcx.gamma)),
            // The `App`'s codomain is scoped under its own binder, one entry
            // past `vcx`.
            cod: Rc::new(under_binder(&cod.shift_global(1), &vcx.gamma)),
            arg: Rc::new(Term::Var(LocalVar(0))),
        }))
    }

    /// `D#projⱼ^δ v` and its type, for a projection of field `idx` off `value`
    /// (`issues/theorem-field-projection-oom.md`). `None` when the record has
    /// no registered projection — every such site keeps the inline walk.
    pub(crate) fn rec_proj_ref(
        &self,
        cx: &Cx,
        tag: u32,
        idx: usize,
        value: &Rc<Term>,
    ) -> Option<(Term, Type, Level)> {
        let key = GenDef::RecProj(tag, idx);
        let fun = self.gen_ref(cx, key)?;
        // The Π is read back out of Ψ rather than remembered from the
        // registration: a stored copy would carry the global indices of the
        // Ψ it was built in, and every declaration since has moved them. The
        // reference's own variable gives the rescoping, exactly as it does for
        // a binding's type in `typing.rs` (`shift_global(v + 1)`).
        let Term::GlobalTm { var, .. } = &fun else {
            return None;
        };
        let abs = *self.types.gdefs().abs_for(&key)? as usize;
        let GlobalBinding::Tm { ty, .. } = self.psi.bindings.get(abs)? else {
            return None;
        };
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } = ty.shift_global(var.0 + 1)
        else {
            return None;
        };
        let tm = Term::App {
            fun: Rc::new(fun),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(weaken(&dom, &cx.gamma)),
            cod: Rc::new(under_binder(&cod, &cx.gamma)),
            arg: Rc::clone(value),
        };
        let ty = instantiate(&cod, Rc::clone(value), &cx.gamma);
        Some((tm, ty, cod_level))
    }

    /// `D#shape := ⌜S⌝` and `D#arity := λ(x : El (D#shape^δ)). n`, for a
    /// **recursive** declaration whose lowering is `Wf(x : S). n`
    /// (`docs/wf-shape-code-design.md` §2.1). Runs off `register_ty_code`'s own
    /// lowering, so it inherits that function's boundary verbatim
    /// (unparameterized, unindexed, `tag_of`-routes-back) and the two
    /// registrations always agree about what `⟦D⟧` is.
    ///
    /// Best-effort like every other piece here, and **all-or-nothing**: the
    /// guard entry is written only when both definitions passed the gate, so a
    /// half-registered pair can never hand out half a spelling.
    fn register_wf_slots(&mut self, ind: &Rc<Inductive>, d_ty: &Type, l: &Level, span: Span) {
        let Type::Wf { shape, arity, .. } = d_ty else {
            // Non-recursive: a sum-of-Σs has no slots to name. `TyCode` is the
            // whole story there.
            return;
        };
        let skey = GenDef::ShapeCode(ind.tag);
        let akey = GenDef::ArityFn(ind.tag);
        if self.types.gdefs().contains_key(&skey)
            || self.types.gdefs().contains_key(&akey)
        {
            return;
        }
        let Some(scode) = crate::code::code_of(shape) else {
            return;
        };
        if self
            .push_gen_def(
                skey,
                &ind.name,
                Type::Ty(l.clone()),
                Level::succ(l.clone()),
                scode.clone(),
                span,
            )
            .is_err()
        {
            return;
        }
        // The λ's domain is the shape *reference* just registered: the arity
        // definition is the one place where writing the shape out again would
        // undo half of what this pair buys.
        let cx = Cx::empty();
        let Some(sref) = self.gen_type_ref(&cx, skey, l) else {
            return;
        };
        let ty = Type::Pi {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(sref.clone()),
            cod: Rc::new(Type::Nat),
        };
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(sref),
            body: Rc::clone(arity),
        };
        if self
            .push_gen_def(akey, &ind.name, ty, l.clone(), body, span)
            .is_ok()
        {
            let shape_decoded = Rc::new(Type::El {
                level: l.clone(),
                tm: Rc::new(scode),
            });
            self.semantic_commit_gen_wf_slots(
                ind.tag,
                WfSlots {
                    shape: Rc::clone(shape),
                    shape_decoded,
                    arity: Rc::clone(arity),
                    level: l.clone(),
                },
            );
        }
    }

    /// `El (D#shape^δ)` and `app(D#arity^δ; x₀)` for a `Wf`'s slot pair, if and
    /// only if the pair in front of us **is** the one the two definitions were
    /// minted from (design §2.3's guard). `None` is every emission site's cue
    /// to keep the slots inline, exactly as before.
    ///
    /// The shape reference is scoped in `cx`; the arity reference is scoped one
    /// binder deeper, because an arity slot is always read under the shape's
    /// own binder (`x : S`) — that asymmetry is the whole of the bookkeeping
    /// here, and getting it wrong is a kernel `SubstMismatch`, not a wrong
    /// answer.
    pub(crate) fn wf_slot_refs(&self, cx: &Cx, shape: &Type, arity: &Term) -> Option<(Type, Term)> {
        if !self.types.gdefs().has_wf_slots() {
            return None;
        }
        let ind = self.tag_of(shape)?;
        let slots = self.types.gdefs().wf_slots(&ind.tag)?;
        let l = &slots.level;
        if (*slots.shape != *shape && *slots.shape_decoded != *shape) || *slots.arity != *arity {
            return None;
        }
        let sref = self.gen_type_ref(cx, GenDef::ShapeCode(ind.tag), l)?;
        let fun = self.gen_ref_deeper(cx, GenDef::ArityFn(ind.tag), 1)?;
        let aref = Term::App {
            fun: Rc::new(fun),
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(sref.shift_local(1)),
            // `Nat` binds nothing, so the `App`'s codomain needs no shift.
            cod: Rc::new(Type::Nat),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        Some((sref, aref))
    }

    /// `El l (D#tycode^δ)` for `inline`, if and only if `inline` **is** the
    /// lowering `D#tycode` was minted from (design §1.3 + the guard note on
    /// [`GenDefs::ty_code`]). `None` is every emission site's cue to keep
    /// writing the type out, exactly as before.
    pub(crate) fn ty_type_ref(&self, cx: &Cx, tag: u32, inline: &Type) -> Option<Type> {
        let (registered, level) = self.types.gdefs().ty_code(&tag)?;
        if **registered != *inline {
            return None;
        }
        self.gen_type_ref(cx, GenDef::TyCode(tag), level)
    }

    /// [`Self::ty_type_ref`] with the tag read out of the type instead of
    /// supplied: `Some(El (D#tycode^δ))` when `ty` **is** some declaration's
    /// registered lowering, `None` otherwise.
    ///
    /// Two filters, both needed. `tag_of` is a *structural* read and will walk
    /// into a `Sum`/`Σ` to find a tag, so it can name a declaration whose
    /// `⟦D⟧` is not `ty` at all; the structural comparison inside
    /// `ty_type_ref` is what turns that into a decline rather than a wrong
    /// reference. And `tag_of` goes through `decoded`, which leaves an `El` of
    /// a neutral code exactly as it is — so an already-reference-spelled type
    /// declines here too, and this is idempotent.
    pub(crate) fn respell_ty(&self, cx: &Cx, ty: &Type) -> Option<Type> {
        let ind = self.tag_of(ty)?;
        self.ty_type_ref(cx, ind.tag, ty)
    }

    /// [`Self::respell_ty`] applied **component-wise**
    /// (`docs/annotation-component-respell-design.md`): rebuild `ty` with
    /// every sub-type that *is* a registered declaration's lowering replaced
    /// by its `El (D#tycode^δ)` reference. `None` when nothing respelled, so
    /// callers keep their original (and its sharing) untouched.
    ///
    /// `depth` is how many binders `ty` sits under, past `cx` — the reference
    /// is minted against `cx` and shifted by `depth` plus however many binders
    /// the walk itself crosses (`Pi` cod, `Sigma` snd). Sound because a type
    /// that compares equal to the registry's **closed** copy is itself closed,
    /// so the shift only fixes the substitution tail's length, exactly as the
    /// `match`-motive respell's `shift_local(1)` does.
    ///
    /// Only **type** components are walked (`Pi`, `Sigma`, `Sum`, `Vec` elem,
    /// `Wf` shape, `Id`/`SEq` ty). Terms inside types — `Id` endpoints, `Vec`
    /// lengths, `El` codes — are not: annotations live in type slots, and the
    /// statement-side cascade (design §2.1) makes newly emitted terms small at
    /// the source. An `El`-headed reference declines at the top (`respell_ty`
    /// is idempotent) and has no walked components, so this is idempotent too.
    pub(crate) fn respell_ty_deep(&self, cx: &Cx, ty: &Type, depth: u32) -> Option<Type> {
        if !self.types.gdefs().has_ty_codes() {
            return None;
        }
        self.respell_deep_at(cx, ty, depth)
    }

    fn respell_deep_at(&self, cx: &Cx, ty: &Type, d: u32) -> Option<Type> {
        if let Some(r) = self.respell_ty(cx, ty) {
            return Some(if d == 0 { r } else { r.shift_local(d) });
        }
        // One arm per former with type components; `or` keeps the sibling
        // untouched (sharing preserved) when only one side respells.
        let or = |orig: &Rc<Type>, new: Option<Type>| match new {
            Some(t) => Rc::new(t),
            None => Rc::clone(orig),
        };
        match ty {
            Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } => {
                let ndom = self.respell_deep_at(cx, dom, d);
                let ncod = self.respell_deep_at(cx, cod, d + 1);
                if ndom.is_none() && ncod.is_none() {
                    return None;
                }
                Some(Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: or(dom, ndom),
                    cod: or(cod, ncod),
                })
            }
            Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } => {
                let nfst = self.respell_deep_at(cx, fst, d);
                let nsnd = self.respell_deep_at(cx, snd, d + 1);
                if nfst.is_none() && nsnd.is_none() {
                    return None;
                }
                Some(Type::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: or(fst, nfst),
                    snd: or(snd, nsnd),
                })
            }
            Type::Sum {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
            } => {
                let nl = self.respell_deep_at(cx, lhs, d);
                let nr = self.respell_deep_at(cx, rhs, d);
                if nl.is_none() && nr.is_none() {
                    return None;
                }
                Some(Type::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: or(lhs, nl),
                    rhs: or(rhs, nr),
                })
            }
            Type::Vec { level, elem, len } => {
                let ne = self.respell_deep_at(cx, elem, d)?;
                Some(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(ne),
                    len: Rc::clone(len),
                })
            }
            Type::Wf {
                level,
                shape,
                arity,
            } => {
                // Reached only for a lowering the registry does not name
                // (parameterized, hence monomorphized — `Box<Ir>`), whose
                // *components* may still be registered lowerings.
                let ns = self.respell_deep_at(cx, shape, d)?;
                Some(Type::Wf {
                    level: level.clone(),
                    shape: Rc::new(ns),
                    arity: Rc::clone(arity),
                })
            }
            Type::Id {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.respell_deep_at(cx, ty, d)?;
                Some(Type::Id {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            Type::SEq {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.respell_deep_at(cx, ty, d)?;
                Some(Type::SEq {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            _ => None,
        }
    }

    /// `El (D#tycode^δ)` back to the registry's inline `⟦D⟧`, at the head only
    /// and in the **current** Ψ world (goal and meta padding included, which is
    /// what [`Self::gen_def_of`] knows and [`Self::unspell_ty_deep`]'s explicit
    /// anchor deliberately does not assume).
    ///
    /// This is the elaborator's `whnf` of a reference
    /// (`docs/wf-shape-code-design.md` §3.3): δ+decode gives a type that is
    /// *convertible* to the registry's copy but spelled `Wf(El ⌜S⌝). n`, and
    /// the inline copy is the identity every structural reader and every
    /// use-site guard is written against. Closed by construction, so nothing
    /// is shifted.
    pub(crate) fn unspell_here(&self, ty: &Type) -> Option<Type> {
        if !self.types.gdefs().has_ty_codes() {
            return None;
        }
        let Type::El { tm, .. } = ty else { return None };
        let Term::GlobalTm { var, .. } = &**tm else {
            return None;
        };
        let GenDef::TyCode(tag) = self.gen_def_of(*var)? else {
            return None;
        };
        self.types
            .gdefs()
            .ty_code(&tag)
            .map(|(inline, _)| (**inline).clone())
    }

    /// `El (D#shape^δ)` back to the inline shape registered for a recursive
    /// declaration. This is the shape-slot counterpart of [`Self::unspell_here`]
    /// and exists for display only: a `Wf` annotation may carry the generated
    /// reference even though the nominal tag and constructor spine live in the
    /// inline shape (issues/display-inductive-type-arguments.md).
    pub(crate) fn unspell_shape_here(&self, ty: &Type) -> Option<Type> {
        if !self.types.gdefs().has_wf_slots() {
            return None;
        }
        let Type::El { tm, .. } = ty else { return None };
        let Term::GlobalTm { var, .. } = &**tm else {
            return None;
        };
        let GenDef::ShapeCode(tag) = self.gen_def_of(*var)? else {
            return None;
        };
        self.types
            .gdefs()
            .wf_slots(&tag)
            .map(|slots| (*slots.shape).clone())
    }

    /// The **inverse** of [`Self::respell_ty_deep`], for the reflection
    /// boundary (`Elaborator::fn_type_code`): rebuild `ty` with every
    /// `El (D#tycode^δ)` reference replaced by the registry's inline lowering.
    /// `None` when nothing unspelled.
    ///
    /// Why it exists: a `meta` analyzer reads a fn's statement *as code*, and
    /// at layer m a global reference is syntax — `box (u^δ)` never unfolds,
    /// by design — so the reference spelling that shrinks every kernel
    /// checking of the statement makes it *opaque to analysis*. The
    /// opaque-globals round already drew the line ("unfolding-for-analysis
    /// happens at the reflection boundary"), and this is that unfolding for
    /// the generated codes: the registry's copy is exactly what δ+decode of
    /// the reference yields, so the analyzer sees the very type it saw
    /// before the respell existed. Closed types, so no depth bookkeeping.
    ///
    /// `len_at` anchors the reference resolution: the Ψ length the type's
    /// `GlobalVar`s count from — the *current* length for a type rescoped by
    /// `shift_global` (`fn_type_code`), the binding's own `abs` for a raw
    /// prefix-scoped statement (`sig_peel` over `global_body`). Goal and
    /// meta padding never applies to either, which is why this does not go
    /// through [`Self::gen_def_of`].
    pub(crate) fn unspell_ty_deep(&self, len_at: u32, ty: &Type) -> Option<Type> {
        if !self.types.gdefs().has_ty_codes() {
            return None;
        }
        if let Type::El { tm, .. } = ty
            && let Term::GlobalTm { var, .. } = &**tm
            && let Some(abs) = var.0.checked_add(1).and_then(|v| len_at.checked_sub(v))
            && let Some(GenDef::TyCode(tag)) = self.types.gdefs().key_for_abs(&abs).copied()
            && let Some((inline, _)) = self.types.gdefs().ty_code(&tag)
        {
            return Some((**inline).clone());
        }
        let or = |orig: &Rc<Type>, new: Option<Type>| match new {
            Some(t) => Rc::new(t),
            None => Rc::clone(orig),
        };
        match ty {
            Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } => {
                let ndom = self.unspell_ty_deep(len_at, dom);
                let ncod = self.unspell_ty_deep(len_at, cod);
                if ndom.is_none() && ncod.is_none() {
                    return None;
                }
                Some(Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: or(dom, ndom),
                    cod: or(cod, ncod),
                })
            }
            Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } => {
                let nfst = self.unspell_ty_deep(len_at, fst);
                let nsnd = self.unspell_ty_deep(len_at, snd);
                if nfst.is_none() && nsnd.is_none() {
                    return None;
                }
                Some(Type::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: or(fst, nfst),
                    snd: or(snd, nsnd),
                })
            }
            Type::Sum {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
            } => {
                let nl = self.unspell_ty_deep(len_at, lhs);
                let nr = self.unspell_ty_deep(len_at, rhs);
                if nl.is_none() && nr.is_none() {
                    return None;
                }
                Some(Type::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: or(lhs, nl),
                    rhs: or(rhs, nr),
                })
            }
            Type::Vec { level, elem, len } => {
                let ne = self.unspell_ty_deep(len_at, elem)?;
                Some(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(ne),
                    len: Rc::clone(len),
                })
            }
            Type::Wf {
                level,
                shape,
                arity,
            } => {
                let ns = self.unspell_ty_deep(len_at, shape)?;
                Some(Type::Wf {
                    level: level.clone(),
                    shape: Rc::new(ns),
                    arity: Rc::clone(arity),
                })
            }
            Type::Id {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.unspell_ty_deep(len_at, ty)?;
                Some(Type::Id {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            Type::SEq {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.unspell_ty_deep(len_at, ty)?;
                Some(Type::SEq {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            _ => None,
        }
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
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let Ok((ty, level, body, l, ilvl)) = self.fam_def(ind, span) else {
            return;
        };
        if self
            .push_gen_def(key, &ind.name, ty, level, body, span)
            .is_ok()
        {
            self.semantic_commit_gen_fam_levels(ind.tag, l, ilvl);
        }
    }

    /// §7.1's tag predicates and §7.2's child projections, per index
    /// constructor. Memoized on the *index* type's tag, so the second family
    /// over one index pays nothing.
    fn register_index_devices(&mut self, iind: &Rc<Inductive>, span: Span) {
        let n = iind.ctors.len();
        for k in 0..n {
            let key = GenDef::IdxTag(iind.tag, k);
            if !self.types.gdefs().contains_key(&key) {
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
                if self.types.gdefs().contains_key(&key) {
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
        if self.types.gdefs().contains_key(&key) {
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
        {
            // A generated definition faces the same gate as a `fn` and the same
            // oracle (`gate.rs`): it is an ordinary bodied binding, so it gets
            // its own cache identity rather than riding its declaration
            // (docs/cache-v1-design.md §4).
            let item = crate::gate::GateItem {
                name: &name,
                ctx: &empty,
                ty: &ty,
                level: &level,
                body: &body,
                opaque: false,
                layer: Layer::Code,
                lands_in_psi: true,
            };
            if !self
                .gate
                .as_ref()
                .is_some_and(|g| g.admits(&self.psi, &item))
            {
                // `stats::time_kernel`, as at the `elab_decl_inner` gate
                // (lib.rs) and the `Layer::Meta` one (quote.rs): the frontend
                // suite's `kernel` phase covers *every* finished declaration,
                // and a generated definition is one
                // (issues/gendef-gate-untimed.md).
                crate::stats::time_kernel(|| {
                    self.kernel_check_type(&self.psi, Layer::Prog, &empty, &ty, &level)
                })
                .map_err(|err| crate::ElabError::Kernel {
                    decl: name.clone(),
                    span,
                    err,
                    note: None,
                })?;
                crate::stats::time_kernel(|| {
                    self.kernel_check_term(&self.psi, Layer::Code, &empty, &body, &ty, &level)
                })
                .map_err(|err| crate::ElabError::Kernel {
                    decl: name.clone(),
                    span,
                    err,
                    note: None,
                })?;
                if let Some(g) = self.gate.as_ref() {
                    g.accepted(&self.psi, &item);
                }
            }
        }
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(GlobalBinding::defined_tm(
            empty,
            Layer::Code,
            Rc::new(ty),
            level,
            Rc::new(body),
        ));
        self.semantic_commit_gen_def(key, abs);
        self.refresh_delta_psi();
        Ok(())
    }

    // -- reference and read-back --------------------------------------------

    /// `u^δ` for a registered definition, out of the current `Γ`. `None` when
    /// the definition was not registered, which is every emission site's cue
    /// to inline instead.
    pub(crate) fn gen_ref(&self, cx: &Cx, key: GenDef) -> Option<Term> {
        self.gen_ref_deeper(cx, key, 0)
    }

    /// [`Self::gen_ref`] for an occurrence sitting `extra` binders past `cx` —
    /// the substitution tail's length is the only thing that moves, since the
    /// definition is closed and its Ψ index is context-independent. One caller:
    /// the arity slot, which is always read under the shape's binder.
    fn gen_ref_deeper(&self, cx: &Cx, key: GenDef, extra: u32) -> Option<Term> {
        let abs = *self.types.gdefs().abs_for(&key)?;
        let len = self.psi.bindings.len() as u32;
        // Goals sit innermost, exactly as in `resolve` — and so do a
        // `meta fn`'s Ψ-extending binders (`Ctx`, `lib.rs`'s `meta_pushed`),
        // which `resolve` has always offset by and this did not. Latent until
        // 2026-08-12: nothing emitted a generated-definition reference from
        // inside a meta body before the tier-1 motive respell did, and the
        // symptom was a kernel `WrongGlobalBinding` naming the context binder
        // (`crates/elab/tests/certgen_route1_spike.rs`'s meta walk over `Ir`).
        // The two paddings never combine: goals are refused inside a `meta fn`.
        let var = GlobalVar(len - 1 - abs + self.attempt.goal_arena.base() + self.meta_offset());
        Some(Term::GlobalTm {
            var,
            subst: LocalSubst {
                tail: SubstTail::Empty {
                    len: cx.gamma.entries.len() as u32 + extra,
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
        self.gen_ref(cx, key).map(|tm| Type::El {
            level: level.clone(),
            tm: Rc::new(tm),
        })
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
            .checked_add(self.attempt.goal_arena.base())?
            .checked_add(self.meta_offset())?
            .checked_sub(var.0.checked_add(1)?)?;
        self.types.gdefs().key_for_abs(&abs).copied()
    }

    /// How far a `meta fn`'s Ψ-extending binders push the committed bindings
    /// out, mirroring `resolve`'s `meta_off` (`lib.rs`). Zero everywhere else.
    fn meta_offset(&self) -> u32 {
        self.meta_pushed.borrow().len() as u32
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
            return crate::err(
                "internal: a parameterized forded family keeps its inlined μ",
                span,
            );
        }
        let cx = Cx::empty();
        let skel = ind
            .skel
            .as_ref()
            .expect("a forded declaration has a skeleton");
        let (skel_ty, l) = self.lower_instance(&cx, skel, &[], &[], span)?;
        let (ity, ilvl) = self.index_type_of(&cx, ind, span)?;
        let node = self.build_mu(&cx, ind, skel, &skel_ty, &l, &ity, &ilvl, span)?;
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(skel_ty.clone()),
            body: Rc::new(
                crate::indexed::set_scrut(&node.shift_local(1), Rc::new(Term::Var(LocalVar(0))))
                    .ok_or_else(|| crate::ElabError::Elab {
                        msg: "internal: a μ node has a scrutinee slot".into(),
                        span,
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
        let (l, ilvl) = self.types.gdefs().fam_levels(&ind.tag)?.clone();
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
        Some((
            Type::El {
                level: l.clone(),
                tm: Rc::new(tm),
            },
            l,
        ))
    }

    /// `is_k = λ(z : I). Case-on-tag(z) { c_k ↦ ⌜Unit⌝ ; _ ↦ ⌜Empty⌝ }` (§7.1),
    /// at type `I → Type⁰`.
    fn tag_pred_def(&self, iind: &Rc<Inductive>, k: usize, span: Span) -> R<(Type, Level, Term)> {
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

// -- scope moves for the record projections ---------------------------------
//
// A projection definition is closed and its codomain is scoped in the
// one-entry context `·, v : ⟦D⟧`, while a use site lives in some `Γ`. All
// three moves below are one `LocalSubst` into that context — written out
// rather than reached through `shift_local`, which would leave the tail's
// *base* at `·` and so cannot re-scope into a `Γ` standing on a context
// variable (`issues/theorem-field-projection-oom.md`).

/// A type scoped in `·`, seen in `Γ`.
fn weaken(ty: &Type, gamma: &LocalCtx) -> Type {
    ty.apply_local(&LocalSubst {
        tail: SubstTail::Empty {
            len: gamma.entries.len() as u32,
            base: gamma.base,
        },
        terms: vec![],
    })
}

/// A type scoped in `·, x`, seen in `Γ, x` — the annotation an `App` carries
/// for a *dependent* codomain.
fn under_binder(ty: &Type, gamma: &LocalCtx) -> Type {
    ty.apply_local(&LocalSubst {
        tail: SubstTail::Empty {
            len: gamma.entries.len() as u32 + 1,
            base: gamma.base,
        },
        terms: vec![Rc::new(Term::Var(LocalVar(0)))],
    })
}

/// `El (D#famⱼ^δ v x)` with `x` instantiated at `arg` — the tail family's
/// annotation applied, which is the type of the `snd` node at that entry.
/// Both are scoped in `Γ = ·, v`.
fn instantiate_fam(fam: &Rc<Type>, arg: &Rc<Term>, gamma: &LocalCtx) -> Type {
    fam.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg)))
}

/// A type scoped in `·, x`, instantiated at `arg` in `Γ`.
fn instantiate(ty: &Type, arg: Rc<Term>, gamma: &LocalCtx) -> Type {
    ty.apply_local(&LocalSubst {
        tail: SubstTail::Empty {
            len: gamma.entries.len() as u32,
            base: gamma.base,
        },
        terms: vec![arg],
    })
}
