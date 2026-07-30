//! Indexed families, route 1: the family by large elimination on the index.
//!
//! This module is the mechanization of `docs/inductive-indexed-lowering.md`,
//! and is meant to be read against it — the section numbers in the comments
//! are that document's, and `crates/elab/tests/indexed_route1.rs` is the hand
//! prototype whose terms this generator emits. The doctrine is the tiers'
//! (`inductive.rs`): the lowering is untrusted, the kernel re-checks every
//! emitted term, and a bug here produces a checked theorem about the wrong
//! type — so no clever shortcuts, and annotations are read off the type being
//! eliminated wherever one exists.
//!
//! The scheme in one line (§4): `⟦D⟧` is `elim_Nat` at motive `Ty l` with one
//! branch of *codes* per index-constructor class, `El rec` spliced for a
//! recursive field, and the pattern-variable field elided — it **is** the
//! branch's `elim_Nat` binder, not payload (§4.1). A use `D<ā>(e)` is
//! `El (fam ⟦e⟧)`; there is no Σ over the index and no un-applied `⟦D⟧`.

use std::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_syntax::ast::{Arm, Expr, ExprKind, Span};

use crate::inductive::{inject, FieldKind, IdxPat, Inductive, Spine};
use crate::{code, err, Alias, Cx, Elaborator, Guard, GuardKind, R};

/// A type in **family form**: `El^l (elim_Nat(_. Ty l; base; step; idx))`,
/// read back into its parts. This is the indexed analogue of `tag_of` — the
/// form every indexed lowering emits and every indexed consumer reads.
pub(crate) struct IndexedFam {
    pub level: Level,
    /// The `Zero`-class branch code, scoped where the type was.
    pub base: Rc<Term>,
    /// The `Succ`-class branch code, scoped two deeper (`m`, `rec`).
    pub step: Rc<Term>,
    /// The index the family is applied at.
    pub idx: Rc<Term>,
}

impl IndexedFam {
    /// The family re-applied at another index, `by` binders deeper — how the
    /// eliminator names `fam 0`, `fam (S m)` and `fam h` from one read-back
    /// type. The branches are shifted as parts of a whole `elim_Nat` node —
    /// never detached, since a detached `step` reads its own `m`/`rec`
    /// binders as free variables and a bare shift would move them.
    pub fn at(&self, idx: Term, by: u32) -> Term {
        let whole = Term::ElimNat {
            level: Level::succ(self.level.clone()),
            motive: Rc::new(Type::Ty(self.level.clone())),
            base: Rc::clone(&self.base),
            step: Rc::clone(&self.step),
            // A closed placeholder: the real index is scoped at the *target*
            // depth and must not be shifted with the branches.
            scrut: Rc::new(Term::Zero),
        };
        let Term::ElimNat { level, motive, base, step, .. } = whole.shift_local(by) else {
            unreachable!("shifting preserves the head constructor")
        };
        Term::ElimNat { level, motive, base, step, scrut: Rc::new(idx) }
    }

    pub fn el_at(&self, idx: Term, by: u32) -> Type {
        Type::El { level: self.level.clone(), tm: Rc::new(self.at(idx, by)) }
    }
}

/// The nominal tag of a *code* spine: `read_tag` (`inductive.rs` §3.3) with
/// every former replaced by its code. Walks to the leftmost `TmSum` summand,
/// expects a `TmSigma` whose first component is the tag's code, and decodes
/// the binary digits.
fn read_tag_code(t: &Term) -> Option<u32> {
    fn digits(t: &Term) -> Option<u32> {
        match t {
            Term::TmUnit { .. } => Some(0),
            Term::TmSigma { fst, snd, .. } => {
                let d = match &**fst {
                    Term::TmUnit { .. } => 0,
                    Term::TmSigma { fst, snd, .. }
                        if matches!(**fst, Term::TmUnit { .. })
                            && matches!(**snd, Term::TmUnit { .. }) =>
                    {
                        1
                    }
                    _ => return None,
                };
                digits(snd)?.checked_mul(2)?.checked_add(d)
            }
            _ => None,
        }
    }
    let mut cur = t;
    while let Term::TmSum { lhs, .. } = cur {
        cur = lhs;
    }
    let Term::TmSigma { fst, .. } = cur else { return None };
    digits(fst)
}

/// The constructor indices of each index-constructor class, in declaration
/// order: (`Zero`-class, `Succ`-class).
fn classes(ind: &Inductive) -> (Vec<usize>, Vec<usize>) {
    let mut zero = Vec::new();
    let mut succ = Vec::new();
    for (i, c) in ind.ctors.iter().enumerate() {
        match c.res {
            Some(IdxPat::Zero) => zero.push(i),
            Some(IdxPat::Succ { .. }) => succ.push(i),
            None => unreachable!("an indexed declaration's ctors all carry a pattern"),
        }
    }
    (zero, succ)
}

/// Everything an indexed `match` arm needs beyond what a tier-0 arm does:
/// where the eliminator's `m` and `rec` binders sit (absolute positions), the
/// motive to instantiate ih types from, and the self-call guard ingredients.
struct IdxArmEnv {
    /// Absolute position of the step's index binder `m`.
    m_pos: usize,
    /// Absolute position of the step's recursion binder `rec`.
    rec_pos: usize,
    level: Level,
    mlvl: Level,
    /// The motive over `(Γ, h, z)`; `gamma_len` is `|Γ|`, for re-scoping it.
    motive: Type,
    gamma_len: usize,
    /// `descends_on_param` of the scrutinee, if the `match` is on one of the
    /// enclosing declaration's own parameters.
    dec: Option<usize>,
    /// The index parameter a self-call *rebinds* to the arm's pattern
    /// variable (§6): `(its parameter position, m_pos)`.
    rebind: Option<(usize, usize)>,
    outer_guard: Option<Rc<Guard>>,
}

impl IdxArmEnv {
    /// `M[h, z]`, with `h`/`z` scoped `extra` binders past Γ.
    fn mot_at(&self, gamma: &heather_kernel::term::LocalCtx, h: Term, z: Term, extra: u32) -> Type {
        self.motive.apply_local(
            &LocalSubst::id(gamma)
                .shift_local(extra)
                .extended(Rc::new(h))
                .extended(Rc::new(z)),
        )
    }
}

impl Elaborator {
    /// Read a type back as a family form, when it is one of a declared
    /// indexed inductive. `None` for everything else — including the same
    /// family *reduced* at a literal index, which has lost its index and is
    /// diagnosed by the consumers that need it.
    pub(crate) fn indexed_of(&self, ty: &Type) -> Option<(Rc<Inductive>, IndexedFam)> {
        let Type::El { level, tm } = ty else { return None };
        let Term::ElimNat { motive, base, step, scrut, .. } = &**tm else { return None };
        if !matches!(&**motive, Type::Ty(_)) {
            return None;
        }
        let tag = read_tag_code(base).or_else(|| read_tag_code(step))?;
        let ind = self.by_tag.get(&tag)?;
        ind.index.as_ref()?;
        Some((
            Rc::clone(ind),
            IndexedFam {
                level: level.clone(),
                base: Rc::clone(base),
                step: Rc::clone(step),
                idx: Rc::clone(scrut),
            },
        ))
    }

    /// `D<ā>(e)` written in type position (§2). The parser's backtracking
    /// delivers it as an *expression* (an applied type is never called, so
    /// the call is the index application); this recognizes the shape before
    /// `OfExpr`'s generic infer-and-decode path would try to call `D`.
    pub(crate) fn try_indexed_ty(
        &self,
        cx: &Cx,
        e: &Expr,
        span: Span,
    ) -> R<Option<(Type, Level)>> {
        let ExprKind::App { head, args, .. } = &e.kind else { return Ok(None) };
        let Some((name, targs)) = crate::inductive::named_head(head) else {
            return Ok(None);
        };
        let Some(ind) = self.inductives.get(name).cloned() else { return Ok(None) };
        if ind.index.is_none() {
            return Ok(None);
        }
        let [idx] = args.as_slice() else {
            return err(format!("`{name}` takes exactly one index"), span);
        };
        if targs.len() != ind.params.len() {
            return err(
                format!(
                    "`{name}` takes {} type argument(s), found {}",
                    ind.params.len(),
                    targs.len()
                ),
                span,
            );
        }
        let mut lowered = Vec::with_capacity(targs.len());
        for a in targs {
            lowered.push(self.elab_ty(cx, a)?);
        }
        let idx_t = self.elab_check(cx, idx, &Type::Nat, &Level::Zero)?;
        self.lower_indexed_instance(cx, &ind, &lowered, idx_t, span).map(Some)
    }

    /// `⟦D<ā>(e)⟧ = El^l (fam ⟦e⟧)` (§4). Two passes: the branch shapes are
    /// built once at a placeholder level to *compute* `l` (only the empty
    /// branch's `Empty^l` and the recursive `El^l rec` components mention it,
    /// and neither contributes beyond the payload join), then rebuilt at `l`.
    pub(crate) fn lower_indexed_instance(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        idx: Term,
        span: Span,
    ) -> R<(Type, Level)> {
        let (zero, succ) = classes(ind);
        let (_, l0) = self.indexed_class_shape(cx, ind, &zero, args, &Level::Zero, false, span)?;
        let (_, l1) = self.indexed_class_shape(cx, ind, &succ, args, &Level::Zero, true, span)?;
        let l = Level::max(l0, l1);
        let (base_ty, _) = self.indexed_class_shape(cx, ind, &zero, args, &l, false, span)?;
        let (step_ty, _) = self.indexed_class_shape(cx, ind, &succ, args, &l, true, span)?;
        let no_code = |which: &str| {
            crate::ElabError::Elab {
                msg: format!(
                    "a field of `{}`'s {which} class has no type code, so it cannot \
                     appear in an indexed family (docs/inductive-indexed-lowering.md §3)",
                    ind.name
                ),
                span,
            }
        };
        let base = code::code_of(&base_ty).ok_or_else(|| no_code("`0`"))?;
        let step = code::code_of(&step_ty).ok_or_else(|| no_code("`Succ`"))?;
        let fam = Term::ElimNat {
            level: Level::succ(l.clone()),
            motive: Rc::new(Type::Ty(l.clone())),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::new(idx),
        };
        Ok((Type::El { level: l.clone(), tm: Rc::new(fam) }, l))
    }

    /// One class's branch as a **type**: the tag spine of its members (tier 0
    /// §3, via the same Σ/Sum folds), with the pattern-variable field elided
    /// (it aliases the `elim_Nat` binder `m`) and each recursive field an
    /// `El rec` (§4). For the `Succ` class the result is scoped `(Γ, m, rec)`;
    /// `code_of` then quotes it into the step code, `Var`s and all.
    fn indexed_class_shape(
        &self,
        cx: &Cx,
        ind: &Inductive,
        members: &[usize],
        args: &[(Type, Level)],
        l: &Level,
        step: bool,
        span: Span,
    ) -> R<(Type, Level)> {
        // The branch context: `m` and `rec` for the step, nothing for the
        // base. Type-parameter instantiations stay scoped in `cx`; their
        // `TyVar.depth` mechanics absorb the two extra binders.
        let mut bcx = cx.clone();
        let (m_pos, rec_pos) = (cx.names.len(), cx.names.len() + 1);
        if step {
            bcx.push("#idx".into(), Type::Nat, Level::Zero);
            bcx.push("#rec".into(), Type::Ty(l.clone()), Level::succ(l.clone()));
        }
        if members.is_empty() {
            // `Fin`'s `fam 0` (§4): a correct branch, not a degenerate one.
            return Ok((Type::Empty { level: l.clone() }, l.clone()));
        }
        let mut parts = Vec::with_capacity(members.len());
        for &i in members {
            parts.push(self.lower_indexed_ctor(&bcx, ind, i, args, l, m_pos, rec_pos, span)?);
        }
        let (mut acc, mut acc_lvl) = parts.pop().expect("non-empty");
        for (ty, lvl) in parts.into_iter().rev() {
            acc = Type::Sum {
                lhs_level: lvl.clone(),
                rhs_level: acc_lvl.clone(),
                lhs: Rc::new(ty),
                rhs: Rc::new(acc),
            };
            acc_lvl = Level::max(lvl, acc_lvl);
        }
        Ok((acc, acc_lvl))
    }

    /// One indexed constructor's field spine: `lower_ctor` (tier 0 §3.1/§3.3)
    /// with the two §4 deletions — the pattern variable becomes an alias for
    /// the `m` binder, a recursive field becomes `El rec` — and everything
    /// else identical, tag first and `Unit`-terminated.
    #[allow(clippy::too_many_arguments)]
    fn lower_indexed_ctor(
        &self,
        bcx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[(Type, Level)],
        l: &Level,
        m_pos: usize,
        rec_pos: usize,
        span: Span,
    ) -> R<(Type, Level)> {
        let _ = span;
        let mut fcx = bcx.clone();
        fcx.selfref = None;
        fcx.guard = None;
        // Instantiations are scoped in the *original* Γ — before `m`/`rec` —
        // which is `bcx` minus the step binders; `TyVar.depth` records it.
        let depth = m_pos;
        fcx.tyvars = ind
            .params
            .iter()
            .zip(args)
            .map(|(name, (ty, level))| crate::TyVar {
                name: name.clone(),
                ty: ty.clone(),
                level: level.clone(),
                depth,
            })
            .collect();
        let ctor = &ind.ctors[i];
        let mut entries = vec![(crate::inductive::tag_type(ind.tag), Level::Zero)];
        fcx.push("#tag".into(), crate::inductive::tag_type(ind.tag), Level::Zero);
        for (k, (name, ty)) in ctor.fields.iter().enumerate() {
            match ctor.kind[k] {
                FieldKind::IndexVar => {
                    // §4.1: not stored. The name denotes the branch's index
                    // binder, for the later field types that mention it.
                    let cur = fcx.names.len();
                    fcx.aliases.push(Rc::new(Alias {
                        name: name.clone().expect("a pattern variable is a named field"),
                        depth: cur,
                        term: Rc::new(Term::Var(LocalVar((cur - 1 - m_pos) as u32))),
                        ty: Type::Nat,
                        level: Level::Zero,
                    }));
                }
                FieldKind::Plain => {
                    let cur = fcx.names.len();
                    let el = Type::El {
                        level: l.clone(),
                        tm: Rc::new(Term::Var(LocalVar((cur - 1 - rec_pos) as u32))),
                    };
                    entries.push((el.clone(), l.clone()));
                    fcx.push(name.clone().unwrap_or_else(|| "#field".into()), el, l.clone());
                }
                FieldKind::Container { .. } => {
                    unreachable!("indexed classification never emits a container")
                }
                FieldKind::Payload => {
                    let (t, lvl) = self.elab_ty(&fcx, ty)?;
                    entries.push((t.clone(), lvl.clone()));
                    let fname = name.clone().unwrap_or_else(|| "#field".into());
                    fcx.push(fname.clone(), t.clone(), lvl.clone());
                    // A field at a universe is a type name for later fields,
                    // exactly as in `lower_ctor`.
                    if let Type::Ty(level) = t {
                        fcx.tyvars.push(crate::TyVar {
                            name: fname,
                            ty: Type::El {
                                level: level.clone(),
                                tm: Rc::new(Term::Var(LocalVar(0))),
                            },
                            level,
                            depth: fcx.names.len(),
                        });
                    }
                }
            }
        }
        let mut acc = Type::Unit { level: Level::Zero };
        let mut acc_lvl = Level::Zero;
        for (ty, lvl) in entries.into_iter().rev() {
            acc = Type::Sigma {
                fst_level: lvl.clone(),
                snd_level: acc_lvl.clone(),
                fst: Rc::new(ty),
                snd: Rc::new(acc),
            };
            acc_lvl = Level::max(lvl, acc_lvl);
        }
        Ok((acc, acc_lvl))
    }

    /// `⟦c_i(a⃗)⟧` (§5): check the written index against the expected family's,
    /// then build the injection and field tuple against the *whnf* of the
    /// expected type — which the index check guarantees is the branch spine,
    /// because a canonical `0`/`S e` target only converts with an index whose
    /// whnf is constructor-headed.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_indexed_ctor(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[Expr],
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let Some((found, fam)) = self.indexed_of(expected) else {
            return err(
                format!(
                    "`{}` constructs the indexed family `{}(i)`, but the expected type \
                     here is not in that family form",
                    ctor.name, ind.name
                ),
                span,
            );
        };
        if found.tag != ind.tag {
            return err(
                format!(
                    "`{}` is a constructor of `{}`, which is not the expected type here",
                    ctor.name, ind.name
                ),
                span,
            );
        }
        // §5: the result index, from the pattern and the written arguments,
        // must convert with the family's. This is the whole index check — the
        // value itself stores nothing index-shaped.
        let pat = ctor.res.expect("indexed ctor");
        let target = match pat {
            IdxPat::Zero => Term::Zero,
            IdxPat::Succ { field } => Term::Succ(Rc::new(self.elab_check(
                cx,
                &args[field],
                &Type::Nat,
                &Level::Zero,
            )?)),
        };
        if conv_term(
            self.psi(),
            &cx.gamma,
            Layer::Prog,
            &target,
            &fam.idx,
            &Type::Nat,
            &Level::Zero,
            self.fuel,
        )
        .is_err()
        {
            return err(
                format!(
                    "`{}` constructs `{}` at index `{}`, which is not the expected index",
                    ctor.name,
                    ind.name,
                    match pat {
                        IdxPat::Zero => "0".to_string(),
                        IdxPat::Succ { field } => format!(
                            "Succ({})",
                            ctor.fields[field].0.as_deref().unwrap_or("_")
                        ),
                    }
                ),
                span,
            );
        }
        let head = self.whnf(cx, expected, span)?;
        let (zero, succ) = classes(ind);
        let class = if matches!(pat, IdxPat::Zero) { zero } else { succ };
        let pos = class.iter().position(|&j| j == i).expect("member of its own class");
        let spine = self.spine(&head, expected_lvl, class.len(), span)?;
        let stored: Vec<Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| !matches!(k, FieldKind::IndexVar))
            .map(|(a, _)| a.clone())
            .collect();
        let fields = self.build_fields(cx, &spine.ctors[pos].0, &stored, true, span)?;
        Ok(inject(&spine, pos, class.len(), fields, 0))
    }

    /// §6.1: the motive over `(Γ, h, z)` from one over `(Γ, z)`. A variable
    /// index is generalized — its occurrences become `h` — and anything else
    /// leaves `h` unused (the goal then must not need per-arm refinement, or
    /// the user writes the two-binder motive explicitly).
    pub(crate) fn generalize_index(&self, cx: &Cx, motive: &Type, idx: &Term) -> Type {
        let mut sig = LocalSubst::id(&cx.gamma).shift_local(2);
        if let Term::Var(LocalVar(i)) = idx {
            let pos = cx.gamma.entries.len() - 1 - *i as usize;
            sig.terms[pos] = Rc::new(Term::Var(LocalVar(1)));
        }
        motive.apply_local(&sig.extended(Rc::new(Term::Var(LocalVar(0)))))
    }

    /// `match` on an indexed family (§6): one `elim_Nat` on the index, a
    /// class case tree inside each branch. The prototype's `vec_elim` /
    /// `tree_elim`, generalized.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_indexed(
        &self,
        cx: &Cx,
        ind: &Inductive,
        fam: &IndexedFam,
        arms: &[Arm],
        scrut: Term,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let l = fam.level.clone();
        // Surface bookkeeping, as in `elab_match_data`: declaration order,
        // duplicates, arity (the binder list includes the pattern variable —
        // it is a surface field, §2), completeness.
        let n = ind.ctors.len();
        let mut ordered: Vec<Option<&Arm>> = vec![None; n];
        for a in arms {
            let Some(i) = ind.ctors.iter().position(|c| c.name == a.ctor) else {
                return err(
                    format!("`{}` is not a constructor of `{}`", a.ctor, ind.name),
                    a.span,
                );
            };
            if ordered[i].replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
            if a.binders.len() != ind.ctors[i].fields.len() {
                return err(
                    format!(
                        "`{}` binds {} field(s), found {}",
                        a.ctor,
                        ind.ctors[i].fields.len(),
                        a.binders.len()
                    ),
                    a.span,
                );
            }
        }
        let missing: Vec<&str> = ordered
            .iter()
            .enumerate()
            .filter(|(_, a)| a.is_none())
            .map(|(i, _)| ind.ctors[i].name.as_str())
            .collect();
        if !missing.is_empty() {
            return err(
                format!("`match` is missing an arm for `{}`", missing.join("`, `")),
                span,
            );
        }
        let (zero, succ) = classes(ind);
        let arm_of = |i: usize| ordered[i].expect("checked above");

        // Self-call plumbing (§6): the guard descends on the matched
        // parameter, and the index parameter — when the family's index is
        // itself a parameter — is *rebound* to the arm's pattern variable.
        let dec = self.descends_on_param(cx, &scrut);
        let rebind = match (&dec, &*fam.idx) {
            (Some(_), Term::Var(LocalVar(i))) => {
                let pos = cx.names.len() - 1 - *i as usize;
                cx.selfref
                    .as_ref()
                    .filter(|s| pos < s.params.len())
                    .map(|_| pos)
            }
            _ => None,
        };

        let gamma_len = cx.names.len();
        let msub = |gamma: &heather_kernel::term::LocalCtx, extra: u32, h: Term, z: Term| {
            motive.apply_local(
                &LocalSubst::id(gamma)
                    .shift_local(extra)
                    .extended(Rc::new(h))
                    .extended(Rc::new(z)),
            )
        };

        // Mot(h) = Π(v : El (fam h)). M[h, v] — the Π binder is the motive's
        // own `z` (§6). The `elim_Nat` motive is this Π, so the eliminator's
        // level is the Π's — `l ⊔ mlvl`, **not** `mlvl`. Every uniformly
        // level-0 declaration hides the difference; a `Type`-valued field
        // (`l = 1`, motive at 0) is what exposes a dropped join
        // (`fields_above_level_zero`).
        let elim_lvl = Level::max(l.clone(), mlvl.clone());
        let mot_pi = Type::Pi {
            dom_level: l.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.el_at(Term::Var(LocalVar(0)), 1)),
            cod: Rc::new(motive.clone()),
        };

        // One class branch body, over (…, v : El (fam <h>)); `extra` is how
        // many binders past Γ the payload binder sits (1 for the base, 3 for
        // the step), and `h` is the branch's index scoped past them + 1 (under
        // the case motive's own binder handled inside).
        let class_body = |vcx: &Cx,
                          members: &[usize],
                          h_at: &dyn Fn(u32) -> Term,
                          extra: u32,
                          env: Option<&IdxArmEnv>|
         -> R<Term> {
            let motive_z = msub(&cx.gamma, extra + 1, h_at(extra + 1), Term::Var(LocalVar(0)));
            if members.is_empty() {
                return Ok(Term::ElimEmpty {
                    level: mlvl.clone(),
                    scrut_level: l.clone(),
                    motive: Rc::new(motive_z),
                    scrut: Rc::new(Term::Var(LocalVar(0))),
                });
            }
            let branch_ty = self.whnf(vcx, &fam.el_at(h_at(extra), extra), span)?;
            let spine = self.spine(&branch_ty, &l, members.len(), span)?;
            let marms: Vec<(usize, &Arm)> = members.iter().map(|&i| (i, arm_of(i))).collect();
            self.indexed_case_tree(
                vcx,
                ind,
                &marms,
                &spine,
                0,
                motive_z,
                &mlvl,
                Rc::new(Term::Var(LocalVar(0))),
                env,
            )
        };

        // base : Mot(0), over Γ.
        let mut vcx = cx.clone();
        vcx.push("#payload".into(), fam.el_at(Term::Zero, 0), l.clone());
        let base_body = class_body(&vcx, &zero, &|_| Term::Zero, 1, None)?;
        let base = Term::Lam {
            dom_level: l.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.el_at(Term::Zero, 0)),
            body: Rc::new(base_body),
        };

        // step, over (Γ, m : Nat, rec : Mot(m)).
        let (m_pos, rec_pos) = (gamma_len, gamma_len + 1);
        let mut scx = cx.clone();
        scx.push("#idx".into(), Type::Nat, Level::Zero);
        let rec_ty = mot_pi.apply_local(
            &LocalSubst::id(&cx.gamma)
                .shift_local(1)
                .extended(Rc::new(Term::Var(LocalVar(0)))),
        );
        scx.push("#rec".into(), rec_ty, Level::max(l.clone(), mlvl.clone()));
        let mut svcx = scx.clone();
        svcx.push(
            "#payload".into(),
            fam.el_at(Term::Succ(Rc::new(Term::Var(LocalVar(1)))), 2),
            l.clone(),
        );
        let env = IdxArmEnv {
            m_pos,
            rec_pos,
            level: l.clone(),
            mlvl: mlvl.clone(),
            motive: motive.clone(),
            gamma_len,
            dec,
            rebind: rebind.map(|p| (p, m_pos)),
            outer_guard: cx.guard.clone(),
        };
        let succ_h = |extra: u32| Term::Succ(Rc::new(Term::Var(LocalVar(extra - 1))));
        let step_body = class_body(&svcx, &succ, &succ_h, 3, Some(&env))?;
        let step = Term::Lam {
            dom_level: l.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.el_at(Term::Succ(Rc::new(Term::Var(LocalVar(1)))), 2)),
            body: Rc::new(step_body),
        };

        // The recursion applied to the scrutinee: `M[idx, scrut]` directly —
        // no repackaging (§6, "minus one composition point").
        Ok(Term::App {
            fun: Rc::new(Term::ElimNat {
                level: elim_lvl,
                motive: Rc::new(mot_pi),
                base: Rc::new(base),
                step: Rc::new(step),
                scrut: Rc::clone(&fam.idx),
            }),
            dom_level: l,
            cod_level: mlvl,
            dom: Rc::new(fam.el_at((*fam.idx).clone(), 0)),
            cod: Rc::new(msub(
                &cx.gamma,
                1,
                fam.idx.shift_local(1),
                Term::Var(LocalVar(0)),
            )),
            arg: Rc::new(scrut),
        })
    }

    /// `case_tree` (tier 0 §5.2) over one class's members, with
    /// [`Self::elab_indexed_arm`] at the leaves. A separate walk rather than a
    /// flag on the shared one: the indexed arm binds the pattern variable and
    /// builds its own guard, and threading both through the tier-0 path would
    /// couple what the tiers keep deliberately separate.
    #[allow(clippy::too_many_arguments)]
    fn indexed_case_tree(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[(usize, &Arm)],
        spine: &Spine,
        j: usize,
        motive: Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        env: Option<&IdxArmEnv>,
    ) -> R<Term> {
        let n = arms.len();
        let d = j as u32;
        if j + 1 == n {
            let expected = motive
                .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut)));
            let ctor_ty = spine.ctors[j].0.shift_local(d);
            return self.elab_indexed_arm(cx, ind, arms[j], &ctor_ty, &scrut, &expected, mlvl, env);
        }
        let ctor_lvl = spine.ctors[j].1.clone();
        let tail_lvl = spine.tails[j].1.clone();
        let ctor_ty = Rc::new(spine.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(spine.tails[j].0.shift_local(d));
        let injected = |val: Term, inl: bool| {
            let (lhs, rhs) =
                (spine.ctors[j].0.shift_local(d + 1), spine.tails[j].0.shift_local(d + 1));
            let (lhs, rhs) = (Rc::new(lhs), Rc::new(rhs));
            let (lhs_level, rhs_level) = (ctor_lvl.clone(), tail_lvl.clone());
            let val = Rc::new(val);
            if inl {
                Term::Inl { lhs_level, rhs_level, lhs, rhs, val }
            } else {
                Term::Inr { lhs_level, rhs_level, lhs, rhs, val }
            }
        };
        let mut lcx = cx.clone();
        lcx.push("#scrut".into(), (*ctor_ty).clone(), ctor_lvl.clone());
        let l_expected = motive.apply_local(
            &crate::embed(&cx.gamma, 1)
                .extended(Rc::new(injected(Term::Var(LocalVar(0)), true))),
        );
        let case_l = self.elab_indexed_arm(
            &lcx,
            ind,
            arms[j],
            &spine.ctors[j].0.shift_local(d + 1),
            &Rc::new(Term::Var(LocalVar(0))),
            &l_expected,
            mlvl,
            env,
        )?;
        let mut rcx = cx.clone();
        rcx.push("#rest".into(), (*tail_ty).clone(), tail_lvl.clone());
        let inner_motive = motive.apply_local(
            &crate::embed(&cx.gamma, 2)
                .extended(Rc::new(injected(Term::Var(LocalVar(0)), false))),
        );
        let case_r = self.indexed_case_tree(
            &rcx,
            ind,
            arms,
            spine,
            j + 1,
            inner_motive,
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
            env,
        )?;
        Ok(Term::Case {
            lhs_level: ctor_lvl,
            rhs_level: tail_lvl,
            motive_level: mlvl.clone(),
            lhs: ctor_ty,
            rhs: tail_ty,
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    /// One indexed arm (§6's table): the pattern-variable binder aliases the
    /// eliminator's `m`, every stored field aliases its projection (as in
    /// `elab_arm`), and each recursive field contributes a `(child, rec child)`
    /// guard entry so a self-call becomes the ih.
    #[allow(clippy::too_many_arguments)]
    fn elab_indexed_arm(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arm: (usize, &Arm),
        ctor_ty: &Type,
        value: &Rc<Term>,
        expected: &Type,
        mlvl: &Level,
        env: Option<&IdxArmEnv>,
    ) -> R<Term> {
        let (ci, arm) = arm;
        let ctor = &ind.ctors[ci];
        let mut acx = cx.clone();
        let mut cur = ctor_ty.clone();
        let mut pair = Rc::clone(value);
        // The tag (spine entry 0): step past it, bind nothing.
        let Type::Sigma { fst_level, snd_level, fst, snd } =
            self.whnf(&acx, &cur, arm.span)?
        else {
            return err("internal: malformed indexed constructor encoding", arm.span);
        };
        let tag_proj = Rc::new(Term::Fst {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::clone(&fst),
            snd_ty: Rc::clone(&snd),
            pair: Rc::clone(&pair),
        });
        pair = Rc::new(Term::Snd {
            fst_level,
            snd_level,
            fst_ty: Rc::clone(&fst),
            snd_ty: Rc::clone(&snd),
            pair: Rc::clone(&pair),
        });
        cur = snd.apply_local(&LocalSubst::id(&acx.gamma).extended(tag_proj));
        let mut children: Vec<(Rc<Term>, Rc<Term>, Type, Level)> = Vec::new();
        for (k, name) in arm.binders.iter().enumerate() {
            if matches!(ctor.kind[k], FieldKind::IndexVar) {
                let env = env.expect("a pattern variable only occurs in the Succ class");
                let cur_len = acx.names.len();
                let m = Term::Var(LocalVar((cur_len - 1 - env.m_pos) as u32));
                acx.aliases.push(Rc::new(Alias {
                    name: name.clone(),
                    depth: cur_len,
                    term: Rc::new(m),
                    ty: Type::Nat,
                    level: Level::Zero,
                }));
                continue;
            }
            let Type::Sigma { fst_level, snd_level, fst, snd } =
                self.whnf(&acx, &cur, arm.span)?
            else {
                return err("internal: malformed indexed constructor encoding", arm.span);
            };
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&snd),
                pair: Rc::clone(&pair),
            });
            let rest = Rc::new(Term::Snd {
                fst_level: fst_level.clone(),
                snd_level,
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&snd),
                pair: Rc::clone(&pair),
            });
            cur = snd.apply_local(&LocalSubst::id(&acx.gamma).extended(Rc::clone(&proj)));
            pair = rest;
            if matches!(ctor.kind[k], FieldKind::Plain) {
                let env = env.expect("a recursive field only occurs in the Succ class");
                let cur_len = acx.names.len();
                let m = || Term::Var(LocalVar((cur_len - 1 - env.m_pos) as u32));
                let rec = Term::Var(LocalVar((cur_len - 1 - env.rec_pos) as u32));
                // ih = rec child : M[m, child] (§6) — one `rec` serves every
                // recursive field, since all sit at the same pattern variable.
                let ih = Term::App {
                    fun: Rc::new(rec),
                    dom_level: env.level.clone(),
                    cod_level: env.mlvl.clone(),
                    dom: Rc::new((*fst).clone()),
                    cod: Rc::new(env.mot_at(
                        &acx.gamma,
                        m().shift_local(1),
                        Term::Var(LocalVar(0)),
                        (cur_len - env.gamma_len) as u32 + 1,
                    )),
                    arg: Rc::clone(&proj),
                };
                let ih_ty = env.mot_at(
                    &acx.gamma,
                    m(),
                    (*proj).clone(),
                    (cur_len - env.gamma_len) as u32,
                );
                children.push((Rc::clone(&proj), Rc::new(ih), ih_ty, env.mlvl.clone()));
            }
            acx.aliases.push(Rc::new(Alias {
                name: name.clone(),
                depth: acx.names.len(),
                term: proj,
                ty: (*fst).clone(),
                level: fst_level,
            }));
        }
        if let Some(env) = env
            && !children.is_empty()
        {
            acx.guard = env
                .dec
                .map(|dec| {
                    Rc::new(Guard {
                        dec,
                        kind: GuardKind::Wf {
                            depth: acx.names.len(),
                            children,
                            container: None,
                        },
                        rebind: env.rebind,
                    })
                })
                .or_else(|| env.outer_guard.clone());
        }
        self.elab_check(&acx, &arm.body, expected, mlvl)
    }
}
