//! Indexed families, route 1: the family by large elimination on the index.
//!
//! This module is the mechanization of `docs/inductive-indexed-lowering.md`,
//! and is meant to be read against it — the section numbers in the comments
//! are that document's, and `crates/elab/tests/indexed_route1.rs` (`Nat`) and
//! `crates/elab/tests/indexed_declared_index.rs` (§8.2) are the hand
//! prototypes whose terms this generator emits. The doctrine is the tiers'
//! (`inductive.rs`): the lowering is untrusted, the kernel re-checks every
//! emitted term, and a bug here produces a checked theorem about the wrong
//! type — so no clever shortcuts, and annotations are read off the type being
//! eliminated wherever one exists.
//!
//! The scheme in one line (§4): `⟦D⟧` is the *index type's* eliminator at
//! motive `Ty l`, with one branch of **codes** per index constructor, the
//! branch's `rec` spliced for a recursive field, and the pattern-variable
//! field elided — it **is** what the branch names for that argument of the
//! index constructor, not payload (§4.1). A use `D<ā>(e)` is `El (fam ⟦e⟧)`;
//! there is no Σ over the index and no un-applied `⟦D⟧`.
//!
//! Which eliminator carries the family is the only thing the index type
//! decides (§8.2), and the three cases are named once, here:
//!
//! | index          | family              | `rec` at argument `a`          |
//! |----------------|---------------------|--------------------------------|
//! | `Nat`          | `elim_Nat`          | the step's `rec` binder        |
//! | declared, flat | a `Case` tree       | none — no recursive argument   |
//! | declared, `Wf` | `elim_Wf`           | `ih' ι_t`, at refined arity    |
//!
//! The third row is `wf.rs`'s own recursor device (§6.2 there) at motive
//! `Ty l`: inside `elim_Wf`'s step the ih has domain `Fin(arity a)` with `a`
//! the open step binder, so no branch can apply it at a literal until the
//! arity is refined — `cs` and `ih` are threaded **through the `Case`
//! motive**, and each branch receives them at its constructor-refined arity.

use std::cell::RefCell;
use std::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{nth, LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_syntax::ast::{Arm, Expr, ExprKind, Span};

use crate::inductive::{inject, nat_lit, FieldKind, IdxTy, Inductive, Spine};
use crate::wf::{Branches, Tel};
use crate::{code, err, Alias, Cx, Elaborator, Guard, GuardKind, R};

/// A type in **family form**: `El^l` of the index type's eliminator at motive
/// `Ty l`, read back into its parts. This is the indexed analogue of `tag_of`
/// — the form every indexed lowering emits and every indexed consumer reads.
pub(crate) struct IndexedFam {
    pub level: Level,
    /// The whole family node — `elim_Nat`, a `Case` tree, or `elim_Wf` — with
    /// a **closed placeholder** in its scrutinee slot. Kept whole rather than
    /// split into branches because a detached branch reads its own binders
    /// (`m`/`rec`, or `cs'`/`ih'`) as free variables and a bare shift would
    /// move them.
    pub node: Rc<Term>,
    /// The index the family is applied at.
    pub idx: Rc<Term>,
}

/// The scrutinee slot of a family node, replaced. For a `Case` *tree* only the
/// outermost node scrutinizes the index; the inner ones scrutinize their own
/// tail binders, so this is still one rewrite.
fn set_scrut(t: &Term, scrut: Rc<Term>) -> Option<Term> {
    Some(match t {
        Term::ElimNat { level, motive, base, step, .. } => Term::ElimNat {
            level: level.clone(),
            motive: Rc::clone(motive),
            base: Rc::clone(base),
            step: Rc::clone(step),
            scrut,
        },
        Term::ElimWf { level, motive_level, shape, arity, motive, step, .. } => Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: Rc::clone(shape),
            arity: Rc::clone(arity),
            motive: Rc::clone(motive),
            step: Rc::clone(step),
            scrut,
        },
        Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, .. } => {
            Term::Case {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                motive_level: motive_level.clone(),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
                motive: Rc::clone(motive),
                case_l: Rc::clone(case_l),
                case_r: Rc::clone(case_r),
                scrut,
            }
        }
        _ => return None,
    })
}

fn scrut_of(t: &Term) -> Option<&Rc<Term>> {
    match t {
        Term::ElimNat { scrut, .. } | Term::ElimWf { scrut, .. } | Term::Case { scrut, .. } => {
            Some(scrut)
        }
        _ => None,
    }
}

impl IndexedFam {
    /// The family re-applied at another index, `by` binders deeper — how the
    /// eliminator names `fam 0`, `fam (S m)` and `fam h` from one read-back
    /// type. The node is shifted **whole**, never branch by branch.
    pub fn at(&self, idx: Term, by: u32) -> Term {
        set_scrut(&self.node.shift_local(by), Rc::new(idx))
            .expect("a family node has a scrutinee slot")
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

/// The nominal tag of a family node, from whichever branch carries one. An
/// empty class is `⌜Empty⌝` and carries none, so every branch is tried; a
/// declared index's branches sit under the `Case` tree and the `cs`/`ih`
/// applications, which is what the walk peels.
///
/// This is §10.1's structural fingerprint, and it got bigger: any pass that
/// normalizes emitted terms makes every indexed type unrecognizable here
/// first.
fn tag_in(t: &Term, fuel: u32) -> Option<u32> {
    if fuel == 0 {
        return None;
    }
    if let Some(k) = read_tag_code(t) {
        return Some(k);
    }
    match t {
        Term::Case { case_l, case_r, .. } => {
            tag_in(case_l, fuel - 1).or_else(|| tag_in(case_r, fuel - 1))
        }
        Term::ElimNat { base, step, .. } => {
            tag_in(base, fuel - 1).or_else(|| tag_in(step, fuel - 1))
        }
        Term::ElimWf { step, .. } => tag_in(step, fuel - 1),
        Term::Lam { body, .. } => tag_in(body, fuel - 1),
        Term::App { fun, .. } => tag_in(fun, fuel - 1),
        _ => None,
    }
}

/// The declaration constructors of each index-constructor class, in
/// declaration order: entry `k` is the class of index constructor `k` (§4).
fn classes(ind: &Inductive, n_idx: usize) -> Vec<Vec<usize>> {
    let mut out = vec![Vec::new(); n_idx];
    for (i, c) in ind.ctors.iter().enumerate() {
        let pat = c.res.as_ref().expect("an indexed declaration's ctors all carry a pattern");
        out[pat.ctor].push(i);
    }
    out
}

/// The body of one branch of [`Elaborator::idx_case_tree`], called as
/// `(cx, j, value, d, obligation)`.
type CaseBody<'a> = dyn Fn(&Cx, usize, &Rc<Term>, u32, &Type) -> R<Term> + 'a;

/// What one branch of the family — or of the derived eliminator — knows about
/// the index constructor it sits under: for each of that constructor's
/// arguments, the term the pattern variable filling it denotes, and the `rec`
/// available there.
///
/// Everything is scoped in the branch context the caller built.
struct IdxBranch {
    /// Per index-constructor argument: `(term, its type, that type's level)`.
    /// A recursive argument is `nth(cs'; ι_t)` (or the `elim_Nat` binder `m`);
    /// a payload one is a projection of the index constructor's label (§8.2
    /// fact 3).
    pat: Vec<(Rc<Term>, Type, Level)>,
    /// Per index-constructor argument: the `rec` at a recursive one — the
    /// family's *code* (`Ty l`-valued) or the eliminator's ih function.
    rec: Vec<Option<Rc<Term>>>,
}

/// Everything an indexed `match` arm needs beyond what a tier-0 arm does: what
/// each pattern variable and each recursive field's ih is, the motive to
/// instantiate ih types from, and the self-call guard ingredients.
struct IdxArmEnv {
    /// [`IdxBranch::pat`], scoped at [`Self::depth`].
    pat: Vec<(Rc<Term>, Type, Level)>,
    /// Per index-constructor argument, at a recursive one: the ih *function*
    /// at that argument (`rec` for `Nat`, `ih' ι_t` for a declared index) and
    /// the index term the recursion sits at. Scoped at [`Self::depth`].
    rec: Vec<Option<(Rc<Term>, Rc<Term>)>>,
    /// `names.len()` of the context [`Self::pat`] and [`Self::rec`] are scoped
    /// in. The arm walk itself pushes no kernel binder, but the class case
    /// tree above it does, so a use here is shifted by the difference.
    depth: usize,
    level: Level,
    mlvl: Level,
    /// The motive over `(Γ, h, z)`; `gamma_len` is `|Γ|`, for re-scoping it.
    motive: Type,
    gamma_len: usize,
    /// `descends_on_param` of the scrutinee, if the `match` is on one of the
    /// enclosing declaration's own parameters.
    dec: Option<usize>,
    /// The index parameter a self-call *rebinds* to the arm's pattern variable
    /// (§6), when the family's index is itself a parameter.
    idx_param: Option<usize>,
    outer_guard: Option<Rc<Guard>>,
}

impl IdxArmEnv {
    /// `M[h, z]`, with `h`/`z` scoped `extra` binders past Γ.
    ///
    /// `gamma` is the *current* context — Γ plus those `extra` binders — so
    /// the substitution out of the motive's `(Γ, h, z)` is built from Γ's
    /// own prefix, not from all of `gamma`. Using `gamma` whole would emit a
    /// map whose source is `|gamma| + extra` long: a scope error that stayed
    /// invisible while it only mis-tailed a motive mentioning no Γ variable
    /// — and `fn`s inlined, so no global reference carried a `·^k` tail for
    /// it to get wrong (issues/simulate-conversion-cost.md).
    fn mot_at(&self, gamma: &LocalCtx, h: Term, z: Term, extra: u32) -> Type {
        let base = LocalCtx {
            base: gamma.base,
            entries: gamma.entries[..self.gamma_len].to_vec(),
        };
        self.motive.apply_local(
            &crate::embed(&base, extra).extended(Rc::new(h)).extended(Rc::new(z)),
        )
    }
}

/// `ih' ι_t` inside an `elim_Wf` branch whose constructor has `m` recursive
/// arguments (`wf.rs` §6.3's ih, at the literal arity a refined branch has).
/// By the branch convention `ih'` is `Var 0` and `cs'` is `Var 1`; inside the
/// application's `cod`, which binds the `Fin` index, `cs'` is `Var 2`.
///
/// At the family's constant motive `Ty l` this *is* the recursive field's
/// code; at the eliminator's `Mot` it is the ih function the arm applies to
/// the stored child. One formula, because it is one device.
fn wf_ih_at(tel: &Tel, m: usize, t: usize, d_body: u32) -> Term {
    let len = Rc::new(nat_lit(m));
    let cod = tel.motive.apply_local(
        &crate::embed(tel.gamma0, d_body + 1).extended(Rc::new(nth(
            &tel.level,
            &Rc::new(tel.d_ty.shift_local(d_body + 1)),
            &len,
            Rc::new(Term::Var(LocalVar(2))),
            Rc::new(Term::Var(LocalVar(0))),
        ))),
    );
    Term::App {
        fun: Rc::new(Term::Var(LocalVar(0))),
        dom_level: Level::Zero,
        cod_level: tel.mlvl.clone(),
        dom: Rc::new(Type::Fin { len: Rc::clone(&len) }),
        cod: Rc::new(cod),
        arg: Rc::new(crate::wf::fin_index(t, m, &Term::Zero)),
    }
}

impl Elaborator {
    /// Read a type back as a family form, when it is one of a declared
    /// indexed inductive. `None` for everything else — including the same
    /// family *reduced* at a constructor-headed index, which has lost its
    /// index and is diagnosed by the consumers that need it.
    pub(crate) fn indexed_of(&self, ty: &Type) -> Option<(Rc<Inductive>, IndexedFam)> {
        let Type::El { level, tm } = ty else { return None };
        let motive_is_ty = match &**tm {
            Term::ElimNat { motive, .. } | Term::ElimWf { motive, .. } => {
                matches!(&**motive, Type::Ty(_))
            }
            Term::Case { motive, .. } => matches!(&**motive, Type::Ty(_)),
            _ => return None,
        };
        if !motive_is_ty {
            return None;
        }
        let tag = tag_in(tm, 64)?;
        let ind = self.by_tag.get(&tag)?;
        ind.index.as_ref()?;
        let idx = Rc::clone(scrut_of(tm)?);
        let node = set_scrut(tm, Rc::new(Term::Zero))?;
        Some((
            Rc::clone(ind),
            IndexedFam { level: level.clone(), node: Rc::new(node), idx },
        ))
    }

    /// [`Self::indexed_of`] with reduction behind it, for a family that arrived
    /// through an `I -> Type` **function value** — `F(n)` where
    /// `fn F(n: Nat) -> Type { V<Nat>(n) }` is `El` of a δ/β-**redex**, not of
    /// the eliminator the structural read wants
    /// (`docs/record-type-values.md` §4/§6).
    ///
    /// The fallback is *not* `whnf`, and that is the whole subtlety: whnf of a
    /// family form at a constructor-headed index reduces the eliminator away,
    /// index and all — which is exactly the case `indexed_of`'s doc comment
    /// says is lost. So this steps the **code** one reduction at a time and
    /// re-runs the structural read after each step, stopping at the *first*
    /// success. A redex above the family node is peeled; the node itself is
    /// never reached, because the read succeeds the moment it surfaces.
    ///
    /// As with [`Self::record_of_at`], the structural read comes first and
    /// unchanged, so nothing that resolved before pays anything new.
    pub(crate) fn indexed_of_at(
        &self,
        cx: &Cx,
        ty: &Type,
    ) -> Option<(Rc<Inductive>, IndexedFam)> {
        if let Some(r) = self.indexed_of(ty) {
            return Some(r);
        }
        let Type::El { level, tm } = ty else { return None };
        let mut tm = Rc::clone(tm);
        // Bounded by the elaborator's own fuel: peeling `F(e)` is δ then β,
        // and a chain of wrappers is two steps each.
        for _ in 0..self.fuel.min(1024) {
            let next = heather_kernel::reduce::step_term_delta(
                &tm,
                &cx.gamma,
                heather_kernel::reduce::Defs::transparent(&self.delta_psi),
            )?;
            tm = Rc::new(next);
            let cand = Type::El { level: level.clone(), tm: Rc::clone(&tm) };
            if let Some(r) = self.indexed_of(&cand) {
                return Some(r);
            }
        }
        None
    }

    /// `⟦I⟧` for a declaration's index type (§2, §8.2), scoped in `cx`.
    pub(crate) fn index_type_of(
        &self,
        cx: &Cx,
        ind: &Inductive,
        span: Span,
    ) -> R<(Type, Level)> {
        match ind.index_ty.as_ref().expect("an indexed declaration has an index type") {
            IdxTy::Nat => Ok((Type::Nat, Level::Zero)),
            IdxTy::Decl(i) => self.lower_instance(cx, i, &[], &[], span),
        }
    }

    /// The index a constructor's result annotation names, built from the
    /// pattern and the written arguments (§5): `Succ(e)` at `Nat`, and the
    /// index type's own constructor at a declared index — where the *index
    /// type's* constructor lowering does the checking, so a pattern variable
    /// of the wrong type is a rejection there and not a mis-built index.
    pub(crate) fn indexed_ctor_index(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let pat = ind.ctors[i].res.as_ref().expect("indexed ctor");
        match ind.index_ty.as_ref().expect("an indexed declaration has an index type") {
            IdxTy::Nat => {
                let t = match pat.vars.first() {
                    None => Term::Zero,
                    Some(&f) => Term::Succ(Rc::new(self.elab_check(
                        cx,
                        &args[f],
                        &Type::Nat,
                        &Level::Zero,
                    )?)),
                };
                Ok((t, Type::Nat, Level::Zero))
            }
            IdxTy::Decl(iind) => {
                let (ity, ilvl) = self.lower_instance(cx, iind, &[], &[], span)?;
                let pargs: Vec<Expr> = pat.vars.iter().map(|&k| args[k].clone()).collect();
                let t = self.build_ctor(cx, iind, pat.ctor, &pargs, &ity, &ilvl, span)?;
                Ok((t, ity, ilvl))
            }
        }
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
        let (ity, ilvl) = self.index_type_of(cx, &ind, span)?;
        let idx_t = self.elab_check(cx, idx, &ity, &ilvl)?;
        self.lower_indexed_instance(cx, &ind, &lowered, idx_t, span).map(Some)
    }

    /// `⟦D<ā>(e)⟧ = El^l (fam ⟦e⟧)` (§4). Two passes: the whole family is
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
        // The first pass never leaves this function, so its scrutinee is a
        // closed placeholder: the branches are what the level is read off, and
        // the index reaches none of them.
        let (_, l) = self.build_family(cx, ind, args, &Level::Zero, Term::Zero, span)?;
        let (fam, _) = self.build_family(cx, ind, args, &l, idx, span)?;
        Ok((Type::El { level: l.clone(), tm: Rc::new(fam) }, l))
    }

    /// The family term (§4), at a given level, applied at `idx`. Also returns
    /// the level the branches actually demand, which is what the first pass of
    /// [`Self::lower_indexed_instance`] reads.
    fn build_family(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        l: &Level,
        idx: Term,
        span: Span,
    ) -> R<(Term, Level)> {
        let ity = ind.index_ty.as_ref().expect("an indexed declaration has an index type");
        let icts = ity.ctors();
        let classes = classes(ind, icts.len());
        let gamma_len = cx.names.len();
        // The join over the branches, gathered as they are built: a branch
        // body is produced inside a callback, so this is where its level can
        // be seen at all.
        let lmax = RefCell::new(Level::Zero);
        let class_code = |bcx: &Cx, k: usize, branch: &IdxBranch| -> R<Term> {
            let (ty, lvl) =
                self.fam_class(bcx, ind, &classes[k], args, l, gamma_len, branch, span)?;
            let mut m = lmax.borrow_mut();
            *m = Level::max(m.clone(), lvl);
            code::code_of(&ty).ok_or_else(|| crate::ElabError::Elab {
                msg: format!(
                    "a field of `{}`'s `{}` class has no type code, so it cannot appear \
                     in an indexed family (docs/inductive-indexed-lowering.md §3)",
                    ind.name, icts[k].name
                ),
                span,
            })
        };

        let fam = match ity {
            IdxTy::Nat => {
                let base = class_code(cx, 0, &IdxBranch { pat: vec![], rec: vec![] })?;
                let mut bcx = cx.clone();
                bcx.push("#idx".into(), Type::Nat, Level::Zero);
                bcx.push("#rec".into(), Type::Ty(l.clone()), Level::succ(l.clone()));
                let step = class_code(
                    &bcx,
                    1,
                    &IdxBranch {
                        pat: vec![(Rc::new(Term::Var(LocalVar(1))), Type::Nat, Level::Zero)],
                        rec: vec![Some(Rc::new(Term::Var(LocalVar(0))))],
                    },
                )?;
                Term::ElimNat {
                    level: Level::succ(l.clone()),
                    motive: Rc::new(Type::Ty(l.clone())),
                    base: Rc::new(base),
                    step: Rc::new(step),
                    scrut: Rc::new(idx),
                }
            }
            // A flat declared index: one `Case` tree at motive `Ty l`. No
            // branch has a `rec` — an enum constructor has no recursive
            // argument to draw one from, which is why a recursive field at
            // such an index was rejected by shape at declaration time (§8.2).
            IdxTy::Decl(iind) if !iind.recursive => {
                let (ity_ty, ity_lvl) = self.lower_instance(cx, iind, &[], &[], span)?;
                let spine = self.spine(&ity_ty, &ity_lvl, iind.ctors.len(), span)?;
                let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, _e: &Type| -> R<Term> {
                    let ctor_ty = spine.ctors[k].0.shift_local(d);
                    let mut pat = Vec::with_capacity(icts[k].rec.len());
                    for a in 0..icts[k].rec.len() {
                        pat.push(self.projection(bcx, &ctor_ty, value, a, span)?);
                    }
                    let rec = vec![None; pat.len()];
                    class_code(bcx, k, &IdxBranch { pat, rec })
                };
                self.idx_case_tree(
                    cx,
                    &spine,
                    iind.ctors.len(),
                    0,
                    Type::Ty(l.clone()),
                    &Level::succ(l.clone()),
                    Rc::new(idx),
                    0,
                    &body,
                )?
            }
            // A recursive declared index: `elim_Wf` at motive `Ty l`, with
            // `cs`/`ih` threaded through the `Case` motive so each branch sees
            // them at its own constructor-refined arity (§8.2 fact 1).
            IdxTy::Decl(iind) => {
                let (ity_ty, _) = self.lower_instance(cx, iind, &[], &[], span)?;
                let body = |bcx: &Cx,
                            tel: &Tel,
                            k: usize,
                            value: &Rc<Term>,
                            d_body: u32,
                            _e: &Type|
                 -> R<Term> {
                    let branch = self.wf_branch_env(bcx, iind, tel, k, value, d_body, span)?;
                    class_code(bcx, k, &branch)
                };
                self.build_elim_wf(
                    cx,
                    iind,
                    &ity_ty,
                    Type::Ty(l.clone()),
                    Level::succ(l.clone()),
                    idx,
                    &Branches::Custom(&body),
                    None,
                    span,
                )?
            }
        };
        let lvl = lmax.into_inner();
        Ok((fam, lvl))
    }

    /// The pattern variables and `rec`s of index constructor `k` inside an
    /// `elim_Wf` branch (§8.2 facts 1 and 3). A recursive argument's variable
    /// is `nth(cs'; ι_t)` — the projection out of the index constructor's
    /// children, with no inversion machinery — and a payload one is a
    /// projection of the label. `cs'` is `Var 1`, `ih'` is `Var 0`.
    #[allow(clippy::too_many_arguments)]
    fn wf_branch_env(
        &self,
        bcx: &Cx,
        iind: &Inductive,
        tel: &Tel,
        k: usize,
        value: &Rc<Term>,
        d_body: u32,
        span: Span,
    ) -> R<IdxBranch> {
        let ctor = &iind.ctors[k];
        let m = ctor.arity();
        let d_ty_here = Rc::new(tel.d_ty.shift_local(d_body));
        let ctor_ty = tel.spine.ctors[k].0.shift_local(d_body);
        let cs_var = Rc::new(Term::Var(LocalVar(1)));
        let (mut t, mut p) = (0usize, 0usize);
        let mut pat = Vec::with_capacity(ctor.fields.len());
        let mut rec = Vec::with_capacity(ctor.fields.len());
        for kind in &ctor.kind {
            match kind {
                FieldKind::Plain => {
                    pat.push((
                        Rc::new(crate::wf::nth_child(
                            &tel.level,
                            &d_ty_here,
                            m,
                            t,
                            Rc::clone(&cs_var),
                            &Term::Zero,
                        )),
                        (*d_ty_here).clone(),
                        tel.level.clone(),
                    ));
                    rec.push(Some(Rc::new(wf_ih_at(tel, m, t, d_body))));
                    t += 1;
                }
                FieldKind::Payload => {
                    pat.push(self.projection(bcx, &ctor_ty, value, p, span)?);
                    rec.push(None);
                    p += 1;
                }
                _ => return err("internal: an index type has no container or index field", span),
            }
        }
        Ok(IdxBranch { pat, rec })
    }

    /// One class's branch as a **type**: the tag spine of its members (tier 0
    /// §3, via the same Σ/Sum folds), with the pattern-variable fields elided
    /// (they alias what the branch names) and each recursive field an
    /// `El rec` (§4). `code_of` then quotes the result, `Var`s and all.
    #[allow(clippy::too_many_arguments)]
    fn fam_class(
        &self,
        bcx: &Cx,
        ind: &Inductive,
        members: &[usize],
        args: &[(Type, Level)],
        l: &Level,
        gamma_len: usize,
        branch: &IdxBranch,
        span: Span,
    ) -> R<(Type, Level)> {
        if members.is_empty() {
            // `Fin`'s `fam 0` (§4): a correct branch, not a degenerate one.
            return Ok((Type::Empty { level: l.clone() }, l.clone()));
        }
        let mut parts = Vec::with_capacity(members.len());
        for &i in members {
            parts.push(self.lower_indexed_ctor(bcx, ind, i, args, l, gamma_len, branch, span)?);
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
    /// with the two §4 deletions — a pattern variable becomes an alias for
    /// what the branch names, a recursive field becomes `El rec` — and
    /// everything else identical, tag first and `Unit`-terminated.
    #[allow(clippy::too_many_arguments)]
    fn lower_indexed_ctor(
        &self,
        bcx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[(Type, Level)],
        l: &Level,
        gamma_len: usize,
        branch: &IdxBranch,
        span: Span,
    ) -> R<(Type, Level)> {
        let _ = span;
        let mut fcx = bcx.clone();
        fcx.selfref = None;
        fcx.guard = None;
        // Instantiations are scoped in the *original* Γ — before any branch
        // binder — and `TyVar.depth` records it.
        fcx.tyvars = ind
            .params
            .iter()
            .zip(args)
            .map(|(name, (ty, level))| crate::TyVar {
                name: name.clone(),
                ty: ty.clone(),
                level: level.clone(),
                depth: gamma_len,
            })
            .collect();
        let ctor = &ind.ctors[i];
        let pat = ctor.res.as_ref().expect("indexed ctor");
        let bdepth = bcx.names.len();
        let mut entries = vec![(crate::inductive::tag_type(ind.tag), Level::Zero)];
        fcx.push("#tag".into(), crate::inductive::tag_type(ind.tag), Level::Zero);
        for (k, (name, ty)) in ctor.fields.iter().enumerate() {
            match ctor.kind[k] {
                FieldKind::IndexVar => {
                    // §4.1: not stored. The name denotes what the branch calls
                    // that argument of the index constructor, for the later
                    // field types that mention it. An `Alias` shifts itself by
                    // `names.len() - depth`, so binding it at the branch's own
                    // depth is all the scoping this needs.
                    let a = pat
                        .vars
                        .iter()
                        .position(|&f| f == k)
                        .expect("an IndexVar field fills an argument of the pattern");
                    let (term, ty, level) = branch.pat[a].clone();
                    fcx.aliases.push(Rc::new(Alias {
                        name: name.clone().expect("a pattern variable is a named field"),
                        depth: bdepth,
                        term,
                        ty,
                        level,
                    }));
                }
                FieldKind::Plain => {
                    let a = ctor.rec_at[k].expect("a recursive field records its argument");
                    let code = branch.rec[a]
                        .as_ref()
                        .expect("a recursive field sits at a recursive argument");
                    let by = (fcx.names.len() - bdepth) as u32;
                    let el = Type::El { level: l.clone(), tm: Rc::new(code.shift_local(by)) };
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
    /// because a canonical index target only converts with an index whose whnf
    /// is constructor-headed.
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
        let Some((found, fam)) = self.indexed_of_at(cx, expected) else {
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
        let (target, ity, ilvl) = self.indexed_ctor_index(cx, ind, i, args, span)?;
        if conv_term(
            self.psi(),
            &cx.gamma,
            Layer::Prog,
            &target,
            &fam.idx,
            &ity,
            &ilvl,
            self.fuel,
        )
        .is_err()
        {
            let pat = ctor.res.as_ref().expect("indexed ctor");
            let icts =
                ind.index_ty.as_ref().expect("an indexed declaration has an index type").ctors();
            let spelling = if pat.vars.is_empty() {
                icts[pat.ctor].name.clone()
            } else {
                format!(
                    "{}({})",
                    icts[pat.ctor].name,
                    pat.vars
                        .iter()
                        .map(|&f| ctor.fields[f].0.as_deref().unwrap_or("_"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            return err(
                format!(
                    "`{}` constructs `{}` at index `{spelling}`, which is not the \
                     expected index",
                    ctor.name, ind.name
                ),
                span,
            );
        }
        let head = self.whnf(cx, expected, span)?;
        let icts =
            ind.index_ty.as_ref().expect("an indexed declaration has an index type").ctors();
        let class = classes(ind, icts.len())
            .swap_remove(ctor.res.as_ref().expect("indexed ctor").ctor);
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

    /// `match` on an indexed family (§6): one eliminator on the index, a class
    /// case tree inside each branch. The prototypes' `vec_elim` / `tree_elim`
    /// / `vecf_elim` / `bal_elim`, generalized.
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
        let ity = ind.index_ty.as_ref().expect("an indexed declaration has an index type");
        let icts = ity.ctors();
        // Surface bookkeeping, as in `elab_match_data`: declaration order,
        // duplicates, arity (the binder list includes the pattern variables —
        // they are surface fields, §2), completeness.
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
        let classes = classes(ind, icts.len());
        let arm_of = |i: usize| ordered[i].expect("checked above");

        // Self-call plumbing (§6): the guard descends on the matched
        // parameter, and the index parameter — when the family's index is
        // itself a parameter — is *rebound* to the arm's pattern variable.
        let dec = self.descends_on_param(cx, &scrut);
        let idx_param = match (&dec, &*fam.idx) {
            (Some(_), Term::Var(LocalVar(i))) => {
                let pos = cx.names.len() - 1 - *i as usize;
                cx.selfref.as_ref().filter(|s| pos < s.params.len()).map(|_| pos)
            }
            _ => None,
        };

        let gamma_len = cx.names.len();
        let gamma = cx.gamma.clone();
        let msub = |gamma: &LocalCtx, extra: u32, h: Term, z: Term| {
            motive.apply_local(
                &LocalSubst::id(gamma)
                    .shift_local(extra)
                    .extended(Rc::new(h))
                    .extended(Rc::new(z)),
            )
        };

        // Mot(h) = Π(v : El (fam h)). M[h, v] — the Π binder is the motive's
        // own `z` (§6). The eliminator's motive is this Π, so its level is the
        // Π's — `l ⊔ mlvl`, **not** `mlvl`. Every uniformly level-0
        // declaration hides the difference; a `Type`-valued field (`l = 1`,
        // motive at 0) is what exposes a dropped join (§10.5).
        let elim_lvl = Level::max(l.clone(), mlvl.clone());
        let mot_pi = Type::Pi {
            dom_level: l.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(fam.el_at(Term::Var(LocalVar(0)), 1)),
            cod: Rc::new(motive.clone()),
        };

        let elim = match ity {
            IdxTy::Nat => {
                // base : Mot(0), over Γ.
                let mut vcx = cx.clone();
                vcx.push("#payload".into(), fam.el_at(Term::Zero, 0), l.clone());
                let base_body = self.indexed_class_body(
                    &vcx, ind, fam, &classes[0], &arm_of, &Term::Zero, 1, &gamma, &motive,
                    &mlvl, &l, None, span,
                )?;
                let base = Term::Lam {
                    dom_level: l.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(fam.el_at(Term::Zero, 0)),
                    body: Rc::new(base_body),
                };
                // step, over (Γ, m : Nat, rec : Mot(m)).
                let mut scx = cx.clone();
                scx.push("#idx".into(), Type::Nat, Level::Zero);
                let rec_ty = mot_pi.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .shift_local(1)
                        .extended(Rc::new(Term::Var(LocalVar(0)))),
                );
                scx.push("#rec".into(), rec_ty, elim_lvl.clone());
                let h = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
                let mut svcx = scx.clone();
                svcx.push("#payload".into(), fam.el_at(h.clone(), 2), l.clone());
                // In the payload context the step binders have moved out by
                // one: `m` is `Var 2` and `rec` is `Var 1`.
                let env = IdxArmEnv {
                    pat: vec![(Rc::new(Term::Var(LocalVar(2))), Type::Nat, Level::Zero)],
                    rec: vec![Some((
                        Rc::new(Term::Var(LocalVar(1))),
                        Rc::new(Term::Var(LocalVar(2))),
                    ))],
                    depth: svcx.names.len(),
                    level: l.clone(),
                    mlvl: mlvl.clone(),
                    motive: motive.clone(),
                    gamma_len,
                    dec,
                    idx_param,
                    outer_guard: cx.guard.clone(),
                };
                let step_body = self.indexed_class_body(
                    &svcx,
                    ind,
                    fam,
                    &classes[1],
                    &arm_of,
                    &Term::Succ(Rc::new(Term::Var(LocalVar(2)))),
                    3,
                    &gamma,
                    &motive,
                    &mlvl,
                    &l,
                    Some(&env),
                    span,
                )?;
                let step = Term::Lam {
                    dom_level: l.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(fam.el_at(h, 2)),
                    body: Rc::new(step_body),
                };
                Term::ElimNat {
                    level: elim_lvl.clone(),
                    motive: Rc::new(mot_pi),
                    base: Rc::new(base),
                    step: Rc::new(step),
                    scrut: Rc::clone(&fam.idx),
                }
            }
            IdxTy::Decl(iind) if !iind.recursive => {
                let (ity_ty, ity_lvl) = self.lower_instance(cx, iind, &[], &[], span)?;
                let spine = self.spine(&ity_ty, &ity_lvl, iind.ctors.len(), span)?;
                let body = |bcx: &Cx, k: usize, value: &Rc<Term>, d: u32, exp: &Type| -> R<Term> {
                    let Type::Pi { dom_level, cod_level, dom, .. } = exp else {
                        return err("internal: an indexed branch obligation is not a Π", span);
                    };
                    let mut vcx = bcx.clone();
                    vcx.push("#payload".into(), (**dom).clone(), dom_level.clone());
                    // Under the payload binder: the label and the spine are
                    // one deeper.
                    let ctor_ty = spine.ctors[k].0.shift_local(d + 1);
                    let value1 = Rc::new(value.shift_local(1));
                    let mut pat = Vec::with_capacity(icts[k].rec.len());
                    for a in 0..icts[k].rec.len() {
                        pat.push(self.projection(&vcx, &ctor_ty, &value1, a, span)?);
                    }
                    let env = IdxArmEnv {
                        pat,
                        rec: vec![None; icts[k].rec.len()],
                        depth: vcx.names.len(),
                        level: l.clone(),
                        mlvl: mlvl.clone(),
                        motive: motive.clone(),
                        gamma_len,
                        dec,
                        idx_param,
                        outer_guard: cx.guard.clone(),
                    };
                    let h = inject(&spine, k, iind.ctors.len(), (*value1).clone(), d + 1);
                    let inner = self.indexed_class_body(
                        &vcx,
                        ind,
                        fam,
                        &classes[k],
                        &arm_of,
                        &h,
                        d + 1,
                        &gamma,
                        &motive,
                        &mlvl,
                        &l,
                        Some(&env),
                        span,
                    )?;
                    Ok(Term::Lam {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::clone(dom),
                        body: Rc::new(inner),
                    })
                };
                self.idx_case_tree(
                    cx,
                    &spine,
                    iind.ctors.len(),
                    0,
                    mot_pi,
                    &elim_lvl,
                    Rc::clone(&fam.idx),
                    0,
                    &body,
                )?
            }
            IdxTy::Decl(iind) => {
                let (ity_ty, _) = self.lower_instance(cx, iind, &[], &[], span)?;
                let body = |bcx: &Cx,
                            tel: &Tel,
                            k: usize,
                            value: &Rc<Term>,
                            d_body: u32,
                            exp: &Type|
                 -> R<Term> {
                    let Type::Pi { dom_level, cod_level, dom, .. } = exp else {
                        return err("internal: an indexed branch obligation is not a Π", span);
                    };
                    let branch = self.wf_branch_env(bcx, iind, tel, k, value, d_body, span)?;
                    let mut vcx = bcx.clone();
                    vcx.push("#payload".into(), (**dom).clone(), dom_level.clone());
                    // The index this branch stands at: `sup_f(ι_k(label); cs')`
                    // rebuilt from the branch's own binders. Its identity with
                    // the declared constructor is `Unit` η, twice (§8.2 fact 2)
                    // — which conversion pays, so nothing here has to.
                    let Type::Wf { level, shape, arity } = tel.d_ty.shift_local(d_body + 1)
                    else {
                        return err("internal: a recursive index did not lower to a `Wf`", span);
                    };
                    let h = Term::Supf {
                        level,
                        shape,
                        arity,
                        label: Rc::new(inject(
                            &tel.spine,
                            k,
                            iind.ctors.len(),
                            value.shift_local(1),
                            d_body + 1,
                        )),
                        children: Rc::new(Term::Var(LocalVar(2))),
                    };
                    let env = IdxArmEnv {
                        pat: branch
                            .pat
                            .iter()
                            .map(|(t, ty, lv)| {
                                (Rc::new(t.shift_local(1)), ty.shift_local(1), lv.clone())
                            })
                            .collect(),
                        rec: branch
                            .rec
                            .iter()
                            .zip(&branch.pat)
                            .map(|(r, (p, _, _))| {
                                r.as_ref().map(|f| {
                                    (Rc::new(f.shift_local(1)), Rc::new(p.shift_local(1)))
                                })
                            })
                            .collect(),
                        depth: vcx.names.len(),
                        level: l.clone(),
                        mlvl: mlvl.clone(),
                        motive: motive.clone(),
                        gamma_len,
                        dec,
                        idx_param,
                        outer_guard: cx.guard.clone(),
                    };
                    let inner = self.indexed_class_body(
                        &vcx,
                        ind,
                        fam,
                        &classes[k],
                        &arm_of,
                        &h,
                        d_body + 1,
                        &gamma,
                        &motive,
                        &mlvl,
                        &l,
                        Some(&env),
                        span,
                    )?;
                    Ok(Term::Lam {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::clone(dom),
                        body: Rc::new(inner),
                    })
                };
                self.build_elim_wf(
                    cx,
                    iind,
                    &ity_ty,
                    mot_pi,
                    elim_lvl.clone(),
                    (*fam.idx).clone(),
                    &Branches::Custom(&body),
                    None,
                    span,
                )?
            }
        };

        // The recursion applied to the scrutinee: `M[idx, scrut]` directly —
        // no repackaging (§6, "minus one composition point").
        Ok(Term::App {
            fun: Rc::new(elim),
            dom_level: l,
            cod_level: mlvl,
            dom: Rc::new(fam.el_at((*fam.idx).clone(), 0)),
            cod: Rc::new(msub(&gamma, 1, fam.idx.shift_local(1), Term::Var(LocalVar(0)))),
            arg: Rc::new(scrut),
        })
    }

    /// One class's arms, inside a branch whose payload binder `v : El (fam h)`
    /// is `Var 0` of `vcx`. `extra` is how many binders past Γ that binder
    /// sits, and `h` is the branch's index scoped there.
    #[allow(clippy::too_many_arguments)]
    fn indexed_class_body<'a>(
        &self,
        vcx: &Cx,
        ind: &Inductive,
        fam: &IndexedFam,
        members: &[usize],
        arm_of: &dyn Fn(usize) -> &'a Arm,
        h: &Term,
        extra: u32,
        gamma: &LocalCtx,
        motive: &Type,
        mlvl: &Level,
        l: &Level,
        env: Option<&IdxArmEnv>,
        span: Span,
    ) -> R<Term> {
        let motive_z = motive.apply_local(
            &LocalSubst::id(gamma)
                .shift_local(extra + 1)
                .extended(Rc::new(h.shift_local(1)))
                .extended(Rc::new(Term::Var(LocalVar(0)))),
        );
        if members.is_empty() {
            return Ok(Term::ElimEmpty {
                level: mlvl.clone(),
                scrut_level: l.clone(),
                motive: Rc::new(motive_z),
                scrut: Rc::new(Term::Var(LocalVar(0))),
            });
        }
        let branch_ty = self.whnf(vcx, &fam.el_at(h.clone(), extra), span)?;
        let spine = self.spine(&branch_ty, l, members.len(), span)?;
        let marms: Vec<(usize, &Arm)> = members.iter().map(|&i| (i, arm_of(i))).collect();
        self.indexed_case_tree(
            vcx,
            ind,
            &marms,
            &spine,
            0,
            motive_z,
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
            env,
        )
    }

    /// A `Case` tree over the **index type's** spine, with the branch bodies
    /// supplied by the caller. Shared by the family (a constant motive `Ty l`)
    /// and by the derived eliminator (the dependent `Mot`), which is why the
    /// motive is threaded rather than assumed constant.
    ///
    /// `spine` is scoped where the caller read it back and `d` counts the
    /// binders pushed since; `motive` is `P_j` over `(cx, z : R_j)`. The body
    /// is called as `(cx, j, value, d, obligation)`.
    #[allow(clippy::too_many_arguments)]
    fn idx_case_tree(
        &self,
        cx: &Cx,
        spine: &Spine,
        n: usize,
        j: usize,
        motive: Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        d: u32,
        body: &CaseBody,
    ) -> R<Term> {
        if j + 1 == n {
            let expected =
                motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut)));
            return body(cx, j, &scrut, d, &expected);
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
        let case_l =
            body(&lcx, j, &Rc::new(Term::Var(LocalVar(0))), d + 1, &l_expected)?;
        let mut rcx = cx.clone();
        rcx.push("#rest".into(), (*tail_ty).clone(), tail_lvl.clone());
        let inner_motive = motive.apply_local(
            &crate::embed(&cx.gamma, 2)
                .extended(Rc::new(injected(Term::Var(LocalVar(0)), false))),
        );
        let case_r = self.idx_case_tree(
            &rcx,
            spine,
            n,
            j + 1,
            inner_motive,
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
            d + 1,
            body,
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

    /// `case_tree` (tier 0 §5.2) over one class's members, with
    /// [`Self::elab_indexed_arm`] at the leaves. A separate walk rather than a
    /// flag on the shared one: the indexed arm binds the pattern variables and
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

    /// One indexed arm (§6's table): a pattern-variable binder aliases what the
    /// branch names for that argument of the index constructor, every stored
    /// field aliases its projection (as in `elab_arm`), and each recursive
    /// field contributes a `(child, ih)` guard entry so a self-call becomes
    /// the ih.
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
        let pat = ctor.res.as_ref().expect("indexed ctor");
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
        // The arm walk pushes aliases, never kernel binders, so `env`'s terms
        // are weakened by one fixed amount throughout.
        let cur_len = acx.names.len();
        let by = |e: &IdxArmEnv| (cur_len - e.depth) as u32;
        let extra = |e: &IdxArmEnv| (cur_len - e.gamma_len) as u32;
        let mut children: Vec<(Rc<Term>, Rc<Term>, Type, Level)> = Vec::new();
        let mut rebind: Vec<Rc<Term>> = Vec::new();
        for (k, name) in arm.binders.iter().enumerate() {
            if matches!(ctor.kind[k], FieldKind::IndexVar) {
                let env = env.expect("a pattern variable only occurs in a branch with one");
                let a = pat
                    .vars
                    .iter()
                    .position(|&f| f == k)
                    .expect("an IndexVar field fills an argument of the pattern");
                let (term, ty, level) = &env.pat[a];
                acx.aliases.push(Rc::new(Alias {
                    name: name.clone(),
                    depth: cur_len,
                    term: Rc::new(term.shift_local(by(env))),
                    ty: ty.shift_local(by(env)),
                    level: level.clone(),
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
                let env = env.expect("a recursive field only occurs in a branch with a rec");
                let a = ctor.rec_at[k].expect("a recursive field records its argument");
                let (ihfn, at) = env.rec[a]
                    .as_ref()
                    .expect("a recursive field sits at a recursive argument");
                let (ihfn, at) = (ihfn.shift_local(by(env)), Rc::new(at.shift_local(by(env))));
                // ih = ⟨the branch's rec at this argument⟩ child : M[at, child]
                // (§6) — one per recursive field, each drawn from the `rec` of
                // the index-constructor argument its pattern variable fills.
                let ih = Term::App {
                    fun: Rc::new(ihfn),
                    dom_level: env.level.clone(),
                    cod_level: env.mlvl.clone(),
                    dom: Rc::new((*fst).clone()),
                    cod: Rc::new(env.mot_at(
                        &acx.gamma,
                        at.shift_local(1),
                        Term::Var(LocalVar(0)),
                        extra(env) + 1,
                    )),
                    arg: Rc::clone(&proj),
                };
                let ih_ty =
                    env.mot_at(&acx.gamma, (*at).clone(), (*proj).clone(), extra(env));
                children.push((Rc::clone(&proj), Rc::new(ih), ih_ty, env.mlvl.clone()));
                rebind.push(at);
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
                        rebind: env.idx_param.map(|p| (p, rebind)),
                    })
                })
                .or_else(|| env.outer_guard.clone());
        }
        self.elab_check(&acx, &arm.body, expected, mlvl)
    }
}
