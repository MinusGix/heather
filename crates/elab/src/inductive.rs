//! Tier-0 inductive declarations: the lowering to sums-of-Σs.
//!
//! This module is the mechanization of `docs/inductive-tier0-lowering.md`, and
//! is meant to be read against it — the section numbers in the comments are
//! that document's. The doctrine (issues/inductive-compiler.md): the lowering
//! is *untrusted* like the rest of the elaborator (the kernel re-checks every
//! emitted declaration), but unlike the rest of the elaborator a bug here
//! produces a checked theorem about the wrong type rather than a rejection.
//! Hence: no clever shortcuts, one function per numbered rule, and the
//! annotations always read off the type being eliminated rather than rebuilt.
//!
//! Not here yet: tier 1 (recursive, exact-height fording) and tier 2 (W).
//! Recursive declarations are classified and rejected, not mis-lowered.

use std::rc::Rc;

use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Arm, Expr, InductiveDecl, Span, Ty, TyKind};

use crate::{embed, err, Alias, Cx, Elaborator, R};

/// A declared inductive, kept in surface form: the field types are lowered
/// afresh at each instantiation, since type parameters are monomorphized
/// (§2 — `Option<Nat>` and `Option<Bool>` are unrelated kernel types).
pub(crate) struct Inductive {
    pub name: String,
    /// The nominal tag (§3.3): sequential per elaborator, carried as the first
    /// field of every constructor (see [`tag_type`]) so that structurally
    /// identical declarations do not share a kernel type.
    pub tag: u32,
    pub params: Vec<String>,
    pub ctors: Vec<Ctor>,
}

pub(crate) struct Ctor {
    pub name: String,
    /// `(optional field name, field type)`. A named field is in scope in the
    /// types of the fields after it, which is why the spine is a Σ.
    pub fields: Vec<(Option<String>, Ty)>,
}

/// A kernel type read back as a tag spine (§3.2). Everything the constructor
/// and `match` lowerings need is here, taken from the type itself rather than
/// regenerated, so the annotations cannot drift from what is being eliminated.
pub(crate) struct Spine {
    /// `(⟦c_i⟧, its level)` for each constructor.
    pub ctors: Vec<(Rc<Type>, Level)>,
    /// `(R_{i+1}, its level)` — the right operand of the `i`-th `+`, for
    /// `i < n-1`.
    pub tails: Vec<(Rc<Type>, Level)>,
}

/// The nominal tag *type* for declaration `k` (§3.3): the binary digits of
/// `k`, as a right-nested Σ of `Unit`s — `Unit` for a 0 digit, `Σ(Unit).Unit`
/// for a 1, terminated by `Unit`.
///
/// Two properties, and the tag needs both:
///
/// - **Distinct per declaration.** Type conversion is structural, so different
///   digit strings are different types (minimal binary representations are
///   distinct as strings, so the encoding is injective).
/// - **Proof-irrelevant.** Built only from `Unit` and `Σ`, both of which have
///   η in `conv.rs`, so *any* two inhabitants are convertible. This is what a
///   dependent motive needs: an arm's binder `x : ⟦c_i⟧` is neutral, and the
///   motive puts it back together as `inl x`, which must still be convertible
///   with the canonical `inl (pair tag ⟨⟩)`. An `Id`-based tag fails exactly
///   here — `Id` has no η, so a neutral `fst x` is not convertible with
///   `refl`, and `match`ing a variable under a dependent motive stops
///   typechecking.
fn tag_type(k: u32) -> Type {
    if k == 0 {
        return Type::Unit;
    }
    let digit = if k & 1 == 0 {
        Type::Unit
    } else {
        Type::Sigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst: Rc::new(Type::Unit),
            snd: Rc::new(Type::Unit),
        }
    };
    Type::Sigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: Rc::new(digit),
        snd: Rc::new(tag_type(k >> 1)),
    }
}

/// Read a tag type back to its declaration index — the inverse of [`tag_type`].
fn read_tag(t: &Type) -> Option<u32> {
    match t {
        Type::Unit => Some(0),
        Type::Sigma { fst, snd, .. } => {
            let digit = match &**fst {
                Type::Unit => 0,
                Type::Sigma { fst, snd, .. }
                    if matches!(**fst, Type::Unit) && matches!(**snd, Type::Unit) =>
                {
                    1
                }
                _ => return None,
            };
            read_tag(snd)?.checked_mul(2)?.checked_add(digit)
        }
        _ => None,
    }
}

/// The tag's inhabitant: nested `⟨⟩`s matching the tag type's shape. Which
/// inhabitant hardly matters — the type is proof-irrelevant — but it has to be
/// *an* inhabitant for the kernel to accept the constructor.
fn tag_value(t: &Type) -> Term {
    match t {
        Type::Sigma { fst_level, snd_level, fst, snd } => Term::Pair {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::clone(fst),
            snd_ty: Rc::clone(snd),
            fst: Rc::new(tag_value(fst)),
            snd: Rc::new(tag_value(snd)),
        },
        _ => Term::Triv,
    }
}

impl Elaborator {
    // -- declaration --------------------------------------------------------

    /// Register an `inductive` declaration: classify its tier, check its names,
    /// and assign its nominal tag. Nothing is emitted here — an inductive has
    /// no kernel counterpart of its own; it is lowered at each use (§2).
    pub(crate) fn elab_inductive(&mut self, d: &InductiveDecl) -> R<()> {
        if self.inductives.contains_key(&d.name) || self.globals.contains_key(&d.name) {
            return err(format!("duplicate name `{}`", d.name), d.span);
        }
        if d.name == "Nat" {
            return err("`Nat` is built in", d.span);
        }
        for (i, p) in d.params.iter().enumerate() {
            if d.params[..i].contains(p) {
                return err(format!("duplicate type parameter `{p}`"), d.span);
            }
        }
        let mut ctors = Vec::new();
        for (i, c) in d.ctors.iter().enumerate() {
            if d.ctors[..i].iter().any(|o| o.name == c.name) {
                return err(format!("duplicate constructor `{}`", c.name), c.span);
            }
            if matches!(c.name.as_str(), "Zero" | "Succ" | "refl") {
                return err(
                    format!("`{}` is built in and cannot be a constructor name", c.name),
                    c.span,
                );
            }
            if let Some((other, _)) = self.ctors.get(&c.name) {
                return err(
                    format!("`{}` is already a constructor of `{}`", c.name, other.name),
                    c.span,
                );
            }
            if self.globals.contains_key(&c.name) || self.inductives.contains_key(&c.name) {
                return err(format!("duplicate name `{}`", c.name), c.span);
            }
            // Tier classification (§2). With no function types in field
            // position there is no *negative* occurrence to find yet, so any
            // self-occurrence means tier 1 or 2 — which is a rejection today,
            // never a silent lowering.
            for f in &c.fields {
                if let Some(sp) = occurs(&f.ty, &d.name) {
                    return err(
                        format!(
                            "`{}` is recursive (field of `{}` mentions `{}`): that is a tier-1 \
                             inductive, and the exact-height encoding is not implemented yet \
                             (docs/inductive-tier0-lowering.md §2)",
                            d.name, c.name, d.name
                        ),
                        sp,
                    );
                }
            }
            ctors.push(Ctor {
                name: c.name.clone(),
                fields: c
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), f.ty.clone()))
                    .collect(),
            });
        }
        let ind = Rc::new(Inductive {
            name: d.name.clone(),
            tag: self.next_tag,
            params: d.params.clone(),
            ctors,
        });
        self.next_tag += 1;
        for i in 0..ind.ctors.len() {
            self.ctors.insert(ind.ctors[i].name.clone(), (Rc::clone(&ind), i));
        }
        self.by_tag.insert(ind.tag, Rc::clone(&ind));
        self.inductives.insert(d.name.clone(), ind);
        Ok(())
    }

    // -- the type (§3) ------------------------------------------------------

    /// `⟦D<args>⟧` for a named type: a type parameter in scope, or a declared
    /// inductive applied to its arguments.
    pub(crate) fn lower_named(
        &self,
        cx: &Cx,
        name: &str,
        args: &[Ty],
        span: Span,
    ) -> R<(Type, Level)> {
        if let Some((_, ty, lvl)) = cx.tyvars.iter().rev().find(|(n, _, _)| n == name) {
            if !args.is_empty() {
                return err(format!("type parameter `{name}` takes no arguments"), span);
            }
            return Ok((ty.clone(), lvl.clone()));
        }
        let Some(ind) = self.inductives.get(name) else {
            return err(format!("unknown type `{name}`"), span);
        };
        if args.len() != ind.params.len() {
            return err(
                format!(
                    "`{name}` takes {} type argument(s), found {}",
                    ind.params.len(),
                    args.len()
                ),
                span,
            );
        }
        let mut lowered = Vec::with_capacity(args.len());
        for a in args {
            lowered.push(self.elab_ty(cx, a)?);
        }
        self.lower_instance(cx, ind, &lowered, span)
    }

    /// The tag spine (§3.2): `⟦D⟧ = ⟦c₁⟧ + (⟦c₂⟧ + …)`, right-nested;
    /// `Empty` with no constructors, and no `+` at all with one.
    pub(crate) fn lower_instance(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        let mut parts = Vec::with_capacity(ind.ctors.len());
        for i in 0..ind.ctors.len() {
            parts.push(self.lower_ctor(cx, ind, i, args, span)?);
        }
        let Some((last, last_lvl)) = parts.pop() else {
            return Ok((Type::Empty, Level::Zero));
        };
        let mut acc = last;
        let mut acc_lvl = last_lvl;
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

    /// One constructor's field spine (§3.1 + §3.3): the nominal tag, then the
    /// fields, Unit-terminated. Built outside-in as a list of entries and
    /// folded from the end, which is exactly why no shifting is needed: entry
    /// `j`'s type is already scoped in `Γ` plus entries `0..j`.
    fn lower_ctor(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[(Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        // Field types see the type parameters and the earlier *named* fields;
        // nothing else from the ambient declaration.
        let mut fcx = cx.clone();
        fcx.selfref = None;
        fcx.guard = None;
        fcx.tyvars = ind
            .params
            .iter()
            .cloned()
            .zip(args.iter().map(|(t, l)| (t.clone(), l.clone())))
            .map(|(n, (t, l))| (n, t, l))
            .collect();
        // Entry 0 is the tag; the surface has no name for it and no way to
        // bind it in a pattern.
        let mut entries = vec![(tag_type(ind.tag), Level::Zero)];
        fcx.push("#tag".into(), tag_type(ind.tag), Level::Zero);
        for (name, ty) in &ind.ctors[i].fields {
            let (t, l) = self.elab_ty(&fcx, ty)?;
            entries.push((t.clone(), l.clone()));
            fcx.push(name.clone().unwrap_or_else(|| "#field".into()), t, l);
        }
        let _ = span;
        let mut acc = Type::Unit;
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

    // -- reading a lowered type back ----------------------------------------

    /// Split a lowered `⟦D⟧` into its `n` constructor summands (§3.2). `n`
    /// comes from the declaration, never from the shape, so a constructor
    /// whose own encoding is a `+` could not confuse it.
    pub(crate) fn spine(&self, ty: &Type, lvl: &Level, n: usize, span: Span) -> R<Spine> {
        let mut ctors = Vec::with_capacity(n);
        let mut tails = Vec::with_capacity(n.saturating_sub(1));
        let mut cur = Rc::new(ty.clone());
        let mut cur_lvl = lvl.clone();
        for _ in 0..n.saturating_sub(1) {
            let Type::Sum { lhs_level, rhs_level, lhs, rhs } = &*cur else {
                return err("internal: malformed inductive encoding (expected a `+`)", span);
            };
            ctors.push((Rc::clone(lhs), lhs_level.clone()));
            tails.push((Rc::clone(rhs), rhs_level.clone()));
            cur_lvl = rhs_level.clone();
            cur = Rc::clone(rhs);
        }
        ctors.push((cur, cur_lvl));
        Ok(Spine { ctors, tails })
    }

    /// Which declaration a lowered type belongs to, by its nominal tag: walk
    /// to the leftmost constructor and read its tag field (§3.3). `None` for
    /// anything that is not an inductive encoding.
    pub(crate) fn tag_of(&self, ty: &Type) -> Option<Rc<Inductive>> {
        let mut cur = ty;
        while let Type::Sum { lhs, .. } = cur {
            cur = lhs;
        }
        let Type::Sigma { fst, .. } = cur else { return None };
        self.by_tag.get(&read_tag(fst)?).cloned()
    }

    /// The surface field types of a constructor, for the narrow type-argument
    /// inference in [`Elaborator::infer_ctor`].
    pub(crate) fn ctor_fields(&self, ind: &Inductive, i: usize) -> Vec<Ty> {
        ind.ctors[i].fields.iter().map(|(_, t)| t.clone()).collect()
    }

    pub(crate) fn ctor_of(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        self.ctors.get(name).map(|(i, k)| (Rc::clone(i), *k))
    }

    // -- constructors (§4) --------------------------------------------------

    /// Build `⟦c_i(a⃗)⟧` at a known type: the injection path, then the field
    /// tuple. Every annotation comes from `expected`, so this is total on a
    /// well-formed encoding and produces a kernel-rejected term otherwise.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_ctor(
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
        if args.len() != ctor.fields.len() {
            return err(
                format!(
                    "`{}` takes {} argument(s), found {}",
                    ctor.name,
                    ctor.fields.len(),
                    args.len()
                ),
                span,
            );
        }
        let expected = self.whnf(cx, expected, span)?;
        match self.tag_of(&expected) {
            Some(found) if found.tag == ind.tag => {}
            _ => {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, which is not the expected type here",
                        ctor.name, ind.name
                    ),
                    span,
                )
            }
        }
        let spine = self.spine(&expected, expected_lvl, ind.ctors.len(), span)?;
        let mut val = self.build_fields(cx, &spine.ctors[i].0, args, true, span)?;
        // …then the injection path: `Inl` unless this is the last constructor,
        // under `i` `Inr`s.
        if i + 1 < ind.ctors.len() {
            val = Term::Inl {
                lhs_level: spine.ctors[i].1.clone(),
                rhs_level: spine.tails[i].1.clone(),
                lhs: Rc::clone(&spine.ctors[i].0),
                rhs: Rc::clone(&spine.tails[i].0),
                val: Rc::new(val),
            };
        }
        for j in (0..i).rev() {
            val = Term::Inr {
                lhs_level: spine.ctors[j].1.clone(),
                rhs_level: spine.tails[j].1.clone(),
                lhs: Rc::clone(&spine.ctors[j].0),
                rhs: Rc::clone(&spine.tails[j].0),
                val: Rc::new(val),
            };
        }
        Ok(val)
    }

    /// The field tuple: `pair(tag_refl, pair(a₁, … pair(a_k, ⟨⟩)))`, walking
    /// the Σ spine of `⟦c_i⟧` and checking each argument against the component
    /// the spine says it must have. `tag` marks the first component, which is
    /// the nominal tag rather than a field.
    fn build_fields(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        args: &[Expr],
        tag: bool,
        span: Span,
    ) -> R<Term> {
        let head = self.whnf(cx, ctor_ty, span)?;
        let Type::Sigma { fst_level, snd_level, fst, snd } = head else {
            // The Unit terminator (§3.1): every field consumed.
            if matches!(head, Type::Unit) && args.is_empty() {
                return Ok(Term::Triv);
            }
            return err("internal: malformed constructor encoding", span);
        };
        // The tag's inhabitant is `refl`, with the annotations read off the
        // encoding's own `Id` rather than rebuilt.
        let (value, rest) = if tag {
            (tag_value(&fst), args)
        } else {
            let (arg, rest) = args
                .split_first()
                .ok_or(crate::ElabError::Elab { msg: "too few arguments".into(), span })?;
            (self.elab_check(cx, arg, &fst, &fst_level)?, rest)
        };
        let value = Rc::new(value);
        let tail = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&value)));
        let tail_tm = self.build_fields(cx, &tail, rest, false, span)?;
        Ok(Term::Pair {
            fst_level,
            snd_level,
            fst_ty: fst,
            snd_ty: snd,
            fst: value,
            snd: Rc::new(tail_tm),
        })
    }

    // -- match (§5) ---------------------------------------------------------

    /// `match` on a tier-0 inductive: nested `Case`, with the motive composed
    /// with the injection at each depth (§5.2).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_data(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[Arm],
        scrut: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let n = ind.ctors.len();
        // Arms are permuted into declaration order; completeness, duplication
        // and arity are surface obligations, resolved before any lowering.
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
        if n == 0 {
            // No constructors: the scrutinee is `Empty`, and the `match` is
            // absurdity elimination — the absurd-pattern case (§5.2).
            if !arms.is_empty() {
                return err(format!("`{}` has no constructors", ind.name), span);
            }
            return Ok(Term::ElimEmpty {
                level: mlvl,
                motive: Rc::new(motive),
                scrut: Rc::new(scrut),
            });
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
        let arms: Vec<&Arm> = ordered.into_iter().map(|a| a.expect("checked above")).collect();
        let spine = self.spine(scrut_ty, scrut_lvl, n, span)?;
        self.case_tree(cx, &arms, &spine, 0, motive, &mlvl, Rc::new(scrut))
    }

    /// The nested-`Case` recursion of §5.2. At depth `j` the context is `cx` —
    /// `Γ` plus the `j` `case_r` binders already pushed — `motive` is `M_j`
    /// over `cx, z : R_j`, and `scrut` is the `R_j`-typed scrutinee.
    ///
    /// `spine`'s components are scoped in the *original* `Γ`, so every use of
    /// one at depth `j` is weakened by `j` (and by `j+1` under a freshly pushed
    /// binder). The motive needs no such treatment: it is re-scoped by the
    /// substitution that composes it with the injection.
    #[allow(clippy::too_many_arguments)]
    fn case_tree(
        &self,
        cx: &Cx,
        arms: &[&Arm],
        spine: &Spine,
        j: usize,
        motive: Type,
        mlvl: &Level,
        scrut: Rc<Term>,
    ) -> R<Term> {
        let n = arms.len();
        let d = j as u32;
        if j + 1 == n {
            // Last constructor: no `Case` — the arm body itself, checked at
            // `M_j[scrut/z]`. At `j = 0` that is the whole `match`.
            let expected =
                motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut)));
            let ctor_ty = spine.ctors[j].0.shift_local(d);
            return self.elab_arm(cx, arms[j], &ctor_ty, &scrut, &expected, mlvl);
        }
        let ctor_lvl = spine.ctors[j].1.clone();
        let tail_lvl = spine.tails[j].1.clone();
        let ctor_ty = Rc::new(spine.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(spine.tails[j].0.shift_local(d));
        // case_l: binder `x : ⟦c_j⟧` over Γ_j, body at `M_j[inl x/z]`.
        let mut lcx = cx.clone();
        lcx.push("#scrut".into(), (*ctor_ty).clone(), ctor_lvl.clone());
        let injected = |val: Term, inl: bool| {
            let (lhs, rhs) = (spine.ctors[j].0.shift_local(d + 1), spine.tails[j].0.shift_local(d + 1));
            let (lhs, rhs) = (Rc::new(lhs), Rc::new(rhs));
            let (lhs_level, rhs_level) = (ctor_lvl.clone(), tail_lvl.clone());
            let val = Rc::new(val);
            if inl {
                Term::Inl { lhs_level, rhs_level, lhs, rhs, val }
            } else {
                Term::Inr { lhs_level, rhs_level, lhs, rhs, val }
            }
        };
        let l_expected = motive
            .apply_local(&embed(&cx.gamma, 1).extended(Rc::new(injected(Term::Var(LocalVar(0)), true))));
        let case_l = self.elab_arm(
            &lcx,
            arms[j],
            &spine.ctors[j].0.shift_local(d + 1),
            &Rc::new(Term::Var(LocalVar(0))),
            &l_expected,
            mlvl,
        )?;
        // case_r: binder `y : R_{j+1}` over Γ_j; inside it, the next `Case` on
        // `y`, whose motive is `M_j` composed with `inr` and weakened past `y`.
        let mut rcx = cx.clone();
        rcx.push("#rest".into(), (*tail_ty).clone(), tail_lvl.clone());
        let inner_motive = motive
            .apply_local(&embed(&cx.gamma, 2).extended(Rc::new(injected(Term::Var(LocalVar(0)), false))));
        let case_r = self.case_tree(
            &rcx,
            arms,
            spine,
            j + 1,
            inner_motive,
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
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

    /// One arm body, with its field binders bound to projections of the
    /// constructor value (§5.1). The binders are *aliases*, not kernel
    /// binders: the kernel has no `let`, so each use is the projection term.
    /// `ctor_ty` is `⟦c_i⟧` scoped in `cx`.
    fn elab_arm(
        &self,
        cx: &Cx,
        arm: &Arm,
        ctor_ty: &Type,
        value: &Rc<Term>,
        expected: &Type,
        mlvl: &Level,
    ) -> R<Term> {
        let mut acx = cx.clone();
        // Walk the Σ spine of the constructor, skipping the tag (entry 0), and
        // alias each surface binder to `fst(snd^j value)`.
        let mut cur = ctor_ty.clone();
        let mut pair = Rc::clone(value);
        let mut binders = arm.binders.iter();
        let mut first = true;
        loop {
            let head = self.whnf(&acx, &cur, arm.span)?;
            let Type::Sigma { fst_level, snd_level, fst, snd } = head else {
                break;
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
            if first {
                // The nominal tag: no surface name, not bindable.
                first = false;
                continue;
            }
            let Some(name) = binders.next() else { break };
            acx.aliases.push(Rc::new(Alias {
                name: name.clone(),
                depth: acx.names.len(),
                term: proj,
                ty: (*fst).clone(),
                level: fst_level,
            }));
        }
        self.elab_check(&acx, &arm.body, expected, mlvl)
    }
}

/// Where `name` occurs in a surface type, if it does — the tier-classification
/// scan (§2). Only *occurrence* today: the surface has no function type, so a
/// negative occurrence cannot be written, and the strict-positivity refinement
/// lands with tier 1.
fn occurs(t: &Ty, name: &str) -> Option<Span> {
    match &t.kind {
        TyKind::Nat => None,
        TyKind::Eq(..) => None,
        TyKind::Named { name: n, args } => {
            if n == name {
                return Some(t.span);
            }
            args.iter().find_map(|a| occurs(a, name))
        }
    }
}


// -- no-confusion (§6) ------------------------------------------------------

/// Which branch body a constant-motive case tree puts at each constructor.
enum ConstBody {
    /// §6.1: the code of `Unit` at constructor `i`, of `Empty` elsewhere. The
    /// motive is `Ty 0` — this is the large elimination, and it is what makes
    /// two distinct constructors provably distinct.
    TagCode(usize),
    /// §6.2: the `k`-th field projection at constructor `i`, and a default
    /// term (the left-hand side's own field value) elsewhere, so that the
    /// projection is total on `⟦D⟧`.
    Field { i: usize, k: usize, default: Rc<Term> },
}

impl Elaborator {
    /// A case tree with a *constant* motive. Simpler than §5.2's: with the
    /// motive independent of the scrutinee there is no injection to compose
    /// with, only the weakening that each pushed binder demands.
    ///
    /// `motive` and `spine` are scoped in the context the caller built them in;
    /// `d` counts the binders pushed since, so a spine component used here is
    /// weakened by `d` (or `d+1` under a branch binder). `j` is the constructor
    /// index — *not* the same counter as `d`, since these trees are built
    /// several binders deep (inside a `J` motive, `d` starts at 2).
    #[allow(clippy::too_many_arguments)]
    fn const_case_tree(
        &self,
        cx: &Cx,
        spine: &Spine,
        n: usize,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &ConstBody,
        j: usize,
        d: u32,
        span: Span,
    ) -> R<Term> {
        if j + 1 == n {
            // The last constructor: no `Case`, so the branch body is scoped in
            // `cx` itself with the scrutinee standing in for the binder.
            return self.const_body(cx, spine, j, &scrut, body, d, span);
        }
        let ctor_lvl = spine.ctors[j].1.clone();
        let tail_lvl = spine.tails[j].1.clone();
        let ctor_ty = Rc::new(spine.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(spine.tails[j].0.shift_local(d));
        let mut bcx = cx.clone();
        bcx.push("#c".into(), (*ctor_ty).clone(), ctor_lvl.clone());
        let case_l = self.const_body(
            &bcx,
            spine,
            j,
            &Rc::new(Term::Var(LocalVar(0))),
            body,
            d + 1,
            span,
        )?;
        let mut rcx = cx.clone();
        rcx.push("#r".into(), (*tail_ty).clone(), tail_lvl.clone());
        let case_r = self.const_case_tree(
            &rcx,
            spine,
            n,
            &motive.shift_local(1),
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
            body,
            j + 1,
            d + 1,
            span,
        )?;
        Ok(Term::Case {
            lhs_level: ctor_lvl,
            rhs_level: tail_lvl,
            motive_level: mlvl.clone(),
            lhs: ctor_ty,
            rhs: tail_ty,
            // The motive binds `z`, which a constant motive simply ignores.
            motive: Rc::new(motive.shift_local(1)),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    /// One branch of [`Self::const_case_tree`], for constructor `j`, with
    /// `value : ⟦c_j⟧` scoped in `cx`.
    #[allow(clippy::too_many_arguments)]
    fn const_body(
        &self,
        cx: &Cx,
        spine: &Spine,
        j: usize,
        value: &Rc<Term>,
        body: &ConstBody,
        d: u32,
        span: Span,
    ) -> R<Term> {
        match body {
            ConstBody::TagCode(i) => {
                Ok(if j == *i { Term::TmUnit } else { Term::TmEmpty })
            }
            ConstBody::Field { i, k, default } => {
                if j != *i {
                    return Ok(default.shift_local(d));
                }
                let ctor_ty = spine.ctors[j].0.shift_local(d);
                let (proj, _, _) = self.projection(cx, &ctor_ty, value, *k, span)?;
                Ok((*proj).clone())
            }
        }
    }

    /// The `k`-th field projection `fst(snd^{k+1} value)` and its type (§5.1;
    /// the `+1` is the nominal tag). `ctor_ty` is `⟦c_i⟧` scoped in `cx`.
    fn projection(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        value: &Rc<Term>,
        k: usize,
        span: Span,
    ) -> R<(Rc<Term>, Type, Level)> {
        let mut cur = ctor_ty.clone();
        let mut pair = Rc::clone(value);
        // Component 0 is the tag, so field `k` is component `k+1`.
        for step in 0..=k + 1 {
            let head = self.whnf(cx, &cur, span)?;
            let Type::Sigma { fst_level, snd_level, fst, snd } = head else {
                return err("internal: constructor encoding is too short", span);
            };
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&snd),
                pair: Rc::clone(&pair),
            });
            if step == k + 1 {
                return Ok((proj, (*fst).clone(), fst_level));
            }
            pair = Rc::new(Term::Snd {
                fst_level,
                snd_level,
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&snd),
                pair: Rc::clone(&pair),
            });
            cur = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(proj));
        }
        err("internal: projection walked off the end", span)
    }

    /// Read a canonical constructor term back: its index and its field values.
    /// `None` if the term is not a constructor of `ind` in canonical form —
    /// which is a diagnosable surface condition, not an internal error, since
    /// no-confusion is only meaningful between actual constructors.
    fn read_ctor(&self, ind: &Inductive, t: &Term) -> Option<(usize, Vec<Rc<Term>>)> {
        let n = ind.ctors.len();
        let mut i = 0usize;
        let mut cur = t;
        loop {
            match cur {
                Term::Inr { val, .. } if i + 1 < n => {
                    i += 1;
                    cur = val;
                }
                Term::Inl { val, .. } => {
                    cur = val;
                    break;
                }
                _ => break,
            }
        }
        if i >= n {
            return None;
        }
        // Skip the nominal tag, then collect one value per declared field.
        let Term::Pair { snd, .. } = cur else { return None };
        let mut p = snd;
        let mut fields = Vec::new();
        for _ in 0..ind.ctors[i].fields.len() {
            let Term::Pair { fst, snd, .. } = &**p else { return None };
            fields.push(Rc::clone(fst));
            p = snd;
        }
        Some((i, fields))
    }

    /// The equation an `absurd`/`inj` argument must prove, with both sides read
    /// back as constructors.
    #[allow(clippy::type_complexity)]
    fn equation(
        &self,
        cx: &Cx,
        e: &Expr,
        who: &str,
    ) -> R<(Term, Rc<Inductive>, Type, Level, Rc<Term>, Rc<Term>, (usize, Vec<Rc<Term>>), (usize, Vec<Rc<Term>>))>
    {
        let (proof, proof_ty, _) = self.elab_infer(cx, e)?;
        let Type::Id { level, ty, lhs, rhs } = self.whnf(cx, &proof_ty, e.span)? else {
            return err(format!("`{who}` needs a proof of an `=` between constructors"), e.span);
        };
        let sty = self.whnf(cx, &ty, e.span)?;
        let Some(ind) = self.tag_of(&sty) else {
            return err(
                format!("`{who}` needs an equation at a declared inductive type"),
                e.span,
            );
        };
        let (Some(l), Some(r)) = (self.read_ctor(&ind, &lhs), self.read_ctor(&ind, &rhs)) else {
            return err(
                format!(
                    "`{who}` needs both sides of the equation to be constructor applications"
                ),
                e.span,
            );
        };
        Ok((proof, ind, sty, level, lhs, rhs, l, r))
    }

    /// §6.1, disjointness: from an equation between *different* constructors,
    /// anything. The tag predicate ignores the fields, so it lands in `Ty 0`
    /// whatever the field levels are, and both `El` reductions are
    /// definitional — which is why the transported case is just `⟨⟩`.
    pub(crate) fn build_absurd(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let (proof, ind, sty, slvl, lhs, rhs, (i, _), (j, _)) =
            self.equation(cx, arg, "absurd")?;
        if i == j {
            return err(
                format!(
                    "both sides of this equation are `{}`, so it is not absurd \
                     (use `inj` to get the field equations)",
                    ind.ctors[i].name
                ),
                span,
            );
        }
        // The J motive, over `y : ⟦D⟧` and `p : lhs = y`: `El⁰ (tag_i y)`.
        let mut mcx = cx.clone();
        mcx.push("#y".into(), sty.clone(), slvl.clone());
        mcx.push(
            "#p".into(),
            Type::Id {
                level: slvl.clone(),
                ty: Rc::new(sty.shift_local(1)),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(Term::Var(LocalVar(0))),
            },
            slvl.clone(),
        );
        let spine = self.spine(&sty, &slvl, ind.ctors.len(), span)?;
        let pred = self.const_case_tree(
            &mcx,
            &spine,
            ind.ctors.len(),
            &Type::Ty(Level::Zero),
            &Level::succ(Level::Zero),
            Rc::new(Term::Var(LocalVar(1))),
            &ConstBody::TagCode(i),
            0,
            2,
            span,
        )?;
        let motive = Type::El { level: Level::Zero, tm: Rc::new(pred) };
        let absurd = Term::J {
            ty_level: slvl.clone(),
            motive_level: Level::Zero,
            ty: Rc::new(sty),
            lhs,
            motive: Rc::new(motive),
            // `El⁰ (tag_i lhs) ⇝ El ⌜Unit⌝ ⇝ Unit`, definitionally.
            case: Rc::new(Term::Triv),
            rhs,
            proof: Rc::new(proof),
        };
        // …and `El⁰ (tag_i rhs) ⇝ Empty`, so this eliminates into anything.
        Ok(Term::ElimEmpty {
            level: expected_lvl.clone(),
            motive: Rc::new(expected.shift_local(1)),
            scrut: Rc::new(absurd),
        })
    }

    /// §6.2, injectivity: from an equation between the *same* constructor, the
    /// equation between its `k`-th fields, by congruence of a total projection.
    ///
    /// The projection needs a value at the other constructors; this takes the
    /// left-hand side's own field, which is in scope and of exactly the right
    /// type. That keeps the motive constant — no code-valued family, and so
    /// none of the level restriction the document's first version carried.
    /// The price: the field's type must not depend on the constructor's
    /// earlier fields, which is checked (by conversion) rather than assumed.
    pub(crate) fn build_inj(
        &self,
        cx: &Cx,
        k: usize,
        arg: &Expr,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (proof, ind, sty, slvl, lhs, rhs, (i, la), (j, rb)) =
            self.equation(cx, arg, "inj")?;
        if i != j {
            return err(
                format!(
                    "this equation is between `{}` and `{}`, which are different constructors \
                     (use `absurd`)",
                    ind.ctors[i].name, ind.ctors[j].name
                ),
                span,
            );
        }
        let arity = ind.ctors[i].fields.len();
        if k >= arity {
            return err(
                format!("`{}` has {arity} field(s), so there is no field {k}", ind.ctors[i].name),
                span,
            );
        }
        let spine = self.spine(&sty, &slvl, ind.ctors.len(), span)?;
        // The field type at each side. They differ exactly when the field's
        // type depends on an earlier field of the same constructor.
        let (_, lty, llvl) = self.projection(cx, &spine.ctors[i].0, &lhs, k, span)?;
        let (_, rty, _) = self.projection(cx, &spine.ctors[i].0, &rhs, k, span)?;
        // Layer p: conversion is only defined at computing layers, and this
        // comparison is the elaborator's own, not part of an emitted term.
        if conv_type(self.psi(), &cx.gamma, Layer::Prog, &lty, &rty, &llvl, self.fuel).is_err() {
            return err(
                format!(
                    "field {k} of `{}` has a type that depends on an earlier field, so its \
                     injectivity is not derivable this way yet \
                     (docs/inductive-tier0-lowering.md §6.2)",
                    ind.ctors[i].name
                ),
                span,
            );
        }
        // The J motive, over `y` and `p : lhs = y`: `a_k = proj y`.
        let mut mcx = cx.clone();
        mcx.push("#y".into(), sty.clone(), slvl.clone());
        mcx.push(
            "#p".into(),
            Type::Id {
                level: slvl.clone(),
                ty: Rc::new(sty.shift_local(1)),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(Term::Var(LocalVar(0))),
            },
            slvl.clone(),
        );
        let proj = self.const_case_tree(
            &mcx,
            &spine,
            ind.ctors.len(),
            &lty.shift_local(2),
            &llvl,
            Rc::new(Term::Var(LocalVar(1))),
            &ConstBody::Field { i, k, default: Rc::clone(&la[k]) },
            0,
            2,
            span,
        )?;
        let motive = Type::Id {
            level: llvl.clone(),
            ty: Rc::new(lty.shift_local(2)),
            lhs: Rc::new(la[k].shift_local(2)),
            rhs: Rc::new(proj),
        };
        let term = Term::J {
            ty_level: slvl,
            motive_level: llvl.clone(),
            ty: Rc::new(sty),
            lhs,
            motive: Rc::new(motive),
            // At `y := lhs` the projection computes back to `a_k`.
            case: Rc::new(Term::Refl {
                level: llvl.clone(),
                ty: Rc::new(lty.clone()),
                tm: Rc::clone(&la[k]),
            }),
            rhs,
            proof: Rc::new(proof),
        };
        // The J term's type mentions the projection; report the type the user
        // means, which it reduces to.
        let result = Type::Id {
            level: llvl.clone(),
            ty: Rc::new(lty),
            lhs: Rc::clone(&la[k]),
            rhs: Rc::clone(&rb[k]),
        };
        Ok((term, result, llvl))
    }
}
