//! Surface vector operations and container-recursion lowering.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type, nth};
use heather_syntax::{Expr, ExprKind, Span};

use super::{fold, map, strengthen, tab_cong, tabulate};
use crate::recursion::GuardKind;
use crate::slots::{Ingredient, Slot};
use crate::{Cx, R, err};

/// Semantic capabilities used by surface vector operations.
///
/// This module owns vector recognition, schema selection, container-IH
/// tabulation, and vector-specific diagnostics. Recursive expression work,
/// normalization, and optional meta-template execution remain explicit
/// capabilities of the root elaborator.
pub(crate) trait SurfaceVecElab {
    fn infer_vector_expr(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)>;
    fn check_vector_expr(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
    ) -> R<Term>;
    fn whnf_vector_type(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type>;
    fn whnf_vector_term(&self, cx: &Cx, term: &Term, span: Span) -> R<Rc<Term>>;
    fn try_vector_template(
        &self,
        cx: &Cx,
        slot: Slot,
        ingredients: &[(&'static str, Ingredient<'_>)],
        span: Span,
    ) -> R<Option<Term>>;
}

/// The arity branch of a builtin vector method, which cannot say what it
/// is about until it has looked at the receiver
/// (issues/receiver-method-shadows-record-field.md).
///
/// These builtins all open with `elab_infer` on the receiver, so a
/// receiver whose type does not infer can never reach one of them — but
/// the arity test runs *first*, and used to announce "on a vector
/// receiver" about a receiver nobody had read. At a record with a field
/// named `fold`, reached off a receiver that needs a motive, that made
/// the elaborator assert something false in place of the one diagnostic
/// the writer could act on.
///
/// So the order here is the order the body would have taken anyway, and
/// the wrong-arity message is uttered only where it is true. The receiver
/// failing to infer is its own diagnosis and is returned as-is: it is
/// exactly what the writer gets when the arity is *right*, so the two
/// paths no longer disagree about the same receiver.
pub(crate) fn method_arity_error<T>(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    args: &[Expr],
    name: &str,
    shape: &str,
    span: Span,
) -> R<T> {
    let [recv, ..] = args else {
        // No receiver at all — the direct spelling `fold()`, since the dot
        // always supplies one. Nothing to read, but nothing is being
        // guessed either: these builtins *are* the vector eliminators, so
        // what they require is a fact about them rather than a claim about
        // some receiver.
        return err(format!("`{name}` needs a vector receiver"), span);
    };
    let (_, ty, _) = elab.infer_vector_expr(cx, recv)?;
    if !matches!(*crate::inductive::decoded(&ty), Type::Vec { .. }) {
        return err(format!("`{name}`'s receiver has to be a vector"), span);
    }
    err(format!("`{name}` takes {shape} on a vector receiver"), span)
}

/// `xs.map(f)`. Two forms, and the split is what
/// `docs/container-fields.md` §4.2 is about:
///
/// - `f` is an ordinary function: the `elim_Nat` schema `map`.
/// - `f` is the **self-name** and `xs` the enclosing arm's container
///   binder: the induction hypothesis, *tabulated* over the container's
///   index range. It cannot be the first form, because the self-name is
///   not a value — there is no fixpoint, and the recursive call exists
///   only as the eliminator's ih (issues/match-recursion.md).
pub(crate) fn elab_map(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    f: &Expr,
    xs: &Expr,
    span: Span,
) -> R<(Term, Type, Level)> {
    let (xs_t, xs_ty, _) = elab.infer_vector_expr(cx, xs)?;
    // `decoded`, not `whnf`: the receiver may be a vector *field* projected
    // out of a record that arrived as a code, in which case its type is
    // `El (TmVec …)` (docs/record-type-values.md §6). Reducing further
    // would unfold the `Vec` into its Σ-chain and lose the element type
    // and the length this reads off it — the same reason `elab_vec_lit`
    // decodes rather than normalizes.
    let xs_ty = &*crate::inductive::decoded(&xs_ty);
    let Type::Vec {
        level: al,
        elem: a_ty,
        len,
    } = xs_ty
    else {
        return err("`map`'s receiver has to be a vector", span);
    };
    // The self-call form.
    if let ExprKind::Var(name) = &f.kind
        && cx.selfref.as_ref().is_some_and(|s| s.matches(name))
    {
        return elab_container_ih(elab, cx, name, &xs_t, false, span);
    }
    let (f_t, f_ty, _) = elab.infer_vector_expr(cx, f)?;
    let Type::Pi {
        cod_level: bl,
        dom,
        cod,
        ..
    } = elab.whnf_vector_type(cx, &f_ty, span)?
    else {
        return err("`map`'s argument has to be a function", span);
    };
    let Some(b_ty) = strengthen(&cod, &cx.gamma) else {
        return err(
            "`map`'s function must not have a dependent result type: the result \
             is a vector, whose elements all have one type",
            span,
        );
    };
    let _ = dom;
    // The evaluation hook (docs/in-language-map-design.md §4): when a
    // template claims `vec.map`, the emitted term comes from evaluating it
    // — kernel computation mid-elaboration — and the Rust schema below
    // serves the instances the level-0 template declines, and every file
    // that declares no template at all. What this site knows is the slot
    // and the *names* of its ingredients; the Π order is the template's
    // own and lives in its signature
    // (docs/meta-def-registration-design.md §3).
    if let Some(t) = elab.try_vector_template(
        cx,
        Slot::VecMap,
        &[
            (
                "A",
                Ingredient::Type {
                    level: al,
                    ty: a_ty,
                },
            ),
            (
                "B",
                Ingredient::Type {
                    level: &bl,
                    ty: &b_ty,
                },
            ),
            ("f", Ingredient::Term(f_t.clone())),
            ("k", Ingredient::Term((**len).clone())),
            ("v", Ingredient::Term(xs_t.clone())),
        ],
        span,
    )? {
        return Ok((
            t,
            Type::Vec {
                level: bl.clone(),
                elem: Rc::new(b_ty),
                len: Rc::clone(len),
            },
            bl,
        ));
    }
    Ok((
        map(al, &bl, a_ty, &b_ty, len, Rc::new(f_t), Rc::new(xs_t)),
        Type::Vec {
            level: bl.clone(),
            elem: Rc::new(b_ty),
            len: Rc::clone(len),
        },
        bl,
    ))
}

/// `head(v)` / `tail(v)` on a vector whose length reduces to a successor:
/// the projections of the `Σ` that `Vec(A; S k)` computes to, annotated
/// with its components. A neutral length is a diagnostic — there is no
/// projection out of a vector that might be empty.
pub(crate) fn elab_head_tail(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    v: &Expr,
    is_head: bool,
    span: Span,
) -> R<(Term, Type, Level)> {
    let (v_t, v_ty, _) = elab.infer_vector_expr(cx, v)?;
    // `decoded`, as in `elab_map`: a coded `Vec` field is one.
    let v_ty = &*crate::inductive::decoded(&v_ty);
    let Type::Vec { level, elem, len } = v_ty else {
        let name = if is_head { "head" } else { "tail" };
        return err(format!("`{name}`'s receiver has to be a vector"), span);
    };
    let len_w = elab.whnf_vector_term(cx, len, span)?;
    let crate::inductive::NatHead::Succ(pred) = crate::inductive::nat_head(&len_w) else {
        let name = if is_head { "head" } else { "tail" };
        return err(
            format!(
                "`{name}` needs a vector whose length reduces to a successor — \
                 this one's does not, so it might be empty"
            ),
            span,
        );
    };
    // `Vec(A; S k) ⇝ Σ(x: A). Vec(A↑; k↑)` — the Σ annotations, exactly
    // as `reduce.rs` spells the reduct.
    let snd_ty = Rc::new(Type::Vec {
        level: level.clone(),
        elem: Rc::new(elem.shift_local(1)),
        len: Rc::new(pred.shift_local(1)),
    });
    let (term, ty) = if is_head {
        (
            Term::Fst {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::clone(elem),
                snd_ty,
                pair: Rc::new(v_t),
            },
            (**elem).clone(),
        )
    } else {
        (
            Term::Snd {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::clone(elem),
                snd_ty,
                pair: Rc::new(v_t),
            },
            // `snd_ty[fst p/x]` — no dependence, so the unshifted spelling.
            Type::Vec {
                level: level.clone(),
                elem: Rc::clone(elem),
                len: Rc::clone(&pred),
            },
        )
    };
    Ok((term, ty, level.clone()))
}

/// `cons(h, t)`: the pair of the same `Σ`, inferring from the tail (which
/// carries both the element type and the length).
pub(crate) fn elab_cons(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    h: &Expr,
    t: &Expr,
    span: Span,
) -> R<(Term, Type, Level)> {
    let (t_t, t_ty, _) = elab.infer_vector_expr(cx, t)?;
    let t_ty = &*crate::inductive::decoded(&t_ty);
    let Type::Vec { level, elem, len } = t_ty else {
        return err(
            "`cons`'s second argument has to be a vector (the tail)",
            span,
        );
    };
    let h_t = elab.check_vector_expr(cx, h, elem, level)?;
    let snd_ty = Rc::new(Type::Vec {
        level: level.clone(),
        elem: Rc::new(elem.shift_local(1)),
        len: Rc::new(len.shift_local(1)),
    });
    Ok((
        Term::Pair {
            fst_level: level.clone(),
            snd_level: level.clone(),
            fst_ty: Rc::clone(elem),
            snd_ty,
            fst: Rc::new(h_t),
            snd: Rc::new(t_t),
        },
        Type::Vec {
            level: level.clone(),
            elem: Rc::clone(elem),
            len: Rc::new(Term::Succ(Rc::clone(len))),
        },
        level.clone(),
    ))
}

/// `xs.fold(init, f)` for `f : A → B → B`. A right fold: `[a, b]` folds to
/// `f a (f b init)`, which is the direction that computes on a
/// constructor form.
pub(crate) fn elab_fold(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    z: &Expr,
    f: &Expr,
    xs: &Expr,
    span: Span,
) -> R<(Term, Type, Level)> {
    let (xs_t, xs_ty, _) = elab.infer_vector_expr(cx, xs)?;
    // As in `elab_map`: decode a coded `Vec`, and no further.
    let xs_ty = &*crate::inductive::decoded(&xs_ty);
    let Type::Vec {
        level: al,
        elem: a_ty,
        len,
    } = xs_ty
    else {
        return err("`fold`'s receiver has to be a vector", span);
    };
    let (z_t, b_ty, bl) = elab.infer_vector_expr(cx, z)?;
    let step_ty = Type::Pi {
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::clone(a_ty),
        cod: Rc::new(Type::Pi {
            dom_level: bl.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(b_ty.shift_local(1)),
            cod: Rc::new(b_ty.shift_local(2)),
        }),
    };
    let f_t = elab.check_vector_expr(cx, f, &step_ty, &Level::max(al.clone(), bl.clone()))?;
    // The evaluation hook, as in `elab_map`: whichever template claims
    // `vec.fold` serves this use site, and the Rust schema below serves the
    // instances the level-0 template declines — and every file that
    // declares no template (issues/quotation-stage-artifacts.md).
    if let Some(t) = elab.try_vector_template(
        cx,
        Slot::VecFold,
        &[
            (
                "A",
                Ingredient::Type {
                    level: al,
                    ty: a_ty,
                },
            ),
            (
                "B",
                Ingredient::Type {
                    level: &bl,
                    ty: &b_ty,
                },
            ),
            ("z", Ingredient::Term(z_t.clone())),
            ("f", Ingredient::Term(f_t.clone())),
            ("k", Ingredient::Term((**len).clone())),
            ("v", Ingredient::Term(xs_t.clone())),
        ],
        span,
    )? {
        return Ok((t, b_ty, bl));
    }
    Ok((
        fold(
            al,
            &bl,
            a_ty,
            &b_ty,
            len,
            Rc::new(z_t),
            Rc::new(f_t),
            Rc::new(xs_t),
        ),
        b_ty,
        bl,
    ))
}

/// `xs[i]` — the kernel's `nth` schema
/// (docs/surface-fin-indexing-design.md §5.2). Modelled on
/// [`elab_fold`], and inferring rather than checking: the
/// element type comes off the receiver.
///
/// The index is **checked** at `Fin(len)` with the receiver's own length,
/// which is what makes an index of the wrong vector's length a diagnostic
/// rather than a silent coercion.
pub(crate) fn elab_nth(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    recv: &Expr,
    idx: &Expr,
    span: Span,
) -> R<(Term, Type, Level)> {
    let (xs_t, xs_ty, _) = elab.infer_vector_expr(cx, recv)?;
    // As in `elab_map`: decode a coded `Vec`, and no further.
    let xs_ty = &*crate::inductive::decoded(&xs_ty);
    let Type::Vec {
        level: vl,
        elem,
        len,
    } = xs_ty
    else {
        return err("an index needs a vector receiver", span);
    };
    let idx_t = elab.check_vector_expr(
        cx,
        idx,
        &Type::Fin {
            len: Rc::clone(len),
        },
        &Level::Zero,
    )?;
    // The evaluation hook, as in `elab_map`/`elab_fold`:
    // `lib/vec_code.hthr`'s `nth_code` claims `vec.nth` when the lib is in
    // scope, and this declines silently when it is not. The kernel schema
    // stays the oracle and the fallback either way.
    if let Some(t) = elab.try_vector_template(
        cx,
        Slot::VecNth,
        &[
            (
                "A",
                Ingredient::Type {
                    level: vl,
                    ty: elem,
                },
            ),
            ("k", Ingredient::Term((**len).clone())),
            ("v", Ingredient::Term(xs_t.clone())),
            ("i", Ingredient::Term(idx_t.clone())),
        ],
        span,
    )? {
        return Ok((t, (**elem).clone(), vl.clone()));
    }
    Ok((
        nth(vl, elem, len, Rc::new(xs_t), Rc::new(idx_t)),
        (**elem).clone(),
        vl.clone(),
    ))
}

/// The self-call over a container binder: `tabulate(len, λ(i : Fin len).
/// ih (inr^m i))` (`docs/container-fields.md` §4.2).
///
/// The ih is indexed by `Fin (Succ^m len)` — `m` plain children first,
/// then the container's — so the index map is `m` `inr`s.
pub(crate) fn elab_container_ih(
    elab: &impl SurfaceVecElab,
    cx: &Cx,
    name: &str,
    xs: &Term,
    as_eq: bool,
    span: Span,
) -> R<(Term, Type, Level)> {
    let Some(g) = cx.guard.clone() else {
        return err(
            format!(
                "recursive call to `{name}` is not structurally guarded: it must occur \
                 inside a `match` on one of `{name}`'s own parameters"
            ),
            span,
        );
    };
    let GuardKind::Wf {
        depth,
        container: Some(c),
        ..
    } = &g.kind
    else {
        return err(
            format!("the enclosing `match` arm of `{name}` has no container field"),
            span,
        );
    };
    let by = (cx.names.len() - depth) as u32;
    if c.term.shift_local(by) != *xs {
        return err(
            format!(
                "a recursive call to `{name}` over a vector has to be over the \
                 container field bound by the enclosing `match`"
            ),
            span,
        );
    }
    // The two spellings are not interchangeable: `.map` produces data and
    // `.cong` produces a proof, so each is rejected where the other belongs
    // (docs/container-proofs.md §6).
    if as_eq && c.result.is_some() {
        return err(
            format!(
                "`{name}`'s result type does not depend on its argument, so a                      recursive call over a container produces a vector of results,                      not an equation between two: write `.map({name})`"
            ),
            span,
        );
    }
    if !as_eq && c.eq.is_some() {
        return err(
            format!(
                "`{name}` proves an equation, so a recursive call over a container                      proves the two children vectors equal rather than producing one:                      write `.cong({name})` (docs/container-proofs.md §6)"
            ),
            span,
        );
    }
    if c.result.is_none() && c.eq.is_none() {
        return err(
            format!(
                "recursing over a container field needs `{name}`'s result type to be \
                 independent of its argument, or else an equation `a = b` at a type \
                 that is (docs/container-proofs.md §7); a dependent result of any \
                 other shape is not supported yet"
            ),
            span,
        );
    }
    let len = c.len.shift_local(by);
    let len_rc = Rc::new(len.clone());
    let elem = c.elem.shift_local(by);
    let ih = c.ih.shift_local(by);
    // `h = λ(i : Fin len). ih (inr^m i)` — the index map, shared by both
    // phases: the ih is indexed by `Fin (Succ^m len)`, so the container's
    // own indices start at `m` (docs/container-fields.md §10.3). The
    // application is annotated with the ih's *own* Π type rather than a
    // rebuilt one, since phase 3's codomain is dependent.
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let mut idx = Term::Var(LocalVar(0));
    for j in 0..c.plain {
        let mut inner = len.shift_local(1);
        for _ in 0..j {
            inner = Term::Succ(Rc::new(inner));
        }
        idx = Term::Inr {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: Rc::new(Type::Fin {
                len: Rc::new(inner),
            }),
            val: Rc::new(idx),
        };
    }
    let Type::Pi {
        dom: ih_dom,
        cod: ih_cod,
        ..
    } = c.ih_ty.shift_local(by + 1)
    else {
        unreachable!("a `Wf` arm's ih is a Π over its index")
    };
    let h = Term::Lam {
        dom_level: Level::Zero,
        cod_level: c.mlvl.clone(),
        dom: Rc::new(Type::Fin {
            len: Rc::clone(&len_rc),
        }),
        body: Rc::new(Term::App {
            fun: Rc::new(ih.shift_local(1)),
            dom_level: Level::Zero,
            cod_level: c.mlvl.clone(),
            dom: ih_dom,
            cod: ih_cod,
            arg: Rc::new(idx),
        }),
    };
    // Phase 2: an independent motive tabulates into a vector of results.
    if let Some(result) = &c.result {
        let result = result.shift_local(by);
        let ty = Type::Vec {
            level: c.mlvl.clone(),
            elem: Rc::new(result.clone()),
            len: Rc::clone(&len_rc),
        };
        // The evaluation hook, as in `elab_map`/`elab_fold` — the
        // call `docs/meta-def-registration-design.md` §9 says this site
        // gains once the surface can write `Fin` and its indices.
        // `lib/vec_code.hthr`'s `tabulate_code` claims `vec.tabulate` when
        // the lib is in scope; without it this declines silently and the
        // schema below runs unchanged.
        //
        // Phase 3's `tabulate`s below are deliberately *not* routed: they
        // build the two endpoints of an `Id` **type**, and a template's
        // output there would change what the proof is a proof of.
        if let Some(t) = elab.try_vector_template(
            cx,
            Slot::VecTabulate,
            &[
                (
                    "B",
                    Ingredient::Type {
                        level: &c.mlvl,
                        ty: &result,
                    },
                ),
                ("k", Ingredient::Term((*len_rc).clone())),
                ("f", Ingredient::Term(h.clone())),
            ],
            span,
        )? {
            return Ok((t, ty, c.mlvl.clone()));
        }
        return Ok((
            tabulate(&c.mlvl, &result, &len_rc, Rc::new(h)),
            ty,
            c.mlvl.clone(),
        ));
    }
    // Phase 3: an equational motive proves the two children *vectors* equal
    // (docs/container-proofs.md §5). `f'`/`g'` are the endpoint functions
    // applied at each index; `h` proves them pointwise equal, verbatim.
    let e = c.eq.as_ref().expect("checked above");
    let (a_ty, kids) = (e.ty.shift_local(by), c.term.shift_local(by));
    let side = |f: &Rc<Term>| {
        let child = nth(
            &c.level,
            &Rc::new(elem.shift_local(1)),
            &Rc::new(len.shift_local(1)),
            Rc::new(kids.shift_local(1)),
            Rc::new(Term::Var(LocalVar(0))),
        );
        Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: e.level.clone(),
            dom: Rc::new(Type::Fin {
                len: Rc::clone(&len_rc),
            }),
            body: Rc::new(Term::App {
                fun: Rc::new(f.shift_local(by + 1)),
                dom_level: c.level.clone(),
                cod_level: e.level.clone(),
                dom: Rc::new(elem.shift_local(1)),
                cod: Rc::new(a_ty.shift_local(2)),
                arg: Rc::new(child),
            }),
        })
    };
    let (f_side, g_side) = (side(&e.lhs), side(&e.rhs));
    Ok((
        tab_cong(
            &e.level,
            &a_ty,
            &len_rc,
            Rc::clone(&f_side),
            Rc::clone(&g_side),
            Rc::new(h),
        ),
        Type::Id {
            level: e.level.clone(),
            ty: Rc::new(Type::Vec {
                level: e.level.clone(),
                elem: Rc::new(a_ty.clone()),
                len: Rc::clone(&len_rc),
            }),
            lhs: Rc::new(tabulate(&e.level, &a_ty, &len_rc, f_side)),
            rhs: Rc::new(tabulate(&e.level, &a_ty, &len_rc, g_side)),
        },
        e.level.clone(),
    ))
}
