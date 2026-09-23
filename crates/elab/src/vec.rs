//! Surface vector operations and their kernel schemas.
//!
//! This module owns `map`, `fold`, `head`, `tail`, `cons`, indexing, and the
//! container-recursion spellings that tabulate an induction hypothesis
//! (`docs/container-fields.md` §4.2, `docs/container-proofs.md` §5).
//!
//! Each is an `elim_Nat` on the *length*, with a motive that is a Π over the
//! vector — the only shape that works, because `Vec` reduces on its length and
//! so a vector of neutral length cannot be projected at all. That is also why
//! these are schemas built here rather than library definitions: the surface
//! has no way to write a recursion on a length.
//!
//! They are modelled on `heather_kernel::term::nth`, which is the same
//! construction one argument wider, and are commented in its style: every
//! index is stated relative to a named context, because de Bruijn arithmetic
//! is where a bug here would hide. Untrusted like the rest of the elaborator —
//! the kernel re-checks every term below — but a wrong schema would produce a
//! *checked theorem about the wrong function*, so no shortcuts.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};

mod surface;
pub(crate) use surface::{
    SurfaceVecElab, elab_cons, elab_container_ih, elab_fold, elab_head_tail, elab_map, elab_nth,
    method_arity_error,
};

fn var(i: u32) -> Rc<Term> {
    Rc::new(Term::Var(LocalVar(i)))
}

/// `Vec^l(A; k)` with `A` shifted by `d`.
fn vec(level: &Level, elem: &Type, d: u32, len: Rc<Term>) -> Type {
    Type::Vec {
        level: level.clone(),
        elem: Rc::new(elem.shift_local(d)),
        len,
    }
}

/// Is `t` — scoped over `(gamma, z)` — independent of `z`? If so, return it
/// strengthened into `gamma`.
///
/// No occurrence traversal: substituting `Zero` for `z` and weakening back is
/// the identity exactly when `z` did not appear, since `shift_local` moves
/// *variables* and leaves the `Zero` that replaced any occurrence behind. Uses
/// only operations `subst.rs` already has, which is the point — a fourth
/// hand-written traversal over the syntax is what that module exists to avoid.
pub(crate) fn strengthen(t: &Type, gamma: &LocalCtx) -> Option<Type> {
    let down = t.apply_local(&LocalSubst::id(gamma).extended(Rc::new(Term::Zero)));
    (down.shift_local(1) == *t).then_some(down)
}

/// `map^{l,l'}(A; B; k; g; xs) : Vec^{l'}(B; k)` for `g : A → B`.
///
/// ```text
/// map(A; B; 0;   g; xs) ⇝ ⟨⟩
/// map(A; B; S k; g; xs) ⇝ (g (fst xs), map(A; B; k; g; snd xs))
/// ```
///
/// All of `a_ty`, `b_ty`, `len`, `g` and `xs` are scoped in the ambient `Γ`,
/// and so is the result.
#[allow(clippy::too_many_arguments)]
pub(crate) fn map(
    al: &Level,
    bl: &Level,
    a_ty: &Type,
    b_ty: &Type,
    len: &Rc<Term>,
    g: Rc<Term>,
    xs: Rc<Term>,
) -> Term {
    let ml = Level::max(al.clone(), bl.clone());
    // Motive in (Γ, k̂): Π(xs : Vec(A; k̂)). Vec(B; k̂).
    let motive = Type::Pi {
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(vec(al, a_ty, 1, var(0))),
        cod: Rc::new(vec(bl, b_ty, 2, var(1))),
    };
    // Base in Γ: λ(xs : Vec(A; 0)). ⟨⟩.
    let base = Term::Lam {
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(vec(al, a_ty, 0, Rc::new(Term::Zero))),
        body: Rc::new(Term::Triv { level: bl.clone() }),
    };
    // Step in (Γ, k̂=1, r=0), under its own λ: (Γ, k̂=2, r=1, xs=0).
    let step = {
        let head = Term::Fst {
            fst_level: al.clone(),
            snd_level: al.clone(),
            fst_ty: Rc::new(a_ty.shift_local(3)),
            snd_ty: Rc::new(vec(al, a_ty, 4, var(3))),
            pair: var(0),
        };
        let tail = Term::Snd {
            fst_level: al.clone(),
            snd_level: al.clone(),
            fst_ty: Rc::new(a_ty.shift_local(3)),
            snd_ty: Rc::new(vec(al, a_ty, 4, var(3))),
            pair: var(0),
        };
        // g head : B, and r tail : Vec(B; k̂).
        let g_head = crate::spelling::checked_app(
            Rc::new(g.shift_local(3)),
            al.clone(),
            bl.clone(),
            Rc::new(a_ty.shift_local(3)),
            Rc::new(b_ty.shift_local(4)),
            Rc::new(head),
        );
        let r_tail = crate::spelling::checked_app(
            var(1),
            al.clone(),
            bl.clone(),
            Rc::new(vec(al, a_ty, 3, var(2))),
            Rc::new(vec(bl, b_ty, 4, var(3))),
            Rc::new(tail),
        );
        Term::Lam {
            dom_level: al.clone(),
            cod_level: bl.clone(),
            // The step proves `M(S k̂)`, so its argument is a vector of length
            // `S k̂` — which is exactly what makes `fst`/`snd` below legal,
            // since `Vec(A; S k̂) ⇝ Σ(_ : A). Vec(A; k̂)`.
            dom: Rc::new(vec(al, a_ty, 2, Rc::new(Term::Succ(var(1))))),
            body: Rc::new(Term::Pair {
                fst_level: bl.clone(),
                snd_level: bl.clone(),
                fst_ty: Rc::new(b_ty.shift_local(3)),
                snd_ty: Rc::new(vec(bl, b_ty, 4, var(3))),
                fst: Rc::new(g_head),
                snd: Rc::new(r_tail),
            }),
        }
    };
    crate::spelling::checked_app(
        Rc::new(Term::ElimNat {
            level: ml,
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::clone(len),
        }),
        al.clone(),
        bl.clone(),
        Rc::new(vec(al, a_ty, 0, Rc::clone(len))),
        Rc::new(vec(bl, b_ty, 1, Rc::new(len.shift_local(1)))),
        xs,
    )
}

/// `fold^{l,l'}(A; B; k; z; g; xs) : B` for `g : A → B → B`.
///
/// ```text
/// fold(A; B; 0;   z; g; xs) ⇝ z
/// fold(A; B; S k; z; g; xs) ⇝ g (fst xs) (fold(A; B; k; z; g; snd xs))
/// ```
///
/// Right fold: `[a, b, c]` folds to `g a (g b (g c z))`, which is the one that
/// computes on a constructor form without needing an accumulator to be
/// threaded through the recursion.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fold(
    al: &Level,
    bl: &Level,
    a_ty: &Type,
    b_ty: &Type,
    len: &Rc<Term>,
    init: Rc<Term>,
    g: Rc<Term>,
    xs: Rc<Term>,
) -> Term {
    let ml = Level::max(al.clone(), bl.clone());
    // Motive in (Γ, k̂): Π(xs : Vec(A; k̂)). B.
    let motive = Type::Pi {
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(vec(al, a_ty, 1, var(0))),
        cod: Rc::new(b_ty.shift_local(2)),
    };
    // Base in Γ: λ(xs : Vec(A; 0)). z.
    let base = Term::Lam {
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(vec(al, a_ty, 0, Rc::new(Term::Zero))),
        body: Rc::new(init.shift_local(1)),
    };
    // Step in (Γ, k̂=1, r=0), under its own λ: (Γ, k̂=2, r=1, xs=0).
    let step = {
        let head = Term::Fst {
            fst_level: al.clone(),
            snd_level: al.clone(),
            fst_ty: Rc::new(a_ty.shift_local(3)),
            snd_ty: Rc::new(vec(al, a_ty, 4, var(3))),
            pair: var(0),
        };
        let tail = Term::Snd {
            fst_level: al.clone(),
            snd_level: al.clone(),
            fst_ty: Rc::new(a_ty.shift_local(3)),
            snd_ty: Rc::new(vec(al, a_ty, 4, var(3))),
            pair: var(0),
        };
        let r_tail = crate::spelling::checked_app(
            var(1),
            al.clone(),
            bl.clone(),
            Rc::new(vec(al, a_ty, 3, var(2))),
            Rc::new(b_ty.shift_local(4)),
            Rc::new(tail),
        );
        // g head (r tail).
        let g_head = crate::spelling::checked_app(
            Rc::new(g.shift_local(3)),
            al.clone(),
            bl.clone(),
            Rc::new(a_ty.shift_local(3)),
            Rc::new(Type::Pi {
                dom_level: bl.clone(),
                cod_level: bl.clone(),
                dom: Rc::new(b_ty.shift_local(4)),
                cod: Rc::new(b_ty.shift_local(5)),
            }),
            Rc::new(head),
        );
        Term::Lam {
            dom_level: al.clone(),
            cod_level: bl.clone(),
            // The step proves `M(S k̂)`, so its argument is a vector of length
            // `S k̂` — which is exactly what makes `fst`/`snd` below legal,
            // since `Vec(A; S k̂) ⇝ Σ(_ : A). Vec(A; k̂)`.
            dom: Rc::new(vec(al, a_ty, 2, Rc::new(Term::Succ(var(1))))),
            body: Rc::new(crate::spelling::checked_app(
                Rc::new(g_head),
                bl.clone(),
                bl.clone(),
                Rc::new(b_ty.shift_local(3)),
                Rc::new(b_ty.shift_local(4)),
                Rc::new(r_tail),
            )),
        }
    };
    crate::spelling::checked_app(
        Rc::new(Term::ElimNat {
            level: ml,
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::clone(len),
        }),
        al.clone(),
        bl.clone(),
        Rc::new(vec(al, a_ty, 0, Rc::clone(len))),
        Rc::new(b_ty.shift_local(1)),
        xs,
    )
}

/// `tabulate^l(B; k; f) : Vec^l(B; k)` for `f : Π(i : Fin k). B`.
///
/// ```text
/// tabulate(B; 0;   f) ⇝ ⟨⟩
/// tabulate(B; S k; f) ⇝ (f (inl ⟨⟩), tabulate(B; k; λj. f (inr j)))
/// ```
///
/// This is the one that turns an *index function* into data, and the induction
/// hypothesis a `Wf` arm receives is exactly such a function
/// (`docs/container-fields.md` §4.2) — which is why the self-call over a
/// container elaborates to this and to nothing else.
///
/// `B` must not depend on the index, which is the phase-2 restriction on the
/// motive (§4.3): a dependent one would need the result to be a Σ or a
/// pointwise predicate, not a `Vec`.
pub(crate) fn tabulate(bl: &Level, b_ty: &Type, len: &Rc<Term>, f: Rc<Term>) -> Term {
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let fin = |k: Rc<Term>| Rc::new(Type::Fin { len: k });
    // `Π(i : Fin k̂). B` at ambient depth `d`. `B` does not depend on `i`, but
    // it is *scoped under* the `Fin` binder, so it shifts by `d + 1` and not by
    // `d` — the domain, which is not under it, takes `d`. Getting this wrong is
    // invisible at a closed `B` (`tabulate_at_an_open_element_type`).
    let idx_fun = |d: u32, k: Rc<Term>| Type::Pi {
        dom_level: Level::Zero,
        cod_level: bl.clone(),
        dom: fin(k),
        cod: Rc::new(b_ty.shift_local(d + 1)),
    };
    // Motive in (Γ, k̂): Π(f : Π(i : Fin k̂). B). Vec(B; k̂).
    let motive = Type::Pi {
        dom_level: bl.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(idx_fun(1, var(0))),
        cod: Rc::new(vec(bl, b_ty, 2, var(1))),
    };
    // Base in Γ: λ(f : Π(i : Fin 0). B). ⟨⟩.
    let base = Term::Lam {
        dom_level: bl.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(idx_fun(0, Rc::new(Term::Zero))),
        body: Rc::new(Term::Triv { level: bl.clone() }),
    };
    // Step in (Γ, k̂=1, r=0), under its own λ: (Γ, k̂=2, r=1, f=0).
    let step = {
        // f (inl ⟨⟩) : B — the head, at index 0 of `Fin (S k̂)`.
        let zero_idx = Term::Inl {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: fin(var(2)),
            val: Rc::new(Term::Triv { level: Level::Zero }),
        };
        let head = crate::spelling::checked_app(
            var(0),
            Level::Zero,
            bl.clone(),
            fin(Rc::new(Term::Succ(var(2)))),
            Rc::new(b_ty.shift_local(4)),
            Rc::new(zero_idx),
        );
        // λ(j : Fin k̂). f (inr j) — the tail's index function, one binder
        // deeper: (Γ, k̂=3, r=2, f=1, j=0).
        let shifted = Term::Lam {
            dom_level: Level::Zero,
            cod_level: bl.clone(),
            dom: fin(var(2)),
            body: Rc::new(crate::spelling::checked_app(
                var(1),
                Level::Zero,
                bl.clone(),
                fin(Rc::new(Term::Succ(var(3)))),
                Rc::new(b_ty.shift_local(5)),
                Rc::new(Term::Inr {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: unit(),
                    rhs: fin(var(3)),
                    val: var(0),
                }),
            )),
        };
        let r_shifted = crate::spelling::checked_app(
            var(1),
            bl.clone(),
            bl.clone(),
            Rc::new(idx_fun(3, var(2))),
            Rc::new(vec(bl, b_ty, 4, var(3))),
            Rc::new(shifted),
        );
        Term::Lam {
            dom_level: bl.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(idx_fun(2, Rc::new(Term::Succ(var(1))))),
            body: Rc::new(Term::Pair {
                fst_level: bl.clone(),
                snd_level: bl.clone(),
                fst_ty: Rc::new(b_ty.shift_local(3)),
                snd_ty: Rc::new(vec(bl, b_ty, 4, var(3))),
                fst: Rc::new(head),
                snd: Rc::new(r_shifted),
            }),
        }
    };
    crate::spelling::checked_app(
        Rc::new(Term::ElimNat {
            level: bl.clone(),
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::clone(len),
        }),
        bl.clone(),
        bl.clone(),
        Rc::new(idx_fun(0, Rc::clone(len))),
        Rc::new(vec(bl, b_ty, 1, Rc::new(len.shift_local(1)))),
        f,
    )
}

// -- `tab_cong` and its pieces (docs/container-proofs.md §4) ----------------
//
// The phase-3 schema needs four type formers repeated at half a dozen depths,
// and its motive quantifies over *three* arguments, so the pieces are written
// as functions rather than closures. Every one takes the ambient depth `d` and
// terms already scoped at that depth; a piece scoped under its own binder
// shifts what it was given by one, and says so.

/// `Π(i : Fin k). A` at depth `d`. `A` is under the binder, hence `d + 1`.
fn idx_fun(al: &Level, a_ty: &Type, d: u32, k: Rc<Term>) -> Type {
    Type::Pi {
        dom_level: Level::Zero,
        cod_level: al.clone(),
        dom: Rc::new(Type::Fin { len: k }),
        cod: Rc::new(a_ty.shift_local(d + 1)),
    }
}

/// `fv i` for `fv : Π(i : Fin k). A`, everything at depth `d`.
fn idx_app(al: &Level, a_ty: &Type, d: u32, k: Rc<Term>, fv: Rc<Term>, i: Rc<Term>) -> Term {
    crate::spelling::checked_app(
        fv,
        Level::Zero,
        al.clone(),
        Rc::new(Type::Fin { len: k }),
        Rc::new(a_ty.shift_local(d + 1)),
        i,
    )
}

/// `Id^l(A; fv i; gv i)` **under** the `i` binder, for `k`/`fv`/`gv` at `d`.
fn pw_cod(al: &Level, a_ty: &Type, d: u32, k: &Rc<Term>, fv: &Rc<Term>, gv: &Rc<Term>) -> Type {
    let k1 = Rc::new(k.shift_local(1));
    Type::Id {
        level: al.clone(),
        ty: Rc::new(a_ty.shift_local(d + 1)),
        lhs: Rc::new(idx_app(
            al,
            a_ty,
            d + 1,
            Rc::clone(&k1),
            Rc::new(fv.shift_local(1)),
            var(0),
        )),
        rhs: Rc::new(idx_app(
            al,
            a_ty,
            d + 1,
            k1,
            Rc::new(gv.shift_local(1)),
            var(0),
        )),
    }
}

/// `Π(i : Fin k). Id^l(A; fv i; gv i)` at depth `d` — the pointwise hypothesis.
fn pointwise(al: &Level, a_ty: &Type, d: u32, k: &Rc<Term>, fv: &Rc<Term>, gv: &Rc<Term>) -> Type {
    Type::Pi {
        dom_level: Level::Zero,
        cod_level: al.clone(),
        dom: Rc::new(Type::Fin { len: Rc::clone(k) }),
        cod: Rc::new(pw_cod(al, a_ty, d, k, fv, gv)),
    }
}

/// `Id^l(Vec(A; k); tabulate(k; fv); tabulate(k; gv))` at depth `d`.
fn concl(al: &Level, a_ty: &Type, d: u32, k: &Rc<Term>, fv: Rc<Term>, gv: Rc<Term>) -> Type {
    let a = a_ty.shift_local(d);
    Type::Id {
        level: al.clone(),
        ty: Rc::new(Type::Vec {
            level: al.clone(),
            elem: Rc::new(a.clone()),
            len: Rc::clone(k),
        }),
        lhs: Rc::new(tabulate(al, &a, k, fv)),
        rhs: Rc::new(tabulate(al, &a, k, gv)),
    }
}

/// `Π(h : pointwise). concl` at depth `d`.
fn m_from_h(al: &Level, a_ty: &Type, d: u32, k: &Rc<Term>, fv: &Rc<Term>, gv: &Rc<Term>) -> Type {
    let k1 = Rc::new(k.shift_local(1));
    Type::Pi {
        dom_level: al.clone(),
        cod_level: al.clone(),
        dom: Rc::new(pointwise(al, a_ty, d, k, fv, gv)),
        cod: Rc::new(concl(
            al,
            a_ty,
            d + 1,
            &k1,
            Rc::new(fv.shift_local(1)),
            Rc::new(gv.shift_local(1)),
        )),
    }
}

/// `Π(g : Fin k → A). Π(h : …). concl` at depth `d`, for a *given* `fv`.
fn m_from_g(al: &Level, a_ty: &Type, d: u32, k: &Rc<Term>, fv: &Rc<Term>) -> Type {
    let k1 = Rc::new(k.shift_local(1));
    Type::Pi {
        dom_level: al.clone(),
        cod_level: al.clone(),
        dom: Rc::new(idx_fun(al, a_ty, d, Rc::clone(k))),
        cod: Rc::new(m_from_h(
            al,
            a_ty,
            d + 1,
            &k1,
            &Rc::new(fv.shift_local(1)),
            &var(0),
        )),
    }
}

/// The motive body `Π(f). Π(g). Π(h). concl` at depth `d` and length `k`.
fn m_from_f(al: &Level, a_ty: &Type, d: u32, k: &Rc<Term>) -> Type {
    let k1 = Rc::new(k.shift_local(1));
    Type::Pi {
        dom_level: al.clone(),
        cod_level: al.clone(),
        dom: Rc::new(idx_fun(al, a_ty, d, Rc::clone(k))),
        cod: Rc::new(m_from_g(al, a_ty, d + 1, &k1, &var(0))),
    }
}

/// `tab_cong^l(A; k; f; g; h) : Id^l(Vec(A; k); tabulate(k; f); tabulate(k; g))`
/// for `f, g : Π(i : Fin k). A` and `h : Π(i : Fin k). Id^l(A; f i; g i)`.
///
/// **The phase-3 schema** (`docs/container-proofs.md` §4): pointwise equality
/// of two index functions gives equality of the vectors they tabulate to. It is
/// what a self-call over a container proves when the motive is an equation, and
/// the reason phase 3 needs no `All` predicate and no new kernel machinery.
///
/// An `elim_Nat` on the length like every schema here, but with a motive that
/// quantifies over `f`, `g` and `h` — it has to, because the recursion feeds
/// itself the *shifted* index functions `λj. f (inr j)`.
///
/// ```text
/// k = 0:   both sides are ⟨⟩ : Vec(A; 0) ⇝ Unit, so Unit-η closes it: refl.
/// k = S k: tabulate(S k; f) ⇝ (f ι₀, tabulate(k; λj. f (inr j))), and
///          Vec(A; S k) ⇝ Σ(_ : A). Vec(A; k) is *non-dependent*, so the two
///          components move under two `J`s and no transitivity lemma.
/// ```
pub(crate) fn tab_cong(
    al: &Level,
    a_ty: &Type,
    len: &Rc<Term>,
    f: Rc<Term>,
    g: Rc<Term>,
    h: Rc<Term>,
) -> Term {
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let fin = |k: Rc<Term>| Rc::new(Type::Fin { len: k });
    let zero = || Rc::new(Term::Zero);

    // Motive in (Γ, k̂): Π(f). Π(g). Π(h). Id(Vec(A; k̂); tab(k̂; f); tab(k̂; g)).
    let motive = m_from_f(al, a_ty, 1, &var(0));

    // Base in Γ, at k̂ = 0: λf. λg. λh. refl. The two tabulates are `⟨⟩` at
    // `Vec(A; 0) ⇝ Unit^l`, and `Unit`'s proof irrelevance makes them
    // convertible — this is the one place the schema leans on an η rule.
    let base = {
        let a3 = a_ty.shift_local(3);
        let body = Term::Refl {
            level: al.clone(),
            ty: Rc::new(Type::Vec {
                level: al.clone(),
                elem: Rc::new(a3.clone()),
                len: zero(),
            }),
            tm: Rc::new(tabulate(al, &a3, &zero(), var(2))),
        };
        Term::Lam {
            dom_level: al.clone(),
            cod_level: al.clone(),
            dom: Rc::new(idx_fun(al, a_ty, 0, zero())),
            body: Rc::new(Term::Lam {
                dom_level: al.clone(),
                cod_level: al.clone(),
                dom: Rc::new(idx_fun(al, a_ty, 1, zero())),
                body: Rc::new(Term::Lam {
                    dom_level: al.clone(),
                    cod_level: al.clone(),
                    dom: Rc::new(pointwise(al, a_ty, 2, &zero(), &var(1), &var(0))),
                    body: Rc::new(body),
                }),
            }),
        }
    };

    // Step in (Γ, k̂=1, r=0), proving M(S k̂); under its own three λs the
    // context is (Γ, k̂=4, r=3, f=2, g=1, h=0), i.e. depth 5.
    let step = {
        let k = var(4);
        let sk = Rc::new(Term::Succ(var(4)));
        let a5 = a_ty.shift_local(5);
        // ι₀ : Fin (S k̂), and the tail index maps `λj. f (inr j)`.
        let zero_idx = Rc::new(Term::Inl {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: fin(Rc::clone(&k)),
            val: Rc::new(Term::Triv { level: Level::Zero }),
        });
        // One binder deeper: (Γ, k̂=5, r=4, f=3, g=2, h=1, j=0).
        let inr_j = Rc::new(Term::Inr {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: fin(var(5)),
            val: var(0),
        });
        let sk6 = Rc::new(Term::Succ(var(5)));
        let shifted = |fv: Rc<Term>| {
            Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: al.clone(),
                dom: fin(Rc::clone(&k)),
                body: Rc::new(idx_app(al, a_ty, 6, Rc::clone(&sk6), fv, Rc::clone(&inr_j))),
            })
        };
        let (f_tl, g_tl) = (shifted(var(3)), shifted(var(2)));
        // h's tail: λj. h (inr j) : Π(j : Fin k̂). Id(A; f_tl j; g_tl j) — the
        // annotation is `pointwise` at the *unshifted* f and g, which is what
        // the App's codomain is before the argument is substituted.
        let h_tl = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: al.clone(),
            dom: fin(Rc::clone(&k)),
            body: Rc::new(crate::spelling::checked_app(
                var(1),
                Level::Zero,
                al.clone(),
                fin(Rc::clone(&sk6)),
                Rc::new(pw_cod(al, a_ty, 6, &sk6, &var(3), &var(2))),
                inr_j,
            )),
        });
        // The two heads and the two tails.
        let head_f = Rc::new(idx_app(
            al,
            a_ty,
            5,
            Rc::clone(&sk),
            var(2),
            Rc::clone(&zero_idx),
        ));
        let head_g = Rc::new(idx_app(
            al,
            a_ty,
            5,
            Rc::clone(&sk),
            var(1),
            Rc::clone(&zero_idx),
        ));
        let tail_f = Rc::new(tabulate(al, &a5, &k, Rc::clone(&f_tl)));
        let tail_g = Rc::new(tabulate(al, &a5, &k, Rc::clone(&g_tl)));
        // p : Id(A; f ι₀; g ι₀), from the hypothesis at index 0.
        let p = Rc::new(crate::spelling::checked_app(
            var(0),
            Level::Zero,
            al.clone(),
            fin(Rc::clone(&sk)),
            Rc::new(pw_cod(al, a_ty, 5, &sk, &var(2), &var(1))),
            zero_idx,
        ));
        // q : Id(Vec(A; k̂); tail_f; tail_g), from the recursive result.
        let q = {
            let k1 = Rc::new(k.shift_local(1));
            let app1 = crate::spelling::checked_app(
                var(3),
                al.clone(),
                al.clone(),
                Rc::new(idx_fun(al, a_ty, 5, Rc::clone(&k))),
                Rc::new(m_from_g(al, a_ty, 6, &k1, &var(0))),
                Rc::clone(&f_tl),
            );
            let app2 = crate::spelling::checked_app(
                Rc::new(app1),
                al.clone(),
                al.clone(),
                Rc::new(idx_fun(al, a_ty, 5, Rc::clone(&k))),
                Rc::new(m_from_h(
                    al,
                    a_ty,
                    6,
                    &k1,
                    &Rc::new(f_tl.shift_local(1)),
                    &var(0),
                )),
                Rc::clone(&g_tl),
            );
            Rc::new(crate::spelling::checked_app(
                Rc::new(app2),
                al.clone(),
                al.clone(),
                Rc::new(pointwise(al, a_ty, 5, &k, &f_tl, &g_tl)),
                Rc::new(concl(
                    al,
                    a_ty,
                    6,
                    &k1,
                    Rc::new(f_tl.shift_local(1)),
                    Rc::new(g_tl.shift_local(1)),
                )),
                h_tl,
            ))
        };
        // `(x, y) : Vec(A; S k̂)` — the snd type is under the fst binder.
        let pair = |d: u32, x: Rc<Term>, y: Rc<Term>| {
            Rc::new(Term::Pair {
                fst_level: al.clone(),
                snd_level: al.clone(),
                fst_ty: Rc::new(a_ty.shift_local(d)),
                snd_ty: Rc::new(Type::Vec {
                    level: al.clone(),
                    elem: Rc::new(a_ty.shift_local(d + 1)),
                    // k̂ is the outermost of the step's binders, so at depth
                    // `d` it is `var(d - 1)` — and this is under the pair's
                    // first component, one deeper.
                    len: var(d),
                }),
                fst: x,
                snd: y,
            })
        };
        let vec_sk = |d: u32| {
            Rc::new(Type::Vec {
                level: al.clone(),
                elem: Rc::new(a_ty.shift_local(d)),
                len: Rc::new(Term::Succ(var(d - 1))),
            })
        };
        // e₁ moves the tail: J on q, with the head held fixed.
        // Motive context (…, y : Vec(A; k̂), _ : Id(…)), i.e. depth 7.
        let e1 = Rc::new(Term::J {
            ty_level: al.clone(),
            motive_level: al.clone(),
            ty: Rc::new(Type::Vec {
                level: al.clone(),
                elem: Rc::new(a5.clone()),
                len: Rc::clone(&k),
            }),
            lhs: Rc::clone(&tail_f),
            motive: Rc::new(Type::Id {
                level: al.clone(),
                ty: vec_sk(7),
                lhs: pair(
                    7,
                    Rc::new(head_f.shift_local(2)),
                    Rc::new(tail_f.shift_local(2)),
                ),
                rhs: pair(7, Rc::new(head_f.shift_local(2)), var(1)),
            }),
            case: Rc::new(Term::Refl {
                level: al.clone(),
                ty: vec_sk(5),
                tm: pair(5, Rc::clone(&head_f), Rc::clone(&tail_f)),
            }),
            rhs: Rc::clone(&tail_g),
            proof: q,
        });
        // e₂ moves the head: J on p, with the *new* tail held fixed. Its case
        // is e₁, which is why no `trans` appears.
        let e2 = Term::J {
            ty_level: al.clone(),
            motive_level: al.clone(),
            ty: Rc::new(a5.clone()),
            lhs: Rc::clone(&head_f),
            motive: Rc::new(Type::Id {
                level: al.clone(),
                ty: vec_sk(7),
                lhs: pair(
                    7,
                    Rc::new(head_f.shift_local(2)),
                    Rc::new(tail_f.shift_local(2)),
                ),
                rhs: pair(7, var(1), Rc::new(tail_g.shift_local(2))),
            }),
            case: e1,
            rhs: head_g,
            proof: p,
        };
        Term::Lam {
            dom_level: al.clone(),
            cod_level: al.clone(),
            dom: Rc::new(idx_fun(al, a_ty, 2, Rc::new(Term::Succ(var(1))))),
            body: Rc::new(Term::Lam {
                dom_level: al.clone(),
                cod_level: al.clone(),
                dom: Rc::new(idx_fun(al, a_ty, 3, Rc::new(Term::Succ(var(2))))),
                body: Rc::new(Term::Lam {
                    dom_level: al.clone(),
                    cod_level: al.clone(),
                    dom: Rc::new(pointwise(
                        al,
                        a_ty,
                        4,
                        &Rc::new(Term::Succ(var(3))),
                        &var(1),
                        &var(0),
                    )),
                    body: Rc::new(e2),
                }),
            }),
        }
    };

    let elim = Term::ElimNat {
        level: al.clone(),
        motive: Rc::new(motive),
        base: Rc::new(base),
        step: Rc::new(step),
        scrut: Rc::clone(len),
    };
    let len1 = Rc::new(len.shift_local(1));
    let app1 = crate::spelling::checked_app(
        Rc::new(elim),
        al.clone(),
        al.clone(),
        Rc::new(idx_fun(al, a_ty, 0, Rc::clone(len))),
        Rc::new(m_from_g(al, a_ty, 1, &len1, &var(0))),
        Rc::clone(&f),
    );
    let app2 = crate::spelling::checked_app(
        Rc::new(app1),
        al.clone(),
        al.clone(),
        Rc::new(idx_fun(al, a_ty, 0, Rc::clone(len))),
        Rc::new(m_from_h(
            al,
            a_ty,
            1,
            &len1,
            &Rc::new(f.shift_local(1)),
            &var(0),
        )),
        Rc::clone(&g),
    );
    crate::spelling::checked_app(
        Rc::new(app2),
        al.clone(),
        al.clone(),
        Rc::new(pointwise(al, a_ty, 0, len, &f, &g)),
        Rc::new(concl(
            al,
            a_ty,
            1,
            &len1,
            Rc::new(f.shift_local(1)),
            Rc::new(g.shift_local(1)),
        )),
        h,
    )
}

#[cfg(test)]
mod tests {
    //! The schemas checked against the *real kernel*, at both a literal and a
    //! neutral length. Written before any surface syntax reaches them: a de
    //! Bruijn slip in an `elim_Nat` motive is far cheaper to find here than
    //! through three layers of elaboration.

    use super::*;
    use heather_kernel::conv::conv_term;
    use heather_kernel::layer::Layer;
    use heather_kernel::term::{CtxEntry, GlobalCtx};
    use heather_kernel::typing::{DEFAULT_FUEL as FUEL, check_term};
    use heather_syntax::{Expr, Span};

    use crate::slots::{Ingredient, Slot};
    use crate::{Cx, R};

    struct FakeSurfaceVec {
        receiver_type: Type,
        normalized_length: Rc<Term>,
    }

    impl SurfaceVecElab for FakeSurfaceVec {
        fn infer_vector_expr(&self, _cx: &Cx, _expression: &Expr) -> R<(Term, Type, Level)> {
            Ok((Term::Zero, self.receiver_type.clone(), Level::Zero))
        }

        fn check_vector_expr(
            &self,
            _cx: &Cx,
            _expression: &Expr,
            _expected: &Type,
            _level: &Level,
        ) -> R<Term> {
            Ok(Term::Zero)
        }

        fn whnf_vector_type(&self, _cx: &Cx, ty: &Type, _span: Span) -> R<Type> {
            Ok(ty.clone())
        }

        fn whnf_vector_term(&self, _cx: &Cx, _term: &Term, _span: Span) -> R<Rc<Term>> {
            Ok(Rc::clone(&self.normalized_length))
        }

        fn try_vector_template(
            &self,
            _cx: &Cx,
            _slot: Slot,
            _ingredients: &[(&'static str, Ingredient<'_>)],
            _span: Span,
        ) -> R<Option<Term>> {
            Ok(None)
        }
    }

    const SPAN: Span = Span { start: 0, end: 1 };

    #[test]
    fn surface_head_and_tail_need_only_vector_capabilities() {
        let length = Rc::new(Term::Succ(Rc::new(Term::Zero)));
        let fake = FakeSurfaceVec {
            receiver_type: Type::Vec {
                level: Level::Zero,
                elem: Rc::new(Type::Nat),
                len: Rc::clone(&length),
            },
            normalized_length: Rc::clone(&length),
        };
        let expression = Expr {
            kind: heather_syntax::ExprKind::Num(0),
            span: SPAN,
        };

        let (_, head_type, _) =
            elab_head_tail(&fake, &Cx::empty(), &expression, true, SPAN).expect("head");
        assert_eq!(head_type, Type::Nat);

        let (_, tail_type, _) =
            elab_head_tail(&fake, &Cx::empty(), &expression, false, SPAN).expect("tail");
        assert_eq!(
            tail_type,
            Type::Vec {
                level: Level::Zero,
                elem: Rc::new(Type::Nat),
                len: Rc::new(Term::Zero),
            }
        );
    }

    fn nat_lit(k: usize) -> Rc<Term> {
        let mut t = Term::Zero;
        for _ in 0..k {
            t = Term::Succ(Rc::new(t));
        }
        Rc::new(t)
    }

    /// Γ built from a list of types, outermost first.
    fn ctx(tys: &[Type]) -> LocalCtx {
        let mut g = LocalCtx::nil();
        for t in tys {
            g.entries.push(CtxEntry {
                ty: Rc::new(t.clone()),
                level: Level::Zero,
            });
        }
        g
    }

    fn ck(g: &LocalCtx, t: &Term, ty: &Type) {
        check_term(
            &GlobalCtx::default(),
            0,
            Layer::Prog,
            g,
            t,
            ty,
            &Level::Zero,
            FUEL,
        )
        .unwrap_or_else(|e| panic!("does not check: {e:?}"));
    }

    fn conv(g: &LocalCtx, a: &Term, b: &Term, ty: &Type) {
        conv_term(
            &GlobalCtx::default(),
            g,
            Layer::Prog,
            a,
            b,
            ty,
            &Level::Zero,
            FUEL,
        )
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
    }

    fn nat_vec(k: Rc<Term>) -> Type {
        Type::Vec {
            level: Level::Zero,
            elem: Rc::new(Type::Nat),
            len: k,
        }
    }

    /// `λ(n : Nat). Succ n`.
    fn succ_fn() -> Rc<Term> {
        Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Succ(var(0))),
        })
    }

    /// The literal vector `[a, b]` of `Nat`s.
    fn pair_vec(a: Rc<Term>, b: Rc<Term>) -> Rc<Term> {
        let tail = Term::Pair {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: Rc::new(Type::Nat),
            snd_ty: Rc::new(nat_vec(nat_lit(0))),
            fst: b,
            snd: Rc::new(Term::Triv { level: Level::Zero }),
        };
        Rc::new(Term::Pair {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: Rc::new(Type::Nat),
            snd_ty: Rc::new(nat_vec(nat_lit(1))),
            fst: a,
            snd: Rc::new(tail),
        })
    }

    #[test]
    fn map_checks_and_computes() {
        let g = ctx(&[]);
        let xs = pair_vec(nat_lit(1), nat_lit(2));
        let t = map(
            &Level::Zero,
            &Level::Zero,
            &Type::Nat,
            &Type::Nat,
            &nat_lit(2),
            succ_fn(),
            xs,
        );
        ck(&g, &t, &nat_vec(nat_lit(2)));
        conv(
            &g,
            &t,
            &pair_vec(nat_lit(2), nat_lit(3)),
            &nat_vec(nat_lit(2)),
        );
    }

    #[test]
    fn map_at_a_neutral_length_and_vector_still_types() {
        // Γ = (n : Nat, xs : Vec(Nat; n)) — nothing reduces, but it must
        // typecheck, because that is the situation inside every `match` arm
        // over a container field.
        let g = ctx(&[Type::Nat, nat_vec(var(0))]);
        let t = map(
            &Level::Zero,
            &Level::Zero,
            &Type::Nat,
            &Type::Nat,
            &var(1),
            succ_fn(),
            var(0),
        );
        ck(&g, &t, &nat_vec(var(1)));
    }

    #[test]
    fn fold_checks_and_computes() {
        let g = ctx(&[]);
        // λ(a : Nat). λ(b : Nat). Succ b — counts the elements.
        let count = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                body: Rc::new(Term::Succ(var(0))),
            }),
        });
        let xs = pair_vec(nat_lit(7), nat_lit(8));
        let t = fold(
            &Level::Zero,
            &Level::Zero,
            &Type::Nat,
            &Type::Nat,
            &nat_lit(2),
            nat_lit(0),
            count,
            xs,
        );
        ck(&g, &t, &Type::Nat);
        conv(&g, &t, &nat_lit(2), &Type::Nat);
    }

    #[test]
    fn fold_at_a_neutral_length_still_types() {
        let g = ctx(&[Type::Nat, nat_vec(var(0))]);
        let keep = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                body: var(1),
            }),
        });
        let t = fold(
            &Level::Zero,
            &Level::Zero,
            &Type::Nat,
            &Type::Nat,
            &var(1),
            nat_lit(0),
            keep,
            var(0),
        );
        ck(&g, &t, &Type::Nat);
    }

    #[test]
    fn tabulate_checks_and_computes() {
        let g = ctx(&[]);
        // λ(i : Fin 2). 5 — a constant index function.
        let f = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: nat_lit(2) }),
            body: nat_lit(5),
        });
        let t = tabulate(&Level::Zero, &Type::Nat, &nat_lit(2), f);
        ck(&g, &t, &nat_vec(nat_lit(2)));
        conv(
            &g,
            &t,
            &pair_vec(nat_lit(5), nat_lit(5)),
            &nat_vec(nat_lit(2)),
        );
    }

    #[test]
    fn tabulate_at_a_neutral_length_still_types() {
        // The shape a `Wf` arm hands over: Γ = (n : Nat, f : Π(i : Fin n). Nat).
        let idx_fun = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: var(0) }),
            cod: Rc::new(Type::Nat),
        };
        let g = ctx(&[Type::Nat, idx_fun]);
        let t = tabulate(&Level::Zero, &Type::Nat, &var(1), var(0));
        ck(&g, &t, &nat_vec(var(1)));
    }

    /// Every test above uses `Nat` as the element type, which is *closed* — so
    /// none of them can see a wrong shift on the element type inside a binder.
    /// Here `B = Vec(Nat; m)` mentions an ambient variable, which is the case a
    /// container recursion at a non-closed result type would hit.
    #[test]
    fn tabulate_at_an_open_element_type() {
        // Γ = (m : Nat, n : Nat, f : Π(i : Fin n). Vec(Nat; m)). Note `ctx`
        // scopes each entry in the *prefix* before it, so `f`'s type sees
        // m = var 1, n = var 0 — and `b(d)` below is for terms in the full Γ.
        let b = |d: u32| nat_vec(var(2 + d));
        let idx_fun = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: var(0) }),
            cod: Rc::new(nat_vec(var(2))),
        };
        let g = ctx(&[Type::Nat, Type::Nat, idx_fun]);
        let t = tabulate(&Level::Zero, &b(0), &var(1), var(0));
        ck(
            &g,
            &t,
            &Type::Vec {
                level: Level::Zero,
                elem: Rc::new(b(0)),
                len: var(1),
            },
        );
    }

    /// The same open-element-type control for `map` and `fold`, so the shift
    /// audit covers the module rather than the one schema that failed it.
    #[test]
    fn map_and_fold_at_an_open_element_type() {
        // Γ = (m : Nat, n : Nat, xs : Vec(Vec(Nat; m); n)); `xs`'s own type is
        // scoped in (m, n), so there m = var 1 and n = var 0.
        let b = |d: u32| nat_vec(var(2 + d));
        let g = ctx(&[
            Type::Nat,
            Type::Nat,
            Type::Vec {
                level: Level::Zero,
                elem: Rc::new(nat_vec(var(1))),
                len: var(0),
            },
        ]);
        // id : Vec(Nat; m) → Vec(Nat; m).
        let id_fn = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(b(0)),
            body: var(0),
        });
        let t = map(
            &Level::Zero,
            &Level::Zero,
            &b(0),
            &b(0),
            &var(1),
            id_fn,
            var(0),
        );
        ck(
            &g,
            &t,
            &Type::Vec {
                level: Level::Zero,
                elem: Rc::new(b(0)),
                len: var(1),
            },
        );

        // fold at an open *result* type: λ(a : Vec(Nat;m)). λ(b : Vec(Nat;m)). b.
        let keep = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(b(0)),
            body: Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(b(1)),
                body: var(0),
            }),
        });
        // The initial value has to be a `Vec(Nat; m)`; `tabulate` of a constant
        // is the cheapest one to hand, and it exercises a schema inside a schema.
        let zeros = Rc::new(tabulate(
            &Level::Zero,
            &Type::Nat,
            &var(2),
            Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Fin { len: var(2) }),
                body: nat_lit(0),
            }),
        ));
        let t = fold(
            &Level::Zero,
            &Level::Zero,
            &b(0),
            &b(0),
            &var(1),
            zeros,
            keep,
            var(0),
        );
        ck(&g, &t, &b(0));
    }

    /// `tab_cong` at a **literal** length, where everything computes.
    #[test]
    fn tab_cong_checks_and_computes() {
        let g = ctx(&[]);
        // f = λ(i : Fin 2). 5, g = the same — pointwise `refl` relates them.
        let const_fn = |n: usize| {
            Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Fin { len: nat_lit(2) }),
                body: nat_lit(n),
            })
        };
        let h = Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: nat_lit(2) }),
            body: Rc::new(Term::Refl {
                level: Level::Zero,
                ty: Rc::new(Type::Nat),
                tm: nat_lit(5),
            }),
        });
        let t = tab_cong(
            &Level::Zero,
            &Type::Nat,
            &nat_lit(2),
            const_fn(5),
            const_fn(5),
            h,
        );
        let ty = Type::Id {
            level: Level::Zero,
            ty: Rc::new(nat_vec(nat_lit(2))),
            lhs: Rc::new(tabulate(&Level::Zero, &Type::Nat, &nat_lit(2), const_fn(5))),
            rhs: Rc::new(tabulate(&Level::Zero, &Type::Nat, &nat_lit(2), const_fn(5))),
        };
        ck(&g, &t, &ty);
        // …and it *computes*: the proof reduces to `refl`, not merely types.
        let refl = Term::Refl {
            level: Level::Zero,
            ty: Rc::new(nat_vec(nat_lit(2))),
            tm: Rc::new(tabulate(&Level::Zero, &Type::Nat, &nat_lit(2), const_fn(5))),
        };
        conv(&g, &t, &refl, &ty);
    }

    /// The case that matters: a **neutral** length, which is the situation
    /// inside every container arm. Nothing reduces, and the schema still has to
    /// typecheck — this is what a `Rose` proof will instantiate.
    #[test]
    fn tab_cong_at_a_neutral_length_still_types() {
        // Γ = (n, f, g, h) with f, g : Π(i : Fin n). Nat and h pointwise.
        let idx_fun = |d: u32| Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: var(d) }),
            cod: Rc::new(Type::Nat),
        };
        // In (n, f, g): h : Π(i : Fin n). Id(Nat; f i; g i).
        let app = |fv: u32| {
            Rc::new(Term::App {
                fun: var(fv),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Fin { len: var(3) }),
                cod: Rc::new(Type::Nat),
                arg: var(0),
            })
        };
        let pw = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: var(2) }),
            cod: Rc::new(Type::Id {
                level: Level::Zero,
                ty: Rc::new(Type::Nat),
                lhs: app(2),
                rhs: app(1),
            }),
        };
        let g = ctx(&[Type::Nat, idx_fun(0), idx_fun(1), pw]);
        // In the full Γ: n = 3, f = 2, g = 1, h = 0.
        let t = tab_cong(&Level::Zero, &Type::Nat, &var(3), var(2), var(1), var(0));
        ck(
            &g,
            &t,
            &Type::Id {
                level: Level::Zero,
                ty: Rc::new(nat_vec(var(3))),
                lhs: Rc::new(tabulate(&Level::Zero, &Type::Nat, &var(3), var(2))),
                rhs: Rc::new(tabulate(&Level::Zero, &Type::Nat, &var(3), var(1))),
            },
        );
    }

    /// …and with an **open element type**, the control that caught the live
    /// `tabulate` shift bug above.
    #[test]
    fn tab_cong_at_an_open_element_type() {
        // Γ = (m, n, f, g, h) with the element type `Vec(Nat; m)`, so in the
        // full Γ the variable `m` is `var(4)`.
        let b = |d: u32| nat_vec(var(4 + d));
        // `n` is the index of the length *outside* the binder, `m` that of the
        // element type's variable *inside* it — one deeper, which is the shift
        // the schema itself had wrong.
        let idx_fun = |n: u32, m: u32| Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: var(n) }),
            cod: Rc::new(nat_vec(var(m))),
        };
        let app = |fv: u32| {
            Rc::new(Term::App {
                fun: var(fv),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Fin { len: var(3) }),
                cod: Rc::new(nat_vec(var(5))),
                arg: var(0),
            })
        };
        // In (m, n, f, g): m = 3, n = 2; under the `i` binder m = 4.
        let pw = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Fin { len: var(2) }),
            cod: Rc::new(Type::Id {
                level: Level::Zero,
                ty: Rc::new(nat_vec(var(4))),
                lhs: app(2),
                rhs: app(1),
            }),
        };
        let g = ctx(&[Type::Nat, Type::Nat, idx_fun(0, 2), idx_fun(1, 3), pw]);
        // The context and the schema must agree about what `h` proves before
        // the schema can be blamed for anything.
        ck(
            &g,
            &Term::Var(LocalVar(0)),
            &pointwise(&Level::Zero, &b(0), 0, &var(3), &var(2), &var(1)),
        );
        // Full Γ: m = 4, n = 3, f = 2, g = 1, h = 0.
        let t = tab_cong(&Level::Zero, &b(0), &var(3), var(2), var(1), var(0));
        ck(
            &g,
            &t,
            &Type::Id {
                level: Level::Zero,
                ty: Rc::new(Type::Vec {
                    level: Level::Zero,
                    elem: Rc::new(b(0)),
                    len: var(3),
                }),
                lhs: Rc::new(tabulate(&Level::Zero, &b(0), &var(3), var(2))),
                rhs: Rc::new(tabulate(&Level::Zero, &b(0), &var(3), var(1))),
            },
        );
    }

    #[test]
    fn strengthen_distinguishes_a_dependent_motive() {
        let g = ctx(&[Type::Nat]);
        // Over (Γ, z : Nat): `Nat` is constant, `z = z` is not.
        assert!(strengthen(&Type::Nat, &g).is_some());
        let dep = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: var(0),
            rhs: var(0),
        };
        assert!(strengthen(&dep, &g).is_none());
        // …and one that mentions an *outer* variable is still constant in `z`.
        let outer = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: var(1),
            rhs: var(1),
        };
        assert!(strengthen(&outer, &g).is_some());
    }
}
