//! Vector eliminators: `map`, `fold` and `tabulate`
//! (`docs/container-fields.md` §4.2).
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

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};

fn var(i: u32) -> Rc<Term> {
    Rc::new(Term::Var(LocalVar(i)))
}

/// `Vec^l(A; k)` with `A` shifted by `d`.
fn vec(level: &Level, elem: &Type, d: u32, len: Rc<Term>) -> Type {
    Type::Vec { level: level.clone(), elem: Rc::new(elem.shift_local(d)), len }
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
        let g_head = Term::App {
            fun: Rc::new(g.shift_local(3)),
            dom_level: al.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(a_ty.shift_local(3)),
            cod: Rc::new(b_ty.shift_local(4)),
            arg: Rc::new(head),
        };
        let r_tail = Term::App {
            fun: var(1),
            dom_level: al.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(vec(al, a_ty, 3, var(2))),
            cod: Rc::new(vec(bl, b_ty, 4, var(3))),
            arg: Rc::new(tail),
        };
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
    Term::App {
        fun: Rc::new(Term::ElimNat {
            level: ml,
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::clone(len),
        }),
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(vec(al, a_ty, 0, Rc::clone(len))),
        cod: Rc::new(vec(bl, b_ty, 1, Rc::new(len.shift_local(1)))),
        arg: xs,
    }
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
        let r_tail = Term::App {
            fun: var(1),
            dom_level: al.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(vec(al, a_ty, 3, var(2))),
            cod: Rc::new(b_ty.shift_local(4)),
            arg: Rc::new(tail),
        };
        // g head (r tail).
        let g_head = Term::App {
            fun: Rc::new(g.shift_local(3)),
            dom_level: al.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(a_ty.shift_local(3)),
            cod: Rc::new(Type::Pi {
                dom_level: bl.clone(),
                cod_level: bl.clone(),
                dom: Rc::new(b_ty.shift_local(4)),
                cod: Rc::new(b_ty.shift_local(5)),
            }),
            arg: Rc::new(head),
        };
        Term::Lam {
            dom_level: al.clone(),
            cod_level: bl.clone(),
            // The step proves `M(S k̂)`, so its argument is a vector of length
            // `S k̂` — which is exactly what makes `fst`/`snd` below legal,
            // since `Vec(A; S k̂) ⇝ Σ(_ : A). Vec(A; k̂)`.
            dom: Rc::new(vec(al, a_ty, 2, Rc::new(Term::Succ(var(1))))),
            body: Rc::new(Term::App {
                fun: Rc::new(g_head),
                dom_level: bl.clone(),
                cod_level: bl.clone(),
                dom: Rc::new(b_ty.shift_local(3)),
                cod: Rc::new(b_ty.shift_local(4)),
                arg: Rc::new(r_tail),
            }),
        }
    };
    Term::App {
        fun: Rc::new(Term::ElimNat {
            level: ml,
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::clone(len),
        }),
        dom_level: al.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(vec(al, a_ty, 0, Rc::clone(len))),
        cod: Rc::new(b_ty.shift_local(1)),
        arg: xs,
    }
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
pub(crate) fn tabulate(
    bl: &Level,
    b_ty: &Type,
    len: &Rc<Term>,
    f: Rc<Term>,
) -> Term {
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let fin = |k: Rc<Term>| Rc::new(Type::Fin { len: k });
    // `Π(i : Fin k̂). B`, with `B` shifted by `d` (it does not depend on `i`).
    let idx_fun = |d: u32, k: Rc<Term>| Type::Pi {
        dom_level: Level::Zero,
        cod_level: bl.clone(),
        dom: fin(k),
        cod: Rc::new(b_ty.shift_local(d)),
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
        let head = Term::App {
            fun: var(0),
            dom_level: Level::Zero,
            cod_level: bl.clone(),
            dom: fin(Rc::new(Term::Succ(var(2)))),
            cod: Rc::new(b_ty.shift_local(4)),
            arg: Rc::new(zero_idx),
        };
        // λ(j : Fin k̂). f (inr j) — the tail's index function, one binder
        // deeper: (Γ, k̂=3, r=2, f=1, j=0).
        let shifted = Term::Lam {
            dom_level: Level::Zero,
            cod_level: bl.clone(),
            dom: fin(var(2)),
            body: Rc::new(Term::App {
                fun: var(1),
                dom_level: Level::Zero,
                cod_level: bl.clone(),
                dom: fin(Rc::new(Term::Succ(var(3)))),
                cod: Rc::new(b_ty.shift_local(5)),
                arg: Rc::new(Term::Inr {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: unit(),
                    rhs: fin(var(3)),
                    val: var(0),
                }),
            }),
        };
        let r_shifted = Term::App {
            fun: var(1),
            dom_level: bl.clone(),
            cod_level: bl.clone(),
            dom: Rc::new(idx_fun(3, var(2))),
            cod: Rc::new(vec(bl, b_ty, 4, var(3))),
            arg: Rc::new(shifted),
        };
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
    Term::App {
        fun: Rc::new(Term::ElimNat {
            level: bl.clone(),
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::clone(len),
        }),
        dom_level: bl.clone(),
        cod_level: bl.clone(),
        dom: Rc::new(idx_fun(0, Rc::clone(len))),
        cod: Rc::new(vec(bl, b_ty, 1, Rc::new(len.shift_local(1)))),
        arg: f,
    }
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
    use heather_kernel::term::{CtxBase, CtxEntry, GlobalCtx};
    use heather_kernel::typing::{check_term, DEFAULT_FUEL as FUEL};

    fn nat_lit(k: usize) -> Rc<Term> {
        let mut t = Term::Zero;
        for _ in 0..k {
            t = Term::Succ(Rc::new(t));
        }
        Rc::new(t)
    }

    /// Γ built from a list of types, outermost first.
    fn ctx(tys: &[Type]) -> LocalCtx {
        let mut g = LocalCtx { base: CtxBase::Nil, entries: Vec::new() };
        for t in tys {
            g.entries.push(CtxEntry { ty: Rc::new(t.clone()), level: Level::Zero });
        }
        g
    }

    fn ck(g: &LocalCtx, t: &Term, ty: &Type) {
        check_term(&GlobalCtx::default(), 0, Layer::Prog, g, t, ty, &Level::Zero, FUEL)
            .unwrap_or_else(|e| panic!("does not check: {e:?}"));
    }

    fn conv(g: &LocalCtx, a: &Term, b: &Term, ty: &Type) {
        conv_term(&GlobalCtx::default(), g, Layer::Prog, a, b, ty, &Level::Zero, FUEL)
            .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
    }

    fn nat_vec(k: Rc<Term>) -> Type {
        Type::Vec { level: Level::Zero, elem: Rc::new(Type::Nat), len: k }
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
        let t = map(&Level::Zero, &Level::Zero, &Type::Nat, &Type::Nat,
                    &nat_lit(2), succ_fn(), xs);
        ck(&g, &t, &nat_vec(nat_lit(2)));
        conv(&g, &t, &pair_vec(nat_lit(2), nat_lit(3)), &nat_vec(nat_lit(2)));
    }

    #[test]
    fn map_at_a_neutral_length_and_vector_still_types() {
        // Γ = (n : Nat, xs : Vec(Nat; n)) — nothing reduces, but it must
        // typecheck, because that is the situation inside every `match` arm
        // over a container field.
        let g = ctx(&[Type::Nat, nat_vec(var(0))]);
        let t = map(&Level::Zero, &Level::Zero, &Type::Nat, &Type::Nat,
                    &var(1), succ_fn(), var(0));
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
        let t = fold(&Level::Zero, &Level::Zero, &Type::Nat, &Type::Nat,
                     &nat_lit(2), nat_lit(0), count, xs);
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
        let t = fold(&Level::Zero, &Level::Zero, &Type::Nat, &Type::Nat,
                     &var(1), nat_lit(0), keep, var(0));
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
        conv(&g, &t, &pair_vec(nat_lit(5), nat_lit(5)), &nat_vec(nat_lit(2)));
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
