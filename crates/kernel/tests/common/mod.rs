//! Shared infrastructure for kernel integration tests: a deterministic RNG,
//! generators for well-scoped (not necessarily well-typed) terms, and node
//! counting. The generator tracks scoping only: shapes of local contexts
//! (base + length), kinds and index-context shapes of global bindings, and
//! the universe-variable count. Substitution tails are generated
//! consistently with those shapes.
//!
//! Caveat: the branch/motive binder telescopes here mirror `subst.rs`'s
//! depth table and `src/rec.rs`'s spec tables; a telescope wrong in *all*
//! places would not be caught by the generator-based tests. The independent
//! hand-elaborated cross-check is the identity-recursor test in
//! `tests/typing.rs`, which re-derives every telescope from docs/delam/04.
#![allow(dead_code)]

pub mod wt;

use std::rc::Rc;

use heather_kernel::level::{Level, UnivVar};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar, Motives, SubstTail,
    Term, Type,
};

/// Deliberately NOT assert_eq!: on failure assert_eq! Debug-formats both
/// terms into an in-memory string, and substituted terms are large enough to
/// OOM the machine. Report only the seed; reproduce it in isolation to
/// inspect.
#[allow(unused_macros)] // not every test binary asserts laws
macro_rules! law {
    ($seed:expr, $a:expr, $b:expr) => {
        assert!($a == $b, "law violated at seed {} (term output suppressed)", $seed);
    };
}
#[allow(unused_imports)]
pub(crate) use law;

// -------------------------------------------------------------------------
// Deterministic RNG (xorshift64*)
// -------------------------------------------------------------------------

pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(2685821657736338717).wrapping_add(1442695040888963407))
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(2685821657736338717)
    }

    pub fn below(&mut self, n: u32) -> u32 {
        assert!(n > 0);
        (self.next() % n as u64) as u32
    }
}

// -------------------------------------------------------------------------
// Scoping shapes
// -------------------------------------------------------------------------

/// Base of a local-context shape: `·` or a context binding at an *absolute*
/// position in the global context (absolute positions are stable under
/// binder pushes; converted to de Bruijn at use sites).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseRef {
    Nil,
    Abs(u32),
}

#[derive(Debug, Clone, Copy)]
pub struct Shape {
    pub base: BaseRef,
    pub len: u32,
}

#[derive(Debug, Clone)]
pub enum GK {
    Ctx,
    Ty(Shape),
    Tm(Shape),
}

#[derive(Debug, Clone)]
pub struct Sc {
    pub univ: u32,
    pub globals: Vec<GK>, // [0] is outermost
    pub local: Shape,
}

impl Sc {
    pub fn db(&self, abs: u32) -> GlobalVar {
        GlobalVar(self.globals.len() as u32 - 1 - abs)
    }

    pub fn base(&self, b: BaseRef) -> CtxBase {
        match b {
            BaseRef::Nil => CtxBase::Nil,
            BaseRef::Abs(a) => CtxBase::Var(self.db(a)),
        }
    }

    /// Context bindings visible in this scope (absolute positions).
    pub fn ctx_bindings(&self) -> Vec<u32> {
        self.globals
            .iter()
            .enumerate()
            .filter(|(_, k)| matches!(k, GK::Ctx))
            .map(|(i, _)| i as u32)
            .collect()
    }

    /// Whether a target shape's base is reachable by a substitution tail
    /// from the current local context (Wk needs the source to end in the
    /// same context variable).
    pub fn reaches(&self, target: BaseRef) -> bool {
        match target {
            BaseRef::Nil => true,
            BaseRef::Abs(a) => self.local.base == BaseRef::Abs(a),
        }
    }
}

// -------------------------------------------------------------------------
// Generators
// -------------------------------------------------------------------------

pub fn gen_level(sc: &Sc, r: &mut Rng, depth: u32) -> Level {
    match r.below(if depth == 0 { 2 } else { 4 }) {
        0 if sc.univ > 0 => Level::Var(UnivVar(r.below(sc.univ))),
        0 | 1 => Level::Zero,
        2 => Level::succ(gen_level(sc, r, depth - 1)),
        _ => Level::max(gen_level(sc, r, depth - 1), gen_level(sc, r, depth - 1)),
    }
}

/// A random shape for a "somewhere else" local context (boxed code etc.),
/// over any visible context binding.
pub fn gen_shape(sc: &Sc, r: &mut Rng) -> Shape {
    let ctxs = sc.ctx_bindings();
    let base = if !ctxs.is_empty() && r.below(4) < 3 {
        BaseRef::Abs(ctxs[r.below(ctxs.len() as u32) as usize])
    } else {
        BaseRef::Nil
    };
    Shape { base, len: r.below(3) }
}

/// A materialized local context matching a freshly chosen shape.
pub fn gen_ctx(sc: &Sc, r: &mut Rng, b: u32) -> (LocalCtx, Shape) {
    let shape = gen_shape(sc, r);
    let mut entries = Vec::new();
    for k in 0..shape.len {
        let inner = Sc { local: Shape { base: shape.base, len: k }, ..sc.clone() };
        entries.push(CtxEntry {
            ty: gen_type(&inner, r, b / 2),
            level: gen_level(sc, r, 1),
        });
    }
    (LocalCtx::from_vec(sc.base(shape.base), entries), shape)
}

/// A substitution from the current local context onto `target`.
/// Precondition: `sc.reaches(target.base)`.
pub fn gen_subst(sc: &Sc, r: &mut Rng, b: u32, target: Shape) -> LocalSubst {
    let tail = match target.base {
        BaseRef::Nil => SubstTail::Empty { len: sc.local.len, base: sc.base(sc.local.base) },
        BaseRef::Abs(a) => {
            assert!(sc.local.base == BaseRef::Abs(a), "generator scoping bug");
            SubstTail::Wk { len: sc.local.len, ctx_var: sc.db(a) }
        }
    };
    let terms = (0..target.len).map(|_| gen_term(sc, r, b / 2)).collect();
    LocalSubst { tail, terms }
}

/// Push a branch/motive telescope: `univs` universe binders, the global
/// bindings produced by `mk` (which receives the absolute position of the
/// first pushed binding, conventionally the context variable `g`), and
/// `locals` recursive-call entries on the ambient local context.
pub fn scope_tele(sc: &Sc, univs: u32, locals: u32, mk: impl Fn(u32) -> Vec<GK>) -> Sc {
    let g = sc.globals.len() as u32;
    let mut s = sc.clone();
    s.univ += univs;
    s.globals.extend(mk(g));
    s.local.len += locals;
    s
}

pub fn sh(base_abs: u32, len: u32) -> Shape {
    Shape { base: BaseRef::Abs(base_abs), len }
}

pub fn gen_motives(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Motives> {
    Rc::new(Motives {
        ty_motive: gen_type(&scope_tele(sc, 1, 1, |_| vec![GK::Ctx]), r, b),
        tm_motive: gen_type(
            &scope_tele(sc, 1, 1, |g| vec![GK::Ctx, GK::Ty(sh(g, 0))]),
            r,
            b,
        ),
    })
}

pub fn gen_branches(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Branches> {
    let mut t = |univs: u32, locals: u32, mk: &dyn Fn(u32) -> Vec<GK>| {
        gen_term(&scope_tele(sc, univs, locals, mk), r, b)
    };
    Rc::new(Branches {
        ty_nat: t(0, 0, &|_| vec![GK::Ctx]),
        ty_pi: t(2, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 1))]),
        ty_ty: t(1, 0, &|_| vec![GK::Ctx]),
        ty_el: t(1, 1, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0))]),
        tm_var: t(1, 0, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]),
        tm_nat: t(0, 0, &|_| vec![GK::Ctx]),
        tm_pi: t(2, 2, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 1))]),
        tm_ty: t(1, 0, &|_| vec![GK::Ctx]),
        tm_zero: t(0, 0, &|_| vec![GK::Ctx]),
        tm_succ: t(0, 1, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0))]),
        tm_elim_nat: t(1, 4, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 2)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        tm_lam: t(2, 2, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 1)), GK::Tm(sh(g, 1))]
        }),
        tm_app: t(2, 4, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        ty_id: t(1, 3, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0))]
        }),
        tm_id: t(1, 3, &|g| {
            vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0))]
        }),
        tm_refl: t(1, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]),
        tm_j: t(2, 6, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Tm(sh(g, 0)),
                GK::Ty(sh(g, 2)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        ty_sigma: t(2, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 1))]),
        tm_sigma: t(2, 2, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 1))]),
        tm_pair: t(2, 4, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        tm_fst: t(2, 3, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 1)), GK::Tm(sh(g, 0))]
        }),
        tm_snd: t(2, 3, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 1)), GK::Tm(sh(g, 0))]
        }),
        ty_unit: t(0, 0, &|_| vec![GK::Ctx]),
        ty_empty: t(0, 0, &|_| vec![GK::Ctx]),
        tm_unit: t(0, 0, &|_| vec![GK::Ctx]),
        tm_empty: t(0, 0, &|_| vec![GK::Ctx]),
        tm_triv: t(0, 0, &|_| vec![GK::Ctx]),
        // (ℓ, g, U_M : Typ_c((g, x:Empty), ℓ), u_t : Trm_c(g ⊢ Empty), x_M, x_t)
        tm_elim_empty: t(1, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 1)), GK::Tm(sh(g, 0))]),
        // (ℓ, ℓ', g, U_A, U_B, x_A, x_B) — both summands in g (non-dependent).
        ty_sum: t(2, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 0))]),
        tm_sum: t(2, 2, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0))]),
        // (ℓ, ℓ', g, U_A, U_B, u_a, x_A, x_B, x_a)
        tm_inl: t(2, 3, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]
        }),
        tm_inr: t(2, 3, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]
        }),
        // (ℓ, ℓ', ℓ'', g, U_A, U_B, U_M : Typ_c((g, z:A+B), ℓ''),
        //  u_l : Trm_c((g, x:A) ⊢ …), u_r : Trm_c((g, y:B) ⊢ …),
        //  u_t : Trm_c(g ⊢ A+B), x_A, x_B, x_M, x_l, x_r, x_t)
        tm_case: t(3, 6, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 1)),
                GK::Tm(sh(g, 1)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        // (ℓ, ℓ', g, U_S, U_T : Typ_c((g, x:U_S), ℓ'), x_S, x_T) — as ty_pi.
        ty_w: t(2, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Ty(sh(g, 1))]),
        tm_w: t(2, 2, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 1))]),
        // (ℓ, ℓ', g, U_S, U_T, u_a, u_f, x_S, x_T, x_a, x_f) — as tm_pair.
        tm_sup: t(2, 4, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        // (ℓ, ℓ', ℓ'', g, U_S, U_T : Typ_c((g, x:U_S), ℓ'),
        //  U_M : Typ_c((g, z:W), ℓ''), u_s : Trm_c((g, a, f, ih) ⊢ …),
        //  u_t : Trm_c(g ⊢ W), x_S, x_T, x_M, x_s, x_t)
        tm_elim_w: t(3, 5, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 3)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        // -- finitary branching (docs/wf-former-design.md §6) --
        // (ℓ, g, U_T, u_k : Trm_c(g ⊢ Nat), x_T, x_k) — the length is a
        // term of g, so it binds nothing.
        ty_vec: t(1, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]),
        tm_vec: t(1, 2, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0))]),
        // (g, u_k, x_k) — no universe binder; `Fin` lives at 0.
        ty_fin: t(0, 1, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0))]),
        tm_fin: t(0, 1, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0))]),
        // (ℓ, g, U_S, u_n : Trm_c((g, x:U_S) ⊢ Nat), x_S, x_n) — one univ
        // only: the arity is a term.
        ty_wf: t(1, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 1))]),
        tm_wf: t(1, 2, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 1))]),
        // (ℓ, g, U_S, u_n, u_a, u_cs, x_S, x_n, x_a, x_cs)
        tm_supf: t(1, 4, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Tm(sh(g, 1)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        // (ℓ, ℓ', g, U_S, u_n, U_M : Typ_c((g, z:Wf), ℓ'),
        //  u_s : Trm_c((g, a, cs, ih) ⊢ …), u_t : Trm_c(g ⊢ Wf),
        //  x_S, x_n, x_M, x_s, x_t)
        tm_elim_wf: t(2, 5, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Tm(sh(g, 1)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 3)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        ty_seq: t(1, 3, &|g| {
            vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0))]
        }),
        tm_seq: t(1, 3, &|g| {
            vec![GK::Ctx, GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0)), GK::Tm(sh(g, 0))]
        }),
        ty_sempty: t(1, 0, &|_| vec![GK::Ctx]),
        tm_sempty: t(1, 0, &|_| vec![GK::Ctx]),
        tm_srefl: t(1, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]),
        tm_transp: t(2, 6, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
                GK::Tm(sh(g, 0)),
            ]
        }),
        tm_elim_sempty: t(2, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 1)), GK::Tm(sh(g, 0))]),
        ty_squash: t(1, 1, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0))]),
        tm_squash: t(1, 1, &|g| vec![GK::Ctx, GK::Tm(sh(g, 0))]),
        tm_squash_in: t(1, 2, &|g| vec![GK::Ctx, GK::Ty(sh(g, 0)), GK::Tm(sh(g, 0))]),
        tm_elim_squash: t(2, 4, &|g| {
            vec![
                GK::Ctx,
                GK::Ty(sh(g, 0)),
                GK::Ty(sh(g, 1)),
                GK::Tm(sh(g, 1)),
                GK::Tm(sh(g, 0)),
            ]
        }),
    })
}

pub fn gen_type(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Type> {
    // Referencable global type bindings.
    let ty_refs: Vec<(u32, Shape)> = sc
        .globals
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            GK::Ty(s) if sc.reaches(s.base) => Some((i as u32, *s)),
            _ => None,
        })
        .collect();

    // Global references exercise the tail/composition machinery — try them
    // eagerly so they stay common in generated terms.
    if b > 0 && !ty_refs.is_empty() && r.below(3) == 0 {
        let (abs, shape) = ty_refs[r.below(ty_refs.len() as u32) as usize];
        return Rc::new(Type::GlobalTy { var: sc.db(abs), subst: gen_subst(sc, r, b, shape) });
    }

    for _ in 0..8 {
        let arm = if b == 0 { r.below(3) } else { r.below(21) };
        match arm {
            0 => return Rc::new(Type::Nat),
            1 => return Rc::new(Type::Ty(gen_level(sc, r, 1))),
            12 => return Rc::new(Type::Unit { level: gen_level(sc, r, 1) }),
            13 => return Rc::new(Type::Empty { level: gen_level(sc, r, 1) }),
            14 if b > 0 => {
                // Sum: non-dependent, both summands in the same scope.
                return Rc::new(Type::Sum {
                    lhs_level: gen_level(sc, r, 1),
                    rhs_level: gen_level(sc, r, 1),
                    lhs: gen_type(sc, r, b / 2),
                    rhs: gen_type(sc, r, b / 2),
                });
            }
            2 if !ty_refs.is_empty() => {
                let (abs, shape) = ty_refs[r.below(ty_refs.len() as u32) as usize];
                return Rc::new(Type::GlobalTy {
                    var: sc.db(abs),
                    subst: gen_subst(sc, r, b, shape),
                });
            }
            3 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Type::Pi {
                    dom_level: gen_level(sc, r, 1),
                    cod_level: gen_level(sc, r, 1),
                    dom: gen_type(sc, r, b / 2),
                    cod: gen_type(&inner, r, b / 2),
                });
            }
            4 if b > 0 => {
                return Rc::new(Type::El {
                    level: gen_level(sc, r, 1),
                    tm: gen_term(sc, r, b - 1),
                });
            }
            5 if b > 0 => {
                let n = 1 + r.below(2);
                let mut inner = sc.clone();
                inner.univ += n;
                return Rc::new(Type::UPi {
                    num_vars: n,
                    level: gen_level(&inner, r, 1),
                    body: gen_type(&inner, r, b / 2),
                });
            }
            6 if b > 0 => {
                let mut inner = sc.clone();
                inner.globals.push(GK::Ctx);
                return Rc::new(Type::CtxPi {
                    level: gen_level(sc, r, 1),
                    body: gen_type(&inner, r, b / 2),
                });
            }
            7 if b > 0 => {
                let (ctx, shape) = gen_ctx(sc, r, b / 2);
                let mut inner = sc.clone();
                inner.globals.push(GK::Ty(shape));
                return Rc::new(Type::TyPi {
                    ctx,
                    arg_level: gen_level(sc, r, 1),
                    body_level: gen_level(sc, r, 1),
                    body: gen_type(&inner, r, b / 2),
                });
            }
            8 if b > 0 => {
                let (ctx, _) = gen_ctx(sc, r, b / 2);
                return Rc::new(Type::CodeTy { ctx, level: gen_level(sc, r, 1) });
            }
            9 if b > 0 => {
                let (ctx, shape) = gen_ctx(sc, r, b / 2);
                let inner = Sc { local: shape, ..sc.clone() };
                return Rc::new(Type::CodeTm {
                    ctx,
                    ty: gen_type(&inner, r, b / 2),
                    level: gen_level(sc, r, 1),
                });
            }
            10 if b > 0 => {
                return Rc::new(Type::Id {
                    level: gen_level(sc, r, 1),
                    ty: gen_type(sc, r, b / 2),
                    lhs: gen_term(sc, r, b / 2),
                    rhs: gen_term(sc, r, b / 2),
                });
            }
            19 if b > 0 => {
                return Rc::new(Type::SEq {
                    level: gen_level(sc, r, 1),
                    ty: gen_type(sc, r, b / 2),
                    lhs: gen_term(sc, r, b / 2),
                    rhs: gen_term(sc, r, b / 2),
                });
            }
            20 => return Rc::new(Type::SEmpty { level: gen_level(sc, r, 1) }),
            11 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Type::Sigma {
                    fst_level: gen_level(sc, r, 1),
                    snd_level: gen_level(sc, r, 1),
                    fst: gen_type(sc, r, b / 2),
                    snd: gen_type(&inner, r, b / 2),
                });
            }
            15 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Type::W {
                    shape_level: gen_level(sc, r, 1),
                    pos_level: gen_level(sc, r, 1),
                    shape: gen_type(sc, r, b / 2),
                    pos: gen_type(&inner, r, b / 2),
                });
            }
            // Vec/Fin: the length is a *term* at the same depth as the
            // element (no binder anywhere), which is the shape substitution
            // and shifting have to respect.
            16 if b > 0 => {
                return Rc::new(Type::Vec {
                    level: gen_level(sc, r, 1),
                    elem: gen_type(sc, r, b / 2),
                    len: gen_term(sc, r, b / 2),
                });
            }
            17 if b > 0 => return Rc::new(Type::Fin { len: gen_term(sc, r, b / 2) }),
            18 if b > 0 => {
                // Wf: the arity is a term under the shape binder.
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Type::Wf {
                    level: gen_level(sc, r, 1),
                    shape: gen_type(sc, r, b / 2),
                    arity: gen_term(&inner, r, b / 2),
                });
            }
            _ => continue,
        }
    }
    Rc::new(Type::Nat)
}

pub fn gen_term(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Term> {
    let tm_refs: Vec<(u32, Shape)> = sc
        .globals
        .iter()
        .enumerate()
        .filter_map(|(i, k)| match k {
            GK::Tm(s) if sc.reaches(s.base) => Some((i as u32, *s)),
            _ => None,
        })
        .collect();

    if b > 0 && !tm_refs.is_empty() && r.below(3) == 0 {
        let (abs, shape) = tm_refs[r.below(tm_refs.len() as u32) as usize];
        return Rc::new(Term::GlobalTm { var: sc.db(abs), subst: gen_subst(sc, r, b, shape) });
    }

    for _ in 0..8 {
        let arm = if b == 0 { r.below(5) } else { r.below(42) };
        match arm {
            0 if sc.local.len > 0 => return Rc::new(Term::Var(LocalVar(r.below(sc.local.len)))),
            0 | 1 => return Rc::new(Term::Zero),
            2 => return Rc::new(Term::TmNat),
            23 => return Rc::new(Term::TmUnit { level: gen_level(sc, r, 1) }),
            24 => return Rc::new(Term::TmEmpty { level: gen_level(sc, r, 1) }),
            25 => return Rc::new(Term::Triv { level: gen_level(sc, r, 1) }),
            26 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                return Rc::new(Term::ElimEmpty {
                    level: gen_level(sc, r, 1),
                    scrut_level: Level::Zero,
                    motive: gen_type(&in1, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            3 => return Rc::new(Term::TmTy(gen_level(sc, r, 1))),
            4 if !tm_refs.is_empty() => {
                let (abs, shape) = tm_refs[r.below(tm_refs.len() as u32) as usize];
                return Rc::new(Term::GlobalTm {
                    var: sc.db(abs),
                    subst: gen_subst(sc, r, b, shape),
                });
            }
            5 if b > 0 => return Rc::new(Term::Succ(gen_term(sc, r, b - 1))),
            6 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                let mut in2 = sc.clone();
                in2.local.len += 2;
                return Rc::new(Term::ElimNat {
                    level: gen_level(sc, r, 1),
                    motive: gen_type(&in1, r, b / 2),
                    base: gen_term(sc, r, b / 2),
                    step: gen_term(&in2, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            7 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::Lam {
                    dom_level: gen_level(sc, r, 1),
                    cod_level: gen_level(sc, r, 1),
                    dom: gen_type(sc, r, b / 2),
                    body: gen_term(&inner, r, b / 2),
                });
            }
            8 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::App {
                    fun: gen_term(sc, r, b / 2),
                    dom_level: gen_level(sc, r, 1),
                    cod_level: gen_level(sc, r, 1),
                    dom: gen_type(sc, r, b / 2),
                    cod: gen_type(&inner, r, b / 2),
                    arg: gen_term(sc, r, b / 2),
                });
            }
            9 if b > 0 => {
                let n = 1 + r.below(2);
                let mut inner = sc.clone();
                inner.univ += n;
                return Rc::new(Term::ULam {
                    num_vars: n,
                    level: gen_level(&inner, r, 1),
                    body: gen_term(&inner, r, b / 2),
                });
            }
            10 if b > 0 => {
                let n = 1 + r.below(2);
                return Rc::new(Term::UApp {
                    fun: gen_term(sc, r, b / 2),
                    levels: (0..n).map(|_| gen_level(sc, r, 1)).collect(),
                });
            }
            11 if b > 0 => {
                let mut inner = sc.clone();
                inner.globals.push(GK::Ctx);
                return Rc::new(Term::CtxLam {
                    level: gen_level(sc, r, 1),
                    body: gen_term(&inner, r, b / 2),
                });
            }
            12 if b > 0 => {
                if r.below(2) == 0 {
                    let (ctx, _) = gen_ctx(sc, r, b / 2);
                    return Rc::new(Term::CtxApp { fun: gen_term(sc, r, b / 2), ctx });
                }
                let shape = gen_shape(sc, r);
                let inner = Sc { local: shape, ..sc.clone() };
                return Rc::new(Term::TyApp {
                    fun: gen_term(sc, r, b / 2),
                    arg: gen_type(&inner, r, b / 2),
                });
            }
            13 if b > 0 => {
                // Boxed code in its own local context.
                let shape = gen_shape(sc, r);
                let inner = Sc { local: shape, ..sc.clone() };
                return Rc::new(if r.below(2) == 0 {
                    Term::BoxTm(gen_term(&inner, r, b / 2))
                } else {
                    Term::BoxTy(gen_type(&inner, r, b / 2))
                });
            }
            14 if b > 0 => {
                let (ctx, shape) = gen_ctx(sc, r, b / 2);
                let mut mo = sc.clone();
                mo.local.len += 1;
                if r.below(2) == 0 {
                    let mut inner = sc.clone();
                    inner.globals.push(GK::Ty(shape));
                    return Rc::new(Term::LetBoxTy {
                        motive_level: gen_level(sc, r, 1),
                        code_level: gen_level(sc, r, 1),
                        ctx,
                        motive: gen_type(&mo, r, b / 2),
                        body: gen_term(&inner, r, b / 2),
                        scrut: gen_term(sc, r, b / 2),
                    });
                }
                let code_sc = Sc { local: shape, ..sc.clone() };
                let mut inner = sc.clone();
                inner.globals.push(GK::Tm(shape));
                return Rc::new(Term::LetBoxTm {
                    motive_level: gen_level(sc, r, 1),
                    code_level: gen_level(sc, r, 1),
                    ctx,
                    ty: gen_type(&code_sc, r, b / 2),
                    motive: gen_type(&mo, r, b / 2),
                    body: gen_term(&inner, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            15 if b >= 6 => {
                let (ctx, shape) = gen_ctx(sc, r, 1);
                let bb = b / 6;
                if r.below(2) == 0 {
                    return Rc::new(Term::ElimCodeTy {
                        ty_motive_level: gen_level(sc, r, 1),
                        tm_motive_level: gen_level(sc, r, 1),
                        motives: gen_motives(sc, r, bb),
                        branches: gen_branches(sc, r, bb),
                        code_level: gen_level(sc, r, 1),
                        ctx,
                        scrut: gen_term(sc, r, bb),
                    });
                }
                let code_sc = Sc { local: shape, ..sc.clone() };
                return Rc::new(Term::ElimCodeTm {
                    ty_motive_level: gen_level(sc, r, 1),
                    tm_motive_level: gen_level(sc, r, 1),
                    motives: gen_motives(sc, r, bb),
                    branches: gen_branches(sc, r, bb),
                    code_level: gen_level(sc, r, 1),
                    ctx,
                    ty: gen_type(&code_sc, r, bb),
                    scrut: gen_term(sc, r, bb),
                });
            }
            16 if b > 0 => {
                return Rc::new(Term::TmId {
                    level: gen_level(sc, r, 1),
                    ty: gen_term(sc, r, b / 2),
                    lhs: gen_term(sc, r, b / 2),
                    rhs: gen_term(sc, r, b / 2),
                });
            }
            17 if b > 0 => {
                return Rc::new(Term::Refl {
                    level: gen_level(sc, r, 1),
                    ty: gen_type(sc, r, b / 2),
                    tm: gen_term(sc, r, b / 2),
                });
            }
            18 if b > 0 => {
                let mut in2 = sc.clone();
                in2.local.len += 2;
                return Rc::new(Term::J {
                    ty_level: gen_level(sc, r, 1),
                    motive_level: gen_level(sc, r, 1),
                    ty: gen_type(sc, r, b / 2),
                    lhs: gen_term(sc, r, b / 2),
                    motive: gen_type(&in2, r, b / 2),
                    case: gen_term(sc, r, b / 2),
                    rhs: gen_term(sc, r, b / 2),
                    proof: gen_term(sc, r, b / 2),
                });
            }
            39 if b > 0 => {
                return Rc::new(Term::SRefl {
                    level: gen_level(sc, r, 1),
                    ty: gen_type(sc, r, b / 2),
                    tm: gen_term(sc, r, b / 2),
                });
            }
            40 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                return Rc::new(Term::Transp {
                    ty_level: gen_level(sc, r, 1),
                    motive_level: gen_level(sc, r, 1),
                    ty: gen_type(sc, r, b / 2),
                    motive: gen_type(&in1, r, b / 2),
                    lhs: gen_term(sc, r, b / 2),
                    rhs: gen_term(sc, r, b / 2),
                    proof: gen_term(sc, r, b / 2),
                    tm: gen_term(sc, r, b / 2),
                });
            }
            41 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                return Rc::new(Term::ElimSEmpty {
                    level: gen_level(sc, r, 1),
                    scrut_level: gen_level(sc, r, 1),
                    motive: gen_type(&in1, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            19 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::TmSigma {
                    fst_level: gen_level(sc, r, 1),
                    snd_level: gen_level(sc, r, 1),
                    fst: gen_term(sc, r, b / 2),
                    snd: gen_term(&inner, r, b / 2),
                });
            }
            20 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::Pair {
                    fst_level: gen_level(sc, r, 1),
                    snd_level: gen_level(sc, r, 1),
                    fst_ty: gen_type(sc, r, b / 2),
                    snd_ty: gen_type(&inner, r, b / 2),
                    fst: gen_term(sc, r, b / 2),
                    snd: gen_term(sc, r, b / 2),
                });
            }
            21 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::Fst {
                    fst_level: gen_level(sc, r, 1),
                    snd_level: gen_level(sc, r, 1),
                    fst_ty: gen_type(sc, r, b / 2),
                    snd_ty: gen_type(&inner, r, b / 2),
                    pair: gen_term(sc, r, b / 2),
                });
            }
            22 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::Snd {
                    fst_level: gen_level(sc, r, 1),
                    snd_level: gen_level(sc, r, 1),
                    fst_ty: gen_type(sc, r, b / 2),
                    snd_ty: gen_type(&inner, r, b / 2),
                    pair: gen_term(sc, r, b / 2),
                });
            }
            27 if b > 0 => {
                // TmSum: non-dependent encoding.
                return Rc::new(Term::TmSum {
                    lhs_level: gen_level(sc, r, 1),
                    rhs_level: gen_level(sc, r, 1),
                    lhs: gen_term(sc, r, b / 2),
                    rhs: gen_term(sc, r, b / 2),
                });
            }
            28 | 29 if b > 0 => {
                // inl/inr: non-dependent type annotations, one value.
                let lhs_level = gen_level(sc, r, 1);
                let rhs_level = gen_level(sc, r, 1);
                let lhs = gen_type(sc, r, b / 2);
                let rhs = gen_type(sc, r, b / 2);
                let val = gen_term(sc, r, b / 2);
                return Rc::new(if arm == 28 {
                    Term::Inl { lhs_level, rhs_level, lhs, rhs, val }
                } else {
                    Term::Inr { lhs_level, rhs_level, lhs, rhs, val }
                });
            }
            30 if b > 0 => {
                // case: motive binds z, each branch binds one value.
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::Case {
                    lhs_level: gen_level(sc, r, 1),
                    rhs_level: gen_level(sc, r, 1),
                    motive_level: gen_level(sc, r, 1),
                    lhs: gen_type(sc, r, b / 2),
                    rhs: gen_type(sc, r, b / 2),
                    motive: gen_type(&inner, r, b / 2),
                    case_l: gen_term(&inner, r, b / 2),
                    case_r: gen_term(&inner, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            31 if b > 0 => {
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::TmW {
                    shape_level: gen_level(sc, r, 1),
                    pos_level: gen_level(sc, r, 1),
                    shape: gen_term(sc, r, b / 2),
                    pos: gen_term(&inner, r, b / 2),
                });
            }
            32 if b > 0 => {
                // sup: pos_ty binds one; label/children in the ambient scope.
                let mut inner = sc.clone();
                inner.local.len += 1;
                return Rc::new(Term::Sup {
                    shape_level: gen_level(sc, r, 1),
                    pos_level: gen_level(sc, r, 1),
                    shape_ty: gen_type(sc, r, b / 2),
                    pos_ty: gen_type(&inner, r, b / 2),
                    label: gen_term(sc, r, b / 2),
                    children: gen_term(sc, r, b / 2),
                });
            }
            33 if b > 0 => {
                // elim_W: pos and motive bind one each, step binds three.
                let mut in1 = sc.clone();
                in1.local.len += 1;
                let mut in3 = sc.clone();
                in3.local.len += 3;
                return Rc::new(Term::ElimW {
                    shape_level: gen_level(sc, r, 1),
                    pos_level: gen_level(sc, r, 1),
                    motive_level: gen_level(sc, r, 1),
                    shape: gen_type(sc, r, b / 2),
                    pos: gen_type(&in1, r, b / 2),
                    motive: gen_type(&in1, r, b / 2),
                    step: gen_term(&in3, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            // sup_f / elim_Wf: `arity` binds one (x : S), motive binds one
            // (z : Wf), step binds three (a, cs, ih) — the depths the
            // substitution laws have to respect.
            34 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                return Rc::new(Term::Supf {
                    level: gen_level(sc, r, 1),
                    shape: gen_type(sc, r, b / 2),
                    arity: gen_term(&in1, r, b / 2),
                    label: gen_term(sc, r, b / 2),
                    children: gen_term(sc, r, b / 2),
                });
            }
            35 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                let mut in3 = sc.clone();
                in3.local.len += 3;
                return Rc::new(Term::ElimWf {
                    level: gen_level(sc, r, 1),
                    motive_level: gen_level(sc, r, 1),
                    shape: gen_type(sc, r, b / 2),
                    arity: gen_term(&in1, r, b / 2),
                    motive: gen_type(&in1, r, b / 2),
                    step: gen_term(&in3, r, b / 2),
                    scrut: gen_term(sc, r, b / 2),
                });
            }
            // Vec/Fin/Wf codes: the lengths are terms of the ambient scope
            // (no binder); only the Wf code's arity binds `x : El s`.
            36 if b > 0 => {
                return Rc::new(Term::TmVec {
                    level: gen_level(sc, r, 1),
                    elem: gen_term(sc, r, b / 2),
                    len: gen_term(sc, r, b / 2),
                });
            }
            37 if b > 0 => return Rc::new(Term::TmFin { len: gen_term(sc, r, b / 2) }),
            38 if b > 0 => {
                let mut in1 = sc.clone();
                in1.local.len += 1;
                return Rc::new(Term::TmWf {
                    level: gen_level(sc, r, 1),
                    shape: gen_term(sc, r, b / 2),
                    arity: gen_term(&in1, r, b / 2),
                });
            }
            _ => continue,
        }
    }
    Rc::new(Term::Zero)
}

/// A random scope: universe variables, a few global bindings, a local shape.
pub fn gen_scope(r: &mut Rng) -> Sc {
    let univ = r.below(3);
    let mut sc = Sc { univ, globals: Vec::new(), local: Shape { base: BaseRef::Nil, len: 0 } };
    let n = r.below(5);
    for _ in 0..n {
        let kind = match r.below(3) {
            0 => GK::Ctx,
            1 => GK::Ty(gen_shape(&sc, r)),
            _ => GK::Tm(gen_shape(&sc, r)),
        };
        sc.globals.push(kind);
    }
    sc.local = gen_shape(&sc, r);
    sc.local.len = r.below(4);
    sc
}

/// A dummy materialized context matching a shape (entry types are irrelevant
/// to id-substitution construction).
pub fn materialize(sc: &Sc, shape: Shape) -> LocalCtx {
    LocalCtx {
        base: sc.base(shape.base),
        entries: ((0..shape.len)
            .map(|_| CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero })
            .collect::<Vec<_>>()).into(),
    }
}

/// A global substitution instantiating the top `n` bindings of `sc`,
/// returning it plus the prefix scope its payloads live in.
pub fn gen_sigma(sc: &Sc, r: &mut Rng, b: u32) -> (GlobalSubst, Sc) {
    let total = sc.globals.len() as u32;
    let n = if total == 0 {
        0
    } else if r.below(2) == 0 {
        total
    } else {
        1 + r.below(total)
    };
    let prefix_len = (total - n) as usize;
    let mut prefix = Sc {
        univ: sc.univ,
        globals: sc.globals[..prefix_len].to_vec(),
        local: Shape { base: BaseRef::Nil, len: 0 },
    };
    // Shapes of the context payloads chosen so far, by absolute position of
    // the substituted binding.
    let mut ctx_shapes: Vec<(u32, Shape)> = Vec::new();
    let sigma_shape = |shape: Shape, ctx_shapes: &[(u32, Shape)]| -> Shape {
        match shape.base {
            BaseRef::Nil => shape,
            BaseRef::Abs(a) if (a as usize) < prefix_len => shape,
            BaseRef::Abs(a) => {
                let (_, ps) = ctx_shapes
                    .iter()
                    .find(|(p, _)| *p == a)
                    .expect("generator scoping bug: base not a context binding");
                Shape { base: ps.base, len: ps.len + shape.len }
            }
        }
    };
    let mut entries = Vec::new();
    for j in prefix_len..sc.globals.len() {
        match &sc.globals[j] {
            GK::Ctx => {
                let (ctx, shape) = gen_ctx(&prefix, r, b / 2);
                ctx_shapes.push((j as u32, shape));
                entries.push(GlobalEntry::Ctx(ctx));
            }
            GK::Ty(shape) => {
                let inner = Sc { local: sigma_shape(*shape, &ctx_shapes), ..prefix.clone() };
                entries.push(GlobalEntry::Ty(gen_type(&inner, r, b / 2)));
            }
            GK::Tm(shape) => {
                let inner = Sc { local: sigma_shape(*shape, &ctx_shapes), ..prefix.clone() };
                entries.push(GlobalEntry::Tm(gen_term(&inner, r, b / 2)));
            }
        }
    }
    prefix.local = sigma_shape(sc.local, &ctx_shapes);
    (GlobalSubst { entries }, prefix)
}

// -------------------------------------------------------------------------
// Node counting (guards against runaway growth when reducing untyped terms)
// -------------------------------------------------------------------------

pub fn count_type(t: &Type) -> u64 {
    1 + match t {
        Type::Nat | Type::Ty(_) | Type::Unit { .. } | Type::Empty { .. }
        | Type::SEmpty { .. } => 0,
        Type::Pi { dom, cod, .. } => count_type(dom) + count_type(cod),
        Type::Id { ty, lhs, rhs, .. } => count_type(ty) + count_term(lhs) + count_term(rhs),
        Type::SEq { ty, lhs, rhs, .. } => count_type(ty) + count_term(lhs) + count_term(rhs),
        Type::Sigma { fst, snd, .. } => count_type(fst) + count_type(snd),
        Type::Sum { lhs, rhs, .. } => count_type(lhs) + count_type(rhs),
        Type::W { shape, pos, .. } => count_type(shape) + count_type(pos),
        Type::Vec { elem, len, .. } => count_type(elem) + count_term(len),
        Type::Fin { len } => count_term(len),
        Type::Wf { shape, arity, .. } => count_type(shape) + count_term(arity),
        Type::Squash { ty, .. } => count_type(ty),
        Type::UPi { body, .. } => count_type(body),
        Type::El { tm, .. } => count_term(tm),
        Type::GlobalTy { subst, .. } => count_subst(subst),
        Type::CtxPi { body, .. } => count_type(body),
        Type::TyPi { ctx, body, .. } => count_ctx(ctx) + count_type(body),
        Type::CodeTy { ctx, .. } => count_ctx(ctx),
        Type::CodeTm { ctx, ty, .. } => count_ctx(ctx) + count_type(ty),
    }
}

pub fn count_term(t: &Term) -> u64 {
    1 + match t {
        Term::Var(_)
        | Term::TmNat
        | Term::TmTy(_)
        | Term::Zero
        | Term::NatLit(_)
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::Triv { .. } => 0,
        Term::TmPi { dom, cod, .. } => count_term(dom) + count_term(cod),
        Term::TmId { ty, lhs, rhs, .. } => {
            count_term(ty) + count_term(lhs) + count_term(rhs)
        }
        Term::TmSEq { ty, lhs, rhs, .. } => {
            count_term(ty) + count_term(lhs) + count_term(rhs)
        }
        Term::TmSEmpty { .. } => 0,
        Term::TmSquash { ty, .. } => count_term(ty),
        Term::TmSigma { fst, snd, .. } => count_term(fst) + count_term(snd),
        Term::TmSum { lhs, rhs, .. } => count_term(lhs) + count_term(rhs),
        Term::TmW { shape, pos, .. } => count_term(shape) + count_term(pos),
        Term::TmVec { elem, len, .. } => count_term(elem) + count_term(len),
        Term::TmFin { len } => count_term(len),
        Term::TmWf { shape, arity, .. } => count_term(shape) + count_term(arity),
        Term::Sup { shape_ty, pos_ty, label, children, .. } => {
            count_type(shape_ty) + count_type(pos_ty) + count_term(label)
                + count_term(children)
        }
        Term::ElimW { shape, pos, motive, step, scrut, .. } => {
            count_type(shape) + count_type(pos) + count_type(motive) + count_term(step)
                + count_term(scrut)
        }
        Term::Supf { shape, arity, label, children, .. } => {
            count_type(shape) + count_term(arity) + count_term(label) + count_term(children)
        }
        Term::ElimWf { shape, arity, motive, step, scrut, .. } => {
            count_type(shape) + count_term(arity) + count_type(motive) + count_term(step)
                + count_term(scrut)
        }
        Term::Succ(t) => count_term(t),
        Term::Refl { ty, tm, .. } => count_type(ty) + count_term(tm),
        Term::J { ty, lhs, motive, case, rhs, proof, .. } => {
            count_type(ty) + count_term(lhs) + count_type(motive) + count_term(case)
                + count_term(rhs) + count_term(proof)
        }
        Term::SRefl { ty, tm, .. } => count_type(ty) + count_term(tm),
        Term::Squash { ty, tm, .. } => count_type(ty) + count_term(tm),
        Term::ElimSEmpty { motive, scrut, .. } => count_type(motive) + count_term(scrut),
        Term::ElimSquash { src_ty, motive, case, scrut, .. } => {
            count_type(src_ty) + count_type(motive) + count_term(case) + count_term(scrut)
        }
        Term::Transp { ty, motive, lhs, rhs, proof, tm, .. } => {
            count_type(ty) + count_type(motive) + count_term(lhs) + count_term(rhs)
                + count_term(proof) + count_term(tm)
        }
        Term::Pair { fst_ty, snd_ty, fst, snd, .. } => {
            count_type(fst_ty) + count_type(snd_ty) + count_term(fst) + count_term(snd)
        }
        Term::Fst { fst_ty, snd_ty, pair, .. } | Term::Snd { fst_ty, snd_ty, pair, .. } => {
            count_type(fst_ty) + count_type(snd_ty) + count_term(pair)
        }
        Term::ElimNat { motive, base, step, scrut, .. } => {
            count_type(motive) + count_term(base) + count_term(step) + count_term(scrut)
        }
        Term::ElimEmpty { motive, scrut, .. } => count_type(motive) + count_term(scrut),
        Term::Inl { lhs, rhs, val, .. } | Term::Inr { lhs, rhs, val, .. } => {
            count_type(lhs) + count_type(rhs) + count_term(val)
        }
        Term::Case { lhs, rhs, motive, case_l, case_r, scrut, .. } => {
            count_type(lhs) + count_type(rhs) + count_type(motive) + count_term(case_l)
                + count_term(case_r) + count_term(scrut)
        }
        Term::Lam { dom, body, .. } => count_type(dom) + count_term(body),
        Term::App { fun, dom, cod, arg, .. } => {
            count_term(fun) + count_type(dom) + count_type(cod) + count_term(arg)
        }
        Term::ULam { body, .. } => count_term(body),
        Term::UApp { fun, .. } => count_term(fun),
        Term::GlobalTm { subst, .. } => count_subst(subst),
        Term::CtxLam { body, .. } => count_term(body),
        Term::CtxApp { fun, ctx } => count_term(fun) + count_ctx(ctx),
        Term::TyLam { ctx, body, .. } => count_ctx(ctx) + count_term(body),
        Term::TyApp { fun, arg } => count_term(fun) + count_type(arg),
        Term::BoxTy(t) => count_type(t),
        Term::BoxTm(t) => count_term(t),
        Term::LetBoxTy { ctx, motive, body, scrut, .. } => {
            count_ctx(ctx) + count_type(motive) + count_term(body) + count_term(scrut)
        }
        Term::LetBoxTm { ctx, ty, motive, body, scrut, .. } => {
            count_ctx(ctx) + count_type(ty) + count_type(motive) + count_term(body)
                + count_term(scrut)
        }
        Term::ElimCodeTy { motives, branches, ctx, scrut, .. } => {
            count_motives(motives) + count_branches(branches) + count_ctx(ctx)
                + count_term(scrut)
        }
        Term::ElimCodeTm { motives, branches, ctx, ty, scrut, .. } => {
            count_motives(motives) + count_branches(branches) + count_ctx(ctx)
                + count_type(ty) + count_term(scrut)
        }
    }
}

pub fn count_ctx(c: &LocalCtx) -> u64 {
    1 + c.entries.iter().map(|e| count_type(&e.ty)).sum::<u64>()
}

pub fn count_subst(s: &LocalSubst) -> u64 {
    1 + s.terms.iter().map(|t| count_term(t)).sum::<u64>()
}

pub fn count_motives(m: &Motives) -> u64 {
    count_type(&m.ty_motive) + count_type(&m.tm_motive)
}

pub fn count_branches(b: &Branches) -> u64 {
    count_term(&b.ty_nat)
        + count_term(&b.ty_pi)
        + count_term(&b.ty_ty)
        + count_term(&b.ty_el)
        + count_term(&b.tm_var)
        + count_term(&b.tm_nat)
        + count_term(&b.tm_pi)
        + count_term(&b.tm_ty)
        + count_term(&b.tm_zero)
        + count_term(&b.tm_succ)
        + count_term(&b.tm_elim_nat)
        + count_term(&b.tm_lam)
        + count_term(&b.tm_app)
        + count_term(&b.ty_id)
        + count_term(&b.ty_sigma)
        + count_term(&b.tm_id)
        + count_term(&b.tm_refl)
        + count_term(&b.tm_j)
        + count_term(&b.tm_sigma)
        + count_term(&b.tm_pair)
        + count_term(&b.tm_fst)
        + count_term(&b.tm_snd)
        + count_term(&b.ty_unit)
        + count_term(&b.ty_empty)
        + count_term(&b.tm_unit)
        + count_term(&b.tm_empty)
        + count_term(&b.tm_triv)
        + count_term(&b.tm_elim_empty)
        + count_term(&b.ty_sum)
        + count_term(&b.tm_sum)
        + count_term(&b.tm_inl)
        + count_term(&b.tm_inr)
        + count_term(&b.tm_case)
        + count_term(&b.ty_w)
        + count_term(&b.tm_w)
        + count_term(&b.tm_sup)
        + count_term(&b.tm_elim_w)
}
