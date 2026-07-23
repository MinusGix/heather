//! Property tests for the ch. 05 substitution algebra, on randomly generated
//! well-scoped (not necessarily well-typed) terms. The laws:
//!
//! - identity:       t[id_Γ] = t,  t[id_φ] = t
//! - composition:    t[δ'][δ] = t[δ'∘δ]  (and associativity of ∘)
//! - universe:       t[φ'][φ] = t[φ'∘φ]
//! - φ/δ commute:    t[δ][φ] = t[φ][δ[φ]]
//! - σ/δ commute:    t[δ][σ] = t[σ][δ[σ]]
//!
//! The generator tracks scoping only: shapes of local contexts (base +
//! length), kinds and index-context shapes of global bindings, and the
//! universe-variable count. Substitution tails are generated consistently
//! with those shapes, which the composition/expansion laws depend on.
//!
//! Caveat: the branch/motive binder telescopes here mirror the tables in
//! `subst.rs`; a telescope wrong in *both* places would not be caught. Those
//! tables are checked against docs/delam/04 by review.

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
macro_rules! law {
    ($seed:expr, $a:expr, $b:expr) => {
        assert!($a == $b, "law violated at seed {} (term output suppressed)", $seed);
    };
}

// -------------------------------------------------------------------------
// Deterministic RNG (xorshift64*)
// -------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(2685821657736338717).wrapping_add(1442695040888963407))
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(2685821657736338717)
    }

    fn below(&mut self, n: u32) -> u32 {
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
enum BaseRef {
    Nil,
    Abs(u32),
}

#[derive(Debug, Clone, Copy)]
struct Shape {
    base: BaseRef,
    len: u32,
}

#[derive(Debug, Clone)]
enum GK {
    Ctx,
    Ty(Shape),
    Tm(Shape),
}

#[derive(Debug, Clone)]
struct Sc {
    univ: u32,
    globals: Vec<GK>, // [0] is outermost
    local: Shape,
}

impl Sc {
    fn db(&self, abs: u32) -> GlobalVar {
        GlobalVar(self.globals.len() as u32 - 1 - abs)
    }

    fn base(&self, b: BaseRef) -> CtxBase {
        match b {
            BaseRef::Nil => CtxBase::Nil,
            BaseRef::Abs(a) => CtxBase::Var(self.db(a)),
        }
    }

    /// Context bindings visible in this scope (absolute positions).
    fn ctx_bindings(&self) -> Vec<u32> {
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
    fn reaches(&self, target: BaseRef) -> bool {
        match target {
            BaseRef::Nil => true,
            BaseRef::Abs(a) => self.local.base == BaseRef::Abs(a),
        }
    }
}

// -------------------------------------------------------------------------
// Generators
// -------------------------------------------------------------------------

fn gen_level(sc: &Sc, r: &mut Rng, depth: u32) -> Level {
    match r.below(if depth == 0 { 2 } else { 4 }) {
        0 if sc.univ > 0 => Level::Var(UnivVar(r.below(sc.univ))),
        0 | 1 => Level::Zero,
        2 => Level::succ(gen_level(sc, r, depth - 1)),
        _ => Level::max(gen_level(sc, r, depth - 1), gen_level(sc, r, depth - 1)),
    }
}

/// A random shape for a "somewhere else" local context (boxed code etc.),
/// over any visible context binding.
fn gen_shape(sc: &Sc, r: &mut Rng) -> Shape {
    let ctxs = sc.ctx_bindings();
    let base = if !ctxs.is_empty() && r.below(4) < 3 {
        BaseRef::Abs(ctxs[r.below(ctxs.len() as u32) as usize])
    } else {
        BaseRef::Nil
    };
    Shape { base, len: r.below(3) }
}

/// A materialized local context matching a freshly chosen shape.
fn gen_ctx(sc: &Sc, r: &mut Rng, b: u32) -> (LocalCtx, Shape) {
    let shape = gen_shape(sc, r);
    let mut entries = Vec::new();
    for k in 0..shape.len {
        let inner = Sc { local: Shape { base: shape.base, len: k }, ..sc.clone() };
        entries.push(CtxEntry {
            ty: gen_type(&inner, r, b / 2),
            level: gen_level(sc, r, 1),
        });
    }
    (LocalCtx { base: sc.base(shape.base), entries }, shape)
}

/// A substitution from the current local context onto `target`.
/// Precondition: `sc.reaches(target.base)`.
fn gen_subst(sc: &Sc, r: &mut Rng, b: u32, target: Shape) -> LocalSubst {
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
fn scope_tele(sc: &Sc, univs: u32, locals: u32, mk: impl Fn(u32) -> Vec<GK>) -> Sc {
    let g = sc.globals.len() as u32;
    let mut s = sc.clone();
    s.univ += univs;
    s.globals.extend(mk(g));
    s.local.len += locals;
    s
}

fn sh(base_abs: u32, len: u32) -> Shape {
    Shape { base: BaseRef::Abs(base_abs), len }
}

fn gen_motives(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Motives> {
    Rc::new(Motives {
        ty_motive: gen_type(&scope_tele(sc, 1, 1, |_| vec![GK::Ctx]), r, b),
        tm_motive: gen_type(
            &scope_tele(sc, 1, 1, |g| vec![GK::Ctx, GK::Ty(sh(g, 0))]),
            r,
            b,
        ),
    })
}

fn gen_branches(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Branches> {
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
    })
}

fn gen_type(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Type> {
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
        let arm = if b == 0 { r.below(3) } else { r.below(10) };
        match arm {
            0 => return Rc::new(Type::Nat),
            1 => return Rc::new(Type::Ty(gen_level(sc, r, 1))),
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
            _ => continue,
        }
    }
    Rc::new(Type::Nat)
}

fn gen_term(sc: &Sc, r: &mut Rng, b: u32) -> Rc<Term> {
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
        let arm = if b == 0 { r.below(5) } else { r.below(16) };
        match arm {
            0 if sc.local.len > 0 => return Rc::new(Term::Var(LocalVar(r.below(sc.local.len)))),
            0 | 1 => return Rc::new(Term::Zero),
            2 => return Rc::new(Term::TmNat),
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
            _ => continue,
        }
    }
    Rc::new(Term::Zero)
}

/// A random scope: universe variables, a few global bindings, a local shape.
fn gen_scope(r: &mut Rng) -> Sc {
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
fn materialize(sc: &Sc, shape: Shape) -> LocalCtx {
    LocalCtx {
        base: sc.base(shape.base),
        entries: (0..shape.len)
            .map(|_| CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero })
            .collect(),
    }
}

/// A global substitution instantiating the top `n` bindings of `sc`,
/// returning it plus the prefix scope its payloads live in.
fn gen_sigma(sc: &Sc, r: &mut Rng, b: u32) -> (GlobalSubst, Sc) {
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
// Laws
// -------------------------------------------------------------------------


const CASES: u64 = 300;
const BUDGET: u32 = 12;

#[test]
fn local_identity() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);
        let id = LocalSubst::id(&materialize(&sc, sc.local));
        assert_eq!(t.apply_local(&id), *t);
    }
}

#[test]
fn local_composition() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x9e3779b97f4a7c15);
        let mut sc = gen_scope(&mut r);
        // Three shapes over a common base so all tails are constructible.
        let base = sc.local.base;
        let sh2 = Shape { base, len: r.below(4) };
        let sh1 = Shape { base, len: r.below(4) };
        let sh0 = Shape { base, len: r.below(4) };

        sc.local = sh2;
        let t = gen_term(&sc, &mut r, BUDGET);

        sc.local = sh1;
        let d2 = gen_subst(&sc, &mut r, BUDGET, sh2); // sh1 ⊢ sh2
        sc.local = sh0;
        let d1 = gen_subst(&sc, &mut r, BUDGET, sh1); // sh0 ⊢ sh1

        law!(seed, 
            t.apply_local(&d2).apply_local(&d1),
            t.apply_local(&d2.compose(&d1)));
    }
}

#[test]
fn local_composition_associative() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x517cc1b727220a95);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let shapes: Vec<Shape> = (0..4).map(|_| Shape { base, len: r.below(4) }).collect();

        sc.local = shapes[1];
        let d3 = gen_subst(&sc, &mut r, BUDGET / 2, shapes[0]); // sh1 ⊢ sh0
        sc.local = shapes[2];
        let d2 = gen_subst(&sc, &mut r, BUDGET / 2, shapes[1]); // sh2 ⊢ sh1
        sc.local = shapes[3];
        let d1 = gen_subst(&sc, &mut r, BUDGET / 2, shapes[2]); // sh3 ⊢ sh2

        law!(seed, 
            d3.compose(&d2).compose(&d1),
            d3.compose(&d2.compose(&d1)));
    }
}

#[test]
fn universe_identity_and_composition() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);

        let id: Vec<Level> = (0..sc.univ).map(|i| Level::Var(UnivVar(i))).collect();
        law!(seed, t.apply_univ(&id), *t);

        // φ₂ : sc.univ levels over u1 variables; φ₁ : u1 levels over u0.
        let u1 = r.below(3);
        let u0 = r.below(3);
        let sc1 = Sc { univ: u1, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let sc0 = Sc { univ: u0, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let phi2: Vec<Level> = (0..sc.univ).map(|_| gen_level(&sc1, &mut r, 2)).collect();
        let phi1: Vec<Level> = (0..u1).map(|_| gen_level(&sc0, &mut r, 2)).collect();
        let composed: Vec<Level> = phi2.iter().map(|l| l.subst(&phi1)).collect();

        law!(seed, 
            t.apply_univ(&phi2).apply_univ(&phi1),
            t.apply_univ(&composed));
    }
}

#[test]
fn universe_local_commute() {
    // t[δ][φ] = t[φ][δ[φ]]
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xd6e8feb86659fd93);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let target = Shape { base, len: r.below(4) };

        let source = sc.local;
        sc.local = target;
        let t = gen_term(&sc, &mut r, BUDGET);
        sc.local = source;
        let delta = gen_subst(&sc, &mut r, BUDGET, target);

        let u0 = r.below(3);
        let sc0 = Sc { univ: u0, globals: vec![], local: Shape { base: BaseRef::Nil, len: 0 } };
        let phi: Vec<Level> = (0..sc.univ).map(|_| gen_level(&sc0, &mut r, 2)).collect();

        law!(seed, 
            t.apply_local(&delta).apply_univ(&phi),
            t.apply_univ(&phi).apply_local(&delta.apply_univ(&phi)));
    }
}

#[test]
fn global_local_commute() {
    // t[δ][σ] = t[σ][δ[σ]]
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xa0761d6478bd642f);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let target = Shape { base, len: r.below(4) };

        let source = sc.local;
        sc.local = target;
        let t = gen_term(&sc, &mut r, BUDGET);
        sc.local = source;
        let delta = gen_subst(&sc, &mut r, BUDGET, target);

        let (sigma, _) = gen_sigma(&sc, &mut r, BUDGET);

        law!(seed, 
            t.apply_local(&delta).apply_global(&sigma),
            t.apply_global(&sigma).apply_local(&delta.apply_global(&sigma)));
    }
}

#[test]
fn global_empty_is_identity() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xe7037ed1a0b428db);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);
        let sigma = GlobalSubst::default();
        law!(seed, t.apply_global(&sigma), *t);
    }
}

#[test]
fn shift_composition() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x8ebc6af09c88c6e3);
        let sc = gen_scope(&mut r);
        let t = gen_term(&sc, &mut r, BUDGET);
        law!(seed, t.shift_local(0), *t);
        law!(seed, t.shift_global(0), *t);
        law!(seed, t.shift_univ(0), *t);
        law!(seed, t.shift_local(2).shift_local(3), t.shift_local(5));
        law!(seed, t.shift_global(2).shift_global(3), t.shift_global(5));
        law!(seed, t.shift_univ(2).shift_univ(3), t.shift_univ(5));
    }
}


#[test]
fn global_local_commute_weakening_focus() {
    // Directly constructs the adversarial configuration for σ's tail
    // expansion: Ψ = (g : Ctx, u : Trm(g, k_u entries ⊢ …)), local contexts
    // based on g, t containing u^{wk-tailed δ'}, and σ replacing g by an
    // m'-entry context and u by a payload that reads the spliced region.
    for seed in 0..300u64 {
        let mut r = Rng::new(seed ^ 0x1f83d9abfb41bd6b);
        let k_u = r.below(3); // entries of u's index context Δ_u = (g, k_u)
        let m_p = 1 + r.below(3); // entries of the context replacing g
        let sc = Sc {
            univ: r.below(2),
            globals: vec![GK::Ctx, GK::Tm(sh(0, k_u))],
            local: Shape { base: BaseRef::Abs(0), len: r.below(3) },
        };

        // t contains a reference u^δ' under a binder.
        let t = {
            let mut inner = sc.clone();
            inner.local.len += 1;
            Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: gen_type(&sc, &mut r, 4),
                body: Rc::new(Term::GlobalTm {
                    var: inner.db(1),
                    subst: gen_subst(&inner, &mut r, 4, sh(0, k_u)),
                }),
            })
        };

        // δ : source ⊢ sc.local, both over base g.
        let src = Sc {
            local: Shape { base: BaseRef::Abs(0), len: r.below(4) },
            ..sc.clone()
        };
        let delta = gen_subst(&src, &mut r, 4, sc.local);

        // σ: g ↦ Γ' (m' entries, empty base), u ↦ payload reading a random
        // variable of its context (with g spliced, deep indices reachable).
        let gamma_p = LocalCtx {
            base: CtxBase::Nil,
            entries: (0..m_p)
                .map(|_| CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero })
                .collect(),
        };
        let payload = Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(
            r.below(m_p + k_u),
        )))));
        let sigma = GlobalSubst {
            entries: vec![GlobalEntry::Ctx(gamma_p), GlobalEntry::Tm(payload)],
        };

        law!(seed, 
            t.apply_local(&delta).apply_global(&sigma),
            t.apply_global(&sigma)
                .apply_local(&delta.apply_global(&sigma)));
    }
}
