//! Indexed-families route 2b — the setoid acceptance prototype
//! (`issues/indexed-families.md` route 2b, `docs/sprop-design.md` §8 step 6).
//!
//! A hand-elaborated forded `Vec` whose index constraint is an **`sEq` field
//! in the constructor payload**:
//!
//! ```text
//! Vec_f(A; m) := Σ(s : List A). sEq(Nat; len s; m)
//! ```
//!
//! The skeleton `List A` is the tier-1 exact-height encoding of
//! `tier1_fording.rs` (`Σ(h : Nat). El (spine h)`) — the same encoding the
//! inductive compiler already emits for the unindexed declaration, here
//! threaded over an element *code* so the open-element axis is writable.
//! `len` is computed by the skeleton's own eliminator, not read off the
//! height field, because a general index is eliminator-computed; that `len`
//! happens to agree with the height is a `Vec`-ism the prototype must not
//! lean on.
//!
//! What the acceptance bar demands (`docs/sprop-design.md` §8 step 6), and
//! where each is pinned:
//!
//! - **(a) `match` β fires on *open* recursive data**, the strip making the
//!   index cast invisible: `beta_fires_on_open_recursive_data` (the stored
//!   proof lands only in positions the `sEq` irrelevance arm and Σ-η erase)
//!   and `index_casts_are_invisible_through_the_strip` (a *neutral*-proof
//!   `transp` around a forded value strips; the eliminator β-fires on the
//!   convertible-not-equal index spelling with no cast term at all; and the
//!   head-only limit of the strip — a redundant cast is opaque to
//!   elimination — is pinned as a negative rather than papered over).
//! - **(b) value equality on forded data costs no `Id`-transport lemmas**:
//!   `value_equality_needs_no_transport_lemmas` — proof-swapped values are
//!   convertible outright, and the would-be transport lemma is literally
//!   `refl`. The route-2 hazard it dissolves is pinned as a contrast:
//!   `route_2_contrast_stored_id_proofs_obstruct_value_equality`.
//! - **(c) mismatched indices genuinely reject**:
//!   `negative_controls_mismatched_indices_reject` — the `sEq` field is a
//!   real constraint, not a silently-droppable one (axis 4: without it,
//!   `Vec_f` would be a quotient with every length inhabiting every index).
//!
//! The four axes of `docs/testing-generated-terms.md`: literal scrutinee
//! *that computes* (`to_kvec_computes_on_literal_data` converts against
//! literal kernel tuples); neutral scrutinee (`to_kvec` typed on an open
//! vector, β on constructor-headed-but-open data); open element type
//! (`open_element_type_instance` — the whole apparatus over an ambient
//! `A : Ty 0`, where every closed-type test would hide a shift bug); and
//! checking positions throughout (constructors checked at `plus0`-spelled
//! indices, `transp` payloads checked across the fording equation, `refl`
//! checked against a strip-dependent goal).
//!
//! **The eliminator finding, recorded for the verdict.** The generated
//! eliminator below re-derives the tail's index from the *motive's* index
//! variable by large elimination on `Nat` (a per-constructor inversion:
//! `S`-headed result index, so the successor branch peels it with `pred`
//! and the zero branch is no-confusion via `zero_pred`/`is_succ` + `transp`
//! into `Empty`). That inversion is what makes β **definitional** on open
//! recursive data: the stored proof is re-derived rather than consulted, and
//! lands only at `sEq` type. The alternative — transporting the arm along
//! the stored proof, no inversion — types at *any* index expression, but its
//! β waits on the strip's guard, i.e. is definitional only where the
//! endpoints convert (closed or index-computable data) and propositional
//! residue otherwise. So 2b's definitional-β story on open data has exactly
//! route 1's invertibility condition; where it fails (`plus(m,k)`-shaped
//! indices), fording still types and still owes no equality lemmas — the
//! setoid test's currency — but open-data β degrades to strip-guarded.
//!
//! Skeleton-choice caveat, also for the verdict: the skeleton here is the
//! tier-1 height encoding, not `Wf` — `Vec` does not branch, and its
//! compiler skeleton is tier 1. The fording layer (the `sEq` field, the
//! inversion, the irrelevance arithmetic) never looks inside the skeleton's
//! eliminator, so a `Wf` skeleton changes the recursion plumbing and not
//! the fording; the branching-family composition (`Wf` + ford + coherence)
//! is untested here and stays open on the issue.

use std::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalSubst, LocalVar, Term, Type,
};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 1_000_000;

// ---------------------------------------------------------------------------
// Construction helpers
// ---------------------------------------------------------------------------

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn c(n: u64) -> Level {
    Level::constant(n)
}

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// A context of `n` entries for building substitutions — `LocalSubst::id`
/// reads only the length and base, so the entry types are irrelevant.
fn scope(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n).map(|_| CtxEntry { ty: rty(Type::Nat), level: c(0) }).collect::<Vec<_>>()).into(),
    }
}

fn triv() -> Term {
    Term::Triv { level: Level::Zero }
}

// ---------------------------------------------------------------------------
// The skeleton: tier-1 `List A` over an element *code* `el : Ty 0`.
//
// Every helper takes `el` in the scope where the helper's own result lives
// and shifts it under binders internally. Most tests pass `TmNat` (closed —
// which is exactly how axis-2 bugs hide); `open_element_type_instance`
// passes an ambient variable.
// ---------------------------------------------------------------------------

/// `spine el n : Ty 0` — `⌜Unit⌝` at 0, `⌜Σ(_ : El el). El rec⌝` at `S _`.
fn sk_code(el: &Term, n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        // (k, rec) with the Σ-code's fst scoped there and snd one deeper.
        step: rt(Term::TmSigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rt(el.shift_local(2)),
            snd: rt(v(1)),
        }),
        scrut: rt(n),
    }
}

fn sk_ty(el: &Term, n: Term) -> Type {
    Type::El { level: c(0), tm: rt(sk_code(el, n)) }
}

/// `List el = Σ(h : Nat). El (spine el h)`.
fn skel(el: &Term) -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(sk_ty(&el.shift_local(1), v(0))),
    }
}

fn sheight(el: &Term, s: Term) -> Term {
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(sk_ty(&el.shift_local(1), v(0))),
        pair: rt(s),
    }
}

fn spayload(el: &Term, s: Term) -> Term {
    Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(sk_ty(&el.shift_local(1), v(0))),
        pair: rt(s),
    }
}

fn srepack(el: &Term, h: Term, payload: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(sk_ty(&el.shift_local(1), v(0))),
        fst: rt(h),
        snd: rt(payload),
    }
}

fn snil(el: &Term) -> Term {
    srepack(el, Term::Zero, triv())
}

/// `scons a s` — height `S (fst s)`, payload `⟨a, snd s⟩`.
fn scons(el: &Term, a: Term, s: Term) -> Term {
    let h = sheight(el, s.clone());
    let inner = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::El { level: c(0), tm: rt(el.clone()) }),
        snd_ty: rty(sk_ty(&el.shift_local(1), h.shift_local(1))),
        fst: rt(a),
        snd: rt(spayload(el, s)),
    };
    srepack(el, Term::Succ(rt(h)), inner)
}

/// `len s` — the eliminator-computed length: the fold
/// `elim_Nat(ĥ. Π(p : spine ĥ). Nat; λ_. 0; k rec. λp. S (rec (snd p)))`
/// applied to the skeleton's own height and payload. Reduces to `S (len s₀)`
/// on `scons a s₀` with `s₀` open, which is the tier-1 property everything
/// downstream leans on.
fn len(el: &Term, s: Term) -> Term {
    let motive = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(sk_ty(&el.shift_local(1), v(0))),
        cod: rty(Type::Nat),
    };
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(sk_ty(el, Term::Zero)),
        body: rt(Term::Zero),
    };
    // (k, rec) ⊢ λ(p : spine (S k)). S (rec (snd p)); body scope (k, rec, p).
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(sk_ty(&el.shift_local(2), Term::Succ(rt(v(1))))),
        body: rt(Term::Succ(rt(Term::App {
            fun: rt(v(1)),
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(sk_ty(&el.shift_local(3), v(2))),
            cod: rty(Type::Nat),
            arg: rt(Term::Snd {
                fst_level: c(0),
                snd_level: c(0),
                fst_ty: rty(Type::El { level: c(0), tm: rt(el.shift_local(3)) }),
                snd_ty: rty(sk_ty(&el.shift_local(4), v(3))),
                pair: rt(v(0)),
            }),
        }))),
    };
    Term::App {
        fun: rt(Term::ElimNat {
            level: c(0),
            motive: rty(motive),
            base: rt(base),
            step: rt(step),
            scrut: rt(sheight(el, s.clone())),
        }),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(sk_ty(el, sheight(el, s.clone()))),
        cod: rty(Type::Nat),
        arg: rt(spayload(el, s)),
    }
}

// ---------------------------------------------------------------------------
// The forded family: `Vec_f(el; m) = Σ(s : List el). sEq(Nat; len s; m)`
// ---------------------------------------------------------------------------

fn seqn(lhs: Term, rhs: Term) -> Type {
    Type::SEq { level: c(0), ty: rty(Type::Nat), lhs: rt(lhs), rhs: rt(rhs) }
}

fn srefl_n(t: Term) -> Term {
    Term::SRefl { level: c(0), ty: rty(Type::Nat), tm: rt(t) }
}

fn vecf(el: &Term, m: Term) -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(skel(el)),
        snd: rty(seqn(len(&el.shift_local(1), v(0)), m.shift_local(1))),
    }
}

fn fst_f(el: &Term, m: Term, x: Term) -> Term {
    Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(skel(el)),
        snd_ty: rty(seqn(len(&el.shift_local(1), v(0)), m.shift_local(1))),
        pair: rt(x),
    }
}

fn snd_f(el: &Term, m: Term, x: Term) -> Term {
    Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(skel(el)),
        snd_ty: rty(seqn(len(&el.shift_local(1), v(0)), m.shift_local(1))),
        pair: rt(x),
    }
}

/// `⟨s, e⟩ : Vec_f(el; m)` — repackage a skeleton and an index proof.
fn pairf(el: &Term, m: Term, s: Term, e: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(skel(el)),
        snd_ty: rty(seqn(len(&el.shift_local(1), v(0)), m.shift_local(1))),
        fst: rt(s),
        snd: rt(e),
    }
}

/// `nil_f : Vec_f(el; 0)` — the index proof is `srefl` at the computed
/// length (`len nil ⇝ 0`, so it checks at `sEq(len nil; 0)`).
fn fnil(el: &Term) -> Term {
    pairf(el, Term::Zero, snil(el), srefl_n(Term::Zero))
}

/// `cons_f n x xs : Vec_f(el; S n)` for `xs : Vec_f(el; n)` — skeleton
/// `scons x (fst xs)`, and the index proof is the tail's proof pushed
/// through `S` by `transp`:
/// `transp(Nat; z. sEq(S (len (fst xs)); S z); len (fst xs); n; snd xs;
///         srefl (S (len (fst xs))))`.
fn fcons(el: &Term, n: Term, x: Term, xs: Term) -> Term {
    let s0 = fst_f(el, n.clone(), xs.clone());
    let p0 = snd_f(el, n.clone(), xs);
    let l0 = len(el, s0.clone());
    let proof = Term::Transp {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        motive: rty(seqn(Term::Succ(rt(l0.shift_local(1))), Term::Succ(rt(v(0))))),
        lhs: rt(l0.clone()),
        rhs: rt(n.clone()),
        proof: rt(p0),
        tm: rt(srefl_n(Term::Succ(rt(l0)))),
    };
    pairf(el, Term::Succ(rt(n)), scons(el, x, s0), proof)
}

/// A literal `Vec_f(⌜Nat⌝; k)` from a slice, index computed.
fn fvec_of(elems: &[u64]) -> Term {
    let mut t = fnil(&Term::TmNat);
    let mut k = 0u64;
    for &e in elems.iter().rev() {
        t = fcons(&Term::TmNat, nat(k), nat(e), t);
        k += 1;
    }
    t
}

// ---------------------------------------------------------------------------
// Nat utilities for the index inversion
// ---------------------------------------------------------------------------

/// `plus0 k` — `elim_Nat(_. Nat; k; _ ih. S ih; 0)`: reduces to `k` but is
/// not syntactically `k`; the canonical convertible-not-equal index.
fn plus0(k: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(k),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(Term::Zero),
    }
}

/// `⌜Unit⌝` at 0, `⌜Empty⌝` at `S _` — no-confusion for a `0`-indexed arm.
fn zero_pred(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmUnit { level: Level::Zero }),
        step: rt(Term::TmEmpty { level: Level::Zero }),
        scrut: rt(n),
    }
}

/// `⌜Empty⌝` at 0, `⌜Unit⌝` at `S _` — no-confusion for an `S`-indexed arm.
fn is_succ(n: Term) -> Term {
    Term::ElimNat {
        level: c(1),
        motive: rty(Type::Ty(c(0))),
        base: rt(Term::TmEmpty { level: Level::Zero }),
        step: rt(Term::TmUnit { level: Level::Zero }),
        scrut: rt(n),
    }
}

/// `pred n` — `elim_Nat(_. Nat; 0; k _. k; n)`.
fn pred(n: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(v(1)),
        scrut: rt(n),
    }
}

fn el_of(code: Term) -> Type {
    Type::El { level: c(0), tm: rt(code) }
}

// ---------------------------------------------------------------------------
// The skeleton's recursor (tier1_fording.rs `list_rec`, element-code
// threaded): `elim_Nat` on the height at the family of payloads.
// ---------------------------------------------------------------------------

/// `M[l/z]` for a motive `M` scoped in `(Γ, z : List el)` and `l` scoped in
/// `Γ` extended by `extra` binders.
fn mot_at(depth: u32, motive: &Type, l: Term, extra: u32) -> Type {
    motive.apply_local(&LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(l)))
}

/// `elim_List(z. M; nil_case; a tail ih. cons_case; scrut)` — `motive`
/// scoped in `(Γ, z : List el)` at level `ml`; `nil_case : M[nil/z]` in `Γ`;
/// `cons_case : M[scons a tail/z]` in `(Γ, a : El el, tail, ih : M[tail/z])`.
#[allow(clippy::too_many_arguments)]
fn list_rec(
    depth: u32,
    el: &Term,
    ml: &Level,
    motive: &Type,
    nil_case: Term,
    cons_case: Term,
    scrut: Term,
) -> Term {
    let base = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(sk_ty(el, Term::Zero)),
        body: rt(nil_case.shift_local(1)),
    };

    // Step scoped (Γ, k, rec); body scope (Γ, k, rec, payload) with k = 2,
    // rec = 1, payload = 0, and `spine (S k)` reducing to a Σ.
    let elem = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el_of(el.shift_local(3))),
        snd_ty: rty(sk_ty(&el.shift_local(4), v(3))),
        pair: rt(v(0)),
    };
    let tail_payload = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el_of(el.shift_local(3))),
        snd_ty: rty(sk_ty(&el.shift_local(4), v(3))),
        pair: rt(v(0)),
    };
    let tail = srepack(&el.shift_local(3), v(2), tail_payload.clone());
    let ih = Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(sk_ty(&el.shift_local(3), v(2))),
        cod: rty(mot_at(depth, motive, srepack(&el.shift_local(4), v(3), v(0)), 4)),
        arg: rt(tail_payload),
    };
    let step_body = cons_case.apply_local(
        &LocalSubst::id(&scope(depth))
            .shift_local(3)
            .extended(rt(elem))
            .extended(rt(tail))
            .extended(rt(ih)),
    );
    let step = Term::Lam {
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(sk_ty(&el.shift_local(2), Term::Succ(rt(v(1))))),
        body: rt(step_body),
    };

    let recursion = Term::ElimNat {
        level: ml.clone(),
        motive: rty(Type::Pi {
            dom_level: c(0),
            cod_level: ml.clone(),
            dom: rty(sk_ty(&el.shift_local(1), v(0))),
            cod: rty(mot_at(depth, motive, srepack(&el.shift_local(2), v(1), v(0)), 2)),
        }),
        base: rt(base),
        step: rt(step),
        scrut: rt(sheight(el, scrut.clone())),
    };
    Term::App {
        fun: rt(recursion),
        dom_level: c(0),
        cod_level: ml.clone(),
        dom: rty(sk_ty(el, sheight(el, scrut.clone()))),
        cod: rty(mot_at(
            depth,
            motive,
            srepack(&el.shift_local(1), sheight(el, scrut.clone()).shift_local(1), v(0)),
            1,
        )),
        arg: rt(spayload(el, scrut)),
    }
}

// ---------------------------------------------------------------------------
// The forded family's eliminator — the term the generator would emit.
//
// Skeleton recursion at the fording motive
//   Q(s) := Π(m' : Nat). Π(e : sEq(len s; m')). M[m', ⟨s, e⟩]
// with each arm inverting the *motive's* index by `elim_Nat` — no-confusion
// into `Empty` where the arm's own index shape cannot match, and in the cons
// arm's successor branch the tail's proof re-derived by `transp` at the
// `pred` motive. The stored proof is consulted nowhere; every equation in
// the output sits at `sEq` type, where the irrelevance arm erases it.
// ---------------------------------------------------------------------------

/// `M2[m, val]` for a motive scoped `(Γ, m' : Nat, z : Vec_f(el; m'))`, with
/// `m`/`val` scoped in `Γ` extended by `extra` binders.
fn mot2_at(depth: u32, motive2: &Type, m: Term, val: Term, extra: u32) -> Type {
    motive2.apply_local(
        &LocalSubst::id(&scope(depth)).shift_local(extra).extended(rt(m)).extended(rt(val)),
    )
}

/// `elim_Vecf(m' z. M; nil_case; n x xs ih. cons_case; idx; val)` at
/// level-0 motives. `motive2` scoped `(Γ, m', z : Vec_f(el; m'))`;
/// `nil_case : M[0, nil_f]` in `Γ`; `cons_case : M[S n, cons_f n x xs]` in
/// `(Γ, n, x : El el, xs : Vec_f(el; n), ih : M[n, xs])`; `idx`, `val` in Γ.
#[allow(clippy::too_many_arguments)]
fn vec_rec(
    depth: u32,
    el: &Term,
    motive2: &Type,
    nil_case: Term,
    cons_case: Term,
    idx: Term,
    val: Term,
) -> Term {
    // Q, scoped (Γ, zl : List el): Π(m'). Π(e : sEq(len zl; m')). M[m', ⟨zl, e⟩].
    let q = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Nat),
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(seqn(len(&el.shift_local(2), v(1)), v(0))),
            cod: rty(mot2_at(
                depth,
                motive2,
                v(1),
                pairf(&el.shift_local(3), v(1), v(2), v(0)),
                3,
            )),
        }),
    };

    // Nil arm, scoped Γ, of type Q[nil]: λ(m'). elim_Nat(m'; zero ↦ λe. b;
    // succ ↦ λe. absurd). Scope inside the λ: (Γ, m').
    let nil_arm = {
        // elim_Nat motive, scoped (Γ, m', ẑ):
        //   Π(e : sEq(len nil; ẑ)). M[ẑ, ⟨nil, e⟩].
        let nmot = Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(seqn(len(&el.shift_local(2), snil(&el.shift_local(2))), v(0))),
            cod: rty(mot2_at(
                depth,
                motive2,
                v(1),
                pairf(&el.shift_local(3), v(1), snil(&el.shift_local(3)), v(0)),
                3,
            )),
        };
        // Zero branch, scoped (Γ, m'): λ(e : sEq(len nil; 0)). nil_case —
        // `⟨nil, e⟩ ≡ ⟨nil, srefl⟩` by the irrelevance arm, so the case fits.
        let zero_branch = Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(seqn(len(&el.shift_local(1), snil(&el.shift_local(1))), Term::Zero)),
            body: rt(nil_case.shift_local(2)),
        };
        // Succ branch, scoped (Γ, m', k, ihN): λ(e : sEq(len nil; S k)).
        // no-confusion — transp e through `zero_pred` turns ⟨⟩ into Empty.
        let succ_branch = {
            // Body scope (Γ, m', k, ihN, e): m' = 3, k = 2, e = 0.
            let goal = mot2_at(
                depth,
                motive2,
                Term::Succ(rt(v(2))),
                pairf(&el.shift_local(4), Term::Succ(rt(v(2))), snil(&el.shift_local(4)), v(0)),
                4,
            );
            let absurd = Term::Transp {
                ty_level: c(0),
                motive_level: c(0),
                ty: rty(Type::Nat),
                motive: rty(el_of(zero_pred(v(0)))),
                lhs: rt(len(&el.shift_local(4), snil(&el.shift_local(4)))),
                rhs: rt(Term::Succ(rt(v(2)))),
                proof: rt(v(0)),
                tm: rt(triv()),
            };
            Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(seqn(
                    len(&el.shift_local(3), snil(&el.shift_local(3))),
                    Term::Succ(rt(v(1))),
                )),
                body: rt(Term::ElimEmpty {
                    level: c(0),
                    scrut_level: Level::Zero,
                    motive: rty(goal.shift_local(1)),
                    scrut: rt(absurd),
                }),
            }
        };
        Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Nat),
            body: rt(Term::ElimNat {
                level: c(0),
                motive: rty(nmot),
                base: rt(zero_branch),
                step: rt(succ_branch),
                scrut: rt(v(0)),
            }),
        }
    };

    // Cons arm, scoped (Γ, a : El el, tail : List el, ihQ : Q[tail]), of
    // type Q[scons a tail]: λ(m'). elim_Nat(m'; zero ↦ absurd; succ ↦ the
    // inversion). Scope inside the λ: (Γ, a, tail, ihQ, m') with a = 3,
    // tail = 2, ihQ = 1, m' = 0.
    let cons_arm = {
        // elim_Nat motive, scoped (Γ, a, tail, ihQ, m', ẑ): a = 4, tail = 3.
        let nmot = Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(seqn(
                len(&el.shift_local(5), scons(&el.shift_local(5), v(4), v(3))),
                v(0),
            )),
            cod: rty(mot2_at(
                depth,
                motive2,
                v(1),
                pairf(
                    &el.shift_local(6),
                    v(1),
                    scons(&el.shift_local(6), v(5), v(4)),
                    v(0),
                ),
                6,
            )),
        };
        // Zero branch, scoped (Γ, a, tail, ihQ, m'): the index is S-headed,
        // so `sEq(len (scons a tail); 0)` is absurd via `is_succ`.
        let zero_branch = {
            // Body scope (Γ, a, tail, ihQ, m', e): a = 4, tail = 3, e = 0.
            let goal = mot2_at(
                depth,
                motive2,
                Term::Zero,
                pairf(
                    &el.shift_local(5),
                    Term::Zero,
                    scons(&el.shift_local(5), v(4), v(3)),
                    v(0),
                ),
                5,
            );
            let absurd = Term::Transp {
                ty_level: c(0),
                motive_level: c(0),
                ty: rty(Type::Nat),
                motive: rty(el_of(is_succ(v(0)))),
                lhs: rt(len(&el.shift_local(5), scons(&el.shift_local(5), v(4), v(3)))),
                rhs: rt(Term::Zero),
                proof: rt(v(0)),
                tm: rt(triv()),
            };
            Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(seqn(
                    len(&el.shift_local(4), scons(&el.shift_local(4), v(3), v(2))),
                    Term::Zero,
                )),
                body: rt(Term::ElimEmpty {
                    level: c(0),
                    scrut_level: Level::Zero,
                    motive: rty(goal.shift_local(1)),
                    scrut: rt(absurd),
                }),
            }
        };
        // Succ branch, scoped (Γ, a, tail, ihQ, m', k, ihN) — the
        // inversion. Body scope adds e: a = 6, tail = 5, ihQ = 4, m' = 3,
        // k = 2, ihN = 1, e = 0.
        let succ_branch = {
            let el7 = el.shift_local(7);
            // e' : sEq(len tail; k), by transp e at the `pred` motive; the
            // payload is srefl at `pred (len (scons a tail)) ⇝ len tail`.
            let lt = len(&el7, v(5));
            let e_tail = Term::Transp {
                ty_level: c(0),
                motive_level: c(0),
                ty: rty(Type::Nat),
                motive: rty(seqn(len(&el.shift_local(8), v(6)), pred(v(0)))),
                lhs: rt(len(&el7, scons(&el7, v(6), v(5)))),
                rhs: rt(Term::Succ(rt(v(2)))),
                proof: rt(v(0)),
                tm: rt(srefl_n(lt.clone())),
            };
            // xs' := ⟨tail, e'⟩ : Vec_f(el; k).
            let xs_tail = pairf(&el7, v(2), v(5), e_tail.clone());
            // ih := ihQ k e' : M[k, ⟨tail, e'⟩].
            let ih = Term::App {
                fun: rt(Term::App {
                    fun: rt(v(4)),
                    dom_level: c(0),
                    cod_level: c(0),
                    dom: rty(Type::Nat),
                    // Q[tail]'s codomain, scoped (…, m''): tail = 6.
                    cod: rty(Type::Pi {
                        dom_level: c(0),
                        cod_level: c(0),
                        dom: rty(seqn(len(&el.shift_local(8), v(6)), v(0))),
                        cod: rty(mot2_at(
                            depth,
                            motive2,
                            v(1),
                            pairf(&el.shift_local(9), v(1), v(7), v(0)),
                            9,
                        )),
                    }),
                    arg: rt(v(2)),
                }),
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(seqn(len(&el7, v(5)), v(2))),
                // Scoped (…, e''): tail = 6, k = 3.
                cod: rty(mot2_at(
                    depth,
                    motive2,
                    v(3),
                    pairf(&el.shift_local(8), v(3), v(6), v(0)),
                    8,
                )),
                arg: rt(e_tail),
            };
            let body = cons_case.apply_local(
                &LocalSubst::id(&scope(depth))
                    .shift_local(7)
                    .extended(rt(v(2)))
                    .extended(rt(v(6)))
                    .extended(rt(xs_tail))
                    .extended(rt(ih)),
            );
            Term::Lam {
                dom_level: c(0),
                cod_level: c(0),
                dom: rty(seqn(
                    len(&el.shift_local(6), scons(&el.shift_local(6), v(5), v(4))),
                    Term::Succ(rt(v(1))),
                )),
                body: rt(body),
            }
        };
        Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(Type::Nat),
            body: rt(Term::ElimNat {
                level: c(0),
                motive: rty(nmot),
                base: rt(zero_branch),
                step: rt(succ_branch),
                scrut: rt(v(0)),
            }),
        }
    };

    // Skeleton recursion at Q, then the index and the stored proof.
    let s_val = fst_f(el, idx.clone(), val.clone());
    let r0 = list_rec(depth, el, &c(0), &q, nil_arm, cons_arm, s_val.clone());
    let r1 = Term::App {
        fun: rt(r0),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Nat),
        // Q[fst val]'s codomain, scoped (Γ, m').
        cod: rty(Type::Pi {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(seqn(len(&el.shift_local(1), s_val.shift_local(1)), v(0))),
            cod: rty(mot2_at(
                depth,
                motive2,
                v(1),
                pairf(&el.shift_local(2), v(1), s_val.shift_local(2), v(0)),
                2,
            )),
        }),
        arg: rt(idx.clone()),
    };
    Term::App {
        fun: rt(r1),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(seqn(len(el, s_val.clone()), idx.clone())),
        // Scoped (Γ, e): the final instance.
        cod: rty(mot2_at(
            depth,
            motive2,
            idx.shift_local(1),
            pairf(&el.shift_local(1), idx.shift_local(1), s_val.shift_local(1), v(0)),
            1,
        )),
        arg: rt(snd_f(el, idx, val)),
    }
}

// ---------------------------------------------------------------------------
// `to_kvec` — the dependent-motive consumer: `Π m (v : Vec_f(el; m)).
// Vec(El el; m)`, the kernel's primitive container as the target. This is
// both the eliminator demo and the "a declared family behaves as well as
// `[T; n]`" bridge.
// ---------------------------------------------------------------------------

fn kvec(el: &Term, m: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(el_of(el.clone())), len: rt(m) }
}

fn to_kvec(depth: u32, el: &Term, idx: Term, val: Term) -> Term {
    // Motive, scoped (Γ, m', z): Vec(El el; m').
    let motive2 = kvec(&el.shift_local(2), v(1));
    // Cons case, scoped (Γ, n, x, xs, ih): ⟨x, ih⟩ at Vec(El el; S n) —
    // which reduces to Σ(_ : El el). Vec(El el; n).
    let cons_case = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el_of(el.shift_local(4))),
        snd_ty: rty(kvec(&el.shift_local(5), v(4))),
        fst: rt(v(2)),
        snd: rt(v(0)),
    };
    vec_rec(depth, el, &motive2, triv(), cons_case, idx, val)
}

/// A literal kernel tuple `⟨e₀, ⟨e₁, … ⟨⟩⟩⟩ : Vec(Nat; k)`.
fn kvec_lit(elems: &[u64]) -> Term {
    let mut t = triv();
    let mut k = 0u64;
    for &e in elems.iter().rev() {
        t = Term::Pair {
            fst_level: c(0),
            snd_level: c(0),
            fst_ty: rty(Type::Nat),
            snd_ty: rty(kvec(&Term::TmNat, nat(k))),
            fst: rt(nat(e)),
            snd: rt(t),
        };
        k += 1;
    }
    t
}

// ---------------------------------------------------------------------------
// Checking helpers
// ---------------------------------------------------------------------------

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("the type does not check: {e:?}"));
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn ck_fails(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("the kernel gate must reject this");
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}

fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

/// `Γ = (n : Nat, x : Nat, xs : Vec_f(⌜Nat⌝; n))` — the open-recursive-data
/// scenario every β test lives in. In this context n = 2, x = 1, xs = 0.
fn open_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    ext(&g, vecf(&Term::TmNat, v(1)), c(0))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn the_forded_type_and_constructors_check() {
    let g = nil_ctx();
    ck(&g, &fnil(&Term::TmNat), &vecf(&Term::TmNat, Term::Zero), c(0));
    ck(&g, &fvec_of(&[5, 7]), &vecf(&Term::TmNat, nat(2)), c(0));

    // Open tail and open index: Γ = (n, x, xs) ⊢ cons_f n x xs : Vec_f(S n).
    let g = open_ctx();
    let t = fcons(&Term::TmNat, v(2), v(1), v(0));
    ck(&g, &t, &vecf(&Term::TmNat, Term::Succ(rt(v(2)))), c(0));

    // Checking position at a convertible-not-equal index spelling: the same
    // constructor checked against `Vec_f(plus0 (S n))` — the sEq-typed
    // conversion in the goal's snd component crosses `plus0 (S n) ≡ S n`.
    ck(&g, &t, &vecf(&Term::TmNat, plus0(Term::Succ(rt(v(2))))), c(0));
}

#[test]
fn to_kvec_computes_on_literal_data() {
    // Axis 1: literal scrutinee, and assert it *computes* — the eliminator
    // lands exactly on the kernel's primitive tuples.
    let g = nil_ctx();
    let t0 = to_kvec(0, &Term::TmNat, Term::Zero, fnil(&Term::TmNat));
    ck(&g, &t0, &kvec(&Term::TmNat, Term::Zero), c(0));
    conv(&g, &t0, &triv(), &kvec(&Term::TmNat, Term::Zero), c(0));

    let t2 = to_kvec(0, &Term::TmNat, nat(2), fvec_of(&[5, 7]));
    ck(&g, &t2, &kvec(&Term::TmNat, nat(2)), c(0));
    conv(&g, &t2, &kvec_lit(&[5, 7]), &kvec(&Term::TmNat, nat(2)), c(0));
}

#[test]
fn to_kvec_is_typed_on_a_neutral_scrutinee() {
    // Axis: neutral scrutinee — Γ = (m, v : Vec_f(m)) ⊢ to_kvec m v, stuck
    // but typed at the family instance over the open index.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, vecf(&Term::TmNat, v(0)), c(0));
    ck(&g, &to_kvec(2, &Term::TmNat, v(1), v(0)), &kvec(&Term::TmNat, v(1)), c(0));
}

#[test]
fn beta_fires_on_open_recursive_data() {
    // Acceptance (a), first half: `match` β is definitional on
    // constructor-headed data whose element, tail and *index* are all open.
    // The eliminator's successor branch re-derives the tail's proof by
    // transp-at-`pred`; that proof and the stored one meet only at sEq type
    // (the irrelevance arm) and inside repackaged pairs (Σ-η), so the
    // comparison closes with no equality lemma anywhere.
    let g = open_ctx();
    let lhs = to_kvec(
        3,
        &Term::TmNat,
        Term::Succ(rt(v(2))),
        fcons(&Term::TmNat, v(2), v(1), v(0)),
    );
    // ⟨x, to_kvec n xs⟩, the cons case's value.
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(kvec(&Term::TmNat, v(3))),
        fst: rt(v(1)),
        snd: rt(to_kvec(3, &Term::TmNat, v(2), v(0))),
    };
    let at = kvec(&Term::TmNat, Term::Succ(rt(v(2))));
    ck(&g, &lhs, &at, c(0));
    conv(&g, &lhs, &rhs, &at, c(0));

    // The nil β as well, closed: already pinned by the literal test; here
    // the open-index variant — to_kvec at `plus0 0` still reaches the base.
    let g0 = nil_ctx();
    let t = to_kvec(0, &Term::TmNat, plus0(Term::Zero), fnil(&Term::TmNat));
    conv(&g0, &t, &triv(), &kvec(&Term::TmNat, Term::Zero), c(0));
}

#[test]
fn index_casts_are_invisible_through_the_strip() {
    // Acceptance (a), second half: a *neutral*-proof transp around a whole
    // forded value, at endpoints that are convertible without being equal
    // (`plus0 (S n) ≡ S n`, n open). The strip erases the cast in
    // conversion. Γ = open_ctx + e : sEq(Nat; plus0 (S n); S n); n = 3,
    // x = 2, xs = 1, e = 0.
    let g = ext(
        &open_ctx(),
        seqn(plus0(Term::Succ(rt(v(2)))), Term::Succ(rt(v(2)))),
        c(0),
    );
    let w = fcons(&Term::TmNat, v(3), v(2), v(1));
    // cast := transp(Nat; z. Vec_f(z); plus0 (S n); S n; e; w). The payload
    // `w : Vec_f(S n)` is *checked* at the motive's left instance
    // `Vec_f(plus0 (S n))` — a checking position across the index equation.
    let cast = Term::Transp {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        motive: rty(vecf(&Term::TmNat, v(0))),
        lhs: rt(plus0(Term::Succ(rt(v(3))))),
        rhs: rt(Term::Succ(rt(v(3)))),
        proof: rt(v(0)),
        tm: rt(w.clone()),
    };
    let at = vecf(&Term::TmNat, Term::Succ(rt(v(3))));
    ck(&g, &cast, &at, c(0));
    conv(&g, &cast, &w, &at, c(0));

    // The scheme-level invisibility: the cast is not *needed* in the first
    // place. The value spelled at one index works at the other (types with
    // sEq components convert endpoint-wise), and the eliminator β-fires
    // when handed the convertible-not-equal index spelling directly.
    let lhs = to_kvec(4, &Term::TmNat, plus0(Term::Succ(rt(v(3)))), w.clone());
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(kvec(&Term::TmNat, v(4))),
        fst: rt(v(2)),
        snd: rt(to_kvec(4, &Term::TmNat, v(3), v(1))),
    };
    let at_k = kvec(&Term::TmNat, Term::Succ(rt(v(3))));
    ck(&g, &lhs, &at_k, c(0));
    conv(&g, &lhs, &rhs, &at_k, c(0));

    // FINDING, pinned so it cannot drift silently: the strip is keyed on a
    // transp at the *head* of a compared term (conv.rs `Conv::strip`); a
    // stuck transp blocking an elimination spine (`Fst (Fst cast)` inside
    // the eliminator's height scrutinee) is never seen by it, so the
    // *redundant* cast — strippable, hence unnecessary — is opaque to
    // elimination: `cast ≡ w` holds (above) but `elim cast ≡ elim w` does
    // not. Algorithmic incompleteness at exactly the terms nobody needs:
    // the generator's rule is therefore "never emit a cast at convertible
    // endpoints", and the declarative-vs-algorithmic gap is flagged for the
    // ch. 07 completeness statement rather than papered over here.
    let opaque = to_kvec(4, &Term::TmNat, Term::Succ(rt(v(3))), cast);
    ck(&g, &opaque, &at_k, c(0));
    not_conv(&g, &opaque, &rhs, &at_k, c(0));
}

#[test]
fn value_equality_needs_no_transport_lemmas() {
    // Acceptance (b). First: values that differ only in how the index proof
    // was obtained are convertible outright. Γ = (n, xs : Vec_f(n),
    // e2 : sEq(Nat; len (fst xs); n)) — e2 is a *different* proof of the
    // same equation than the one stored in xs.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, vecf(&Term::TmNat, v(0)), c(0));
    let g = ext(
        &g,
        seqn(len(&Term::TmNat, fst_f(&Term::TmNat, v(1), v(0))), v(1)),
        c(0),
    );
    // n = 2, xs = 1, e2 = 0.
    let repacked = pairf(&Term::TmNat, v(2), fst_f(&Term::TmNat, v(2), v(1)), v(0));
    conv(&g, &repacked, &v(1), &vecf(&Term::TmNat, v(2)), c(0));

    // Second: the would-be transport lemma is `refl`. Γ = (n,
    // w : Vec_f(plus0 n)); w used at index n and at index plus0 n maps to
    // the same kernel vector *definitionally* — no cast term, no coherence
    // between the two uses, `Id(Vec(Nat; n); to_kvec n w; to_kvec (plus0 n)
    // w)` is refl. (The index-spelling half of this is Id-conversion too —
    // Id types also convert endpoint-wise; what `sEq` alone buys is that
    // the *stored proof* riding in w never enters the comparison, which is
    // the part the contrast test below shows failing for route 2.)
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, vecf(&Term::TmNat, plus0(v(0))), c(0));
    // n = 1, w = 0.
    let lhs = to_kvec(2, &Term::TmNat, v(1), v(0));
    let rhs = to_kvec(2, &Term::TmNat, plus0(v(1)), v(0));
    let at = kvec(&Term::TmNat, v(1));
    let goal = Type::Id { level: c(0), ty: rty(at.clone()), lhs: rt(lhs.clone()), rhs: rt(rhs) };
    let proof = Term::Refl { level: c(0), ty: rty(at), tm: rt(lhs) };
    ck(&g, &proof, &goal, c(0));
}

#[test]
fn route_2_contrast_stored_id_proofs_obstruct_value_equality() {
    // The route-2 defect the sEq field dissolves, pinned so the comparison
    // stays honest: with the index constraint stored as a *relevant* `Id`,
    // two values differing only in the proof are NOT convertible — that is
    // the stored-proof hazard (UIP at the index type, Hedberg at `Nat`, a
    // cliff at non-decidable indices) named in the issue's 2026-07-28 log.
    // Γ = (n, s : List, p q : Id(Nat; len s; n)); n = 3, s = 2, p = 1, q = 0.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, skel(&Term::TmNat), c(0));
    let id_at = |s: Term, n: Term| Type::Id {
        level: c(0),
        ty: rty(Type::Nat),
        lhs: rt(len(&Term::TmNat, s)),
        rhs: rt(n),
    };
    let g = ext(&g, id_at(v(0), v(1)), c(0));
    let g = ext(&g, id_at(v(1), v(2)), c(0));
    // The Id-forded Σ at this Γ: under the snd binder, n = v(4).
    let at = Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(skel(&Term::TmNat)),
        snd: rty(id_at(v(0), v(4))),
    };
    let mk = |p: Term| Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(skel(&Term::TmNat)),
        snd_ty: rty(id_at(v(0), v(4))),
        fst: rt(v(2)),
        snd: rt(p),
    };
    ck(&g, &mk(v(1)), &at, c(0));
    not_conv(&g, &mk(v(1)), &mk(v(0)), &at, c(0));
}

#[test]
fn open_element_type_instance() {
    // Axis 2: the whole apparatus over an ambient element code A : Ty 0 —
    // the instance where a de Bruijn shift error in the schema stops being
    // the identity. Γ = (A : Ty 0, n : Nat, x : El A, xs : Vec_f(A; n));
    // A = 3, n = 2, x = 1, xs = 0.
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, el_of(v(1)), c(0));
    let g = ext(&g, vecf(&v(2), v(1)), c(0));

    let t = fcons(&v(3), v(2), v(1), v(0));
    ck(&g, &t, &vecf(&v(3), Term::Succ(rt(v(2)))), c(0));

    // And β on open recursive data at the open element type.
    let lhs = to_kvec(4, &v(3), Term::Succ(rt(v(2))), t);
    let rhs = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(el_of(v(3))),
        snd_ty: rty(kvec(&v(4), v(3))),
        fst: rt(v(1)),
        snd: rt(to_kvec(4, &v(3), v(2), v(0))),
    };
    let at = kvec(&v(3), Term::Succ(rt(v(2))));
    ck(&g, &lhs, &at, c(0));
    conv(&g, &lhs, &rhs, &at, c(0));
}

#[test]
fn negative_controls_mismatched_indices_reject() {
    // Acceptance (c) / axis 4: the sEq field is a genuine constraint.
    let g = nil_ctx();

    // nil_f does not check at index 1 — srefl's endpoints cannot bridge
    // `0 ≡ 1`.
    ck_fails(&g, &fnil(&Term::TmNat), &vecf(&Term::TmNat, nat(1)), c(0));

    // The quotient control: a length-1 skeleton cannot inhabit Vec_f(0),
    // whatever srefl is tried in the proof slot — dropping the field (or it
    // failing to constrain) would make this check.
    let skel1 = scons(&Term::TmNat, nat(9), snil(&Term::TmNat));
    for proof in [srefl_n(Term::Zero), srefl_n(nat(1))] {
        let bad = pairf(&Term::TmNat, Term::Zero, skel1.clone(), proof);
        ck_fails(&g, &bad, &vecf(&Term::TmNat, Term::Zero), c(0));
    }

    // Distinct *neutral* indices: v : Vec_f(m) does not check at Vec_f(k),
    // and srefl does not prove sEq(m; k). Γ = (m, k, v : Vec_f(m)).
    let g = ext(&ext(&nil_ctx(), Type::Nat, c(0)), Type::Nat, c(0));
    let g = ext(&g, vecf(&Term::TmNat, v(1)), c(0));
    ck_fails(&g, &v(0), &vecf(&Term::TmNat, v(1)), c(0));
    ck_fails(&g, &srefl_n(v(2)), &seqn(v(2), v(1)), c(0));

    // Off-by-one on an open index: cons_f at Vec_f(n) instead of Vec_f(S n).
    let g = open_ctx();
    let t = fcons(&Term::TmNat, v(2), v(1), v(0));
    ck_fails(&g, &t, &vecf(&Term::TmNat, v(2)), c(0));

    // And irrelevance does not leak into the data: same index, different
    // elements — inconvertible.
    let g0 = nil_ctx();
    not_conv(&g0, &fvec_of(&[1]), &fvec_of(&[2]), &vecf(&Term::TmNat, nat(1)), c(0));
    // Same elements, honest positive alongside: conversion still works.
    conv(&g0, &fvec_of(&[1]), &fvec_of(&[1]), &vecf(&Term::TmNat, nat(1)), c(0));
}
