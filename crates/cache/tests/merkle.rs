//! The canaries under the Merkle substitution and the walker's framing
//! (`docs/infrastructure/cache-v1-design.md` §12, `crates/cache/src/merkle.rs` module docs).
//!
//! v1's canaries pinned a *scanner*: they asserted that the printed spellings
//! `u<d>`/`U<d>`/`g<d>` were rewritten and that ordinary text was not. There
//! is no printed form any more, so those questions do not exist. What survives
//! is the property they were proxies for, and it is now asked directly:
//!
//! - every site that carries a `GlobalVar` is **substituted** when it names a
//!   constant — the hash moves when the referent's interface hash moves, and
//!   does *not* move when only the position does — and a variable, which is
//!   bound in the term, is hashed as its index and reads no referent;
//! - the walk is **fail-closed** on an unresolvable or poisoned reference;
//! - opacity and a definition's body are part of the interface;
//! - and the framing is injective on a corpus of near-miss structures,
//!   including the fifteen `Branches` fields the old rendering did not print
//!   at all.
//!
//! The middle two are ported verbatim in meaning from v1. The last is new and
//! is the differential pin for the transition: it fails on anything the
//! scanner would have conflated.

use heather_kernel::rc::Rc;

use heather_cache::merkle::{Hash, interface_hash, term_hash};
use heather_cache::sha256::sha256;
use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalVar, LocalCtx, LocalSubst, LocalVar, Motives,
    SubstTail, Term, Type,
};

/// Distinguishable stand-in hashes for a Ψ prefix.
fn prefix(n: usize) -> Vec<Option<Hash>> {
    (0..n).map(|i| Some(sha256(format!("binding-{i}").as_bytes()))).collect()
}

fn id_subst() -> LocalSubst {
    LocalSubst { tail: SubstTail::Empty, terms: Vec::new() }
}

/// The constant at position `p`: what a reference to a committed binding is.
fn global_tm(p: u32) -> Term {
    Term::GlobalTm { var: GlobalVar::constant(p), subst: id_subst() }
}

/// The four places a `GlobalVar` occurs in `crates/kernel/src/term.rs`, each as
/// a term mentioning the constant at position `k` and (the last row's head,
/// the first binding, apart) nothing else global.
///
/// If a sixth site is ever added to the kernel, the walker's exhaustive
/// `match` breaks the build first — this list is the *behavioural* half of the
/// same guarantee, and adding the arm without adding the row here leaves a
/// site untested.
fn every_reference_site(k: u32) -> Vec<(&'static str, Term)> {
    every_site_of(GlobalVar::constant(k))
}

/// [`every_reference_site`] for any spelling.
fn every_site_of(g: GlobalVar) -> Vec<(&'static str, Term)> {
    let (tm, ty) = (
        Term::GlobalTm { var: g, subst: id_subst() },
        Type::GlobalTy { var: g, subst: id_subst() },
    );
    vec![
        ("Term::GlobalTm", tm),
        (
            "Type::GlobalTy",
            Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(ty),
                body: Rc::new(Term::Var(LocalVar(0))),
            },
        ),
        (
            "CtxBase::Var (a context's base)",
            Term::CtxApp { fun: Rc::new(Term::Zero), ctx: LocalCtx::ctx_var(g) },
        ),
        (
            "SubstTail::Wk",
            Term::GlobalTm {
                var: GlobalVar::constant(0),
                subst: LocalSubst { tail: SubstTail::Wk { len: 0, ctx_var: g }, terms: Vec::new() },
            },
        ),
    ]
}

/// Every reference site is fed the *referent's hash*: change what binding `k`
/// resolves to and the hash of the enclosing term must move.
///
/// This is v1's `rewrites_every_global_spelling` asked structurally. A site the
/// walker forgot to substitute would feed a positional index (or nothing) and
/// this would not move.
#[test]
fn every_reference_site_reads_its_referent() {
    let base = prefix(4);
    let mut moved = base.clone();
    moved[2] = Some(sha256(b"a different referent entirely"));

    for (what, t) in every_reference_site(2) {
        let a = term_hash(&base, 4, &t).expect("resolves");
        let b = term_hash(&moved, 4, &t).expect("resolves");
        assert_ne!(a, b, "{what}: the referent's interface hash is not reaching the walk");
    }
}

/// And the *position* is not fed: a reference over two Ψ prefixes of
/// different lengths, with the referent's hash at the position the reference
/// names in each, hashes the same.
///
/// This is the property the substitution exists for — the kernel telescope is
/// positional, and a key that kept a Ψ index would die on the first merge that
/// renumbers a suffix.
#[test]
fn no_reference_site_reads_its_position() {
    let referent = sha256(b"the referent");
    let short = {
        let mut v = prefix(2);
        v.push(Some(referent));
        v
    };
    let long = {
        let mut v = prefix(8);
        v.push(Some(referent));
        v
    };

    // The last binding of each: position 2 of the one, 8 of the other.
    for ((what, at_short), (_, at_long)) in every_reference_site(2).into_iter().zip(every_reference_site(8)) {
        let h = term_hash(&short, short.len() as u32, &at_short);
        assert!(h.is_some(), "{what}: unhashable");
        assert_eq!(h, term_hash(&long, long.len() as u32, &at_long), "{what}: hashed differently at two Ψ positions");
    }
}

/// A variable is bound in the term (a `letbox`'s, a recursor branch's, a
/// `Λg`'s): it is hashed as its index and reads nothing of Ψ. Before
/// constants, a bound global was resolved against the prefix like a free
/// one, so its hash was that of whichever committed binding sat that far from
/// the end: it moved with an unrelated binding, and two bound globals whose
/// stand-ins had one interface were one hash.
#[test]
fn a_bound_global_is_hashed_as_its_index() {
    let base = prefix(4);
    let mut moved = base.clone();
    for h in moved.iter_mut() {
        *h = Some(sha256(b"every binding is another"));
    }
    for i in [0u32, 1, 9] {
        for (what, t) in every_site_of(GlobalVar::index(i)) {
            let h = term_hash(&base, 4, &t);
            assert!(h.is_some(), "{what}: a bound global at index {i} is hashable whatever Ψ holds");
            let mut other = moved.clone();
            // The last row's head is the first binding, a constant.
            other[0] = base[0];
            assert_eq!(h, term_hash(&other, 4, &t), "{what}: a bound global read a referent");
        }
    }
    // Two bound globals stay two even when the bindings an index-resolving
    // walk would have read for them are one.
    let twins: Vec<Option<Hash>> = vec![Some(sha256(b"twin")); 4];
    for ((what, a), (_, b)) in every_site_of(GlobalVar::index(0)).into_iter().zip(every_site_of(GlobalVar::index(1))) {
        assert_ne!(term_hash(&twins, 4, &a), term_hash(&twins, 4, &b), "{what}: two bound globals hashed as one");
    }
    // And neither spelling is the other: index `i` and the constant it would
    // have been resolved to.
    for ((what, var), (_, konst)) in every_site_of(GlobalVar::index(1)).into_iter().zip(every_reference_site(2)) {
        assert_ne!(term_hash(&base, 4, &var), term_hash(&base, 4, &konst), "{what}: a variable hashed as a constant");
    }
}

/// The same property one level up, through a whole binding — v1's
/// `the_same_declaration_at_two_positions_agrees`, unchanged in meaning.
#[test]
fn the_same_declaration_at_two_positions_agrees() {
    let referent = sha256(b"the referent");
    let short = {
        let mut v = prefix(2);
        v.push(Some(referent));
        v
    };
    let long = {
        let mut v = prefix(8);
        v.push(Some(referent));
        v
    };

    // The declaration mentions the binding before it: position 2, or 8.
    let binding = |referent: u32| GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: Rc::new(Type::El { level: Level::Zero, tm: Rc::new(global_tm(referent)) }),
        level: Level::Zero,
        body: None,
    };

    assert_eq!(
        interface_hash(&short, &binding(2)),
        interface_hash(&long, &binding(8)),
        "the same declaration hashed differently at two Ψ positions"
    );
    assert!(interface_hash(&short, &binding(2)).is_some());
}

/// Fail closed: a reference outside the known prefix, or onto a poisoned
/// entry, yields no hash at all rather than a hash of something else.
///
/// Both cases can still arise — poison is real (a binding whose own hash
/// failed stores `None` and its dependents must not be cached), and an
/// out-of-range index is what a desynchronized prefix would look like — so
/// this is not simplified away.
#[test]
fn an_unresolvable_reference_is_not_hashable() {
    let p = prefix(2);
    for (what, t) in every_reference_site(7) {
        assert!(term_hash(&p, 2, &t).is_none(), "{what}: out-of-range reference produced a hash");
    }

    let poisoned: Vec<Option<Hash>> = vec![None, Some(sha256(b"fine"))];
    for (what, t) in every_reference_site(0) {
        assert!(term_hash(&poisoned, 2, &t).is_none(), "{what}: poison did not propagate");
    }
    assert!(term_hash(&poisoned, 2, &global_tm(1)).is_some(), "and only propagates");
    // The length the term is scoped at bounds its constants, whatever the
    // prefix holds past it.
    assert!(term_hash(&p, 1, &global_tm(1)).is_none(), "a constant past the scope produced a hash");
}

/// A theorem's interface must not depend on its proof, and a `fn`'s must
/// depend on its body. The interface split of
/// `issues/parallel-checking-and-caching.md` at the level of one hash.
#[test]
fn opacity_is_part_of_the_interface() {
    let p = prefix(1);
    let mk = |body: Option<Term>| GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: Rc::new(Type::Nat),
        level: Level::Zero,
        body: body.map(Rc::new),
    };
    let opaque = interface_hash(&p, &mk(None));
    let zero = interface_hash(&p, &mk(Some(Term::Zero)));
    let one = interface_hash(&p, &mk(Some(Term::Succ(Rc::new(Term::Zero)))));
    assert_ne!(opaque, zero, "opaque and transparent are different interfaces");
    assert_ne!(zero, one, "a definition's body is part of its interface");
}

/// The layer is part of the identity: the same `(ty, body)` checked at
/// `Layer::Code` and at `Layer::Meta` is two different kernel questions
/// (`gate.rs`'s `GateItem::layer`, since the meta gate joined the seam), so
/// the bindings the two build must never hash alike.
#[test]
fn the_layer_is_part_of_the_interface() {
    let p = prefix(1);
    let mk = |layer: Layer| GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer,
        ty: Rc::new(Type::Nat),
        level: Level::Zero,
        body: Some(Rc::new(Term::Zero)),
    };
    assert_ne!(
        interface_hash(&p, &mk(Layer::Code)),
        interface_hash(&p, &mk(Layer::Meta)),
        "a verdict earned at one layer must not vouch for a check at another"
    );
}

/// The two hash families are domain-separated: the same material fed as an
/// interface and as a check key must not collide.
#[test]
fn the_domains_do_not_meet() {
    let p = prefix(1);
    let b = GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: Rc::new(Type::Nat),
        level: Level::Zero,
        body: Some(Rc::new(Term::Zero)),
    };
    let iface = interface_hash(&p, &b).expect("hashable");
    let key = heather_cache::merkle::check_key(&p, &Term::Zero, false, &iface).expect("hashable");
    assert_ne!(iface, key);
}

// ---------------------------------------------------------------------------
// Framing: distinct structures, distinct hashes.
// ---------------------------------------------------------------------------

fn nat() -> Rc<Type> {
    Rc::new(Type::Nat)
}

fn zero() -> Rc<Term> {
    Rc::new(Term::Zero)
}

/// A `Branches` with every field the same term, so that changing one field is
/// the *only* difference between two of them.
fn uniform_branches(t: Rc<Term>) -> Branches {
    Branches {
        ty_nat: Rc::clone(&t),
        ty_pi: Rc::clone(&t),
        ty_ty: Rc::clone(&t),
        ty_el: Rc::clone(&t),
        ty_id: Rc::clone(&t),
        ty_sigma: Rc::clone(&t),
        ty_unit: Rc::clone(&t),
        ty_empty: Rc::clone(&t),
        tm_var: Rc::clone(&t),
        tm_nat: Rc::clone(&t),
        tm_pi: Rc::clone(&t),
        tm_ty: Rc::clone(&t),
        tm_zero: Rc::clone(&t),
        tm_succ: Rc::clone(&t),
        tm_elim_nat: Rc::clone(&t),
        tm_lam: Rc::clone(&t),
        tm_app: Rc::clone(&t),
        tm_id: Rc::clone(&t),
        tm_refl: Rc::clone(&t),
        tm_j: Rc::clone(&t),
        tm_sigma: Rc::clone(&t),
        tm_pair: Rc::clone(&t),
        tm_fst: Rc::clone(&t),
        tm_snd: Rc::clone(&t),
        tm_unit: Rc::clone(&t),
        tm_empty: Rc::clone(&t),
        tm_triv: Rc::clone(&t),
        tm_elim_empty: Rc::clone(&t),
        ty_sum: Rc::clone(&t),
        tm_sum: Rc::clone(&t),
        tm_inl: Rc::clone(&t),
        tm_inr: Rc::clone(&t),
        tm_case: Rc::clone(&t),
        ty_w: Rc::clone(&t),
        tm_w: Rc::clone(&t),
        tm_sup: Rc::clone(&t),
        tm_elim_w: Rc::clone(&t),
        ty_vec: Rc::clone(&t),
        tm_vec: Rc::clone(&t),
        ty_fin: Rc::clone(&t),
        tm_fin: Rc::clone(&t),
        ty_wf: Rc::clone(&t),
        tm_wf: Rc::clone(&t),
        tm_supf: Rc::clone(&t),
        tm_elim_wf: Rc::clone(&t),
        ty_seq: Rc::clone(&t),
        tm_seq: Rc::clone(&t),
        ty_sempty: Rc::clone(&t),
        tm_sempty: Rc::clone(&t),
        tm_srefl: Rc::clone(&t),
        tm_elim_sempty: t,
        ty_squash: zero(),
        tm_squash: zero(),
        tm_squash_in: zero(),
        tm_elim_squash: zero(),
        ty_m: zero(),
        tm_m: zero(),
        tm_corec: zero(),
        tm_out: zero(),
        ty_dvec: zero(),
        tm_dvec: zero(),
        ty_iwf: zero(),
        tm_iwf: zero(),
        tm_sup_i: zero(),
        tm_elim_iwf: zero(),
    }
}

fn code_recursor(b: Branches) -> Term {
    Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: Rc::new(Motives { ty_motive: nat(), tm_motive: nat() }),
        branches: Rc::new(b),
        code_level: Level::Zero,
        ctx: LocalCtx::nil(),
        scrut: zero(),
    }
}

/// **The finding this round paid for.** `heather_kernel::fmt`'s `Debug` for
/// `Branches` prints 37 of the struct's 52 fields, so under v1 two code
/// recursors differing only in one of the other fifteen — every `Vec`/`Fin`/
/// `Wf` branch and every strict-equality branch — had the *same cache
/// identity*. The walker now distinguishes all 60 (the historical 52 plus
/// the four squash branches and the four `M` branches).
///
/// This is the differential pin for the transition: it is a property the
/// scanner provably did not have, on the fields it did not have it for.
#[test]
fn every_recursor_branch_is_hashed() {
    let base = uniform_branches(zero());
    let p: Vec<Option<Hash>> = Vec::new();

    let base_hash = term_hash(&p, 0, &code_recursor(base)).expect("no references");

    // One field at a time, by name, so a failure says which branch is unhashed.
    type Mutation = (&'static str, Box<dyn Fn(&mut Branches)>);
    let mut mutate: Vec<Mutation> = Vec::new();
    macro_rules! field {
        ($($f:ident),* $(,)?) => {
            $(mutate.push((stringify!($f), Box::new(|b: &mut Branches| b.$f = Rc::new(Term::Succ(Rc::new(Term::Zero))))));)*
        };
    }
    field!(
        ty_nat,
        ty_pi,
        ty_ty,
        ty_el,
        ty_id,
        ty_sigma,
        ty_unit,
        ty_empty,
        tm_var,
        tm_nat,
        tm_pi,
        tm_ty,
        tm_zero,
        tm_succ,
        tm_elim_nat,
        tm_lam,
        tm_app,
        tm_id,
        tm_refl,
        tm_j,
        tm_sigma,
        tm_pair,
        tm_fst,
        tm_snd,
        tm_unit,
        tm_empty,
        tm_triv,
        tm_elim_empty,
        ty_sum,
        tm_sum,
        tm_inl,
        tm_inr,
        tm_case,
        ty_w,
        tm_w,
        tm_sup,
        tm_elim_w,
        ty_vec,
        tm_vec,
        ty_fin,
        tm_fin,
        ty_wf,
        tm_wf,
        tm_supf,
        tm_elim_wf,
        ty_seq,
        tm_seq,
        ty_sempty,
        tm_sempty,
        tm_srefl,
        tm_elim_sempty,
        ty_squash,
        tm_squash,
        tm_squash_in,
        tm_elim_squash,
        ty_m,
        tm_m,
        tm_corec,
        tm_out,
        ty_dvec,
        tm_dvec,
        ty_iwf,
        tm_iwf,
        tm_sup_i,
        tm_elim_iwf,
    );
    assert_eq!(mutate.len(), 65, "every branch field must be listed here");

    let mut seen = std::collections::BTreeSet::new();
    for (name, f) in &mutate {
        let mut b = uniform_branches(zero());
        f(&mut b);
        let h = term_hash(&p, 0, &code_recursor(b)).expect("no references");
        assert_ne!(h, base_hash, "branch `{name}` does not reach the hash");
        assert!(seen.insert(h), "branch `{name}` hashes the same as an earlier branch");
    }
}

/// Framing: a corpus of structurally distinct values, pairwise distinct
/// hashes. The shapes chosen are the ones an unframed or under-tagged encoding
/// conflates — sequences of different lengths that concatenate alike, adjacent
/// fields of the same sort swapped, and the leaf constructors that carry no
/// payload at all.
#[test]
fn distinct_structures_hash_distinctly() {
    let p = prefix(2);
    let l0 = Level::Zero;
    let l1 = Level::succ(Level::Zero);
    let lv = Level::Var(UnivVar(0));

    let subst_with = |terms: Vec<Rc<Term>>| LocalSubst {
        tail: SubstTail::Empty,
        terms,
    };
    let ctx_with = |entries: Vec<CtxEntry>| LocalCtx::from_vec(CtxBase::Nil, entries);
    let entry = |ty: Rc<Type>| CtxEntry { ty, level: Level::Zero };

    let corpus: Vec<(&str, Term)> = vec![
        // Nullary leaves: only the tag distinguishes these.
        ("Zero", Term::Zero),
        ("TmNat", Term::TmNat),
        ("Triv 0", Term::Triv { level: l0.clone() }),
        ("Triv 1", Term::Triv { level: l1.clone() }),
        ("Triv ℓ0", Term::Triv { level: lv.clone() }),
        // Two levels in a row, swapped: the second field must not be
        // absorbable into the first.
        (
            "Pi[0,1]",
            Term::Lam {
                dom_level: l0.clone(),
                cod_level: l1.clone(),
                dom: nat(),
                body: zero(),
            },
        ),
        (
            "Pi[1,0]",
            Term::Lam {
                dom_level: l1.clone(),
                cod_level: l0.clone(),
                dom: nat(),
                body: zero(),
            },
        ),
        // Sequence lengths: `[]`, `[a]`, `[a, a]` under one tag.
        ("UApp []", Term::UApp { fun: zero(), levels: vec![] }),
        ("UApp [0]", Term::UApp { fun: zero(), levels: vec![l0.clone()] }),
        ("UApp [0,0]", Term::UApp { fun: zero(), levels: vec![l0.clone(), l0.clone()] }),
        ("UApp [1]", Term::UApp { fun: zero(), levels: vec![l1.clone()] }),
        // Substitution term lists, same question one sort down.
        ("c0^{}", global_tm(0)),
        ("c1^{}", global_tm(1)),
        ("u1^{}", Term::GlobalTm { var: GlobalVar::index(1), subst: subst_with(vec![]) }),
        ("u0^{}", Term::GlobalTm { var: GlobalVar::index(0), subst: subst_with(vec![]) }),
        ("u0^{0}", Term::GlobalTm { var: GlobalVar::index(0), subst: subst_with(vec![zero()]) }),
        (
            "u0^{0;0}",
            Term::GlobalTm { var: GlobalVar::index(0), subst: subst_with(vec![zero(), zero()]) },
        ),
        // Context entry counts.
        ("capp ()", Term::CtxApp { fun: zero(), ctx: ctx_with(vec![]) }),
        ("capp (Nat)", Term::CtxApp { fun: zero(), ctx: ctx_with(vec![entry(nat())]) }),
        (
            "capp (Nat, Nat)",
            Term::CtxApp { fun: zero(), ctx: ctx_with(vec![entry(nat()), entry(nat())]) },
        ),
        // Substitution tails: the weakening, over the same numbers (the
        // empty tail is `u0^{}` above, and records nothing more).
        (
            "tail wk^0_g1",
            Term::GlobalTm {
                var: GlobalVar::index(0),
                subst: LocalSubst {
                    tail: SubstTail::Wk { len: 0, ctx_var: GlobalVar::index(1) },
                    terms: vec![],
                },
            },
        ),
        (
            "tail wk^1_g1",
            Term::GlobalTm {
                var: GlobalVar::index(0),
                subst: LocalSubst {
                    tail: SubstTail::Wk { len: 1, ctx_var: GlobalVar::index(1) },
                    terms: vec![],
                },
            },
        ),
        // Term-level vs type-level encodings of the same former.
        ("box(Ty)", Term::BoxTy(Rc::new(Type::Ty(l0.clone())))),
        ("box(«Ty»)", Term::BoxTm(Rc::new(Term::TmTy(l0.clone())))),
        // Adjacent same-sort fields swapped, in a term that carries four.
        (
            "Fst(Nat. Ty0)",
            Term::Fst {
                fst_level: l0.clone(),
                snd_level: l1.clone(),
                fst_ty: nat(),
                snd_ty: Rc::new(Type::Ty(l0.clone())),
                pair: zero(),
            },
        ),
        (
            "Snd(Nat. Ty0)",
            Term::Snd {
                fst_level: l0.clone(),
                snd_level: l1.clone(),
                fst_ty: nat(),
                snd_ty: Rc::new(Type::Ty(l0.clone())),
                pair: zero(),
            },
        ),
        (
            "Fst(Ty0. Nat)",
            Term::Fst {
                fst_level: l0.clone(),
                snd_level: l1.clone(),
                fst_ty: Rc::new(Type::Ty(l0.clone())),
                snd_ty: nat(),
                pair: zero(),
            },
        ),
        // Local variable indices.
        ("x0", Term::Var(LocalVar(0))),
        ("x1", Term::Var(LocalVar(1))),
        // A deep nest vs a shallow one built from the same pieces.
        ("S(S 0)", Term::Succ(Rc::new(Term::Succ(zero())))),
        ("S 0", Term::Succ(zero())),
    ];

    let mut seen: std::collections::BTreeMap<Hash, &str> = std::collections::BTreeMap::new();
    for (what, t) in &corpus {
        let h = term_hash(&p, 2, t).unwrap_or_else(|| panic!("{what}: unhashable"));
        if let Some(other) = seen.insert(h, what) {
            panic!("framing collision: `{what}` and `{other}` hash the same");
        }
    }
}

/// The walk is a function: the same structure hashes the same twice, and
/// sharing does not change the answer (an `Rc` reached twice is two nodes).
#[test]
fn the_walk_is_a_function_of_the_tree_not_of_its_sharing() {
    let p = prefix(1);
    let shared = Rc::new(Term::Succ(Rc::new(Term::Zero)));
    let with_sharing = Term::TmSigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: Rc::clone(&shared),
        snd: Rc::clone(&shared),
    };
    let without = Term::TmSigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: Rc::new(Term::Succ(Rc::new(Term::Zero))),
        snd: Rc::new(Term::Succ(Rc::new(Term::Zero))),
    };
    let a = term_hash(&p, 1, &with_sharing);
    assert_eq!(a, term_hash(&p, 1, &with_sharing), "not deterministic");
    assert_eq!(a, term_hash(&p, 1, &without), "sharing leaked into the hash");
}

/// `σ(x, x)` nested `depth` times over `0`, each level's two children one
/// shared node (`shared`) or two separately built trees.
fn doubling(depth: u32, shared: bool) -> Rc<Term> {
    let mut t = Rc::new(Term::Zero);
    for _ in 0..depth {
        let (fst, snd) = if shared { (Rc::clone(&t), Rc::clone(&t)) } else { (Rc::new((*t).clone()), deep_copy(&t)) };
        t = Rc::new(Term::TmSigma { fst_level: Level::Zero, snd_level: Level::Zero, fst, snd });
    }
    t
}

/// The same tree with no node shared.
fn deep_copy(t: &Term) -> Rc<Term> {
    Rc::new(match t {
        Term::TmSigma { fst_level, snd_level, fst, snd } => Term::TmSigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: deep_copy(fst),
            snd: deep_copy(snd),
        },
        other => other.clone(),
    })
}

/// Large nodes are hashed as digests, and a node shared in memory is walked
/// once (`issues/image-tree-walks-let-shared-terms.md`): a term whose tree
/// has 2⁶⁴ leaves hashes, and whether a node is a digest is decided by its
/// content, so a tree built with no sharing at all hashes as the shared one
/// does, past the digest threshold as below it.
#[test]
fn a_shared_term_is_walked_once_and_hashes_as_its_tree() {
    let p = prefix(1);
    assert!(term_hash(&p, 1, &doubling(64, true)).is_some());
    for depth in [3, 6, 9, 12] {
        let shared = term_hash(&p, 1, &doubling(depth, true));
        assert_eq!(shared, term_hash(&p, 1, &doubling(depth, false)), "sharing leaked into the hash at depth {depth}");
        assert_ne!(shared, term_hash(&p, 1, &doubling(depth + 1, true)));
    }
}
