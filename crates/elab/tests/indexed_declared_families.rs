//! Acceptance for indexed families at a **declared** index type — the
//! generator for §8.2 of `docs/inductive-indexed-lowering.md`, end to end from
//! the surface. The hand prototype behind it is `indexed_declared_index.rs`,
//! whose kernel terms these declarations lower to.
//!
//! Its own file rather than an extension of `indexed_families.rs` for the same
//! reason the prototype has one: every declaration here needs an *index
//! declaration* above it, and the three index shapes — flat, linear `Wf`,
//! branching `Wf` — are what the section is about, where `indexed_families.rs`
//! is the `Nat` round's record and stays that.
//!
//! The four axes of `docs/testing-generated-terms.md` throughout: a literal
//! *and* a neutral index (a variable `s: Shape` is the neutral case here, and
//! it is the one the family cannot reduce under), an **open** element type
//! (the polymorphic families below are lowered at a type variable), checking
//! position (every `theorem` is one), and a negative control per positive.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

const ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
"#;

// ---------------------------------------------------------------------------
// Part A — a flat (enum) declared index. The family is one `Case` tree at
// motive `Ty l`; no branch has a `rec`, because an enum constructor has no
// recursive argument to draw one from.
// ---------------------------------------------------------------------------

const PAR: &str = r#"
inductive Par { PE, PO }
inductive AB<A> : (p: Par) -> Type {
    A2(x: A, y: A) : AB<A>(PE),
    B0            : AB<A>(PO),
}
"#;

#[test]
fn enum_index_declares_constructors_and_matches() {
    elab(&format!(
        "{PAR}{ADD}
         fn mk() -> AB<Nat>(PE) {{ A2(1, 2) }}
         fn mko() -> AB<Nat>(PO) {{ B0 }}
         // Open element type: the family is lowered at the type variable `A`.
         fn pmk<A>(x: A, y: A) -> AB<A>(PE) {{ A2(x, y) }}
         fn pmko<A>() -> AB<A>(PO) {{ B0 }}
         // A literal index: the `Case` on `PE` reduces and the arm is reached.
         fn fst(d: AB<Nat>(PE), z: Nat) -> Nat {{ match d {{ A2(x, y) => x, B0 => z }} }}
         // A *neutral* index: `p` is a variable, so the family is stuck and
         // the eliminator is the whole `Case` — the same arms, unreduced.
         fn either(p: Par, d: AB<Nat>(p), z: Nat) -> Nat {{
             match d {{ A2(x, y) => add(x, y), B0 => z }}
         }}
         theorem fst_open(x: Nat, y: Nat, z: Nat): fst(A2(x, y), z) = x {{ refl }}
         theorem either_e(x: Nat, y: Nat, z: Nat): either(PE, A2(x, y), z) = add(x, y) {{ refl }}
         theorem either_o(z: Nat): either(PO, B0, z) = z {{ refl }}"
    ));
}

// A pattern variable at a **payload** argument of the index constructor: it is
// not `nth` of anything (there are no children), it is a projection of the
// index constructor's own label, and the arm recovers it by that projection.
const COL: &str = r#"
inductive Col { CZ, CS(n: Nat) }
inductive Tg : (c: Col) -> Type {
    TZ            : Tg(CZ),
    TS(n: Nat, x: Nat) : Tg(CS(n)),
}
"#;

#[test]
fn enum_index_recovers_a_payload_pattern_variable() {
    elab(&format!(
        "{COL}{ADD}
         fn subj(c: Col, t: Tg(c)) -> Nat {{ match t {{ TZ => 0, TS(n, x) => n }} }}
         fn load(c: Col, t: Tg(c)) -> Nat {{ match t {{ TZ => 0, TS(n, x) => x }} }}
         theorem subj_closed(): subj(CS(3), TS(3, 7)) = 3 {{ refl }}
         theorem load_closed(): load(CS(3), TS(3, 7)) = 7 {{ refl }}
         // Open subject *and* open payload, at a neutral index.
         theorem subj_open(n: Nat, x: Nat): subj(CS(n), TS(n, x)) = n {{ refl }}
         theorem load_open(n: Nat, x: Nat): load(CS(n), TS(n, x)) = x {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// Part B — a linear recursive declared index: `MN` is a declared `Nat`-clone,
// lowered onto `Wf` exactly as tier 1 declares it, and the family is `elim_Wf`
// at motive `Ty l` with the recursive field's code drawn from the threaded ih
// at a literal `Fin` index.
// ---------------------------------------------------------------------------

const MNAT: &str = r#"
inductive MN { MZ, MS(p: MN) }
inductive VF<A> : (n: MN) -> Type {
    VFNil                                : VF<A>(MZ),
    VFCons(n: MN, x: A, xs: VF<A>(n))     : VF<A>(MS(n)),
}
"#;

#[test]
fn wf_index_declares_and_constructors_check() {
    elab(&format!(
        "{MNAT}
         fn nil0() -> VF<Nat>(MZ) {{ VFNil }}
         fn two() -> VF<Nat>(MS(MS(MZ))) {{ VFCons(MS(MZ), 4, VFCons(MZ, 5, VFNil)) }}
         // Everything open: element type, index, element and tail. `famVF (MS n)`
         // unfolds whatever `n` is, because `MS(n)` is `sup_f`-headed.
         fn push<A>(n: MN, x: A, xs: VF<A>(n)) -> VF<A>(MS(n)) {{ VFCons(n, x, xs) }}"
    ));
}

#[test]
fn wf_index_beta_and_pattern_variable_recovery() {
    elab(&format!(
        "{MNAT}
         fn lenf(n: MN, xs: VF<Nat>(n)) -> Nat {{
             match xs {{ VFNil => 0, VFCons(k, x, t) => Succ(lenf(k, t)) }}
         }}
         // The arm binds `k` and receives `nth(cs'; fz)` — the projection out
         // of `MS`'s children, with no inversion machinery (§8.2 fact 3).
         fn peekf(n: MN, xs: VF<Nat>(n)) -> MN {{
             match xs {{ VFNil => MZ, VFCons(k, x, t) => k }}
         }}
         fn two() -> VF<Nat>(MS(MS(MZ))) {{ VFCons(MS(MZ), 4, VFCons(MZ, 5, VFNil)) }}
         theorem len_closed(): lenf(MS(MS(MZ)), two()) = 2 {{ refl }}
         theorem len_open(n: MN, x: Nat, xs: VF<Nat>(n)):
             lenf(MS(n), VFCons(n, x, xs)) = Succ(lenf(n, xs)) {{ refl }}
         theorem peek_open(n: MN, x: Nat, xs: VF<Nat>(n)):
             peekf(MS(n), VFCons(n, x, xs)) = n {{ refl }}"
    ));
}

#[test]
fn wf_index_append_and_definitional_index_arithmetic() {
    elab(&format!(
        "{MNAT}
         fn madd(a: MN, b: MN) -> MN {{ match b {{ MZ => a, MS(k) => MS(madd(a, k)) }} }}
         // The `VFCons` arm owes `VF(madd(m, MS k))` and pays
         // `VF(MS(madd(m, k)))`: definitional, through the *declared* index's
         // own `elim_Wf` β.
         fn appf(n: MN, m: MN, xs: VF<Nat>(n), ys: VF<Nat>(m)) -> VF<Nat>(madd(m, n)) {{
             match xs {{
                 VFNil => ys,
                 VFCons(k, x, t) => VFCons(madd(m, k), x, appf(k, m, t, ys)),
             }}
         }}
         theorem app_closed():
             appf(MS(MZ), MS(MZ), VFCons(MZ, 1, VFNil), VFCons(MZ, 2, VFNil))
                 = VFCons(MS(MZ), 1, VFCons(MZ, 2, VFNil)) {{ refl }}
         theorem app_open(n: MN, m: MN, x: Nat, xs: VF<Nat>(n), ys: VF<Nat>(m)):
             appf(MS(n), m, VFCons(n, x, xs), ys)
                 = VFCons(madd(m, n), x, appf(n, m, xs, ys)) {{ refl }}"
    ));
}

#[test]
fn wf_index_induction_over_a_declared_index() {
    elab(&format!(
        "{MNAT}
         fn cmapf(n: MN, xs: VF<Nat>(n)) -> VF<Nat>(n) {{
             match xs {{ VFNil => VFNil, VFCons(k, x, t) => VFCons(k, x, cmapf(k, t)) }}
         }}
         theorem cmapf_id(n: MN, xs: VF<Nat>(n)): cmapf(n, xs) = xs {{
             match xs {{
                 VFNil => refl,
                 VFCons(k, x, t) => j(cmapf_id(k, t),
                     \u{3bb} y q => VFCons(k, x, cmapf(k, t)) = VFCons(k, x, y),
                     refl),
             }}
         }}"
    ));
}

// ---------------------------------------------------------------------------
// Part C — a branching recursive declared index: the subject-recursive
// judgment in miniature. `SNode(l, r)` has two recursive arguments, `BNode`
// has one derivation at each, and both value ihs come from the *same* threaded
// `ih` at two `Fin` literals (§8.2 fact 4).
// ---------------------------------------------------------------------------

const SHAPE: &str = r#"
inductive Shape { SLeaf, SNode(l: Shape, r: Shape) }
inductive Bal : (s: Shape) -> Type {
    BLeaf : Bal(SLeaf),
    BNode(l: Shape, r: Shape, dl: Bal(l), dr: Bal(r)) : Bal(SNode(l, r)),
}
"#;

#[test]
fn branching_index_declares_and_both_ihs_engage() {
    elab(&format!(
        "{SHAPE}{ADD}
         fn count(s: Shape, d: Bal(s)) -> Nat {{
             match d {{ BLeaf => 1, BNode(l, r, dl, dr) => add(count(l, dl), count(r, dr)) }}
         }}
         fn two() -> Bal(SNode(SLeaf, SLeaf)) {{ BNode(SLeaf, SLeaf, BLeaf, BLeaf) }}
         theorem count_closed(): count(SNode(SLeaf, SLeaf), two()) = 2 {{ refl }}
         // β through a *branching* index constructor with the subjects and
         // both derivations open, and both ihs synthesized.
         theorem count_open(l: Shape, r: Shape, dl: Bal(l), dr: Bal(r)):
             count(SNode(l, r), BNode(l, r, dl, dr)) = add(count(l, dl), count(r, dr))
             {{ refl }}
         theorem count_leaf(): count(SLeaf, BLeaf) = 1 {{ refl }}"
    ));
}

#[test]
fn branching_index_induction() {
    elab(&format!(
        "{SHAPE}
         fn bmap(s: Shape, d: Bal(s)) -> Bal(s) {{
             match d {{
                 BLeaf => BLeaf,
                 BNode(l, r, dl, dr) => BNode(l, r, bmap(l, dl), bmap(r, dr)),
             }}
         }}
         theorem bmap_id(s: Shape, d: Bal(s)): bmap(s, d) = d {{
             match d {{
                 BLeaf => refl,
                 BNode(l, r, dl, dr) => j(bmap_id(r, dr),
                     \u{3bb} y q => BNode(l, r, bmap(l, dl), bmap(r, dr)) = BNode(l, r, dl, y),
                     j(bmap_id(l, dl),
                       \u{3bb} y q => BNode(l, r, bmap(l, dl), bmap(r, dr))
                                    = BNode(l, r, y, bmap(r, dr)),
                       refl)),
             }}
         }}"
    ));
}

// A **payload** field whose type mentions a *recursive* pattern variable:
// `w: Bal(l)` with `l = nth(cs'; ι₀)`. This is what the family's `cs` thread
// is for — §8.2 item 1 says the family needs only `ih` threaded, which is true
// only while no payload field names a child of the index constructor.
#[test]
fn a_payload_field_at_a_recursive_pattern_variable() {
    elab(&format!(
        "{SHAPE}{ADD}
         inductive Tw : (s: Shape) -> Type {{
             TL                                          : Tw(SLeaf),
             TN(l: Shape, r: Shape, w: Bal(l), t: Tw(r)) : Tw(SNode(l, r)),
         }}
         fn count(s: Shape, d: Bal(s)) -> Nat {{
             match d {{ BLeaf => 1, BNode(l, r, dl, dr) => add(count(l, dl), count(r, dr)) }}
         }}
         fn weight(s: Shape, t: Tw(s)) -> Nat {{
             match t {{ TL => 0, TN(l, r, w, u) => add(count(l, w), weight(r, u)) }}
         }}
         theorem weight_open(l: Shape, r: Shape, w: Bal(l), u: Tw(r)):
             weight(SNode(l, r), TN(l, r, w, u)) = add(count(l, w), weight(r, u)) {{ refl }}"
    ));
}

// The `Fin` shape at a declared index: an index constructor with **no**
// declaration constructors is an empty class, and its branch is `Empty` — so
// `Bal2(SLeaf)` is uninhabited definitionally and a no-arm `match` eliminates
// it. Also §6.1's explicit two-binder motive, whose index binder is now a
// `Shape` and not a `Nat`.
#[test]
fn empty_class_and_an_explicit_motive() {
    elab(&format!(
        "{SHAPE}
         inductive B2 : (s: Shape) -> Type {{
             B2N(l: Shape, r: Shape, dl: B2(l)) : B2(SNode(l, r)),
         }}
         fn from_empty(p: B2(SLeaf)) -> Nat {{ match p {{ }} }}
         fn depth(s: Shape, d: B2(s)) -> Nat {{
             match d as \u{3bb} h z => Nat {{ B2N(l, r, dl) => Succ(depth(l, dl)) }}
         }}
         theorem depth_open(l: Shape, r: Shape, dl: B2(l)):
             depth(SNode(l, r), B2N(l, r, dl)) = Succ(depth(l, dl)) {{ refl }}"
    ));
}

// §10.5: everything above lives at level 0, where `l ⊔ mlvl = mlvl` hides a
// dropped join. A `Type`-valued field puts the family at level 1 with the
// motive at 0, so the two-pass level computation and the eliminator's
// `l ≠ mlvl` plumbing both do real work — over a *branching declared* index,
// which is where the level flows through `elim_Wf`'s motive as well.
#[test]
fn fields_above_level_zero_at_a_declared_index() {
    elab(&format!(
        "{SHAPE}{ADD}
         inductive PT : (s: Shape) -> Type {{
             PL(A: Type)                                                  : PT(SLeaf),
             PN(l: Shape, r: Shape, A: Type, x: A, a: PT(l), b: PT(r))    : PT(SNode(l, r)),
         }}
         fn psize(s: Shape, p: PT(s)) -> Nat {{
             match p {{ PL(A) => 1, PN(l, r, A, x, a, b) => add(psize(l, a), psize(r, b)) }}
         }}
         theorem psize_closed():
             psize(SNode(SLeaf, SLeaf), PN(SLeaf, SLeaf, Nat, 3, PL(Nat), PL(Nat))) = 2
             {{ refl }}
         theorem psize_open(l: Shape, r: Shape, x: Nat, a: PT(l), b: PT(r)):
             psize(SNode(l, r), PN(l, r, Nat, x, a, b)) = add(psize(l, a), psize(r, b))
             {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// Negatives. Each positive above has one here; a rejection is load-bearing
// because everything on this list is lowerable in principle by fording, and
// silently mis-lowering it into the index-recursive scheme is the hazard class.
// ---------------------------------------------------------------------------

#[test]
fn wrong_indices_are_rejected() {
    // A successor-class value at the base index, and the reverse.
    elab_err(&format!("{MNAT} fn bad() -> VF<Nat>(MZ) {{ VFCons(MZ, 1, VFNil) }}"));
    elab_err(&format!("{MNAT} fn bad(n: MN) -> VF<Nat>(MS(n)) {{ VFNil }}"));
    // The written index disagrees with the expected one.
    elab_err(&format!(
        "{MNAT} fn bad(n: MN, x: Nat, xs: VF<Nat>(n)) -> VF<Nat>(n) {{ VFCons(n, x, xs) }}"
    ));
    // A tail at the wrong index.
    elab_err(&format!(
        "{MNAT} fn bad(n: MN, m: MN, x: Nat, xs: VF<Nat>(n)) -> VF<Nat>(MS(m)) {{
             VFCons(m, x, xs)
         }}"
    ));
    // A derivation stored under the *wrong* pattern variable: `dr` where `dl`
    // belongs, at two distinct open subjects.
    elab_err(&format!(
        "{SHAPE} fn bad(l: Shape, r: Shape, dl: Bal(l), dr: Bal(r)) -> Bal(SNode(l, r)) {{
             BNode(l, r, dr, dl)
         }}"
    ));
    // `BLeaf` at a node index, and `BNode` at the leaf index.
    elab_err(&format!(
        "{SHAPE} fn bad(l: Shape, r: Shape) -> Bal(SNode(l, r)) {{ BLeaf }}"
    ));
    elab_err(&format!(
        "{SHAPE} fn bad(l: Shape, r: Shape, dl: Bal(l), dr: Bal(r)) -> Bal(SLeaf) {{
             BNode(l, r, dl, dr)
         }}"
    ));
    // A value at the wrong index in *checking* position: `fst` takes the
    // `PE`-class family, so the `PO`-class constructor has nowhere to go.
    elab_err(&format!(
        "{PAR} fn fst(d: AB<Nat>(PE), z: Nat) -> Nat {{ match d {{ A2(x, y) => x, B0 => z }} }}
         theorem bad(z: Nat): fst(B0, z) = z {{ refl }}"
    ));
    // A `refl` does not prove an induction: the map is neutral on an open
    // scrutinee at a declared index too.
    elab_err(&format!(
        "{SHAPE}
         fn bmap(s: Shape, d: Bal(s)) -> Bal(s) {{
             match d {{ BLeaf => BLeaf, BNode(l, r, dl, dr) => BNode(l, r, bmap(l, dl), bmap(r, dr)) }}
         }}
         theorem bad(s: Shape, d: Bal(s)): bmap(s, d) = d {{ refl }}"
    ));
}

// §7 at a declared index: constructors in different index classes have no
// common type, so their equation fails to *state* rather than failing to prove.
#[test]
fn cross_class_equations_fail_to_state() {
    elab_err(&format!(
        "{MNAT} theorem bad(n: MN, x: Nat, xs: VF<Nat>(n)): VFNil = VFCons(n, x, xs) {{ refl }}"
    ));
    elab_err(&format!(
        "{SHAPE} theorem bad(l: Shape, r: Shape, dl: Bal(l), dr: Bal(r)):
             BLeaf = BNode(l, r, dl, dr) {{ refl }}"
    ));
}

#[test]
fn declaration_rejections_carry_their_messages() {
    // §8.2's classification consequence: at a flat index there is no recursive
    // argument, so no `rec` exists for a recursive field to read — and the
    // message says that by shape rather than by policy.
    let m = elab_err(
        "inductive Col { CZ, CS(n: Nat) }
         inductive Bad : (c: Col) -> Type {
             B0                        : Bad(CZ),
             B1(n: Nat, d: Bad(n))     : Bad(CS(n)),
         }",
    );
    assert!(m.contains("no recursive argument"), "{m}");
    // A recursive field away from any pattern variable.
    let m = elab_err(&format!(
        "inductive Sh2 {{ L2, N2(a: Sh2, b: Sh2) }}
         inductive Bad : (s: Sh2) -> Type {{
             D0                                       : Bad(L2),
             D1(l: Sh2, r: Sh2, d: Bad(L2))           : Bad(N2(l, r)),
         }}{ADD}"
    ));
    assert!(m.contains("pattern variable"), "{m}");
    // Non-linear pattern: one field filling two arguments.
    // A *non-linear* result index is no longer a rejection: route 1 still
    // declines it (its pattern must be linear), but route 2b generates it —
    // one child at `l`, and `μ` recomputes `N2(μ d, μ d)` faithfully, which is
    // §3.2's F1–F4 with nothing left to check
    // (docs/inductive-fording-lowering.md §3.4). What route 2b *does* reject is
    // two children sharing one index variable (F2), and that has its own
    // observer in `indexed_route_2b_gen.rs`.
    elab(
        "inductive Sh2 { L2, N2(a: Sh2, b: Sh2) }
         inductive Bad : (s: Sh2) -> Type {
             D0                   : Bad(L2),
             D1(l: Sh2, d: Bad(l)) : Bad(N2(l, l)),
         }",
    );
    // Deeper than one constructor: route 1 still declines it, but this is
    // exactly §3.4's "deep pattern" row — route 2b generates it with no special
    // case at all (`μ(d1 r) = N2(L2, μ… )`), so the declaration now lands
    // rather than rejecting (docs/inductive-fording-lowering.md §3.4, §15.4).
    elab(
        "inductive Sh2 { L2, N2(a: Sh2, b: Sh2) }
         inductive Bad : (s: Sh2) -> Type {
             D0                   : Bad(L2),
             D1(r: Sh2)           : Bad(N2(L2, r)),
         }",
    );
    // The index constructor at the wrong arity.
    let m = elab_err(
        "inductive Sh2 { L2, N2(a: Sh2, b: Sh2) }
         inductive Bad : (s: Sh2) -> Type {
             D0                   : Bad(L2),
             D1(l: Sh2)           : Bad(N2(l)),
         }",
    );
    assert!(m.contains("argument"), "{m}");
    // A pattern variable at a recursive argument must be a field of the index
    // type, not of some other one.
    let m = elab_err(
        "inductive Sh2 { L2, N2(a: Sh2, b: Sh2) }
         inductive Bad : (s: Sh2) -> Type {
             D0                        : Bad(L2),
             D1(l: Nat, r: Sh2)        : Bad(N2(l, r)),
         }",
    );
    assert!(m.contains("must be a `Sh2` field"), "{m}");
    // Index-type shapes the scheme has no branch for.
    let m = elab_err("inductive Bad : (x: Unknown) -> Type { D0 : Bad(x) }");
    assert!(m.contains("unknown index type"), "{m}");
    let m = elab_err(
        "inductive Box<A> { Mk(a: A), Mk2(a: A) }
         inductive Bad : (b: Box) -> Type { D0 : Bad(x) }",
    );
    assert!(m.contains("parameters"), "{m}");
    let m = elab_err(
        "inductive One { Only }
         inductive Bad : (o: One) -> Type { D0 : Bad(Only) }",
    );
    assert!(m.contains("fewer than two constructors"), "{m}");
    let m = elab_err(&format!(
        "{MNAT}
         inductive Bad : (v: VF) -> Type {{ D0 : Bad(v) }}"
    ));
    assert!(m.contains("parameters"), "{m}");
    // An indexed family used without its index is still the old message.
    let m = elab_err(&format!("{MNAT} fn bad(x: VF<Nat>) -> Nat {{ 0 }}"));
    assert!(m.contains("needs its index"), "{m}");
}
