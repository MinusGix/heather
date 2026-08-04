//! Acceptance for **form A at a declared index** — route 2b's index inversion
//! carried by the index type's own eliminator
//! (`docs/inductive-fording-lowering.md` §8.2, the seam §14.4 recorded and this
//! file closes; the hand composition of the two ingredients is
//! `crates/elab/src/forded.rs`'s `decl_inversion` module).
//!
//! Its own file rather than a section of `indexed_route_2b_gen.rs`, for the
//! reason `indexed_declared_families.rs` gives: every declaration here needs an
//! *index declaration* above it, and the three index shapes — flat, linear
//! `Wf`, branching `Wf` — are what the section is about.
//!
//! Until 2026-08-04 every constructor of a declared-index forded family took
//! form B, so §8.4's aggregate limit applied to all of them: **no induction
//! over open data at all**. What each test below carries is which axis of
//! `docs/testing-generated-terms.md` makes it falsifiable:
//!
//! - **axis 1** — a *literal* scrutinee asserted to compute, not merely type;
//! - **axis 2** — a *neutral* scrutinee, open children and an open index;
//! - **axis 3** — a **checking** position: every claim is a `theorem`, which
//!   is a checking position across the index equation;
//! - **axis 4** — a negative control per decision, including the two the round
//!   *measured* rather than assumed (form B still stalls; a branching form A at
//!   a three-constructor index exceeds the conversion budget);
//! - **axis 6** — a **three-constructor** index type crossed with an open
//!   payload, which is what an inversion emitted branch-by-branch gets wrong:
//!   with two constructors there is no inner `Case` at all.
//!
//! Every declaration here is genuinely route 2b and not route 1, and each one
//! says why in a comment: route 1 rejects a deep pattern, a non-linear one and
//! a bare-variable index, so a declaration carrying one of those *and* still
//! elaborating has gone through the fording generator.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
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
// A **three-constructor** recursive index (axis 6). `TB`'s result index
// `SBud(s)` is `I_k(x̄)` at distinct child-index variables, so it takes form A;
// `TX`'s `SNode(l, SBud(r))` is two constructors deep, so it takes form B —
// and that is also what fords the declaration, since route 1 rejects a deep
// pattern.
// ---------------------------------------------------------------------------

const TW: &str = r#"
inductive Shape { SLeaf, SBud(s: Shape), SNode(l: Shape, r: Shape) }
inductive Tw : (s: Shape) -> Type {
    TL                                              : Tw(SLeaf),
    TB(s: Shape, x: Nat, t: Tw(s))                  : Tw(SBud(s)),
    TX(l: Shape, r: Shape)                          : Tw(SNode(l, SBud(r))),
}
fn tsize(s: Shape, t: Tw(s)) -> Nat {
    match t { TL => 0, TB(k, x, u) => Succ(tsize(k, u)), TX(a, b) => 0 }
}
fn tsize2(s: Shape, t: Tw(s)) -> Nat {
    match t { TL => 0, TB(k, x, u) => add(tsize2(k, u), 1), TX(a, b) => 0 }
}
"#;

#[test]
fn form_a_at_a_declared_index_is_definitional_on_open_data() {
    // §8.2's rule at a declared index, which is the whole round: `TB` would
    // have been route-1-eligible on its own, so its arm inverts the *motive's*
    // index by `elim_Shape` and consults the stored proof nowhere — and β fires
    // with the payload, the subtree and the index all open (axis 2).
    //
    // The `j ≠ k` branches are exercised by construction: each of them
    // transports the stored equation through the tag predicate into `Empty`,
    // and all three are kernel-checked when `tsize` is declared. A wrong tag
    // predicate (or one at the wrong constructor) is a rejection there, which
    // is why every test in this file elaborates `tsize` before claiming
    // anything about it.
    elab(&format!(
        "{ADD}{TW}
         fn leaf() -> Tw(SLeaf) {{ TL }}
         fn one() -> Tw(SBud(SLeaf)) {{ TB(SLeaf, 7, TL) }}
         // Axis 1: a literal scrutinee that computes.
         theorem lit(): tsize(SBud(SLeaf), one()) = 1 {{ refl }}
         theorem leaf_beta(): tsize(SLeaf, TL) = 0 {{ refl }}
         // Axis 2 + 3: open everything, in checking position.
         theorem open_beta(s: Shape, x: Nat, t: Tw(s)):
             tsize(SBud(s), TB(s, x, t)) = Succ(tsize(s, t)) {{ refl }}
         // …and the form-B constructor of the same declaration still types and
         // still computes on literal data.
         fn x0(l: Shape, r: Shape) -> Tw(SNode(l, SBud(r))) {{ TX(l, r) }}
         theorem x_beta(l: Shape, r: Shape):
             tsize(SNode(l, SBud(r)), TX(l, r)) = 0 {{ refl }}"
    ));
}

#[test]
fn an_induction_whose_step_is_a_form_a_constructor_closes() {
    // §8.4's limit, shrunk. Before this round every constructor of a
    // declared-index forded family was form B, so the goal at every arm was a
    // stuck `App(transp …)` on *both* sides of the step's equation and there
    // was no proof to write. The `TB` step now has definitional β, so the `j`
    // closes — the same payout §8.2's rule has at `Nat`.
    elab(&format!(
        "{ADD}{TW}
         theorem agree(s: Shape, t: Tw(s)): tsize(s, t) = tsize2(s, t) {{
             match t {{
                 TL => refl,
                 TB(k, x, u) => j(agree(k, u),
                     \u{3bb} y q => Succ(tsize(k, u)) = Succ(y),
                     refl),
                 TX(a, b) => refl,
             }}
         }}"
    ));
}

// The contrast, kept in the same shape so the two cannot drift: the *same*
// index type and the same form-A constructor, with the form-B constructor
// given a child. §8.4's third bullet then applies to that constructor and to
// no other — a forded constructor over an open child carries a non-`srefl`
// proof, the arm's `transp` does not β, and the residue is a stuck
// `App(transp …)` the head-only strip never reaches.
const TWC: &str = r#"
inductive Shape { SLeaf, SBud(s: Shape), SNode(l: Shape, r: Shape) }
inductive Tw : (s: Shape) -> Type {
    TL                                              : Tw(SLeaf),
    TB(s: Shape, x: Nat, t: Tw(s))                  : Tw(SBud(s)),
    TX(l: Shape, r: Shape, u: Tw(l))                : Tw(SNode(l, SBud(r))),
}
fn tsize(s: Shape, t: Tw(s)) -> Nat {
    match t { TL => 0, TB(k, x, u) => Succ(tsize(k, u)), TX(a, b, w) => Succ(tsize(a, w)) }
}
"#;

#[test]
fn the_form_b_contrast_in_the_same_family_still_stalls() {
    // Axis 4, a *deliberate* negative: the documented residue is in a test
    // rather than in a bug report, and it is the boundary of what this round
    // moved — form A at a declared index, not form B.
    let m = elab_err(&format!(
        "{ADD}{TWC}
         fn mk(l: Shape, r: Shape, u: Tw(l)) -> Tw(SNode(l, SBud(r))) {{ TX(l, r, u) }}
         theorem tx_beta(l: Shape, r: Shape, u: Tw(l)):
             tsize(SNode(l, SBud(r)), mk(l, r, u)) = Succ(tsize(l, u)) {{ refl }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
    // …while the form-A constructor of that same declaration computes.
    elab(&format!(
        "{ADD}{TWC}
         theorem tb_beta(s: Shape, x: Nat, t: Tw(s)):
             tsize(SBud(s), TB(s, x, t)) = Succ(tsize(s, t)) {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// A **branching** index constructor: the `Bal`-over-`Shape` shape of
// `indexed_declared_families.rs`, forded by `BDup`'s non-linear result index
// (which route 1 rejects, so this declaration is genuinely route 2b).
// ---------------------------------------------------------------------------

const BAL: &str = r#"
inductive Shape { SLeaf, SNode(l: Shape, r: Shape) }
inductive Bl : (s: Shape) -> Type {
    BLeaf                                            : Bl(SLeaf),
    BNode(l: Shape, r: Shape, dl: Bl(l), dr: Bl(r))  : Bl(SNode(l, r)),
    BDup(s: Shape)                                   : Bl(SNode(s, s)),
}
fn count(s: Shape, d: Bl(s)) -> Nat {
    match d {
        BLeaf => 1,
        BNode(l, r, dl, dr) => add(count(l, dl), count(r, dr)),
        BDup(s) => 0,
    }
}
"#;

#[test]
fn form_a_through_a_branching_index_constructor() {
    // §10.1's composition, now with the *index's* recursion branching too:
    // `SNode` has two recursive arguments, so the arm recovers two child-index
    // binders (`nth(cs'_I; ι₀)` and `ι₁`) and re-derives two equations through
    // two different child projections. Swapping them is exactly the defect a
    // single-child index cannot see, so both children are open here and both
    // sides of the reduct name them.
    elab(&format!(
        "{ADD}{BAL}
         fn two() -> Bl(SNode(SLeaf, SLeaf)) {{ BNode(SLeaf, SLeaf, BLeaf, BLeaf) }}
         theorem c_closed(): count(SNode(SLeaf, SLeaf), two()) = 2 {{ refl }}
         theorem c_leaf(): count(SLeaf, BLeaf) = 1 {{ refl }}
         theorem c_open(l: Shape, r: Shape, dl: Bl(l), dr: Bl(r)):
             count(SNode(l, r), BNode(l, r, dl, dr)) = add(count(l, dl), count(r, dr))
             {{ refl }}"
    ));
}

// An identity induction over the *values* of a forded family — `bmap(s, d) = d`
// — is **not** provable here, and the reason is not this round's: every forded
// declaration has at least one form-B constructor by construction (a
// declaration all of whose constructors are route-1-eligible takes route 1),
// and a form-B arm whose goal mentions the value itself is exactly §8.4's stall
// — the arm's `transp` sits over a *bound* proof and does not β. Measured at a
// `Nat` index too, on machinery this round did not touch, so it is recorded as
// a finding rather than pinned here (the smallest failing case is two
// *childless* constructors, `NfZ(x) : Nf(0)` beside `NfD(a, b) : Nf(add(a,b))`).

// ---------------------------------------------------------------------------
// A **flat** (enum) declared index: the inversion is a `Case` tree rather than
// an `elim_Wf`, which is the other half of §8.2's dispatch. `QAny`'s
// bare-variable index is what fords the declaration (§3.4's non-uniform row).
// ---------------------------------------------------------------------------

const FLAT: &str = r#"
inductive Par { PA, PB, PC }
inductive AB : (p: Par) -> Type {
    QA(x: Nat)                  : AB(PA),
    QB(y: Nat, z: Nat)          : AB(PB),
    QC                          : AB(PC),
    QAny(p: Par)                : AB(p),
}
fn rd(p: Par, d: AB(p)) -> Nat {
    match d { QA(x) => x, QB(y, z) => add(y, z), QC => 0, QAny(p) => 0 }
}
"#;

#[test]
fn a_flat_declared_index_inverts_by_case_tree() {
    // Three index constructors and three form-A arms, each with **two**
    // no-confusion branches — axis 6 again, and the reason this is not folded
    // into the two-constructor `Par` of `indexed_declared_families.rs`.
    elab(&format!(
        "{ADD}{FLAT}
         theorem a(x: Nat): rd(PA, QA(x)) = x {{ refl }}
         theorem b(y: Nat, z: Nat): rd(PB, QB(y, z)) = add(y, z) {{ refl }}
         theorem c(): rd(PC, QC) = 0 {{ refl }}
         fn any(p: Par) -> AB(p) {{ QAny(p) }}
         theorem d(p: Par): rd(p, QAny(p)) = 0 {{ refl }}"
    ));
}

#[test]
fn a_nullary_index_constructor_is_not_a_bare_variable() {
    // Found while building the row above (2026-08-04): `AB(PA)` parses as
    // `App(AB, [Var("PA")])`, so the *uniform bare variable* test read a family
    // whose every index is a nullary index constructor as a parameter wearing
    // an index's spelling, and rejected `FLAT` with the parameter message
    // instead of fording it. The index type's own constructor names are now
    // excluded from that test — and the parameter message still wins where it
    // should.
    let m = elab_err("inductive Q : (n: Nat) -> Type { Mk(n: Nat) : Q(n) }");
    assert!(m.contains("a **parameter**, not an index"), "{m}");
    // At a *declared* index the same uniform declaration is still rejected, but
    // with route 1's generic message: the parameter row of §3.3 is `Nat`-only
    // in `parse_result_index`, which is a message asymmetry and not a routing
    // one.
    let m = elab_err(
        "inductive Par { PA, PB }
         inductive Q : (p: Par) -> Type { Mk(p: Par) : Q(p) }",
    );
    assert!(m.contains("not constructor-headed"), "{m}");
}

// ---------------------------------------------------------------------------
// A nonzero level (route 1 §10.5's standing rule, not re-learned) and the
// negatives.
// ---------------------------------------------------------------------------

const LEVEL1: &str = r#"
inductive Shape { SLeaf, SNode(l: Shape, r: Shape) }
inductive PT : (s: Shape) -> Type {
    PL(A: Type)                                          : PT(SLeaf),
    PN(l: Shape, r: Shape, A: Type, a: PT(l), b: PT(r))  : PT(SNode(l, r)),
    PD(s: Shape)                                         : PT(SNode(s, s)),
}
fn psize(s: Shape, p: PT(s)) -> Nat {
    match p { PL(A) => 1, PN(l, r, A, a, b) => add(psize(l, a), psize(r, b)), PD(s) => 0 }
}
"#;

#[test]
fn fields_above_level_zero_at_a_declared_index() {
    // A `Type`-valued payload puts the skeleton and the family at level 1 while
    // the motive stays at 0, so every `l ⊔ li` and `l ⊔ mlvl` the inversion
    // threads — including the one the *index's* eliminator carries — is now a
    // different level. A dropped join cannot hide here.
    elab(&format!(
        "{ADD}{LEVEL1}
         fn one() -> PT(SLeaf) {{ PL(Nat) }}
         theorem closed():
             psize(SNode(SLeaf, SLeaf), PN(SLeaf, SLeaf, Nat, PL(Nat), PL(Nat))) = 2 {{ refl }}
         theorem leaf_beta(): psize(SLeaf, PL(Nat)) = 1 {{ refl }}
         theorem open_beta(l: Shape, r: Shape, a: PT(l), b: PT(r)):
             psize(SNode(l, r), PN(l, r, Nat, a, b)) = add(psize(l, a), psize(r, b))
             {{ refl }}"
    ));
}

#[test]
fn wrong_indices_are_rejected() {
    // Axis 4 for the inversion itself: every one of these *would* elaborate
    // under an arm that ignored the index it stands at, and what it would build
    // is a checked theorem about a type the user did not write.
    elab_err(&format!("{ADD}{TW} fn bad(s: Shape) -> Tw(SLeaf) {{ TB(s, 1, TL) }}"));
    elab_err(&format!("{ADD}{TW} fn bad(s: Shape, t: Tw(s)) -> Tw(s) {{ TB(s, 1, t) }}"));
    elab_err(&format!("{ADD}{TW} fn bad(s: Shape) -> Tw(SBud(s)) {{ TL }}"));
    // A child at the wrong index, at two distinct open subjects — the swap the
    // branching arm's two child projections exist to keep apart.
    elab_err(&format!(
        "{ADD}{BAL} fn bad(l: Shape, r: Shape, dl: Bl(l), dr: Bl(r)) -> Bl(SNode(l, r)) {{
             BNode(l, r, dr, dl)
         }}"
    ));
    elab_err(&format!(
        "{ADD}{BAL} fn bad(l: Shape, r: Shape) -> Bl(SNode(l, r)) {{ BLeaf }}"
    ));
    // A `refl` does not prove an induction, at a declared index either.
    let m = elab_err(&format!(
        "{ADD}{BAL}
         fn bmap(s: Shape, d: Bl(s)) -> Bl(s) {{
             match d {{
                 BLeaf => BLeaf,
                 BNode(l, r, dl, dr) => BNode(l, r, bmap(l, dl), bmap(r, dr)),
                 BDup(s) => BDup(s),
             }}
         }}
         theorem bad(s: Shape, d: Bl(s)): bmap(s, d) = d {{ refl }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

#[test]
fn a_branching_form_a_at_a_three_constructor_index_fits_the_fuel_budget() {
    // **The positive this test was always trying to be** (§14.9, closed
    // 2026-08-04 by `issues/generated-term-defs.md`).
    //
    // History, because the shape of the claim is the history. Until the
    // generator's artifacts became Ψ definitions, form A at a declared index
    // emitted, per arm, one child projection per child and one tag predicate
    // per *other* index constructor — each a whole `elim_Wf` over the index
    // type, written out at every occurrence because the emitted term had
    // nowhere to name it. The product of *branching* (two projections) and
    // *three* index constructors (two tag predicates) put the eliminator over
    // the conversion budget: the claim below was true, the kernel accepted it
    // at twice `DEFAULT_FUEL`, and it was pinned here as a deliberate negative
    // asserting `OutOfFuel`, with the note that "when a kernel `def` lands,
    // the right fix is to turn it into the positive it was always trying to
    // be". That is this.
    //
    // What it now pins is the *sum*: `μ_Tn`, `Shape#tag{0,1,2}` and
    // `Shape#child{k}.{t}` are registered once at declaration time and
    // referenced, so the arm's size no longer multiplies and the same claim
    // fits inside `DEFAULT_FUEL`. Both factors are still present — branching
    // children *and* a three-constructor index — which is what makes this the
    // falsifier for the definition routing and not merely another passing
    // form-A test.
    elab(&format!(
        "{ADD}
         inductive Shape {{ SLeaf, SBud(s: Shape), SNode(l: Shape, r: Shape) }}
         inductive Tn : (s: Shape) -> Type {{
             TnL                                             : Tn(SLeaf),
             TnN(l: Shape, r: Shape, a: Tn(l), b: Tn(r))     : Tn(SNode(l, r)),
             TnX(l: Shape, r: Shape)                         : Tn(SNode(l, SBud(r))),
         }}
         fn tn(s: Shape, t: Tn(s)) -> Nat {{
             match t {{ TnL => 0, TnN(a, b, p, q) => add(tn(a, p), tn(b, q)), TnX(a, b) => 0 }}
         }}
         theorem open_beta(l: Shape, r: Shape, a: Tn(l), b: Tn(r)):
             tn(SNode(l, r), TnN(l, r, a, b)) = add(tn(l, a), tn(r, b)) {{ refl }}"
    ));
}
