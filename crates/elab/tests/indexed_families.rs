//! Acceptance for indexed families, route 1 — the generator, end to end
//! (docs/inductive-indexed-lowering.md §9 item 8; the hand prototype behind
//! it is `indexed_route1.rs`).
//!
//! Every declaration below is lowered to the index-recursive family form and
//! re-checked by the real kernel, so a wrong encoding is a rejection. The
//! surface tests mirror the prototype's kernel-level ones: β on fully open
//! data, pattern-variable recovery, `append`'s definitional index arithmetic,
//! `Fin(0)` as `Empty`, branching for free, and `mirror (mirror t) = t` by a
//! surface induction. Rejections are §8.1's, each pinned by its message.

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

const VEC: &str = r#"
inductive V<A> : (n: Nat) -> Type {
    VNil : V<A>(0),
    VCons(n: Nat, x: A, xs: V<A>(n)) : V<A>(Succ(n)),
}
"#;

// §9.1–2 — the declaration lowers, and constructors check at literal and at
// fully open indices, monomorphic and polymorphic.
#[test]
fn vec_declares_and_constructors_check() {
    elab(&format!(
        "{VEC}
         fn empty() -> V<Nat>(0) {{ VNil }}
         fn three() -> V<Nat>(3) {{ VCons(2, 1, VCons(1, 2, VCons(0, 3, VNil))) }}
         fn push(n: Nat, x: Nat, xs: V<Nat>(n)) -> V<Nat>(Succ(n)) {{ VCons(n, x, xs) }}
         fn ppush<A>(n: Nat, x: A, xs: V<A>(n)) -> V<A>(Succ(n)) {{ VCons(n, x, xs) }}"
    ));
}

// §6.2 — match β fires on fully open data, and the arm recovers the pattern
// variable as the eliminator's own binder (§4.1). Both pinned by `refl`.
#[test]
fn beta_fires_and_the_pattern_variable_recovers() {
    elab(&format!(
        "{VEC}
         fn len(n: Nat, xs: V<Nat>(n)) -> Nat {{
             match xs {{ VNil => 0, VCons(k, x, t) => Succ(len(k, t)) }}
         }}
         fn peek(n: Nat, xs: V<Nat>(n)) -> Nat {{
             match xs {{ VNil => 0, VCons(k, x, t) => k }}
         }}
         fn three() -> V<Nat>(3) {{ VCons(2, 1, VCons(1, 2, VCons(0, 3, VNil))) }}
         theorem len_closed(): len(3, three()) = 3 {{ refl }}
         theorem len_open(n: Nat, x: Nat, xs: V<Nat>(n)):
             len(Succ(n), VCons(n, x, xs)) = Succ(len(n, xs)) {{ refl }}
         theorem peek_open(n: Nat, x: Nat, xs: V<Nat>(n)):
             peek(Succ(n), VCons(n, x, xs)) = n {{ refl }}"
    ));
}

// §9.3 — append at `V(add(m, n))`: the arm owes `V(add(m, Succ k))` and pays
// `V(Succ (add(m, k)))`, definitionally. The self-call rebinds the index
// parameter to the arm's pattern variable (§6).
#[test]
fn append_and_definitional_index_arithmetic() {
    elab(&format!(
        "{VEC}
         fn add(a: Nat, b: Nat) -> Nat {{
             match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }}
         }}
         fn append(n: Nat, m: Nat, xs: V<Nat>(n), ys: V<Nat>(m)) -> V<Nat>(add(m, n)) {{
             match xs {{
                 VNil => ys,
                 VCons(k, x, t) => VCons(add(m, k), x, append(k, m, t, ys)),
             }}
         }}
         theorem app_closed():
             append(2, 1, VCons(1, 1, VCons(0, 2, VNil)), VCons(0, 3, VNil))
                 = VCons(2, 1, VCons(1, 2, VCons(0, 3, VNil))) {{ refl }}
         theorem app_open(n: Nat, m: Nat, x: Nat, xs: V<Nat>(n), ys: V<Nat>(m)):
             append(Succ(n), m, VCons(n, x, xs), ys)
                 = VCons(add(m, n), x, append(n, m, xs, ys)) {{ refl }}"
    ));
}

// An induction with the motive dependent on the index: `cmap` is the identity,
// proved by a surface `match` whose step is one `j` — the ih is the recursive
// theorem call, exactly as for `Nat` and `Wf` matches.
#[test]
fn map_id_by_surface_induction() {
    elab(&format!(
        "{VEC}
         fn cmap(n: Nat, xs: V<Nat>(n)) -> V<Nat>(n) {{
             match xs {{ VNil => VNil, VCons(k, x, t) => VCons(k, x, cmap(k, t)) }}
         }}
         theorem cmap_id(n: Nat, xs: V<Nat>(n)): cmap(n, xs) = xs {{
             match xs {{
                 VNil => refl,
                 VCons(k, x, t) => j(cmap_id(k, t),
                     \u{3bb} y q => VCons(k, x, cmap(k, t)) = VCons(k, x, y),
                     refl),
             }}
         }}"
    ));
}

// The `Fin` shape: an empty index class does its job — `F(0)` *is* `Empty`
// (a no-arm match eliminates it), two constructors share the `Succ` class,
// and an explicit two-binder motive is writable (§6.1).
#[test]
fn fin_empty_class_and_shared_succ_class() {
    elab(
        r#"
        inductive F : (n: Nat) -> Type {
            FZ(n: Nat) : F(Succ(n)),
            FS(n: Nat, i: F(n)) : F(Succ(n)),
        }
        fn fz1() -> F(1) { FZ(0) }
        fn fs2() -> F(2) { FS(1, FZ(0)) }
        fn up(n: Nat, i: F(n)) -> F(Succ(n)) { FS(n, i) }
        fn from_empty(p: F(0)) -> Nat { match p { } }
        fn which(n: Nat, i: F(Succ(n))) -> Nat {
            match i as λ h z => Nat { FZ(k) => 0, FS(k, t) => 1 }
        }
        theorem which_fz(n: Nat): which(n, FZ(n)) = 0 { refl }
        theorem which_fs(n: Nat, i: F(n)): which(n, FS(n, i)) = 1 { refl }
        "#,
    );
}

// §5.1, the marquee: branching is free. `N` keeps constructor form on open
// children, `mirror` β-fires through it, and `mirror (mirror t) = t` goes
// through by surface induction with two `j`s — each child's ih a recursive
// theorem call at the rebound index.
#[test]
fn branching_tree_mirror_and_involution() {
    elab(
        r#"
        inductive T : (n: Nat) -> Type {
            L : T(0),
            N(n: Nat, l: T(n), r: T(n)) : T(Succ(n)),
        }
        fn mirror(n: Nat, t: T(n)) -> T(n) {
            match t { L => L, N(k, a, b) => N(k, mirror(k, b), mirror(k, a)) }
        }
        theorem m_closed(): mirror(1, N(0, L, L)) = N(0, L, L) { refl }
        theorem m_open(n: Nat, a: T(n), b: T(n)):
            mirror(Succ(n), N(n, a, b)) = N(n, mirror(n, b), mirror(n, a)) { refl }
        theorem mm(n: Nat, t: T(n)): mirror(n, mirror(n, t)) = t {
            match t {
                L => refl,
                N(k, a, b) => j(mm(k, b),
                    λ y q => N(k, mirror(k, mirror(k, a)), mirror(k, mirror(k, b)))
                           = N(k, a, y),
                    j(mm(k, a),
                      λ y q => N(k, mirror(k, mirror(k, a)), mirror(k, mirror(k, b)))
                             = N(k, y, mirror(k, mirror(k, b))),
                      refl)),
            }
        }
        "#,
    );
}

// §8.1 — the rejections, each with the route that *does* cover it named, and
// §2's form errors. A rejection is load-bearing here: everything in this list
// is lowerable in principle by fording, and silently mis-lowering it into the
// index-recursive scheme is the hazard class.
#[test]
fn rejections_carry_their_messages() {
    // A computed result index and a deep pattern used to be rejections naming
    // route 2b as "not yet generated". Route 2b **is** generated now
    // (docs/inductive-fording-lowering.md; the observers are
    // `indexed_route_2b_gen.rs` §13.2 items 9 and 11), so both declarations
    // land — by fording, not by this scheme. What stays a rejection is what
    // neither fragment covers, and the list below is that.
    elab("inductive P : (n: Nat) -> Type { Mk(a: Nat, b: Nat) : P(plus(a, b)) }");
    elab(
        "inductive E : (n: Nat) -> Type { E0 : E(0), ESS(n: Nat, e: E(n)) : E(Succ(Succ(n))) }",
    );
    // A bare-variable index in *every* constructor is not an index at all: it
    // is uniform, so it is a **parameter**, and it lowers by substitution with
    // none of fording's machinery. This message used to send it toward route
    // 2b; `docs/surface-existential-investigation.md` §C.7 identified that as
    // the wrong steer, and `record Q(n: Nat)` is now the grammar it names
    // (docs/surface-value-parameters.md).
    let m = elab_err("inductive Q : (n: Nat) -> Type { Mk(n: Nat) : Q(n) }");
    assert!(m.contains("a **parameter**, not an index"), "{m}");
    assert!(m.contains("record Q(n: Nat)"), "{m}");
    // Non-uniform: one constructor pins its index, so this one really does
    // target *every* index and really is the fording case. The old message
    // stands, which is what makes the arm above a distinction and not a
    // blanket rewording.
    // Non-uniform: one constructor pins its index, so this one really does
    // target *every* index and really is the fording case — §3.4's
    // non-uniform-bare-variable row, which route 2b now generates.
    elab("inductive Q2 : (n: Nat) -> Type { A : Q2(0), Mk(n: Nat) : Q2(n) }");
    let m = elab_err(
        "inductive W2 : (n: Nat) -> Type { M0 : W2(0), Mk(n: Nat, w: W2(0)) : W2(Succ(n)) }",
    );
    assert!(m.contains("pattern variable"), "{m}");
    let m = elab_err("inductive M : (n: Nat) -> Type { Mk }");
    assert!(m.contains("result annotation"), "{m}");
    let m = elab_err("inductive U { Mk : U(0) }");
    assert!(m.contains("not indexed"), "{m}");
    let m = elab_err(&format!("{VEC} fn bad(x: V<Nat>) -> Nat {{ 0 }}"));
    assert!(m.contains("needs its index"), "{m}");
}

// The kernel gate half: index-shaped near-misses are rejections, not terms.
#[test]
fn wrong_indices_are_rejected() {
    // A `VCons` at index 0.
    elab_err(&format!("{VEC} fn bad() -> V<Nat>(0) {{ VCons(0, 1, VNil) }}"));
    // The written index disagrees with the expected one.
    elab_err(&format!(
        "{VEC} fn bad(n: Nat, x: Nat, xs: V<Nat>(n)) -> V<Nat>(n) {{ VCons(n, x, xs) }}"
    ));
    // A tail at the wrong index.
    elab_err(&format!(
        "{VEC} fn bad(n: Nat, m: Nat, x: Nat, xs: V<Nat>(n)) -> V<Nat>(Succ(m)) {{
             VCons(m, x, xs)
         }}"
    ));
    // `VNil` at a successor index.
    elab_err(&format!("{VEC} fn bad(n: Nat) -> V<Nat>(Succ(n)) {{ VNil }}"));
    // A `refl` does not prove an induction: the map is neutral on an open
    // scrutinee.
    elab_err(&format!(
        "{VEC}
         fn cmap(n: Nat, xs: V<Nat>(n)) -> V<Nat>(n) {{
             match xs {{ VNil => VNil, VCons(k, x, t) => VCons(k, x, cmap(k, t)) }}
         }}
         theorem bad(n: Nat, xs: V<Nat>(n)): cmap(n, xs) = xs {{ refl }}"
    ));
}

// §9 item 8's "fields at levels above 0": a `Type`-valued field puts the
// family at level 1, so the two-pass level computation in
// `lower_indexed_instance` and the eliminator's `l ≠ mlvl` plumbing (motive
// at 0, scrutinee at 1) both do real work — everything else in this file is
// uniformly level 0 and would not notice a dropped join.
#[test]
fn fields_above_level_zero() {
    elab(
        r#"
        inductive P : (n: Nat) -> Type {
            P0(A: Type) : P(0),
            PS(n: Nat, A: Type, x: A, t: P(n)) : P(Succ(n)),
        }
        fn depth(n: Nat, p: P(n)) -> Nat {
            match p { P0(A) => 0, PS(k, A, x, t) => Succ(depth(k, t)) }
        }
        theorem depth_closed(): depth(1, PS(0, Nat, 3, P0(Nat))) = 1 { refl }
        theorem depth_open(n: Nat, x: Nat, t: P(n)):
            depth(Succ(n), PS(n, Nat, x, t)) = Succ(depth(n, t)) { refl }
        "#,
    );
}
