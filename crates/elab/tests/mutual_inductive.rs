//! Acceptance for mutual inductive families (`docs/mutual-inductive-design.md`):
//! a group of `inductive` declarations lowered to one `IWf` family indexed by
//! its members, a `match` per member, and a group of `fn`s or `theorem`s
//! recursing over it as one structural recursion.
//!
//! The four axes of `docs/testing-generated-terms.md` throughout: a literal
//! scrutinee (closed values computed by `refl`) and a neutral one (β by
//! `refl` on open data, every `theorem` a checking position), an **open**
//! element type (the `Tree<A>`/`Forest<A>` group, at type variables), and a
//! negative control per positive. One group has members indexed by
//! different types (a declared `Sort` and `Nat`), the tag-dependent case,
//! and the `Ty`/`Tm` group has an unindexed member beside an indexed one.

use heather_elab::{ElabError, Elaborator};

use crate::support;

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

/// An unindexed member beside an indexed one.
const TYTM: &str = r#"
inductive Ty {
    Base,
    Arr(a: Ty, b: Ty),
    Box(n: Nat, t: Tm(n)),
}
inductive Tm : (n: Nat) -> Type {
    Var(n: Nat) : Tm(Succ(n)),
    Lam(n: Nat, ty: Ty, body: Tm(Succ(n))) : Tm(n),
    App(n: Nat, f: Tm(n), a: Tm(n)) : Tm(n),
}
"#;

/// Members indexed by different types: a declared index and `Nat`.
const SORTED: &str = r#"
inductive Sort { SV, ST }
inductive Ty : (s: Sort) -> Type {
    TVar : Ty(SV),
    TBase : Ty(ST),
    TArr(a: Ty(ST), b: Ty(ST)) : Ty(ST),
    TBox(n: Nat, t: Tm(n)) : Ty(ST),
}
inductive Tm : (n: Nat) -> Type {
    Var(n: Nat) : Tm(Succ(n)),
    Ann(n: Nat, t: Tm(n), ty: Ty(ST)) : Tm(n),
}
"#;

const EVEN_ODD: &str = r#"
inductive Even : (n: Nat) -> Type {
    EZ : Even(0),
    ES(n: Nat, o: Odd(n)) : Even(Succ(n)),
}
inductive Odd : (n: Nat) -> Type {
    OS(n: Nat, e: Even(n)) : Odd(Succ(n)),
}
"#;

const FOREST: &str = r#"
inductive Tree<A> { Leaf(x: A), Node(f: Forest<A>) }
inductive Forest<A> { Nil, Cons(t: Tree<A>, rest: Forest<A>) }
"#;

// ---------------------------------------------------------------------------
// Declarations, constructors and `match` per member (§1–§5).

#[test]
fn members_construct_and_match_by_their_own_constructors() {
    elab(&format!(
        "{ADD}{TYTM}
         fn size_ty(t: Ty) -> Nat {{ match t {{ Base => 1, Arr(a, b) => add(size_ty(a), size_ty(b)), Box(n, m) => 1 }} }}
         theorem literal(): size_ty(Arr(Base, Arr(Base, Base))) = 3 {{ refl }}
         theorem open(a: Ty, b: Ty): size_ty(Arr(a, b)) = add(size_ty(a), size_ty(b)) {{ refl }}
         fn mk(n: Nat) -> Tm(n) {{ Lam(n, Base, Var(n)) }}
         fn ty_of(n: Nat, t: Tm(n)) -> Ty {{ match t {{ Var(k) => Base, Lam(k, ty, b) => ty, App(k, f, a) => Base }} }}
         theorem lam(n: Nat, ty: Ty, b: Tm(Succ(n))): ty_of(n, Lam(n, ty, b)) = ty {{ refl }}
         theorem built(): ty_of(2, mk(2)) = Base {{ refl }}"
    ));
}

#[test]
fn an_arm_for_another_members_constructor_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(a, b) => 0, Box(n, m) => 0, Var(k) => 0 }} }}"
    ));
    assert!(m.contains("`Var` is a constructor of `Tm`, not of `Ty`"), "{m}");
}

#[test]
fn a_default_arm_covers_the_members_own_constructors() {
    // `_` expands to `Ty`'s constructors only, not to the family's.
    elab(&format!(
        "{TYTM}
         fn is_base(t: Ty) -> Nat {{ match t {{ Base => 1, _ => 0 }} }}
         theorem b(n: Nat, m: Tm(n)): is_base(Box(n, m)) = 0 {{ refl }}"
    ));
}

#[test]
fn a_constructor_at_the_wrong_member_is_refused() {
    let m = elab_err(&format!("{TYTM}\nfn bad() -> Ty {{ Var(0) }}"));
    assert!(m.contains("`Var` is a constructor of `Tm`") && m.contains("`Ty`"), "{m}");
}

#[test]
fn recursion_on_one_member_rebinds_its_index() {
    // The recursive call varies `n` through the member: the guard reads the
    // inner index off `Tm#member(e)` (§5).
    elab(&format!(
        "{ADD}{TYTM}
         fn lams(n: Nat, t: Tm(n)) -> Nat {{
             match t {{ Var(k) => 0, Lam(k, ty, b) => Succ(lams(Succ(k), b)), App(k, f, a) => add(lams(k, f), lams(k, a)) }}
         }}
         theorem l1(n: Nat, ty: Ty, b: Tm(Succ(n))): lams(n, Lam(n, ty, b)) = Succ(lams(Succ(n), b)) {{ refl }}
         theorem l2(): lams(0, Lam(0, Base, Lam(1, Base, Var(1)))) = 2 {{ refl }}"
    ));
}

#[test]
fn a_member_at_a_declared_index_inverts_on_it() {
    // Tag-dependent indices: `Ty` is indexed by `Sort`, `Tm` by `Nat`. At
    // `Ty(ST)` the `TVar` arm cannot occur and is not written.
    elab(&format!(
        "{SORTED}
         fn arity(t: Ty(ST)) -> Nat {{ match t {{ TBase => 0, TArr(a, b) => Succ(arity(b)), TBox(_, _) => 0 }} }}
         theorem a1(a: Ty(ST), b: Ty(ST)): arity(TArr(a, TArr(a, b))) = Succ(Succ(arity(b))) {{ refl }}
         theorem a2(): arity(TArr(TBase, TBox(1, Var(0)))) = 1 {{ refl }}"
    ));
}

#[test]
fn a_member_at_a_declared_index_still_needs_its_reachable_arms() {
    let m = elab_err(&format!(
        "{SORTED}
         fn arity(t: Ty(ST)) -> Nat {{ match t {{ TArr(a, b) => Succ(arity(b)), TBox(_, _) => 0 }} }}"
    ));
    assert!(m.contains("TBase"), "{m}");
}

#[test]
fn inversion_recurses_into_the_members_index() {
    // `Even(Succ(n))` inverts twice: on the member, then on `Nat`, so the
    // `EZ` arm cannot occur; `Odd(0)` has no constructor at all.
    elab(&format!(
        "{EVEN_ODD}
         fn pred_even(n: Nat, e: Even(Succ(n))) -> Odd(n) {{ match e {{ ES(k, o) => o }} }}
         theorem pe(n: Nat, o: Odd(n)): pred_even(n, ES(n, o)) = o {{ refl }}
         fn pred_odd(n: Nat, o: Odd(Succ(n))) -> Even(n) {{ match o {{ OS(k, e) => e }} }}
         theorem t2(): pred_odd(0, pred_even(1, ES(1, OS(0, EZ)))) = EZ {{ refl }}
         fn no_odd_zero(o: Odd(0)) -> Nat {{ match o {{ }} }}"
    ));
}

#[test]
fn an_inverted_arm_is_still_typed_at_its_index() {
    // Negative for the inversion: `pred_even`'s arm returns the `Odd` at the
    // inverted index, not at any other.
    let m = elab_err(&format!(
        "{EVEN_ODD}
         fn pred_even(n: Nat, e: Even(Succ(n))) -> Odd(Succ(n)) {{ match e {{ ES(k, o) => o }} }}"
    ));
    assert!(m.contains("Odd"), "{m}");
}

#[test]
fn a_parameterized_group_at_an_open_element_type() {
    elab(&format!(
        "{FOREST}
         fn leaves<A>(f: Forest<A>) -> Nat {{ match f {{ Nil => 0, Cons(t, rest) => Succ(leaves(rest)) }} }}
         theorem open<A>(t: Tree<A>, f: Forest<A>): leaves(Cons(t, f)) = Succ(leaves(f)) {{ refl }}
         fn single<A>(x: A) -> Tree<A> {{ Node(Cons(Leaf(x), Nil)) }}
         theorem lit(): leaves(Cons(single(3), Cons(Leaf(4), Nil))) = 2 {{ refl }}"
    ));
}

#[test]
fn a_group_at_a_wrong_element_type_is_refused() {
    let m = elab_err(&format!(
        "{FOREST}
         fn bad<A>(x: A) -> Forest<A> {{ Cons(Leaf(0), Nil) }}"
    ));
    assert!(!m.is_empty(), "{m}");
}

// ---------------------------------------------------------------------------
// What a group requires (§1, §7).

#[test]
fn a_non_uniform_occurrence_is_refused() {
    let m = elab_err(
        "inductive T<A> { L(x: A), N(f: F<Nat>) }
         inductive F<A> { E, C(t: T<A>) }",
    );
    assert!(m.contains("uniform"), "{m}");
}

#[test]
fn members_with_different_parameters_are_refused() {
    let m = elab_err(
        "inductive T<A> { L(x: A), N(f: F) }
         inductive F { E, C(t: T<Nat>) }",
    );
    assert!(m.contains("same type parameters"), "{m}");
}

#[test]
fn a_codata_member_is_refused() {
    let m = elab_err(
        "inductive T { L, N(f: F) }
         codata F { C(t: T, rest: F) }",
    );
    assert!(m.contains("`codata`"), "{m}");
}

#[test]
fn a_nested_occurrence_of_a_member_is_refused() {
    let m = elab_err(
        "inductive List<A> { Nil, Cons(h: A, t: List<A>) }
         inductive T { L, N(f: F) }
         inductive F { E, C(ts: List<T>, f: F) }",
    );
    assert!(m.contains("inside another type"), "{m}");
}

#[test]
fn a_member_in_a_function_fields_domain_is_refused() {
    // A member as the codomain is a function child
    // (docs/iwf-infinitary-design.md §12, `iwf_infinitary.rs`); in the domain
    // it is not strictly positive.
    let m = elab_err(
        "inductive T { L, N(f: F) }
         inductive F { E, C(k: T -> Nat) }",
    );
    assert!(m.contains("only as its codomain"), "{m}");
}

#[test]
fn a_result_at_another_member_is_refused() {
    let m = elab_err(
        "inductive A : (n: Nat) -> Type { MkA(b: B(n)) : B(n) }
         inductive B : (n: Nat) -> Type { MkB(a: A(n)) : B(n) }",
    );
    assert!(m.contains("each member's constructors build that member"), "{m}");
}

#[test]
fn constructors_share_one_namespace() {
    let m = elab_err(
        "inductive T { L, N(f: F) }
         inductive F { L, C(t: T) }",
    );
    assert!(m.contains("a constructor of both"), "{m}");
}

// ---------------------------------------------------------------------------
// Mutual structural recursion over a group (§6).

const SIZES: &str = r#"
fn size_ty(t: Ty, d: Nat) -> Nat {
    match t {
        Base => d,
        Arr(a, b) => add(size_ty(a, d), size_ty(b, Succ(d))),
        Box(n, m) => size_tm(n, m),
    }
}
fn size_tm(n: Nat, t: Tm(n)) -> Nat {
    match t {
        Var(k) => n,
        Lam(k, ty, b) => add(size_ty(ty, n), size_tm(Succ(n), b)),
        App(k, f, a) => add(size_tm(k, f), size_tm(n, a)),
    }
}
"#;

#[test]
fn a_group_recurses_over_both_members() {
    // Each member reads its own index (`n`) at this level, varies it in a
    // sibling call, and passes an extra parameter that a call varies (`d`).
    elab(&format!(
        "{ADD}{TYTM}{SIZES}
         theorem b1(a: Ty, b: Ty, d: Nat): size_ty(Arr(a, b), d) = add(size_ty(a, d), size_ty(b, Succ(d))) {{ refl }}
         theorem b2(n: Nat, t: Tm(n)): size_ty(Box(n, t), 3) = size_tm(n, t) {{ refl }}
         theorem b3(n: Nat, ty: Ty, b: Tm(Succ(n))):
             size_tm(n, Lam(n, ty, b)) = add(size_ty(ty, n), size_tm(Succ(n), b)) {{ refl }}
         theorem b4(): size_tm(1, Var(0)) = 1 {{ refl }}
         theorem b5(): size_ty(Box(0, Lam(0, Base, Var(0))), 0) = 1 {{ refl }}"
    ));
}

#[test]
fn a_group_computes_what_it_says() {
    // Negative for the β rules: the wrong unfolding is refused.
    let m = elab_err(&format!(
        "{ADD}{TYTM}{SIZES}
         theorem wrong(n: Nat, t: Tm(n)): size_ty(Box(n, t), 3) = size_tm(Succ(n), t) {{ refl }}"
    ));
    assert!(!m.is_empty(), "{m}");
}

/// The ring `Mᵢ { Lᵢ, Nᵢ(a: Mᵢ₊₁, b: Mᵢ) }` of `m` members and one `sizeᵢ`
/// each (`issues/mutual-group-recursion-gate-cost.md`, the bench family
/// `inductive/mutual-recursion`).
fn ring(m: usize) -> String {
    let mut s = String::from(ADD);
    for i in 0..m {
        let j = (i + 1) % m;
        s.push_str(&format!("inductive M{i} {{ L{i}, N{i}(a: M{j}, b: M{i}) }}\n"));
    }
    for i in 0..m {
        let j = (i + 1) % m;
        s.push_str(&format!(
            "fn size{i}(t: M{i}) -> Nat {{ match t {{ L{i} => 1, N{i}(a, b) => add(size{j}(a), size{i}(b)) }} }}\n"
        ));
    }
    s
}

#[test]
fn an_eight_member_ring_unfolds_by_refl() {
    // Eight members ran out of conversion fuel on the open unfolding: the
    // two sides' recursions compared their steps through the ih's shifted
    // copy of the step.
    let src = ring(8);
    elab(&format!(
        "{src}
         theorem open(a: M1, b: M0): size0(N0(a, b)) = add(size1(a), size0(b)) {{ refl }}
         theorem deep(a: M0, b: M7): size7(N7(L0, N7(a, b))) = add(1, add(size0(a), size7(b))) {{ refl }}
         theorem lit(): size0(N0(N1(L2, L1), L0)) = 3 {{ refl }}"
    ));
    // Negative control: the members' recursions are not interchangeable.
    let m = elab_err(&format!(
        "{src}
         theorem wrong(a: M1, b: M0): size0(N0(a, b)) = add(size0(b), size0(b)) {{ refl }}"
    ));
    assert!(!m.is_empty(), "{m}");
}

#[test]
fn a_theorem_group_is_mutual_induction() {
    elab(&format!(
        "{TYTM}
         fn id_ty(t: Ty) -> Ty {{
             match t {{ Base => Base, Arr(a, b) => Arr(id_ty(a), id_ty(b)), Box(n, m) => Box(n, id_tm(n, m)) }}
         }}
         fn id_tm(n: Nat, t: Tm(n)) -> Tm(n) {{
             match t {{ Var(k) => Var(k), Lam(k, ty, b) => Lam(k, id_ty(ty), id_tm(Succ(k), b)), _ => t }}
         }}
         theorem cong_arr(a: Ty, b: Ty, c: Ty, d: Ty, p: a = c, q: b = d): Arr(a, b) = Arr(c, d) {{ rewrite(p, q, refl) }}
         theorem cong_box(n: Nat, a: Tm(n), b: Tm(n), p: a = b): Box(n, a) = Box(n, b) {{ rewrite(p, refl) }}
         theorem cong_lam(n: Nat, a: Ty, c: Ty, b: Tm(Succ(n)), d: Tm(Succ(n)), p: a = c, q: b = d):
             Lam(n, a, b) = Lam(n, c, d) {{ rewrite(p, q, refl) }}
         theorem id_ty_ok(t: Ty): id_ty(t) = t {{
             match t {{
                 Base => refl,
                 Arr(a, b) => cong_arr(id_ty(a), id_ty(b), a, b, id_ty_ok(a), id_ty_ok(b)),
                 Box(n, m) => cong_box(n, id_tm(n, m), m, id_tm_ok(n, m)),
             }}
         }}
         theorem id_tm_ok(n: Nat, t: Tm(n)): id_tm(n, t) = t {{
             match t {{
                 Var(k) => refl,
                 Lam(k, ty, b) => cong_lam(k, id_ty(ty), ty, id_tm(Succ(k), b), b, id_ty_ok(ty), id_tm_ok(Succ(k), b)),
                 App(k, f, a) => refl,
             }}
         }}"
    ));
}

#[test]
fn a_group_need_not_cover_the_family() {
    // `Env` is a member nobody recurses on: its motive is `True`.
    elab(&format!(
        "{ADD}
         inductive Ty {{ Base, Box(n: Nat, t: Tm(n)) }}
         inductive Tm : (n: Nat) -> Type {{
             Var(n: Nat) : Tm(Succ(n)),
             Clo(n: Nat, c: Env, body: Tm(n)) : Tm(n),
             Ann(n: Nat, e: Tm(n), ty: Ty) : Tm(n),
         }}
         inductive Env {{ Empty, Ext(c: Env, t: Ty) }}
         fn depth_ty(t: Ty) -> Nat {{ match t {{ Base => 0, Box(n, m) => Succ(depth_tm(n, m)) }} }}
         fn depth_tm(n: Nat, t: Tm(n)) -> Nat {{ match t {{ Var(_) => 0, Clo(k, _, b) => depth_tm(k, b), Ann(_, _, ty) => depth_ty(ty) }} }}
         theorem d(): depth_ty(Box(1, Clo(1, Ext(Empty, Base), Ann(1, Var(0), Box(1, Var(0)))))) = 2 {{ refl }}"
    ));
}

#[test]
fn a_group_over_members_indexed_by_different_types() {
    elab(&format!(
        "{ADD}{SORTED}
         fn ty_size(s: Sort, t: Ty(s)) -> Nat {{
             match t {{ TVar => 1, TBase => 1, TArr(a, b) => add(ty_size(ST, a), ty_size(ST, b)), TBox(n, m) => tm_size(n, m) }}
         }}
         fn tm_size(n: Nat, t: Tm(n)) -> Nat {{
             match t {{ Var(_) => 1, Ann(k, e, ty) => add(tm_size(k, e), ty_size(ST, ty)) }}
         }}
         theorem z1(n: Nat, e: Tm(n), ty: Ty(ST)): tm_size(n, Ann(n, e, ty)) = add(tm_size(n, e), ty_size(ST, ty)) {{ refl }}
         theorem z2(): ty_size(ST, TBox(1, Ann(1, Var(0), TArr(TBase, TBase)))) = 3 {{ refl }}"
    ));
}

#[test]
fn a_group_at_an_open_element_type() {
    elab(&format!(
        "{ADD}{FOREST}
         fn map_tree<A, B>(g: A -> B, t: Tree<A>) -> Tree<B> {{
             match t {{ Leaf(x) => Leaf(g(x)), Node(f) => Node(map_forest(g, f)) }}
         }}
         fn map_forest<A, B>(g: A -> B, f: Forest<A>) -> Forest<B> {{
             match f {{ Nil => Nil, Cons(t, rest) => Cons(map_tree(g, t), map_forest(g, rest)) }}
         }}
         theorem m1<A, B>(g: A -> B, t: Tree<A>, f: Forest<A>):
             map_forest(g, Cons(t, f)) = Cons(map_tree(g, t), map_forest(g, f)) {{ refl }}
         theorem m2(): map_tree(λ (n: Nat) => Succ(n), Node(Cons(Leaf(1), Nil))) = Node(Cons(Leaf(2), Nil)) {{ refl }}
         fn size_tree<A>(t: Tree<A>) -> Nat {{ match t {{ Leaf(_) => 1, Node(f) => Succ(size_forest(f)) }} }}
         fn size_forest<A>(f: Forest<A>) -> Nat {{
             match f {{ Nil => 0, Cons(t, rest) => add(size_tree(t), size_forest(rest)) }}
         }}
         theorem s1<A>(x: A, f: Forest<A>): size_forest(Cons(Leaf(x), f)) = add(1, size_forest(f)) {{ refl }}"
    ));
}

#[test]
fn an_even_odd_group_reads_this_levels_index() {
    elab(&format!(
        "{ADD}{EVEN_ODD}
         fn even_half(n: Nat, e: Even(n)) -> Nat {{ match e {{ EZ => 0, ES(k, o) => odd_half(k, o) }} }}
         fn odd_half(n: Nat, o: Odd(n)) -> Nat {{ match o {{ OS(k, e) => Succ(even_half(k, e)) }} }}
         theorem e1(): even_half(4, ES(3, OS(2, ES(1, OS(0, EZ))))) = 2 {{ refl }}
         theorem e2(k: Nat, e: Even(k)): odd_half(Succ(k), OS(k, e)) = Succ(even_half(k, e)) {{ refl }}
         fn idx_even(n: Nat, e: Even(n)) -> Nat {{ match e {{ EZ => n, ES(k, o) => idx_odd(k, o) }} }}
         fn idx_odd(n: Nat, o: Odd(n)) -> Nat {{ match o {{ OS(k, e) => add(n, idx_even(k, e)) }} }}
         theorem i1(): idx_odd(3, OS(2, ES(1, OS(0, EZ)))) = 4 {{ refl }}"
    ));
}

const F_CALLS_G: &str = "fn f(t: Ty) -> Nat { match t { Base => 0, Arr(a, b) => f(a), Box(n, m) => g(n, m) } }\n";

#[test]
fn a_group_arm_for_another_members_constructor_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(a, b) => f(a), Box(n, m) => g(n, m), Var(k) => 0 }} }}
         fn g(n: Nat, t: Tm(n)) -> Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => g(k, x) }} }}"
    ));
    assert!(m.contains("`Var` is a constructor of `Tm`, not of `Ty`"), "{m}");
}

#[test]
fn a_group_member_that_is_not_one_match_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}{F_CALLS_G}
         fn g(n: Nat, t: Tm(n)) -> Nat {{ f(Base) }}"
    ));
    assert!(m.contains("`g`'s is not"), "{m}");
}

#[test]
fn a_group_mixing_fn_and_theorem_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}{F_CALLS_G}
         theorem g(n: Nat, t: Tm(n)): Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => g(k, x) }} }}"
    ));
    assert!(m.contains("all `fn`s or all `theorem`s"), "{m}");
}

#[test]
fn a_group_call_that_does_not_descend_names_the_callee() {
    let m = elab_err(&format!(
        "{TYTM}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(a, b) => f(Arr(a, b)), Box(n, m) => g(n, m) }} }}
         fn g(n: Nat, t: Tm(n)) -> Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => g(k, x) }} }}"
    ));
    assert!(m.contains("recursive call to `f` must descend: argument `t`"), "{m}");
    assert!(!m.contains('#'), "{m}");
}

#[test]
fn a_group_member_at_a_non_variable_index_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}{F_CALLS_G}
         fn g(n: Nat, t: Tm(Succ(n))) -> Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => 0 }} }}"
    ));
    assert!(m.contains("at an index that is not one of its parameters"), "{m}");
}

#[test]
fn two_group_members_on_one_member_are_refused() {
    let m = elab_err(&format!(
        "{TYTM}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(a, b) => g(a), Box(n, m) => 0 }} }}
         fn g(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(a, b) => f(a), Box(n, m) => 0 }} }}"
    ));
    assert!(m.contains("both recurse on `Ty`"), "{m}");
}

#[test]
fn a_group_arm_with_a_deep_pattern_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(Base, b) => f(b), Arr(a, b) => f(a), Box(n, m) => g(n, m) }} }}
         fn g(n: Nat, t: Tm(n)) -> Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => g(k, x) }} }}"
    ));
    assert!(m.contains("deep pattern") && m.contains("`f`"), "{m}");
}

#[test]
fn a_group_member_passed_as_a_value_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}
         fn ap(h: Ty -> Nat, t: Ty) -> Nat {{ h(t) }}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Arr(a, b) => ap(f, a), Box(n, m) => g(n, m) }} }}
         fn g(n: Nat, t: Tm(n)) -> Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => g(k, x) }} }}"
    ));
    assert!(m.contains("not passed as a value"), "{m}");
}

#[test]
fn a_group_missing_an_arm_is_refused() {
    let m = elab_err(&format!(
        "{TYTM}
         fn f(t: Ty) -> Nat {{ match t {{ Base => 0, Box(n, m) => g(n, m) }} }}
         fn g(n: Nat, t: Tm(n)) -> Nat {{ match t {{ Var(k) => 0, Lam(k, ty, b) => f(ty), App(k, x, y) => g(k, x) }} }}"
    ));
    assert!(m.contains("no arm for `Arr`"), "{m}");
}

// ---------------------------------------------------------------------------
// Images: a group, its members and a recursion over it, written to a module
// image and replayed, then used from a module that imports them.

const SYNTAX_MODULE: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
inductive Ty {
    Base,
    Arr(a: Ty, b: Ty),
    Box(n: Nat, t: Tm(n)),
}
inductive Tm : (n: Nat) -> Type {
    Var(n: Nat) : Tm(Succ(n)),
    Lam(n: Nat, ty: Ty, body: Tm(Succ(n))) : Tm(n),
    App(n: Nat, f: Tm(n), a: Tm(n)) : Tm(n),
}
fn size_ty(t: Ty) -> Nat { match t { Base => 1, Arr(a, b) => add(size_ty(a), size_ty(b)), Box(n, m) => size_tm(n, m) } }
fn size_tm(n: Nat, t: Tm(n)) -> Nat {
    match t { Var(_) => 1, Lam(k, ty, b) => add(size_ty(ty), size_tm(Succ(k), b)), App(k, f, a) => add(size_tm(k, f), size_tm(k, a)) }
}
"#;

#[test]
fn a_group_round_trips_through_images() {
    let dir = std::env::temp_dir().join(format!("heather-mutual-images-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let modules = &[("syntax", SYNTAX_MODULE)];
    let cold = support::semantic_test_base_at(modules, dir.clone());
    let expected = cold.psi().clone();
    let mut warm = support::semantic_test_base_at(modules, dir.clone());
    assert_eq!(warm.psi(), &expected);
    let consumer = "import syntax;
         theorem imported(a: Ty, b: Ty): size_ty(Arr(a, b)) = add(size_ty(a), size_ty(b)) { refl }
         theorem through(): size_ty(Box(0, Lam(0, Base, Var(0)))) = 2 { refl }
         fn apps(n: Nat, t: Tm(n)) -> Nat { match t { Var(_) => 0, Lam(k, _, b) => apps(Succ(k), b), App(k, f, a) => Succ(apps(k, f)) } }
         theorem local(n: Nat, f: Tm(n), a: Tm(n)): apps(n, App(n, f, a)) = Succ(apps(n, f)) { refl }
         fn depth_ty(t: Ty) -> Nat { match t { Base => 0, Arr(a, b) => Succ(depth_ty(b)), Box(n, m) => depth_tm(n, m) } }
         fn depth_tm(n: Nat, t: Tm(n)) -> Nat { match t { Var(_) => 0, Lam(k, ty, b) => depth_ty(ty), App(k, f, a) => depth_tm(k, f) } }
         theorem group(n: Nat, ty: Ty, b: Tm(Succ(n))): depth_tm(n, Lam(n, ty, b)) = depth_ty(ty) { refl }";
    warm.elab_module_source("consumer", consumer)
        .unwrap_or_else(|err| panic!("{}", err.render(consumer)));
    let _ = std::fs::remove_dir_all(dir);
}
