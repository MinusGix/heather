//! Acceptance for tier-2 inductives — a recursive **function** field, lowered
//! on `W` (`issues/recursive-function-fields.md`), against the checklist of
//! `docs/inductives/inductive-tier2-w-lowering.md` §10 and the four axes of
//! `docs/testing-generated-terms.md`.
//!
//! Every declaration below is lowered onto `W`/`sup`/`elim_W` plus the leaf
//! predicate and re-checked by the real kernel, so a wrong encoding is a
//! rejection; the propositional tests are what catch a *well-typed* wrong
//! one.

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

/// The milestone's shape: a leaf, a plain child, and a function child whose
/// domain depends on the payload before it.
const ITREE: &str = r#"
inductive Flag { Yes, No }
inductive Cmd { Ask, Say(v: Nat) }
fn Resp(c: Cmd) -> Type { match c { Ask => Nat, Say(v) => Flag } }
inductive Tree { Ret(r: Nat), Tau(t: Tree), Vis(c: Cmd, k: Resp(c) -> Tree) }
"#;

// §10.1 — the declaration lowers and its constructors check, at open
// payloads and open children.
#[test]
fn itree_declares_and_builds() {
    elab(&format!(
        "{ITREE}
         fn ret(n: Nat) -> Tree {{ Ret(n) }}
         fn tau(t: Tree) -> Tree {{ Tau(t) }}
         fn ask(k: Nat -> Tree) -> Tree {{ Vis(Ask, k) }}
         fn say(v: Nat, t: Tree) -> Tree {{ Vis(Say(v), λ f => t) }}
         fn vis(c: Cmd, k: Resp(c) -> Tree) -> Tree {{ Vis(c, k) }}
         fn echo() -> Tree {{ Vis(Ask, λ n => Ret(n)) }}"
    ));
}

/// Recursion through every kind: `first` follows the tree to a leaf, feeding
/// each `Vis` its own command's canonical answer; `rebuild` maps the tree to
/// itself constructor by constructor.
const WALK: &str = r#"
fn answer(c: Cmd) -> Resp(c) { match c { Ask => 7, Say(v) => Yes } }
fn first(t: Tree) -> Nat {
    match t {
        Ret(r) => r,
        Tau(s) => first(s),
        Vis(c, k) => first(k(answer(c))),
    }
}
fn rebuild(t: Tree) -> Tree {
    match t {
        Ret(r) => Ret(r),
        Tau(s) => Tau(rebuild(s)),
        Vis(c, k) => Vis(c, λ x => rebuild(k(x))),
    }
}
"#;

// §10.2 — closed computation through a function child, by `refl`.
#[test]
fn closed_computation_through_k() {
    elab(&format!(
        "{ITREE}{WALK}
         theorem f_ret(): first(Ret(3)) = 3 {{ refl }}
         theorem f_tau(): first(Tau(Tau(Ret(4)))) = 4 {{ refl }}
         theorem f_ask(): first(Vis(Ask, λ n => Ret(Succ(n)))) = 8 {{ refl }}
         theorem f_say(): first(Vis(Say(1), λ b => match b {{ Yes => Ret(1), No => Ret(2) }})) = 1 {{ refl }}
         theorem f_deep(): first(Tau(Vis(Ask, λ n => Tau(Ret(n))))) = 7 {{ refl }}
         theorem r_closed(): first(rebuild(Vis(Ask, λ n => Ret(n)))) = 7 {{ refl }}"
    ));
}

// §10.3 — β on open subterms: the recursion unfolds on a constructor form
// whatever its payload and children are, with `c` and `k` variables.
#[test]
fn beta_fires_on_open_children() {
    elab(&format!(
        "{ITREE}{WALK}
         theorem o_ret(r: Nat): first(Ret(r)) = r {{ refl }}
         theorem o_tau(s: Tree): first(Tau(s)) = first(s) {{ refl }}
         theorem o_vis(c: Cmd, k: Resp(c) -> Tree): first(Vis(c, k)) = first(k(answer(c))) {{ refl }}
         theorem o_rebuild(c: Cmd, k: Resp(c) -> Tree):
             rebuild(Vis(c, k)) = Vis(c, λ x => rebuild(k(x))) {{ refl }}
         theorem o_leaf(r: Nat): rebuild(Ret(r)) = Ret(r) {{ refl }}"
    ));
}

// §10.4 — a dependent motive at every kind, the leaf included, proved by
// induction at a neutral tree. The leaf arm is where `J` carries the user's
// proof from the constructor form to the abstract children (§2.4); the `Vis`
// arm is the ih through `k`, at the argument the recursion chose.
#[test]
fn induction_at_every_kind() {
    elab(&format!(
        "{ITREE}{WALK}
         theorem first_rebuild(t: Tree): first(rebuild(t)) = first(t) {{
             match t {{
                 Ret(r) => refl,
                 Tau(s) => first_rebuild(s),
                 Vis(c, k) => first_rebuild(k(answer(c))),
             }}
         }}"
    ));
}

// §10.5 — a neutral scrutinee does not compute: without a constructor form
// there is nothing for `elim_W` to fire on.
#[test]
fn neutral_scrutinee_is_stuck() {
    let msg = elab_err(&format!(
        "{ITREE}{WALK}
         theorem bad(t: Tree): first(t) = 0 {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// §10.6 — negative controls. Recursion must go through `k`; an equation
// between trees differing only under `k` is not definitional (that would be
// funext); and a false computation is refused.
#[test]
fn a_call_at_a_non_subtree_is_refused() {
    let msg = elab_err(&format!(
        "{ITREE}
         fn answer(c: Cmd) -> Resp(c) {{ match c {{ Ask => 7, Say(v) => Yes }} }}
         fn bad(t: Tree) -> Nat {{
             match t {{ Ret(r) => r, Tau(s) => bad(s), Vis(c, k) => bad(Tau(k(answer(c)))) }}
         }}"
    ));
    assert!(msg.contains("function field applied to an argument"), "{msg}");
    // …and recursion on `k` applied to *anything* is fine: here an argument
    // computed from the payload by another function, and one depending on a
    // second parameter.
    elab(&format!(
        "{ITREE}
         fn pick(c: Cmd, n: Nat) -> Resp(c) {{ match c {{ Ask => Succ(n), Say(v) => No }} }}
         fn ok(t: Tree, n: Nat) -> Nat {{
             match t {{
                 Ret(r) => r,
                 Tau(s) => ok(s, n),
                 Vis(c, k) => ok(k(pick(c, n)), Succ(n)),
             }}
         }}
         theorem ok_two(): ok(Vis(Ask, λ a => Vis(Ask, λ b => Ret(b))), 0) = 2 {{ refl }}"
    ));
}

#[test]
fn rebuild_is_not_definitionally_the_identity() {
    // `rebuild(Vis(c, k)) = Vis(c, λx. rebuild(k x))`, and `rebuild(k x) ≡
    // k x` is an inductive fact, not a definitional one.
    let msg = elab_err(&format!(
        "{ITREE}{WALK}
         theorem bad(c: Cmd, k: Resp(c) -> Tree): rebuild(Vis(c, k)) = Vis(c, k) {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn a_false_equation_under_k_is_refused() {
    let msg = elab_err(&format!(
        "{ITREE}
         theorem bad(): Vis(Ask, λ n => Ret(n)) = Vis(Ask, λ n => Ret(Succ(n))) {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
    // The positive twin: the same children, spelled two ways.
    elab(&format!(
        "{ITREE}
         theorem good(): Vis(Ask, λ n => Ret(n)) = Vis(Ask, λ m => Ret(m)) {{ refl }}"
    ));
}

#[test]
fn a_false_computation_is_refused() {
    let msg = elab_err(&format!(
        "{ITREE}{WALK}
         theorem bad(): first(Vis(Ask, λ n => Ret(n))) = 8 {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// Axis 2 — an **open** element type: the payload is a type parameter, and
// every scheme above is instantiated at a variable `R`.
const PTREE: &str = r#"
inductive Flag { Yes, No }
inductive Cmd { Ask, Say(v: Nat) }
fn Resp(c: Cmd) -> Type { match c { Ask => Nat, Say(v) => Flag } }
fn answer(c: Cmd) -> Resp(c) { match c { Ask => 7, Say(v) => Yes } }
inductive ITree<R> { Ret(r: R), Tau(t: ITree<R>), Vis(c: Cmd, k: Resp(c) -> ITree<R>) }
fn first<R>(t: ITree<R>) -> R {
    match t {
        Ret(r) => r,
        Tau(s) => first(s),
        Vis(c, k) => first(k(answer(c))),
    }
}
fn bind<R, S>(t: ITree<R>, h: R -> ITree<S>) -> ITree<S> {
    match t {
        Ret(r) => h(r),
        Tau(s) => Tau(bind(s, h)),
        Vis(c, k) => Vis(c, λ x => bind(k(x), h)),
    }
}
"#;

#[test]
fn an_open_element_type() {
    elab(&format!(
        "{PTREE}
         theorem p_ret<R>(r: R): first(Ret(r)) = r {{ refl }}
         theorem p_vis<R>(c: Cmd, k: Resp(c) -> ITree<R>): first(Vis(c, k)) = first(k(answer(c))) {{ refl }}
         theorem p_bind_ret<R, S>(r: R, h: R -> ITree<S>): bind(Ret(r), h) = h(r) {{ refl }}
         theorem p_bind_vis<R, S>(c: Cmd, k: Resp(c) -> ITree<R>, h: R -> ITree<S>):
             bind(Vis(c, k), h) = Vis(c, λ x => bind(k(x), h)) {{ refl }}
         theorem p_closed(): first(bind(Vis<Nat>(Ask, λ n => Ret(n)), λ m => Tau(Ret(Succ(m))))) = 8 {{ refl }}
         theorem first_bind<R, S>(t: ITree<R>, h: R -> ITree<S>): first(bind(t, h)) = first(h(first(t))) {{
             match t {{
                 Ret(r) => refl,
                 Tau(s) => first_bind(s, h),
                 Vis(c, k) => first_bind(k(answer(c)), h),
             }}
         }}"
    ));
}

// Shapes beyond the milestone's: no plain child (Brouwer ordinals), and a
// single constructor (no tag case at all — the uninhabited `Inf`).
#[test]
fn ordinals_and_a_single_constructor() {
    elab(
        r#"
        inductive Ord { OZ, OS(o: Ord), Lim(f: Nat -> Ord) }
        fn at0(o: Ord) -> Nat {
            match o { OZ => 0, OS(p) => Succ(at0(p)), Lim(f) => at0(f(2)) }
        }
        fn omega() -> Ord { Lim(λ n => OS(OZ)) }
        theorem at0_omega(): at0(OS(omega())) = 2 {{ refl }}

        inductive Inf { Mk(k: Nat -> Inf) }
        fn never(i: Inf) -> Nat { match i { Mk(k) => never(k(0)) } }
        theorem never_mk(k: Nat -> Inf): never(Mk(k)) = never(k(0)) {{ refl }}
        "#,
    );
}

// §10.6 — every §1 restriction is a rejection with its own message, never a
// lowering.
#[test]
fn the_restrictions_are_diagnosed() {
    let cases: &[(&str, &str)] = &[
        // §1.2: a branching constructor beside a function field.
        ("inductive T { L, N(a: T, b: T), F(k: Nat -> T) }", "more than one recursive field"),
        // §1.4: one arrow.
        ("inductive T { L, F(k: Nat -> Nat -> T) }", "curried"),
        // Strict positivity.
        ("inductive T { L, F(k: T -> Nat) }", "not strictly positive"),
        ("inductive T { L, F(k: T -> T) }", "not strictly positive"),
        // The result is `T` itself, not `T` under another former.
        ("inductive T { L, F(k: Nat -> [T; 2]) }", "under another type"),
        // §1.5: one level for every domain.
        ("inductive T { L, F(k: Nat -> T), G(k: Type -> T) }", "different universe levels"),
        // §1.3: no container beside it.
        ("inductive T { L, C(n: Nat, xs: [T; n]), F(k: Nat -> T) }", "container"),
        // §1.1's "no indexed family" is lifted: an indexed family with a
        // function field lowers on the IWf-on-W route
        // (docs/kernel/iwf-infinitary-design.md, crates/elab/tests/iwf_infinitary.rs).
    ];
    for (src, needle) in cases {
        let msg = elab_err(src);
        assert!(msg.contains(needle), "{src}: {msg}");
    }
}

// A tier-1 declaration is untouched by the new tier: still `Wf`, still
// branching.
#[test]
fn tier1_is_unchanged() {
    elab(
        r#"
        inductive Tree { Leaf, Node(l: Tree, r: Tree) }
        fn size(t: Tree) -> Nat { match t { Leaf => 1, Node(l, r) => Succ(size(l)) } }
        theorem s(): size(Node(Node(Leaf, Leaf), Leaf)) = 3 { refl }
        "#,
    );
}

// §10.7 — no-confusion: `absurd` between constructors of every kind, `inj`
// at a payload field (open and closed), and `inj` at a recursive field
// diagnosed.
#[test]
fn no_confusion() {
    elab(&format!(
        "{ITREE}
         theorem ret_not_tau(r: Nat, s: Tree, p: Ret(r) = Tau(s)): r = 0 {{ absurd(p) }}
         theorem tau_not_vis(s: Tree, c: Cmd, k: Resp(c) -> Tree, p: Tau(s) = Vis(c, k)): s = s {{ absurd(p) }}
         theorem vis_not_ret(c: Cmd, k: Resp(c) -> Tree, r: Nat, p: Vis(c, k) = Ret(r)): r = 0 {{ absurd(p) }}
         fn done(r: Nat) -> Tree {{ Ret(r) }}
         theorem computed_ret_not_tau(r: Nat, s: Tree, p: done(r) = Tau(s)): r = 0 {{ absurd(p) }}
         theorem ret_inj(a: Nat, b: Nat, p: Ret(a) = Ret(b)): a = b {{ inj(p, 0) }}
         theorem vis_say(a: Nat, b: Nat, n: Flag -> Tree, m: Flag -> Tree, p: Vis(Say(a), n) = Vis(Say(b), m)):
             Say(a) = Say(b) {{ inj(p, 0) }}
         theorem vis_cmd(c: Cmd, d: Cmd, k: Resp(c) -> Tree, h: Resp(d) -> Tree, p: Vis(c, k) = Vis(d, h)):
             c = d {{ inj(p, 0) }}"
    ));
    let msg = elab_err(&format!(
        "{ITREE}
         theorem tau_inj(s: Tree, t: Tree, p: Tau(s) = Tau(t)): s = t {{ inj(p, 0) }}"
    ));
    assert!(msg.contains("funext"), "{msg}");
    let msg = elab_err(&format!(
        "{ITREE}
         theorem same(r: Nat, p: Ret(r) = Ret(r)): r = 0 {{ absurd(p) }}"
    ));
    assert!(msg.contains("not absurd"), "{msg}");
}

// The arm binder of a function field reads as the field was written, at the
// arm's own payload — not as the domain's unfolded body.
#[test]
fn a_function_binder_shows_its_written_domain() {
    let src = format!(
        "{ITREE}
         fn hole(t: Tree) -> Nat {{ match t {{ Ret(r) => r, Tau(s) => 0, Vis(c, k) => ? }} }}"
    );
    let mut e = Elaborator::with_prelude().expect("prelude");
    let shown = match e.elab_source(&src) {
        Err(err) => err.render(&src),
        Ok(()) => panic!("the hole should be unsolved"),
    };
    assert!(shown.contains("k : Resp(c) -> Tree"), "{shown}");
}

// The leaf predicate is a generated definition, `D#canon`, registered at the
// all-`Ty 0` profile (docs/inductives/inductive-tier2-w-lowering.md §13). Every test
// above runs through the named spelling; an instance at another profile —
// a tree of types — keeps the inline one, and must build, match, compute and
// refuse exactly as the named one does, beside it in one module.
#[test]
fn both_spellings_of_the_leaf_predicate() {
    const BX: &str = r#"
inductive Bx<R> { Leaf(r: R), Node(k: Nat -> Bx<R>) }
fn leftmost(t: Bx<Type>) -> Type { match t { Leaf(r) => r, Node(k) => leftmost(k(0)) } }
fn depth(t: Bx<Type>) -> Nat { match t { Leaf(_) => 0, Node(k) => Succ(depth(k(0))) } }
fn depthn(t: Bx<Nat>) -> Nat { match t { Leaf(_) => 0, Node(k) => Succ(depthn(k(0))) } }
"#;
    elab(&format!(
        "{BX}
         theorem lm(): leftmost(Node(λ n => Leaf(Nat))) = Nat {{ refl }}
         theorem d_open(k: Nat -> Bx<Type>): depth(Node(k)) = Succ(depth(k(0))) {{ refl }}
         theorem dn_open(k: Nat -> Bx<Nat>): depthn(Node(k)) = Succ(depthn(k(0))) {{ refl }}
         theorem dn_leaf(r: Nat): depthn(Leaf(r)) = 0 {{ refl }}
         theorem d_leaf(r: Type): depth(Leaf(r)) = 0 {{ refl }}"
    ));
    for bad in [
        "theorem bad(): leftmost(Node(λ n => Leaf(Nat))) = (Nat -> Nat) { refl }",
        "theorem bad(): depthn(Node(λ n => Leaf(n))) = 0 { refl }",
    ] {
        let msg = elab_err(&format!("{BX}{bad}"));
        assert!(msg.contains("NotConvertible"), "{msg}");
    }
}
