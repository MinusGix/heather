//! Container fields (docs/container-fields.md), phase 1: `Rose` declares,
//! constructs, and its arm binds the children as a vector.

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

const ROSE: &str = r#"
inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }
"#;

// §8.3–4 — the declaration lowers, and constructors check at both a zero and
// a nonzero length, with open children.
#[test]
fn rose_declares_and_builds() {
    elab(&format!(
        "{ROSE}
         fn leaf(n: Nat) -> Rose {{ Node(n, 0, []) }}
         fn one(t: Rose) -> Rose {{ Node(0, 1, [t]) }}
         fn two(a: Rose, b: Rose) -> Rose {{ Node(0, 2, [a, b]) }}
         fn deep(t: Rose) -> Rose {{ Node(0, 2, [Node(1, 0, []), t]) }}"
    ));
}

// **The observer.** If the container field were dropped from the encoding —
// which is exactly what happened while this was being written, because
// `recursive` was computed from the *plain* child count and a container-only
// constructor has none — then two nodes differing only in their children
// would be definitionally equal, and `Rose` would be a type nobody wrote.
//
// Nothing above catches that: every positive test still passes against the
// dropped encoding. Only a negative control does.
#[test]
fn a_container_is_not_dropped() {
    let msg = elab_err(&format!(
        "{ROSE}
         theorem collapsed(a: Rose, b: Rose):
             Node(0, 1, [a]) = Node(0, 1, [b]) {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");

    // `inj` at the container field is *not* phase 1, and says so rather than
    // mis-deriving: the field's type depends on the length before it (§6).
    let msg = elab_err(&format!(
        "{ROSE}
         theorem kids_inj(a: [Rose; 1], b: [Rose; 1], p: Node(0, 1, a) = Node(0, 1, b)):
             a = b {{ inj(p, 2) }}"
    ));
    assert!(msg.contains("container field"), "{msg}");
    assert!(msg.contains("definitionally equal"), "{msg}");
}

// §8.5 — the arm binds `kids` as a real `[Rose; n]` value: it can be
// returned, which is the thing an accessor-or-fold design would not allow.
#[test]
fn an_arm_binds_the_children_as_a_vector() {
    elab(&format!(
        "{ROSE}
         fn label(r: Rose) -> Nat {{
             match r {{ Node(l, n, kids) => l }}
         }}
         theorem l0(): label(Node(7, 0, [])) = 7 {{ refl }}
         theorem l1(t: Rose): label(Node(7, 1, [t])) = 7 {{ refl }}

         fn arity(r: Rose) -> Nat {{
             match r {{ Node(l, n, kids) => n }}
         }}
         theorem a2(a: Rose, b: Rose): arity(Node(0, 2, [a, b])) = 2 {{ refl }}"
    ));
}

// The container binder round-trips: `match` it out and put it straight back,
// and the result is convertible with the original — β on an *open* node,
// which is the property §8.1 of the tier-1 doc says a `List`-based lowering
// would lose.
#[test]
fn the_children_vector_round_trips() {
    elab(&format!(
        "{ROSE}
         fn rebuild(r: Rose) -> Rose {{
             match r {{ Node(l, n, kids) => Node(l, n, kids) }}
         }}
         theorem closed(): rebuild(Node(3, 0, [])) = Node(3, 0, []) {{ refl }}
         theorem open_one(t: Rose): rebuild(Node(3, 1, [t])) = Node(3, 1, [t]) {{ refl }}
         theorem open_two(a: Rose, b: Rose):
             rebuild(Node(3, 2, [a, b])) = Node(3, 2, [a, b]) {{ refl }}"
    ));
}

// §8.6 — a plain recursive field *and* a container in one constructor. This
// is what the `Succ`-headed arity of §3.3 exists for: `Vec` unfolds once for
// the plain child and leaves the container as the tail.
#[test]
fn a_plain_child_and_a_container_together() {
    elab(
        r#"
        inductive T {
            Tip(Nat),
            Both(first: T, len: Nat, rest: [T; len]),
        }

        fn head_label(t: T) -> Nat {
            match t {
                Tip(n) => n,
                Both(first, len, rest) => head_label(first),
            }
        }

        theorem h0(): head_label(Tip(4)) = 4 { refl }
        theorem h1(): head_label(Both(Tip(5), 0, [])) = 5 { refl }
        theorem h2(x: T): head_label(Both(Tip(5), 1, [x])) = 5 { refl }

        // the container binder is still the tail, with a plain child in front
        fn rebuild(t: T) -> T {
            match t {
                Tip(n) => Tip(n),
                Both(f, len, rest) => Both(f, len, rest),
            }
        }
        theorem r2(a: T, b: T): rebuild(Both(a, 1, [b])) = Both(a, 1, [b]) { refl }
        "#,
    );
}

// §8.8 — no-confusion still works on a declaration with a container field.
#[test]
fn no_confusion_with_a_container() {
    elab(
        r#"
        inductive T { Tip(Nat), Node(len: Nat, kids: [T; len]) }

        theorem distinct(n: Nat, k: Nat, xs: [T; k]):
            Tip(n) = Node(k, xs) -> Nat
        { λ (p: Tip(n) = Node(k, xs)) => absurd(p) }

        theorem tip_inj(a: Nat, b: Nat, p: Tip(a) = Tip(b)): a = b { inj(p) }
        "#,
    );
}

// §8.9 — the rejections.
#[test]
fn rejections() {
    let m = elab_err("inductive R { N(a: Nat, b: Nat, x: [R; a], y: [R; b]) }");
    assert!(m.contains("more than one container field"), "{m}");

    let m = elab_err("inductive R { N(len: Nat, xs: [R; len], t: R) }");
    assert!(m.contains("may not follow a container field"), "{m}");

    let m = elab_err("inductive R { N(len: Nat, xs: [R; 2]) }");
    assert!(m.contains("must be the name of a `Nat` field"), "{m}");

    let m = elab_err("inductive R { N(xs: [R; len]) }");
    assert!(m.contains("declared before this one"), "{m}");

    // the length must come *before* the container
    let m = elab_err("inductive R { N(xs: [R; len], len: Nat) }");
    assert!(m.contains("declared before this one"), "{m}");
}
