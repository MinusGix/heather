//! Container fields phase 2 (docs/container-fields.md §4.2): recursing into a
//! container's children. This is what makes `Rose` programmable rather than
//! merely declarable.

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

// `map` and `fold` on their own, with no recursion in sight.
#[test]
fn map_and_fold_are_ordinary_vector_operations() {
    elab(&format!(
        "{ADD}
         fn bump(xs: [Nat; 2]) -> [Nat; 2] {{ xs.map(λ (n: Nat) => Succ(n)) }}
         theorem b(): bump([1, 2]) = [2, 3] {{ refl }}

         fn total(xs: [Nat; 3]) -> Nat {{
             xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
         }}
         theorem t(): total([1, 2, 3]) = 6 {{ refl }}

         // and at a variable length, where nothing reduces but it must type
         fn total_n(n: Nat, xs: [Nat; n]) -> Nat {{
             xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
         }}
         theorem t0(): total_n(0, []) = 0 {{ refl }}
         theorem t2(): total_n(2, [4, 5]) = 9 {{ refl }}"
    ));
}

// **The acceptance.** A recursive function over `Rose`, which phase 1 could
// declare and construct but not fold.
#[test]
fn size_over_rose() {
    elab(&format!(
        "{ADD}
         inductive Rose {{ Node(label: Nat, len: Nat, kids: [Rose; len]) }}

         fn size(r: Rose) -> Nat {{
             match r {{
                 Node(label, len, kids) =>
                     Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}

         theorem s_leaf(): size(Node(0, 0, [])) = 1 {{ refl }}
         theorem s_one(): size(Node(0, 1, [Node(1, 0, [])])) = 2 {{ refl }}
         theorem s_two():
             size(Node(0, 2, [Node(1, 0, []), Node(2, 0, [])])) = 3 {{ refl }}
         theorem s_deep():
             size(Node(0, 1, [Node(1, 2, [Node(2, 0, []), Node(3, 0, [])])])) = 4
         {{ refl }}"
    ));
}

// A different fold over the same recursion, so the result is not an artefact
// of one arithmetic: the maximum label depth.
#[test]
fn a_second_recursive_function_over_rose() {
    elab(&format!(
        "{ADD}
         inductive Rose {{ Node(label: Nat, len: Nat, kids: [Rose; len]) }}

         fn sum_labels(r: Rose) -> Nat {{
             match r {{
                 Node(label, len, kids) =>
                     add(label, kids.map(sum_labels).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}

         theorem l0(): sum_labels(Node(5, 0, [])) = 5 {{ refl }}
         theorem l1(): sum_labels(Node(5, 2, [Node(1, 0, []), Node(2, 0, [])])) = 8 {{ refl }}"
    ));
}

// A plain recursive field *and* a container in one constructor: the ih is
// indexed by `Fin (Succ len)`, so the container's indices are offset by one
// and the `inr` shift in `elab_container_ih` is what has to be right.
#[test]
fn a_plain_child_and_a_container_recurse_together() {
    elab(&format!(
        "{ADD}
         inductive T {{
             Tip(Nat),
             Both(first: T, len: Nat, rest: [T; len]),
         }}

         fn total(t: T) -> Nat {{
             match t {{
                 Tip(n) => n,
                 Both(first, len, rest) =>
                     add(total(first), rest.map(total).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}

         theorem t0(): total(Tip(4)) = 4 {{ refl }}
         theorem t1(): total(Both(Tip(1), 0, [])) = 1 {{ refl }}
         theorem t2(): total(Both(Tip(1), 2, [Tip(2), Tip(3)])) = 6 {{ refl }}
         // the plain child and the container must not be confused: an
         // asymmetric tree distinguishes them
         theorem t3(): total(Both(Tip(10), 1, [Tip(1)])) = 11 {{ refl }}"
    ));
}

// The negative controls. `size` is a real recursion, so an open `Rose` does
// not compute, and a wrong closed value is rejected by the kernel.
#[test]
fn the_gate_rejects_wrong_recursions() {
    let base = format!(
        "{ADD}
         inductive Rose {{ Node(label: Nat, len: Nat, kids: [Rose; len]) }}
         fn size(r: Rose) -> Nat {{
             match r {{
                 Node(label, len, kids) =>
                     Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}"
    );
    let m = elab_err(&format!("{base}\ntheorem wrong(): size(Node(0, 0, [])) = 2 {{ refl }}"));
    assert!(m.contains("NotConvertible"), "{m}");
    let m = elab_err(&format!("{base}\ntheorem open(r: Rose): size(r) = 1 {{ refl }}"));
    assert!(m.contains("NotConvertible"), "{m}");
}

#[test]
fn rejections() {
    let d = format!(
        "{ADD}
         inductive Rose {{ Node(label: Nat, len: Nat, kids: [Rose; len]) }}"
    );
    // a self-call over something that is not the container binder
    let m = elab_err(&format!(
        "{d}
         fn size(r: Rose, other: [Rose; 1]) -> Nat {{
             match r {{
                 Node(label, len, kids) =>
                     Succ(other.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}"
    ));
    assert!(m.contains("container field bound by the enclosing"), "{m}");

    // §4.3: a *dependent* result is phase 3
    let m = elab_err(&format!(
        "{d}
         theorem refl_all(r: Rose): r = r {{
             match r {{
                 Node(label, len, kids) => kids.map(refl_all),
             }}
         }}"
    ));
    assert!(m.contains("independent of its argument"), "{m}");
    assert!(m.contains("§4.3"), "{m}");

    // map's receiver has to be a vector
    let m = elab_err("fn f(n: Nat) -> Nat { n.map(λ (x: Nat) => x) }");
    assert!(m.contains("receiver has to be a vector"), "{m}");
}
