//! Surface coverage for propositional truncation.

use heather_elab::{ElabError, Elaborator};

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected rejection"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
    }
}

#[test]
fn both_squash_type_spellings_and_introduction_check() {
    ok("fn a(n: Nat) -> ∥Nat∥ { squash(n) }");
    ok("fn b(n: Nat) -> Squash<Nat> { squash(n) }");
    ok("fn inferred(n: Nat) -> ∥Nat∥ { let q = squash(n); q }");
    ok("fn unicode_code() -> Type { ∥Nat∥ }");
    ok("fn ascii_code() -> Type { Squash<Nat> }");
}

#[test]
fn dependent_squash_elimination_computes() {
    ok(r#"
fn map_squash(q: ∥Nat∥) -> ∥Nat∥ {
    squash_ind(q, λ z => Nat, λ x => squash(Succ(x)))
}
theorem beta(): map_squash(squash(0)) = squash(1) { refl }
"#);
}

#[test]
fn squash_elimination_cannot_return_unsquashed_data() {
    let msg = bad(r#"
fn release(q: ∥Nat∥) -> Nat {
    squash_ind(q, λ z => Nat, λ x => x)
}
"#);
    assert!(
        msg.contains("squash") || msg.contains("expected") || msg.contains("NotConvertible"),
        "{msg}"
    );
}
