//! The canaries under the Merkle substitution (`docs/cache-v1-design.md` §3.2).
//!
//! The rewriter is a state machine over the characters
//! `heather_kernel::fmt::write_exact` emits, and it rests on one assumption
//! about the kernel's printed form: a global reference is `u<digits>`,
//! `U<digits>` or `g<digits>`, and nothing else in `crates/kernel/src/fmt.rs`
//! prints a word-initial `u`/`U`/`g` followed by digits.
//!
//! That assumption is cheap to state and would be silent to break — a missed
//! rewrite leaves a *positional* Ψ index inside a content hash, and positional
//! keys can mean different declarations in different contexts. So it is not
//! left as a comment. These tests are what makes it maintainable: the first
//! two fail if the kernel renames the form, and the third fails if the
//! rewriter starts eating ordinary text.

use std::rc::Rc;

use heather_cache::merkle::{Hash, interface_hash, rewritten_text};
use heather_cache::sha256::{hex, sha256};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type,
};

/// Distinguishable stand-in hashes for a Ψ prefix.
fn prefix(n: usize) -> Vec<Option<Hash>> {
    (0..n).map(|i| Some(sha256(format!("binding-{i}").as_bytes()))).collect()
}

fn id_subst() -> LocalSubst {
    LocalSubst { tail: SubstTail::Empty { len: 0, base: CtxBase::Nil }, terms: Vec::new() }
}

/// `u<k>` — a term-level global reference.
fn global_tm(k: u32) -> Term {
    Term::GlobalTm { var: GlobalVar(k), subst: id_subst() }
}

/// `U<k>` — a type-level global reference.
fn global_ty(k: u32) -> Type {
    Type::GlobalTy { var: GlobalVar(k), subst: id_subst() }
}

/// Every spelling of a global reference is rewritten, and none survives.
///
/// If the kernel renames `u`/`U`/`g`, or prints an index some other way, this
/// is the test that says so.
#[test]
fn rewrites_every_global_spelling() {
    let p = prefix(4);
    let len = p.len() as u32;

    // A term mentioning a term global, a type global, and a context-variable
    // base — the three productions in `crates/kernel/src/fmt.rs` that carry a
    // `GlobalVar`.
    let ctx = LocalCtx { base: CtxBase::Var(GlobalVar(2)), entries: Default::default() };
    let t = Term::App {
        fun: Rc::new(global_tm(0)),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::new(global_ty(1)),
        cod: Rc::new(Type::CodeTy { ctx, level: Level::Zero }),
        arg: Rc::new(Term::Zero),
    };

    let raw = format!("{t:?}");
    assert!(raw.contains("u0^"), "the fixture must contain a term global: {raw}");
    assert!(raw.contains("U1^"), "the fixture must contain a type global: {raw}");
    assert!(raw.contains("g2"), "the fixture must contain a context global: {raw}");

    let out = rewritten_text(&p, len, &t).expect("every reference resolves");
    for (marker, k) in [("u", 0u32), ("U", 1), ("g", 2)] {
        let referent = hex(&p[(len - 1 - k) as usize].expect("set"));
        assert!(
            out.contains(&format!("{marker}{referent}")),
            "`{marker}{k}` was not replaced by its referent's hash:\n{out}"
        );
    }
    // And no positional index survives anywhere.
    for marker in ['u', 'U', 'g'] {
        assert!(!leaks(&out, marker), "a positional `{marker}` index survived:\n{out}");
    }
}

/// Is there a `<marker><digits>` in `s` that is *not* the 64-hex-digit
/// substitution? A rewritten reference is a marker followed by 64 hex
/// characters; a surviving positional index is a marker followed by digits and
/// then something else.
fn leaks(s: &str, marker: char) -> bool {
    let b: Vec<char> = s.chars().collect();
    for i in 0..b.len() {
        if b[i] != marker {
            continue;
        }
        if i > 0 && b[i - 1].is_ascii_alphanumeric() {
            continue;
        }
        let run: String = b[i + 1..].iter().take_while(|c| c.is_ascii_hexdigit()).collect();
        if run.chars().next().is_some_and(|c| c.is_ascii_digit()) && run.len() != 64 {
            return true;
        }
    }
    false
}

/// The property the rewriter exists for: a declaration's hash does not depend
/// on where in Ψ it (or its referents) happen to sit.
///
/// Two prefixes of different lengths, the same referent hash at the position
/// the reference resolves to, the same declaration — one hash. A positional
/// key would give two.
#[test]
fn the_same_declaration_at_two_positions_agrees() {
    let referent = sha256(b"the referent");
    // Ψ of length 3 with the referent last, and Ψ of length 9 with the
    // referent last. `u0` means "the last binding" in both.
    let short: Vec<Option<Hash>> = {
        let mut v = prefix(2);
        v.push(Some(referent));
        v
    };
    let long: Vec<Option<Hash>> = {
        let mut v = prefix(8);
        v.push(Some(referent));
        v
    };

    let binding = |_| GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: Rc::new(Type::El { level: Level::Zero, tm: Rc::new(global_tm(0)) }),
        level: Level::Zero,
        body: None,
    };

    assert_eq!(
        interface_hash(&short, &binding(())),
        interface_hash(&long, &binding(())),
        "the same declaration hashed differently at two Ψ positions — the \
         Merkle substitution is not firing (see this file's module docs)"
    );
    assert!(interface_hash(&short, &binding(())).is_some());
}

/// The rewriter must not eat ordinary text: the kernel's output is full of
/// `u`, `U` and `g` characters that are not references.
#[test]
fn unrelated_text_is_not_rewritten() {
    let p = prefix(2);
    // `sup` (a `u` inside a word), `Unit 0` (a `U` before a letter), `⟨⟩0`,
    // and a `wk^n_g` substitution tail are the shapes most likely to trip a
    // naive scan.
    let t = Term::Pair {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: Rc::new(Type::Unit { level: Level::Zero }),
        snd_ty: Rc::new(Type::Nat),
        fst: Rc::new(Term::Triv { level: Level::Zero }),
        snd: Rc::new(Term::Succ(Rc::new(Term::Zero))),
    };
    let raw = format!("{t:?}");
    assert!(raw.contains("Unit 0"), "fixture: {raw}");
    let out = rewritten_text(&p, p.len() as u32, &t).expect("no references at all");
    assert_eq!(out, raw, "text with no global references must pass through unchanged");
}

/// Fail closed: a reference outside the known prefix yields no hash at all,
/// rather than a hash of something else.
#[test]
fn an_unresolvable_reference_is_not_hashable() {
    let p = prefix(2);
    let t = global_tm(7); // far beyond a two-binding Ψ
    assert!(rewritten_text(&p, p.len() as u32, &t).is_none());

    let poisoned: Vec<Option<Hash>> = vec![None, Some(sha256(b"fine"))];
    // `u1` resolves to index 0, which is poisoned.
    assert!(rewritten_text(&poisoned, 2, &global_tm(1)).is_none(), "poison propagates");
    assert!(rewritten_text(&poisoned, 2, &global_tm(0)).is_some(), "and only propagates");
}

/// A theorem's interface must not depend on its proof, and a `fn`'s must
/// depend on its body. This is the interface split of
/// `issues/parallel-checking-and-caching.md` at the level of one hash — the
/// end-to-end consequence is in `tests/end_to_end.rs`.
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
