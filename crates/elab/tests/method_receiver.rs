//! The `self` marker: which parameter a method call's receiver fills.
//! Tracking issue: `issues/method-receiver-position.md`.
//!
//! `x.f(a)` used to append the receiver, so a two-premise lemma inverted —
//! `p.trans(q)` meant `trans(q, p)`. The receiver now fills the callee's
//! `self` parameter, defaulting to the first explicit one. Every positive
//! test here is kernel-checked, so a receiver landing in the wrong hole is a
//! rejection rather than a passing test: the two premises of `trans` have
//! *different* types, and `cong`'s do too.

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

// -- 1: the default -------------------------------------------------------

// The unmarked case, which is every declaration that predates the marker.
// `trans` is the lemma the issue was filed over: the prelude declares it
// `(p, q)`, so subject-first makes the method spelling read forward.
#[test]
fn the_receiver_defaults_to_the_first_explicit_parameter() {
    ok("theorem forward(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c {
            p.trans(q)
        }");
}

// The inversion, now an error. Worth a test of its own: it is the *only*
// thing that tells first from last, and its absence is why the old
// convention survived (the justification in `parser.rs` cited two unary
// examples, where the two positions coincide).
#[test]
fn the_old_backwards_spelling_is_now_rejected() {
    let e = bad("theorem backwards(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c {
                     q.trans(p)
                 }");
    // The receiver is `q : b = c`, so `trans` wants `c = _` next, and `p : a = b`
    // is not that. The argument is the first site that fails, so it is the one
    // reported (issues/implicit-argument-mismatch-reaches-kernel.md); before
    // arguments owed their comparison, the result's `b = b` against `a = c`
    // was (issues/check-fallback-discards-expected-type.md).
    assert!(e.contains("this has type `a = b`, but `c = b` is expected here"), "{e}");
}

// A unary lemma is indifferent to the whole question, and must stay free of
// ceremony — that is the argument for defaulting rather than requiring.
#[test]
fn a_unary_lemma_needs_no_marker() {
    ok("theorem s(a: Nat, b: Nat, p: a = b): b = a { p.sym() }");
}

// -- 2: the marker --------------------------------------------------------

// `cong` is why the marker exists: its subject is the *last* parameter,
// because `f` reads better first, so it is a counterexample to both fixed
// orders. Marking `p` lets the method and direct spellings coexist, and the
// direct one is unchanged — `self` is call-site sugar only.
#[test]
fn a_marked_subject_can_be_last() {
    ok("theorem cong(f: Nat -> Nat, {a: Nat}, {b: Nat}, self p: a = b): f(a) = f(b) {
            j(p, λ y q => f(a) = f(y), refl)
        }
        theorem method(a: Nat, b: Nat, p: a = b): Succ(a) = Succ(b) { p.cong(Succ) }
        theorem direct(a: Nat, b: Nat, p: a = b): Succ(a) = Succ(b) { cong(Succ, p) }");
}

// The counting subtlety in `subject_index`: the receiver is inserted into the
// *written* argument list, so the position is counted over explicit
// parameters only. `cong` above already has two implicits before its `self`;
// this puts them on both sides of it, so an off-by-one that happened to
// cancel there would show up here.
#[test]
fn implicits_do_not_shift_the_subject_position() {
    ok("theorem mid({a: Nat}, f: Nat -> Nat, {b: Nat}, self p: a = b, {c: Nat}, r: b = c):
            f(a) = f(b)
        { j(p, λ y q => f(a) = f(y), refl) }
        theorem method(a: Nat, b: Nat, c: Nat, p: a = b, r: b = c): Succ(a) = Succ(b) {
            p.mid(Succ, r)
        }");
}

// A marker on a *middle* parameter, so the receiver is neither prepended nor
// appended. Nothing needs this yet; it is here because the mechanism allows
// it and an insertion that only handled the ends would pass everything else.
#[test]
fn a_marked_subject_can_be_in_the_middle() {
    ok("fn add(a: Nat, b: Nat) -> Nat { match a { Zero => b, Succ(k) => Succ(add(k, b)) } }
        fn pick(a: Nat, self b: Nat, c: Nat) -> Nat { add(add(a, b), c) }
        theorem lands_in_the_middle(n: Nat): n.pick(1, 3) = pick(1, n, 3) { refl }");
}

// `self: T` names the parameter as well, for the record-method case where
// Rust's spelling is the natural one. Also the reason there is no third
// reading: a parameter merely *named* `self` would otherwise be a silent
// non-subject.
#[test]
fn self_alone_marks_and_names() {
    ok("record Counter { n: Nat }
        fn bump(self: Counter) -> Nat { Succ(self.n) }
        theorem method(c: Counter): c.bump() = Succ(c.n) { refl }
        theorem direct(c: Counter): bump(c) = Succ(c.n) { refl }");
}

// The mark may sit inside a run of names sharing one annotation
// (`issues/modifiers-in-shared-binder-runs.md`): a modifier prefixes exactly
// one name — the one it is written on — and the annotation is the only thing
// the run shares. So `self b, c: Nat` is the same declaration as
// `self b: Nat, c: Nat`, receiver position included.
#[test]
fn a_marked_subject_may_be_a_name_inside_a_shared_run() {
    ok("fn add(a: Nat, b: Nat) -> Nat { match a { Zero => b, Succ(k) => Succ(add(k, b)) } }
        fn pick(a: Nat, self b, c: Nat) -> Nat { add(add(a, b), c) }
        theorem lands_in_the_middle(n: Nat): n.pick(1, 3) = pick(1, n, 3) { refl }");
    // …and the mark reaches its own name only: `c` is an ordinary parameter,
    // so the receiver is still the second slot and not the third.
    ok("fn snd(self a, b: Nat) -> Nat { b }
        theorem receiver_is_a(n: Nat): n.snd(3) = snd(n, 3) { refl }");
}

// -- 3: rejections --------------------------------------------------------

#[test]
fn at_most_one_self() {
    let e = bad("fn f(self a: Nat, self b: Nat) -> Nat { a }");
    assert!(e.contains("at most one `self`"), "{e}");
    assert!(e.contains("`a` is already it"), "{e}");
    // The run form does not open a second door: the scan sees the group it is
    // standing in, whose names are not parameters yet.
    let e = bad("fn g(self a, self b: Nat) -> Nat { a }");
    assert!(e.contains("at most one `self`"), "{e}");
    assert!(e.contains("`a` is already it"), "{e}");
}

// An implicit parameter has no argument slot, so there is nowhere for the
// receiver to land.
#[test]
fn self_may_not_be_implicit() {
    let e = bad("theorem t({self a: Nat}, p: a = a): a = a { p }");
    assert!(e.contains("cannot be implicit"), "{e}");
}

// Same reason, one layer up: type arguments are never passed at a call site
// (`issues/at-and-type-arguments.md`).
#[test]
fn self_may_not_be_a_type_parameter() {
    let e = bad("fn id<self>(x: self) -> self { x }");
    assert!(e.contains("type parameter cannot be `self`"), "{e}");
}

// -- 4: the built-ins -----------------------------------------------------

// `map`/`fold`/`inj` are Rust rather than declarations, so they have no
// `self` to write and take the default: receiver first, in *both* spellings.
// `inj`'s direct spelling moved to match (tier-0 §6.3) — that divergence was
// the entire obstacle the prototype measured.
#[test]
fn the_builtins_take_the_receiver_first() {
    ok("inductive Pair { Both(x: Nat, y: Nat) }
        theorem by_method(a: Nat, b: Nat, p: Both(0, a) = Both(0, b)): a = b { p.inj(1) }
        theorem by_call(a: Nat, b: Nat, p: Both(0, a) = Both(0, b)): a = b { inj(p, 1) }");
}

#[test]
fn the_vector_eliminators_take_the_receiver_first() {
    ok("fn add(a: Nat, b: Nat) -> Nat { match a { Zero => b, Succ(k) => Succ(add(k, b)) } }
        fn doubled(xs: [Nat; 2]) -> [Nat; 2] { map(xs, λ (x: Nat) => add(x, x)) }
        fn total(xs: [Nat; 2]) -> Nat { fold(xs, 0, add) }
        theorem maps(): doubled([1, 2]) = [2, 4] { refl }
        theorem folds(): total([1, 2]) = 3 { refl }");
}
