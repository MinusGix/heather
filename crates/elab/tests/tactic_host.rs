//! Round 1 of `docs/host-elaboration-interface-design.md`: `by t` runs a
//! Heather tactic (`lib/std/tactic.hthr`'s `Tac<Expr>`) or a registered Rust
//! one against the goal, and checks what it returns.
//!
//! The axes of `docs/testing-generated-terms.md`: a closed and a neutral
//! hypothesis, an open element type, a checking position (the goal comes from
//! an annotation or a parameter, not only a statement), and negative controls
//! (no match, a wrong proof, forged references, no goal, no protocol).

use std::cell::OnceCell;

use heather_elab::host::{Answer, NativeTactic, RExpr, Request, Step};
use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("char", include_str!("../../../lib/std/char.hthr")),
    ("string", include_str!("../../../lib/std/string.hthr")),
    ("tactic", include_str!("../../../lib/std/tactic.hthr")),
];

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn elaborator() -> Elaborator {
    BASE.with(|base| base.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator())
}

fn message(error: ElabError) -> String {
    match error {
        ElabError::Elab { msg, .. } => msg,
        other => other.to_string(),
    }
}

fn check_in(mut e: Elaborator, src: &str) {
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
}

fn check(src: &str) {
    check_in(elaborator(), &format!("import tactic;\nimport nat;\n{src}"));
}

fn refused_in(mut e: Elaborator, src: &str) -> String {
    match e.elab_source(src) {
        Err(err) => message(err),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

fn refused(src: &str) -> String {
    refused_in(elaborator(), &format!("import tactic;\nimport nat;\n{src}"))
}

#[test]
fn assumption_closes_goals() {
    check(
        "theorem closed(n: Nat, h: n = 3, q: Nat): n = 3 { by assumption }
         theorem open_type<A>(a: A, b: A, p: a = b, q: b = a): a = b { by assumption }
         theorem neutral(f: Nat → Nat, n: Nat, h: f(n) = n): f(n) = n { by assumption }
         theorem qualified(n: Nat, h: n = 3): n = 3 { by tactic::assumption }",
    );
}

/// The comparison is definitional equality, not syntax: `1 + 1 = 2` is the
/// goal `2 = 2` up to computation.
#[test]
fn assumption_compares_up_to_conversion() {
    check("theorem computed(p: 1 + 1 = 2): 2 = 2 { by assumption }");
}

/// The goal is whatever the position expects: an annotated `let`, and an
/// argument whose parameter type is known.
#[test]
fn checking_positions() {
    check(
        "theorem annotated(n: Nat, h: n = 3): n = 3 { let p: (n = 3) = by assumption; p }
         fn keep(n: Nat, p: n = 3) → n = 3 { p }
         theorem argument(n: Nat, h: n = 3): n = 3 { keep(n, by assumption) }",
    );
}

/// The failure is the tactic's own search state: every local it tried, the
/// most recent first.
#[test]
fn failure_lists_what_was_tried() {
    let msg = refused("theorem none(n: Nat, q: n = 4): n = 3 { by assumption }");
    assert!(msg.contains("`by assumption`: the tactic failed: no local's type is the goal"), "{msg}");
    let q = msg.find("tried q: its type is not the goal").expect(&msg);
    let n = msg.find("tried n: its type is not the goal").expect(&msg);
    assert!(q < n, "{msg}");
}

/// A tactic is a function like any other: composed with `bind`, and written
/// in the client module.
#[test]
fn client_tactics() {
    check(
        "fn twice() → tactic::Tac<tactic::Expr> { assumption().bind(λ e => assumption()) }
         theorem t(n: Nat, h: n = 3): n = 3 { by twice }
         fn spin(k: Nat) → tactic::Tac<tactic::Expr> {
             match k { Zero => assumption(), Succ(j) => defeq(NatLit(0), NatLit(0)).bind(λ g => spin(j)) }
         }
         theorem many(n: Nat, h: n = 3): n = 3 { by spin(300) }",
    );
}

#[test]
fn wrong_results_are_refused_at_the_by() {
    let msg = refused(
        "fn bad() → tactic::Tac<tactic::Expr> { Pure(NatLit(5)) }
         theorem t(n: Nat, h: n = 3): n = 3 { by bad }",
    );
    assert!(msg.contains("the tactic returned a proof of `Nat`, not of the goal `n = 3`"), "{msg}");
    let msg = refused(
        "fn forged() → tactic::Tac<tactic::Expr> { Pure(Local(LocalRef(9))) }
         theorem t(n: Nat, h: n = 3): n = 3 { by forged }",
    );
    assert!(msg.contains("there is no local 9 in this goal"), "{msg}");
    let msg = refused(
        "fn a_type() → tactic::Tac<tactic::Expr> { goal().bind(λ g => Pure(Hd(g.target))) }
         theorem t(n: Nat, h: n = 3): n = 3 { by a_type }",
    );
    assert!(msg.contains("which is not a term"), "{msg}");
    let msg = refused(
        "fn handle() → tactic::Tac<tactic::Expr> { defeq(Hd(Handle(77)), Hd(Handle(0))).bind(λ s => assumption()) }
         theorem t(n: Nat, h: n = 3): n = 3 { by handle }",
    );
    assert!(msg.contains("handle 77 was not issued by this run"), "{msg}");
    let msg = refused(
        "fn applied() → tactic::Tac<tactic::Expr> { Pure(App(NatLit(1), NatLit(2))) }
         theorem t(n: Nat, h: n = 3): n = 3 { by applied }",
    );
    assert!(msg.contains("is applied but is not a function"), "{msg}");
}

#[test]
fn by_needs_a_goal_and_the_protocol() {
    let msg = refused("theorem t(n: Nat, h: n = 3): Nat { let p = by assumption; 0 }");
    assert!(msg.contains("there is none here"), "{msg}");
    let msg = refused_in(elaborator(), "theorem t(n: Nat, h: n = 3): n = 3 { by assumption }");
    assert!(msg.contains("import tactic;"), "{msg}");
    // Round 1 runs a closed tree: an argument naming a local is refused, and
    // the tactic reaches the local through the `Goal` request instead.
    let msg = refused(
        "fn with_fact<P>(p: P) → tactic::Tac<tactic::Expr> { assumption() }
         theorem t(n: Nat, h: n = 3): n = 3 { by with_fact(h) }",
    );
    assert!(msg.contains("cannot mention the goal's locals yet"), "{msg}");
}

/// `by` is recognised only before a name, so a local called `by` still reads
/// as itself.
#[test]
fn a_local_named_by() {
    check("fn f(by: Nat → Nat) → Nat { by(1) + by(2) }");
}

/// A Rust tactic speaking the same protocol (design §8a): `assumption`,
/// written natively.
struct NativeAssumption {
    target: u64,
    locals: Vec<(u64, u64)>,
    tried: Vec<String>,
    names: Vec<String>,
}

impl NativeTactic for NativeAssumption {
    fn start(&mut self) -> Result<Step, String> {
        Ok(Step::Ask(Request::Goal))
    }

    fn resume(&mut self, answer: Answer) -> Result<Step, String> {
        match answer {
            Answer::Goal(g) => {
                self.target = g.target;
                self.locals = g.locals.iter().map(|l| (l.id, l.ty)).collect();
                self.names = g.locals.iter().map(|l| l.name.clone()).collect();
            }
            Answer::Bool(true) => return Ok(Step::Done(RExpr::Local(self.locals[self.tried.len() - 1].0))),
            Answer::Bool(false) => {}
        }
        match self.locals.get(self.tried.len()) {
            Some(&(_, ty)) => {
                self.tried.push(self.names[self.tried.len()].clone());
                Ok(Step::Ask(Request::Defeq(RExpr::Hd(ty), RExpr::Hd(self.target))))
            }
            None => Ok(Step::Ask(Request::Fail(format!("natively tried {}", self.tried.join(", "))))),
        }
    }
}

fn native() -> Box<dyn NativeTactic> {
    Box::new(NativeAssumption { target: 0, locals: vec![], tried: vec![], names: vec![] })
}

#[test]
fn native_tactics_speak_the_same_protocol() {
    let mut e = elaborator();
    e.register_native_tactic("native_assumption", native);
    check_in(
        e.clone(),
        "theorem t<A>(a: A, b: A, p: a = b, q: b = a): a = b { by native_assumption }",
    );
    let msg = refused_in(e.clone(), "theorem t(n: Nat, q: n = 4): n = 3 { by native_assumption }");
    assert!(msg.contains("the tactic failed: natively tried q, n"), "{msg}");
    // A declared name wins over a native tactic of the same name.
    e.register_native_tactic("assumption", native);
    let msg = refused_in(e, "import tactic;\ntheorem t(n: Nat, q: n = 4): n = 3 { by assumption }");
    assert!(msg.contains("no local's type is the goal"), "{msg}");
}
