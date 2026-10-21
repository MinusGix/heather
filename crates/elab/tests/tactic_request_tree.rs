//! Probe for `docs/host-elaboration-interface-design.md` §9: the tactic
//! protocol — a request container (`Req`, `Resp`), the generic request tree
//! `Tac<A>` with its `bind`, and a tactic written against it — is writable
//! and computes in today's surface, with no host at all. The handler here is
//! a Heather function answering from a mock goal, the "Heather implementation
//! of the host" in miniature (§3.3).
//!
//! The axes of `docs/testing-generated-terms.md`: closed runs, a neutral
//! tree and continuation, an open result type, and negative controls.

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

/// The protocol, cut down to what the probe needs: handles are numbers, a
/// hypothesis is named by its position, and `Fail` answers in the empty type
/// so a failure has no continuation by type.
const PROTOCOL: &str = r#"
inductive Flag { Yes, No }
inductive Void { }
record Handle { id: Nat }
inductive Expr { Hd(h: Handle), Local(x: Nat), App(f: Expr, a: Expr) }
record GoalInfo { target: Handle, hyps: Nat }
inductive Req { Goal, HypType(i: Nat), Defeq(a: Expr, b: Expr), Fail(code: Nat) }
fn Resp(r: Req) -> Type {
    match r { Goal => GoalInfo, HypType(_) => Handle, Defeq(_, _) => Flag, Fail(_) => Void }
}
inductive Tac<A> { Pure(a: A), Ask(r: Req, k: Resp(r) -> Tac<A>) }

fn bind<A, B>(t: Tac<A>, f: A -> Tac<B>) -> Tac<B> {
    match t { Pure(a) => f(a), Ask(r, k) => Ask(r, λ x => bind(k(x), f)) }
}
"#;

/// `assumption`, the design's first customer (§5): ask for the goal, then
/// compare each hypothesis's type with it, last hypothesis first.
const ASSUMPTION: &str = r#"
fn scan(target: Handle, i: Nat) -> Tac<Expr> {
    match i {
        Zero => Ask(Fail(0), λ v => match v {}),
        Succ(j) => Ask(HypType(j), λ h => Ask(Defeq(Hd(h), Hd(target)), λ same => match same {
            Yes => Pure(Local(j)),
            No => scan(target, j),
        })),
    }
}
fn assumption() -> Tac<Expr> { Ask(Goal, λ g => scan(g.target, g.hyps)) }
"#;

/// A handler over a mock environment: the goal and each hypothesis are typed
/// by a handle id, and definitional equality is equality of ids. `reply`
/// answers at the request's own response type, or stops; matching on the
/// request inside `run` would not refine the continuation's domain, so the
/// dependent answer is computed by a function whose result type is
/// `Reply<Resp(r)>`.
const HANDLER: &str = r#"
fn nat_eq(a: Nat, b: Nat) -> Flag {
    match a {
        Zero => match b { Zero => Yes, Succ(_) => No },
        Succ(p) => match b { Zero => No, Succ(q) => nat_eq(p, q) },
    }
}
fn expr_id(e: Expr) -> Nat { match e { Hd(h) => h.id, Local(_) => 1000, App(_, _) => 2000 } }
inductive Outcome<A> { Done(a: A), Failed(code: Nat), OutOfFuel }
inductive Reply<R> { Stop(code: Nat), Give(a: R) }
fn reply(goal: Nat, hyps: Nat, ty: Nat -> Nat, r: Req) -> Reply<Resp(r)> {
    match r {
        Goal => Give(GoalInfo(Handle(goal), hyps)),
        HypType(i) => Give(Handle(ty(i))),
        Defeq(a, b) => Give(nat_eq(expr_id(a), expr_id(b))),
        Fail(c) => Stop(c),
    }
}
fn run<A>(fuel: Nat, goal: Nat, hyps: Nat, ty: Nat -> Nat, t: Tac<A>) -> Outcome<A> {
    match fuel {
        Zero => OutOfFuel,
        Succ(f) => match t {
            Pure(a) => Done(a),
            Ask(r, k) => match reply(goal, hyps, ty, r) {
                Stop(c) => Failed(c),
                Give(x) => run(f, goal, hyps, ty, k(x)),
            },
        },
    }
}
fn tys(i: Nat) -> Nat { match i { Zero => 5, Succ(j) => match j { Zero => 7, Succ(_) => 9 } } }
"#;

fn with(body: &str) -> String {
    format!("{PROTOCOL}{ASSUMPTION}{HANDLER}{body}")
}

#[test]
fn closed_runs_compute() {
    elab(&with(
        "theorem finds_middle(): run(10, 7, 3, tys, assumption()) = Done(Local(1)) { refl }
         theorem finds_first(): run(10, 5, 3, tys, assumption()) = Done(Local(0)) { refl }
         theorem fails(): run(10, 8, 3, tys, assumption()) = Failed(0) { refl }
         theorem no_hyps(): run(10, 5, 0, tys, assumption()) = Failed(0) { refl }
         theorem runs_dry(): run(2, 7, 3, tys, assumption()) = OutOfFuel { refl }",
    ));
}

/// `bind` composes a tactic with what follows it, and the handler threads
/// the composite's requests in order. A continuation that only fails fixes
/// no result type, so `then_fail` names it.
#[test]
fn bind_composes() {
    elab(&with(
        "theorem twice(): run(10, 5, 3, tys, bind(assumption(), λ e => Pure(App(e, e))))
             = Done(App(Local(0), Local(0))) { refl }
         theorem then_fail(): run(10, 5, 3, tys, bind<Expr, Expr>(assumption(), λ e => Ask(Fail(3), λ v => match v {})))
             = Failed(3) { refl }",
    ));
}

/// At a neutral tree, continuation and result type: the monad laws that are
/// definitional are definitional, and the handler takes exactly one step per
/// request whatever the continuation is.
#[test]
fn open_trees_and_continuations() {
    elab(&with(
        "theorem bind_pure<A, B>(a: A, f: A -> Tac<B>): bind(Pure(a), f) = f(a) { refl }
         theorem bind_ask<A, B>(r: Req, k: Resp(r) -> Tac<A>, f: A -> Tac<B>):
             bind(Ask(r, k), f) = Ask(r, λ x => bind(k(x), f)) { refl }
         theorem run_pure<A>(n: Nat, g: Nat, h: Nat, ty: Nat -> Nat, a: A):
             run(Succ(n), g, h, ty, Pure(a)) = Done(a) { refl }
         theorem run_goal<A>(n: Nat, g: Nat, h: Nat, ty: Nat -> Nat, k: GoalInfo -> Tac<A>):
             run(Succ(n), g, h, ty, Ask(Goal, k)) = run(n, g, h, ty, k(GoalInfo(Handle(g), h))) { refl }
         theorem run_fail<A>(n: Nat, g: Nat, h: Nat, ty: Nat -> Nat, c: Nat, k: Void -> Tac<A>):
             run(Succ(n), g, h, ty, Ask(Fail(c), k)) = Failed(c) { refl }",
    ));
}

#[test]
fn negative_controls() {
    // A wrong answer is refused.
    let msg = elab_err(&with(
        "theorem wrong(): run(10, 7, 3, tys, assumption()) = Done(Local(0)) { refl }",
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
    // A neutral tree does not run.
    let msg = elab_err(&with(
        "theorem stuck(t: Tac<Expr>): run(10, 7, 3, tys, t) = OutOfFuel { refl }",
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
    // A continuation is applied only at its request's answer type.
    let msg = elab_err(&with("fn bad() -> Tac<Expr> { Ask(Goal, λ (b: Flag) => Pure(Local(0))) }"));
    assert!(!msg.is_empty());
}
