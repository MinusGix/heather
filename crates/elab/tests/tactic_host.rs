//! Rounds 1 and 2 of `docs/host-elaboration-interface-design.md`: `by t` runs
//! a Heather tactic (`lib/std/tactic/tactic.hthr`'s `Tac<Expr>`) or a registered Rust
//! one against the goal, and checks what it returns. Round 2 adds binders
//! (`Open`, `Lam`), `Infer` and `Resolve`, quoting of hypotheses into `Expr`
//! arguments, and the library's `exact`, `intro`, `apply` and `first_of`.
//! Round 2½ adds `View`, `Whnf`, and `Match`, through which `apply` solves
//! the parameters its conclusion determines, implicit ones included. Round 3
//! adds holes shared across premises (`Hole`, undone by `Mark`/`Restore`),
//! global references (`Lookup`, `Global`) and notes about terms (`At`).
//!
//! The axes of `docs/testing-generated-terms.md`: a closed and a neutral
//! hypothesis, an open element type, a checking position (the goal comes from
//! an annotation or a parameter, not only a statement), and negative controls
//! (no match, a wrong proof, forged references, no goal, no protocol).

use std::sync::OnceLock;

use heather_elab::host::{Answer, NativeTactic, RExpr, Request, Step};
use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("tactic", include_str!("../../../lib/std/tactic/tactic.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn elaborator() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
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

/// `Say`: what a run says about itself is one `tactic-report` warning at the
/// `by`, rendered as a failure's notes are, and only once the run's result
/// is the goal's proof. A run that says something and then fails reports
/// only its failure.
#[test]
fn say_reports_only_a_run_that_succeeds() {
    let mut e = elaborator();
    let src = "import tactic;\nimport nat;\nimport list;\nimport string;\n
         fn told() → tactic::Tac<tactic::Expr> {
             say(\"used h\", [Tried(\"twice\", \"the same\")]).bind(λ _ => say(\"and again\", []).bind(λ _ => assumption()))
         }
         theorem t(n: Nat, h: n = 3): n = 3 { by told }";
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    let warnings = e.take_warnings();
    assert_eq!(warnings.len(), 1, "one warning per run");
    assert_eq!(warnings[0].lint, heather_elab::Lint::TacticReport);
    assert_eq!(warnings[0].msg, "`by told`: used h\n  tried twice: the same\nand again");
    let mut e = elaborator();
    let failing = "import tactic;\nimport nat;\nimport list;\nimport string;\n
         fn told() → tactic::Tac<tactic::Expr> { say(\"used h\", []).bind(λ _ => assumption()) }
         theorem t(n: Nat, h: n = 4): n = 3 { by told }";
    let msg = message(e.elab_source(failing).expect_err("the run fails"));
    assert!(msg.contains("no local's type is the goal"), "{msg}");
    assert!(e.take_warnings().is_empty(), "a failed run says nothing else");
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
    assert!(msg.contains("there is no local 9 in this run"), "{msg}");
    let msg = refused(
        "fn a_type() → tactic::Tac<tactic::Expr> { goal().bind(λ g => Pure(Hd(g.target))) }
         theorem t(n: Nat, h: n = 3): n = 3 { by a_type }",
    );
    // A type handle where a term is expected stands for its code, which is
    // a term of a universe and so no proof of the goal.
    assert!(msg.contains("the tactic returned a proof of `Type<0>`, not of the goal `n = 3`"), "{msg}");
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
    // The tree is closed apart from what is quoted: an argument naming a
    // local where the tactic does not expect an `Expr` is refused, and the
    // tactic reaches the local through the `Goal` request instead.
    let msg = refused(
        "fn with_fact<P>(p: P) → tactic::Tac<tactic::Expr> { assumption() }
         theorem t(n: Nat, h: n = 3): n = 3 { by with_fact(h) }",
    );
    assert!(msg.contains("can mention the goal's locals only where it expects an `Expr`"), "{msg}");
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
            other => return Err(format!("an answer to a request it did not make: {other:?}")),
        }
        match self.locals.get(self.tried.len()) {
            Some(&(_, ty)) => {
                self.tried.push(self.names[self.tried.len()].clone());
                Ok(Step::Ask(Request::Defeq(RExpr::Hd(ty), RExpr::Hd(self.target))))
            }
            None => Ok(Step::Ask(Request::Fail(format!("natively tried {}", self.tried.join(", ")), Vec::new()))),
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

/// A run is not limited by the length of its conversation
/// (issues/tactic-run-continuation-chain.md): a resumed tree's proof is the
/// previous tree's applied, and the host pins each one as it is made, so
/// reading the result after thousands of answers is as shallow as after one.
/// Past the old ceiling (about a thousand) at both kinds of request, with
/// each continuation using its answer, ending in a result and in a failure.
#[test]
fn long_runs() {
    check(
        "fn walk(k: Nat, t: Handle) → tactic::Tac<tactic::Expr> {
             match k {
                 Zero => assumption(),
                 Succ(j) => goal().bind(λ g => defeq(Hd(g.target), Hd(t)).bind(λ same => match same {
                     True => walk(j, g.target),
                     False => Pure(NatLit(0)),
                 })),
             }
         }
         theorem many(n: Nat, h: n = 3): n = 3 { by walk(1500, Handle(0)) }",
    );
    let msg = refused(
        "fn spin(k: Nat) → tactic::Tac<tactic::Expr> {
             match k { Zero => assumption(), Succ(j) => defeq(NatLit(0), NatLit(0)).bind(λ g => spin(j)) }
         }
         theorem late(n: Nat, q: n = 4): n = 3 { by spin(1500) }",
    );
    assert!(msg.contains("the tactic failed: no local's type is the goal"), "{msg}");
    assert!(msg.contains("tried q: its type is not the goal"), "{msg}");
    // A run under a `bind`: the tree the host pins is the bind's, and the
    // inner run's proof is read through one `match` alias per answered
    // request, a chain the final `Pure`'s `J` forces whole. Each link used to
    // cost a native re-entry, so this failed past about 2000 requests
    // (issues/grind-unrelated-lemma-fuel.md); the machine now forces a
    // variable head on its own loop (docs/native-depth-budget-design.md §9).
    check(
        "fn spin(k: Nat) → tactic::Tac<tactic::Expr> {
             match k { Zero => assumption(), Succ(j) => defeq(NatLit(0), NatLit(0)).bind(λ g => spin(j)) }
         }
         theorem under(n: Nat, h: n = 3): n = 3 { by spin(3000).bind(λ e => pure(e)) }",
    );
    // The conversation itself is still bounded.
    let msg = refused(
        "fn spin(k: Nat) → tactic::Tac<tactic::Expr> {
             match k { Zero => assumption(), Succ(j) => defeq(NatLit(0), NatLit(0)).bind(λ g => spin(j)) }
         }
         theorem t(n: Nat, h: n = 3): n = 3 { by spin(10500) }",
    );
    assert!(msg.contains("the tactic made more than 10000 requests without finishing"), "{msg}");
}

/// Binds nested to the left (issues/tier2-left-nested-bind-cost.md): "the
/// first `j` steps, then one more". Each level of `bind` used to evaluate the
/// tree below it once for the tree and once for its proof, so the run cost
/// `2^d` in the depth and `lspin(14)` ran out of fuel. Now the halves share
/// one evaluation of the child (`shared_apps` counts the kernel's part) and
/// the run is quadratic: forty levels, two requests each, then the
/// assumption. A failure at the bottom of the nest is still reported.
#[test]
fn left_nested_runs() {
    let tick = "fn tick() → tactic::Tac<tactic::Expr> { defeq(NatLit(0), NatLit(0)).bind(λ g => assumption()) }
         fn lspin(k: Nat) → tactic::Tac<tactic::Expr> {
             match k { Zero => assumption(), Succ(j) => lspin(j).bind(λ e => tick()) }
         }";
    let before = heather_kernel::stats::snapshot();
    check(&format!("{tick}\ntheorem deep(n: Nat, h: n = 3): n = 3 {{ by lspin(40) }}"));
    let shared = heather_kernel::stats::snapshot().since(&before).shared_apps;
    assert!(shared > 0, "the function child's halves did not share an evaluation");
    let msg = refused(&format!("{tick}\ntheorem bad(n: Nat, q: n = 4): n = 3 {{ by lspin(40) }}"));
    assert!(msg.contains("the tactic failed: no local's type is the goal"), "{msg}");
}

/// `intro` opens the goal's binder, proves the body under the new local, and
/// abstracts it: a non-dependent and a dependent binder, an open type, and
/// binders under hypotheses.
#[test]
fn intro_opens_binders() {
    check(
        "theorem implication(n: Nat, q: n = 2): n = 1 → n = 2 { by intro(assumption()) }
         theorem itself(n: Nat): n = 1 → n = 1 { by intro(assumption()) }
         theorem dependent(): (n: Nat) → n = 1 → n = 1 { by intro(intro(assumption())) }
         theorem open_type<A>(a: A, b: A): a = b → b = a → a = b { by intro(intro(assumption())) }",
    );
    let msg = refused("theorem t(n: Nat, h: n = 1): n = 1 { by intro(assumption()) }");
    assert!(msg.contains("intro: `n = 1` is not a function type"), "{msg}");
}

/// Where a tactic's parameter is an `Expr`, a term of the goal's context is
/// quoted: a hypothesis, a local of a data type, and an application of
/// hypotheses. `exact` checks the quoted term's type against the goal.
#[test]
fn exact_quotes_hypotheses() {
    check(
        "theorem hypothesis(n: Nat, p: n = 3): n = 3 { by exact(p) }
         theorem data(n: Nat): Nat { by exact(n) }
         theorem applied(a: Nat, h: a = 1 → a = 2, p: a = 1): a = 2 { by exact(h(p)) }",
    );
    let msg = refused("theorem t(a: Nat, p: a = 1): a = 2 { by exact(p) }");
    assert!(msg.contains("exact: the term's type is not the goal"), "{msg}");
    // A term of the tactic expression's own binders is not the goal's, so
    // it cannot be quoted.
    let msg = refused("theorem t(a: Nat, p: a = 1): a = 1 { by goal().bind(λ g => exact(g)) }");
    assert!(msg.contains("mentions a local of the tactic expression"), "{msg}");
}

/// The milestone's check (design §10, R2): a Heather `apply` closes an
/// implication chain. Premises are proved left to right by the premise
/// tactic, a later one may depend on an earlier one, and a recursive client
/// tactic searches by `first_of` over `assumption` and `apply` of each local.
#[test]
fn apply_closes_implication_chains() {
    check(
        "import list;
         theorem chain(a: Nat, b: Nat, h1: a = 1 → b = 2, h2: b = 2 → a = b, p: a = 1): a = b {
             by apply(h2, apply(h1, assumption()))
         }
         theorem two(a: Nat, f: a = 1 → a = 2 → a = 3, p: a = 1, q: a = 2): a = 3 { by apply(f, assumption()) }
         theorem dependent(a: Nat, f: (m: Nat) → m = 1 → m = 2, p: a = 1): a = 2 { by apply(f, assumption()) }
         theorem none_needed(a: Nat, p: a = 1): a = 1 { by apply(p, assumption()) }
         fn auto(d: Nat) → tactic::Tac<tactic::Expr> {
             match d {
                 Zero => assumption(),
                 Succ(e) => first_of([assumption(), goal().bind(λ g => first_of(g.locals.map(λ l => apply(Local(l.ref), auto(e)))))]),
             }
         }
         theorem searched(a: Nat, b: Nat, c: Nat, h1: a = 1 → b = 2, h2: b = 2 → c = 3, p: a = 1): c = 3 { by auto(3) }",
    );
    let msg = refused("theorem t(a: Nat): a = 1 → a = 1 { by apply(a, assumption()) }");
    assert!(msg.contains("apply: no number of arguments makes the conclusion of `Nat` the goal"), "{msg}");
    // A premise the premise tactic cannot prove ends the run with its failure.
    let msg = refused("theorem t(a: Nat, h: a = 1 → a = 2): a = 2 { by apply(h, assumption()) }");
    assert!(msg.contains("no local's type is the goal"), "{msg}");
}

/// A failed `first_of` reports each alternative's failure, with that
/// alternative's own notes indented beneath it.
#[test]
fn first_of_reports_each_branch() {
    let msg = refused(
        "import list;
         theorem t(a: Nat, h: a = 1 → a = 2, q: a = 3): a = 2 { by first_of([assumption(), apply(h, assumption())]) }",
    );
    assert!(msg.contains("the tactic failed: no alternative succeeded"), "{msg}");
    let first = msg.find("\n  tried an alternative: no local's type is the goal").expect(&msg);
    let nested = msg.find("\n    tried q: its type is not the goal").expect(&msg);
    let second = msg.rfind("\n  tried an alternative: no local's type is the goal").expect(&msg);
    assert!(first < nested && nested < second, "{msg}");
    // Catching a failure is pure: what succeeds after a caught failure is
    // the run's result.
    check(
        "import list;
         theorem u(a: Nat, p: a = 1): a = 1 { by first_of([exact(NatLit(0)), assumption()]) }",
    );
}

/// `Resolve` elaborates a name where the `by` is; `Lam` and locals are
/// checked against the binders the run opened.
#[test]
fn resolve_and_binder_discipline() {
    check(
        "import bool;
         import list;
         import string;
         import char;
         fn named(x: String) → tactic::Tac<tactic::Expr> {
             resolve(x).bind(λ c => match c { Accepted(h) => Pure(Hd(h)), Refused(why) => fail(why, Nil) })
         }
         theorem t(a: Nat, p: a = 1): a = 1 { by named(\"p\") }",
    );
    let msg = refused(
        "import bool;
         import list;
         import string;
         import char;
         fn named(x: String) → tactic::Tac<tactic::Expr> {
             resolve(x).bind(λ c => match c { Accepted(h) => Pure(Hd(h)), Refused(why) => fail(why, Nil) })
         }
         theorem t(a: Nat, p: a = 1): a = 1 { by named(\"nowhere\") }",
    );
    assert!(msg.contains("the tactic failed:") && msg.contains("nowhere"), "{msg}");
    // `Lam` abstracts only a local the run opened, at the binder it opened.
    let msg = refused("theorem t(a: Nat): a = 1 → a = 1 { by goal().bind(λ g => Pure(Lam(LocalRef(0), Local(LocalRef(0))))) }");
    assert!(msg.contains("`Lam` abstracts local 0, which is not bound here"), "{msg}");
    let msg = refused(
        "theorem t(a: Nat): a = 1 → a = 1 { by intro(goal().bind(λ g => Pure(Lam(LocalRef(1), Local(LocalRef(1)))))) }",
    );
    assert!(msg.contains("`Lam` abstracts local 1, which is not bound here"), "{msg}");
    // An opened local returned without its `Lam` is outside its binder.
    let msg = refused(
        "import bool;
         import list;
         import string;
         import char;
         fn escape() → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => open(g.target, \"x\").bind(λ c => match c {
                 Accepted(o) => Pure(Local(o.local.ref)),
                 Refused(why) => fail(why, Nil),
             }))
         }
         theorem t(a: Nat): a = 1 → a = 1 { by escape }",
    );
    assert!(msg.contains("local 1 is used outside its binder"), "{msg}");
}

/// A native tactic opens binders through the same protocol: `λ x. x`.
struct NativeIdentity {
    local: u64,
}

impl NativeTactic for NativeIdentity {
    fn start(&mut self) -> Result<Step, String> {
        Ok(Step::Ask(Request::Goal))
    }

    fn resume(&mut self, answer: Answer) -> Result<Step, String> {
        match answer {
            Answer::Goal(g) => Ok(Step::Ask(Request::Open(g.target, "x".into()))),
            Answer::Opened(Ok(o)) => {
                self.local = o.local.id;
                Ok(Step::Ask(Request::Infer(RExpr::Local(o.local.id))))
            }
            Answer::Handle(Ok(_)) => Ok(Step::Done(RExpr::Lam(self.local, Box::new(RExpr::Local(self.local))))),
            Answer::Opened(Err(why)) | Answer::Handle(Err(why)) => Ok(Step::Ask(Request::Fail(why, Vec::new()))),
            other => Err(format!("an answer to a request it did not make: {other:?}")),
        }
    }
}

#[test]
fn native_tactics_open_binders() {
    let mut e = elaborator();
    e.register_native_tactic("native_identity", || Box::new(NativeIdentity { local: 0 }));
    check_in(e.clone(), "theorem t(n: Nat): n = 1 → n = 1 { by native_identity }");
    let msg = refused_in(e, "theorem t(n: Nat, h: n = 1): n = 1 { by native_identity }");
    assert!(msg.contains("the tactic failed: `n = 1` is not a function type"), "{msg}");
}

/// `apply` matches the conclusion against the goal with the parameters as
/// unknowns (the elaborator's unifier, as for implicit arguments), so a
/// lemma's implicit parameters and any explicit one the conclusion
/// determines are filled in, and only the rest are left to the premise
/// tactic. A bare global is quoted as itself, its implicits still binders.
#[test]
fn apply_solves_what_the_conclusion_determines() {
    check(
        "theorem symmetric(a: Nat, b: Nat, p: a = b): b = a { by apply(sym, assumption()) }
         theorem open_type<A>(a: A, b: A, p: a = b): b = a { by apply(sym, assumption()) }
         theorem determined(a: Nat, f: (m: Nat) → m = 1 → m = 2, p: a = 1): a = 2 { by apply(f, assumption()) }
         theorem explicit_lemma(x: Nat, y: Nat): x + y = y + x { by apply(Nat::add_comm, assumption()) }
         theorem chained(a: Nat, b: Nat, p: a = b): a = b { by apply(sym, apply(sym, assumption())) }",
    );
    let msg = refused("theorem t(a: Nat, b: Nat, p: a = b): Nat { by apply(sym, assumption()) }");
    assert!(msg.contains("no number of arguments makes the conclusion of"), "{msg}");
}

/// `View` presents one layer of a handle the way a diagnostic would print
/// it, and `Whnf` reduces a handle first: a tactic dispatches on a Π, an
/// equation, a relation's name, a local's call, a call to a global, and a
/// numeral's head normal form.
#[test]
fn view_dispatches_on_the_goal() {
    let kinds = "import bool;
         import list;
         import string;
         import char;
         fn intros_then(n: Nat, t: tactic::Tac<tactic::Expr>) → tactic::Tac<tactic::Expr> {
             match n {
                 Zero => t,
                 Succ(m) => goal().bind(λ g => view(g.target).bind(λ v => match v {
                     HPi(_) => intro(intros_then(m, t)),
                     _ => t,
                 })),
             }
         }
         fn say(v: Head) → tactic::Tac<tactic::Expr> {
             match v {
                 HGlobal(_, name, args) => fail(\"global \" ++ name ++ \" of \" ++ match args { Nil => \"none\", Cons(_, _) => \"some\" }, Nil),
                 HEq(_, _) => fail(\"an equation\", Nil),
                 HPi(_) => fail(\"a function type\", Nil),
                 HLocal(_, args) => fail(\"a local of \" ++ match args { Nil => \"none\", Cons(_, _) => \"some\" }, Nil),
                 HLit(_) => fail(\"a literal\", Nil),
                 HMatch(_) => fail(\"a stuck match\", Nil),
                 HHole => fail(\"a hole\", Nil),
                 HField(_, name, _) => fail(\"a field \" ++ name, Nil),
                 HLam(_) => fail(\"a function\", Nil),
                 HCtor(_, _, name, _) => fail(\"a constructor \" ++ name, Nil),
                 HOther => fail(\"other\", Nil),
             }
         }
         fn goal_kind() → tactic::Tac<tactic::Expr> { goal().bind(λ g => view(g.target).bind(λ v => say(v))) }
         fn lhs_kind(reduce: Bool) → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => view(g.target).bind(λ v => match v {
                 HEq(l, _) => match reduce {
                     True => whnf(l).bind(λ c => match c { Accepted(w) => view(w).bind(λ u => say(u)), Refused(why) => fail(why, Nil) }),
                     False => view(l).bind(λ u => say(u)),
                 },
                 _ => fail(\"not an equation\", Nil),
             }))
         }";
    check(&format!("{kinds}\ntheorem t(a: Nat): a = 1 → a = 2 → a = 1 {{ by intros_then(5, assumption()) }}"));
    for (goal, kind) in [
        ("theorem t(n: Nat, m: Nat): n <= m { by goal_kind }", "global Le of some"),
        ("theorem t(n: Nat): n = n { by goal_kind }", "an equation"),
        ("theorem t(n: Nat): n = n → n = n { by goal_kind }", "a function type"),
        ("theorem t(f: Nat → Nat, n: Nat): f(n) = n { by lhs_kind(False) }", "a local of some"),
        ("theorem t(n: Nat): 3 = n { by lhs_kind(False) }", "a literal"),
        ("theorem t(n: Nat): n = 3 { by lhs_kind(False) }", "a local of none"),
        ("theorem t(n: Nat): 1 + 1 = n { by lhs_kind(True) }", "global Succ of some"),
        ("theorem t(n: Nat): n + 1 = 1 + n { by lhs_kind(False) }", "global add of some"),
        ("theorem t(n: Nat): 1 + n = n { by lhs_kind(True) }", "a stuck match"),
    ] {
        let msg = refused(&format!("{kinds}\n{goal}"));
        assert!(msg.contains(&format!("the tactic failed: {kind}")), "{goal}: {msg}");
    }
}

/// A parameter only a premise determines is a hole: `trans`'s middle point
/// is solved by proving its first premise, and the second is proved at the
/// solution. A hole made in an enclosing scope is solved from under a binder
/// (`intro` inside the premise), and one nothing solves is refused at the
/// result.
#[test]
fn holes_are_shared_across_premises() {
    check(
        "import list;
         theorem middle(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c { by apply(trans, assumption()) }
         theorem open_type<A>(a: A, b: A, c: A, p: a = b, q: b = c): a = c { by apply(trans, assumption()) }
         theorem twice(a: Nat, b: Nat, c: Nat, d: Nat, p: a = b, q: b = c, r: c = d): a = d {
             by apply(trans, first_of([assumption(), apply(trans, assumption())]))
         }
         theorem under(a: Nat, f: (m: Nat) → (m = m → a = a) → a = a): a = a {
             by apply(f, intro(assumption()))
         }",
    );
    // `assumption` commits to the first local that fits: `r` fits the first
    // premise with the wrong middle point, and nothing goes back.
    let msg = refused("theorem t(a: Nat, b: Nat, c: Nat, d: Nat, p: a = b, q: b = c, r: a = d): a = c { by apply(trans, assumption()) }");
    assert!(msg.contains("no local's type is the goal"), "{msg}");
    let msg = refused(
        "import bool;
         import list;
         import string;
         import char;
         theorem t(n: Nat): Nat {
             by goal().bind(λ g => hole(g.target).bind(λ c => match c { Accepted(h) => Pure(Hd(h)), Refused(why) => fail(why, Nil) }))
         }",
    );
    assert!(msg.contains("the tactic's proof `?1` mentions a hole nothing solved"), "{msg}");
}

/// Solving a hole is the one state a request changes, and `attempt` forgets
/// what a failed alternative solved: the second branch below sees the hole
/// unsolved, so it can solve it differently.
#[test]
fn a_failed_alternative_solves_nothing() {
    let forgets = "import bool;
         import list;
         import string;
         import char;
         fn forgets() → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => view(g.target).bind(λ v => match v {
                 HEq(l, r) => infer(Hd(l)).bind(λ c => match c {
                     Accepted(ty) => hole(ty).bind(λ c2 => match c2 {
                         Accepted(h) => first_of([
                             defeq(Hd(h), Hd(r)).bind(λ _ => fail(\"after solving it\", Nil)),
                             defeq(Hd(h), Hd(l)).bind(λ same => match same {
                                 True => assumption(),
                                 False => fail(\"the first branch's solution stuck\", Nil),
                             }),
                         ]),
                         Refused(why) => fail(why, Nil),
                     }),
                     Refused(why) => fail(why, Nil),
                 }),
                 _ => fail(\"not an equation\", Nil),
             }))
         }";
    check(&format!("{forgets}\ntheorem t(a: Nat, b: Nat, p: a = b): a = b {{ by forgets() }}"));
    // Without `attempt`, the solution stays: the same two comparisons in
    // sequence disagree.
    let msg = refused(
        "import bool;
         import list;
         import string;
         import char;
         fn keeps() → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => view(g.target).bind(λ v => match v {
                 HEq(l, r) => infer(Hd(l)).bind(λ c => match c {
                     Accepted(ty) => hole(ty).bind(λ c2 => match c2 {
                         Accepted(h) => defeq(Hd(h), Hd(r)).bind(λ _ => defeq(Hd(h), Hd(l)).bind(λ same => match same {
                             True => assumption(),
                             False => fail(\"the solution stuck\", Nil),
                         })),
                         Refused(why) => fail(why, Nil),
                     }),
                     Refused(why) => fail(why, Nil),
                 }),
                 _ => fail(\"not an equation\", Nil),
             }))
         }
         theorem t(a: Nat, b: Nat, p: a = b): a = b { by keeps() }",
    );
    assert!(msg.contains("the solution stuck"), "{msg}");
}

/// `Lookup` and `View` hand out the same reference for the same global, so
/// a tactic compares heads by identity; `Global(g)` is the global as a
/// term, with its implicit parameters for `Match` to solve.
#[test]
fn globals_by_identity() {
    let tactics = "import bool;
         import list;
         import string;
         import char;
         fn named(name: String) → tactic::Tac<tactic::GlobalRef> {
             lookup(name).bind(λ c => match c { Accepted(g) => Pure(g), Refused(why) => fail(why, Nil) })
         }
         fn head_is(name: String) → tactic::Tac<tactic::Expr> {
             named(name).bind(λ want => goal().bind(λ g => view(g.target).bind(λ v => match v {
                 HGlobal(got, _, _) => match got.id.same(want.id) {
                     True => fail(\"the same global\", Nil),
                     False => fail(\"a different global\", Nil),
                 },
                 _ => fail(\"not a global\", Nil),
             })))
         }
         fn by_ref(name: String) → tactic::Tac<tactic::Expr> {
             named(name).bind(λ s => apply(Global(s), assumption()))
         }";
    check(&format!("{tactics}\ntheorem t(a: Nat, b: Nat, p: a = b): b = a {{ by by_ref(\"sym\") }}"));
    for (goal, verdict) in [
        ("theorem t(n: Nat, m: Nat): n <= m { by head_is(\"Nat::Le\") }", "the same global"),
        ("theorem t(n: Nat, m: Nat): n <= m { by head_is(\"Nat\") }", "a different global"),
        ("theorem t(n: Nat): Nat { by head_is(\"Nat\") }", "the same global"),
        ("theorem t(n: Nat): Nat { by head_is(\"nowhere\") }", "`nowhere` names no global here"),
    ] {
        let msg = refused(&format!("{tactics}\n{goal}"));
        assert!(msg.contains(verdict), "{goal}: {msg}");
    }
    let msg = refused(&format!("{tactics}\ntheorem t(n: Nat): Nat {{ by named(\"Nat\").bind(λ g => Pure(Global(g))) }}"));
    assert!(msg.contains("is a kernel former or a type with no code, not a term"), "{msg}");
}

/// An `At` note is about a term, which the host spells as its diagnostics
/// do, with the note it carries one level deeper.
#[test]
fn notes_about_terms_are_spelled() {
    let msg = refused(
        "import bool;
         import list;
         import string;
         import char;
         theorem t(n: Nat, p: n = 1): n = 2 {
             by goal().bind(λ g => fail(\"stuck\", [At(Hd(g.target), Tried(\"refl\", \"the sides differ\")), At(Local(LocalRef(1)), Under(Tried(\"it\", \"too\")))]))
         }",
    );
    assert!(msg.contains("the tactic failed: stuck\n  at `n = 2`\n    tried refl: the sides differ\n  at `p`\n      tried it: too"), "{msg}");
}
