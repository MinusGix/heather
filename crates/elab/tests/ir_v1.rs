//! FunctionIR v1, `simulate`, and the fuel interface, kept as a **frozen
//! corpus** (`crates/elab/tests/fixtures/ir_v1.hthr`). The library file
//! `lib/certgen/ir_v1.hthr` was the source IR of the per-function certificate
//! path, which burn B2 retired (docs/native-program-logic-design.md §3.2); the
//! verified compiler's source is `function_ir_source` instead. The copy stays
//! because it is still the elaborator's heaviest single file of deep proofs
//! over `nat` alone (`step_mono`'s explicit motives, the ∃-composition kit's
//! double-`j` lemmas), the frontend bench's heavy case
//! (`crates/elab/benches/frontend/fixtures/corpus.rs`), and the corpus the
//! emission walker's residue is recorded against
//! (`issues/emission-walker-residual-sites.md`). Frozen means nothing here is
//! edited to follow the library: a change that breaks it is a change to the
//! elaborator, which is the point.
//!
//! BUDGET. The full-library test is the suite's heaviest elaboration;
//! `scripts/test --fast` skips it by name and a round's final verification
//! runs it. If it outgrows the rail the answer is to make the elaborator
//! compute generalized motives (`issues/ih-generalization.md`), not to raise
//! the limit.
//!
//! - the first elaborates every DECLARATION (datatypes, helpers, the
//!   interpreter, the continuation helpers, the add programs) and runs the
//!   negative controls the file cannot state about itself — a wrong simulate
//!   claim, a false `<=` witness under `fuel_monotone`, and a wrong-result
//!   `equiv` — at the cheapest possible depth;
//! - the second is the full acceptance, the file's own theorems, with the
//!   emission walk on.

use heather_elab::Elaborator;

const LIB: &str = include_str!("fixtures/ir_v1.hthr");
/// The corpus's one import: the Nat kit it used to declare itself
/// (docs/modules-design.md §7). The test elaborates the **closure**, in the
/// order the CLI's loader would — dependencies first — into one accumulator.
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");

/// A prelude'd elaborator with `nat` already in it, positioned in module
/// `ir_v1`: every snippet below is therefore an *addition to the library
/// file*, which is what a control on the library has to be.
fn ir_v1_elaborator() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).unwrap_or_else(|err| panic!("{}", err.render(LOGIC)));
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

/// Everything up to the first theorem. The library keeps every `fn` and
/// `inductive` ahead of its theorem section for exactly this reason, so this
/// is precisely the declarations.
fn decls() -> &'static str {
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    &LIB[..cut]
}

/// Slots the walker still lists on this library, recorded rather than fixed
/// (`issues/emission-walker-residual-sites.md`, filed by the round that
/// landed the walker). Each is written either by an emitter the chokepoint
/// does not yet govern — a rewrite's `J`, a generated eliminator motive, a
/// schema's `App`, the tier-0 match arm's alias projections — or by a
/// governed one that re-reads components off the whnf of a whole-type
/// reference (`project_field`'s fallback walk), and each carries either a
/// whole declaration lowering inline where a `#tycode` reference exists or a
/// `⌜…⌝` quote of one. Routing them is that issue's work; this list is a
/// **regression guard** instead: a slot outside it means an emitter the
/// chokepoint *does* govern today — the statement cascade, a constructor
/// label's injections, a `Wf` slot pair, a field tuple's own annotations, a
/// written `λ`'s domain, `refl`'s element type — started disagreeing again.
/// It only ever shrinks.
const WALK_RESIDUE: &[&str] = &[
    "App.cod",
    "App.dom",
    "Case.motive",
    "ElimEmpty.motive",
    "ElimNat.motive",
    "Fst.fst_ty",
    "Fst.snd_ty",
    "J.motive",
    "J.ty",
    "Pair.fst_ty",
    "Pair.snd_ty",
    "Refl.ty",
    "Snd.fst_ty",
    "Snd.snd_ty",
];

/// The emission walker's findings, one line per `(slot, depth)` with a count
/// and the first declaration and spelling seen at it: the ones outside
/// [`WALK_RESIDUE`] first (empty is the assertion), then all of them.
fn emission_walk_residue(e: &Elaborator) -> (String, String) {
    let mut by_site = std::collections::BTreeMap::<(&str, u32), (usize, String)>::new();
    for f in e.take_emission_findings() {
        let entry = by_site
            .entry((f.slot, f.depth))
            .or_insert_with(|| (0, f.decl.clone()));
        entry.0 += 1;
    }
    let line = |(slot, depth): (&str, u32), (count, decl): &(usize, String)| {
        format!("  {slot} depth={depth} count={count} first={decl}\n")
    };
    let outside = by_site
        .iter()
        .filter(|((slot, _), _)| !WALK_RESIDUE.contains(slot))
        .map(|(k, v)| line(*k, v))
        .collect();
    let all = by_site.iter().map(|(k, v)| line(*k, v)).collect();
    (outside, all)
}

/// `refl` at a false equation dies in the kernel as `NotConvertible`; a
/// mis-typed proof argument dies as an elaboration error. Either way the
/// point of a negative control is that the claim does **not** land.
fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    match e.elab_module_source("ir_v1", src) {
        Err(_) => {}
        Ok(()) => panic!("{what} elaborated, but it is false"),
    }
}

#[test]
fn declarations_check_and_wrong_claims_are_refuted() {
    let src = decls();
    let mut e = ir_v1_elaborator();
    e.elab_module_source("ir_v1", src)
        .unwrap_or_else(|err| panic!("{}", err.render(src)));

    // `IrCases` is usable independently of the interpreter: this consumer
    // observes only the outer constructor, while `step_cases` closes over a
    // recursive evaluator. Together they pin Cases as case analysis/open
    // recursion, rather than a second spelling of the recursive fold.
    let cases_probe = "fn ir_constructor_number(ir: Ir) -> Nat {\n\
        ir_cases(IrCases<Nat> {\n\
            ret: λ rs => 0,\n\
            letcon: λ tag args rest => 1,\n\
            letmatch: λ scrut arms rest => 2,\n\
            arm: λ body next => 3,\n\
            noarm: 4,\n\
            letloop: λ init body rest => 5,\n\
            loopiter: λ body => 6,\n\
            letcall: λ callee args rest => 7,\n\
        }, ir)\n\
    }\n\
    theorem cases_ret(): ir_constructor_number(Ret(RNil)) = 0 { refl }\n\
    theorem cases_letcall(): ir_constructor_number(LetCall(3, RNil, NoArm)) = 7 { refl }";
    e.elab_module_source("ir_v1", cases_probe)
        .unwrap_or_else(|err| panic!("{}", err.render(cases_probe)));
    refuted(
        &mut e,
        "theorem cases_wrong(): ir_constructor_number(Ret(RNil)) = 1 { refl }",
        "a Cases table selecting the wrong clause",
    );

    // 1. Zero fuel is OutOfFuel; claiming it produced a value must fail. One
    // eval unfolding, so the control costs seconds, not minutes.
    let wrong = "theorem wrong(): eval(0, PNil)(VNil, Ret(RNil)) = Out(VNil) { refl }";
    match e.elab_module_source("ir_v1", wrong) {
        Err(err) => {
            let msg = format!("{err}");
            assert!(msg.contains("NotConvertible"), "unexpected refutation: {msg}");
        }
        Ok(()) => panic!("a false simulate claim elaborated"),
    }

    // 2. `fuel_monotone`'s statement family, refuted at the hypothesis that
    // makes it monotone rather than arbitrary: `leb(5)(3) = True` is
    // `False = True`, so no `refl` supplies it. Without this control a
    // `fuel_monotone` whose order hypothesis was vacuous would look identical
    // from the outside.
    refuted(
        &mut e,
        "theorem bad_le(): leb(5)(3) = True { refl }",
        "5 <= 3",
    );

    // …and the shape one step down: monotonicity is not symmetric. Claiming
    // a *smaller* fuel still answers is exactly the converse, and it fails at
    // the one place it can be seen concretely — the add loop mid-flight.
    refuted(
        &mut e,
        "theorem bad_anti(): eval(4, add_prog())(VCons(embed_nat(2), VCons(embed_nat(3), VNil)), \
         add_body()) = Out(VCons(embed_nat(5), VNil)) { refl }",
        "the add IR answering below its bound",
    );

    // 3. A wrong-result `equiv`: the bound is right, the answer is not. The
    // scrutinee here is a *literal* pair, which is the cheap half of the
    // axis; the file's own `add_equiv` carries the neutral one (`a`, `b` are
    // open Nats) and this control's purpose is only to show that being off by
    // one is visible at all.
    refuted(
        &mut e,
        "theorem bad_equiv(): eval(add(2, 5), add_prog())(VCons(embed_nat(2), \
         VCons(embed_nat(3), VNil)), add_body()) = Out(VCons(embed_nat(6), VNil)) { refl }",
        "add(2, 3) = 6 through the IR",
    );
}

/// The full library, acceptance theorems included: the deep combined
/// theorems, `step_mono`'s whole case tree, `fuel_monotone` in both shapes,
/// `Converges`/`BindInv` and the ∃-form of the refinement chain, and the
/// ∀-arguments `equiv`. 34s release; the debug figure is in this file's header
/// and is the reason nothing else lives in this test binary.
///
/// The ∃-form's negative controls ride along **in this test** rather than in
/// one of their own, deliberately: each would otherwise re-elaborate the whole
/// library, and two full elaborations do not fit the 300-second rail. They are
/// the controls the library cannot state about itself —
/// `Converges(p, env, ir, vs)` is a *predicate*, and the standing risk of the
/// encoding (docs/surface-value-parameters.md §2) is that a mis-weakened value
/// parameter would silently make it a vacuous one.
#[test]
fn the_full_ir_library_checks() {
    let mut e = ir_v1_elaborator();
    // The emission audit rides on the broadest load there is, rather than
    // paying for a whole-library elaboration of its own
    // (issues/emission-spelling-chokepoint.md;
    // docs/annotation-component-respell-design.md §2.5): every emitted
    // annotation slot of every declaration below is asked whether the one
    // chokepoint would still respell it.
    e.enable_emission_walk();
    e.elab_module_source("ir_v1", LIB)
        .unwrap_or_else(|err| panic!("{}", err.render(LIB)));
    // Drained here, before the negative controls: a refused declaration is
    // walked before the kernel refuses it, and its slots are not the
    // library's.
    let (residue, all) = emission_walk_residue(&e);
    // Printed, not only asserted: the point of the audit is the list, and a
    // green run that says nothing about it is how the last four rows of
    // `issues/emission-site-respell-audit.md` went unnoticed. `--nocapture`
    // shows it.
    eprint!("emission walk over `ir_v1`:\n{all}");
    assert!(
        residue.is_empty(),
        "the emission walker found slots outside the recorded residue:\n{residue}"
    );

    // The *wrong* answer at the right program and the right witness: refused.
    // If the `vs` parameter were captured under the Σ binder rather than
    // substituted, this would be the same proposition as `add_converges`'s,
    // which the library just proved.
    refuted(
        &mut e,
        "theorem conv_wrong(): Converges(add_prog(), VCons(embed_nat(1), \
         VCons(embed_nat(1), VNil)), add_body(), VCons(embed_nat(3), VNil)) \
         { Converges(50, refl) }",
        "converging to 3 where the IR answers 2",
    );

    // …and no witness closes a starved bound, so the `n` field is doing work
    // rather than being ignored by the encoding.
    refuted(
        &mut e,
        "theorem conv_starved(): Converges(add_prog(), VCons(embed_nat(1), \
         VCons(embed_nat(1), VNil)), add_body(), VCons(embed_nat(2), VNil)) \
         { Converges(1, refl) }",
        "converging at fuel 1",
    );

    // `BindInv`'s `hr` field pins the scrutinee, so an inversion claimed at a
    // `Stuck` sub-region — which produced no `ws` at all — must not check.
    refuted(
        &mut e,
        "theorem inv_wrong(ev: Val -> Ir -> Res, env: Val, rest: Ir, vs: Val) \
         : BindInv(ev, env, rest, Stuck, vs) { BindInv(VNil, refl, refl) }",
        "an inversion of a Stuck sub-region",
    );

    // `Compile` v1 controls (docs/compile-typeclass-design.md §7 item 3).
    // A wrong-result SPEC: the instance's certificate is the real theorem, so
    // the failure is precisely the coupling — `cert`'s expected type carries
    // `bad_spec` and the delivered convergence is to `add(b, a)`.
    refuted(
        &mut e,
        "fn bad_spec(a: Nat) -> Nat -> Nat { λ (b: Nat) => add(a, a) }\n\
         fn bad_instance() -> CompileNat2(bad_spec) {\n\
             CompileNat2 { prog: add_chain(), entry: ir_call2(),\n\
                 cert: λ (a: Nat) => λ (b: Nat) => add_converges_through_calls(a, b) } }",
        "an instance for a spec the IR does not implement",
    );

    // …and a wrong IR under the right spec: the certificate is about
    // `ir_call2()`, so an instance claiming it for the loop body must fail —
    // `entry` is substituted into `cert`'s type, not decoration.
    refuted(
        &mut e,
        "fn bad_entry() -> CompileNat2(add_spec) {\n\
             CompileNat2 { prog: add_chain(), entry: ir_loop(),\n\
                 cert: λ (a: Nat) => λ (b: Nat) => add_converges_through_calls(a, b) } }",
        "an instance whose entry is not the IR the certificate is about",
    );

    // The route-1 spike's item (c), against the REAL kit
    // (issues/in-language-certificate-emission.md; the memo is
    // docs/certgen-emission-route1-spike.md). It rides here because a suite
    // of its own would re-elaborate the whole corpus: a staged meta fn whose
    // `code` block cites the kit's own `ret_conv`.
    //
    // What it pins: a `Converges` statement over Ψ-resident *globals* is a
    // legal code-type index (ch. 04 CAPP — a contextual type may mention
    // globals, and only globals), and the boxed payload may **apply a kit
    // lemma** at its stated type, `gather`'s side condition discharged by a
    // layer-c `refl` (conversion for a layer-c term runs at `typeof(c) = p`,
    // typing.rs:360, so δ/ι still decide it). Route 1's fold is that move,
    // repeated per instruction.
    let staged = "fn cert_env() -> Val { VNil }\n\
                  fn cert_ir() -> Ir { Ret(RNil) }\n\
                  fn cert_out() -> Val { VNil }\n\
                  meta fn ret_cert(g: Ctx)\n\
                      -> Code(g |- Converges(add_prog(), cert_env(), cert_ir(), cert_out()))\n\
                  { code { ret_conv(add_prog(), cert_env(), RNil, cert_out(), refl) } }";
    e.elab_module_source("ir_v1", staged)
        .unwrap_or_else(|err| panic!("{}", err.render(staged)));

    // …and the boundary route 1 routes *around*, still closed: the same
    // statement with the `Ir` at a meta-level LOCAL rather than a Ψ global is
    // what docs/certgen-transcriber-in-language-design.md §5 calls unstatable,
    // and it is unstatable against the real `Converges` too. If this ever
    // starts elaborating, route 3 landed.
    refuted(
        &mut e,
        "meta fn bad_cert(g: Ctx, ir: Ir)\n\
             -> Code(g |- Converges(add_prog(), cert_env(), ir, cert_out()))\n\
         { code { ret_conv(add_prog(), cert_env(), RNil, cert_out(), refl) } }",
        "a code type indexed by a meta-level local",
    );
}
