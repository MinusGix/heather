//! The route-1 (Ψ-staging) verification spike for
//! `issues/in-language-certificate-emission.md`, memo in
//! `docs/certgen-emission-route1-spike.md`.
//!
//! Route 1's claim is that certificate emission can move in-language once the
//! `prog`/`Ir` definitions are elaborated FIRST — they become Ψ globals, and a
//! code type may be indexed by globals (ch. 04 CAPP; the map round's
//! correction 1). Three facts have to hold for that to be more than a wish,
//! and this file pins each at the smallest honest size:
//!
//! (a) an elimination over a **Wf-lowered** (branching) inductive checks at
//!     `Layer::Meta`, so a layer-m builder may recurse over an `Ir` value;
//! (b) a quote payload and — the part that matters — a code **type** may
//!     reference a just-minted global;
//! (c) a kit lemma is applicable from *inside* a box, at its stated type.
//!
//! All three hold. A fourth, which the issue's list did not name and which the
//! spike found, does not: (d) the fold's RECURSIVE STEP needs a code type that
//! follows the sub-`Ir` it is about, and staging the top `Ir` into Ψ does not
//! reach the sub-`Ir`s. The last section pins that boundary too.
//!
//! (a) uses the real `Ir` (copied verbatim from `lib/certgen/ir_v1.hthr`, without the
//! interpreter that makes that file a 120 CPU-second test). (c) is pinned
//! twice: a structurally honest miniature here, and the **real** `ret_conv`
//! against the real `Converges` inside
//! `crates/elab/tests/ir_v1.rs::the_full_ir_library_checks`, which already
//! pays for the library's elaboration.

use heather_elab::{ElabError, Elaborator};
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::check_term;

const FUEL: u64 = 1_000_000;

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

/// The last committed binding's body, together with the Ψ it was elaborated
/// *against* — `GlobalVar` counts from the end of Ψ, so a body must be
/// re-checked under the prefix that excludes its own binding.
fn last_body(e: &Elaborator) -> (GlobalCtx, Term, Type, heather_kernel::level::Level) {
    let mut before = e.psi().bindings.to_vec();
    let last = before.pop().expect("a binding");
    match &last {
        GlobalBinding::Tm { ty, level, body: Some(b), .. } => (
            GlobalCtx::new(before.to_vec()),
            (**b).clone(),
            (**ty).clone(),
            level.clone(),
        ),
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// (a) elimination over a Wf-lowered inductive, at Layer::Meta
// ---------------------------------------------------------------------------

/// `Ir` and its `Refs`, verbatim from `lib/certgen/ir_v1.hthr` (comments dropped).
/// Three constructors carry **two** recursive fields, which is what puts the
/// inductive on the tier-1 `Wf` route (`docs/inductive-tier1-wf-lowering.md`)
/// rather than the tier-0 Σ/+ one — the whole point of item (a).
const IR: &str = r#"
inductive Refs { RNil, RCons(i: Nat, next: Refs) }

inductive Ir {
    Ret(rs: Refs),
    LetCon(tag: Nat, args: Refs, rest: Ir),
    LetMatch(scrut: Nat, arms: Ir, rest: Ir),
    Arm(body: Ir, next: Ir),
    NoArm,
    LetLoop(init: Refs, body: Ir, rest: Ir),
    LoopIter(body: Ir),
    LetCall(callee: Nat, args: Refs, rest: Ir),
}
"#;

/// A structural recursion over `Ir` with a **neutral** scrutinee (the
/// parameter), which is the shape route 1's in-code fold has: the builder
/// recurses over an `Ir` it was handed, not over a literal.
/// (On a `Wf`-lowered inductive the guarded self-call *is* the induction
/// hypothesis — there are no ih binders, and a constructor with two recursive
/// fields makes two of them, `docs/inductive-tier1-wf-lowering.md` §"the ih is
/// a function of the index". Every arm here uses the ih, so the lowering takes
/// the full `elim_Wf` route rather than the ih-free `const_elim_wf` shortcut.)
const IR_SIZE: &str = r#"
fn plus(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k, ih) => Succ(ih) } }

fn ir_size(ir: Ir) -> Nat {
    match ir {
        Ret(rs) => 1,
        LetCon(tag, args, rest) => Succ(ir_size(rest)),
        LetMatch(scrut, arms, rest) => Succ(plus(ir_size(arms), ir_size(rest))),
        Arm(body, next) => Succ(plus(ir_size(body), ir_size(next))),
        NoArm => 1,
        LetLoop(init, body, rest) => Succ(plus(ir_size(body), ir_size(rest))),
        LoopIter(body) => Succ(ir_size(body)),
        LetCall(callee, args, rest) => Succ(ir_size(rest)),
    }
}
"#;

#[test]
fn ir_is_wf_lowered() {
    // The premise of item (a): if `Ir` were a tier-0 Σ/+ inductive the
    // question would be about `elim_Sum`, not `elim_Wf`, and the answer would
    // say nothing about route 1.
    let e = elab(&format!("{IR}{IR_SIZE}"));
    let (psi, _, ty, _) = last_body(&e);
    let Type::Pi { dom, .. } = &ty else { panic!("ir_size is a function") };
    // Since the component-respell round (docs/annotation-component-respell-
    // design.md §2.1) the statement spells `⟦Ir⟧` as `El (Ir#tycode^δ)`;
    // δ + one decode step recovers the `Wf` head, which is the premise this
    // test pins — the lowering, not the statement's spelling of it.
    let dom = heather_kernel::reduce::whnf_type_delta(
        dom,
        &LocalCtx::nil(),
        heather_kernel::reduce::Defs::transparent(&psi),
        FUEL,
    )
    .expect("the statement dom reduces");
    assert!(matches!(dom, Type::Wf { .. }), "Ir did not lower to Wf: {dom:?}");
}

#[test]
fn elim_over_a_wf_lowered_inductive_checks_at_the_meta_layer() {
    // The eliminators are layer-generic: `Term::ElimWf`'s rule
    // (typing.rs:1436) opens with `not_var_layer`, not `meta_layer` and not a
    // `Layer::Prog` equality, so layer m is admitted exactly as layers c/p
    // are. This test is that sentence, checked rather than read: the very
    // term the elaborator committed for `ir_size` — an `elim_Wf` over a
    // neutral (variable) scrutinee, with the `nth`-schema child projections
    // the Wf lowering emits — re-checked at `Layer::Meta`.
    let e = elab(&format!("{IR}{IR_SIZE}"));
    let (psi, body, ty, level) = last_body(&e);
    check_term(&psi, 0, Layer::Prog, &LocalCtx::nil(), &body, &ty, &level, FUEL)
        .expect("the elaborator's own layer");
    check_term(&psi, 0, Layer::Meta, &LocalCtx::nil(), &body, &ty, &level, FUEL)
        .expect("elim_Wf at Layer::Meta");
}

#[test]
fn a_meta_body_may_match_a_wf_lowered_ir() {
    // The same fact from the side route 1 actually consumes, and the spike's
    // first surprise: this needs **no new surface at all**. A `meta fn` may
    // already take an ordinary program-layer parameter and `match` it — the
    // analyzer round widened the slice that far
    // (docs/certgen-transcriber-in-language-design.md §9.1 option A, landed)
    // — and the whole declaration is kernel-checked at `Layer::Meta`, so this
    // elaborating *is* an `elim_Wf` typed at layer m with all eight arms.
    elab(&format!(
        "{IR}
         meta fn walk(g: Ctx, ir: Ir) -> Nat {{
             match ir {{
                 Ret(rs) => 0,
                 LetCon(tag, args, rest) => 1,
                 LetMatch(scrut, arms, rest) => 2,
                 Arm(body, next) => 3,
                 NoArm => 4,
                 LetLoop(init, body, rest) => 5,
                 LoopIter(body) => 6,
                 LetCall(callee, args, rest) => 7,
             }}
         }}"
    ));
}

#[test]
fn elim_over_a_wf_lowered_inductive_computes_at_the_meta_layer() {
    // The literal half of the scrutinee axis (docs/testing-generated-terms.md),
    // and the half route 1 actually consumes: the fold *runs* at layer m, so
    // the eliminator must not merely type there but reduce. `Layer::computes`
    // is `Prog | Meta` (layer.rs:30), so ι should fire; conversion against the
    // numeral is the check.
    let src = format!(
        "{IR}{IR_SIZE}
         fn a_literal_ir() -> Ir {{ LetMatch(0, Arm(Ret(RNil), NoArm), Ret(RNil)) }}
         fn measured() -> Nat {{ ir_size(a_literal_ir()) }}"
    );
    let e = elab(&src);
    let (psi, measured, ty, level) = last_body(&e);
    let num = |n: u32| (0..n).fold(Term::Zero, |t, _| Term::Succ(std::sync::Arc::new(t)));
    for layer in [Layer::Prog, Layer::Meta] {
        // 1 + ((1 + 1 + 1) + 1): the LetMatch, its two-cell arm chain, and the
        // two `Ret`s.
        conv_term(&psi, &LocalCtx::nil(), layer, &measured, &num(5), &ty, &level, FUEL)
            .unwrap_or_else(|err| panic!("ir_size of a literal at {layer:?}: {err:?}"));
        // …and the control that says the conversion above decided something:
        // a term that never reduced would be neutral and convertible with
        // neither numeral.
        assert!(
            conv_term(&psi, &LocalCtx::nil(), layer, &measured, &num(4), &ty, &level, FUEL)
                .is_err(),
            "ir_size of that literal is 5, not 4, at {layer:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// (b) a code type indexed by a just-minted global
// ---------------------------------------------------------------------------

#[test]
fn a_code_type_may_be_indexed_by_a_just_minted_global() {
    // The route's load-bearing formation. `Type::CodeTm`'s rule
    // (typing.rs:630-635) checks its statement at `Layer::Prog` in the quote's
    // context, and `Term::GlobalTm`'s binding invariant is `i' ≤ i`
    // (typing.rs:748-763; ch. 04 l. 1077-1081) with declarations bound at
    // `Layer::Code` (crates/elab/src/lib.rs:1705) — so a
    // global is admissible in a code type's index, which is exactly ch. 04's
    // CAPP restriction read positively: *globals* are what a contextual type
    // may mention.
    elab(
        "fn seven() -> Nat { 7 }
         meta fn cert(g: Ctx) -> Code(g |- seven() = 7) { code { refl } }",
    );
}

#[test]
fn the_statement_may_apply_a_global_to_global_arguments() {
    // One step closer to `Converges(prog, env, ir, out)`: a *predicate* global
    // applied to argument globals, all four minted by the same file. This is
    // the exact shape route 1 stages — the emitted text already declares
    // `prog` and the `Ir`, so by the time the builder runs they are Ψ entries
    // and the statement is closed.
    elab(
        "fn dbl(n: Nat) -> Nat { match n { Zero => 0, Succ(k, ih) => Succ(Succ(ih)) } }
         fn arg() -> Nat { 3 }
         fn out() -> Nat { 6 }
         meta fn cert(g: Ctx) -> Code(g |- dbl(arg()) = out()) { code { refl } }",
    );
}

#[test]
fn the_payload_may_name_the_global_its_statement_mentions() {
    // Formation is one half; the box body is the other. The payload is checked
    // at `Layer::Code` (typing.rs:658-663), where `Code ≤ Code` admits the
    // reference and type conversion still happens at `typeof(c) = p`
    // (typing.rs:360, `Layer::type_layer`) — which is why a code-layer `refl`
    // can close an equation that only δ/ι-reduction decides.
    elab(
        "fn dbl(n: Nat) -> Nat { match n { Zero => 0, Succ(k, ih) => Succ(Succ(ih)) } }
         theorem dbl3(): dbl(3) = 6 { refl }
         meta fn cert(g: Ctx) -> Code(g |- dbl(3) = 6) { code { dbl3() } }",
    );
}

// -- the negative control: route 3's boundary is still there ----------------

#[test]
fn a_code_type_indexed_by_a_meta_local_is_still_refused() {
    // The sentence route 1 exists to route around
    // (docs/certgen-transcriber-in-language-design.md §5): a code type whose
    // statement mentions a meta-level LOCAL is unstatable, and staging does
    // not change that — it changes the *address* of the data. If this ever
    // starts elaborating, route 3 (dependent code types over meta data) landed
    // and this file should say so.
    // Surface-side the refusal is *name resolution* — a `meta fn`'s code type
    // elaborates with no locals in scope at all, the same enforcement that
    // makes a `match code` motive constant — so the diagnostic is "unbound
    // name `k`" rather than a layer complaint.
    let msg = elab_err(
        "fn dbl(n: Nat) -> Nat { match n { Zero => 0, Succ(k, ih) => Succ(Succ(ih)) } }
         meta fn cert(g: Ctx, k: Nat) -> Code(g |- dbl(k) = 6) { code { refl } }",
    );
    assert!(msg.contains("unbound") && msg.contains('k'), "{msg}");
}

#[test]
fn the_kernel_refuses_a_local_indexed_code_type_too() {
    // …and the kernel says the same thing one layer down, which is the fact
    // the surface rule is *for*. `Type::CodeTm`'s rule (typing.rs:631-634)
    // checks its statement in `env.in_ctx(ctx, Layer::Prog)`, and `in_ctx`
    // (typing.rs:288-290) **replaces** the local context rather than extending
    // it: the ambient meta-level Γ is discarded wholesale, so a `Var` of it is
    // not merely ill-layered but out of scope. That is
    // docs/certgen-transcriber-in-language-design.md §5's "unstatable", stated
    // as a kernel line — and it is why route 1 has to move the data into Ψ
    // rather than find a spelling.
    let meta_gamma = {
        let mut g = LocalCtx::nil();
        g.entries.push(heather_kernel::term::CtxEntry {
            ty: std::sync::Arc::new(Type::Nat),
            level: heather_kernel::level::Level::Zero,
        });
        g
    };
    let indexed_by_a_local = Type::CodeTm {
        ctx: LocalCtx::nil(),
        ty: std::sync::Arc::new(Type::Id {
            level: heather_kernel::level::Level::Zero,
            ty: std::sync::Arc::new(Type::Nat),
            lhs: std::sync::Arc::new(Term::Var(heather_kernel::term::LocalVar(0))),
            rhs: std::sync::Arc::new(Term::Zero),
        }),
        level: heather_kernel::level::Level::Zero,
    };
    assert!(matches!(
        heather_kernel::typing::check_type(
            &GlobalCtx::default(),
            0,
            Layer::Meta,
            &meta_gamma,
            &indexed_by_a_local,
            &heather_kernel::level::Level::Zero,
            FUEL,
        ),
        Err(heather_kernel::typing::TypeError::UnboundLocalVar(0))
    ));
    // The control on the control: the very same statement with the local
    // replaced by a closed term is a well-formed code type.
    let indexed_by_a_closed_term = Type::CodeTm {
        ctx: LocalCtx::nil(),
        ty: std::sync::Arc::new(Type::Id {
            level: heather_kernel::level::Level::Zero,
            ty: std::sync::Arc::new(Type::Nat),
            lhs: std::sync::Arc::new(Term::Zero),
            rhs: std::sync::Arc::new(Term::Zero),
        }),
        level: heather_kernel::level::Level::Zero,
    };
    heather_kernel::typing::check_type(
        &GlobalCtx::default(),
        0,
        Layer::Meta,
        &meta_gamma,
        &indexed_by_a_closed_term,
        &heather_kernel::level::Level::Zero,
        FUEL,
    )
    .expect("a closed statement is a legal code-type index");
}

// ---------------------------------------------------------------------------
// (c) kit lemmas from inside a box — the miniature
// ---------------------------------------------------------------------------

#[test]
fn a_boxed_payload_may_apply_a_lemma_global_at_its_stated_type() {
    // The in-code fold's one move, in miniature: a `theorem` is a Ψ global
    // like any other, and the payload applies it at its statement. A theorem's
    // *proof* is opaque to body reflection by policy
    // (docs/opaque-globals-analysis-design.md), which is irrelevant here — the
    // fold never reads the proof, it names the lemma.
    elab(
        "fn plus(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k, ih) => Succ(ih) } }
         theorem plus_zero(n: Nat): plus(n, 0) = n { refl }
         fn three() -> Nat { 3 }
         meta fn cert(g: Ctx) -> Code(g |- plus(three(), 0) = three()) {
             code { plus_zero(three()) }
         }",
    );
}

#[test]
fn a_boxed_payload_may_compose_two_lemma_globals() {
    // A fold is composition, not one application: the payload feeds one
    // lemma's conclusion to another's hypothesis, at layer c, with both
    // lemmas and both indices Ψ-resident. That is the whole certificate
    // shape, one instruction wide.
    elab(
        "fn plus(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k, ih) => Succ(ih) } }
         theorem plus_zero(n: Nat): plus(n, 0) = n { refl }
         theorem bump(a: Nat, b: Nat, h: a = b): Succ(a) = Succ(b) {
             j(h, λ x q => Succ(a) = Succ(x), refl)
         }
         fn three() -> Nat { 3 }
         meta fn cert(g: Ctx) -> Code(g |- Succ(plus(three(), 0)) = Succ(three())) {
             code { bump(plus(three(), 0), three(), plus_zero(three())) }
         }",
    );
}

// ---------------------------------------------------------------------------
// (d) the item the issue's list did not name: the fold's RECURSIVE STEP
// ---------------------------------------------------------------------------

#[test]
fn code_may_be_built_by_matching_an_ir_at_a_constant_statement() {
    // The good half. A `meta fn` may match a Wf-lowered `Ir` and return
    // *code* — building code by recursion over a value is not blocked in
    // itself, as long as every arm's code has the SAME statement. That is the
    // same constant-motive discipline `match code` runs under (§3), reappearing
    // one level out.
    elab(&format!(
        "{IR}
         meta fn build(g: Ctx, ir: Ir) -> Code(g |- Nat) {{
             match ir {{
                 Ret(rs) => code {{ 0 }},
                 LetCon(tag, args, rest) => code {{ 1 }},
                 LetMatch(scrut, arms, rest) => code {{ 2 }},
                 Arm(body, next) => code {{ 3 }},
                 NoArm => code {{ 4 }},
                 LetLoop(init, body, rest) => code {{ 5 }},
                 LoopIter(body) => code {{ 6 }},
                 LetCall(callee, args, rest) => code {{ 7 }},
             }}
         }}"
    ));
}

#[test]
fn a_certificate_statement_cannot_follow_the_ir_it_is_about() {
    // …and the bad half, which is route 1's real remaining blocker. A
    // certificate fold is exactly a recursion whose result type *varies with
    // the scrutinee*: proving `Converges(p, env, LetCon(t, a, rest), vs)`
    // consumes `Converges(p, env', rest, vs)`, and `rest` is a binder of the
    // arm, not a Ψ global. So the fold wants `Code(· ⊢ P(ir))` — a code type
    // depending on a local — which is the same refusal as
    // `a_code_type_indexed_by_a_meta_local_is_still_refused`, met one level in.
    // Staging the TOP `Ir` into Ψ does not reach the sub-`Ir`s.
    let msg = elab_err(&format!(
        "{IR}
         fn ir_head(ir: Ir) -> Nat {{ match ir {{ Ret(rs) => 0, _ => 1 }} }}
         meta fn build(g: Ctx, ir: Ir) -> Code(g |- ir_head(ir) = 0) {{ code {{ refl }} }}"
    ));
    assert!(msg.contains("unbound") && msg.contains("ir"), "{msg}");
}

#[test]
fn a_meta_fn_cannot_call_itself_or_another_meta_fn() {
    // The other half of the same gap, and a correction to the issue's
    // "meta-body-statement-loop territory": ordinary `match` in a meta body
    // already works (see above); what does not is RECURSION. A `meta fn` is
    // elaborator-held, not Ψ-resident (docs/in-language-map-design.md §8), so
    // it is not in scope in its own body and not in another's. A program-layer
    // `fn` may recurse, but may not return code — `Code`/`Ctx`/`TyCode` are
    // meta-layer types (typing.rs:625/631 `meta_layer`).
    let self_call = elab_err(
        "meta fn m(g: Ctx, n: Nat) -> Nat { match n { Zero => 0, Succ(k, ih) => m(g, k) } }",
    );
    assert!(self_call.contains("unbound name `m`"), "{self_call}");
    let cross_call = elab_err(
        "meta fn a(g: Ctx) -> Nat { 0 }
         meta fn b(g: Ctx) -> Nat { a(g) }",
    );
    assert!(cross_call.contains('a'), "{cross_call}");
    let code_from_prog = elab_err("fn f(g: Ctx) -> Code(g |- Nat) { code { 0 } }");
    assert!(code_from_prog.contains("meta-layer types"), "{code_from_prog}");
}
