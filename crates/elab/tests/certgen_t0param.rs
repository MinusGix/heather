//! TIER-0 (non-`Nat`) PARAMETERS for the certifying generator — the
//! acceptance of `docs/certgen-tier0-params-design.md` §10: a fragment fn's
//! parameters may be payload-free tier-0 enumerations, consumed via `match`
//! (`Term::Case` at the kernel level) and passed to callees.
//!
//! Positives — every one generated, elaborated and kernel-checked end to end:
//! - `pick` over `Flag` (the if-shape), the round's hand-run retired into
//!   generated form;
//! - `gate` (a tier-0 match) called by `route` — the enum parameter FLOWING
//!   TO A CALLEE, the charter's composition item: a two-member program with
//!   `gate_gen_conv_in_route` re-derived inside it, applied at the caller's
//!   own `Flag` parameter;
//! - `fnot` — the tier-0 parameter and the tier-0 RESULT stages composed
//!   (`CompileFlagFlag`);
//! - `sel3` over `Sign3` — three constructors (a dispatch tag past 1) and a
//!   foreign call inside an arm;
//! - `wsum` — a tier-0 parameter riding a `Nat` INDUCTION and passed to a
//!   callee from inside an arm;
//! - `tsel` — a tier-0 parameter beside a TIER-1 recursion: the tier stages
//!   compose (`CompileToksFlagNat`).
//!
//! A binary of its own for the usual two reasons (`certgen.rs`'s header):
//! one `match code` shell elaboration per test thread (the stack rail), and
//! one `ulimit -t` rail per process. Both tests here are acceptance-class
//! and on `scripts/test --fast`'s skip list; the plain full run is what
//! checks them (CLAUDE.md).

use heather_elab::certgen::{generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

mod support;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const CODE: &str = include_str!("../../../lib/certgen_code.hthr");
const CERT: &str = include_str!("../../../lib/certgen_cert.hthr");

/// Items a generated emission needs beyond the declarations prefix, in
/// dependency (file-consistent) order — `certgen_emissions.rs`'s list.
const SUPPORT_ITEMS: [&str; 14] = [
    "dbl",
    "BindInv",
    "k_bind_inv",
    "k_bind_mono",
    "step_mono",
    "eval_mono_succ",
    "eval_mono_plus",
    "fuel_monotone",
    "Converges",
    "ret_conv",
    "letcon_conv",
    "letcall_conv",
    "letmatch_conv",
    "CompileNat2",
];

fn support_prelude() -> String {
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    let mut s = LIB[..cut].to_string();
    let file = parse_file(LIB).expect("the library parses");
    for name in SUPPORT_ITEMS {
        let span = file
            .items
            .iter()
            .find_map(|i| match i {
                Item::Inductive(ind) if ind.name == name => Some(ind.span),
                Item::Decl(d) if d.name == name => Some(d.span),
                _ => None,
            })
            .unwrap_or_else(|| panic!("the library declares {name}"));
        s.push('\n');
        s.push_str(&LIB[span.start..span.end]);
        s.push('\n');
    }
    s
}

fn lib_decl(name: &str) -> Decl {
    let file = parse_file(NAT).expect("`nat` parses");
    file.items
        .into_iter()
        .find_map(|i| match i {
            Item::Decl(d) if d.name == name => Some(d),
            _ => None,
        })
        .unwrap_or_else(|| panic!("`nat` declares fn {name}"))
}

fn decl_of(src: &str) -> Decl {
    let file = parse_file(src).unwrap_or_else(|e| panic!("test fn parses: {e:?}"));
    assert_eq!(file.items.len(), 1);
    file.items.into_iter().next().unwrap().into_decl()
}

fn elab(e: &mut Elaborator, src: &str, what: &str) {
    e.elab_module_source("ir_v1", src)
        .unwrap_or_else(|err| panic!("{what}:\n{}", err.render(src)));
}

fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    if e.elab_module_source("ir_v1", src).is_ok() {
        panic!("{what} elaborated, but it must fail");
    }
}

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

const TYPES: &str = "\
inductive Flag { Off, On }
inductive Sign3 { SNeg, SZero, SPos }
inductive Peek { PNone, PSome(k: Nat) }
";
const TOKS: &str = "inductive Toks { TNil, TCons(n: Nat, rest: Toks) }";
const PICK: &str =
    "fn pick(f: Flag, a: Nat, b: Nat) -> Nat { match f { Off => a, On => b } }";
const GATE: &str = "fn gate(f: Flag, n: Nat) -> Nat { match f { Off => 0, On => n } }";
const ROUTE: &str = "fn route(f: Flag, n: Nat) -> Nat { gate(f, n) }";
const FNOT: &str = "fn fnot(f: Flag) -> Flag { match f { Off => On, On => Off } }";
const SEL3: &str =
    "fn sel3(s: Sign3, n: Nat) -> Nat { match s { SNeg => 0, SZero => n, SPos => add(n, n) } }";
const WSUM: &str =
    "fn wsum(f: Flag, n: Nat) -> Nat { match n { Zero => gate(f, 0), Succ(k) => Succ(wsum(f, k)) } }";
const TSEL: &str =
    "fn tsel(l: Toks, f: Flag) -> Nat { match l { TNil => Zero, TCons(n, rest) => Succ(tsel(rest, f)) } }";

// THE LAYOUT INTERFACE for tier-0 parameter matches, pinned as literals
// exactly as `certgen_tier1.rs` pins the tier-1 ones: one arm fn per
// constructor in declaration order, NO fields prepended (payload-free), the
// dispatch slot the parameter's distance.

const IR_PICK: &str = "\
pick_gen_arm0() = Ret(RCons(1, RNil))
pick_gen_arm1() = Ret(RCons(2, RNil))
pick_gen_body() = LetMatch(0, Arm(pick_gen_arm0(), Arm(pick_gen_arm1(), NoArm)), Ret(RCons(0, RNil)))";

const IR_GATE: &str = "\
gate_gen_arm0() = LetCon(0, RNil, Ret(RCons(0, RNil)))
gate_gen_arm1() = Ret(RCons(1, RNil))
gate_gen_body() = LetMatch(0, Arm(gate_gen_arm0(), Arm(gate_gen_arm1(), NoArm)), Ret(RCons(0, RNil)))";

/// The composition positive: a straight-line caller passing its own `Flag`
/// parameter at the callee's tier-0 slot.
const IR_ROUTE: &str =
    "route_gen_body() = LetCall(0, RCons(0, RCons(1, RNil)), Ret(RCons(0, RNil)))";

/// Three constructors: a dispatch past tag 1, and a foreign call in an arm
/// (closure `[add, sel3]`).
const IR_SEL3: &str = "\
sel3_gen_arm0() = LetCon(0, RNil, Ret(RCons(0, RNil)))
sel3_gen_arm1() = Ret(RCons(1, RNil))
sel3_gen_arm2() = LetCall(0, RCons(1, RCons(1, RNil)), Ret(RCons(0, RNil)))
sel3_gen_body() = LetMatch(0, Arm(sel3_gen_arm0(), Arm(sel3_gen_arm1(), Arm(sel3_gen_arm2(), NoArm))), Ret(RCons(0, RNil)))";

/// A `Nat` induction with the tier-0 parameter riding through: the `Zero`
/// arm calls `gate(f, 0)` — the enum slot read from UNDER the induction.
const IR_WSUM: &str = "\
wsum_gen_arm_zero() = LetCon(0, RNil, LetCall(0, RCons(1, RCons(0, RNil)), Ret(RCons(0, RNil))))
wsum_gen_arm_succ() = LetCall(1, RCons(1, RCons(0, RNil)), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))
wsum_gen_body() = LetMatch(1, Arm(wsum_gen_arm_zero(), Arm(wsum_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// The end-to-end acceptance (design doc §10 items 1–5): the positives
/// generated, elaborated and kernel-checked, then the declines with their
/// attributions.
#[test]
fn t0param_emissions_and_declines() {
    let mut e = base();
    let sup = support_prelude();
    support::with_decl_cache(&mut e, |e| {
        elab(e, &sup, "support prelude");
        elab(e, CODE, "lib/certgen_code.hthr");
        elab(e, CERT, "lib/certgen_cert.hthr");
    });
    for (src, what) in [
        (TYPES, "the tier-0 parameter types"),
        (TOKS, "inductive Toks"),
        (PICK, "fn pick"),
        (GATE, "fn gate"),
        (ROUTE, "fn route"),
        (FNOT, "fn fnot"),
        (SEL3, "fn sel3"),
        (WSUM, "fn wsum"),
        (TSEL, "fn tsel"),
    ] {
        elab(&mut e, src, what);
    }

    let mut ctx = GenCtx::new();
    let mut support_done: Vec<String> = Vec::new();
    let mut generate = |e: &mut Elaborator, ctx: &mut GenCtx, d: &Decl| {
        let em = generate_in_language(e, d, ctx)
            .unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
        for (key, text) in &em.support {
            if !support_done.contains(key) {
                elab(e, text, key);
                support_done.push(key.clone());
            }
        }
        elab(e, &em.text, &format!("emission for {}", em.name));
        ctx.push(em);
    };
    generate(&mut e, &mut ctx, &decl_of(PICK));
    generate(&mut e, &mut ctx, &decl_of(GATE));
    generate(&mut e, &mut ctx, &decl_of(ROUTE));
    generate(&mut e, &mut ctx, &decl_of(FNOT));
    generate(&mut e, &mut ctx, &lib_decl("add"));
    generate(&mut e, &mut ctx, &decl_of(SEL3));
    generate(&mut e, &mut ctx, &decl_of(WSUM));
    generate(&mut e, &mut ctx, &decl_of(TSEL));

    let get = |name: &str| ctx.iter().find(|e| e.name == name).expect("emission present");
    assert_eq!(get("pick").ir_body, IR_PICK, "pick transcribes differently");
    assert_eq!(get("gate").ir_body, IR_GATE, "gate transcribes differently");
    assert_eq!(get("route").ir_body, IR_ROUTE, "route transcribes differently");
    assert_eq!(get("sel3").ir_body, IR_SEL3, "sel3 transcribes differently");
    assert_eq!(get("wsum").ir_body, IR_WSUM, "wsum transcribes differently");
    assert_eq!(get("route").closure, vec!["gate".to_string(), "route".to_string()]);
    assert_eq!(get("sel3").closure, vec!["add".to_string(), "sel3".to_string()]);
    assert_eq!(get("wsum").closure, vec!["gate".to_string(), "wsum".to_string()]);

    // The composition item: the callee's invariant re-derived inside the
    // caller's program and applied at the caller's own `Flag` parameter —
    // in the tier-0 induction-free shape (`cert_app`'s `RecT` spelling).
    let route = &get("route").text;
    assert!(route.contains("gate_gen_conv_in_route(f)(n, VNil)"), "{route}");
    // …and from under a `Nat` induction, at the enum slot's own embedding.
    let wsum = &get("wsum").text;
    assert!(wsum.contains("gate_gen_conv_in_wsum(f)(Zero, VNil)"), "{wsum}");
    assert!(wsum.contains("VCons(Flag_gen_embed(f), VCons(embed_nat(Zero), VNil))"), "{wsum}");

    // Per-signature records name every parameter tier
    // (docs/certgen-tier1-source-types-design.md §7's rule, tier-general).
    assert!(get("pick").text.contains("CompileFlagNatNatNat(pick)"), "{}", get("pick").text);
    assert!(get("fnot").text.contains("CompileFlagFlag(fnot)"), "{}", get("fnot").text);
    assert!(get("tsel").text.contains("CompileToksFlagNat(tsel)"), "{}", get("tsel").text);
    // The tier stages compose: the tier-1 ih is the over-applied self-call
    // with the tier-0 parameter riding in the curried arguments.
    assert!(get("tsel").text.contains("tsel_gen_conv(gf1)(f, VNil)"), "{}", get("tsel").text);
    // The non-recursive embedding travels once per type.
    let flag_embed = get("pick")
        .support
        .iter()
        .find(|(k, _)| k == "embed:Flag")
        .expect("Flag_gen_embed travels with the emission");
    assert!(flag_embed.1.contains("Off => VCon(0, VNil)"), "{}", flag_embed.1);
    assert_eq!(support_done.iter().filter(|k| *k == "embed:Flag").count(), 1);

    // Declines (design doc §8), each with its attribution and none a
    // signature disagreement.
    for (src, frag) in [
        // A fielded tier-0 parameter type: the rim's field rule (the
        // in-language checker accepts the shape — checker-accepts/
        // rim-declines, not a drift).
        ("fn fpk(p: Peek, n: Nat) -> Nat { n }", "fielded tier-0 parameter"),
        // A constructor VALUE at a callee's enum slot: the renderer's
        // per-slot check (design doc §7).
        ("fn con0(n: Nat) -> Nat { gate(Off, n) }", "declared parameter type"),
        // A tier-0 match nested inside a `Nat` induction's arm: the walker
        // (a case tree is not a value).
        (
            "fn nst(f: Flag, n: Nat) -> Nat { match n { Zero => 0, Succ(k) => match f { Off => k, On => 0 } } }",
            "declined this body",
        ),
        // …and in a value position: only the root may match.
        (
            "fn vp(f: Flag) -> Nat { Succ(match f { Off => 0, On => 1 }) }",
            "declined this body",
        ),
    ] {
        let d = decl_of(src);
        elab(&mut e, src, "decline fixture");
        let msg = match generate_in_language(&e, &d, &ctx) {
            Err(m) => m,
            Ok(_) => panic!("`{}` must decline", d.name),
        };
        assert!(msg.contains(frag), "{msg}");
        assert!(!msg.contains("disagreement"), "{msg}");
    }
}

/// The perturbed-library control for the tier-0 widening
/// (docs/certgen-tier0-params-design.md §10 item 6, in the style of
/// `certgen_tier1.rs`'s): perturb the walker's tier-0 dispatch slot
/// (`LetMatch(j, …)` → `LetMatch(Succ(j), …)` in `ta_arms_at`). The mutated
/// `pick` RENDERS — the mis-dispatched `LetMatch(1, …)` over a `Nat`
/// parameter reads back as a plausible `Nat`-induction model — its exactness
/// fixture even PASSES (at the depth-2 literals the two dispatches agree on
/// the answer), and the kernel refuses it at the open-argument invariant,
/// the strongest of the refusal sites. The library's own `t0_case_transcribes`
/// refuses the mutation first, asserted before the theorems are stripped.
#[test]
fn a_perturbed_t0_dispatch_slot_is_refused_by_the_kernel() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    support::with_decl_cache(&mut e, |e| elab(e, &LIB[..cut], "declarations prefix"));
    let bad_code = CODE.replace(
        "TYes(LetMatch(j, ta_wf_chain(arity, j, parts), Ret(RCons(0, RNil))))",
        "TYes(LetMatch(Succ(j), ta_wf_chain(arity, j, parts), Ret(RCons(0, RNil))))",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `ta_arms_at`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shells are the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    let mut bad = base();
    let sup = support_prelude();
    support::with_decl_cache(&mut bad, |e| elab(e, &sup, "support prelude"));
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    elab(&mut bad, CERT, "lib/certgen_cert.hthr");
    elab(&mut bad, "inductive Flag { Off, On }", "inductive Flag");
    elab(&mut bad, PICK, "fn pick");
    let em = generate_in_language(&bad, &decl_of(PICK), &GenCtx::new())
        .unwrap_or_else(|r| panic!("the mutation must render, not decline: {r}"));
    for (key, text) in &em.support {
        elab(&mut bad, text, key);
    }
    refuted(&mut bad, &em.text, "an emission dispatching on the wrong slot");
}
