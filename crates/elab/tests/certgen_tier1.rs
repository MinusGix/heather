//! TIER-1 SOURCE TYPES for the certifying generator — the acceptance of
//! `docs/certgen-tier1-source-types-design.md` §10: a fragment fn may
//! structurally recurse over a tier-1 (recursive, finitary-branching)
//! inductive parameter.
//!
//! Positives — every one generated, elaborated and kernel-checked end to end:
//! - `tsum` over `Toks` (linear: one recursive field), the round's hand-run
//!   retired into generated form;
//! - `esum` over `Expr2` — the `eval` shape the showcase named as this
//!   stage's customer: TWO recursive fields in one constructor, both
//!   induction hypotheses consumed in one arm, a foreign `add` combining
//!   them — a two-member program with the callee's invariant re-derived
//!   inside it;
//! - `th` over a three-constructor type with payload fields on either side
//!   of the children, a second `Nat` parameter, and a foreign call;
//! - `thas` — a tier-1 parameter WITH a tier-0 enumeration result, the two
//!   previous stages composed;
//! - `plen` over `TksP<Nat>` — a *parameterized instantiation*, generable
//!   since `datarepr` became the minting site for a monomorph's name
//!   (docs/datarepr-design.md §5.1 item 3). The decline it replaced survives
//!   beside it at an instantiation nobody minted.
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

/// Shared with the other `certgen_*` binaries, and guarded: a mutation that
/// leaves the text unparseable must not read as a refusal
/// (`support::refuted_by_the_kernel`).
fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    support::refuted_by_the_kernel(e, src, what)
}

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

const TOKS: &str = "inductive Toks { TNil, TCons(n: Nat, rest: Toks) }";
const TSUM: &str =
    "fn tsum(l: Toks) -> Nat { match l { TNil => Zero, TCons(n, rest) => Succ(tsum(rest)) } }";
const EXPR2: &str = "inductive Expr2 { Lit2(n: Nat), Plus2(l: Expr2, r: Expr2) }";
/// The `eval` shape (docs/showcase/README.md's derive-`Compile` row): both
/// children's recursions combined by a foreign call.
const ESUM: &str =
    "fn esum(x: Expr2) -> Nat { match x { Lit2(n) => n, Plus2(l, r) => add(esum(l), esum(r)) } }";
const TH: &str = "inductive Th { A, B(n: Nat, t: Th), C(t: Th, m: Nat) }";
const THF: &str =
    "fn th(x: Th, b: Nat) -> Nat { match x { A => b, B(n, t) => Succ(th(t, b)), C(t, m) => add(m, th(t, b)) } }";
const FLAG: &str = "inductive Flag { Off, On }";
const THAS: &str =
    "fn thas(l: Toks) -> Flag { match l { TNil => Off, TCons(n, rest) => On } }";

// THE LAYOUT INTERFACE for tier-1 emissions, pinned as literals exactly as
// `certgen.rs` pins the `Nat` ones: one arm fn per constructor in
// declaration order, the matched value's fields prepended in slot order
// (field `t` at distance `t`), the self-call gathering the child at its
// field slot in the recursion position.

const IR_TSUM: &str = "\
tsum_gen_arm0() = LetCon(0, RNil, Ret(RCons(0, RNil)))
tsum_gen_arm1() = LetCall(0, RCons(1, RNil), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))
tsum_gen_body() = LetMatch(0, Arm(tsum_gen_arm0(), Arm(tsum_gen_arm1(), NoArm)), Ret(RCons(0, RNil)))";

/// Two children: two self-calls (`l` at distance 0, `r` at distance 1 —
/// shifted by the first call's binding), then the foreign `add` (closure
/// member 0) over both results.
const IR_ESUM: &str = "\
esum_gen_arm0() = Ret(RCons(0, RNil))
esum_gen_arm1() = LetCall(1, RCons(0, RNil), LetCall(1, RCons(2, RNil), LetCall(0, RCons(1, RCons(0, RNil)), Ret(RCons(0, RNil)))))
esum_gen_body() = LetMatch(0, Arm(esum_gen_arm0(), Arm(esum_gen_arm1(), NoArm)), Ret(RCons(0, RNil)))";

/// Three constructors; payloads on either side of the children (`B(n, t)`,
/// `C(t, m)`); the second parameter `b` read from under the fields.
const IR_TH: &str = "\
th_gen_arm0() = Ret(RCons(1, RNil))
th_gen_arm1() = LetCall(1, RCons(1, RCons(3, RNil)), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))
th_gen_arm2() = LetCall(1, RCons(0, RCons(3, RNil)), LetCall(0, RCons(2, RCons(0, RNil)), Ret(RCons(0, RNil))))
th_gen_body() = LetMatch(0, Arm(th_gen_arm0(), Arm(th_gen_arm1(), Arm(th_gen_arm2(), NoArm))), Ret(RCons(0, RNil)))";

/// The end-to-end acceptance (design doc §10 items 1–5): the four positives
/// generated, elaborated and kernel-checked, then the declines with their
/// attributions.
#[test]
fn tier1_emissions_and_declines() {
    let mut e = base();
    let sup = support_prelude();
    support::with_decl_cache(&mut e, |e| {
        elab(e, &sup, "support prelude");
        elab(e, CODE, "lib/certgen_code.hthr");
        elab(e, CERT, "lib/certgen_cert.hthr");
    });
    for (src, what) in [
        (TOKS, "inductive Toks"),
        (TSUM, "fn tsum"),
        (EXPR2, "inductive Expr2"),
        (ESUM, "fn esum"),
        (TH, "inductive Th"),
        (THF, "fn th"),
        (FLAG, "inductive Flag"),
        (THAS, "fn thas"),
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
    generate(&mut e, &mut ctx, &decl_of(TSUM));
    generate(&mut e, &mut ctx, &lib_decl("add"));
    generate(&mut e, &mut ctx, &decl_of(ESUM));
    generate(&mut e, &mut ctx, &decl_of(THF));
    generate(&mut e, &mut ctx, &decl_of(THAS));
    // A tier-1 parameter that is NOT the recursion parameter: a plain body
    // beside it, and a `Nat` induction beside it — the design doc §2's "the
    // paths are independent" sentence, exercised (the parameter's slot must
    // embed at its own embedding in a `Nat`-shaped invariant).
    const TLEN0: &str = "fn tlen0(l: Toks) -> Nat { 0 }";
    const WNAT: &str =
        "fn wnat(l: Toks, n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(wnat(l, k)) } }";
    elab(&mut e, TLEN0, "fn tlen0");
    elab(&mut e, WNAT, "fn wnat");
    generate(&mut e, &mut ctx, &decl_of(TLEN0));
    generate(&mut e, &mut ctx, &decl_of(WNAT));

    let get = |name: &str| ctx.iter().find(|e| e.name == name).expect("emission present");
    assert_eq!(get("tsum").ir_body, IR_TSUM, "tsum transcribes differently");
    assert_eq!(get("esum").ir_body, IR_ESUM, "esum transcribes differently");
    assert_eq!(get("th").ir_body, IR_TH, "th transcribes differently");
    assert_eq!(get("tsum").closure, vec!["tsum".to_string()]);
    assert_eq!(get("esum").closure, vec!["add".to_string(), "esum".to_string()]);
    assert_eq!(get("th").closure, vec!["add".to_string(), "th".to_string()]);
    // The callee's invariant is re-derived inside the tier-1 program, and
    // the tier-1 induction consumes its own over-applied self-call as the
    // ih at each child (design doc §1).
    assert!(get("esum").text.contains("add_gen_conv_in_esum"));
    assert!(get("esum").text.contains("esum_gen_conv(gf0, VNil)"));
    assert!(get("esum").text.contains("esum_gen_conv(gf1, VNil)"));
    // The recursive embedding and the per-signature records.
    let toks_embed = get("tsum")
        .support
        .iter()
        .find(|(k, _)| k == "embed:Toks")
        .expect("Toks_gen_embed travels with the emission");
    assert!(toks_embed.1.contains("VCons(embed_nat(gf0), VCons(Toks_gen_embed(gf1), VNil))"));
    assert!(get("tsum").text.contains("CompileToksNat"));
    assert!(get("thas").text.contains("CompileToksFlag"));

    // Declines (design doc §8), each with its attribution and none a
    // signature disagreement.
    for (src, frag) in [
        // Two tier-1 parameters: `SigOut` carries one position.
        ("fn two1(a: Toks, b: Toks) -> Nat { 0 }", "signature checker"),
        // A tier-1-parameter callee has no callee marker.
        ("fn callt(l: Toks) -> Nat { tsum(l) }", "outside the fragment"),
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
    // FLIP RECORDED (docs/datarepr-design.md §5.1 item 3): a parameterized
    // instantiation was a decline here — the in-language checker accepted the
    // lowering and the rim had no name to spell `embed_T` with. `datarepr` is
    // the minting site, so with a repr declared the same fn GENERATES, and
    // the emission is kernel-checked like any other.
    {
        elab(&mut e, "inductive TksP<A> { PN, PC(h: A, t: TksP<A>) }", "inductive TksP");
        elab(
            &mut e,
            "datarepr TksPNat for TksP<Nat> := repr::naive();",
            "datarepr TksPNat",
        );
        let src = "fn plen(l: TksP<Nat>) -> Nat { match l { PN => Zero, PC(h, t) => Succ(plen(t)) } }";
        elab(&mut e, src, "plen");
        generate(&mut e, &mut ctx, &decl_of(src));
        // The minted name is what names the artifacts; the TYPE is still
        // written applied, which is the split the flip turned on.
        let em = ctx.iter().find(|e| e.name == "plen").expect("emission present");
        assert!(em.text.contains("CompileTksPNatNat"), "{}", em.text);
        let embed = em
            .support
            .iter()
            .find(|(k, _)| k == "embed:TksPNat")
            .expect("TksPNat_gen_embed travels with the emission");
        assert!(embed.1.contains("fn TksPNat_gen_embed(gx: TksP<Nat>)"), "{}", embed.1);
    }
    // The decline that REMAINS: an instantiation no `datarepr` has minted a
    // name for. The flip turned on the minting, not the guess.
    {
        elab(&mut e, "inductive TksQ<A> { QN, QC(h: A, t: TksQ<A>) }", "inductive TksQ");
        let src = "fn plen2(l: TksQ<Nat>) -> Nat { match l { QN => Zero, QC(h, t) => Succ(plen2(t)) } }";
        let d = decl_of(src);
        elab(&mut e, src, "plen2");
        let msg = match generate_in_language(&e, &d, &ctx) {
            Err(m) => m,
            Ok(_) => panic!("plen2 must decline"),
        };
        assert!(msg.contains("no `datarepr` has minted a name"), "{msg}");
    }
}

/// The perturbed-library control for the tier-1 widening
/// (docs/certgen-tier1-source-types-design.md §10 item 6, in the style of
/// `certgen_controls.rs`): perturb the walker's ih marker to hand back the
/// arm's FIRST FIELD as the self-call's value instead of the call's result
/// (`RLoc(0)` → `RFld(0)` in `ta_ih_at`). The mutation RENDERS — right
/// instruction, right arity, references in range — and the program computes
/// the wrong thing, so it is refused by the kernel at the emission's own
/// exactness fixture, not by any decline. The library's own theorems refuse
/// the mutation first (`tier1_ih_marker`, `tier1_linear_transcribes`), which
/// is asserted before they are stripped.
#[test]
fn a_perturbed_tier1_ih_value_is_refused_by_the_kernel() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    support::with_decl_cache(&mut e, |e| elab(e, &LIB[..cut], "declarations prefix"));
    let bad_code = CODE.replace(
        "TNum(t) => TExp(PSelf(t, PEnd), RLoc(0), 1)",
        "TNum(t) => TExp(PSelf(t, PEnd), RFld(0), 1)",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `ta_ih_at`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shells are the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    let mut bad = base();
    let sup = support_prelude();
    support::with_decl_cache(&mut bad, |e| elab(e, &sup, "support prelude"));
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    elab(&mut bad, CERT, "lib/certgen_cert.hthr");
    elab(&mut bad, TOKS, "inductive Toks");
    elab(&mut bad, TSUM, "fn tsum");
    let em = generate_in_language(&bad, &decl_of(TSUM), &GenCtx::new())
        .unwrap_or_else(|r| panic!("the mutation must render, not decline: {r}"));
    for (key, text) in &em.support {
        elab(&mut bad, text, key);
    }
    refuted(&mut bad, &em.text, "an emission whose ih value is the arm's field");
}
