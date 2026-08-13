//! The certifying generator's END-TO-END EMISSIONS and their mutation
//! controls — `docs/certifying-generator-design.md` §9 items 3–4.
//!
//! Every positive here is generated, elaborated and kernel-checked against the
//! support prelude: `add` (the hand-run reproduction), `dbl` (1-ary
//! recursive), `seven` (non-recursive), `third3` (3-ary recursive), and
//! `viaadd` via `add` — the v2 cross-function acceptance, a two-function
//! program with the callee's invariant re-derived inside it. (`viaadd` was
//! named `mul` until 2026-08-13; `certgen.rs`'s `VIAADD` says why it is not.)
//!
//! Support prelude: the library's declarations section (everything up to the
//! first theorem, the same cut `ir_v1.rs` uses) plus the named items a
//! generated emission's *proofs* elaborate against, sliced by parse span in
//! dependency order — the ∃-composition kit and its chain, `Converges`,
//! `CompileNat2`, `dbl`. Generated code references only these, never the
//! library's IR theorems, so the harness never pays the full-file
//! elaboration.
//!
//! **A binary of its own since 2026-08-12** (the non-`Nat` embeddings round):
//! `scripts/test`'s `ulimit -t` is per *process*, and this test plus
//! `certgen.rs`'s `in_language_transcriber` no longer fit one 300-second rail
//! together — each pays a ~40 s elaboration of `lib/certgen_code.hthr` on top
//! of its own work. Splitting is the free lever
//! `issues/certgen-harness-cost.md` records, and it is free because the two
//! tests never shared an elaborator in the first place. `scripts/test --fast`
//! skips this test by name; a round's final verification runs it.
//!
//! This is also cover (b) of `issues/retire-rust-transcriber.md`: with no
//! oracle left, a transcriber that silently started declining would show up
//! here as a panic, and one that emitted a different-but-plausible program
//! would be refused by its own exactness fixture or by the kernel.

use heather_elab::certgen::{generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
/// The library's one import (docs/modules-design.md §7). Elaborated whole,
/// which is why the arithmetic and order kit is no longer sliced out of
/// `LIB` item by item below — `import nat;` in the declarations prefix brings
/// all of it into scope.
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
/// The transcriber: the data and helpers, plus the two `match code` shells
/// claiming `certgen.transcribe` and `certgen.check_sig`
/// (docs/certgen-transcriber-in-language-design.md,
/// docs/fn-signature-reflection-design.md). This file IS the fragment's
/// definition — signature rule and body rule both — and nothing in Rust
/// decides it.
const CODE: &str = include_str!("../../../lib/certgen_code.hthr");
/// The certificate fold: the `Cert`/`CertOut` data and the `fn`s that fold an
/// `Ir` into a chain of ∃-kit applications
/// (docs/certgen-cert-expression-design.md). Ordinary program-layer code — no
/// `match code`, so no 52-branch gate — and the emitters read its answer back
/// instead of deciding the fold in Rust.
const CERT: &str = include_str!("../../../lib/certgen_cert.hthr");

/// Items a generated emission needs beyond the declarations prefix, in
/// dependency (file-consistent) order.
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

fn support() -> String {
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

/// A parsed `fn` declaration from the library — or from `nat`, where `add`
/// lives now — by name.
fn lib_decl(name: &str) -> Decl {
    let file = parse_file(LIB).expect("the library parses");
    let file = if file.items.iter().any(|i| matches!(i, Item::Decl(d) if d.name == name)) {
        file
    } else {
        parse_file(NAT).expect("`nat` parses")
    };
    file.items
        .into_iter()
        .find_map(|i| match i {
            Item::Decl(d) if d.name == name => Some(d),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the library declares fn {name}"))
}

fn decl_of(src: &str) -> Decl {
    let file = parse_file(src).unwrap_or_else(|e| panic!("test fn parses: {e:?}"));
    assert_eq!(file.items.len(), 1);
    file.items.into_iter().next().unwrap().into_decl()
}

/// Test functions with no hand-written certificate anywhere.
const SEVEN: &str = "fn seven(n: Nat) -> Nat { 7 }";
const THIRD3: &str =
    "fn third3(a: Nat, b: Nat, c: Nat) -> Nat { match c { Zero => b, Succ(k) => Succ(third3(a, b, k)) } }";
/// The v2 acceptance function: a foreign call whose argument is the
/// self-call's result. The zero arm spells `Zero` rather than `0` because the
/// walker is source-blind and derives `Zero` where the source said `0` (both
/// denote the same Nat) — spelling it this way keeps the pins about the
/// cross-function call rather than about literal spelling. Named `viaadd`
/// rather than `mul` since 2026-08-13, when `lib/std/nat.hthr` took the
/// latter name for a differently-spelled library function
/// (`crates/elab/tests/certgen.rs`'s `VIAADD` carries the reasons).
const VIAADD: &str =
    "fn viaadd(a: Nat, b: Nat) -> Nat { match b { Zero => Zero, Succ(k) => add(a, viaadd(a, k)) } }";


/// Everything here elaborates **as the library module**, so that the
/// declarations prefix's `import nat;` means what it means in the file.
fn elab(e: &mut Elaborator, src: &str, what: &str) {
    e.elab_module_source("ir_v1", src)
        .unwrap_or_else(|err| panic!("{what}:\n{}", err.render(src)));
}

fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    if e.elab_module_source("ir_v1", src).is_ok() {
        panic!("{what} elaborated, but it must fail");
    }
}

/// A prelude'd elaborator with `nat` in it — the closure `heather check
/// lib/ir_v1.hthr` walks, minus the root.
fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

/// One elaborator serves the whole acceptance: the support prelude and
/// `lib/certgen_code.hthr` are the expensive parts, so the positive emissions
/// and the mutation controls (renamed apart) all share it.
///
/// Positives — every one of them generated, elaborated and kernel-checked:
/// - `add` (the hand-run reproduction), `dbl` (1-ary recursive), `seven`
///   (non-recursive), `third3` (3-ary recursive) — §9 item 3;
/// - `viaadd` via `add` — the v2 cross-function acceptance: a two-function
///   program, `add`'s invariant re-derived inside it, the caller's
///   certificate consuming the callee's at an open argument.
///
/// This is cover (b) of `issues/retire-rust-transcriber.md`: with no oracle
/// left, a transcriber that silently started declining would show up here as a
/// panic, and one that emitted a different-but-plausible program would be
/// refused by its own exactness fixture or by the kernel.
#[test]
fn emissions_check_and_controls() {
    let mut e = base();
    let sup = support();
    // DELIBERATELY NO `support::with_decl_cache` HERE. The other certgen
    // binaries gate this same checked-in prefix through the shared
    // declaration cache (issues/elaborator-snapshot-across-test-binaries.md);
    // this one is the designated backstop: every full-suite run contains one
    // front-to-back kernel-checked elaboration of the support prelude,
    // `lib/certgen_code.hthr` and `lib/certgen_cert.hthr`, so a defect in the
    // cache mechanism itself cannot turn the whole family green.
    elab(&mut e, &sup, "support prelude");
    elab(&mut e, CODE, "lib/certgen_code.hthr");
    elab(&mut e, CERT, "lib/certgen_cert.hthr");
    elab(&mut e, SEVEN, "fn seven");
    elab(&mut e, THIRD3, "fn third3");
    elab(&mut e, VIAADD, "fn viaadd");

    let mut ctx = GenCtx::new();
    // The shared declarations an emission refers to — the per-type `embed_T`
    // and the per-signature record — travel with the emission and are
    // elaborated once each (docs/certgen-non-nat-embeddings-design.md §3).
    let mut support_done: Vec<String> = Vec::new();
    let generate = |e: &mut Elaborator,
                    ctx: &mut GenCtx,
                    support_done: &mut Vec<String>,
                    d: &Decl| {
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
    for d in [lib_decl("add"), lib_decl("dbl"), decl_of(SEVEN), decl_of(THIRD3), decl_of(VIAADD)] {
        generate(&mut e, &mut ctx, &mut support_done, &d);
    }
    // The viaadd emission really is the two-function program with the
    // re-derived callee invariant.
    let viaadd = ctx_get(&ctx, "viaadd");
    assert_eq!(viaadd.closure, vec!["add".to_string(), "viaadd".to_string()]);
    assert!(viaadd.text.contains("add_gen_conv_in_viaadd"));

    // §9 item 4, the mutation controls: perturb the known-good dbl emission
    // and the certificate refuses. Renamed apart so one elaborator serves
    // all of them (dbl's emission itself is already elaborated above).
    let good = &ctx_get(&ctx, "dbl").text;
    let rename = |s: &str, tag: &str| s.replace("dbl_gen", &format!("dbl{tag}_gen"));

    // (a) a reference off by one in the IR: the emitted proofs still spell
    // the correct chain, so the invariant no longer matches the body.
    let m = rename(good, "m1").replacen("LetCall(0, RCons(0, RNil)", "LetCall(0, RCons(3, RNil)", 1);
    assert_ne!(m, rename(good, "m1"));
    refuted(&mut e, &m, "off-by-one reference");

    // (b) a wrong-result fixture claim: the spec argument perturbed.
    let m = rename(good, "m2").replacen("embed_nat(dbl(2))", "embed_nat(dbl(3))", 1);
    assert_ne!(m, rename(good, "m2"));
    refuted(&mut e, &m, "wrong fixture result");

    // (c) the wrong constructor tag in the IR.
    let m = rename(good, "m3").replacen("LetCon(1, RCons(0, RNil)", "LetCon(0, RCons(0, RNil)", 1);
    assert_ne!(m, rename(good, "m3"));
    refuted(&mut e, &m, "wrong constructor tag");

    // (d) the instance claims a different spec function of the same arity.
    let m = rename(good, "m4").replacen("CompileNat1(dbl)", "CompileNat1(seven)", 1);
    assert_ne!(m, rename(good, "m4"));
    refuted(&mut e, &m, "wrong spec function");

    // (e) CALLEE IDENTITY, the control the retired `generate_forced` used to
    // play (issues/retire-rust-transcriber.md stage 2): a `LetCall` names a
    // slot in the program, so swapping the program's two members routes every
    // call to the other function while the whole emission stays well-formed.
    // `viaadd`'s self-call becomes an `add` call and vice versa, the run stops
    // converging, and the exactness fixture — a `refl` on a concrete run —
    // refuses it. Cheaper than the old control and cross-function, which the
    // old one was not.
    let mutant = ctx_get(&ctx, "viaadd")
        .text
        .replace("viaadd_gen", "viaaddm5_gen")
        .replace("_in_viaadd", "_in_viaaddm5")
        .replacen(
            "PFun(add_gen_body(), PFun(viaaddm5_gen_body(), PNil))",
            "PFun(viaaddm5_gen_body(), PFun(add_gen_body(), PNil))",
            1,
        );
    assert!(
        mutant.contains("PFun(viaaddm5_gen_body(), PFun(add_gen_body(), PNil))"),
        "the mutation must apply"
    );
    refuted(&mut e, &mutant, "a program whose members are swapped");
}

fn ctx_get<'a>(ctx: &'a GenCtx, name: &str) -> &'a heather_elab::certgen::Emission {
    ctx.iter().find(|e| e.name == name).expect("emission present")
}
