//! The certificate FOLD's controls (docs/certgen-cert-expression-design.md §8).
//!
//! Round A moved the ∃-kit fold — which lemma applies where, and whose
//! certificate discharges a call — out of `crates/elab/src/certgen.rs` and into
//! `lib/certgen/certgen_cert.hthr`. The property that move exists for is the one this
//! file tests: **a wrong fold is refused by the kernel**, not believed. One
//! edit to the library, and the emission it produces must fail to check rather
//! than prove anything about `dbl`.
//!
//! A binary of its own, for the reason `certgen.rs`'s header gives: checking a
//! `match code` shell is 52 branch telescopes against a library-inductive
//! motive, and `scripts/test`'s 8 MiB thread stack fits one per thread. This
//! file elaborates `lib/certgen/certgen_code.hthr` exactly once, and gets its own
//! 300-second `ulimit -t` rail into the bargain (the certgen binary is the
//! suite's second most expensive; `issues/certgen-harness-cost.md`).
//!
//! It carries the invocation's negative control too, because the cheapest
//! place to have "the fold is not declared" happen is *before* the mutated
//! copy is elaborated into the same session.

use heather_elab::certgen::{generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

use crate::support;

const LIB: &str = include_str!("../../../lib/certgen/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const CODE: &str = include_str!("../../../lib/certgen/certgen_code.hthr");
const CERT: &str = include_str!("../../../lib/certgen/certgen_cert.hthr");

/// The same support prelude `certgen.rs` slices — the ∃-composition kit and
/// its chain — because a fold perturbation shows up in the *invariant*, which
/// is the one part of an emission that needs the kit to elaborate at all.
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

fn span_of(name: &str) -> String {
    let file = parse_file(LIB).expect("the library parses");
    let span = file
        .items
        .iter()
        .find_map(|i| match i {
            Item::Inductive(ind) if ind.name == name => Some(ind.span),
            Item::Decl(d) if d.name == name => Some(d.span),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the library declares {name}"));
    LIB[span.start..span.end].to_string()
}

fn support() -> String {
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    let mut s = LIB[..cut].to_string();
    for name in SUPPORT_ITEMS {
        s.push('\n');
        s.push_str(&span_of(name));
        s.push('\n');
    }
    s
}

fn lib_decl(name: &str) -> Decl {
    parse_file(LIB)
        .expect("the library parses")
        .items
        .into_iter()
        .find_map(|i| match i {
            Item::Decl(d) if d.name == name => Some(d),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the library declares fn {name}"))
}

fn elab(e: &mut Elaborator, src: &str, what: &str) {
    e.elab_module_source("ir_v1", src)
        .unwrap_or_else(|err| panic!("{what}:\n{}", err.render(src)));
}

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).unwrap_or_else(|err| panic!("{}", err.render(LOGIC)));
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

/// The honesty control, and the round's whole point in one edit: perturb the
/// *library's* fold — `cert_rebind` claiming the match's arm result is rebound
/// at slot 1 rather than slot 0 — and what it produces must fail to check.
///
/// The perturbation is chosen to be one that *renders*: a fold that emits a
/// nonsensical instruction (a `Succ` with no argument, a callee tag with no
/// name) is refused one step earlier, by the readback, which is a decline and
/// not the property this control is about. This one produces a complete,
/// well-formed, plausible certificate — and a false one.
///
/// Two controls, as the transcriber's is (docs/certgen-transcriber-in-language-
/// design.md §10.6a): the file states its own acceptance, so its `refl`
/// theorems refuse the mutation at its declaration; strip those, and the
/// emitted invariant is the only thing on trial. Everything upstream of the
/// invariant is untouched by a fold perturbation — the IR, the program and the
/// two exactness fixtures come from the transcription model — so the mutant
/// emission is *plausible* right up to the theorem the kernel judges, which is
/// exactly the shape a real fold bug would have.
///
/// The positive half lives in `certgen.rs::emissions_check_and_controls`,
/// which elaborates `dbl`'s unperturbed emission — invariant and all — in the
/// same shape this test refuses.
#[test]
fn a_perturbed_fold_is_refused_by_the_kernel() {
    const GOOD: &str = "Zero => match next { RNil => CRet(RCons(0, RNil)), _ => CStuck },";
    const BAD: &str = "Zero => match next { RNil => CRet(RCons(1, RNil)), _ => CStuck },";
    let bad_code = CERT.replace(GOOD, BAD);
    assert_ne!(bad_code, CERT, "the mutation must apply");

    // (1) The file's own theorems refuse it, before anything downstream sees
    // it. Cheap: the declarations prefix is all a `Cert` pin needs.
    {
        let mut e = base();
        let cut = LIB.find("\ntheorem ").expect("the library has theorems");
        // Checked-in prefix through the shared declaration cache; the mutant
        // below faces the kernel unconditionally.
        support::with_decl_cache(&mut e, |e| elab(e, &LIB[..cut], "declarations prefix"));
        if e.elab_module_source("ir_v1", &bad_code).is_ok() {
            panic!("the library's own theorems must refuse a perturbed `cert_rebind`");
        }
    }

    let mut e = base();
    // The support prelude and the (unmutated) transcriber are checked-in
    // prefix too; the mutated fold and its emission face the kernel
    // unconditionally after the seal.
    support::with_decl_cache(&mut e, |e| {
        elab(e, &support(), "support prelude");
        elab(e, CODE, "lib/certgen/certgen_code.hthr");
    });

    // (2) The invocation's negative control, taken here because this session
    // has a transcriber and no fold yet: generation declines by naming the
    // library file it could not find, rather than emitting a body-only
    // file.
    let Err(msg) = generate_in_language(&e, &lib_decl("dbl"), &GenCtx::new()) else {
        panic!("with no `cert_body` in Ψ there is no certificate to emit")
    };
    assert!(msg.contains("cert_body"), "{msg}");

    // (3) The perturbed fold, with the file's own acceptance stripped so the
    // emission is what is on trial.
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    elab(&mut e, &bad_code[..thms], "mutated lib/certgen/certgen_cert.hthr");

    let wrong = generate_in_language(&e, &lib_decl("dbl"), &GenCtx::new())
        .expect("a wrong fold still emits — that is the point");
    // The mutation really is in the certificate and nowhere else: `dbl` is
    // 1-ary, so every reference in its IR is slot 0, and the emitted IR still
    // is — while the certificate now names slot 1.
    assert!(!wrong.ir_body.contains("RCons(1,"), "{}", wrong.ir_body);
    assert!(wrong.text.contains("Ret(RCons(1, RNil))"), "the mutation must reach the certificate");
    // Everything up to the invariant checks; the invariant is refused,
    // because `letmatch_conv` at the wrong rebinding continuation proves a
    // `Converges` about a different `Ir` than `dbl_gen_body()`.
    let upto = wrong.text.find("theorem dbl_gen_conv").expect("the emission proves an invariant");
    elab(&mut e, &wrong.text[..upto], "the mutant emission's IR, program and fixtures");
    if e.elab_module_source("ir_v1", &wrong.text[upto..]).is_ok() {
        panic!("a certificate folded at the wrong constructor tag must not check");
    }
}
