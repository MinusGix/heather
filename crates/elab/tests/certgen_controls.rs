//! The perturbed-LIBRARY controls for the certifying generator's two
//! in-language analyzers: the transcriber (`lib/certgen_code.hthr`'s body
//! rule) and the signature checker (its `check_sig`). The certificate fold's
//! own control is `certgen_cert.rs`; the positives both of these are measured
//! against are `certgen.rs`.
//!
//! Why a binary rather than two more tests in `certgen.rs`: `ulimit -t` is
//! per process, and every one of these tests elaborates
//! `lib/certgen_code.hthr` — the suite's most expensive single item — into an
//! elaborator of its own. Four of them in one binary passed the 300-second
//! rail when the certificate fold's evaluation joined the generator
//! (2026-08-12); splitting costs nothing, because each control builds its own
//! session in any case. The 8 MiB `RUST_MIN_STACK` rail is unaffected and
//! still says one `match code` shell per *thread*.

use heather_elab::certgen::{generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

mod support;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const CODE: &str = include_str!("../../../lib/certgen_code.hthr");
/// The certificate fold (docs/certgen-cert-expression-design.md), unperturbed
/// in this file: a wrong *transcription* still has to be folded into a
/// certificate, or the control below would be testing the fold's absence.
const CERT: &str = include_str!("../../../lib/certgen_cert.hthr");

/// 1-ary recursive, a `Succ` arm nesting two constructors around the ih —
/// `certgen.rs`'s `IR_DBL`, repeated here because the honesty control's whole
/// point is that a perturbed transcriber does *not* produce it.
const IR_DBL: &str = "\
dbl_gen_arm_zero() = LetCon(0, RNil, Ret(RCons(0, RNil)))
dbl_gen_arm_succ() = LetCall(0, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil)))))
dbl_gen_body() = LetMatch(0, Arm(dbl_gen_arm_zero(), Arm(dbl_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// Two fields, one of them computed — the smallest fixture that can see a
/// field-order mutation (`certgen_nonnat.rs`'s `PACK`).
const PACK: &str =
    "fn pack(n: Nat) -> Both { match n { Zero => BNone, Succ(k) => BSome(k, Succ(k)) } }";

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

fn lib_item(name: &str) -> String {
    span_of(name)
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

/// The in-language honesty control (design doc §10.6a), in a test of its own
/// **because of the stack**: checking one `match code` shell means checking 52
/// branch telescopes against a library-inductive motive, and two of those in
/// one test thread overflow the 8 MiB `scripts/test` gives it. One shell per
/// thread is also the cheaper arrangement. (The file it lives in is its own
/// for the *CPU* rail, which is a different limit — see this module's header.)
#[test]
fn a_perturbed_transcriber_is_refused_by_the_kernel() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    // The checked-in declarations prefix goes through the shared declaration
    // cache; every mutant below faces the kernel unconditionally (a mutated
    // declaration has a different content key in any case, so no cache could
    // vouch for it — but the seal keeps the line bright).
    support::with_decl_cache(&mut e, |e| elab(e, &LIB[..cut], "declarations prefix"));
    // The honesty control, and the whole architecture in one edit: perturb the
    // *library* — `ta_succ` emitting the `Zero` tag — and what it produces
    // must fail to check rather than prove anything about `dbl`.
    //
    // It arrives as two controls, because the file states its own acceptance:
    // the perturbed `dist` is refused by `certgen_code.hthr`'s own theorems
    // before anything downstream sees it. Strip those, and the emission is the
    // only thing on trial — its *exactness fixture*, which needs nothing but
    // the declarations prefix, so this control costs no kit.
    // The mutation is chosen to be one that RENDERS
    // (docs/certgen-cert-expression-design.md §8 item 3): `ta_succ`'s
    // instruction keeps its tag and its argument and loses only the reference
    // to *itself*, so the emitted IR is well-formed and computes the wrong
    // thing — a `Succ` arm that returns the induction hypothesis's value
    // instead of the two constructors around it. A wrong TAG would be refused
    // one step earlier, by the readback's constructor-arity check, which is a
    // decline and a weaker control (2026-08-12: that is what the previous
    // mutation, `PCon(1, …)` → `PCon(0, …)`, became once the readback learned
    // the result type's constructor table).
    let bad_code = CODE.replace(
        "TExp(PCon(1, QCons(res, QNil), pre), RLoc(len), Succ(len))",
        "TExp(PCon(1, QCons(res, QNil), pre), RLoc(0), Succ(len))",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `dist`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shell is the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    // The failed elaboration above stopped at a theorem, which is *before* the
    // file's shell, so this is still the only 52-branch check in this thread.
    let mut bad = base();
    support::with_decl_cache(&mut bad, |e| elab(e, &LIB[..cut], "declarations prefix"));
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    // The fold is unperturbed here: a wrong *transcription* must still be
    // folded into a certificate, or this control would be testing the fold's
    // absence instead of the transcriber's error.
    elab(&mut bad, CERT, "lib/certgen_cert.hthr");
    elab(&mut bad, &lib_item("dbl"), "fn dbl");
    let wrong = generate_in_language(&bad, &lib_decl("dbl"), &GenCtx::new())
        .expect("a wrong transcriber still emits — that is the point");
    assert_ne!(wrong.ir_body, IR_DBL, "the mutation must change the transcription");
    // Everything up to the invariant: the IR, the program, and the two
    // literal-fuel fixtures. The fixtures are `refl` on a concrete run, so a
    // transcription that reads the wrong slots is `Stuck` there.
    let upto = wrong.text.find("theorem dbl_gen_conv").expect("the emission proves an invariant");
    refuted(&mut bad, &wrong.text[..upto], "mutated-transcriber emission");
}

/// The agreement property's loud half (docs/fn-signature-reflection-design.md
/// §4): perturb the LIBRARY's signature rule — `sig_finish` accepting the
/// nullary signature — and a nullary fn's generation must fail with the
/// **disagreement** message, never silently ride either verdict. Own test for
/// the same stack reason as above (a second `match code` shell check per
/// thread), and with the file's own theorems stripped first, because they
/// refuse the mutation before anything downstream sees it — the same
/// two-controls shape as the transcriber's honesty control.
#[test]
fn a_perturbed_signature_checker_is_a_loud_disagreement() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    // The checked-in declarations prefix goes through the shared declaration
    // cache; every mutant below faces the kernel unconditionally (a mutated
    // declaration has a different content key in any case, so no cache could
    // vouch for it — but the seal keeps the line bright).
    support::with_decl_cache(&mut e, |e| elab(e, &LIB[..cut], "declarations prefix"));
    // `sig_finish`'s default arm is where "a bare `Nat` is a nullary fn" lives
    // (the walk only ever mints `SFn` from a Π), so accepting it at arity 0 is
    // the one-token perturbation that makes the library's verdict disagree
    // with the Rust peel's.
    let bad_code = CODE.replace(
        "        _ => SigNo,
    }
}

// ------",
        "        _ => SigYes(0, 0),
    }
}

// ------",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `sig_finish`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shells are the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    // The failed elaboration stopped at a theorem, before either shell, so the
    // stripped file's two shells are this thread's only 52-branch checks.
    let mut bad = base();
    support::with_decl_cache(&mut bad, |e| elab(e, &LIB[..cut], "declarations prefix"));
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    let nofn = "fn nofn2() -> Nat { 0 }";
    elab(&mut bad, nofn, "fn nofn2");
    let Err(msg) = generate_in_language(&bad, &decl_of(nofn), &GenCtx::new()) else {
        panic!("a nullary fn must not generate")
    };
    assert!(msg.contains("disagreement"), "{msg}");
}


/// The FIELDS half of the transcriber's honesty control
/// (docs/certgen-ctor-fields-design.md §4, `ta_flds_cons`): perturb the
/// LIBRARY's field merge so a two-field constructor collects its slots in the
/// wrong order, and the emission must fail to check.
///
/// Chosen, like the `dbl` control above, to be a mutation that **renders**
/// (docs/certgen-cert-expression-design.md §8 item 3) rather than one that
/// declines: `ta_flds_cons` keeps the tag, keeps the arity and keeps every
/// reference — it only snocs the new field where it should cons it, which is
/// exactly the shape `ta_call_arg` legitimately uses for a call's arguments.
/// So the readback's arity check passes, the IR is well-formed, and what is
/// wrong is the *value*: `pack` builds `BSome(Succ(k), k)` where its own
/// exactness fixture says `BSome(k, Succ(k))`. A one-field constructor cannot
/// see the mutation at all, which is why the fixture here has two.
///
/// Own test for the stack reason this file's header gives: one `match code`
/// shell per thread.
#[test]
fn a_perturbed_field_merge_is_refused_by_the_kernel() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    support::with_decl_cache(&mut e, |e| elab(e, &LIB[..cut], "declarations prefix"));
    let bad_code = CODE.replace(
        "QCons(shift_ref(ra, len), args)),
        VNo => TStuck,",
        "qsnoc(args, shift_ref(ra, len))),
        VNo => TStuck,",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `ta_flds_cons`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shell is the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    let mut bad = base();
    support::with_decl_cache(&mut bad, |e| elab(e, &LIB[..cut], "declarations prefix"));
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    // The fold is unperturbed: a wrong *transcription* must still be folded.
    elab(&mut bad, CERT, "lib/certgen_cert.hthr");
    elab(&mut bad, "inductive Both { BNone, BSome(a: Nat, b: Nat) }\n", "the result type");
    elab(&mut bad, PACK, "fn pack");
    let wrong = generate_in_language(&bad, &decl_of(PACK), &GenCtx::new())
        .expect("a wrong field merge still emits — that is the point");
    assert!(
        wrong.ir_body.contains("LetCon(1, RCons(0, RCons(1, RNil))"),
        "the mutation must swap the two field slots: {}",
        wrong.ir_body
    );
    for (key, text) in &wrong.support {
        elab(&mut bad, text, key);
    }
    // Everything up to the invariant: the IR, the program and the two
    // literal-fuel fixtures, which are `refl` on a concrete run and therefore
    // `Stuck` at a constructor built from the wrong slots.
    let upto = wrong.text.find("theorem pack_gen_conv").expect("the emission proves an invariant");
    refuted(&mut bad, &wrong.text[..upto], "perturbed-field-merge emission");
}
