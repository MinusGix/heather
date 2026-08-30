//! Generated scale: what happens to the frontend as a *file* grows, with
//! nothing clever in it.
//!
//! Sources are generated here rather than committed as `.hthr` files. The
//! kernel suite's precedent is generated corpora too (`fixtures/terms.rs`),
//! and the argument is the same one plus a second: a swept family is four
//! files that differ only in a loop bound, so committing them commits the
//! generator's output instead of the generator, and the sweep can never be
//! extended without a diff nobody reads. The committed `.hthr` files stay
//! what they are for: real proofs, in `lib/`.

use crate::harness::{Case, Family};
use heather_elab::{Elaborator, IndexedRoute};

use super::{cloned_runner, image_runner, prelude, validate, validate_route};

pub fn families() -> Vec<Family> {
    vec![
        declarations(),
        image_first_ordinary(),
        image_first_inductive(),
        wide_inductive(),
        certified_dispatch(),
    ]
}

const LOGIC: &str = include_str!("../../../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../../../lib/std/list.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../../../lib/std/certified_lookup.hthr");

/// `n` independent declarations, each a small `fn` plus the `theorem` that
/// runs it. Every one of them looks the same to the elaborator; what grows
/// is Ψ, the global name table, and the number of times the kernel gate is
/// entered.
fn declarations() -> Family {
    let src = |n: u64| {
        let mut s = String::from(
            "fn base(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(k) } }\n",
        );
        for i in 0..n {
            s.push_str(&format!(
                "fn f{i}(a: Nat, b: Nat) -> Nat {{ let x = base(a); Succ(x) }}\n\
                 theorem t{i}(): f{i}(1, 2) = 2 {{ refl }}\n"
            ));
        }
        s
    };
    Family {
        name: "scale/declarations",
        what: "n independent fn+theorem pairs — file size with no pathology in it",
        unit: "decls",
        // Linear is the claim: nothing in a declaration should cost more
        // because an unrelated declaration exists. A superlinear reading
        // here means a per-declaration walk over Ψ.
        expect_slope: Some((0.80, 1.30)),
        cases: sweep("scale/declarations", &[16, 32, 64, 128], src),
    }
}

/// The cost of entering one new module after importing an increasingly large
/// ordinary prefix. The declaration itself is deliberately fixed; movement
/// with `n` is first-write detachment or a prefix-dependent lookup, not more
/// source work.
fn image_first_ordinary() -> Family {
    let sizes = [16, 64, 256, 1024];
    let sizes = if crate::harness::smoke() {
        &sizes[..1]
    } else {
        &sizes[..]
    };
    let cases = sizes
        .iter()
        .map(|&n| {
            let mut base = prelude();
            let mut prefix = String::new();
            for i in 0..n {
                prefix.push_str(&format!("fn imported_{i}(x: Nat) -> Nat {{ x }}\n"));
            }
            let errors = base.check_module_source("imported", &prefix);
            assert!(
                errors.is_empty(),
                "fixture `scale/image-first-ordinary:{n}` prefix does not check: {}",
                errors[0].render(&prefix)
            );
            let suffix = "fn suffix(x: Nat) -> Nat { x }".to_string();
            let image = base.semantic_image();
            let mut validation = image.elaborator();
            let errors = validation.check_module_source("suffix", &suffix);
            assert!(
                errors.is_empty(),
                "fixture `scale/image-first-ordinary:{n}` suffix does not check: {}",
                errors[0].render(&suffix)
            );
            let (run, cell) = image_runner(image, suffix);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect();

    Family {
        name: "scale/image-first-ordinary",
        what: "first ordinary declaration after an n-declaration semantic image",
        unit: "imported decls",
        expect_slope: Some((-0.35, 0.35)),
        cases,
    }
}

/// The matching first-write probe for the nominal type registry. The prefix
/// grows by independent one-constructor inductives while the suffix inductive
/// stays fixed, so a slope identifies imported `Types` detachment rather than
/// generated-term width.
fn image_first_inductive() -> Family {
    let sizes = [4, 16, 64, 256];
    let sizes = if crate::harness::smoke() {
        &sizes[..1]
    } else {
        &sizes[..]
    };
    let cases = sizes
        .iter()
        .map(|&n| {
            let mut base = prelude();
            let mut prefix = String::new();
            for i in 0..n {
                prefix.push_str(&format!(
                    "inductive Imported{i} {{ MkImported{i} }}\n"
                ));
            }
            let errors = base.check_module_source("imported_types", &prefix);
            assert!(
                errors.is_empty(),
                "fixture `scale/image-first-inductive:{n}` prefix does not check: {}",
                errors[0].render(&prefix)
            );
            let suffix = "inductive SuffixType { MkSuffixType }".to_string();
            let image = base.semantic_image();
            let mut validation = image.elaborator();
            let errors = validation.check_module_source("suffix_type", &suffix);
            assert!(
                errors.is_empty(),
                "fixture `scale/image-first-inductive:{n}` suffix does not check: {}",
                errors[0].render(&suffix)
            );
            let (run, cell) = image_runner(image, suffix);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect();

    Family {
        name: "scale/image-first-inductive",
        what: "first inductive after an n-inductive semantic image",
        unit: "imported types",
        expect_slope: Some((-0.35, 0.35)),
        cases,
    }
}

/// One tier-0 inductive with `n` constructors, and one `fn` that matches all
/// `n` arms. The lowering builds a recursor whose motive and branch
/// telescope grow with the constructor count, so this is the elaborator's
/// own generated-term volume — the cheap, unindexed version of what
/// `forded.rs` measures.
fn wide_inductive() -> Family {
    let src = |n: u64| {
        let ctors: Vec<String> =
            (0..n).map(|i| format!("K{i}(x{i}: Nat)")).collect();
        let arms: Vec<String> =
            (0..n).map(|i| format!("        K{i}(v) => Succ(v),")).collect();
        format!(
            "inductive W {{ {} }}\nfn wread(w: W) -> Nat {{\n    match w {{\n{}\n    }}\n}}\n",
            ctors.join(", "),
            arms.join("\n"),
        )
    };
    Family {
        name: "scale/wide-inductive",
        what: "an inductive with n constructors and the n-arm match over it",
        unit: "ctors",
        // Quadratic by construction and not a defect: the recursor has n
        // branches and each branch's telescope mentions the motive, so the
        // emitted term is O(n²) before anything checks it. The band is
        // recorded rather than claimed — what it guards is a *third* power
        // appearing.
        //
        // 2026-08-17, re-recorded (issues/frontend-benchmarks.md): **1.23**,
        // measured as the mean of six consecutive runs whose whole range was
        // 1.22-1.25. The 1.30 floor had been exited from below since at least
        // 2026-08-16 and the exit was not noise; the band now spans the
        // measurement +/-0.35, which is the same distance `--check` calls a
        // slope drift, so band and drift gate mean the same thing by "moved".
        expect_slope: Some((0.90, 1.60)),
        cases: sweep("scale/wide-inductive", &[4, 8, 16, 32], src),
    }
}

/// An n-row certified dispatch table, including its classifier soundness
/// bridge, payload interpreter, and one completeness theorem covering every
/// descriptor. This is the schema used by x86 opcode dispatch: adding an
/// opcode should add a row and an arm, not another layer of dependent
/// equality plumbing.
fn certified_dispatch() -> Family {
    let src = |n: u64| {
        let ctors: Vec<String> = (0..n).map(|i| format!("K{i}")).collect();
        let opcode_arms: Vec<String> = (0..n).map(|i| format!("        K{i} => {i},")).collect();
        let interpret_arms: Vec<String> = (0..n).map(|i| format!("        K{i} => {i},")).collect();
        let complete_arms: Vec<String> = (0..n).map(|i| format!("        K{i} => refl,")).collect();
        let rows = (0..n).rev().fold(String::from("Nil"), |tail, i| {
            format!("Cons(CertifiedEntry(key := {i}, value := K{i}, valid := refl), {tail})")
        });
        format!(
            "import certified_lookup;\n\
             import nat;\n\
             import list;\n\
             import option;\n\n\
             inductive Opcode {{ {} }}\n\n\
             fn opcode(form: Opcode) -> Nat {{\n    match form {{\n{}\n    }}\n}}\n\n\
             fn Matches(byte: Nat, form: Opcode) -> Type {{ byte = opcode(form) }}\n\n\
             fn rows() -> List<CertifiedEntry<Nat, Opcode>(Matches)> {{\n    {rows}\n}}\n\n\
             fn classify(byte: Nat) -> Option<Opcode> {{\n    lookup(Matches, nat::eq_dec, byte, rows())\n}}\n\n\
             theorem classify_sound(byte: Nat, form: Opcode,\n\
                 success: classify(byte) = Some(form)): Matches(byte, form) {{\n\
                 lookup_sound(Matches, nat::eq_dec, byte, rows(), form, success)\n}}\n\n\
             fn interpret(form: Opcode) -> Nat {{\n    match form {{\n{}\n    }}\n}}\n\n\
             theorem classify_complete(form: Opcode):\n\
                 classify(opcode(form)) = Some(form) {{\n    match form {{\n{}\n    }}\n}}\n",
            ctors.join(", "),
            opcode_arms.join("\n"),
            interpret_arms.join("\n"),
            complete_arms.join("\n"),
        )
    };

    let base = certified_lookup_base();
    let sizes = [2, 4, 8, 16];
    let sizes = if crate::harness::smoke() {
        &sizes[..1]
    } else {
        &sizes[..]
    };
    let cases = sizes
        .iter()
        .map(|&n| {
            let text = src(n);
            let mut validation = base.clone();
            let errors = validation.check_source(&text);
            assert!(
                errors.is_empty(),
                "fixture `scale/certified-dispatch:{n}` does not check ({} error(s)); first:\n{}",
                errors.len(),
                errors[0].render(&text)
            );
            let (run, cell) = cloned_runner(base.clone(), text);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect();

    Family {
        name: "scale/certified-dispatch",
        what: "an n-row certified table with generic soundness and completeness",
        unit: "rows",
        // 2026-08-28: 1.31 over 2/4/8/16 rows. The +/-0.35 band uses the
        // suite's ordinary definition of meaningful slope drift. This is a
        // structural guard, deliberately not a host-time budget.
        expect_slope: Some((0.95, 1.65)),
        cases,
    }
}

fn certified_lookup_base() -> Elaborator {
    let mut e = prelude();
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("certified_lookup", CERTIFIED_LOOKUP),
    ] {
        e.elab_module_source(name, src)
            .unwrap_or_else(|err| panic!("benchmark base module `{name}`: {}", err.render(src)));
    }
    e
}

/// Build one case per size: generate, validate, then hand the harness a
/// closure that checks the generated source against a cloned prelude.
pub fn sweep(
    what: &'static str,
    sizes: &[u64],
    src: impl Fn(u64) -> String,
) -> Vec<Case> {
    let base = prelude();
    // In smoke mode only the smallest size is built at all: validating a
    // generated source means elaborating it, so construction is where this
    // suite's seconds go (crate::harness::smoke).
    let sizes = if crate::harness::smoke() { &sizes[..1] } else { sizes };
    sizes
        .iter()
        .map(|&n| {
            let text = src(n);
            validate(&format!("{what}:{n}"), &text);
            let (run, cell) = cloned_runner(base.clone(), text);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect()
}

/// A swept indexed family whose smallest case first pins the classifier's
/// route. Later sizes share the same source schema and only vary its width.
pub fn indexed_sweep(
    what: &'static str,
    sizes: &[u64],
    declaration: &str,
    route: IndexedRoute,
    src: impl Fn(u64) -> String,
) -> Vec<Case> {
    let base = prelude();
    let sizes = if crate::harness::smoke() { &sizes[..1] } else { sizes };
    sizes
        .iter()
        .enumerate()
        .map(|(i, &n)| {
            let text = src(n);
            if i == 0 {
                validate_route(&format!("{what}:{n}"), &text, declaration, route);
            } else {
                validate(&format!("{what}:{n}"), &text);
            }
            let (run, cell) = cloned_runner(base.clone(), text);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect()
}
