//! The third in-language derived artifact (issues/quotation-stage-artifacts.md):
//! `lib/lang/vec_code.hthr`'s `tabulate_code` kernel-checks at `Layer::Meta`, the
//! evaluation hook routes `elab_container_ih`'s phase 2 through it, and the
//! emitted terms are convertible with the Rust `vec::tabulate` oracle's —
//! adequacy, not just typing.
//!
//! Same axes as in_language_fold.rs (docs/testing-generated-terms.md), read for
//! the one construct whose use site is not a method the user writes: a
//! self-call over a container field, `kids.map(size)`
//! (docs/container-fields.md §4.2). Two consequences for the axis list:
//!
//! * **The neutral scrutinee is the default here, not the hard case.** The
//!   length a container IH tabulates at is the arm's own field length, always a
//!   bound variable — so every fixture below is the neutral one, and the
//!   literal case appears only downstream, at an application, where the
//!   theorems make it compute.
//! * **The open element type is the interesting axis** and the reason this
//!   template exists: `vec::tabulate` has to shift its `B` by `d + 1` under the
//!   index binder and by `d` outside it, a distinction its own comment calls
//!   "invisible at a closed `B`" (vec.rs:275-278). The template has no
//!   arithmetic to get wrong; `open_result` below is what would notice if the
//!   *hook plumbing* did.
//!
//! Plus the vacuity guard in_language_fold.rs introduced, sharpened: these
//! fixtures also contain a `.fold`, which routes through `fold_code`, so plain
//! inequality against the Rust path would be satisfied by the fold alone. The
//! baseline here is therefore the lib *without this round's templates*
//! ([`lib_before_this_round`]), which isolates `vec.tabulate`.

use heather_elab::Elaborator;
use heather_kernel::conv::conv_term;
#[cfg(feature = "value-metrics")]
use heather_kernel::conv::conv_term_profiled;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};
#[cfg(feature = "value-metrics")]
use heather_kernel::value::ValueMetrics;

const LIB: &str = include_str!("../../../lib/lang/vec_code.hthr");

/// The lib as it stood before `tabulate_code` — `map_code` and `fold_code`
/// only. The cut is by declaration text rather than by line number so that a
/// rename breaks this loudly instead of silently truncating the wrong prefix.
fn lib_before_this_round() -> &'static str {
    let cut = LIB
        .find("meta fn tabulate_code")
        .expect("lib/lang/vec_code.hthr declares `tabulate_code`");
    // Back up over the declaration's header comment, which is the block of
    // `//` lines immediately above it.
    let head = &LIB[..cut];
    let keep = head
        .rfind("\n\n")
        .map(|i| i + 1)
        .expect("the templates are separated by blank lines");
    &LIB[..keep]
}

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_in(lib: &str, src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(lib).unwrap_or_else(|err| panic!("{}", err.render(lib)));
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_with_lib(src: &str) -> Elaborator {
    elab_in(LIB, src)
}

/// The preamble every fixture shares: `add`, and the `Rose` whose `Node` has a
/// container field — the shape that makes a recursive call over `kids` elaborate
/// to a `tabulate` and to nothing else (vec.rs:258-262).
const PRE: &str = "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }
";

/// The fixtures, one container self-call per axis. Declared identically with
/// and without the lib in scope; the theorems apply them to literal trees, so
/// they are adequacy checks and not just typing.
fn fixtures() -> String {
    format!(
        "{PRE}
fn size(r: Rose) -> Nat {{
    match r {{
        Node(l, n, kids) =>
            Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
    }}
}}
theorem size_computes(): size(Node(0, 2, [Node(0, 0, []), Node(0, 0, [])])) = 3 {{ refl }}

// A recursion whose *result* type mentions an ambient variable: the tabulate's
// `B` is `[Nat; Succ(m)]`, the axis a `Nat`-valued recursion cannot reach and
// the one the Rust schema needs its two different shifts for.
fn heads(m: Nat, z: [Nat; Succ(m)], r: Rose) -> [Nat; Succ(m)] {{
    match r {{
        Node(l, n, kids) =>
            kids.map(heads).fold(z, λ (a: [Nat; Succ(m)]) (b: [Nat; Succ(m)]) => a),
    }}
}}

// A checking position: the tabulated vector goes straight into an argument
// whose type is declared, so the emitted term meets a goal rather than being
// inferred into one. (A `let` cannot do this job here — a match arm is an
// expression, not a block — so argument position is the checking axis.)
fn sum(n: Nat, v: [Nat; n]) -> Nat {{ v.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }}
fn checked_size(r: Rose) -> Nat {{
    match r {{
        Node(l, n, kids) => Succ(sum(n, kids.map(size))),
    }}
}}
theorem checked_computes(): checked_size(Node(0, 1, [Node(0, 0, [])])) = 2 {{ refl }}
"
    )
}

/// The body of the *last* committed binding — the fixture each cross-check
/// declares last, so no name table is needed.
fn last_body(e: &Elaborator) -> (Term, Type, Level) {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { ty, level, body: Some(b), .. } => {
            ((**b).clone(), (**ty).clone(), level.clone())
        }
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

/// The Ψ a binding's body is scoped over: every binding *before* it. A body
/// mentions only older globals, and with de Bruijn global indices the newest
/// binding is index 0 — so reading the last binding's body against the full
/// Ψ shifts every global by one (its own `add` resolves to itself). The
/// stored-annotation application rule never consulted Ψ for a head's type and
/// let that pass; the typed rule reads the head's declared type and does not.
fn owning_psi(e: &Elaborator) -> GlobalCtx {
    let mut bindings = e.psi().bindings.to_vec();
    bindings.pop().expect("a binding");
    GlobalCtx::new(bindings)
}

#[test]
fn the_fixtures_elaborate_and_compute_through_the_hook() {
    elab_with_lib(&fixtures());
}

#[test]
fn the_fixtures_still_elaborate_without_the_lib() {
    // A file that never declares `tabulate_code` takes the Rust path as before
    // — the silent decline surface_fin.rs tested with no template in existence
    // (`the_container_ih_still_takes_the_rust_path`), now with one that is
    // merely out of scope.
    elab(&fixtures());
}

/// The cross-check proper: for each fixture, the hook-emitted declaration body
/// and the Rust-emitted one are convertible at the declaration's own statement,
/// at `Layer::Prog`. A container IH is *always* at a neutral length, so no
/// theorem can decide these — conversion is the only instrument that can.
#[test]
fn hook_output_is_convertible_with_the_rust_oracle() {
    for fixture in [
        "fn probe(r: Rose) -> Nat {
             match r {
                 Node(l, n, kids) =>
                     Succ(kids.map(probe).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }
         }",
        "fn probe(m: Nat, z: [Nat; Succ(m)], r: Rose) -> [Nat; Succ(m)] {
             match r {
                 Node(l, n, kids) =>
                     kids.map(probe).fold(z, λ (a: [Nat; Succ(m)]) (b: [Nat; Succ(m)]) => a),
             }
         }",
    ] {
        let src = format!("{PRE}{fixture}");
        let hooked = elab_with_lib(&src);
        let rust = elab(&src);
        let (ht, hty, hl) = last_body(&hooked);
        let (rt, _, _) = last_body(&rust);
        // The vacuity guard (in_language_fold.rs:132), sharpened: every fixture
        // here also folds, so `ht != rt` alone would be satisfied by
        // `fold_code` firing while `tabulate_code` declined. Comparing against
        // the lib *before* this round holds the fold fixed and leaves the
        // tabulate as the only difference.
        let baseline = elab_in(lib_before_this_round(), &src);
        let (bt, _, _) = last_body(&baseline);
        assert!(
            ht != bt,
            "`vec.tabulate` declined on:\n{fixture}\nso the conversion below \
             would be testing `fold_code` and nothing else"
        );
        assert!(ht != rt, "the hook declined entirely on:\n{fixture}");
        let empty = LocalCtx::nil();
        #[cfg(feature = "value-metrics")]
        if std::env::var_os("HEATHER_VALUE_METRICS").is_some() {
            let metrics = ValueMetrics::default();
            conv_term_profiled(
                &owning_psi(&hooked), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000, &metrics,
            )
            .unwrap_or_else(|e| panic!("hook and Rust `tabulate` disagree on:\n{fixture}\n{e:?}"));
            eprintln!("tabulate oracle metrics: {:?}", metrics.snapshot());
            continue;
        }
        conv_term(&owning_psi(&hooked), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000)
            .unwrap_or_else(|e| panic!("hook and Rust `tabulate` disagree on:\n{fixture}\n{e:?}"));
    }
}

// -- negative controls ------------------------------------------------------

/// The rigidity control, and the round's finding.
///
/// docs/surface-fin-indexing-design.md §9 predicted `tabulate_code` would be
/// rigid in `map`'s sense, because its result `[B; k]` is length-indexed. The
/// index really does pin the *shape* — no arm can return a vector of the wrong
/// length — but rigidity needs the elements pinned too, and the elements come
/// out of `f : Fin(Succ(zk)) -> B`, which accepts `FZ` exactly where it accepts
/// `FS(i)`. The index shift is a choice, so the constant-head tabulate below —
/// every component `f(FZ)` — checks at the declared signature and registers for
/// `vec.tabulate` exactly as the real one does (registration checks the type,
/// never the body: docs/meta-def-registration-design.md §2.2).
///
/// The heuristic's boundary is therefore not "is the result indexed": an
/// indexed container of unconstrained elements constrains nothing about them.
#[test]
fn a_mutated_arm_checks_but_fails_the_cross_check() {
    let constant_tabulate = r#"
meta fn tabulate_code(g: Ctx) for vec.tabulate -> Code(g |-
    (B: Type<0>) -> (k: Nat) -> (f: Fin(k) -> B) -> [B; k]
) {
    code {
        fun (B: Type<0>) => fun (k: Nat) =>
            match k as λ z => (Fin(z) -> B) -> [B; z] {
                Zero => fun (f: Fin(0) -> B) => [],
                Succ(zk, ih) => fun (f: Fin(Succ(zk)) -> B) =>
                    cons(f(FZ), ih(fun (i: Fin(zk)) => f(FZ))),
            }
    }
}
"#;
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(constant_tabulate).unwrap_or_else(|err| {
        panic!("the mutated template itself checks: {}", err.render(constant_tabulate))
    });

    // Applied to a tree whose children differ, it recurses into the first child
    // twice and misses the second, so the theorem that pins the size fails.
    let computing = format!(
        "{PRE}
         fn size(r: Rose) -> Nat {{
             match r {{
                 Node(l, n, kids) =>
                     Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}
         theorem t(): size(Node(0, 2, [Node(0, 1, [Node(0, 0, [])]), Node(0, 0, [])])) = 4 {{ refl }}"
    );
    assert!(
        e.elab_source(&computing).is_err(),
        "the constant-head tabulate should not size a two-child tree correctly — if \
         this checked, the hook is not routing the container IH through `tabulate_code`"
    );

    // At the definition site nothing computes and only conversion can tell: the
    // emitted term must *fail* to convert with the Rust oracle's.
    let neutral = format!(
        "{PRE}
         fn probe(r: Rose) -> Nat {{
             match r {{
                 Node(l, n, kids) =>
                     Succ(kids.map(probe).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}"
    );
    let mut wrong = Elaborator::with_prelude().expect("prelude");
    wrong.elab_source(constant_tabulate).expect("the mutated template checks");
    wrong
        .elab_source(&neutral)
        .unwrap_or_else(|err| panic!("the neutral instance still types: {}", err.render(&neutral)));
    let rust = elab(&neutral);
    let (wt, wty, wl) = last_body(&wrong);
    let (rt, _, _) = last_body(&rust);
    let empty = LocalCtx::nil();
    assert!(
        conv_term(&owning_psi(&wrong), &empty, Layer::Prog, &wt, &rt, &wty, &wl, 1_000_000).is_err(),
        "the constant-head tabulate is not `tabulate`: the cross-check must reject it"
    );
}

/// The whole family coexists: one expression whose container IH tabulates,
/// whose `.fold` folds, and whose `xs[i]` projects, each routed to its own slot
/// (docs/meta-def-registration-design.md §8 item 5's positive half). This is
/// the fixture that would notice a hook dispatching on the wrong slot now that
/// every slot in the vocabulary has a claimant.
#[test]
fn every_slot_routes_independently() {
    let src = format!(
        "{PRE}
         fn size(r: Rose) -> Nat {{
             match r {{
                 Node(l, n, kids) =>
                     Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
             }}
         }}
         fn first_size(rs: [Rose; 2]) -> Nat {{
             rs.map(λ (r: Rose) => size(r))[0]
         }}
         theorem fs(): first_size([Node(0, 1, [Node(0, 0, [])]), Node(0, 0, [])]) = 2 {{ refl }}"
    );
    elab_with_lib(&src);
}
