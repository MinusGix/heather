//! Declaration-slice replay (`docs/declaration-slice-replay-design.md`): after
//! an edit, `check_module_delta_from` reproduces the unchanged items of a
//! module from its previous delta and elaborates the rest, and what comes out
//! is what fresh elaboration produces — the same Ψ, the same events, the same
//! scope, the same warnings. Each edit shape below states which items may
//! replay; the negative shapes are the ones where nothing after the edit may.
//!
//! Every shape runs at gate width one and four: replayed bindings are
//! rechecked on the elaborator's thread whatever the width, beside the pool
//! the elaborated items use.

use heather_elab::{Elaborator, ModuleDelta, ModuleDependencyIdentity, SliceReport};

use crate::support;

const ADD: &str = "fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}";
const DOUBLE: &str = "fn double(n: Nat) -> Nat { add(n, n) }";
const ADD_ZERO_A: &str = "theorem add_zero(n: Nat): add(n, 0) = n {
    match n as λ z => add(z, 0) = z {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(k, 0), k, ih),
    }
}";
const DOUBLE_ZERO: &str = "theorem double_zero(): double(0) = 0 { refl }";
const TRIPLE: &str = "fn triple(n: Nat) -> Nat { add(n, double(n)) }";

fn module(items: &[&str]) -> String {
    items.join("\n\n") + "\n"
}

fn base() -> String {
    module(&[ADD, DOUBLE, ADD_ZERO_A, DOUBLE_ZERO, TRIPLE])
}

fn elaborator(workers: usize) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.set_kernel_workers(workers);
    e
}

fn fresh(workers: usize, src: &str) -> (Elaborator, ModuleDelta) {
    let mut e = elaborator(workers);
    let delta = e
        .check_module_delta("m", src, ModuleDependencyIdentity::default())
        .unwrap_or_else(|errs| panic!("the fixture must check: {}", errs[0].render(src)));
    (e, delta)
}

fn sliced(workers: usize, previous: &ModuleDelta, src: &str) -> (Elaborator, ModuleDelta, SliceReport) {
    let mut e = elaborator(workers);
    let (delta, report) = e
        .check_module_delta_from("m", src, ModuleDependencyIdentity::default(), previous)
        .unwrap_or_else(|errs| panic!("the edited fixture must check: {}", errs[0].render(src)));
    (e, delta, report)
}

fn warnings(delta: &ModuleDelta) -> Vec<(String, usize, usize)> {
    delta.warnings().iter().map(|w| (w.msg.clone(), w.span.start, w.span.end)).collect()
}

/// The sliced check of `edited` against `previous` equals a fresh check of
/// `edited`, and did what the shape says.
fn same_as_fresh(previous: &ModuleDelta, edited: &str, expect: SliceReport, shape: &str) {
    for workers in [1usize, 4] {
        let (fresh_elab, fresh_delta) = fresh(workers, edited);
        let (sliced_elab, sliced_delta, report) = sliced(workers, previous, edited);
        assert_eq!(report, expect, "{shape}, width {workers}: what the pass did");
        assert_eq!(
            sliced_delta.to_image_bytes(),
            fresh_delta.to_image_bytes(),
            "{shape}, width {workers}: the delta (Ψ, events, scope)"
        );
        assert_eq!(sliced_delta.items(), fresh_delta.items(), "{shape}, width {workers}: the slices");
        assert_eq!(warnings(&sliced_delta), warnings(&fresh_delta), "{shape}, width {workers}: warnings");
        assert_eq!(sliced_elab.psi(), fresh_elab.psi(), "{shape}, width {workers}: the elaborator's Ψ");
        // The world is usable afterwards, the same way: a consumer of the
        // edited module checks in both.
        for e in [fresh_elab, sliced_elab] {
            let mut e = e;
            let consumer = "import m;\ntheorem t3(): triple(1) = 3 { refl }\n";
            let errs = e.check_module_delta("consumer", consumer, ModuleDependencyIdentity::default());
            assert!(errs.is_ok(), "{shape}, width {workers}: the consumer checks after");
        }
    }
}

#[test]
fn slices_partition_the_delta() {
    let (_, delta) = fresh(1, &base());
    let items = delta.items();
    assert_eq!(items.len(), 5);
    let mut psi = 0;
    let mut events = 0;
    for (item, text) in items.iter().zip([ADD, DOUBLE, ADD_ZERO_A, DOUBLE_ZERO, TRIPLE]) {
        assert_eq!(item.source, text);
        assert_eq!(item.psi.start, psi, "contiguous Ψ ranges");
        assert_eq!(item.events.start, events, "contiguous event ranges");
        psi = item.psi.end;
        events = item.events.end;
        assert!(!item.psi.is_empty(), "every declaration lands in Ψ");
    }
    assert_eq!(psi, delta.binding_count(), "the slices cover the extension");
}

#[test]
fn the_same_source_replays_every_item() {
    let (_, previous) = fresh(1, &base());
    same_as_fresh(&previous, &base(), SliceReport { replayed: 5, elaborated: 0, forced: 0 }, "unchanged");
}

#[test]
fn an_appended_declaration_replays_everything_before_it() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, DOUBLE, ADD_ZERO_A, DOUBLE_ZERO, TRIPLE, "fn quad(n: Nat) -> Nat { double(double(n)) }"]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 5, elaborated: 1, forced: 0 }, "append");
}

/// The edit the design is for: a proof edit re-elaborates the theorem, its
/// opaque binding comes out identical, and everything after it replays.
#[test]
fn a_proof_body_edit_replays_the_declarations_after_it() {
    let (_, previous) = fresh(1, &base());
    let proof_b = "theorem add_zero(n: Nat): add(n, 0) = n {
    @sym(n, add(n, 0), @sym(add(n, 0), n, match n as λ z => add(z, 0) = z {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(k, 0), k, ih),
    }))
}";
    let edited = module(&[ADD, DOUBLE, proof_b, DOUBLE_ZERO, TRIPLE]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 4, elaborated: 1, forced: 0 }, "proof edit");
}

/// Two proof edits: the prefix is restored after each, so only the two
/// theorems are elaborated.
#[test]
fn two_proof_edits_each_restore_the_prefix() {
    let with_two = module(&[ADD, DOUBLE, ADD_ZERO_A, DOUBLE_ZERO, TRIPLE, "theorem triple_zero(): triple(0) = 0 { refl }"]);
    let (_, previous) = fresh(1, &with_two);
    let edited = module(&[
        ADD,
        DOUBLE,
        "theorem add_zero(n: Nat): add(n, 0) = n {
    @sym(n, add(n, 0), @sym(add(n, 0), n, match n as λ z => add(z, 0) = z {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(k, 0), k, ih),
    }))
}",
        DOUBLE_ZERO,
        TRIPLE,
        "theorem triple_zero(): triple(0) = 0 {\n    refl\n}",
    ]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 4, elaborated: 2, forced: 0 }, "two proof edits");
}

/// A comment or reformatting inside a definition: the text differs, the
/// contribution does not, so the rest replays.
#[test]
fn a_formatting_edit_replays_the_declarations_after_it() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, "fn double(n: Nat) -> Nat {\n    // twice\n    add(n, n)\n}", ADD_ZERO_A, DOUBLE_ZERO, TRIPLE]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 4, elaborated: 1, forced: 0 }, "formatting");
}

/// A changed `fn` body changes its binding, and every later declaration may
/// have unfolded it: nothing after it replays.
#[test]
fn a_definition_body_edit_re_elaborates_everything_after_it() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, "fn double(n: Nat) -> Nat { add(n, add(n, 0)) }", ADD_ZERO_A, DOUBLE_ZERO, TRIPLE]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 1, elaborated: 4, forced: 0 }, "fn body edit");
}

#[test]
fn an_inserted_declaration_re_elaborates_everything_after_it() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, "fn one() -> Nat { 1 }", DOUBLE, ADD_ZERO_A, DOUBLE_ZERO, TRIPLE]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 1, elaborated: 5, forced: 0 }, "insert");
}

#[test]
fn a_deleted_declaration_re_elaborates_everything_after_it() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, DOUBLE, ADD_ZERO_A, TRIPLE]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 3, elaborated: 1, forced: 0 }, "delete");
}

#[test]
fn reordered_declarations_re_elaborate_from_the_first_moved_one() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, DOUBLE, ADD_ZERO_A, TRIPLE, DOUBLE_ZERO]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 3, elaborated: 2, forced: 0 }, "reorder");
}

#[test]
fn a_rename_re_elaborates_everything_after_it() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[
        ADD,
        "fn dbl(n: Nat) -> Nat { add(n, n) }",
        ADD_ZERO_A,
        "theorem double_zero(): dbl(0) = 0 { refl }",
        "fn triple(n: Nat) -> Nat { add(n, dbl(n)) }",
    ]);
    same_as_fresh(&previous, &edited, SliceReport { replayed: 1, elaborated: 4, forced: 0 }, "rename");
}

/// A mutual measure group is one slice at its first member, keyed by every
/// member's text: editing the *second* member re-elaborates the group.
#[test]
fn a_mutual_group_is_one_slice_keyed_by_every_member() {
    // `decreases` states its obligations through omega over the flattened
    // measure, so the group's module sits over the library's arithmetic
    // prefix — the same image base `mutual_recursion.rs` forks.
    const EV: &str = "fn ev(n: Nat) -> Nat decreases n { match n { Zero => 1, Succ(k) => od(k) } }";
    const OD: &str = "fn od(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => ev(k) } }";
    const EV4: &str = "theorem ev4(): ev(4) = 1 { refl }";
    const IMPORTS: &str = "import logic; import nat; import list; import int; import omega; import pair;";
    let image = support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/logic.hthr")),
        ("bool", include_str!("../../../lib/std/bool.hthr")),
        ("nat", include_str!("../../../lib/std/nat.hthr")),
        ("option", include_str!("../../../lib/std/option.hthr")),
        ("pair", include_str!("../../../lib/std/pair.hthr")),
        ("list", include_str!("../../../lib/std/list.hthr")),
        ("algebra", include_str!("../../../lib/std/algebra.hthr")),
        ("int", include_str!("../../../lib/std/int.hthr")),
        ("omega", include_str!("../../../lib/std/omega.hthr")),
    ])
    .semantic_image();
    let over_nat = |workers: usize| {
        let mut e = image.elaborator();
        e.set_kernel_workers(workers);
        e
    };
    let src = module(&[IMPORTS, ADD, EV, OD, EV4]);
    let previous = over_nat(1)
        .check_module_delta("m", &src, ModuleDependencyIdentity::default())
        .unwrap_or_else(|errs| panic!("the group checks: {}", errs[0].render(&src)));
    // Six import items precede `add`.
    let ev_at = previous.items().iter().position(|i| i.source.starts_with("fn ev")).expect("ev's slice");
    assert_eq!(ev_at, 7);
    assert!(previous.items()[ev_at].source.contains("fn od"), "the group's slice names both members");
    assert!(previous.items()[ev_at + 1].psi.is_empty(), "the second member's own slice is empty");
    for (edited, expect, shape) in [
        // Unchanged: the group replays as one, its second member as an empty slice.
        (src.clone(), SliceReport { replayed: 10, elaborated: 0, forced: 0 }, "group unchanged"),
        // The second member's text changes without changing what it means:
        // the group's first member sees the new text and the group is
        // elaborated (the second member's own empty slice too), comes out
        // equal, and the theorem after it replays.
        (
            module(&[IMPORTS, ADD, EV, "fn od(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => ev(k) }  }", EV4]),
            SliceReport { replayed: 8, elaborated: 2, forced: 0 },
            "group member reformatted",
        ),
        // The second member's body changes: the group is elaborated and so
        // is everything after it.
        (
            module(&[IMPORTS, ADD, EV, "fn od(n: Nat) -> Nat decreases n { match n { Zero => 2, Succ(k) => ev(k) } }", "theorem ev5(): ev(5) = 2 { refl }"]),
            SliceReport { replayed: 7, elaborated: 3, forced: 0 },
            "group member edited",
        ),
    ] {
        for workers in [1usize, 4] {
            let fresh_delta = over_nat(workers)
                .check_module_delta("m", &edited, ModuleDependencyIdentity::default())
                .unwrap_or_else(|errs| panic!("{shape}: {}", errs[0].render(&edited)));
            let (sliced_delta, report) = over_nat(workers)
                .check_module_delta_from("m", &edited, ModuleDependencyIdentity::default(), &previous)
                .unwrap_or_else(|errs| panic!("{shape}: {}", errs[0].render(&edited)));
            assert_eq!(report, expect, "{shape}, width {workers}");
            assert_eq!(sliced_delta.to_image_bytes(), fresh_delta.to_image_bytes(), "{shape}, width {workers}");
            assert_eq!(sliced_delta.items(), fresh_delta.items(), "{shape}, width {workers}");
        }
    }
}

/// A previous delta from a different dependency world replays nothing.
#[test]
fn a_different_dependency_world_replays_nothing() {
    let (_, previous) = fresh(1, &base());
    let mut e = elaborator(1);
    e.check_module_delta("extra", "fn extra() -> Nat { 0 }\n", ModuleDependencyIdentity::default())
        .expect("extra checks");
    let (delta, report) = e
        .check_module_delta_from("m", &base(), ModuleDependencyIdentity::default(), &previous)
        .expect("checks");
    assert_eq!(report, SliceReport { replayed: 0, elaborated: 5, forced: 0 });
    let mut plain = elaborator(1);
    plain.check_module_delta("extra", "fn extra() -> Nat { 0 }\n", ModuleDependencyIdentity::default()).unwrap();
    let fresh_delta = plain.check_module_delta("m", &base(), ModuleDependencyIdentity::default()).unwrap();
    assert_eq!(delta.to_image_bytes(), fresh_delta.to_image_bytes());
}

/// A slice whose binding was tampered with is refused by the kernel, rolled
/// back, and the item elaborated instead; the result is still fresh
/// elaboration's.
#[test]
fn a_forged_slice_is_refused_and_the_item_elaborated() {
    use heather_kernel::term::{GlobalBinding, Term};
    let (_, mut previous) = fresh(1, &base());
    let at = previous.items()[0].psi.start;
    let GlobalBinding::Tm { body, .. } = &mut previous.extension_mut()[at] else { unreachable!() };
    *body = Some(std::sync::Arc::new(Term::TmNat));
    for workers in [1usize, 4] {
        let (_, fresh_delta) = fresh(workers, &base());
        let (_, sliced_delta, report) = sliced(workers, &previous, &base());
        assert_eq!(sliced_delta.to_image_bytes(), fresh_delta.to_image_bytes(), "width {workers}");
        // `add` is elaborated (its forged slice was refused) and comes out
        // different from the forged binding, so the prefix is broken and
        // nothing after it replays either.
        assert_eq!(report, SliceReport { replayed: 0, elaborated: 5, forced: 0 }, "width {workers}");
    }
}

/// An edit that breaks the module reports what fresh elaboration reports,
/// and the elaborator is usable afterwards.
#[test]
fn a_broken_edit_reports_the_fresh_errors() {
    let (_, previous) = fresh(1, &base());
    let edited = module(&[ADD, DOUBLE, "theorem add_zero(n: Nat): add(n, 0) = n { refl }", DOUBLE_ZERO, TRIPLE]);
    let mut plain = elaborator(1);
    let Err(fresh_errs) = plain.check_module_delta("m", &edited, ModuleDependencyIdentity::default()) else {
        panic!("the edit breaks the proof")
    };
    let mut e = elaborator(1);
    let Err(sliced_errs) =
        e.check_module_delta_from("m", &edited, ModuleDependencyIdentity::default(), &previous)
    else {
        panic!("the edit breaks the proof")
    };
    let render = |errs: &Vec<heather_elab::ElabError>| errs.iter().map(|e| e.render(&edited)).collect::<Vec<_>>();
    assert_eq!(render(&sliced_errs), render(&fresh_errs));
    // Usable afterwards, with no plan left behind.
    e.check_module_delta("again", "fn z() -> Nat { 0 }\n", ModuleDependencyIdentity::default()).expect("checks");
}

/// `--only` (`docs/check-only-design.md`): a forced item is elaborated from
/// source over an exact prefix, every other item replays, and the result is
/// the fresh elaboration's — for an unchanged source, where nothing would
/// have been elaborated otherwise, and for a name in a mutual group.
#[test]
fn a_forced_item_is_elaborated_and_the_rest_replays() {
    let src = base();
    let (_, previous) = fresh(1, &src);
    for workers in [1usize, 4] {
        let (fresh_elab, fresh_delta) = fresh(workers, &src);
        let mut e = elaborator(workers);
        let force = ["double_zero".to_string()].into_iter().collect();
        let (delta, report, met) = e
            .check_module_delta_only("m", &src, ModuleDependencyIdentity::default(), &previous, force)
            .unwrap_or_else(|errs| panic!("{}", errs[0].render(&src)));
        assert_eq!(report, SliceReport { replayed: 4, elaborated: 1, forced: 1 }, "width {workers}");
        assert_eq!(met, ["double_zero".to_string()].into_iter().collect(), "width {workers}");
        assert_eq!(delta.to_image_bytes(), fresh_delta.to_image_bytes(), "width {workers}: the delta");
        assert_eq!(delta.items(), fresh_delta.items(), "width {workers}: the slices");
        assert_eq!(e.psi(), fresh_elab.psi(), "width {workers}: Ψ");
    }
    // A name nothing declares is reported as unmet, and forces nothing.
    let mut e = elaborator(1);
    let force = ["nope".to_string()].into_iter().collect();
    let (_, report, met) = e
        .check_module_delta_only("m", &src, ModuleDependencyIdentity::default(), &previous, force)
        .unwrap_or_else(|errs| panic!("{}", errs[0].render(&src)));
    assert_eq!(report, SliceReport { replayed: 5, elaborated: 0, forced: 0 });
    assert!(met.is_empty());
}

/// A gate that vouches for nothing: every binding is kernel-checked, and a
/// slice replay takes the gated path through `recheck_extension`, as it does
/// under `heather check --cache`, whose verdict store is always installed.
struct VouchesForNothing;

impl heather_elab::gate::KernelGate for VouchesForNothing {
    fn admits(&self, _psi: &heather_kernel::term::GlobalCtx, _item: &heather_elab::gate::GateItem<'_>) -> bool {
        false
    }
    fn accepted(&self, _psi: &heather_kernel::term::GlobalCtx, _item: &heather_elab::gate::GateItem<'_>) {}
}

/// A proof the elaborator lets through and the kernel refuses, edited into
/// the prefix, with the items after it replayable. At width > 1 its body is
/// queued on the pool; a slice replayed later in the same pass must not
/// consume that pending verdict. It once did — the replay's recheck joined
/// the module's pool, took the rejection as its own failure, elaborated its
/// item instead, and the module's join found nothing: the refused proof
/// checked.
#[test]
fn a_refused_proof_before_a_replayed_slice_still_refuses_the_module() {
    let (_, previous) = fresh(1, &base());
    let refused = "theorem add_zero(n: Nat): add(n, 0) = n { refl }";
    let edited = module(&[ADD, DOUBLE, refused, DOUBLE_ZERO, TRIPLE]);
    for workers in [1usize, 4] {
        let mut e = elaborator(workers);
        e.set_gate(std::sync::Arc::new(VouchesForNothing));
        let errors = e
            .check_module_delta_from("m", &edited, ModuleDependencyIdentity::default(), &previous)
            .err()
            .unwrap_or_else(|| panic!("width {workers}: a module with a refused proof checked"));
        assert!(
            errors.iter().any(|err| matches!(err, heather_elab::ElabError::Kernel { decl, .. } if decl == "add_zero")),
            "width {workers}: the refused declaration is named: {}",
            errors.iter().map(|err| err.render(&edited)).collect::<Vec<_>>().join("\n"),
        );
    }
}

/// Copy-on-write stays O(1) per module, not per declaration
/// (`heather_elab::stats::make_mut`, docs/instrumentation-design.md). A
/// registry layer is copied when something still holds it at the next
/// write; a per-declaration holder — a checkpoint around each replayed
/// slice, as there once was (issues/check-module-delta-certificate-cost.md)
/// — makes every declaration copy the module's layers so far. Counted here
/// over a module of many declarations, elaborated and then slice-replayed;
/// the persistent Ψ (`GlobalCtx`) and the committed world's handle struct
/// copy in O(1) and are expected per commit.
#[test]
fn registry_layers_are_not_copied_per_declaration() {
    const N: usize = 60;
    let items: Vec<String> = (0..N)
        .map(|i| format!("fn f{i}(n: Nat) -> Nat {{ add(n, {i}) }}\n\ntheorem t{i}(): f{i}(0) = {i} {{ refl }}"))
        .collect();
    let src = module(&[&[ADD.to_string()], items.as_slice()].concat().iter().map(String::as_str).collect::<Vec<_>>());
    let layer_copies = |sites: &str| -> u64 {
        sites
            .lines()
            .filter(|line| !matches!(line.split('\t').nth(2), Some("GlobalCtx" | "CommittedWorld")))
            .filter_map(|line| line.split('\t').next()?.parse::<u64>().ok())
            .sum()
    };
    heather_elab::stats::take_cow_sites();
    let (_, previous) = fresh(1, &src);
    let elaborated = heather_elab::stats::take_cow_sites();
    let edited = src.clone() + "\nfn appended() -> Nat { 0 }\n";
    let (_, _, report) = sliced(1, &previous, &edited);
    let replayed = heather_elab::stats::take_cow_sites();
    assert_eq!(report.replayed, 2 * N + 1, "everything before the append replays");
    for (pass, sites) in [("elaboration", &elaborated), ("slice replay", &replayed)] {
        assert!(layer_copies(sites) < N as u64 / 2, "{pass} copied registry layers per declaration:\n{sites}");
    }
}
