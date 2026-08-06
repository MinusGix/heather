//! The cache against the real elaborator: stability, the interface split, hits
//! and misses, and the negative controls.
//!
//! `docs/cache-v1-design.md` is the design; this file is where its claims are
//! either true of the shipped code or not. The four groups map onto the four
//! things a rung-1 cache has to get right:
//!
//! 1. **Stability** — the same source twice gives the same keys. Piggybacks on
//!    `issues/elaboration-determinism.md`: without that guarantee no key is
//!    well-defined, and with it this is the first thing to break if it lapses.
//! 2. **The interface split** — a proof-body edit invalidates only that
//!    theorem; an interface edit invalidates its dependents and nothing else.
//! 3. **Hit/miss** — a warm run really does skip the kernel, and a changed
//!    fingerprint really does discard everything.
//! 4. **Negative controls** — what a corrupted cache does, and (stated, not
//!    tested, because it cannot be) what a forged one does.

use std::rc::Rc;

use heather_cache::store::{FORMAT, Rejected, Store};
use heather_cache::{Cache, KERNEL_SEMANTICS};
use heather_elab::Elaborator;

/// `add`, so that the fixtures have something δ-relevant to depend on.
const ADD: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}
"#;

/// One proof of `add(n, 0) = n`.
const PROOF_A: &str = r#"match n as λ z => add(z, 0) = z {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
    }"#;

/// Another proof of the *same* statement: the first one, symmetrised twice.
/// Different term, identical type — which is exactly the edit a session spends
/// its day making, and the edit the design promises costs nothing downstream.
fn proof_b() -> String {
    format!(
        "@sym(n, add(n, 0), @sym(add(n, 0), n, {PROOF_A}))"
    )
}

/// `add`, a helper theorem, a theorem that uses it, and one that does not.
fn source(proof: &str, helper_stmt: &str) -> String {
    format!(
        "{ADD}
theorem helper(n: Nat): {helper_stmt} {{
    {proof}
}}

theorem dep(n: Nat): add(n, 0) = n {{
    helper(n)
}}

theorem unrelated(n: Nat): add(0, n) = n {{
    refl
}}
"
    )
}

/// Elaborate `src` under a fresh cache backed by nothing, and hand back the
/// cache. Panics on any elaboration error: these fixtures must check.
fn run(src: &str) -> Rc<Cache> {
    run_with(Rc::new(Cache::over(Store::empty("unused".into()))), src)
}

fn run_with(cache: Rc<Cache>, src: &str) -> Rc<Cache> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    // The prelude is elaborated *inside* `with_prelude`, before any gate can
    // be installed, so it is always kernel-checked (docs/cache-v1-design.md
    // §4). Zero the phase counter here so that `stats::kernel_ns()` afterwards
    // means "gate time spent on `src`".
    heather_elab::stats::reset_kernel_ns();
    cache.begin_run();
    e.set_gate(Rc::clone(&cache) as Rc<dyn heather_elab::gate::KernelGate>);
    let errs = e.check_source(src);
    assert!(errs.is_empty(), "the fixture must check: {}", errs[0].render(src));
    cache
}

// -- 1. stability -----------------------------------------------------------

/// The same source twice, two fresh elaborators, the same keys.
///
/// This is `issues/elaboration-determinism.md`'s guarantee seen from the cache
/// side: `HashMap` iteration order that reached an emitted term would move a
/// key here before it moved anything a user could see.
#[test]
fn the_same_source_twice_gives_the_same_keys() {
    let src = source(PROOF_A, "add(n, 0) = n");
    let a = run(&src);
    let b = run(&src);
    assert_eq!(a.keys(), b.keys(), "elaborating one source twice gave different cache keys");
    assert!(a.keys().len() >= 4, "the fixture should record several declarations");
    assert_eq!(a.counts().hits, 0, "a cold run hits nothing");
}

// -- 2. the interface split -------------------------------------------------

/// Editing a **proof body** moves that theorem's key and nothing else.
///
/// The load-bearing invariant of `issues/parallel-checking-and-caching.md`:
/// a theorem's interface is its statement, so a dependent cannot observe which
/// proof was given. Here that means `dep`'s and `unrelated`'s keys — and
/// `helper`'s own *interface* hash — are all untouched.
#[test]
fn editing_a_proof_invalidates_only_that_theorem() {
    let before = run(&source(PROOF_A, "add(n, 0) = n")).recorded();
    let after = run(&source(&proof_b(), "add(n, 0) = n")).recorded();

    let (key_a, iface_a) = &before["helper"];
    let (key_b, iface_b) = &after["helper"];
    assert_ne!(key_a, key_b, "a different proof must be re-checked");
    assert_eq!(iface_a, iface_b, "a different proof of one statement is one interface");

    for name in ["dep", "unrelated", "add"] {
        assert_eq!(
            before[name], after[name],
            "`{name}` was invalidated by an edit to a proof body it cannot see"
        );
    }
}

/// Editing a **statement** moves the theorem's interface, hence its
/// dependents' keys — and nothing else's.
///
/// The two statements here are definitionally equal (`add(0, 0)` reduces to
/// `0`), so `dep` still checks with its own source untouched. That is what
/// makes this a clean test of *closure* propagation rather than of two
/// unrelated files: the only thing that moved for `dep` is a hash it
/// references.
#[test]
fn editing_a_statement_invalidates_its_dependents() {
    let before = run(&source(PROOF_A, "add(n, 0) = n")).recorded();
    let after = run(&source(PROOF_A, "add(n, add(0, 0)) = n")).recorded();

    let (key_a, iface_a) = &before["helper"];
    let (key_b, iface_b) = &after["helper"];
    assert_ne!(iface_a, iface_b, "a changed statement is a changed interface");
    assert_ne!(key_a, key_b);

    assert_ne!(before["dep"], after["dep"], "a dependent's closure must move with it");
    assert_eq!(
        before["unrelated"], after["unrelated"],
        "a declaration that never mentions `helper` must be untouched, however \
         far down the file it sits"
    );
    assert_eq!(before["add"], after["add"], "and so must everything before it");
}

// -- 3. hits and misses -----------------------------------------------------

/// A warm run skips the kernel entirely, and says how much it skipped.
#[test]
fn a_warm_run_skips_the_kernel_gate() {
    let src = source(PROOF_A, "add(n, 0) = n");
    let cache = run(&src);
    let cold = cache.counts();
    assert!(cold.checked > 0 && cold.hits == 0);

    let cache = run_with(cache, &src);
    let warm = cache.counts().since(&cold);
    assert_eq!(warm.hits, cold.checked, "every declaration should have been cached");
    assert_eq!(warm.checked, 0, "a warm run must not reach the kernel gate at all");
    assert_eq!(
        heather_elab::stats::kernel_ns(),
        0,
        "no time may be attributed to the kernel gate on a fully warm run"
    );
}

/// One edited proof, and only that declaration is re-checked.
#[test]
fn a_warm_run_after_one_edit_rechecks_one_declaration() {
    let cache = run(&source(PROOF_A, "add(n, 0) = n"));
    let cold = cache.counts();
    let cache = run_with(cache, &source(&proof_b(), "add(n, 0) = n"));
    let warm = cache.counts().since(&cold);
    assert_eq!(warm.checked, 1, "only the edited theorem should reach the kernel");
    assert_eq!(warm.hits, cold.checked - 1);
}

/// With no gate installed nothing changes: the unflagged `heather check` is
/// the same program it was.
#[test]
fn without_a_gate_the_kernel_runs_on_everything() {
    let src = source(PROOF_A, "add(n, 0) = n");
    let mut e = Elaborator::with_prelude().expect("prelude");
    heather_elab::stats::reset_kernel_ns();
    assert!(e.check_source(&src).is_empty());
    assert!(heather_elab::stats::kernel_ns() > 0, "the kernel gate must have run");
}

// -- 4. persistence, the fingerprint, and the negative controls -------------

fn tempdir(tag: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!(
        "heather-cache-test-{tag}-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&d);
    d
}

/// A cache written by one process is read by the next, and the file says what
/// it knows in a form a human can read.
#[test]
fn the_file_round_trips() {
    let dir = tempdir("roundtrip");
    let src = source(PROOF_A, "add(n, 0) = n");

    let (cache, why) = Cache::open(dir.clone());
    assert!(matches!(why, Some(Rejected::Absent)), "a first run finds nothing");
    let cache = run_with(Rc::new(cache), &src);
    cache.save().expect("write");

    let text = std::fs::read_to_string(Store::path(&dir)).expect("read back");
    assert!(
        text.starts_with(&format!("heather-cache\t{FORMAT}\n")),
        "versioned header: {text:.40}"
    );
    assert!(text.contains(KERNEL_SEMANTICS), "the fingerprint is in the header");
    assert!(text.contains("\thelper\n"), "names are there for the human reading it");

    let (reopened, why) = Cache::open(dir.clone());
    assert!(why.is_none(), "a valid file must load");
    assert_eq!(reopened.entries(), cache.entries());
    let reopened = run_with(Rc::new(reopened), &src);
    assert_eq!(reopened.counts().checked, 0, "a reloaded cache is a warm cache");

    let _ = std::fs::remove_dir_all(&dir);
}

/// A cache written by a different kernel is discarded, loudly, and the run is
/// a full re-check.
///
/// This is the format rule the issue fixed before any format existed: an entry
/// is meaningful only against the semantics that produced it.
#[test]
fn a_stale_kernel_fingerprint_discards_everything() {
    let dir = tempdir("fingerprint");
    let src = source(PROOF_A, "add(n, 0) = n");
    let cache = run_with(Rc::new(Cache::over(Store::empty(dir.clone()))), &src);
    cache.save().expect("write");

    // Rewrite the header as if another kernel had produced it — and fix the
    // checksum, so that this is a *fingerprint* failure and not a corruption
    // one.
    let path = Store::path(&dir);
    let text = std::fs::read_to_string(&path).unwrap();
    let doctored: String = text
        .lines()
        .map(|l| {
            if l.starts_with("kernel-semantics\t") {
                format!("kernel-semantics\t{}\n", "0".repeat(64))
            } else {
                format!("{l}\n")
            }
        })
        .collect();
    std::fs::write(&path, doctored).unwrap();

    let (reopened, why) = Cache::open(dir.clone());
    match why {
        Some(Rejected::KernelChanged { entries }) => {
            assert!(entries > 0, "it should say how much it is throwing away");
            let msg = Rejected::KernelChanged { entries }.message().expect("a loud message");
            assert!(msg.contains("full check"), "and what that means: {msg}");
        }
        _ => panic!("a stale fingerprint must be reported as one"),
    }
    assert_eq!(reopened.entries(), 0, "nothing may survive");
    let after = run_with(Rc::new(reopened), &src);
    assert!(after.counts().checked > 0, "and the kernel must run again");

    let _ = std::fs::remove_dir_all(&dir);
}

/// The negative control: a corrupted cache is rejected rather than half-read.
///
/// **What this does and does not prove.** At rung 1 the trusted base is "the
/// OS gave us a file nobody tampered with" (`docs/cache-v1-design.md` §6). The
/// checksum catches *accident* — truncation, a bit flip, a half-written file —
/// and the shape checks catch a mangled line. Neither catches **forgery**:
/// anyone who can write the file can compute the key of a declaration with a
/// bogus proof, insert it, and recompute the checksum, and this cache will
/// believe it. That is the definition of rung 1, not an oversight, and it is
/// why `--cache` is opt-in and the unflagged `heather check` remains the gate.
/// Rung 2 (certificate replay) is what closes it.
#[test]
fn a_corrupted_cache_is_rejected_and_not_half_read() {
    let dir = tempdir("corrupt");
    let src = source(PROOF_A, "add(n, 0) = n");
    let cache = run_with(Rc::new(Cache::over(Store::empty(dir.clone()))), &src);
    cache.save().expect("write");
    let path = Store::path(&dir);
    let good = std::fs::read_to_string(&path).unwrap();

    // Every way a file can be damaged that a reader could otherwise limp past.
    let mutations: Vec<(&str, String)> = vec![
        ("a flipped bit in an entry", {
            let mut t = good.clone();
            let i = t.rfind("ok\t").expect("an entry") + 3;
            let c = if t.as_bytes()[i] == b'a' { 'b' } else { 'a' };
            t.replace_range(i..i + 1, &c.to_string());
            t
        }),
        ("a truncated file", good[..good.len() - 20].to_string()),
        ("a dropped line", {
            let mut lines: Vec<&str> = good.lines().collect();
            lines.remove(4.min(lines.len() - 1));
            lines.join("\n") + "\n"
        }),
        ("a missing header", good.lines().skip(1).collect::<Vec<_>>().join("\n")),
        // Both directions of a version mismatch. The *older* one is what a
        // format bump actually meets in the field — a v1 file left in
        // `.heather/cache` by the previous build — and it must be reported and
        // discarded, never partially believed (`store::FILE` deliberately does
        // not change with the version, so the stale file is *read* and
        // rejected rather than orphaned and silently ignored).
        (
            "a past format version",
            good.replacen(&format!("heather-cache\t{FORMAT}"), "heather-cache\t1", 1),
        ),
        (
            "a future format version",
            good.replacen(&format!("heather-cache\t{FORMAT}"), "heather-cache\t9999", 1),
        ),
    ];

    for (what, text) in mutations {
        std::fs::write(&path, &text).unwrap();
        let (c, why) = Cache::open(dir.clone());
        assert!(
            matches!(why, Some(Rejected::Malformed(_))),
            "{what} must be rejected as malformed"
        );
        assert!(why.unwrap().message().is_some(), "{what} must be reported out loud");
        assert_eq!(c.entries(), 0, "{what} must not leave a partially-read cache");
        // And the run that follows is a real one.
        let after = run_with(Rc::new(c), &src);
        assert!(after.counts().checked > 0, "{what} must lead to a full re-check");
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// A cache entry that does not correspond to anything in the run is inert: it
/// is never consulted, because lookup is by the key the *current* elaboration
/// computes.
///
/// Which is the honest shape of the forgery statement: a forged entry only
/// does damage if its key is the key of a declaration actually being checked,
/// and computing that key requires the declaration. Rung 1 cannot tell such an
/// entry from an earned one — see the test above.
#[test]
fn an_entry_for_nothing_is_never_consulted() {
    let dir = tempdir("inert");
    let src = source(PROOF_A, "add(n, 0) = n");
    let mut store = Store::empty(dir.clone());
    store.insert([7u8; 32], [9u8; 32], "not-a-real-declaration");
    let cache = run_with(Rc::new(Cache::over(store)), &src);
    assert_eq!(cache.counts().hits, 0, "a key nothing computes cannot be hit");
    assert!(cache.counts().checked > 0);
}
