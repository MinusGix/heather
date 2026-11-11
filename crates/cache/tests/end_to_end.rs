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

use std::sync::Arc;

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
        Succ(k, ih) => @Nat::cong_succ(add(k, 0), k, ih),
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
fn run(src: &str) -> Arc<Cache> {
    run_with(Arc::new(Cache::over(Store::empty("unused".into()))), src)
}

fn run_with(cache: Arc<Cache>, src: &str) -> Arc<Cache> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    // The prelude is elaborated *inside* `with_prelude`, before any gate can
    // be installed, so it is always kernel-checked (docs/cache-v1-design.md
    // §4). Zero the phase counter here so that `stats::kernel_ns()` afterwards
    // means "gate time spent on `src`".
    heather_elab::stats::reset_kernel_ns();
    cache.begin_run();
    e.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
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

/// An axiom and a proved opaque theorem have the same kernel binding shape,
/// but not the same trust interface. Replacing one with the other must move a
/// dependent's closure hash even when the public statement is byte-identical.
#[test]
fn proving_an_axiom_changes_dependent_cache_identity() {
    let assumed = run(
        "axiom seed(): Nat;\n\
         theorem dep(): Nat { seed() }",
    )
    .recorded();
    let proved = run(
        "theorem seed(): Nat { 0 }\n\
         theorem dep(): Nat { seed() }",
    )
    .recorded();
    assert_ne!(
        assumed["dep"], proved["dep"],
        "trust provenance is part of a dependent's cache identity"
    );
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

// -- 3b. the meta-layer gate ------------------------------------------------
//
// `quote.rs`'s `elab_meta_decl_inner` is the third gate site
// (issues/elaborator-snapshot-across-test-binaries.md's round): a `meta fn`
// is checked at `Layer::Meta` and registered in the meta-def table, so it
// never lands in Ψ — `GateItem::lands_in_psi` is false and the cache must
// neither leave a pending interface hash for the next Ψ binding to absorb
// nor let its `admits`/`accepted` memo answer for a neighbour at the same Ψ
// length. The fixture is `certgen_route1_spike.rs`'s miniature.

/// `plus`, two proofs of `plus(n, 0) = n`, and a `three` for the meta body.
const META_BASE: &str = r#"
fn plus(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k, ih) => Succ(ih) } }
theorem plus_zero(n: Nat): plus(n, 0) = n { refl }
theorem plus_zero2(n: Nat): plus(n, 0) = n { plus_zero(n) }
fn three() -> Nat { 3 }
"#;

/// A meta fn whose payload applies `plus_zero` at `arg`. Payload variants must
/// differ in the *argument*, not in which same-statement lemma they name: two
/// opaque theorems with one statement share an interface hash, so substituted
/// bodies naming either coincide and so do the check keys — correctly (the
/// kernel question is literally the same one).
fn meta_fn(name: &str, arg: &str) -> String {
    format!(
        "meta fn {name}(g: Ctx) -> Code(g |- plus({arg}, 0) = {arg}) {{
             code {{ plus_zero({arg}) }}
         }}\n"
    )
}

/// A `meta fn`'s verdict is recorded cold and admitted warm, like any other
/// declaration's.
#[test]
fn a_meta_fn_is_cached_and_admitted_warm() {
    let src = format!("{META_BASE}{}", meta_fn("cert", "three()"));
    let cache = run(&src);
    let cold = cache.counts();
    assert!(cache.recorded().contains_key("cert"), "the meta fn must be recorded");

    let cache = run_with(cache, &src);
    let warm = cache.counts().since(&cold);
    assert_eq!(warm.checked, 0, "a warm run must not reach the kernel gate at all");
    assert_eq!(warm.hits, cold.checked);
    assert_eq!(heather_elab::stats::kernel_ns(), 0, "the meta checks were really skipped");
}

/// A `meta fn` between two Ψ declarations changes no Ψ key: nothing lands in
/// Ψ for it, so nothing downstream may hash differently. This is the
/// regression test for the pending-hash guard — before it, the meta fn's
/// interface hash would be absorbed by the next binding to land (here the
/// gate-less `inductive`), mis-describing it to every dependent.
#[test]
fn a_meta_fn_leaves_psi_hashing_untouched() {
    let tail = "inductive W { WA }\nfn use_w(x: W) -> W { x }\n";
    let with = run(&format!("{META_BASE}{}{tail}", meta_fn("cert", "three()"))).recorded();
    let without = run(&format!("{META_BASE}{tail}")).recorded();
    assert_eq!(
        with["use_w"], without["use_w"],
        "a `meta fn` in the file moved a Ψ declaration's cache identity"
    );
}

/// Two adjacent `meta fn`s sit at the *same* Ψ length, which is exactly what
/// the `admits`/`accepted` memo is keyed on: with the memo not cleared, the
/// second would inherit the first's verdict — a wrong vouch, not a wrong
/// speed. Warm run with only the second one edited: one check, not zero.
#[test]
fn adjacent_meta_fns_do_not_share_a_verdict() {
    let two = |arg: &str| {
        format!("{META_BASE}{}{}", meta_fn("cert_a", "three()"), meta_fn("cert_b", arg))
    };
    // Distinct content cold, so both are recorded — a `cert_b` identical to
    // `cert_a` would (correctly) hit its neighbour's entry, since names are
    // metadata and identity is content.
    let cache = run(&two("0"));
    let cold = cache.counts();
    assert_eq!(cold.hits, 0);
    let cache = run_with(cache, &two("1"));
    let warm = cache.counts().since(&cold);
    assert_eq!(warm.checked, 1, "the edited meta fn must be re-checked, and only it");
    assert_eq!(warm.hits, cold.checked - 1);
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
    let cache = run_with(Arc::new(cache), &src);
    cache.save().expect("write");

    let text = std::fs::read_to_string(Store::path(&dir)).expect("read back");
    assert!(
        text.starts_with(&format!("heather-cache\t{FORMAT}\n")),
        "versioned header: {text:.40}"
    );
    assert!(
        text.contains(&format!("\nkernel\t{KERNEL_SEMANTICS}\t")),
        "the fingerprint heads its section"
    );
    assert!(text.contains("\thelper\n"), "names are there for the human reading it");

    let (reopened, why) = Cache::open(dir.clone());
    assert!(why.is_none(), "a valid file must load");
    assert_eq!(reopened.entries(), cache.entries());
    let reopened = run_with(Arc::new(reopened), &src);
    assert_eq!(reopened.counts().checked, 0, "a reloaded cache is a warm cache");

    let _ = std::fs::remove_dir_all(&dir);
}

/// A cache written by a different kernel is not believed, loudly, and the run
/// is a full re-check — but the other kernel's verdicts are kept for it.
///
/// This is the format rule the issue fixed before any format existed: an entry
/// is meaningful only against the semantics that produced it. What changed
/// with `issues/verdict-store-one-kernel.md` is only what happens to the
/// entries this reader cannot use: they stay, in their own section.
#[test]
fn a_stale_kernel_fingerprint_discards_everything() {
    let dir = tempdir("fingerprint");
    let src = source(PROOF_A, "add(n, 0) = n");
    let cache = run_with(Arc::new(Cache::over(Store::empty(dir.clone()))), &src);
    cache.save().expect("write");

    // Re-label the section as another kernel's. The fingerprint is not under
    // the section's checksum, so that this is a *fingerprint* failure and not
    // a corruption one.
    let other = "0".repeat(64);
    let path = Store::path(&dir);
    let text = std::fs::read_to_string(&path).unwrap();
    let doctored = text.replacen(&format!("kernel\t{KERNEL_SEMANTICS}\t"), &format!("kernel\t{other}\t"), 1);
    assert_ne!(doctored, text, "the section header names its kernel");
    std::fs::write(&path, doctored).unwrap();

    let (reopened, why) = Cache::open(dir.clone());
    let stale = match why {
        Some(Rejected::KernelChanged { entries, kernels }) => {
            assert!(entries > 0, "it should say how much it cannot use");
            assert_eq!(kernels, 1);
            let msg = Rejected::KernelChanged { entries, kernels }.message().expect("a loud message");
            assert!(msg.contains("full check"), "and what that means: {msg}");
            entries
        }
        _ => panic!("a stale fingerprint must be reported as one"),
    };
    assert_eq!(reopened.entries(), 0, "nothing may be believed");
    let after = run_with(Arc::new(reopened), &src);
    assert!(after.counts().checked > 0, "and the kernel must run again");

    // Saving this kernel's verdicts keeps the other kernel's section whole.
    after.save().expect("write");
    let theirs = Store::load(dir.clone(), &other).ok().expect("the other kernel's section survives");
    assert_eq!(theirs.entries.len(), stale, "every one of its entries");
    let (mine, why) = Cache::open(dir.clone());
    assert!(why.is_none(), "and this kernel now has its own");
    assert_eq!(mine.entries(), after.entries());

    let _ = std::fs::remove_dir_all(&dir);
}

fn key(n: u8) -> [u8; 32] {
    [n; 32]
}

fn kernel(n: u8) -> String {
    format!("{n:02x}").repeat(32)
}

/// A store with one entry `key(n)`, saved as kernel `k` at `now`.
fn save_one(dir: &std::path::Path, k: &str, n: u8, now: u64) {
    let mut s = Store::empty(dir.to_path_buf());
    s.insert(key(n), key(n), &format!("decl{n}"));
    s.save_at(k, now).expect("write");
}

fn loaded(dir: &std::path::Path, k: &str) -> Option<Store> {
    Store::load(dir.to_path_buf(), k).ok()
}

/// Checkouts with different kernels sharing one store keep each other's
/// verdicts, and each believes only its own (`issues/verdict-store-one-kernel.md`).
#[test]
fn kernels_sharing_a_store_keep_their_own_verdicts() {
    let dir = tempdir("shared-kernels");
    let (a, b) = (kernel(0xa1), kernel(0xb2));
    let t = 1_800_000_000;
    save_one(&dir, &a, 1, t);
    save_one(&dir, &b, 2, t + 10);
    save_one(&dir, &a, 3, t + 20);

    let sa = loaded(&dir, &a).expect("a's section");
    let sb = loaded(&dir, &b).expect("b's section");
    assert!(sa.contains(&key(1)) && sa.contains(&key(3)), "a's saves merged");
    assert!(!sa.contains(&key(2)), "a never believes b's verdict");
    assert!(sb.contains(&key(2)) && !sb.contains(&key(1)) && !sb.contains(&key(3)));
    assert_eq!(sa.used, Some(t + 20), "a section carries its last save");

    match Store::load(dir.clone(), &kernel(0xc3)) {
        Err((s, Rejected::KernelChanged { entries: 3, kernels: 2 })) => assert!(s.entries.is_empty()),
        _ => panic!("a third kernel finds nothing of its own, and says what it saw"),
    }

    // Most recently used first, so the file reads newest-kernel-first.
    let text = std::fs::read_to_string(Store::path(&dir)).unwrap();
    let order: Vec<&str> = text.lines().filter_map(|l| l.strip_prefix("kernel\t")).map(|l| &l[..64]).collect();
    assert_eq!(order, vec![a.as_str(), b.as_str()]);

    let _ = std::fs::remove_dir_all(&dir);
}

/// Old kernels leave by age — unused past `MAX_AGE_SECS`, or beyond the
/// `MAX_KERNELS` most recent — never because another kernel saved last.
#[test]
fn old_kernels_are_evicted_by_age() {
    use heather_cache::store::{MAX_AGE_SECS, MAX_KERNELS};
    let dir = tempdir("evict");
    let t = 1_800_000_000;
    save_one(&dir, &kernel(1), 1, t);
    save_one(&dir, &kernel(2), 2, t + MAX_AGE_SECS - 5);
    // Kernel 1 last saved MAX_AGE_SECS ago: this save drops it. Kernel 2 is
    // within the window and stays.
    save_one(&dir, &kernel(3), 3, t + MAX_AGE_SECS);
    assert!(loaded(&dir, &kernel(1)).is_none(), "an idle kernel ages out");
    assert!(loaded(&dir, &kernel(2)).is_some());
    assert!(loaded(&dir, &kernel(3)).is_some());
    let _ = std::fs::remove_dir_all(&dir);

    // The count bound keeps the most recently used.
    let dir = tempdir("evict-count");
    let n = MAX_KERNELS as u8 + 3;
    for i in 1..=n {
        save_one(&dir, &kernel(i), i, t + u64::from(i));
    }
    for i in 1..=n {
        let kept = loaded(&dir, &kernel(i)).is_some();
        assert_eq!(kept, i > n - MAX_KERNELS as u8, "kernel {i} of {n}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A fully warm kernel saves nothing new, yet must not age out: a loaded
/// section is due a fresh stamp once it is `REFRESH_SECS` old.
#[test]
fn a_warm_kernel_refreshes_its_stamp() {
    use heather_cache::store::REFRESH_SECS;
    let dir = tempdir("refresh");
    let t = 1_800_000_000;
    save_one(&dir, &kernel(1), 1, t);
    let s = loaded(&dir, &kernel(1)).unwrap();
    assert!(!s.wants_save(t + REFRESH_SECS - 1), "a fresh stamp is left alone");
    assert!(s.wants_save(t + REFRESH_SECS), "an old one is renewed");
    s.save_at(&kernel(1), t + REFRESH_SECS).unwrap();
    assert_eq!(loaded(&dir, &kernel(1)).unwrap().used, Some(t + REFRESH_SECS));
    assert!(!Store::empty(dir.clone()).wants_save(t), "an empty run writes nothing");
    let _ = std::fs::remove_dir_all(&dir);
}

/// One kernel's damaged section is that kernel's miss, not every kernel's: a
/// reader verifies only its own, and the next save drops the damaged one.
#[test]
fn a_damaged_section_is_only_its_kernels_loss() {
    let dir = tempdir("damaged-section");
    let t = 1_800_000_000;
    let (a, b) = (kernel(0xa1), kernel(0xb2));
    save_one(&dir, &a, 1, t);
    save_one(&dir, &b, 2, t + 1);
    let path = Store::path(&dir);
    let text = std::fs::read_to_string(&path).unwrap();
    // b saved last, so its section is first; flip a byte of its entry.
    let doctored = text.replacen(&format!("ok\t{}", heather_cache::sha256::hex(&key(2))), &format!("ok\t{}", heather_cache::sha256::hex(&key(4))), 1);
    assert_ne!(doctored, text);
    std::fs::write(&path, doctored).unwrap();

    assert!(loaded(&dir, &a).is_some_and(|s| s.contains(&key(1))), "a is untouched");
    assert!(matches!(Store::load(dir.clone(), &b), Err((_, Rejected::Malformed(_)))), "b is told");
    save_one(&dir, &a, 3, t + 2);
    let text = std::fs::read_to_string(&path).unwrap();
    assert!(!text.contains(&b), "the damaged section is not carried forward");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A format-3 file (one kernel, no sections) is read rather than discarded:
/// its keys mean what they meant, so the bump costs no shared store a cold
/// run. The first save rewrites it in sections.
#[test]
fn a_single_kernel_file_is_read_as_one_section() {
    use heather_cache::sha256::{hex, sha256};
    use heather_cache::store::LEGACY_FORMAT;
    let dir = tempdir("legacy");
    std::fs::create_dir_all(&dir).unwrap();
    let k = kernel(0xa1);
    let body = format!("ok\t{}\t{}\tdecl1\n", hex(&key(1)), hex(&key(1)));
    let text = format!(
        "heather-cache\t{LEGACY_FORMAT}\nkernel-semantics\t{k}\nchecksum\t{}\n{body}",
        hex(&sha256(body.as_bytes()))
    );
    std::fs::write(Store::path(&dir), text).unwrap();
    let s = loaded(&dir, &k).expect("a format-3 file under its own kernel loads");
    assert!(s.contains(&key(1)));
    assert!(matches!(Store::load(dir.clone(), &kernel(2)), Err((_, Rejected::KernelChanged { kernels: 1, .. }))));

    save_one(&dir, &kernel(2), 2, 1_800_000_000);
    let text = std::fs::read_to_string(Store::path(&dir)).unwrap();
    assert!(text.starts_with(&format!("heather-cache\t{FORMAT}\n")), "rewritten at the current format");
    assert!(loaded(&dir, &k).is_some_and(|s| s.contains(&key(1))), "the old kernel's verdicts carried over");
    assert!(loaded(&dir, &kernel(2)).is_some_and(|s| s.contains(&key(2))));
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
    let cache = run_with(Arc::new(Cache::over(Store::empty(dir.clone()))), &src);
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
        let after = run_with(Arc::new(c), &src);
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
    let cache = run_with(Arc::new(Cache::over(store)), &src);
    assert_eq!(cache.counts().hits, 0, "a key nothing computes cannot be hit");
    assert!(cache.counts().checked > 0);
}

// -- 5. one render per declaration ------------------------------------------

/// `admits` and `accepted` ask about the same declaration, and hashing it is
/// a full render: the run must render each gated declaration once, with the
/// inline gate and at a deferred join alike. Until 2026-09-17 the deferred
/// join re-rendered every declaration and the inline path re-walked every
/// interface (`issues/merkle-walk-cold-share.md`).
#[test]
fn each_gated_declaration_is_rendered_once_at_either_gate_width() {
    let src = source(PROOF_A, "add(n, 0) = n");
    let mut per_width = Vec::new();
    for workers in [1usize, 4] {
        let cache = Arc::new(Cache::over(Store::empty("unused".into())));
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.set_kernel_workers(workers);
        cache.begin_run();
        e.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
        let errs = e.check_source(&src);
        assert!(errs.is_empty(), "the fixture must check: {}", errs[0].render(&src));
        let c = cache.counts();
        assert_eq!(
            c.hashed, c.checked,
            "width {workers}: {} declarations went to the kernel but {} were rendered",
            c.checked, c.hashed
        );
        per_width.push((c.checked, cache.keys()));
    }
    assert_eq!(per_width[0], per_width[1], "the gate width must not change what is cached");
}

/// The open question a refused declaration leaves behind must not answer for
/// the next declaration at the same Ψ position: the elaborator keeps going
/// after a failure, and a same-named declaration with different content is
/// exactly what a second module, or an edit, puts there. Driven at the gate
/// interface directly, since a kernel refusal is hard to arrange from source.
#[test]
fn an_abandoned_question_does_not_answer_for_a_different_declaration() {
    use heather_elab::gate::{GateItem, KernelGate};
    use heather_kernel::layer::Layer;
    use heather_kernel::level::Level;
    use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};

    let cache = Cache::over(Store::empty("unused".into()));
    cache.begin_run();
    let psi = GlobalCtx::new(Vec::new());
    let empty = LocalCtx::nil();
    let level = Level::constant(0);
    let body_a = Term::TmNat;
    let body_b = Term::TmUnit { level: Level::constant(0) };
    let item = |body: &'static Term| GateItem {
        name: "helper",
        ctx: &empty,
        ty: &Type::Nat,
        level: &level,
        body,
        opaque: true,
        layer: Layer::Code,
        lands_in_psi: true,
    };
    // The bodies outlive the items; leak them so the closure can hand out
    // `'static` borrows without a lifetime dance.
    let body_a: &'static Term = Box::leak(Box::new(body_a));
    let body_b: &'static Term = Box::leak(Box::new(body_b));

    assert!(!cache.admits(&psi, &item(body_a)), "an empty store admits nothing");
    assert_eq!(cache.counts().hashed, 1);
    // The same declaration, accepted: answered from the open question.
    cache.accepted(&psi, &item(body_a), &[]);
    assert_eq!(cache.counts().hashed, 1, "accepted must not render again");
    // A theorem's verdict is two entries: its check key, and its statement's
    // (the same for both bodies here, which share a statement).
    let key_a = cache.keys();
    assert_eq!(key_a.len(), 2);

    // A second declaration with the same name at the same position — refused
    // before it could land, then a different one asks.
    let cache = Cache::over(Store::empty("unused".into()));
    cache.begin_run();
    assert!(!cache.admits(&psi, &item(body_a)));
    cache.abandon(&psi);
    assert!(!cache.admits(&psi, &item(body_b)));
    assert_eq!(cache.counts().hashed, 2, "after abandon the new declaration is rendered afresh");
    cache.accepted(&psi, &item(body_b), &[]);
    let key_b = cache.keys();
    assert_eq!(key_b.len(), 2);
    assert_ne!(key_a, key_b, "the two bodies must not share a check key");
    assert_eq!(key_a.iter().filter(|k| key_b.contains(k)).count(), 1, "and they share the statement's");

    // Without abandon, the belt: a second Ψ-landing question at one length
    // kills the first, since only one declaration can be waiting to land at
    // a position. (A same-named one is indistinguishable by position and is
    // exactly what `abandon` exists for.)
    let other = |body: &'static Term| GateItem { name: "other", ..item(body) };
    let cache = Cache::over(Store::empty("unused".into()));
    cache.begin_run();
    assert!(!cache.admits(&psi, &item(body_a)));
    assert!(!cache.admits(&psi, &other(body_b)));
    assert_eq!(cache.counts().hashed, 2);
    cache.accepted(&psi, &other(body_b), &[]);
    assert_eq!(cache.keys(), key_b, "the check key is content-addressed; the name is metadata");
    // `helper`'s question is dead: asking again renders again.
    assert!(!cache.admits(&psi, &item(body_a)));
    assert_eq!(cache.counts().hashed, 3);
}

/// A check that opened a sealed theorem proof leaned on that proof's body,
/// which no interface hash covers, so its verdict is not kept: a warm run
/// re-checks it, and vouches for everything else
/// (`issues/theorem-witness-unfolding.md`).
#[test]
fn a_verdict_that_opened_a_sealed_proof_is_not_kept() {
    let src = "record Wit { n: Nat, ok: n = 2 }
theorem wit(): Wit { Wit(n := 2, ok := refl) }
theorem wit_two(): wit().n = 2 { refl }
theorem two_two(): 2 = 2 { refl }
";
    let cache = Arc::new(Cache::over(Store::empty("unused".into())));
    let mut runs = Vec::new();
    for workers in [1usize, 4, 1] {
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.set_kernel_workers(workers);
        cache.begin_run();
        e.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
        let errs = e.check_source(src);
        assert!(errs.is_empty(), "the fixture must check: {}", errs[0].render(src));
        runs.push(cache.counts());
    }
    let cold = runs[0].clone();
    for (warm, earlier) in [(&runs[1], &runs[0]), (&runs[2], &runs[1])] {
        let warm = warm.since(earlier);
        assert_eq!(warm.checked, 1, "only `wit_two`, which opened `wit`, faces the kernel again");
        assert_eq!(warm.hits, cold.checked - 1, "every other declaration is vouched for");
    }
}

// -- 5. replay ---------------------------------------------------------------

/// A module replayed from its semantic image asks the gate the same questions
/// its source elaboration asked: a stored definition is the binding the cold
/// gate's `GateItem::binding` produced, over the same Ψ, so the warm store
/// vouches for it and the kernel runs on nothing (the statement of a stored
/// theorem, which carries no proof, asks about its statement alone: the next
/// test). An
/// empty store rechecks every body and records it, so the *second* replay is
/// the warm one; and a body the store never saw is not vouched for, at either
/// gate width.
#[test]
fn a_replayed_module_accepts_stored_verdicts_and_rechecks_only_misses() {
    use heather_elab::{ModuleDependencyIdentity, ModuleReplayError};
    use heather_kernel::term::{GlobalBinding, Term};

    let src = source(PROOF_A, "add(n, 0) = n");
    let cache = Arc::new(Cache::over(Store::empty("unused".into())));
    let mut cold = Elaborator::with_prelude().expect("prelude");
    cache.begin_run();
    cold.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
    let delta = cold
        .elab_module_delta("m", &src, ModuleDependencyIdentity::default())
        .unwrap_or_else(|e| panic!("the fixture must check: {}", e.render(&src)));
    let bodies = delta
        .extension()
        .iter()
        .filter(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
        .count();
    assert_eq!(bodies, 1, "`add` is the one transparent definition; the theorems are opaque");
    let c = cache.counts();
    assert_eq!((c.checked, c.hits), (4, 0), "cold: every declaration faced the kernel");

    for workers in [1usize, 4] {
        // Warm: the store holds every verdict the cold run earned.
        let mut warm = Elaborator::with_prelude().expect("prelude");
        warm.set_kernel_workers(workers);
        cache.begin_run();
        warm.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
        let before = cache.counts();
        warm.replay_module_delta(&delta, &ModuleDependencyIdentity::default())
            .expect("the stored suffix replays");
        let c = cache.counts().since(&before);
        assert_eq!(
            (c.checked, c.hits, c.hashed),
            (0, bodies, bodies),
            "width {workers}: a warm replay is vouched for, one render per body"
        );
        assert_eq!(warm.psi(), cold.psi(), "the replay lands the cold run's Ψ");

        // An empty store: every body is checked and recorded, and the next
        // replay against that store is warm.
        let fresh = Arc::new(Cache::over(Store::empty("unused".into())));
        for (round, expected) in [(1, (bodies, 0)), (2, (0, bodies))] {
            let mut e = Elaborator::with_prelude().expect("prelude");
            e.set_kernel_workers(workers);
            fresh.begin_run();
            e.set_gate(Arc::clone(&fresh) as Arc<dyn heather_elab::gate::KernelGate>);
            let before = fresh.counts();
            e.replay_module_delta(&delta, &ModuleDependencyIdentity::default())
                .expect("the stored suffix replays");
            let c = fresh.counts().since(&before);
            assert_eq!((c.checked, c.hits), expected, "width {workers}, round {round}");
        }

        // A body the store never saw: the kernel judges it, and refuses.
        let mut forged = delta.clone();
        let at = forged
            .extension()
            .iter()
            .position(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
            .unwrap();
        let GlobalBinding::Tm { body, .. } = &mut forged.extension_mut()[at] else {
            unreachable!()
        };
        *body = Some(heather_kernel::rc::Rc::new(Term::TmNat));
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.set_kernel_workers(workers);
        cache.begin_run();
        e.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
        let before = e.psi().clone();
        let counts = cache.counts();
        let verdict = e.replay_module_delta(&forged, &ModuleDependencyIdentity::default());
        assert!(
            matches!(verdict, Err(ModuleReplayError::Kernel(_))),
            "width {workers}: the forged body is refused through the kernel"
        );
        assert_eq!(e.psi(), &before, "nothing lands from a rejected replay");
        let c = cache.counts().since(&counts);
        assert_eq!((c.checked, c.hits), (1, 0), "width {workers}: the forged body was a miss");
        // The refused question is dead: the same store still vouches for the
        // genuine delta at the same Ψ position afterwards.
        cache.begin_run();
        let mut again = Elaborator::with_prelude().expect("prelude");
        again.set_kernel_workers(workers);
        again.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
        let before = cache.counts();
        again
            .replay_module_delta(&delta, &ModuleDependencyIdentity::default())
            .expect("the genuine suffix replays after a refused one");
        let c = cache.counts().since(&before);
        assert_eq!((c.checked, c.hits), (0, bodies), "width {workers}: still warm after a refusal");
    }
}

/// Replay `delta` in a fresh elaborator over `cache`, at kernel width
/// `workers`, and hand back what the gate counted.
fn replay_counts(
    cache: &Arc<Cache>,
    delta: &heather_elab::ModuleDelta,
    workers: usize,
) -> heather_cache::Counts {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.set_kernel_workers(workers);
    cache.begin_run();
    e.set_gate(Arc::clone(cache) as Arc<dyn heather_elab::gate::KernelGate>);
    let before = cache.counts();
    e.replay_module_delta(delta, &heather_elab::ModuleDependencyIdentity::default())
        .expect("the stored suffix replays");
    cache.counts().since(&before)
}

fn cold_delta(src: &str) -> heather_elab::ModuleDelta {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_delta("m", src, heather_elab::ModuleDependencyIdentity::default())
        .unwrap_or_else(|e| panic!("the fixture must check: {}", e.render(src)))
}

fn bodiless(delta: &heather_elab::ModuleDelta) -> usize {
    use heather_kernel::term::GlobalBinding;
    delta.extension().iter().filter(|b| matches!(b, GlobalBinding::Tm { body: None, .. })).count()
}

/// A replayed declaration without a body (a theorem, stored without its
/// proof) is vouched for by a verdict about its statement: the first replay
/// over an empty store checks every statement and records it, the second
/// checks none. Before, every load re-checked every statement, which was the
/// whole of a warm native world's `image_recheck`
/// (`issues/native-process-fixed-cost.md`).
///
/// The verdict is keyed by the interface hash, which renders each referent
/// as its own interface: the same statement text over a different `value`
/// is a different statement, and the store that vouched for the first does
/// not vouch for the second.
#[test]
fn a_replayed_statement_is_vouched_for_by_its_own_verdict_and_only_by_it() {
    let zero = cold_delta("fn value() -> Nat { 0 }\ntheorem same(): value() = value() { refl }\n");
    let one = cold_delta("fn value() -> Nat { 1 }\ntheorem same(): value() = value() { refl }\n");
    let n = bodiless(&zero);
    assert!(n >= 1, "`same` is stored without its proof");
    assert_eq!(bodiless(&one), n);
    for workers in [1usize, 4] {
        let cache = Arc::new(Cache::over(Store::empty("unused".into())));
        let c = replay_counts(&cache, &zero, workers);
        assert_eq!((c.statements_checked, c.statement_hits), (n, 0), "width {workers}: an empty store vouches for nothing");
        let c = replay_counts(&cache, &zero, workers);
        assert_eq!((c.statements_checked, c.statement_hits), (0, n), "width {workers}: the second replay is warm");
        let c = replay_counts(&cache, &one, workers);
        assert_eq!(
            (c.statements_checked, c.statement_hits),
            (n, 0),
            "width {workers}: the same text over a different referent is checked again"
        );
    }
}

/// A statement check that opened a sealed theorem proof keeps no verdict,
/// the rule `a_verdict_that_opened_a_sealed_proof_is_not_kept` states for
/// bodies: `uses`' statement is well-typed only because `wit().n` computes
/// to `2`, which reads `wit`'s sealed proof. Every warm replay checks it
/// again, and vouches for every other statement.
#[test]
fn a_statement_that_opened_a_sealed_proof_keeps_no_verdict() {
    let src = "record Wit { n: Nat, ok: n = 2 }
theorem wit(): Wit { Wit(n := 2, ok := refl) }
fn need(n: Nat, p: n = 2) -> Nat { n }
theorem uses(): need(wit().n, refl) = 2 { refl }
theorem two_two(): 2 = 2 { refl }
";
    let delta = cold_delta(src);
    let n = bodiless(&delta);
    for workers in [1usize, 4] {
        let cache = Arc::new(Cache::over(Store::empty("unused".into())));
        let c = replay_counts(&cache, &delta, workers);
        assert_eq!((c.statements_checked, c.statement_hits), (n, 0), "width {workers}: cold");
        for round in [2, 3] {
            let c = replay_counts(&cache, &delta, workers);
            assert_eq!(
                (c.statements_checked, c.statement_hits),
                (1, n - 1),
                "width {workers}, round {round}: only `uses`, which opened `wit`, is checked again"
            );
        }
    }
}

/// Elaborate `src` over `cache` at kernel width `workers`, as the build that
/// writes a module's image does, and hand back the suffix it would store.
fn gated_delta(cache: &Arc<Cache>, src: &str, workers: usize) -> heather_elab::ModuleDelta {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.set_kernel_workers(workers);
    cache.begin_run();
    e.set_gate(Arc::clone(cache) as Arc<dyn heather_elab::gate::KernelGate>);
    e.elab_module_delta("m", src, heather_elab::ModuleDependencyIdentity::default())
        .unwrap_or_else(|e| panic!("the fixture must check: {}", e.render(src)))
}

fn bodied(delta: &heather_elab::ModuleDelta) -> usize {
    use heather_kernel::term::GlobalBinding;
    delta.extension().iter().filter(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. })).count()
}

/// Two use sites of `Mag<Pair<Nat, Nat>>`: the derivation is minted as a
/// global of its own between `use1` and `use2`, by the resolver and not by a
/// declaration (`traits_resolution.rs`,
/// `a_derived_instance_is_minted_once_and_reused`). No two bindings have the
/// same content, so no verdict here answers for two of them (which is why
/// the carrier is `Nat` and not an enumeration declared here: the summands
/// of two nullary constructors are one definition written twice).
const DERIVING: &str = "class Mag<A> { op: A -> A -> A }
record Pair<A, B> { fst: A, snd: B }
instance Mag<Nat> { fn op(x: Nat, y: Nat) -> Nat { y } }
instance<A, B> Mag<Pair<A, B>> requires ma: Mag<A>, mb: Mag<B> {
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> {
    Pair { fst: ma.op(x.fst, y.fst), snd: mb.op(x.snd, y.snd) }
  }
}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A { m.op(x, y) }
fn use1(p: Pair<Nat, Nat>, q: Pair<Nat, Nat>) -> Pair<Nat, Nat> { combine(p, q) }
fn use2(p: Pair<Nat, Nat>, q: Pair<Nat, Nat>) -> Pair<Nat, Nat> { combine(q, p) }
theorem same(p: Pair<Nat, Nat>, q: Pair<Nat, Nat>): use1(p, q) = use2(q, p) { refl }
theorem two_two(): 2 = 2 { refl }
";

/// The first replay of an image asks the kernel nothing its build asked.
/// The build's gate checked every theorem's statement on the way to its
/// proof and every minted derivation before it landed, and each is a
/// verdict the store keeps: about the statement alone, which is what a
/// theorem stored without its proof asks at replay, and about the mint,
/// which used to face the kernel without the store being told
/// (`issues/first-replay-rechecks-what-the-build-checked.md`).
///
/// The control is the same replay over a store the build did not write to:
/// every binding is checked, the mint among them.
#[test]
fn the_first_replay_of_a_build_asks_the_kernel_nothing_the_build_asked() {
    let mut plain = Elaborator::with_prelude().expect("prelude");
    plain
        .elab_module_delta("m", DERIVING, heather_elab::ModuleDependencyIdentity::default())
        .unwrap_or_else(|e| panic!("the fixture must check: {}", e.render(DERIVING)));
    assert_eq!(plain.derived_instances().len(), 1, "the fixture mints one derivation");
    for workers in [1usize, 4] {
        let built = Arc::new(Cache::over(Store::empty("unused".into())));
        let delta = gated_delta(&built, DERIVING, workers);
        let (bodies, statements) = (bodied(&delta), bodiless(&delta));
        assert!(statements >= 2, "`same` and `two_two` are stored without their proofs");
        let c = replay_counts(&built, &delta, workers);
        assert_eq!((c.checked, c.hits), (0, bodies), "width {workers}: every body is one the build's gate passed");
        assert_eq!(
            (c.statements_checked, c.statement_hits),
            (0, statements),
            "width {workers}: every statement is one the build's gate passed"
        );
        let elsewhere = Arc::new(Cache::over(Store::empty("unused".into())));
        let c = replay_counts(&elsewhere, &delta, workers);
        assert_eq!((c.checked, c.hits), (bodies, 0), "width {workers}: another store vouches for no body");
        assert_eq!((c.statements_checked, c.statement_hits), (statements, 0), "width {workers}: nor for a statement");
    }
}

/// A build keeps no statement verdict for a theorem whose check opened a
/// sealed proof, as it keeps none about the theorem
/// (`a_statement_that_opened_a_sealed_proof_keeps_no_verdict` is the same
/// rule at replay): `uses`' statement is well-typed only because `wit().n`
/// computes to `2`. The first replay checks that one statement and no other.
#[test]
fn a_build_keeps_no_statement_verdict_that_opened_a_sealed_proof() {
    let src = "record Wit { n: Nat, ok: n = 2 }
theorem wit(): Wit { Wit(n := 2, ok := refl) }
fn need(n: Nat, p: n = 2) -> Nat { n }
theorem uses(): need(wit().n, refl) = 2 { refl }
theorem two_two(): 2 = 2 { refl }
";
    for workers in [1usize, 4] {
        let built = Arc::new(Cache::over(Store::empty("unused".into())));
        let delta = gated_delta(&built, src, workers);
        let n = bodiless(&delta);
        let c = replay_counts(&built, &delta, workers);
        assert_eq!(
            (c.statements_checked, c.statement_hits),
            (1, n - 1),
            "width {workers}: only `uses`, which opened `wit`, is checked at the first replay"
        );
    }
}

/// A question that died describes nothing that lands after it. `refused` is
/// asked about at the end of an empty Ψ and abandoned; another binding then
/// lands there without asking, as an inductive's or a prelude's does, and a
/// definition that refers to it is keyed by what landed. Before, the dead
/// question's interface hash was still waiting for whatever landed at its
/// index, and the dependent's key named the refused declaration.
#[test]
fn an_abandoned_question_does_not_describe_what_lands_in_its_place() {
    use heather_elab::gate::{GateItem, KernelGate};
    use heather_kernel::layer::Layer;
    use heather_kernel::level::Level;
    use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type};

    let empty = LocalCtx::nil();
    let level = Level::constant(0);
    let nothing = GlobalCtx::new(Vec::new());
    let landed = GlobalCtx::new(vec![GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: heather_kernel::rc::Rc::new(Type::Nat),
        level: Level::constant(0),
        body: Some(heather_kernel::rc::Rc::new(Term::TmUnit { level: Level::constant(0) })),
    }])
    .with_consts(1);
    let refused = Term::TmNat;
    let reads = Term::GlobalTm { var: GlobalVar::constant(0), subst: LocalSubst { tail: SubstTail::Empty, terms: vec![] } };
    let item = |name: &'static str, body: &'static Term| GateItem {
        name,
        ctx: &empty,
        ty: &Type::Nat,
        level: &level,
        body,
        opaque: false,
        layer: Layer::Code,
        lands_in_psi: true,
    };
    let refused: &'static Term = Box::leak(Box::new(refused));
    let reads: &'static Term = Box::leak(Box::new(reads));
    let dependent_key = |a_question_died_first: bool| {
        let cache = Cache::over(Store::empty("unused".into()));
        cache.begin_run();
        if a_question_died_first {
            assert!(!cache.admits(&nothing, &item("refused", refused)));
            cache.abandon(&nothing);
        }
        assert!(!cache.admits(&landed, &item("dependent", reads)));
        cache.accepted(&landed, &item("dependent", reads), &[]);
        let keys = cache.keys();
        assert_eq!(keys.len(), 1);
        keys
    };
    assert_eq!(dependent_key(true), dependent_key(false), "the dependent is keyed by the binding that landed");
}

/// An elaborator and its forks share one gate and ask about different Ψs in
/// turn (`write-elf` reads its program on forks and checks its certificate
/// on the parent). The gate keeps the interface hashes of what the asking Ψ
/// shares with the last one and re-hashes only the rest, and what it keeps
/// is what a fresh gate computes: here the second fork, which lands more
/// bindings than the first before it asks anything, ends with exactly a
/// fresh run's hashes, and with none of the first fork's verdicts.
#[test]
fn forks_sharing_a_gate_keep_only_the_prefix_they_share() {
    let first = "fn value() -> Nat { 0 }\ntheorem same(): value() = value() { refl }\n";
    let second = "record Pair { a: Nat, b: Nat }\nfn value() -> Nat { 1 }\ntheorem same(): value() = value() { refl }\n";
    let cache = Arc::new(Cache::over(Store::empty("unused".into())));
    let mut parent = Elaborator::with_prelude().expect("prelude");
    cache.begin_run();
    parent.set_gate(Arc::clone(&cache) as Arc<dyn heather_elab::gate::KernelGate>);
    parent.fork().elab_module_source("m", first).unwrap_or_else(|e| panic!("{}", e.render(first)));
    let before = cache.counts();
    parent.fork().elab_module_source("m", second).unwrap_or_else(|e| panic!("{}", e.render(second)));
    let c = cache.counts().since(&before);
    assert_eq!(c.hits, 0, "nothing the first fork checked vouches for the second's declarations");

    let fresh = Arc::new(Cache::over(Store::empty("unused".into())));
    let mut alone = Elaborator::with_prelude().expect("prelude");
    fresh.begin_run();
    alone.set_gate(Arc::clone(&fresh) as Arc<dyn heather_elab::gate::KernelGate>);
    alone.elab_module_source("m", second).unwrap_or_else(|e| panic!("{}", e.render(second)));
    assert_eq!(cache.interface_hashes(), fresh.interface_hashes(), "the kept prefix is a fresh gate's");
    assert_eq!(c.checked, fresh.counts().checked);

    // And back on the first fork's text: its verdicts are still the store's.
    let before = cache.counts();
    parent.fork().elab_module_source("m", first).unwrap_or_else(|e| panic!("{}", e.render(first)));
    let c = cache.counts().since(&before);
    assert_eq!(c.checked, 0, "every declaration of the first text is vouched for");
}

/// The same rule at the gate interface, where a Ψ that diverges from the
/// last one and is already longer than the hashed prefix can be built
/// directly: before 2026-10-29 the gate trusted the prefix for any Ψ at
/// least as long, so the second Ψ's first binding took the first Ψ's hash.
#[test]
fn a_longer_divergent_psi_does_not_inherit_the_last_ones_hashes() {
    use heather_elab::gate::{GateItem, KernelGate};
    use heather_kernel::layer::Layer;
    use heather_kernel::level::Level;
    use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};

    let empty = LocalCtx::nil();
    let level = Level::constant(0);
    let def = |body: Term| GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: heather_kernel::rc::Rc::new(Type::Nat),
        level: Level::constant(0),
        body: Some(heather_kernel::rc::Rc::new(body)),
    };
    let unit = || Term::TmUnit { level: Level::constant(0) };
    // Committed bindings, as an elaborator's Ψ is: only a signature has keys.
    let first = GlobalCtx::new(vec![def(Term::TmNat)]).with_consts(1);
    let second = GlobalCtx::new(vec![def(unit()), def(Term::TmNat)]).with_consts(2);
    let body = Term::TmNat;
    let item = GateItem {
        name: "next",
        ctx: &empty,
        ty: &Type::Nat,
        level: &level,
        body: &body,
        opaque: true,
        layer: Layer::Code,
        lands_in_psi: true,
    };
    let cache = Cache::over(Store::empty("unused".into()));
    cache.begin_run();
    cache.admits(&first, &item);
    cache.abandon(&first);
    cache.admits(&second, &item);
    let fresh = Cache::over(Store::empty("unused".into()));
    fresh.begin_run();
    fresh.admits(&second, &item);
    assert_eq!(cache.interface_hashes(), fresh.interface_hashes());
    assert_eq!(fresh.interface_hashes().len(), 2, "the second Ψ's bindings were hashed");
}
