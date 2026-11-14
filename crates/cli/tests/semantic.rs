//! The semantic loader is a library boundary, not merely an implementation
//! detail of the `heather` binary.

use heather_cli::loader::Module;
use heather_cache::module_image::{ImageFreshness, ModuleCacheKey, ModuleImageCache, SemanticsIdentity};
use heather_cli::semantic::{CacheNoticeKind, SemanticSession};
use heather_elab::ModuleDependencyIdentity;
use heather_elab::{Elaborator, LintProfile};

fn temp(tag: &str) -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "heather-semantic-session-{tag}-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&path);
    path
}

#[test]
fn a_fresh_consumer_can_replay_a_previous_sessions_module() {
    let cache = temp("replay");
    let module = Module {
        name: "sample".into(),
        path: "sample.hthr".into(),
        src: "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n".into(),
    };

    let mut cold_elab = Elaborator::with_prelude().unwrap();
    let mut cold = SemanticSession::new(Some(cache.clone()));
    let outcome = cold.check(&mut cold_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(!outcome.replayed);
    assert_eq!(cold.hits(), 0);

    let expected_psi = cold_elab.psi().clone();
    let mut warm_elab = Elaborator::with_prelude().unwrap();
    let mut warm = SemanticSession::new(Some(cache.clone()));
    let outcome = warm.check(&mut warm_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(outcome.replayed);
    assert_eq!(warm.hits(), 1);
    assert_eq!(warm_elab.psi(), &expected_psi);

    let _ = std::fs::remove_dir_all(cache);
}

#[test]
fn an_uncached_session_preserves_the_plain_source_path() {
    let module = Module {
        name: "bad".into(),
        path: "bad.hthr".into(),
        src: "theorem open(n: Nat): n = n { ? }".into(),
    };
    let mut elab = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(None);
    let outcome = session.check(&mut elab, &module, LintProfile::Default);
    assert!(!outcome.errors.is_empty());
    assert!(!outcome.replayed);
    assert!(outcome.notices.is_empty());
    assert_eq!(session.hits(), 0);
}

/// The inner-loop policy after a compiler edit: an image another build wrote
/// is replayed and said so, per module; the default policy rebuilds instead.
#[test]
fn a_stale_image_is_replayed_only_under_the_accepting_policy_and_is_reported() {
    let cache = temp("stale");
    let module = Module {
        name: "sample".into(),
        path: "sample.hthr".into(),
        src: "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n".into(),
    };
    // Stage the artifact a previous build would have left behind.
    let dependencies = ModuleDependencyIdentity::default();
    let key = ModuleCacheKey::for_source(&module.name, &module.src, &dependencies, LintProfile::Default);
    let mut writer = Elaborator::with_prelude().unwrap();
    let delta = writer
        .elab_module_delta(&module.name, &module.src, dependencies)
        .unwrap();
    let expected_psi = writer.psi().clone();
    ModuleImageCache::new(cache.clone())
        .publish_as(key, &delta, &[], SemanticsIdentity::of("older", "build"))
        .unwrap();

    let mut exact_elab = Elaborator::with_prelude().unwrap();
    let mut exact = SemanticSession::new(Some(cache.clone()));
    let outcome = exact.check(&mut exact_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(!outcome.replayed, "the exact policy rebuilds");
    assert!(outcome.notices.is_empty(), "{:?}", outcome.notices);
    assert_eq!(exact.stale_hits(), 0);

    // The rebuild overwrote the artifact; stage the stale one again.
    ModuleImageCache::new(cache.clone())
        .publish_as(key, &delta, &[], SemanticsIdentity::of("older", "build"))
        .unwrap();
    let mut stale_elab = Elaborator::with_prelude().unwrap();
    let mut stale = SemanticSession::new(Some(cache.clone()))
        .with_freshness(ImageFreshness::AcceptStale);
    let outcome = stale.check(&mut stale_elab, &module, LintProfile::Default);
    assert!(outcome.errors.is_empty());
    assert!(outcome.replayed);
    assert_eq!(stale.hits(), 1);
    assert_eq!(stale.stale_hits(), 1);
    assert_eq!(outcome.notices.len(), 1);
    assert_eq!(outcome.notices[0].kind, CacheNoticeKind::StaleReplayed);
    assert!(outcome.notices[0].to_string().contains("another build"), "{}", outcome.notices[0]);
    assert_eq!(stale_elab.psi(), &expected_psi);

    let _ = std::fs::remove_dir_all(cache);
}

#[test]
fn reexport_dependencies_load_replay_and_invalidate_through_a_facade() {
    let root = temp("reexports");
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    let origin = root.join("origin.hthr");
    let facade = root.join("facade.hthr");
    let client = root.join("client.hthr");
    std::fs::write(&origin, "fn value() -> Nat { 7 } fn hidden() -> Nat { 9 }").unwrap();
    std::fs::write(&facade, "export origin::{value};").unwrap();
    std::fs::write(&client, "import facade; theorem correct(): facade::value() = 7 { refl }").unwrap();
    for warm in [false, true] {
        let modules = heather_cli::loader::load(&client, &[]).unwrap_or_else(|e| panic!("{}", e.msg));
        assert_eq!(modules.iter().map(|m| m.name.as_str()).collect::<Vec<_>>(), ["origin", "facade", "client"]);
        let mut e = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(cache.clone()));
        for module in &modules {
            let out = session.check(&mut e, module, LintProfile::Default);
            assert!(out.errors.is_empty(), "{}", module.name);
            assert_eq!(out.replayed, warm, "{}", module.name);
        }
    }
    // A changed origin invalidates the unchanged facade and its client.
    std::fs::write(&origin, "fn value() -> Nat { 8 } fn hidden() -> Nat { 9 }").unwrap();
    let modules = heather_cli::loader::load(&client, &[]).unwrap_or_else(|e| panic!("{}", e.msg));
    let mut e = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(Some(cache.clone()));
    for module in &modules {
        let out = session.check(&mut e, module, LintProfile::Default);
        assert!(!out.replayed, "{}", module.name);
        assert_eq!(out.errors.is_empty(), module.name != "client");
    }
    // Export edges participate in the loader's ordinary cycle check.
    std::fs::write(&origin, "export facade::{value};").unwrap();
    assert!(heather_cli::loader::load(&client, &[]).is_err());
    let _ = std::fs::remove_dir_all(root);
}

/// Two processes missing one key at once build it once: the second waits on
/// the key's build lock, looks again, and replays what the first published
/// (`ModuleImageCache::build_lock`). The test holds the lock itself as the
/// "first process", so the session under test must be blocked while it is
/// held and must replay, not elaborate, once it is released.
#[test]
fn a_miss_waits_for_a_concurrent_build_of_the_same_key_and_replays_it() {
    let cache = temp("single-flight");
    let name = "sample";
    let src = "theorem stable(n: Nat): n = n { refl }\nfn value() -> Nat { 0 }\n";
    let dependencies = ModuleDependencyIdentity::default();
    let key = ModuleCacheKey::for_source(name, src, &dependencies, LintProfile::Default);
    let store = ModuleImageCache::new(cache.clone());
    let lock = store.build_lock(key).expect("a fresh store can take a build lock");

    let (done, finished) = std::sync::mpsc::channel();
    let waiter = std::thread::spawn({
        let cache = cache.clone();
        move || {
            let module = Module { name: name.into(), path: "sample.hthr".into(), src: src.into() };
            let mut elab = Elaborator::with_prelude().unwrap();
            let mut session = SemanticSession::new(Some(cache));
            let outcome = session.check(&mut elab, &module, LintProfile::Default);
            done.send(()).unwrap();
            (outcome.errors.is_empty(), outcome.replayed, session.hits(), elab.psi().clone())
        }
    });
    // Elaborating this module takes milliseconds; a session that did not
    // wait would be finished long before this.
    assert!(
        finished.recv_timeout(std::time::Duration::from_millis(500)).is_err(),
        "the session elaborated instead of waiting on the build lock"
    );

    let mut writer = Elaborator::with_prelude().unwrap();
    let delta = writer.elab_module_delta(name, src, dependencies).unwrap();
    store.publish(key, &delta, &[]).unwrap();
    drop(lock);

    let (clean, replayed, hits, psi) = waiter.join().unwrap();
    assert!(clean);
    assert!(replayed, "the waiter rebuilt a key the lock holder published");
    assert_eq!(hits, 1);
    assert_eq!(&psi, writer.psi());

    let _ = std::fs::remove_dir_all(cache);
}

/// One pass over `client`'s closure in `root`: per module, whether it was
/// replayed and the kinds of the notices it got; the session's relocation
/// count; and the Ψ it left.
struct Pass {
    modules: Vec<(String, bool, Vec<CacheNoticeKind>)>,
    relocated: usize,
    psi: heather_kernel::term::GlobalCtx,
}

fn pass(client: &std::path::Path, cache: Option<&std::path::Path>, freshness: ImageFreshness, audit: Option<&std::path::Path>) -> Pass {
    let modules = heather_cli::loader::load(client, &[]).unwrap_or_else(|e| panic!("{}", e.msg));
    let mut e = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(cache.map(|c| c.to_path_buf()))
        .with_freshness(freshness)
        .with_audit(audit.map(|a| a.to_path_buf()));
    let mut out = Vec::new();
    for module in &modules {
        let o = session.check(&mut e, module, LintProfile::Default);
        assert!(o.errors.is_empty(), "{}: {:?}", module.name, o.errors);
        out.push((module.name.clone(), o.replayed, o.notices.iter().map(|n| n.kind).collect()));
    }
    Pass { modules: out, relocated: session.relocated(), psi: e.psi().clone() }
}

/// A library edit under a client: the client is checked once over `before`,
/// then `before` becomes `after` and the stale lane runs again. Returns that
/// second pass, after asserting that it left exactly the Ψ an uncached
/// elaboration of the edited closure does — whether the client was moved or
/// re-elaborated, the result is the same world.
fn edit(tag: &str, before: &str, after: &str, client: &str) -> Pass {
    let root = temp(tag);
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    let origin = root.join("origin.hthr");
    let client_path = root.join("client.hthr");
    std::fs::write(&origin, before).unwrap();
    std::fs::write(&client_path, client).unwrap();
    pass(&client_path, Some(&cache), ImageFreshness::AcceptStale, None);
    std::fs::write(&origin, after).unwrap();
    let moved = pass(&client_path, Some(&cache), ImageFreshness::AcceptStale, None);
    let fresh = pass(&client_path, None, ImageFreshness::Exact, None);
    assert!(moved.psi == fresh.psi, "{tag}: the stale lane's world differs from a fresh elaboration");
    assert!(!moved.modules[0].1, "{tag}: the edited module itself replayed");
    let _ = std::fs::remove_dir_all(root);
    moved
}

const ORIGIN: &str = "fn value() -> Nat { 7 }\ninductive Shade { Light, Dark }\nfn shade() -> Shade { Shade::Dark }\n";
const CLIENT: &str = "import origin;\ntheorem correct(): origin::value() = 7 { refl }\nfn pick(s: origin::Shade) -> Nat { match s { Light => 0, Dark => origin::value() } }\ntheorem picked(): pick(origin::shade()) = 7 { refl }\n";

/// Early cutoff (`docs/module-interface-cutoff-design.md`): a theorem added
/// to a dependency, ahead of everything the client refers to so that every
/// reference moves, leaves the client's elaboration unobserved. The stale
/// lane moves its image onto the new world instead of elaborating it.
#[test]
fn a_client_moves_over_a_theorem_added_ahead_of_what_it_uses() {
    let after = format!("theorem unrelated(n: Nat): n = n {{ refl }}\n{ORIGIN}");
    let moved = edit("cutoff-prepend", ORIGIN, &after, CLIENT);
    assert_eq!(moved.relocated, 1);
    assert_eq!(moved.modules[1].0, "client");
    assert!(moved.modules[1].1);
    assert_eq!(moved.modules[1].2, [CacheNoticeKind::Relocated]);
}

/// A changed statement the client never refers to is not observed either.
#[test]
fn a_client_moves_over_a_changed_theorem_it_does_not_use() {
    let before = format!("{ORIGIN}theorem unrelated(n: Nat): n = n {{ refl }}\n");
    let after = format!("{ORIGIN}theorem unrelated(n: Nat): 0 = 0 {{ refl }}\n");
    assert_eq!(edit("cutoff-unused", &before, &after, CLIENT).relocated, 1);
}

/// A module's registry digest does not depend on which world first asked for
/// it (`issues/registry-digest-taken-in-observer-coordinates.md`). `shape`
/// declares a record and stands after `wide` in `client`'s world (`wide` has
/// the larger closure, so its world is the spine), not where its own world
/// puts it. The first session meets `shape` only under
/// `client`; the second, after an edit to `origin`, meets it first under
/// `near`, where it stands in its own place. Both take the same digest, and
/// `client` is moved.
#[test]
fn a_registry_digest_is_the_same_whichever_world_asks_first() {
    let root = temp("cutoff-digest-coordinates");
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    let write = |name: &str, src: &str| std::fs::write(root.join(name), src).unwrap();
    write("origin.hthr", ORIGIN);
    write("shape.hthr", "import origin;\nrecord Shape { side: Nat }\nfn round() -> Shape { Shape { side: origin::value() } }\n");
    let wide: String =
        (0..12).map(|i| format!("fn wide{i}() -> Nat {{ origin::value() }}\ntheorem wide{i}_is(): wide{i}() = 7 {{ refl }}\n")).collect();
    write("pad.hthr", "import origin;\nfn pad() -> Nat { origin::value() }\n");
    write("wide.hthr", &format!("import origin;\nimport pad;\n{wide}"));
    write(
        "client.hthr",
        "import wide;\nimport shape;\nfn side(s: shape::Shape) -> Nat { s.side }\nfn flat() -> Nat { side(shape::round()) }\ntheorem flat_is(): flat() = wide::wide0() { refl }\n",
    );
    write("near.hthr", "import shape;\nfn again() -> shape::Shape { shape::round() }\n");
    write("top.hthr", "import near;\nimport client;\n");
    let first = pass(&root.join("client.hthr"), Some(&cache), ImageFreshness::AcceptStale, None);
    assert_eq!(first.relocated, 0);
    write("origin.hthr", &format!("theorem unrelated(n: Nat): n = n {{ refl }}\n{ORIGIN}"));
    let moved = pass(&root.join("top.hthr"), Some(&cache), ImageFreshness::AcceptStale, None);
    let order: Vec<&str> = moved.modules.iter().map(|m| m.0.as_str()).collect();
    let at = |name: &str| order.iter().position(|m| *m == name).unwrap_or_else(|| panic!("{name} in {order:?}"));
    assert!(at("near") < at("client"), "{order:?}");
    let client = &moved.modules[at("client")];
    assert!(client.1, "the client was elaborated again: {:?}", client.2);
    assert_eq!(client.2, [CacheNoticeKind::Relocated]);
    let fresh = pass(&root.join("top.hthr"), None, ImageFreshness::Exact, None);
    assert!(moved.psi == fresh.psi, "the stale lane's world differs from a fresh elaboration");
    let _ = std::fs::remove_dir_all(root);
}

/// Negative controls: each edit below is something the client observed, and
/// the client is elaborated again, never moved.
#[test]
fn a_client_is_elaborated_again_when_it_observed_the_edit() {
    let client = "import origin;\ntheorem same(): origin::value() = origin::value() { refl }\nfn helper(unrelated: Nat) -> Nat { unrelated }\n";
    for (tag, after) in [
        // The body of a definition it refers to (its content hash).
        ("cutoff-body", ORIGIN.replace("{ 7 }", "{ 8 }")),
        // A new declaration named like an identifier the client wrote.
        ("cutoff-name", format!("{ORIGIN}fn unrelated() -> Nat {{ 0 }}\n")),
        // A new inductive: a registry change anywhere in the world.
        ("cutoff-registry", format!("{ORIGIN}inductive Hue {{ Red, Green }}\n")),
    ] {
        let p = edit(tag, ORIGIN, &after, client);
        assert_eq!(p.relocated, 0, "{tag}");
        assert!(!p.modules[1].1, "{tag}: the client replayed");
    }
}

/// The exact lane never moves an image, and does not replay one the stale
/// lane moved (it was written under another semantics identity). With an
/// audit file it does attempt the move and records that the elaboration
/// reproduced it.
#[test]
fn the_exact_lane_never_relocates_and_audits_the_move() {
    let root = temp("cutoff-exact");
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    let audit = root.join("audit.tsv");
    let origin = root.join("origin.hthr");
    let client = root.join("client.hthr");
    std::fs::write(&origin, ORIGIN).unwrap();
    std::fs::write(&client, CLIENT).unwrap();
    pass(&client, Some(&cache), ImageFreshness::Exact, None);
    std::fs::write(&origin, format!("theorem unrelated(n: Nat): n = n {{ refl }}\n{ORIGIN}")).unwrap();
    let exact = pass(&client, Some(&cache), ImageFreshness::Exact, Some(&audit));
    assert_eq!(exact.relocated, 0);
    assert!(exact.modules.iter().all(|m| !m.1));
    assert_eq!(std::fs::read_to_string(&audit).unwrap(), "client\tsame\t\n");

    // A stale-lane move, then the exact lane over the same world: the moved
    // image is not the exact lane's to replay.
    std::fs::write(&origin, format!("theorem unrelated2(n: Nat): n = n {{ refl }}\n{ORIGIN}")).unwrap();
    assert_eq!(pass(&client, Some(&cache), ImageFreshness::AcceptStale, None).relocated, 1);
    let again = pass(&client, Some(&cache), ImageFreshness::AcceptStale, None);
    assert_eq!(again.modules[1].2, [CacheNoticeKind::Relocated], "a moved image replays as moved");
    let exact = pass(&client, Some(&cache), ImageFreshness::Exact, None);
    assert!(!exact.modules[1].1, "the exact lane replayed a moved image");
    let _ = std::fs::remove_dir_all(root);
}

/// A theorem turned into an assumption of the same statement is a change to
/// every client of it, though the kernel binding is the same shape: the
/// client's provenance now reaches an axiom.
#[test]
fn a_client_is_elaborated_again_when_a_theorem_it_uses_becomes_an_assumption() {
    let before = "theorem same_at(n: Nat): n = n { refl }\n";
    let after = "axiom same_at(n: Nat): n = n;\n";
    let client = "import origin;\ntheorem mine(m: Nat): m = m { origin::same_at(m) }\n";
    let p = edit("cutoff-axiom", before, after, client);
    assert_eq!(p.relocated, 0);
    assert!(!p.modules[1].1);
}

/// A name the elaboration looked up that the source never spells: `+` falls
/// back to whatever `add` resolves to. Renaming the old `add` and declaring
/// a new one leaves every binding the client referred to in place, by
/// content, under another name; only the lookup record notices that `+`
/// now means something else.
#[test]
fn a_client_is_elaborated_again_when_a_name_it_looked_up_changes_meaning() {
    let before = "fn add(a: Nat, b: Nat) -> Nat { a }\n";
    let after = "fn add_first(a: Nat, b: Nat) -> Nat { a }\nfn add(a: Nat, b: Nat) -> Nat { b }\n";
    let client = "import origin;\nfn sum(x: Nat, y: Nat) -> Nat { x + y }\n";
    let p = edit("cutoff-fallback", before, after, client);
    assert_eq!(p.relocated, 0);
    assert!(!p.modules[1].1);
}

fn module(name: &str, src: &str) -> Module {
    Module { name: name.into(), path: format!("{name}.hthr").into(), src: src.into() }
}

const SHADES: &str = "inductive Shade { Light, Dark }\nfn dark() -> Shade { Shade::Dark }\n";
const PICKER: &str = "import shades;\nfn pick(s: shades::Shade) -> Nat { match s { Light => 0, Dark => 1 } }\ntheorem picked(): pick(shades::dark()) = 1 { refl }\n";
const UNRELATED: &str = "inductive Other { A, B, C }\nfn first() -> Other { Other::A }\n";

/// A module is checked over its import closure alone
/// (`docs/module-dag-design.md` §2): a session that checked an unrelated
/// module, one with an inductive of its own, before it keys and builds it
/// exactly as a session that did not, so the second replays the first's
/// images. Before, a module's image was keyed by everything its process had
/// loaded before it, and the unrelated inductive also moved every later
/// nominal tag.
#[test]
fn a_module_means_the_same_whatever_else_its_process_loaded() {
    let cache = temp("closure");
    let mut alone = Elaborator::with_prelude().unwrap();
    let mut first = SemanticSession::new(Some(cache.clone()));
    for m in [module("shades", SHADES), module("picker", PICKER)] {
        let out = first.check(&mut alone, &m, LintProfile::Default);
        assert!(out.errors.is_empty() && !out.replayed, "{}", m.name);
    }

    let mut beside = Elaborator::with_prelude().unwrap();
    let prelude = beside.psi().bindings.len();
    let mut second = SemanticSession::new(Some(cache.clone()));
    let out = second.check(&mut beside, &module("unrelated", UNRELATED), LintProfile::Default);
    assert!(out.errors.is_empty() && !out.replayed);
    let unrelated = beside.psi().bindings.len() - prelude;
    for m in [module("shades", SHADES), module("picker", PICKER)] {
        let out = second.check(&mut beside, &m, LintProfile::Default);
        assert!(out.errors.is_empty(), "{}", m.name);
        assert!(out.replayed, "{} was elaborated again over a prefix holding an unrelated module", m.name);
    }
    assert_eq!(second.hits(), 2);
    // The caller's world holds all three, the two replayed ones moved past
    // the unrelated module.
    assert_eq!(beside.psi().bindings.len(), alone.psi().bindings.len() + unrelated);

    let _ = std::fs::remove_dir_all(cache);
}

/// A session that planned on an image and then finds it gone elaborates
/// the module again (`issues/image-sweep-removes-planned-image.md`). A
/// module replayed straight into the caller's world keeps no canonical
/// delta; a later module checked out of place needs its canonical world and
/// decodes it from the store again. Another process's sweep may have removed
/// the image between the two (here, the test removes every image), and that
/// is an ordinary miss: the module is rebuilt with the identity its
/// dependents were keyed by and published again, and the client checks.
#[test]
fn a_planned_image_swept_from_the_store_is_elaborated_again() {
    let cache = temp("swept");
    let mut cold = Elaborator::with_prelude().unwrap();
    let mut first = SemanticSession::new(Some(cache.clone()));
    let out = first.check(&mut cold, &module("shades", SHADES), LintProfile::Default);
    assert!(out.errors.is_empty() && !out.replayed);

    let mut beside = Elaborator::with_prelude().unwrap();
    let mut second = SemanticSession::new(Some(cache.clone()));
    let out = second.check(&mut beside, &module("unrelated", UNRELATED), LintProfile::Default);
    assert!(out.errors.is_empty());
    // Out of place behind `unrelated`: moved into the caller's world from
    // its image, its canonical delta not kept.
    let out = second.check(&mut beside, &module("shades", SHADES), LintProfile::Default);
    assert!(out.errors.is_empty() && out.replayed);

    let images = cache.join("modules-v1");
    for entry in std::fs::read_dir(&images).unwrap().flatten() {
        if entry.path().extension().and_then(|x| x.to_str()) == Some("hmi") {
            std::fs::remove_file(entry.path()).unwrap();
        }
    }

    // A client nothing has published, checked out of place: its world is
    // `shades`'s canonical one, whose image is gone.
    let client = module("picker", PICKER);
    let out = second.check(&mut beside, &client, LintProfile::Default);
    let text = out.errors.iter().map(|e| e.render(&client.src)).collect::<Vec<_>>().join("\n");
    assert!(out.errors.is_empty(), "{text}");
    assert!(!out.replayed);
    assert_eq!(second.hits(), 1, "the rebuild counted as one of the caller's modules");
    let key = ModuleCacheKey::for_source("shades", SHADES, &ModuleDependencyIdentity::default(), LintProfile::Default);
    assert!(ModuleImageCache::new(cache.clone()).path(key).exists(), "the rebuilt image was not published again");

    let _ = std::fs::remove_dir_all(cache);
}

const MAG: &str = "class Mag<A> { op: A -> A -> A }\nfn combine<A> requires m: Mag<A> (x: A, y: A) -> A { m.op(x, y) }\n";
const MAG_NAT: &str = "import mag;\ninstance Mag<Nat> { fn op(x: Nat, y: Nat) -> Nat { y } }\n";
const TWICE: &str = "fn twice(x: Nat) -> Nat { combine(x, x) }\ntheorem second(): twice(3) = 3 { refl }\n";

/// What a module sees of the registries is what its closure contributes
/// (`docs/module-dag-design.md` §2): an instance declared in a module the
/// client does not import is not found, although the session checked that
/// module first, and importing it is the fix. Before, every module checked
/// earlier in the process was visible, imported or not, so whether `twice`
/// checked depended on what else the process loaded.
#[test]
fn an_instance_is_visible_only_through_imports() {
    for cache in [None, Some(temp("instances"))] {
        let mut e = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(cache.clone());
        for m in [module("mag", MAG), module("mag_nat", MAG_NAT)] {
            assert!(session.check(&mut e, &m, LintProfile::Default).errors.is_empty(), "{}", m.name);
        }
        let blind = format!("import mag;\n{TWICE}");
        let out = session.check(&mut e, &module("blind", &blind), LintProfile::Default);
        assert!(!out.errors.is_empty(), "an instance from a module `blind` does not import was found");
        let seeing = format!("import mag;\nimport mag_nat;\n{TWICE}");
        let out = session.check(&mut e, &module("seeing", &seeing), LintProfile::Default);
        assert!(out.errors.is_empty(), "{:?}", out.errors.iter().map(|e| e.render(&seeing)).collect::<Vec<_>>());
        if let Some(cache) = cache {
            let _ = std::fs::remove_dir_all(cache);
        }
    }
}

/// A module whose closure holds one that did not check is not checked:
/// there is no world to check it in. One beside it, outside that closure,
/// is checked as usual, with its image.
#[test]
fn a_failed_import_stops_its_dependents_and_nothing_else() {
    let cache = temp("failed-import");
    let mut e = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(Some(cache.clone()));
    let broken = module("broken", "fn bad() -> Nat { Type }\n");
    assert!(!session.check(&mut e, &broken, LintProfile::Default).errors.is_empty());
    let dependent = module("dependent", "import broken;\nfn ok() -> Nat { 0 }\n");
    let out = session.check(&mut e, &dependent, LintProfile::Default);
    let text = out.errors.iter().map(|e| e.render(&dependent.src)).collect::<Vec<_>>().join("\n");
    assert!(text.contains("`broken`, which did not check"), "{text}");
    let beside = module("shades", SHADES);
    let out = session.check(&mut e, &beside, LintProfile::Default);
    assert!(out.errors.is_empty());
    let mut again = Elaborator::with_prelude().unwrap();
    let mut warm = SemanticSession::new(Some(cache.clone()));
    assert!(warm.check(&mut again, &beside, LintProfile::Default).replayed, "a module checked after a failure was not published");
    let _ = std::fs::remove_dir_all(cache);
}

const LEFT: &str = "import shades;\nfn left() -> shades::Shade { shades::dark() }\n";
const RIGHT: &str = "import shades;\nfn right() -> Nat { 2 }\n";
const TOP: &str = "import left;\nimport right;\ntheorem both(): right::right() = 2 { refl }\n";

/// A session told its load (`expect_load`) keeps a module's world only while
/// a module still to come imports it, and its delta only while one holds it
/// in its closure (`docs/module-dag-design.md` §8), so a folder of test
/// modules does not hold a world per test. A load that leaves an importer
/// out costs that importer a rebuilt world, never a verdict.
#[test]
fn a_session_lets_go_of_what_nothing_left_needs() {
    let diamond = || [module("shades", SHADES), module("left", LEFT), module("right", RIGHT), module("top", TOP)];
    for (tag, told) in [("load-all", 4), ("load-part", 2)] {
        let cache = temp(tag);
        let mut e = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(cache.clone())).without_process_world();
        let modules = diamond();
        let imports: Vec<Vec<String>> = modules.iter().map(|m| heather_cli::semantic::written_imports(&m.src)).collect();
        session.expect_load(modules.iter().zip(&imports).take(told).map(|(m, i)| (m.name.as_str(), i.as_slice())));
        let mut held = Vec::new();
        for m in &modules {
            let out = session.check(&mut e, m, LintProfile::Default);
            assert!(out.errors.is_empty(), "{tag} {}: {:?}", m.name, out.errors.iter().map(|e| e.render(&m.src)).collect::<Vec<_>>());
            held.push(session.held());
        }
        if told == 4 {
            // After `left`, `shades` is still imported by `right`; after
            // `right` only `top` needs the two sides, and after `top` nothing.
            assert_eq!(held, [(1, 1), (2, 2), (2, 3), (0, 0)], "{tag}");
        } else {
            // Only `shades` and `left` were announced, so after `left` nothing
            // is needed. `right` and `top` then rebuild the worlds after
            // `shades` and `left` from the store, and keep what they finish.
            assert_eq!(held[1], (0, 0), "{tag}");
            assert_eq!(held[3], (4, 2), "{tag}");
        }
        let _ = std::fs::remove_dir_all(cache);
    }
}

const REFUSING: &str = "fn good() -> Nat { 1 }\n\n// expect-error: unbound name\nfn bad() -> Nat { nope() }\n";
const OVER_REFUSING: &str = "import refusing;\ntheorem uses(): refusing::good() = 1 { refl }\n";

/// A module refused exactly as its directives say is, to a session that
/// judges them, a module that checked: it has an image, which replays with
/// its refusal count, and its dependents are checked over what did check
/// (`docs/module-dag-design.md` §11).
#[test]
fn a_module_refused_as_it_says_replays_for_a_judging_session() {
    let cache = temp("refusing");
    let (refusing, over) = (module("refusing", REFUSING), module("over_refusing", OVER_REFUSING));
    for warm in [false, true] {
        let mut e = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(cache.clone())).with_expectations();
        let out = session.check(&mut e, &refusing, LintProfile::Default);
        assert!(out.errors.is_empty(), "{:?}", out.errors.iter().map(|e| e.render(REFUSING)).collect::<Vec<_>>());
        assert_eq!((out.replayed, out.expected_refusals), (warm, 1));
        let out = session.check(&mut e, &over, LintProfile::Default);
        assert!(out.errors.is_empty(), "{:?}", out.errors.iter().map(|e| e.render(OVER_REFUSING)).collect::<Vec<_>>());
        assert_eq!(out.replayed, warm);
    }
    // A session that does not judge refusals never replays one: its refused
    // declaration is an error again.
    let mut e = Elaborator::with_prelude().unwrap();
    let mut plain = SemanticSession::new(Some(cache.clone()));
    let out = plain.check(&mut e, &refusing, LintProfile::Default);
    assert!(!out.replayed);
    assert_eq!(out.expected_refusals, 0);
    let text = out.errors.iter().map(|e| e.render(REFUSING)).collect::<Vec<_>>().join("\n");
    assert!(text.contains("unbound name"), "{text}");
    let _ = std::fs::remove_dir_all(cache);
}

/// A refusal another build recorded is not this build's verdict, and no
/// kernel recheck can make it one: the stale lane elaborates the module
/// again and judges it afresh.
#[test]
fn a_stale_image_of_refusals_is_elaborated_again() {
    let cache = temp("stale-refusing");
    let refusing = module("refusing", REFUSING);
    let dependencies = ModuleDependencyIdentity::default();
    let key = ModuleCacheKey::for_source(&refusing.name, &refusing.src, &dependencies, LintProfile::Default);
    let mut writer = Elaborator::with_prelude().unwrap();
    let (delta, errors) = writer.check_module_delta_refusing(&refusing.name, &refusing.src, dependencies);
    assert_eq!(errors.len(), 1);
    ModuleImageCache::new(cache.clone())
        .publish_refused(key, &delta, &[], SemanticsIdentity::of("older", "build"), None, 1)
        .unwrap();
    let mut e = Elaborator::with_prelude().unwrap();
    let mut stale = SemanticSession::new(Some(cache.clone()))
        .with_freshness(ImageFreshness::AcceptStale)
        .with_expectations();
    let out = stale.check(&mut e, &refusing, LintProfile::Default);
    assert!(!out.replayed, "a stale refusal was replayed");
    assert_eq!(stale.stale_hits(), 0);
    assert!(out.errors.is_empty());
    assert_eq!(out.expected_refusals, 1);
    let _ = std::fs::remove_dir_all(cache);
}

const JUDGED: &str = "import origin;\nfn before() -> Nat { origin::value() }\n\n// expect-error: unbound name\nfn bad() -> Nat { origin::nope() }\n\ntheorem after(): before() = 7 { refl }\n";

/// One judging pass over `root/judged.hthr` and its import: the client's
/// outcome, the session's relocation count and the Ψ it left.
fn judging(root: &std::path::Path, cache: Option<&std::path::Path>, freshness: ImageFreshness) -> (heather_cli::semantic::ModuleOutcome, usize, heather_kernel::term::GlobalCtx) {
    // The library is on the path for a client that imports `bool`.
    let lib = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    let modules = heather_cli::loader::load(&root.join("judged.hthr"), &[lib]).unwrap_or_else(|e| panic!("{}", e.msg));
    let mut e = Elaborator::with_prelude().unwrap();
    let mut session = SemanticSession::new(cache.map(|c| c.to_path_buf())).with_freshness(freshness).with_expectations();
    let mut last = None;
    for module in &modules {
        last = Some(session.check(&mut e, module, LintProfile::Default));
    }
    (last.expect("a module"), session.relocated(), e.psi().clone())
}

/// A module with directives over an edited dependency
/// (`issues/expected-refusal-modules-never-moved.md`): `before` writes
/// `judged.hthr` over `ORIGIN` and checks it, `after` rewrites `origin.hthr`.
fn judged_edit(tag: &str, after: &str) -> (std::path::PathBuf, std::path::PathBuf) {
    let root = temp(tag);
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    std::fs::write(root.join("origin.hthr"), ORIGIN).unwrap();
    std::fs::write(root.join("judged.hthr"), JUDGED).unwrap();
    let (first, relocated, _) = judging(&root, Some(&cache), ImageFreshness::AcceptStale);
    assert!(first.errors.is_empty(), "{tag}: {:?}", first.errors);
    assert_eq!((first.expected_refusals, first.replayed_items, relocated), (1, 0, 0), "{tag}");
    std::fs::write(root.join("origin.hthr"), after).unwrap();
    (root, cache)
}

/// The stale lane moves the accepted declarations of a module with
/// directives over an edit it did not observe, and elaborates the refused
/// one again: the refusal it reports is this build's, over this world. The
/// image it leaves says it holds moved declarations, so a later stale pass
/// does the same again and the exact lane elaborates the module whole.
#[test]
fn a_module_with_directives_moves_what_it_accepted_and_judges_its_refusals_again() {
    let (root, cache) = judged_edit("refusing-moves", &format!("theorem unrelated(n: Nat): n = n {{ refl }}\n{ORIGIN}"));
    let (fresh, _, fresh_psi) = judging(&root, Some(&root.join("fresh")), ImageFreshness::Exact);
    assert_eq!((fresh.expected_refusals, fresh.replayed_items), (1, 0));
    for again in [false, true] {
        let (moved, relocated, psi) = judging(&root, Some(&cache), ImageFreshness::AcceptStale);
        assert!(moved.errors.is_empty(), "{again}: {:?}", moved.errors);
        assert!(!moved.replayed, "{again}: an image of refusals replayed whole");
        // The import, `before` and `after` replay; `bad` is elaborated.
        assert_eq!((moved.expected_refusals, moved.replayed_items), (1, 3), "{again}");
        assert!(moved.notices.iter().any(|n| n.kind == CacheNoticeKind::Relocated), "{again}");
        assert!(relocated >= 1, "{again}");
        assert!(psi == fresh_psi, "{again}: the stale lane's world differs from a fresh elaboration");
    }
    let (exact, relocated, psi) = judging(&root, Some(&cache), ImageFreshness::Exact);
    assert_eq!((exact.replayed, exact.expected_refusals, exact.replayed_items, relocated), (false, 1, 0, 0));
    assert!(psi == fresh_psi);
    let _ = std::fs::remove_dir_all(root);
}

/// What a refusal says can draw on a note an earlier declaration's
/// elaboration left in the pass: why `tally` has no branch equation. A
/// declaration reproduced from a moved image leaves no note, the refusal
/// reads as a plain unbound name, and the directive would be missed. The
/// module is then elaborated whole and judged on that.
#[test]
fn a_refusal_that_reads_differently_over_moved_declarations_is_judged_on_a_whole_elaboration() {
    let noted = "import origin;\nimport bool;\nfn tally(b: Bool, n: Nat) -> Nat { if b { origin::value() } else { match n { Zero => 0, Succ(m) => tally(b, m) } } }\n\n// expect-error: no branch equation `tally::True`\ntheorem tally_true(n: Nat): tally(True, n) = 7 { tally::True(True, n) }\n";
    let root = temp("refusing-noted");
    std::fs::create_dir_all(&root).unwrap();
    let cache = root.join("cache");
    std::fs::write(root.join("origin.hthr"), ORIGIN).unwrap();
    std::fs::write(root.join("judged.hthr"), noted).unwrap();
    let (first, _, _) = judging(&root, Some(&cache), ImageFreshness::AcceptStale);
    assert!(first.errors.is_empty(), "{:?}", first.errors);
    assert_eq!(first.expected_refusals, 1);
    std::fs::write(root.join("origin.hthr"), format!("theorem unrelated(n: Nat): n = n {{ refl }}\n{ORIGIN}")).unwrap();
    let (out, relocated, psi) = judging(&root, Some(&cache), ImageFreshness::AcceptStale);
    assert!(out.errors.is_empty(), "{:?}", out.errors);
    assert_eq!((out.expected_refusals, out.replayed_items, relocated), (1, 0, 0));
    let (_, _, fresh_psi) = judging(&root, Some(&root.join("fresh")), ImageFreshness::Exact);
    assert!(psi == fresh_psi, "the world after the second elaboration differs from a fresh one");
    let _ = std::fs::remove_dir_all(root);
}

/// Negative controls. An edit the accepted declarations observed moves
/// nothing, and what they now fail with is reported. An edit that gives the
/// refused declaration its missing name moves nothing either, and the
/// declaration is accepted: no refusal is counted for a directive the
/// module no longer meets.
#[test]
fn a_module_with_directives_is_elaborated_again_when_it_observed_the_edit() {
    let (root, cache) = judged_edit("refusing-observed", &ORIGIN.replace("{ 7 }", "{ 8 }"));
    let (out, relocated, _) = judging(&root, Some(&cache), ImageFreshness::AcceptStale);
    assert_eq!((out.replayed_items, relocated), (0, 0));
    assert_eq!(out.errors.len(), 2, "{:?}", out.errors);
    let _ = std::fs::remove_dir_all(root);

    let (root, cache) = judged_edit("refusing-met", &format!("{ORIGIN}fn nope() -> Nat {{ 0 }}\n"));
    let (out, relocated, _) = judging(&root, Some(&cache), ImageFreshness::AcceptStale);
    assert!(out.errors.is_empty(), "{:?}", out.errors);
    assert_eq!((out.expected_refusals, out.replayed_items, relocated), (0, 0, 0));
    let _ = std::fs::remove_dir_all(root);
}

/// Refusals that do not meet their directives leave no image: the module
/// failed, and its raw errors go to the caller to judge.
#[test]
fn a_module_that_misses_its_directives_is_not_published() {
    let cache = temp("misses-directive");
    let src = REFUSING.replace("unbound name", "a reason it is not refused for");
    let refusing = module("refusing", &src);
    for _ in 0..2 {
        let mut e = Elaborator::with_prelude().unwrap();
        let mut session = SemanticSession::new(Some(cache.clone())).with_expectations();
        let out = session.check(&mut e, &refusing, LintProfile::Default);
        assert!(!out.replayed);
        assert_eq!(out.expected_refusals, 0);
        assert_eq!(out.errors.len(), 1);
    }
    let _ = std::fs::remove_dir_all(cache);
}
