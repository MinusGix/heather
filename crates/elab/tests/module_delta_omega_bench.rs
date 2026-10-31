//! Manual end-to-end benchmark for Stage 3's forcing dependency closure.
//!
//! Kept ignored because source-building `omega.hthr` is intentionally a
//! minutes-scale acceptance workload. Run with:
//! `scripts/test --release -p heather-elab --test module_delta_omega_bench -- --ignored --nocapture`

use std::time::Instant;

use heather_elab::{Elaborator, ModuleDependencyIdentity, ModuleDelta};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/tactic/omega.hthr");

fn identity(n: usize) -> ModuleDependencyIdentity {
    ModuleDependencyIdentity::new((0..n).map(|i| [i as u8; 32]).collect())
}

#[test]
#[ignore = "manual minutes-scale source/replay benchmark"]
fn omega_dependency_closure_source_vs_safe_replay() {
    let modules = [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("algebra", ALGEBRA),
        ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
        ("int", INT),
        ("omega", OMEGA),
    ];
    let mut source = Elaborator::with_prelude().expect("prelude");
    let source_started = Instant::now();
    let mut deltas: Vec<ModuleDelta> = Vec::new();
    for (i, (name, text)) in modules.iter().enumerate() {
        let started = Instant::now();
        let delta = source
            .elab_module_delta(name, text, identity(i))
            .unwrap_or_else(|error| panic!("source `{name}`: {error}"));
        eprintln!("module-delta source {name}: {:.3}s", started.elapsed().as_secs_f64());
        deltas.push(delta);
    }
    let source_elapsed = source_started.elapsed();

    let mut replay = Elaborator::with_prelude().expect("prelude");
    let replay_started = Instant::now();
    for (i, delta) in deltas.iter().enumerate() {
        let started = Instant::now();
        replay
            .replay_module_delta(delta, &identity(i))
            .unwrap_or_else(|error| panic!("replay `{}`: {error}", delta.module()));
        eprintln!(
            "module-delta replay {}: {:.3}s",
            delta.module(),
            started.elapsed().as_secs_f64()
        );
    }
    let replay_elapsed = replay_started.elapsed();
    assert_eq!(replay.psi(), source.psi());
    eprintln!(
        "module-delta omega closure: source={:.3}s replay={:.3}s speedup={:.2}x bindings={}",
        source_elapsed.as_secs_f64(),
        replay_elapsed.as_secs_f64(),
        source_elapsed.as_secs_f64() / replay_elapsed.as_secs_f64(),
        replay.psi().bindings.len(),
    );
}
