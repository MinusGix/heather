use crate::common;
use heather_elab::function_ir_source::generate_elaborated_typed_x86;
use heather_elab::function_ir_x86_lower::{Gpr, Placements};
use heather_elab::stats;

// What a crossing's links cost (docs/native-first-program-design.md §10.1,
// issues/crossing-link-quadratic-cost.md): each link is checked over its
// crossing's name, so a link costs the same at every depth of a helper chain,
// and a helper whose body composes other helpers meets its source through the
// body's own call, never by unfolding the whole body.
const CLIENTS: &str = r#"import bitvec; import bool;
fn place(state, threshold, weight: BitVec(64)) → BitVec(64) {
    match state.unsigned_lt_bit(threshold) {
        True => state,
        False => state.sub(threshold).add(weight),
    }
}
fn double(x: BitVec(64)) → BitVec(64) { x.add(x) }
fn quad(x: BitVec(64)) → BitVec(64) { double(double(x)) }
fn oct(x: BitVec(64)) → BitVec(64) { quad(quad(x)) }
"#;

fn chain(depth: usize, seed: &str) -> String {
    (0..depth).fold(seed.to_string(), |state, i| format!("place({state}, BitVec::ofNat({}), BitVec::ofNat({}))", 1000 + i, i + 1))
}

// Kernel steps of every `_link`/`_link_at` item, by name within the
// certificate, the gate run serially.
fn link_steps(clients: &str, function: &str) -> Vec<(String, u64)> {
    let mut elab = common::base_image(common::MODULES.len());
    let model = include_str!("../../../lib/std/arch/x86_64/x86_64_structured_block.hthr");
    elab.elab_module_source("x86_64_structured_block", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    elab.set_kernel_workers(1);
    elab.elab_module_source("clients", clients).unwrap_or_else(|e| panic!("{}", e.render(clients)));
    let emission = generate_elaborated_typed_x86(&elab, "c", &format!("clients::{function}"),
        &Placements::from([(0, Gpr::Rdi), (1, Gpr::Rsi)]), &[Gpr::Rax, Gpr::Rdx, Gpr::Rcx, Gpr::R8, Gpr::R9], &Placements::from([(2, Gpr::Rax)]))
        .unwrap_or_else(|e| panic!("{function}: {e}"));
    elab.enable_item_timings();
    elab.elab_module_source("certificate", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    let rows = elab.take_item_timings();
    stats::disable();
    rows.into_iter().filter_map(|row| {
        let name = row.item.rsplit("::").next().filter(|name| name.starts_with("c_"))?.to_string();
        (name.ends_with("_link") || name.ends_with("_link_at")).then_some((name, row.kernel.eval_steps))
    }).collect()
}

// The link at crossing level `level`: the name's `prefix_` count.
fn level(name: &str) -> usize { name.matches("prefix_").count() }

#[test]
fn slow_acceptance_crossing_links_cost_the_same_at_every_depth() {
    let at = |depth: usize| {
        let clients = format!("{CLIENTS}fn chain(n, unused: BitVec(64)) → BitVec(64) {{ {} }}\n", chain(depth, "n.add(BitVec::ofNat(1))"));
        link_steps(&clients, "chain")
    };
    let (short, long) = (at(3), at(8));
    eprintln!("links at depth 3: {short:?}\nlinks at depth 8: {long:?}");
    // Every link of the shorter chain costs exactly what the same kind of
    // link costs in the longer one, at every level.
    let cost = |links: &[(String, u64)], kind: &str| -> Vec<u64> {
        let mut costs: Vec<_> = links.iter().filter(|(name, _)| name.ends_with(kind)).map(|(name, steps)| (level(name), *steps)).collect();
        costs.sort();
        costs.into_iter().map(|(_, steps)| steps).collect()
    };
    for kind in ["_link_at", "_link"] {
        let (short, long) = (cost(&short, kind), cost(&long, kind));
        assert!(!short.is_empty() && long.len() > short.len(), "{kind}: {short:?} {long:?}");
        let flat = long[0];
        assert!(long[..long.len() - 1].iter().all(|&steps| steps == flat), "{kind} cost moves with depth: {long:?}");
        assert!(short[..short.len() - 1].iter().all(|&steps| steps == flat), "{kind} cost moves with chain length: {short:?} vs {long:?}");
    }
}

// `oct`'s body is `quad(quad(x))` and `quad`'s is `double(double(x))`: the
// three share a result port. The `oct` crossing's link reads `oct`'s own body
// call over its child; with only the innermost body kept, it once fell back
// to one `refl` that unfolded every doubling (545K steps under `raise` in
// `decimal_line`).
#[test]
fn slow_acceptance_a_nested_helper_links_through_its_own_body() {
    let clients = format!("{CLIENTS}fn chain(n, unused: BitVec(64)) → BitVec(64) {{ {} }}\n", chain(2, "oct(n)"));
    let links = link_steps(&clients, "chain");
    eprintln!("links: {links:?}");
    // The plain `_link`s are one step of transport each once `_link_at`
    // carries the comparison; the costliest one stays below its `_link_at`s.
    let plain = links.iter().filter(|(name, _)| name.ends_with("_link")).map(|(_, steps)| *steps).max().unwrap();
    let at = links.iter().filter(|(name, _)| name.ends_with("_link_at")).map(|(_, steps)| *steps).max().unwrap();
    assert!(plain < at, "a link compares an unfolded body: {links:?}");
    // One `_link_at` per crossing whose prefix is itself a crossing: both
    // `place`s, `oct`'s `quad` and `quad`'s `double`.
    assert!(links.iter().filter(|(name, _)| name.ends_with("_link_at")).count() >= 3, "{links:?}");
}
