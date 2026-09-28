//! Small deterministic evaluator-count probes. Setup is excluded from the
//! measured declaration, and the kernel gate runs serially. No wall-time gate.
use heather_elab::{Elaborator, stats};

fn measure(setup: &str, source: &str, item: &str, refusal: &str) -> u64 {
    measure_item(setup, source, item, refusal).kernel.eval_steps
}

fn measure_item(setup: &str, source: &str, item: &str, refusal: &str) -> stats::ItemTiming {
    let mut el = Elaborator::with_prelude().expect("prelude");
    el.set_kernel_workers(1);
    el.elab_source(setup).unwrap_or_else(|e| panic!("{}", e.render(setup)));
    el.enable_item_timings();
    el.elab_source(source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let rows = el.take_item_timings();
    stats::disable();
    if !refusal.is_empty() {
        assert!(el.elab_source(refusal).is_err(), "false equation was accepted");
    }
    rows.into_iter().find(|r| r.item == item).expect("measured declaration")
}

fn payload(width: usize) -> String {
    let fields = (0..width).map(|i| format!("f{i}: Nat")).collect::<Vec<_>>().join(", ");
    format!("inductive Payload {{ P0, P1({fields}), P2 }}")
}

/// Dispatching on a port id should not normalize the result's vector at
/// every successor. The arms remain neutral so no bit computation is timed.
#[test]
fn valuation_lookup_case_step_cost() {
    let mut baseline = None;
    for width in [1, 8, 64] {
        let counts: Vec<_> = [0, 8, 16, 32].into_iter().map(|depth| {
            let mut body = "values(width, 7)".to_string();
            for i in (0..=depth).rev() {
                let id = if i == 0 { "id".to_string() } else { format!("id_{i}") };
                let port = if i == depth { 7 } else { 0 };
                body = format!("match {id} {{ Zero => values(width, {port}), Succ(id_{}) => {body} }}", i + 1);
            }
            measure(
                &format!("inductive Bit {{ Off, On }}\nrecord Word(n: Nat) {{ bits: [Bit; n] }}\nfn lookup(values: (width: Nat) -> Nat -> Word(width)) -> (width: Nat) -> Nat -> Word(width) {{ λ width id => {body} }}"),
                &format!("theorem probe(values: (width: Nat) -> Nat -> Word(width)): lookup(values)({width}, {depth}) = values({width}, 7) {{ refl }}"),
                "probe", &format!("theorem wrong(values: (width: Nat) -> Nat -> Word(width)): lookup(values)({width}, {depth}) = values({width}, 9) {{ refl }}"),
            )
        }).collect();
        eprintln!("lookup width {width}, ids 0/8/16/32: {counts:?}");
        assert!(counts[0] > 0);
        for (i, depth) in [0, 8, 16, 32].into_iter().enumerate() {
            assert_eq!(counts[i] - counts[0], 2 * depth,
                "case dispatch must cost two steps per successor: {counts:?}");
        }
        if let Some(ref first) = baseline {
            assert_eq!(&counts, first, "result width leaked into dispatch");
        } else {
            baseline = Some(counts);
        }
    }
}

#[test]
fn named_recursive_telescope_cost_does_not_follow_payload_width() {
    let counts: Vec<_> = [2, 8, 32].into_iter().map(|width| {
        let setup = format!("{}\ninductive Box<A> {{ BNil, BCons(a: A, r: Box<A>) }}", payload(width));
        measure(&setup,
            "fn probe(b: Box<Payload>) -> Nat { match b { BNil => 0, BCons(a, r) => Succ(probe(r)) } }",
            "probe", "")
    }).collect();
    eprintln!("telescope payload widths 2/8/32: {counts:?}");
    assert!(counts.iter().all(|&n| n > 0));
    assert!(counts[2] <= 2 * counts[0], "payload growth leaked into annotations: {counts:?}");
}

#[test]
fn indexed_dependent_copy_cost_is_bounded_across_payload_widths() {
    let counts: Vec<_> = [2, 8, 32].into_iter().map(|width| {
        let setup = format!("{}\ninductive Shape {{ Leaf, Unary(p: Payload, s: Shape), Fork(l: Shape, r: Shape) }}", payload(width));
        measure(&setup, "
inductive Family<A> : (s: Shape) -> Type {
    FLeaf(x: A): Family<A>(Leaf),
    FUnary(p: Payload, s: Shape, xs: Family<A>(s)): Family<A>(Unary(p, s)),
    FFork(l: Shape, r: Shape, x: Family<A>(l), y: Family<A>(r)): Family<A>(Fork(l, r)),
}

fn predecessor<A>(s: Shape, x: Family<A>(s)) -> Shape {
    match x { FLeaf(a) => Leaf, FUnary(p, t, y) => t, FFork(l, r, x, y) => l }
}
fn copy<A>(s: Shape, x: Family<A>(s)) -> Family<A>(s) {
    match x {
        FLeaf(a) => FLeaf(a),
        FUnary(p, t, y) => FUnary(p, t, copy(t, y)),
        FFork(l, r, x, y) => FFork(l, r, copy(l, x), copy(r, y)),
    }
}
theorem copy_open<A>(a: A): copy<A>(Leaf, FLeaf<A>(a)) = FLeaf(a) { refl }
theorem copy_literal(): copy<Nat>(Unary(P0, Leaf), FUnary<Nat>(P0, Leaf, FLeaf<Nat>(7))) = FUnary(P0, Leaf, FLeaf(7)) { refl }
theorem predecessor_literal(): predecessor<Nat>(Unary(P0, Leaf), FUnary<Nat>(P0, Leaf, FLeaf<Nat>(7))) = Leaf { refl }
", "copy", "theorem copy_wrong(): copy<Nat>(Leaf, FLeaf<Nat>(7)) = FLeaf<Nat>(8) { refl }")
    }).collect();
    eprintln!("indexed payload widths 2/8/32: {counts:?}");
    assert!(counts.iter().all(|&n| n > 0));
    // The indexed family still carries structural payloads: a flat-cost
    // promise would be false. Bound the measured linear trend with margin.
    assert!(counts[2] <= 4 * counts[0], "indexed payload cost growth: {counts:?}");
}

#[test]
fn projection_chains_check_after_neutral_and_computed_substitution() {
    for depth in [1, 2, 3] {
        let ty = format!("{}A{}", "Cell<".repeat(depth), ">".repeat(depth));
        let path = ".value".repeat(depth);
        let rebuilt = format!("{}c{path}{}", "Cell(".repeat(depth), ")".repeat(depth));
        let setup = format!("
record Cell<A> {{ value: A }}
fn rebuild<A>(c: {ty}) -> {ty} {{ {rebuilt} }}
fn repeat<A>(n: Nat, c: {ty}) -> {ty} {{
    match n {{ Zero => c, Succ(k) => rebuild(repeat(k, c)) }}
}}
record Claim<A>(seed: {ty}) {{ out: {ty}, same: out{path} = seed{path} }}
");
        let counts: Vec<_> = [None, Some(0), Some(1), Some(2), Some(4), Some(8)].into_iter().map(|steps| {
            let receiver = steps.map_or_else(|| "seed".to_owned(), |n| format!("repeat({n}, seed)"));
            let literal = format!("{}7{}", "Cell(".repeat(depth), ")".repeat(depth));
            let source = format!("
fn make<A>(seed: {ty}) -> Claim<A>(seed) {{ Claim({receiver}, refl) }}
theorem read<A>(seed: {ty}): make(seed).out{path} = seed{path} {{ make(seed).same }}
");
            let source = format!("{source}\ntheorem literal(): make({literal}).out{path} = 7 {{ refl }}");
            let refusal = format!("theorem wrong(): make({literal}).out{path} = 8 {{ refl }}");
            measure(&setup, &source, "make", &refusal)
        }).collect();
        eprintln!("projection chain {depth}, bare receiver, repeats 0/1/2/4/8: {counts:?}");
        assert!(counts.iter().all(|&n| n > 0));
        // Doubling rebuilding steps must stay within a generous growth bound.
        // Leave room for changes in fixed kernel-checking overhead.
        assert!(counts[5] <= 3 * counts[4], "projection cost growth: {counts:?}");
    }
}

/// A visible conjunction spine must not turn into a chain of deferred
/// selections whose prefixes are normalized again at every projection, or
/// have each inferred suffix respelled by recursive instance matching.
#[test]
fn conjunction_projection_chain_cost() {
    for alias in [false, true] {
        let rows: Vec<_> = [8, 16, 32].into_iter().map(|depth| {
            let ty = format!("{}A{}", "And<A, ".repeat(depth), ">".repeat(depth));
            let path = ".right".repeat(depth);
            let body = if alias { format!("let p = identity(facts); p{path}") } else { format!("facts{path}") };
            measure_item(
                "record And<P, Q> { left: P, right: Q }\ntheorem identity<A>(a: A): A { a }",
                &format!("fn probe<A>(facts: {ty}) -> A {{ {body} }}"),
                "probe", "",
            )
        }).collect();
        let counts: Vec<_> = rows.iter().map(|r| r.kernel.eval_steps).collect();
        let matches: Vec<_> = rows.iter().map(|r| r.counters[stats::Counter::InstanceMatchCalls as usize]).collect();
        eprintln!("conjunction depths 8/16/32, alias={alias}: {counts:?}");
        eprintln!("conjunction instance matches, alias={alias}: {matches:?}");
        assert!(counts.iter().all(|&n| n > 0));
        assert!(counts[2] <= 3 * counts[1], "projection prefix replay returned: {counts:?}");
        assert!(matches.iter().all(|&n| n > 0));
        assert!(matches[2] <= 3 * matches[1], "inferred suffix respelling returned: {matches:?}");
        for row in &rows {
            assert!(row.counters[stats::Counter::ProjectionStructural as usize] > 0,
                "the structural fallback must be exercised");
            if alias {
                assert_eq!(row.counters[stats::Counter::ProjectionNamed as usize], 0,
                    "opaque aliases must retain the receiver boundary");
            }
        }
    }
}

#[test]
fn conjunction_projection_chains_preserve_fields_and_dependencies() {
    let mut el = Elaborator::with_prelude().expect("prelude");
    let source = "
record And<P, Q> { left: P, right: Q }
record Witness<A> { value: A, same: value = value }
theorem identity<A>(a: A): A { a }
fn read<A, B>(facts: And<B, And<B, Witness<A>>>) -> A { facts.right.right.value }
theorem evidence<A, B>(facts: And<B, And<B, Witness<A>>>):
    facts.right.right.value = facts.right.right.value { facts.right.right.same }
fn aliased<A, B>(facts: And<B, And<B, A>>) -> A {
    let p = identity(facts); p.right.right
}
theorem literal(): read(And(1, And(2, Witness(7, refl)))) = 7 { refl }
theorem neutral<A>(a: A): read(And(1, And(2, Witness(a, refl)))) = a { refl }
theorem left(): And(1, And(2, 3)).right.left = 2 { refl }
";
    el.elab_source(source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    assert!(el.elab_source("theorem wrong(): read(And(1, And(2, Witness(7, refl)))) = 8 { refl }").is_err());
    assert!(el.elab_source("fn wrong_type<A, B>(facts: And<B, And<B, A>>) -> B { facts.right.right }").is_err());
}
