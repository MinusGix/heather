mod support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec.hthr")),
];

#[test]
fn bounded_readonly_semantics_checks() {
    let mut elab = support::semantic_test_base(MODULES);
    let source = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
}

#[test]
fn readonly_loop_source_reflection_checks() {
    use heather_elab::function_ir_source::{reflect_elaborated_readonly_loop, generate_readonly_loop_certificate};
    let mut elab = support::semantic_test_base(MODULES);
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let extra = r#"
import function_ir_loop; import readonly_loops; import bitvec; import bool; import nat;
fn unchanged_body(needle: BitVec(8), cursor: Nat, byte: BitVec(8), count: Nat) → LoopStep<Nat> { Continue(count) }
fn changed_source(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, count: Nat) → LoopOutcome<Nat> {
    bounded_readonly<Nat>(buffer, needle, budget, cursor, count, unchanged_body)
}
fn swapped(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, count: Nat) → LoopOutcome<Nat> {
    bounded_readonly<Nat>(buffer, needle, cursor, budget, count, count_body)
}
fn closure(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, count: Nat) → LoopOutcome<Nat> {
    bounded_readonly<Nat>(buffer, needle, budget, cursor, count, λ needle index byte count => Continue(count))
}
fn fake_bounded_readonly(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, count: Nat) → LoopOutcome<Nat> { Exhausted(cursor, count) }
fn wrong_operation(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, count: Nat) → LoopOutcome<Nat> {
    fake_bounded_readonly(buffer, needle, budget, cursor, count)
}
"#;
    elab.elab_module_source("loop_controls", extra).unwrap_or_else(|e| panic!("{}", e.render(extra)));
    for name in ["swapped", "closure", "wrong_operation", "count_body"] {
        assert!(reflect_elaborated_readonly_loop(&elab, name).is_err(), "must decline {name}");
    }
    for name in ["count_occurrences", "first_match"] {
        let reflected = reflect_elaborated_readonly_loop(&elab, name).unwrap();
        assert_eq!(reflected.source_name, format!("readonly_loops::{name}"));
        let certificate = generate_readonly_loop_certificate(name, &reflected);
        elab.elab_module_source(&format!("{name}_certificate"), &certificate)
            .unwrap_or_else(|e| panic!("{}", e.render(&certificate)));
    }
    let image = elab.semantic_image();
    let reflected = reflect_elaborated_readonly_loop(&elab, "count_occurrences").unwrap();
    let mut stale = reflected.clone();
    stale.source_name = "loop_controls::changed_source".into();
    reject(&image, "stale_source", &generate_readonly_loop_certificate("stale", &stale));
    stale = reflected.clone();
    stale.body_name = "loop_controls::unchanged_body".into();
    reject(&image, "wrong_body", &generate_readonly_loop_certificate("stale", &stale));
    let certificate = generate_readonly_loop_certificate("swapped", &reflected);
    let mutant = certificate.replace("readonly_loops::count_occurrences(buffer, needle, budget, cursor, carry)",
        "readonly_loops::count_occurrences(buffer, needle, cursor, budget, carry)");
    assert_ne!(mutant, certificate);
    reject(&image, "wrong_binding", &mutant);

}

const LAWS: &str = r#"
import function_ir_loop;
import bitvec;
import bool;
import nat;
import option;
import logic;

// Open carry type and source read function: no permission can be smuggled in
// by reducing a concrete byte array or by specializing the state to a word.
theorem empty_no_read<C>(budget: Nat, region: ReadonlyLoop<C>, source, base: Nat,
    read: Nat → Option<BitVec(8)>, needle: BitVec(8), carry: C):
    loop_run(budget, region, ReadonlyBytes(source, base, 0, read), needle, 0, carry) = End(0, budget, carry) {
    match budget { Zero => refl, Succ(rest) => refl }
}
theorem empty_readable<C>(budget: Nat, region: ReadonlyLoop<C>, source, base: Nat,
    read: Nat → Option<BitVec(8)>, needle: BitVec(8), carry: C):
    LoopReadable(budget, region, ReadonlyBytes(source, base, 0, read), needle, 0, carry) {
    match budget { Zero => trivial, Succ(rest) => trivial }
}
theorem exhausted_no_read<C>(region: ReadonlyLoop<C>, source, base, length: Nat,
    read: Nat → Option<BitVec(8)>, needle: BitVec(8), carry: C):
    loop_run(0, region, ReadonlyBytes(source, base, Succ(length), read), needle, 0, carry) = Exhausted(0, carry) { refl }
theorem exhausted_readable<C>(region: ReadonlyLoop<C>, source, base, length: Nat,
    read: Nat → Option<BitVec(8)>, needle: BitVec(8), carry: C):
    LoopReadable(0, region, ReadonlyBytes(source, base, Succ(length), read), needle, 0, carry) { trivial }
theorem denied_preserves<C>(region: ReadonlyLoop<C>, source, base, length, rest: Nat,
    needle: BitVec(8), carry: C):
    loop_run(Succ(rest), region, ReadonlyBytes(source, base, Succ(length), λ address => None), needle, 0, carry) = Denied(0, Succ(rest), carry) { refl }
theorem early_consumes<C>(source, length, rest: Nat, needle, byte: BitVec(8), carry, result: C):
    loop_run(Succ(rest), ReadonlyLoop<C>(λ needle index byte carry => Break(result)),
        ReadonlyBytes(source, 0, Succ(length), λ address => match address { Zero => Some(byte), Succ(_) => None }), needle, 0, carry) = Early(1, rest, result) { refl }
theorem early_needs_no_next_byte<C>(source, length, rest: Nat, needle, byte: BitVec(8), carry, result: C):
    LoopReadable(Succ(rest), ReadonlyLoop<C>(λ needle index byte carry => Break(result)),
        ReadonlyBytes(source, 0, Succ(length), λ address => match address { Zero => Some(byte), Succ(_) => None }), needle, 0, carry) { trivial }
theorem continue_binds_next<C>(source, rest: Nat, needle, byte: BitVec(8), carry, next: C):
    loop_run(Succ(rest), ReadonlyLoop<C>(λ needle index byte carry => Continue(next)),
        ReadonlyBytes(source, 0, 1, λ address => Some(byte)), needle, 0, carry) =
    loop_run(rest, ReadonlyLoop<C>(λ needle index byte carry => Continue(next)),
        ReadonlyBytes(source, 0, 1, λ address => Some(byte)), needle, 1, next) { refl }
theorem decode_counter(width: Nat, word: BitVec(width)):
    LoopWord(width, word, @bitvec::BitVec::toNat(width, word)) { refl }
theorem representable_end(): LoopAddressBound(3, ReadonlyBytes(0, 1, 6, λ address => None)) { trivial }

"#;

fn reject(image: &heather_elab::SemanticImage, name: &str, text: &str) {
    heather_syntax::parse_file(text).expect("negative control must parse");
    let error = image.elaborator().elab_module_source(name, text).expect_err("dishonest contract must fail");
    let message = error.render(text);
    assert!(!message.contains("unknown") && !message.contains("not in scope"), "control failed on missing name: {message}");
}

#[test]
fn readonly_loop_open_contracts_and_rejections() {
    let mut elab = support::semantic_test_base(MODULES);
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    elab.elab_module_source("loop_laws", LAWS).unwrap_or_else(|e| panic!("{}", e.render(LAWS)));
    let image = elab.semantic_image();
    for (name, original, changed) in [
        ("end_before_budget", "End(0, budget, carry)", "Exhausted(0, carry)"),
        ("wrong_budget", "Early(1, rest, result)", "Early(1, Succ(rest), result)"),
        ("wrong_cursor", "Early(1, rest, result)", "Early(0, rest, result)"),
        ("wrong_carry", "needle, 1, next) { refl }", "needle, 1, carry) { refl }"),
        ("wrapping_end", "ReadonlyBytes(0, 1, 6,", "ReadonlyBytes(0, 1, 7,"),
        ("wrong_word_relation", "word, @bitvec::BitVec::toNat(width, word))", "word, Succ(@bitvec::BitVec::toNat(width, word)))"),
    ] {
        let mutant = LAWS.replace(original, changed);
        assert_ne!(mutant, LAWS);
        reject(&image, name, &mutant);
    }
    reject(&image, "unguarded_read", r#"
import function_ir_loop; import bitvec; import bool; import option; import nat; import logic;
theorem unguarded_read<C>(region: ReadonlyLoop<C>, needle: BitVec(8), carry: C):
    LoopReadable(1, region, ReadonlyBytes(0, 0, 1, λ address => None), needle, 0, carry) { trivial }
"#);
    reject(&image, "bad_cursor_bound", r#"
import function_ir_loop; import nat; import option; import logic;
theorem bad_cursor_bound(): LoopBounds(ReadonlyBytes(0, 0, 0, λ address => None), 1) { trivial }
"#);
}

#[test]
fn readonly_loop_two_clients_compute() {
    let mut elab = support::semantic_test_base(MODULES);
    let model = include_str!("../../../lib/function_ir_loop.hthr");
    elab.elab_module_source("function_ir_loop", model).unwrap_or_else(|e| panic!("{}", e.render(model)));
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    let checks = r#"
import function_ir_loop; import readonly_loops; import bitvec; import bool; import nat; import option;
fn sample() → ReadonlyBytes {
    ReadonlyBytes(42, 7, 3, λ address => match nat::Nat::sub(address, 7) {
        Zero => Some(@bitvec::BitVec::ofNat(8, 0)),
        Succ(rest) => match rest {
            Zero => Some(@bitvec::BitVec::ofNat(8, 1)),
            Succ(rest) => match rest { Zero => Some(@bitvec::BitVec::ofNat(8, 0)), Succ(_) => None },
        },
    })
}
theorem count_all(initial: Nat): count_occurrences(sample(), @bitvec::BitVec::ofNat(8, 0), 3, 0, initial) = End(3, 0, Succ(Succ(initial))) { refl }
theorem count_budget(initial: Nat): count_occurrences(sample(), @bitvec::BitVec::ofNat(8, 0), 1, 0, initial) = Exhausted(1, Succ(initial)) { refl }
theorem count_extra_budget(initial: Nat): count_occurrences(sample(), @bitvec::BitVec::ofNat(8, 0), 5, 0, initial) = End(3, 2, Succ(Succ(initial))) { refl }
theorem search_first(): first_match(sample(), @bitvec::BitVec::ofNat(8, 0), 3, 0, False) = Early(1, 2, True) { refl }
theorem search_second(): first_match(sample(), @bitvec::BitVec::ofNat(8, 1), 3, 0, False) = Early(2, 1, True) { refl }
theorem search_missing(): first_match(sample(), @bitvec::BitVec::ofNat(8, 2), 3, 0, False) = End(3, 0, False) { refl }
theorem search_last_budget(): first_match(sample(), @bitvec::BitVec::ofNat(8, 1), 2, 0, False) = Early(2, 0, True) { refl }
theorem search_resumed(): first_match(sample(), @bitvec::BitVec::ofNat(8, 0), 2, 1, False) = Early(3, 0, True) { refl }
"#;
    elab.elab_module_source("client_checks", checks).unwrap_or_else(|e| panic!("{}", e.render(checks)));
}
