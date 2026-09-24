use crate::common;
use heather_elab::function_ir_source::generate_elaborated_typed_x86;
use heather_elab::function_ir_x86_lower::{Gpr, Placements};

fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("x86_64_structured_block", include_str!("../../../lib/std/arch/x86_64/structured_block.hthr")),
        ("x86_64_data_read", include_str!("../../../lib/std/arch/x86_64/data_read.hthr")),
        ("x86_64_access_code", include_str!("../../../lib/std/arch/x86_64/access_code.hthr")),
        ("x86_64_access_memory", include_str!("../../../lib/std/arch/x86_64/access_memory.hthr")),
        ("bitvec_nat", include_str!("../../../lib/std/bitvec/nat.hthr")),
        ("function_ir_loop", include_str!("../../../lib/function_ir_loop.hthr")),
        ("function_ir_loop_x86", include_str!("../../../lib/function_ir_loop_x86.hthr")),
        ("function_ir_loop_trace", include_str!("../../../lib/function_ir_loop_trace.hthr")),
    ] { elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source))); }
    elab
}

// The loop's own steps go through the ordinary typed generator: no loop
// instruction is templated in Rust (docs/native-bounded-loops-design.md §5).
#[test]
fn loop_steps_select_through_the_shared_generator() {
    let mut elab = checker();
    elab.elab_module_source("loop_steps", "import function_ir_loop_x86; import bitvec; import bool;").unwrap();
    let mut text = String::new();
    for (prefix, source, inputs, temporaries, output) in [
        ("guard", "function_ir_loop_x86::loop_guard", vec![(0, Gpr::Rsi), (1, Gpr::Rdx), (2, Gpr::R12)],
            vec![Gpr::R13, Gpr::Rax, Gpr::Rbx, Gpr::R10, Gpr::R14], (3, Gpr::R13)),
        ("next_cursor", "function_ir_loop_x86::loop_next_cursor", vec![(0, Gpr::Rsi)], vec![Gpr::R10, Gpr::Rax], (1, Gpr::R10)),
        ("next_budget", "function_ir_loop_x86::loop_next_budget", vec![(0, Gpr::R12)], vec![Gpr::R14, Gpr::Rax], (1, Gpr::R14)),
        ("copy", "function_ir_loop_x86::loop_copy", vec![(0, Gpr::R10)], vec![Gpr::Rsi], (1, Gpr::Rsi)),
    ] {
        let emission = generate_elaborated_typed_x86(&elab, prefix, source, &Placements::from_iter(inputs), &temporaries,
            &Placements::from([output])).unwrap_or_else(|e| panic!("{prefix}: {e:?}"));
        text.push_str(&emission.text);
        text.push('\n');
    }
    let text = stitch(&text);
    elab.elab_module_source("loop_step_certificates", &text).unwrap_or_else(|e| panic!("{}", e.render(&text)));
}

// Controls for the word bridges: each must refuse the wrapping or reversed case.
#[test]
fn loop_word_lemmas_refuse_what_they_must() {
    let mut elab = checker();
    let imports = "import function_ir_loop; import function_ir_loop_x86; import function_ir_loop_trace; import bitvec; import bool; import nat; import logic;";
    let positive = format!("{imports} theorem guard_ends(c, l, b: BitVec(64)): function_ir_loop_x86::loop_guard(c, l, b) = function_ir_loop_x86::loop_guard(c, l, b) {{ refl }}");
    elab.elab_module_source("positive", &positive).unwrap_or_else(|e| panic!("{}", e.render(&positive)));
    for (name, body) in [
        // An empty budget has no predecessor to decrement to.
        ("budget_wrap", "theorem bad(word: BitVec(64), placed: LoopWord(64, word, 0)): LoopWord(64, function_ir_loop_x86::loop_next_budget(word), 0) { loop_budget_decrement(word, 0, placed) }"),
        // The guard never continues at the end of input, whatever the budget.
        ("guard_polarity", "theorem bad(cw, lw, bw: BitVec(64), c, l, b: Nat, pc: LoopWord(64, cw, c), pl: LoopWord(64, lw, l), pb: LoopWord(64, bw, b), ended: nat::Nat::leb(l, c) = True): function_ir_loop_x86::loop_guard(cw, lw, bw) = True { trans(loop_guard_word(cw, lw, bw, c, l, b, pc, pl, pb), j(sym(ended), λ e _ => match e { True => False, False => nat::Nat::leb(1, b) } = True, refl)) }"),
        // 2^48 is not a low-canonical bound.
        ("canonical_bound", "theorem bad(buffer: ReadonlyBytes, c: Nat, address: BitVec(64), placed: LoopWord(64, address, buffer.base + c), open: nat::Nat::leb(buffer.length, c) = False, low: buffer.base + buffer.length <= nat::Nat::pow(2, 48)): @bitvec::BitVec::drop_low(47, 17, address) = @bitvec::BitVec::zero(17) { loop_address_canonical(buffer, c, address, placed, open, low) }"),
    ] {
        let text = format!("{imports} {body}");
        heather_syntax::parse_file(&text).unwrap();
        let error = elab.semantic_image().elaborator().elab_module_source(name, &text).expect_err(name).render(&text);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}

fn stitch(text: &str) -> String {
    let mut imports = std::collections::BTreeSet::new();
    let mut body = String::new();
    for line in text.lines() {
        if line.starts_with("import ") { imports.insert(line); }
        else { body.push_str(line); body.push('\n'); }
    }
    format!("{}\n{body}", imports.into_iter().collect::<Vec<_>>().join("\n"))
}
