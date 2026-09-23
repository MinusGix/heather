#[path = "function_ir_x86.rs"]
mod common;

#[test]
fn bounds_models_check() {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("x86_64_structured_block", include_str!("../../../lib/std/arch/x86_64/structured_block.hthr")),
        ("x86_64_data_read", include_str!("../../../lib/std/arch/x86_64/data_read.hthr")),
        ("x86_64_access_code", include_str!("../../../lib/std/arch/x86_64/access_code.hthr")),
        ("x86_64_access_memory", include_str!("../../../lib/std/arch/x86_64/access_memory.hthr")),
        ("bitvec_nat", include_str!("../../../lib/std/bitvec/nat.hthr")),
        ("function_ir_loop", include_str!("../../../lib/function_ir_loop.hthr")),
        ("function_ir_loop_x86", include_str!("../../../lib/function_ir_loop_x86.hthr")),
    ] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    }
}

#[test]
fn bounds_refuse_wrap_and_reversed_selection() {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("bitvec_nat", include_str!("../../../lib/std/bitvec/nat.hthr")),
    ] { elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source))); }
    let positive = "import bitvec_nat; import bitvec; import nat; import bool; theorem open_sum(n: Nat, a, b: BitVec(n), bounded: @bitvec::BitVec::toNat(n, a) + @bitvec::BitVec::toNat(n, b) < nat::Nat::pow(2, n)): @bitvec::BitVec::toNat(n, @bitvec::BitVec::add(n, a, b)) = @bitvec::BitVec::toNat(n, a) + @bitvec::BitVec::toNat(n, b) { toNat_add(n, a, b, bounded) } theorem zero_width(): @bitvec::BitVec::toNat(0, @bitvec::BitVec::add(0, @bitvec::BitVec::zero(0), @bitvec::BitVec::zero(0))) = 0 { toNat_add(0, @bitvec::BitVec::zero(0), @bitvec::BitVec::zero(0), trivial) } theorem last_byte(): @bitvec::BitVec::toNat(8, @bitvec::BitVec::add(8, @bitvec::BitVec::ofNat(8, 254), @bitvec::BitVec::ofNat(8, 1))) = 255 { toNat_add(8, @bitvec::BitVec::ofNat(8, 254), @bitvec::BitVec::ofNat(8, 1), trivial) }";
    elab.elab_module_source("positive", positive).unwrap_or_else(|e| panic!("{}", e.render(positive)));
    for (name, body) in [
        ("wrap", "theorem bad(): @bitvec::BitVec::toNat(8, @bitvec::BitVec::add(8, @bitvec::BitVec::ofNat(8, 255), @bitvec::BitVec::ofNat(8, 1))) = 256 { toNat_add(8, @bitvec::BitVec::ofNat(8, 255), @bitvec::BitVec::ofNat(8, 1), trivial) }"),
        ("reversed", "theorem bad(): @bitvec::BitVec::unsigned_lt_bit(8, @bitvec::BitVec::ofNat(8, 0), @bitvec::BitVec::ofNat(8, 1)) = nat::Nat::leb(1, 0) { refl }"),
        ("signed", "theorem bad(): @bitvec::BitVec::signed_lt_bit(8, @bitvec::BitVec::ofNat(8, 128), @bitvec::BitVec::ofNat(8, 1)) = @bitvec::BitVec::unsigned_lt_bit(8, @bitvec::BitVec::ofNat(8, 128), @bitvec::BitVec::ofNat(8, 1)) { refl }"),
    ] {
        let text = format!("import bitvec_nat; import bitvec; import nat; import bool; {body}");
        assert!(heather_syntax::parse_file(&text).is_ok());
        let error = elab.semantic_image().elaborator().elab_module_source(name, &text).expect_err(name).render(&text);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{error}");
    }
}
