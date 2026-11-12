use crate::support;

// FunctionIR's straight-line regions lowered by a Heather function proved
// correct once (issues/function-ir-verified-lowering.md, round 1). The
// module holds the lowering and its theorem; the fixture lowers add64, sum4,
// mix and a comparison by evaluation, instantiates the theorem for each, and
// keeps the refusal controls (a clobbering placement, a narrow port, a narrow
// signed comparison) beside a comparison placed over its own operand and a
// region that computes at 32 bits between 64-bit ports.
const FUNCTION_IR_LOWER: &str = include_str!("../../../lib/native/function_ir/function_ir_lower.hthr");
const EXAMPLES: &str = include_str!("fixtures/function_ir_lower_examples.hthr");

// The x86 prefix up to the block layer, then FunctionIR and what a block
// leaves (x86_64_kept): what the lowering imports, and nothing B2 burns.
const PREFIX: &[&str] = &[
    "logic", "bool", "nat", "option", "pair", "list", "relation", "relation_props", "algebra_rel",
    "algebra", "morphism", "int", "bitvec", "location", "certified_lookup", "x86_64", "x86_64_block",
    "function_ir",
];

#[test]
fn verified_lowering_checks_and_lowers_the_examples() {
    let mut modules: Vec<(&str, &str)> = PREFIX
        .iter()
        .map(|name| {
            *crate::common::MODULES
                .iter()
                .find(|(module, _)| module == name)
                .unwrap_or_else(|| panic!("{name} is in the FunctionIR x86 prefix"))
        })
        .collect();
    modules.push(("x86_64_kept", include_str!("../../../lib/std/arch/x86_64/x86_64_kept.hthr")));
    // What the lowering's narrow widths read.
    modules.push(("bitvec_nat", include_str!("../../../lib/std/bitvec/bitvec_nat.hthr")));
    modules.push(("bitvec_resize", include_str!("../../../lib/std/bitvec/bitvec_resize.hthr")));
    modules.push(("function_ir_lower", FUNCTION_IR_LOWER));
    let mut elaborator = support::semantic_test_base(&modules);
    if let Err(error) = elaborator.elab_module_source("function_ir_lower_examples", EXAMPLES) {
        panic!("the lowered examples did not check: {}", error.render(EXAMPLES));
    }
}
