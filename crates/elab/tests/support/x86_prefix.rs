//! The x86 prefix the native tests stand on: the core library, the ISA model
//! and its blocks, and FunctionIR, as one ordered module list.
//!
//! Generated from the imports: edit the roots on the marker, then run
//! `scripts/lib-closures --fix`.

// lib-closure: x86_64_block function_ir
pub(crate) const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../../lib/std/core/bool.hthr")),
    ("option", include_str!("../../../../lib/std/core/option.hthr")),
    ("nat", include_str!("../../../../lib/std/num/nat.hthr")),
    ("pair", include_str!("../../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../../lib/std/num/int.hthr")),
    ("bitvec", include_str!("../../../../lib/std/bitvec/bitvec.hthr")),
    ("location", include_str!("../../../../lib/std/machine/location.hthr")),
    ("certified_lookup", include_str!("../../../../lib/std/data/certified_lookup.hthr")),
    ("x86_64", include_str!("../../../../lib/std/arch/x86_64/x86_64.hthr")),
    ("x86_64_block", include_str!("../../../../lib/std/arch/x86_64/x86_64_block.hthr")),
    ("function_ir", include_str!("../../../../lib/native/function_ir/function_ir.hthr")),
];
