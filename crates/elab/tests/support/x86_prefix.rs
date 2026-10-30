//! The x86 prefix the native tests stand on: the core library, the ISA model
//! and its blocks, and FunctionIR, as one ordered module list.

const LOGIC: &str = include_str!("../../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../../lib/std/num/int.hthr");
const BITVEC: &str = include_str!("../../../../lib/std/bitvec/bitvec.hthr");
const RELATION: &str = include_str!("../../../../lib/std/relation/relation.hthr");
const LOCATION: &str = include_str!("../../../../lib/std/machine/location.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../../lib/std/data/certified_lookup.hthr");
const X86_64: &str = include_str!("../../../../lib/std/arch/x86_64/x86_64.hthr");
const X86_64_BLOCK: &str = include_str!("../../../../lib/std/arch/x86_64/x86_64_block.hthr");
const FUNCTION_IR: &str = include_str!("../../../../lib/native/function_ir/function_ir.hthr");

pub(crate) const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("morphism", include_str!("../../../../lib/std/algebra/morphism.hthr")),
    ("int", INT),
    ("bitvec", BITVEC),
    ("relation", RELATION),
    ("relation_props", include_str!("../../../../lib/std/relation/relation_props.hthr")),
    ("location", LOCATION),
    ("certified_lookup", CERTIFIED_LOOKUP),
    ("x86_64", X86_64),
    ("x86_64_block", X86_64_BLOCK),
    ("function_ir", FUNCTION_IR),
];
