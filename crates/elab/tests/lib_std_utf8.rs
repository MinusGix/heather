//! `lib/std/text/utf8.hthr` — UTF-8 as the first *representation* of
//! `String`, and the `Utf8` byte-level spec type beside it
//! (docs/string-char-design.md §5): the refusals that need the checker. The
//! encoder at every byte width, the strict decoder at each rejection Rust's
//! `from_utf8` makes, every law at a literal and at a neutral string, and the
//! `¬` theorems for the wrong values are `lib/_tests/std/text/utf8_tests.hthr`,
//! which the whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4).
//!
//! What is left: laws cited at statements they do not prove, and
//! incompleteness pins (§4.6) showing the open-string laws are the lemmas'
//! work and not conversion's.

use heather_elab::SemanticImage;
use std::sync::OnceLock;

use crate::support::{self, Refusal};

static BASE: OnceLock<SemanticImage> = OnceLock::new();

/// The first nine entries are `semantic_x86_warmup.rs`'s list in its order,
/// so this target reads the images that warmup wrote instead of elaborating
/// `bitvec` again per case.
const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec/bitvec.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("utf8", include_str!("../../../lib/std/text/utf8.hthr")),
];

const PREAMBLE: &str = concat!(
    "import logic;\nimport bool;\nimport nat;\nimport option;\nimport pair;\n",
    "import list;\nimport bitvec;\nimport char;\nimport string;\nimport utf8;\n",
);

fn refused(body: &str, why: Refusal) {
    let mut e = BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator();
    support::assert_refused(&mut e, "probe", &format!("{PREAMBLE}{body}"), why);
}

/// Incompleteness pins: the round trip, the re-encoding and the head-then-tail
/// step at open arguments are not conversions, so the lemmas
/// (`decode_encode`, `encode_decode`, `decode_step`) do the work. The last
/// is a wrong tail; the right one is `uf3` in the probes.
#[test]
fn the_open_laws_are_not_refl() {
    refused("theorem bad(s: String): utf8::decode(utf8::encode(s)) = Some(s) { refl }\n", Refusal::Kernel);
    refused(
        "theorem bad(bs: List<BitVec(8)>, s: String, p: utf8::decode(bs) = Some(s)): utf8::encode(s) = bs { refl }\n",
        Refusal::Kernel,
    );
    refused(
        r#"
theorem bad(q: BitVec(4), r, s, u: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t))))
        = push_char(decode_seq(C3, lead3_byte(q),
              Cons(cont_byte(r), Cons(cont_byte(s), t))), decode(Cons(cont_byte(u), t)))
{ refl }
"#,
        Refusal::Kernel,
    );
}

/// Injectivity needs a real premise: two arbitrary strings have no common
/// encoding by `refl`. The section is stated about the value it is given.
#[test]
fn laws_need_their_premises() {
    refused("theorem bad(s, t: String): s = t { utf8::encode_injective(s, t, refl) }\n", Refusal::Kernel);
    refused(
        "theorem bad(u: utf8::Utf8, s: String): utf8::ofString(s) = u { utf8::ofString_toString(u) }\n",
        Refusal::Mismatch,
    );
}
