//! `lib/std/certified_lookup.hthr` — generic proof-carrying finite lookup.

use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../lib/std/certified_lookup.hthr");

#[test]
fn certified_lookup_checks_and_computes() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("certified_lookup", CERTIFIED_LOOKUP),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {}", err.render(src));
        }
    }

    let src = r#"
import certified_lookup;
import nat;
import list;
import option;

fn IsSuccess(key, value: Nat) → Type { key = value }

fn rows() → List<CertifiedEntry<Nat, Nat>(IsSuccess)> {
    Cons(CertifiedEntry(key := 3, value := 3, valid := refl),
        Cons(CertifiedEntry(key := 7, value := 7, valid := refl), Nil))
}

theorem retain_valid<K, V>(Valid: K → V → Type, {key: K}, {value: V},
    valid: Valid(key, value)): Valid(key, value)
{
    valid
}

theorem field_type_infers_hidden_values<K, V>(Valid: K → V → Type,
    entry: CertifiedEntry<K, V>(Valid)): Valid(entry.key, entry.value)
{
    retain_valid(Valid, entry.valid)
}

theorem finds_head():
    lookup(IsSuccess, nat::Nat::eq_dec, 3, rows()) = Some(3)
{}

theorem finds_tail():
    lookup(IsSuccess, nat::Nat::eq_dec, 7, rows()) = Some(7)
{}

theorem misses(): lookup(IsSuccess, nat::Nat::eq_dec, 5, rows()) = None {}

theorem found_is_valid(value: Nat,
    success: lookup(IsSuccess, nat::Nat::eq_dec, 7, rows()) = Some(value)):
    IsSuccess(7, value)
{
    lookup_sound(IsSuccess, nat::Nat::eq_dec, 7, rows(), value, success)
}
"#;
    if let Err(err) = e.elab_module_source("certified_lookup_test", src) {
        panic!(
            "certified lookup controls did not check: {}",
            err.render(src)
        );
    }
}
