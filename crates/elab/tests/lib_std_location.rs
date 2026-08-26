//! Total location laws at open carriers, plus a concrete nested-record probe.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const LOCATION: &str = include_str!("../../../lib/std/location.hthr");

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [("logic", LOGIC), ("location", LOCATION)] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {}", err.render(src));
        }
    }
    e
}

#[test]
fn the_location_module_checks() {
    elaborated();
}

#[test]
fn composition_and_disjointness_apply_at_open_carriers() {
    let mut e = elaborated();
    let src = r#"
import logic;
import location;

theorem composed_read<S, A, B>(outer: Location<S, A>, inner: Location<A, B>,
    state: S):
    compose_location(outer, inner).read(state) = inner.read(outer.read(state))
{
    refl
}

theorem certified_get_put<S, A>(location: Location<S, A>,
    laws: LocationLaws<S, A>(location), state: S):
    location.write(state, location.read(state)) = state
{
    lawful_get_put(location, laws, state)
}

theorem framed<S, A, B>(left: Location<S, A>, right: Location<S, B>,
    apart: Disjoint<S, A, B>(left, right), state: S, value: B):
    left.read(right.write(state, value)) = left.read(state)
{
    disjoint_read_left(left, right, apart, state, value)
}
"#;
    if let Err(err) = e.elab_module_source("probe", src) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("open location laws did not apply: {msg}");
    }
}
