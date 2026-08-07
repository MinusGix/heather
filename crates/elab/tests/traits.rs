//! Traits, layer 1: the `class` and `instance` declaration forms
//! (`docs/traits-layer1-design.md`, `issues/traits.md`).
//!
//! Everything here is a *generated term* test in the sense of
//! `docs/testing-generated-terms.md`, because every artifact is synthesized:
//! the class's record, the members' globals, the assembled value, the
//! synthesized canonical parents, and the override-agreement certificates. So
//! the four axes are varied deliberately — an **open** carrier (a class used
//! through a `fn`'s type parameter), a **checking** position (an instance
//! passed where a class type is expected, and the value assembled against the
//! class type with no annotation), a **neutral** receiver (a parameter, not a
//! literal), and a **negative control** beside each positive.
//!
//! The load-bearing tests, if only three are read: `a_disagreeing_override_is_refused`
//! (the agreement discipline is what makes overriding safe),
//! `a_shared_ancestor_is_reached_at_one_value` (the diamond collapses
//! structurally, not by discipline), and `a_failed_instance_registers_nothing`
//! (an instance emits many globals and must be all-or-nothing).

use heather_elab::Elaborator;

/// The recovering entry point: one diagnostic per failed item, the rest of
/// the file still checked. What an instance's all-or-nothing property is
/// observable through.
fn check(src: &str) -> Vec<String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.check_source(src).into_iter().map(|err| err.render(src)).collect()
}

fn ok(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
    e
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

/// The prelude-shaped corpus named in `docs/traits-design.md` §13: a class
/// over container-ish carriers, with a **dependent** field (a law mentioning
/// earlier fields) so the Σ spine's dependency is exercised, not just its
/// product part.
const MONOID: &str = r#"
class Monoid<A> {
  unit: A,
  op: A -> A -> A,
  unit_l: (x: A) -> op(unit, x) = x,
}
"#;

const OPTION: &str = r#"
inductive Option<A> { None, Some(v: A) }
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
inductive Result<A> { Err, Ok(v: A) }
"#;

// -- 1: a class is a record ------------------------------------------------

#[test]
fn a_class_is_a_record_with_a_dependent_field() {
    ok(&format!(
        "{MONOID}
inductive Z {{ Z0, Z1 }}
fn zop(x: Z, y: Z) -> Z {{ y }}
theorem zl(x: Z): zop(Z0, x) = x {{ refl }}
fn m() -> Monoid<Z> {{ Monoid {{ unit: Z0, op: zop, unit_l: λ (x: Z) => zl(x) }} }}
"
    ));
}

#[test]
fn a_class_field_is_projected_like_any_record_field() {
    // Neutral receiver (a parameter), open carrier (`A` is the `fn`'s own type
    // parameter), and the projection applied — the three things a class is for.
    ok(&format!(
        "{MONOID}
fn twice<A>(m: Monoid<A>, x: A) -> A {{ m.op(x, x) }}
"
    ));
}

#[test]
fn a_class_with_no_arguments_at_a_use_is_refused() {
    let e = bad(&format!(
        "{MONOID}
fn f(m: Monoid) -> Nat {{ 0 }}
"
    ));
    assert!(e.contains("type argument"), "{e}");
}

#[test]
fn a_class_without_brackets_at_its_reference_is_refused() {
    // `extends Monoid` — a class is a record *parameterized by its carrier*,
    // so the carrier is always written (design §1).
    let e = bad(&format!(
        "{MONOID}
class Extra<A> extends Monoid {{ x: A }}
"
    ));
    assert!(e.contains("needs its arguments"), "{e}");
}

// -- 2: instances, block form ----------------------------------------------

const ZMONOID: &str = r#"
inductive Z { Z0, Z1 }

instance Monoid<Z> {
  fn unit() -> Z { Z0 }
  fn op(x: Z, y: Z) -> Z { y }
  theorem unit_l(x: Z): op(unit(), x) = x { refl }
}
"#;

#[test]
fn a_block_instance_declares_a_value_and_its_members() {
    // The value is reachable by its canonical name, its fields compute, and a
    // later member used an earlier one by short name (`unit_l` mentions `op`
    // and `unit` — it would not have checked otherwise).
    ok(&format!(
        "{MONOID}{ZMONOID}
theorem computes(): Z::Monoid.op(Z0, Z1) = Z1 {{ refl }}
"
    ));
}

#[test]
fn an_instance_is_an_ordinary_value_in_checking_position() {
    // Passed where `Monoid<Z>` is expected, at an *open* callee: `twice` knows
    // nothing about `Z`.
    ok(&format!(
        "{MONOID}{ZMONOID}
fn twice<A>(m: Monoid<A>, x: A) -> A {{ m.op(x, x) }}
theorem t(): twice(Z::Monoid, Z1) = Z1 {{ refl }}
"
    ));
}

#[test]
fn a_member_is_the_same_value_as_the_field_it_fills() {
    // The block form dissolves Lean's name duplication (design §4.2): one
    // definition per fact, reachable as a projection.
    ok(&format!(
        "{MONOID}{ZMONOID}
fn direct(x: Z, y: Z) -> Z {{ Z::Monoid.op(x, y) }}
theorem same(x: Z, y: Z): direct(x, y) = Z::Monoid.op(x, y) {{ refl }}
"
    ));
}

#[test]
fn a_member_that_is_not_a_field_of_the_class_is_refused() {
    let e = bad(&format!(
        "{MONOID}
inductive Z {{ Z0 }}
instance Monoid<Z> {{
  fn unit() -> Z {{ Z0 }}
  fn op(x: Z, y: Z) -> Z {{ y }}
  theorem unit_l(x: Z): op(unit(), x) = x {{ refl }}
  fn extra() -> Nat {{ 0 }}
}}
"
    ));
    assert!(e.contains("`extra` is not a field of `Monoid`"), "{e}");
}

#[test]
fn a_missing_field_is_reported_by_name() {
    let e = bad(&format!(
        "{MONOID}
inductive Z {{ Z0 }}
instance Monoid<Z> {{
  fn unit() -> Z {{ Z0 }}
}}
"
    ));
    assert!(e.contains("missing") && e.contains("op") && e.contains("unit_l"), "{e}");
}

#[test]
fn an_instance_of_something_that_is_not_a_class_is_refused() {
    let e = bad(
        "record R<A> { x: A }
inductive Z { Z0 }
instance R<Z> { x := Z0 }
",
    );
    assert!(e.contains("is not a class"), "{e}");
}

#[test]
fn two_instances_at_one_carrier_head_collide_loudly() {
    // Design §4.1/§7.1: the canonical name is keyed on the carrier *head*, so
    // this is refused rather than silently overwritten.
    let e = bad(&format!(
        "{MONOID}{ZMONOID}
instance Monoid<Z> {{
  fn unit() -> Z {{ Z1 }}
  fn op(x: Z, y: Z) -> Z {{ y }}
  theorem unit_l(x: Z): op(unit(), x) = x {{ refl }}
}}
"
    ));
    assert!(e.contains("already has an instance"), "{e}");
}

#[test]
fn a_failed_instance_registers_nothing() {
    // An instance emits several globals — its members, its value, its
    // synthesized parents — and a failure at any of them must leave none
    // behind. Observable only through the recovering entry point: the first
    // instance fails (its `unit_l` is false), and the second then declares the
    // *same* names successfully, which it could not do if the first had left
    // `Z::Monoid::op` or `Z::Monoid` in the tables.
    let errs = check(&format!(
        "{MONOID}
inductive Z {{ Z0, Z1 }}
instance Monoid<Z> {{
  fn unit() -> Z {{ Z0 }}
  fn op(x: Z, y: Z) -> Z {{ x }}
  theorem unit_l(x: Z): op(unit(), x) = x {{ refl }}
}}
instance Monoid<Z> {{
  fn unit() -> Z {{ Z0 }}
  fn op(x: Z, y: Z) -> Z {{ y }}
  theorem unit_l(x: Z): op(unit(), x) = x {{ refl }}
}}
theorem after(): Z::Monoid.op(Z0, Z1) = Z1 {{ refl }}
"
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(!errs[0].contains("duplicate"), "{}", errs[0]);
}

// -- 3: instances, literal form --------------------------------------------

#[test]
fn a_literal_instance_assembles_from_earlier_globals() {
    ok(&format!(
        "{MONOID}
inductive Z {{ Z0, Z1 }}
fn zunit() -> Z {{ Z0 }}
fn zop(x: Z, y: Z) -> Z {{ y }}
theorem zl(x: Z): zop(zunit(), x) = x {{ refl }}
instance Monoid<Z> {{ unit := zunit(), op := zop, unit_l := λ (x: Z) => zl(x) }}
theorem computes(): Z::Monoid.op(Z0, Z1) = Z1 {{ refl }}
"
    ));
}

#[test]
fn a_literal_instance_rejects_an_unknown_field() {
    let e = bad(&format!(
        "{MONOID}
inductive Z {{ Z0 }}
instance Monoid<Z> {{ nope := Z0 }}
"
    ));
    assert!(e.contains("`nope` is not a field of `Monoid`"), "{e}");
}

#[test]
fn a_mixed_body_is_refused() {
    let e = bad(&format!(
        "{MONOID}
inductive Z {{ Z0 }}
instance Monoid<Z> {{ fn unit() -> Z {{ Z0 }} op := Z0 }}
"
    ));
    assert!(e.contains("never both") || e.contains("parse error"), "{e}");
}

// -- 4: `extends`, flattening, canonical parents ---------------------------

const HIER: &str = r#"
class AddMonoid<G> {
  zero: G,
  add: G -> G -> G,
}
class AddGroup<G> extends AddMonoid<G> {
  neg: G -> G,
}
class AddCommMonoid<G> extends AddMonoid<G> {
  comm: (x: G) -> (y: G) -> add(x, y) = add(y, x),
}
class AddCommGroup<G> extends AddGroup<G>, AddCommMonoid<G> {
}
inductive Z { Z0 }
"#;

/// Child-first: no parent instance exists, so the child synthesizes and
/// registers all three ancestors as its own projections (design §4.4).
const CHILD_FIRST: &str = r#"
instance AddCommGroup<Z> {
  fn zero() -> Z { Z0 }
  fn add(x: Z, y: Z) -> Z { x }
  fn neg(x: Z) -> Z { x }
  theorem comm(x: Z, y: Z): add(x, y) = add(y, x) { match x { Z0 => match y { Z0 => refl } } }
}
"#;

#[test]
fn extends_flattens_the_field_list() {
    // The child's record has the ancestors' fields directly, so a `AddCommGroup`
    // literal is written with all of them and nothing nested.
    ok(&format!(
        "{HIER}
fn m() -> AddCommGroup<Z> {{
  AddCommGroup {{
    zero: Z0,
    add: λ (x: Z) => λ (y: Z) => x,
    neg: λ (x: Z) => x,
    comm: λ (x: Z) => λ (y: Z) => match x {{ Z0 => match y {{ Z0 => refl }} }},
  }}
}}
"
    ));
}

#[test]
fn a_child_first_declaration_synthesizes_its_parents() {
    ok(&format!(
        "{HIER}{CHILD_FIRST}
theorem p1(): Z::AddGroup.zero = Z0 {{ refl }}
theorem p2(): Z::AddCommMonoid.zero = Z0 {{ refl }}
theorem p3(): Z::AddMonoid.zero = Z0 {{ refl }}
"
    ));
}

#[test]
fn a_shared_ancestor_is_reached_at_one_value() {
    // The diamond: `AddMonoid<Z>` reached through `AddGroup` and through
    // `AddCommMonoid` is the same value, and the projections agree by `refl`
    // rather than by a discipline anybody has to follow.
    ok(&format!(
        "{HIER}{CHILD_FIRST}
theorem diamond(): Z::AddGroup.zero = Z::AddCommMonoid.zero {{ refl }}
theorem diamond_add(): Z::AddGroup.add = Z::AddCommMonoid.add {{ refl }}
theorem to_child(): Z::AddMonoid.add = Z::AddCommGroup.add {{ refl }}
"
    ));
}

#[test]
fn a_parent_first_declaration_fills_by_reference() {
    // The other direction (design §4.3 rule 3): `AddGroup<Z>` writes only what
    // is new, and its `zero`/`add` are the canonical parent's.
    ok(&format!(
        "{HIER}
instance AddMonoid<Z> {{
  fn zero() -> Z {{ Z0 }}
  fn add(x: Z, y: Z) -> Z {{ x }}
}}
instance AddGroup<Z> {{
  fn neg(x: Z) -> Z {{ x }}
}}
theorem by_reference(): Z::AddGroup.zero = Z::AddMonoid.zero {{ refl }}
theorem add_too(): Z::AddGroup.add = Z::AddMonoid.add {{ refl }}
"
    ));
}

#[test]
fn an_agreeing_override_is_accepted() {
    // Overriding a field the canonical parent already holds, with a value that
    // *is* convertible with it. The certificate is minted and checked.
    ok(&format!(
        "{HIER}
fn zadd(x: Z, y: Z) -> Z {{ x }}
instance AddMonoid<Z> {{
  fn zero() -> Z {{ Z0 }}
  fn add(x: Z, y: Z) -> Z {{ zadd(x, y) }}
}}
instance AddGroup<Z> {{
  fn add(x: Z, y: Z) -> Z {{ x }}
  fn neg(x: Z) -> Z {{ x }}
}}
"
    ));
}

#[test]
fn a_disagreeing_override_is_refused() {
    // The negative control the whole discipline exists for.
    let e = bad(&format!(
        "{HIER}
instance AddMonoid<Z> {{
  fn zero() -> Z {{ Z0 }}
  fn add(x: Z, y: Z) -> Z {{ x }}
}}
inductive B {{ B0, B1 }}
instance AddMonoid<B> {{
  fn zero() -> B {{ B0 }}
  fn add(x: B, y: B) -> B {{ x }}
}}
instance AddGroup<B> {{
  fn add(x: B, y: B) -> B {{ y }}
  fn neg(x: B) -> B {{ x }}
}}
"
    ));
    assert!(e.contains("overrides `add`") && e.contains("owes agreement"), "{e}");
}

#[test]
fn an_extends_argument_must_be_a_type_parameter() {
    let e = bad(
        "class P<A> { x: A }
inductive Box<A> { Mk(v: A) }
class C<A> extends P<Box<A>> { y: A }
",
    );
    assert!(e.contains("own type parameters"), "{e}");
}

#[test]
fn a_class_may_not_redeclare_an_inherited_field() {
    let e = bad(
        "class P<A> { x: A }
class C<A> extends P<A> { x: A }
",
    );
    assert!(e.contains("already has a field"), "{e}");
}

#[test]
fn two_unrelated_ancestors_contributing_one_field_collide() {
    let e = bad(
        "class P<A> { x: A }
class Q<A> { x: A }
class C<A> extends P<A>, Q<A> { }
",
    );
    assert!(e.contains("unrelated"), "{e}");
}

// -- 5: generic instances as values ----------------------------------------

const PAIR: &str = r#"
record Pair<A, B> { fst: A, snd: B }
"#;

#[test]
fn a_generic_instance_applies_and_computes() {
    // Without the law field, so the round's *value* story is tested on its
    // own: the dictionary is a function, and projecting from its application
    // computes at a concrete carrier.
    ok(&format!(
        "class Mag<A> {{ op: A -> A -> A }}
{PAIR}
inductive Z {{ Z0, Z1 }}
instance Mag<Z> {{ fn op(x: Z, y: Z) -> Z {{ y }} }}
instance<A, B> Mag<Pair<A, B>> requires ma: Mag<A>, mb: Mag<B> {{
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> {{
    Pair {{ fst: ma.op(x.fst, y.fst), snd: mb.op(x.snd, y.snd) }}
  }}
}}
fn pz() -> Mag<Pair<Z, Z>> {{ Pair::Mag }}
theorem computes():
  pz().op(Pair {{ fst: Z0, snd: Z0 }}, Pair {{ fst: Z1, snd: Z1 }}).fst = Z1 {{ refl }}
"
    ));
}

#[test]
fn a_generic_instances_cross_member_reference_finds_its_requires() {
    // Layer 1 pinned the opposite of this — a cross-member call *passed* its
    // `requires` binders — and said in the same breath that layer 2 would
    // change it (layer 1 §4.2, §8; layer 2 §9.3). It has: the binders are
    // solver parameters, and resolution finds them where they are, as locals
    // of this very declaration (the first ascending scope).
    ok(&format!(
        "class Mag<A> {{ op: A -> A -> A, twice: A -> A }}
{PAIR}
inductive Z {{ Z0, Z1 }}
instance<A, B> Mag<Pair<A, B>> requires ma: Mag<A>, mb: Mag<B> {{
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> {{
    Pair {{ fst: ma.op(x.fst, y.fst), snd: mb.op(x.snd, y.snd) }}
  }}
  fn twice(x: Pair<A, B>) -> Pair<A, B> {{ op(x, x) }}
}}
"
    ));
}

#[test]
fn a_cross_member_reference_passing_its_requires_positionally_is_refused() {
    // The negative control, and the retired layer-1 spelling: a solver
    // parameter has no positional slot, so the old `op(ma, mb, x, x)` is now
    // an arity error rather than the way it is written. `@op(…)` is the
    // spelling that passes one by hand.
    let e = bad(&format!(
        "class Mag<A> {{ op: A -> A -> A, twice: A -> A }}
{PAIR}
instance<A, B> Mag<Pair<A, B>> requires ma: Mag<A>, mb: Mag<B> {{
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> {{
    Pair {{ fst: ma.op(x.fst, y.fst), snd: mb.op(x.snd, y.snd) }}
  }}
  fn twice(x: Pair<A, B>) -> Pair<A, B> {{ op(ma, mb, x, x) }}
}}
"
    ));
    assert!(e.contains("op"), "{e}");
}

#[test]
fn a_parameterized_canonical_parent_is_not_a_fill_source() {
    // Design §4.3/§8: a generic instance's value is a *function*, so there is
    // no projection to fill from and no agreement partner — deciding what to
    // apply it to is resolution, which layer 1 does not have. The child writes
    // the inherited field itself; leaving it out is an honest missing-field
    // error rather than a wrong fill.
    let e = bad(
        "class P<A> {{ zero: A }}
class C<A> extends P<A> {{ one: A }}
record Box<A> {{ v: A }}
instance<A> P<Box<A>> requires pa: P<A> {{ fn zero() -> Box<A> {{ Box {{ v: pa.zero }} }} }}
instance<A> C<Box<A>> requires pa: P<A> {{ fn one() -> Box<A> {{ Box {{ v: pa.zero }} }} }}
"
        .replace("{{", "{")
        .replace("}}", "}")
        .as_str(),
    );
    assert!(e.contains("missing") && e.contains("zero"), "{e}");
}

#[test]
fn a_generic_child_writing_every_field_declares() {
    ok(
        "class P<A> { zero: A }
class C<A> extends P<A> { one: A }
record Box<A> { v: A }
instance<A> P<Box<A>> requires pa: P<A> { fn zero() -> Box<A> { Box { v: pa.zero } } }
instance<A> C<Box<A>> requires pa: P<A> {
  fn zero() -> Box<A> { Box { v: pa.zero } }
  fn one() -> Box<A> { Box { v: pa.zero } }
}
",
    );
}

// -- 6: the prelude-shaped corpus ------------------------------------------

#[test]
fn classes_over_the_prelude_carriers() {
    // `docs/traits-design.md` §13's first acceptance item: ordinary classes
    // over Option/Result/List-shaped types, each used through an **open** type
    // parameter so nothing is hidden by a closed carrier
    // (docs/testing-generated-terms.md).
    ok(&format!(
        "{OPTION}
class Functor<F> {{ dummy: Nat }}
class Pointed<A> {{ point: A }}
instance<A> Pointed<Option<A>> {{ fn point() -> Option<A> {{ None }} }}
instance<A> Pointed<List<A>> {{ fn point() -> List<A> {{ Nil }} }}
instance<A> Pointed<Result<A>> {{ fn point() -> Result<A> {{ Err }} }}
fn first<A>(p: Pointed<A>) -> A {{ p.point }}
theorem at_option(): first(Option::Pointed<Nat>()) = None {{ refl }}
theorem at_list(): first(List::Pointed<Nat>()) = Nil {{ refl }}
"
    ));
}

#[test]
fn a_class_over_an_open_carrier_checks_and_computes() {
    // The open axis on the *law* side: a dependent field instantiated at a
    // type parameter, projected at a neutral receiver, and only then closed.
    ok(&format!(
        "{MONOID}{ZMONOID}
fn fold<A>(m: Monoid<A>, x: A, y: A) -> A {{ m.op(m.op(m.unit, x), y) }}
theorem closes(): fold(Z::Monoid, Z0, Z1) = Z1 {{ refl }}
"
    ));
}
