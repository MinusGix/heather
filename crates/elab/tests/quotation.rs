//! The quotation slice (docs/in-language-map-design.md): `meta fn`
//! declarations elaborate through the modal signature, quote payloads with
//! letbox-hoisted splices, and the `Layer::Meta` kernel gate. The evaluation
//! hook and the `map_code` artifact have their own suite; this one is the
//! slice's own mechanics and its diagnostics.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

// -- the slice's mechanics, smallest first ---------------------------------

#[test]
fn a_closed_template_checks_at_the_meta_layer() {
    // No splices at all: one `Ctx` binder and a constant payload. The
    // smallest `meta fn` there is, and the first term ever checked at
    // `Layer::Meta` from the surface.
    elab("meta fn just_two(g: Ctx) -> Code(g |- Nat) { code { 2 } }");
}

#[test]
fn a_term_splice_hoists_a_letbox() {
    // `$x` under a `Succ`: the payload references the letbox-bound global,
    // and the kernel checks the whole letbox chain at layer m.
    elab(
        "meta fn wrap_succ(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { \
             code { Succ($x) } \
         }",
    );
}

#[test]
fn one_splice_used_twice_is_one_letbox() {
    // `add($x, $x)` — the scan dedupes by name; the payload references one
    // global twice. (`add` is not in scope inside a quote — the payload
    // spells addition structurally instead.)
    elab(
        "meta fn double_succ(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { \
             code { Succ(Succ($x)) } \
         }",
    );
}

#[test]
fn genericity_is_bound_inside_the_code() {
    // The calculus's answer to a polymorphic template (the round's central
    // finding, docs/in-language-map-design.md §3): a `TyPi`-bound type is
    // layer p and cannot appear inside layer-c code, so a generic template
    // binds its types *inside* the quote — code-level Π over the universe,
    // ordinary MLTT. This is the shape `map_code` takes.
    elab(
        "meta fn id_code(g: Ctx) -> Code(g |- (A: Type<0>) -> A -> A) { \
             code { fun (A: Type<0>) => fun (x: A) => x } \
         }",
    );
}

#[test]
fn splices_compose_under_binders() {
    // A term splice used *under* a payload binder: the letbox global's
    // weakening substitution is the calculus's job, not the author's — the
    // de Bruijn arithmetic vec.rs does by hand happens here in the kernel.
    elab(
        "meta fn const_fn(g: Ctx, x: Code(g |- Nat)) \
             -> Code(g |- Nat -> Nat) { \
             code { fun (y: Nat) => $x } \
         }",
    );
}

#[test]
fn let_code_names_a_splice() {
    elab(
        "meta fn renamed(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { \
             let code y = x; \
             code { Succ($y) } \
         }",
    );
}

#[test]
fn a_meta_fn_can_take_a_function_code_argument() {
    // `f` is code of a function, spliced at an application head inside the
    // payload — the letbox-composition shape the `map_code` fixture family
    // exercises at `Nat`.
    elab(
        "meta fn apply_code(g: Ctx, f: Code(g |- Nat -> Nat), x: Code(g |- Nat)) \
             -> Code(g |- Nat) { \
             code { $f($x) } \
         }",
    );
}

// -- diagnostics (the negative controls of the slice) ----------------------

#[test]
fn a_quote_outside_a_meta_fn_is_refused() {
    let msg = elab_err("fn f(n: Nat) -> Nat { code { 0 } }");
    assert!(msg.contains("meta fn"), "{msg}");
}

#[test]
fn a_quote_in_inference_position_is_refused() {
    let msg = elab_err(
        "meta fn f(g: Ctx) -> Code(g |- Nat) { let y = code { 0 }; code { 0 } }",
    );
    assert!(msg.contains("expected"), "{msg}");
}

#[test]
fn a_global_binder_after_a_local_is_refused() {
    let msg = elab_err(
        "meta fn f(g: Ctx, x: Code(g |- Nat), h: Ctx) -> Code(g |- Nat) { code { $x } }",
    );
    assert!(msg.contains("before"), "{msg}");
}

#[test]
fn an_ordinary_global_is_not_in_scope_inside_a_meta_fn() {
    let msg = elab_err(
        "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
         meta fn f(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { code { add($x, 1) } }",
    );
    assert!(msg.contains("pure"), "{msg}");
}

#[test]
fn tycode_binders_are_out_of_the_slice_with_the_layer_reason() {
    // The reserved syntax parses; the elaborator declines it by naming the
    // kernel fact (the `i' ≤ i` binding invariant) and the route around.
    let msg = elab_err(
        "meta fn f(g: Ctx, a: TyCode(g)) -> Code(g |- Nat) { code { 0 } }",
    );
    assert!(msg.contains("layer p"), "{msg}");
    assert!(msg.contains("Type<0>"), "{msg}");
}

#[test]
fn a_type_splice_is_refused_with_the_layer_reason() {
    let msg = elab_err(
        "meta fn f(g: Ctx, x: Code(g |- Nat)) -> Code(g |- $a -> Nat) { \
             code { fun (y: $a) => $x } \
         }",
    );
    assert!(msg.contains("layer p"), "{msg}");
}

#[test]
fn splicing_a_non_code_name_is_refused() {
    let msg =
        elab_err("meta fn f(g: Ctx) -> Code(g |- Nat) { code { Succ($nope) } }");
    assert!(msg.contains("nope"), "{msg}");
}

#[test]
fn goals_are_refused_in_a_meta_fn() {
    let msg = elab_err("meta fn f(g: Ctx) -> Code(g |- Nat) { code { ?later } }");
    assert!(msg.contains("goal"), "{msg}");
}

#[test]
fn a_meta_fn_must_return_code() {
    let msg = elab_err("meta fn f(g: Ctx) -> Nat { 0 }");
    assert!(msg.contains("Code"), "{msg}");
}

#[test]
fn modal_types_outside_a_meta_fn_are_refused() {
    let msg = elab_err("fn f(g: Ctx) -> Nat { 0 }");
    assert!(msg.contains("meta"), "{msg}");
}

// -- head/tail/cons, the vector spellings the payload wanted ---------------

#[test]
fn head_tail_cons_compute_on_literals() {
    // The vector arrives through a `fn` (a literal is checking-only, and
    // `head`/`tail`/`cons` infer their receiver).
    elab(
        "fn xs45() -> [Nat; 2] { [4, 5] }
         theorem h(): head(xs45()) = 4 { refl }
         theorem t(): head(tail(xs45())) = 5 { refl }
         theorem c(): cons(3, xs45()) = [3, 4, 5] { refl }",
    );
}

#[test]
fn head_and_tail_type_at_a_successor_of_a_neutral_length() {
    // The length is `Succ(n)` with `n` neutral — reduces to a successor, so
    // the projections type; nothing computes.
    elab(
        "fn first(n: Nat, xs: [Nat; Succ(n)]) -> Nat { head(xs) }
         fn rest(n: Nat, xs: [Nat; Succ(n)]) -> [Nat; n] { tail(xs) }
         fn put_back(n: Nat, xs: [Nat; Succ(n)]) -> [Nat; Succ(n)] {
             cons(head(xs), tail(xs))
         }",
    );
}

#[test]
fn head_at_a_fully_neutral_length_is_refused() {
    let msg = elab_err("fn f(n: Nat, xs: [Nat; n]) -> Nat { head(xs) }");
    assert!(msg.contains("successor"), "{msg}");
}
