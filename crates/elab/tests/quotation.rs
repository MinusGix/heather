//! The quotation slice (docs/metaprogramming/in-language-map-design.md): `meta fn`
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

#[test]
fn explicit_emission_runs_a_named_template_under_binders() {
    elab(
        "meta fn identity(g: Ctx) -> Code(g |- Nat -> Nat) { code { fun (n: Nat) => n } }
        fn use_it(n: Nat) -> Nat { emit_code(identity)(n) }
        theorem computes(n: Nat): use_it(n) = n { refl }",
    );
}

#[test]
fn explicit_emission_checks_shape_and_result() {
    assert!(
        elab_err(
            "meta fn m(g: Ctx, c: Code(g |- Nat)) -> Code(g |- Nat) { code { $c } }
        fn bad() -> Nat { emit_code(m) }"
        )
        .contains("exactly one Ctx")
    );
    assert!(
        elab_err(
            "meta fn m(g: Ctx) -> Code(g |- Nat) { code { 0 } }
        fn bad(m: Nat) -> Nat { emit_code(m) }"
        )
        .contains("local value")
    );
    elab_err(
        "meta fn m(g: Ctx) -> Code(g |- Nat) { code { 0 } }
        theorem bad(): 0 = 1 { emit_code(m) }",
    );
}

#[test]
fn explicit_emission_rescopes_globals_and_respects_shadowing() {
    elab(
        "fn original(n: Nat) -> Nat { Succ(n) }
        meta fn m(g: Ctx) -> Code(g |- Nat -> Nat) { code { original } }
        fn intervening() -> Nat { 42 }
        theorem kept(): emit_code(m)(2) = 3 { refl }",
    );
    elab(
        "fn emit_code(n: Nat) -> Nat { n }
        theorem ordinary(): emit_code(2) = 2 { refl }",
    );
}

// -- the slice's mechanics, smallest first ---------------------------------

#[test]
fn explicit_emission_obeys_module_visibility() {
    let mut e = Elaborator::with_prelude().unwrap();
    for module in ["left", "right"] {
        e.elab_module_source(
            module,
            "meta fn template(g: Ctx) -> Code(g |- Nat) { code { 2 } }",
        )
        .unwrap();
    }
    assert!(
        e.elab_module_source("hidden", "fn f() -> Nat { emit_code(template) }")
            .is_err()
    );
    assert!(
        e.elab_module_source(
            "ambiguous",
            "import left; import right; fn f() -> Nat { emit_code(template) }"
        )
        .is_err()
    );
    assert!(
        e.elab_module_source("self_shadow", "import left;
            fn template() -> Nat { emit_code(template) }")
            .is_err()
    );
    e.elab_module_source(
        "qualified",
        "import left; import right;
        theorem works(): emit_code(left::template) = 2 { refl }",
    )
    .unwrap();
}

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
    // finding, docs/metaprogramming/in-language-map-design.md §3): a `TyPi`-bound type is
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
fn an_ordinary_global_is_in_scope_inside_a_meta_fn() {
    // It was not, until the analyzer round
    // (docs/archive/certgen-transcriber-in-language-design.md §9.1): the obstacle was
    // never the layer — a layer-c global is referenceable from layer m and
    // from layer-c code alike (`i' ≤ i`) — but the index arithmetic, since a
    // `meta fn`'s own Ψ-extending binders sit above Ψ. With that offset
    // applied, a payload may call a library function.
    elab(
        "fn add2(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k, ih) => Succ(ih) } }
         meta fn f(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { code { add2($x, 1) } }",
    );
}

#[test]
fn a_tycode_parameter_is_an_ordinary_code_of_a_type_local() {
    // Flipped from a refusal by the signature-reflection round
    // (docs/metaprogramming/fn-signature-reflection-design.md §3): `TyCode(g)` as a
    // *parameter* is an ordinary local of kernel type `CodeTy` — an
    // analyzer's reflected input — and extends nothing. What stays out is the
    // Ψ-extending `TyCode` *binder* role (a `$a` type splice for building
    // generic code), which the `i' ≤ i` binding invariant refuses — the next
    // test still pins that.
    elab("meta fn f(g: Ctx, a: TyCode(g)) -> Code(g |- Nat) { code { 0 } }");
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
fn a_meta_fn_may_return_ordinary_data() {
    // A *template* returns code; an **analyzer** returns a value, and it has
    // to: its `match code` motive must be context-free, which `Code(g |- T)`
    // is not (docs/archive/certgen-transcriber-in-language-design.md §9.1).
    elab("meta fn f(g: Ctx) -> Nat { 0 }");
}

#[test]
fn modal_types_outside_a_meta_fn_are_refused() {
    let msg = elab_err("fn f(g: Ctx) -> Nat { 0 }");
    assert!(msg.contains("meta"), "{msg}");
}

// -- `match code`: the analysis surface -------------------------------------
//
// docs/archive/certgen-transcriber-in-language-design.md §3. The elimination itself is
// exercised by the transcriber's own suite (certgen.rs); these are the slice's
// mechanics and its diagnostics.

#[test]
fn a_match_code_analyses_a_code_argument() {
    // Six arms and a default, at a constant motive. The kernel gate is the
    // `Layer::Meta` check of the whole declaration, so this passing means a
    // 65-branch `ElimCodeTm` was assembled and typed.
    elab(
        "meta fn probe(g: Ctx, body: Code(g |- Nat)) -> Nat {
             match code body as Nat {
                 tm_zero => 0,
                 tm_succ(t) => t,
                 tm_var => 1,
                 tm_lam(dom, b) => b,
                 tm_app(dom, cod, hd, arg) => arg,
                 tm_elim_nat(m, z, s, sc) => sc,
                 _ => 0,
             }
         }",
    );
}

#[test]
fn a_match_code_analyses_a_type_code_argument() {
    // The `ty_*` side (docs/metaprogramming/fn-signature-reflection-design.md §3): a
    // `TyCode(g)` scrutinee assembles an `ElimCodeTy` — same motives, same 65
    // branches — so this passing means the type-code recursor typed at the
    // meta gate. `ty_pi` binds two recursive results (rec.rs `ty_pi`; ch. 04
    // `G_Typ`), the codomain's at an extended local context, which the
    // constant motive absorbs exactly as it does for `tm_lam`.
    elab(
        "meta fn probe(g: Ctx, sig: TyCode(g)) -> Nat {
             match code sig as Nat {
                 ty_nat => 0,
                 ty_pi(s, t) => t,
                 _ => 1,
             }
         }",
    );
}

#[test]
fn a_match_code_needs_its_default_arm() {
    let msg = elab_err(
        "meta fn probe(g: Ctx, body: Code(g |- Nat)) -> Nat {
             match code body as Nat { tm_zero => 0 }
         }",
    );
    assert!(msg.contains("65"), "{msg}");
}

#[test]
fn a_match_code_arm_names_a_branch_of_the_recursor() {
    let msg = elab_err(
        "meta fn probe(g: Ctx, body: Code(g |- Nat)) -> Nat {
             match code body as Nat { Zero => 0, _ => 0 }
         }",
    );
    assert!(msg.contains("tm_zero"), "{msg}");
}

#[test]
fn a_match_code_arm_binds_its_branchs_results() {
    // `tm_succ` has exactly one recursive result; the arm's binders are those
    // and nothing else, so a second one is a shape error rather than a name.
    let msg = elab_err(
        "meta fn probe(g: Ctx, body: Code(g |- Nat)) -> Nat {
             match code body as Nat { tm_succ(t, u) => t, _ => 0 }
         }",
    );
    assert!(msg.contains("recursive result"), "{msg}");
}

#[test]
fn a_match_code_motive_is_constant() {
    // The motive elaborates with no locals in scope, so "constant" is enforced
    // by name resolution: a motive mentioning a parameter cannot even name it.
    // (`Fin(k)` is the smallest type that would try.)
    let msg = elab_err(
        "meta fn probe(g: Ctx, k: Nat, body: Code(g |- Nat)) -> Nat {
             match code body as Fin(k) { _ => FZ }
         }",
    );
    assert!(msg.contains('k'), "{msg}");
}

#[test]
fn match_code_is_meta_layer_machinery() {
    let msg = elab_err("fn probe(n: Nat) -> Nat { match code n as Nat { _ => 0 } }");
    assert!(msg.contains("meta"), "{msg}");
}

#[test]
fn match_code_does_not_go_inside_a_quote_payload() {
    let msg = elab_err(
        "meta fn probe(g: Ctx, body: Code(g |- Nat)) -> Code(g |- Nat) {
             code { match code $body as Nat { _ => 0 } }
         }",
    );
    assert!(msg.contains("layer"), "{msg}");
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
