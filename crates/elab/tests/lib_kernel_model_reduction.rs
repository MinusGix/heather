//! `lib/kernel_model/kernel_reduction.hthr` — a reference model of the
//! kernel's weak-head reduction and the substitution property the fold
//! classifier (`crates/kernel/src/eval/probe.rs`) relies on
//! (`docs/kernel-model-design.md`, milestone `hih-kernel-model`):
//!
//!  1. the module checks from images, and the kit is *there*, named one by
//!     one;
//!  2. the four axes of `docs/testing-generated-terms.md`: the model run at
//!     literal terms by `refl`, the probe lemma applied at an **open** value
//!     in checking position, out of fuel exactly where the probe was, and
//!     negative controls — a step that cases on `k` is blocked and its
//!     instance really differs, an instance by a non-value really differs,
//!     and the lemma cannot be applied to a blocked probe.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("kernel_reduction", include_str!("../../../lib/kernel_model/kernel_reduction.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn check(name: &str, src: &str) {
    let mut e = base();
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

fn refused(name: &str, src: &str) -> String {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => err.render(src),
    }
}

const IMPORTS: &str = "import logic; import bool; import nat; import option; import kernel_reduction;
// `add`'s step, `λ k ih. Succ(ih)`.
fn add_step() → Tm { Lam(Lam(NSucc(Bv(0)))) }
// A step that cases on `k`: `λ k ih. elim_Nat(0, λ _ _. 0, k)`.
fn split_step() → Tm { Lam(Lam(NRec(NZero, Lam(Lam(NZero)), Bv(1)))) }
// A step that returns `k`.
fn k_step() → Tm { Lam(Lam(Bv(1))) }
fn three() → Tm { NSucc(NSucc(NSucc(NZero))) }
";

const KIT: &[&str] = &[
    // Syntax, opening, instantiation.
    "Tm::open_at", "Tm::open", "Tm::Lc", "Tm::open_lc", "Tm::inst", "Tm::inst_open_at",
    "Tm::Ground", "Tm::inst_ground", "Proj::pick", "Proj::inst_pick",
    // Reduction.
    "Tm::step", "Tm::whnf", "Tm::rigid", "Tm::blocked", "Tm::Unblocked", "Tm::Value",
    // The substitution property and the probe.
    "Tm::CommutesOn", "Tm::Commutes", "Tm::app_k_inst", "Tm::rec_k_inst", "Tm::proj_k_inst", "Tm::run_step_inst",
    "Tm::step_inst", "Tm::whnf_inst",
    "Tm::probe", "Tm::probe_sub", "Tm::probe_step",
    // Instantiating by thunks: settled runs.
    "Tm::settled", "Tm::Settled", "Tm::step_inst_settled", "Tm::whnf_inst_settled", "Tm::probe_step_settled",
];

#[test]
fn the_kit_is_there() {
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check("kernel_reduction_kit", &src);
}

// The model runs by kernel evaluation: the probe of `add`'s step, the step
// at literals, and a run cut short by fuel.
#[test]
fn the_model_runs_at_literals() {
    check(
        "kernel_reduction_literals",
        &format!(
            "{IMPORTS}
            theorem add_probe(): Tm::whnf(4, Tm::probe(add_step())) = Some(NSucc(Fv(1))) {{ refl }}
            theorem add_at_three(): Tm::whnf(4, App(App(add_step(), three()), three())) = Some(NSucc(three())) {{ refl }}
            theorem add_short(): Tm::whnf(2, Tm::probe(add_step())) = None {{ refl }}
            theorem split_probe_blocked():
                Tm::whnf(4, Tm::probe(split_step())).map(λ (t: Tm) => t.blocked()) = Some(True) {{ refl }}"
        ),
    );
    let msg = refused(
        "kernel_reduction_wrong",
        &format!("{IMPORTS}\ntheorem bad(): Tm::whnf(4, Tm::probe(add_step())) = Some(NSucc(Fv(0))) {{ refl }}"),
    );
    assert!(msg.contains("NotConvertible") && !msg.contains("Ground"), "{msg}");
}

// The probe lemma at an open `ih`, in checking position: what the probe
// reduced to is what the step reduces to at any closed value, at the same
// fuel, and an instance runs out of fuel where the probe did.
#[test]
fn the_probe_holds_at_open_values() {
    check(
        "kernel_reduction_open",
        &format!(
            "{IMPORTS}
            theorem add_open(ihv: Tm, c: ihv.Lc(0), v: ihv.Value()):
                    Tm::whnf(4, App(App(add_step(), NZero), ihv)) = Some(NSucc(ihv)) {{
                Tm::probe_step(add_step(), trivial, 4, NZero, trivial, trivial, ihv, c, v, refl)
            }}
            theorem add_open_short(kv, ihv: Tm, kc: kv.Lc(0), kvv: kv.Value(), c: ihv.Lc(0), v: ihv.Value()):
                    Tm::whnf(2, App(App(add_step(), kv), ihv)) = None {{
                Tm::probe_step(add_step(), trivial, 2, kv, kc, kvv, ihv, c, v, trivial)
            }}
            // `ih` as the kernel holds it: an unevaluated thunk, left as it is.
            theorem add_thunk(kv, ihv: Tm, kc: kv.Lc(0), c: ihv.Lc(0)):
                    Tm::whnf(4, App(App(add_step(), kv), ihv)) = Some(NSucc(ihv)) {{
                Tm::probe_step_settled(add_step(), trivial, 4, kv, kc, ihv, c, refl)
            }}
            theorem add_thunk_literal():
                    Tm::whnf(4, App(App(add_step(), NZero), App(Lam(Bv(0)), NZero))) = Some(NSucc(App(Lam(Bv(0)), NZero))) {{
                add_thunk(NZero, App(Lam(Bv(0)), NZero), trivial, And(trivial, trivial))
            }}
            // The peeled reading (`k := Succ x`) is an instantiation whose
            // image mentions another atom: `split_step` settles there.
            theorem split_peeled_probe(): Tm::whnf(5, App(App(split_step(), NSucc(Fv(2))), Fv(1))) = Some(NZero) {{ refl }}
            theorem split_peeled(x: Tm, c: x.Lc(0)):
                    Tm::whnf(5, App(App(split_step(), NSucc(x)), x)) = Some(NZero) {{
                j(split_step().inst_ground(λ (a: Nat) => x, And(trivial, And(trivial, trivial))),
                  λ y p => Tm::whnf(5, App(App(y, NSucc(x)), x)) = Some(NZero),
                  Tm::whnf_inst_settled(λ (a: Nat) => x, λ a => c, 5,
                      App(App(split_step(), NSucc(Fv(2))), Fv(1)), refl))
            }}"
        ),
    );
}

// Each hypothesis is needed. A step that cases on `k` is blocked, and its
// instance at `k := 0` is not the instance of its probe; an instance by a
// non-value is not the instance of the probe either; and the lemma cannot
// be applied to a blocked probe.
#[test]
fn the_hypotheses_are_needed() {
    check(
        "kernel_reduction_controls",
        &format!(
            "{IMPORTS}
            theorem split_differs():
                    Tm::whnf(4, App(App(split_step(), NZero), NZero))
                        ≠ Tm::whnf(4, Tm::probe(split_step())).map(λ (v: Tm) => v.inst(Tm::probe_sub(NZero, NZero))) {{
                λ h => absurd(Option::some_inj(NZero, NRec(NZero, Lam(Lam(NZero)), NZero), h))
            }}
            theorem non_value_differs():
                    Tm::whnf(4, App(App(k_step(), App(Lam(Bv(0)), NZero)), NZero))
                        ≠ Tm::whnf(4, Tm::probe(k_step())).map(λ (v: Tm) => v.inst(Tm::probe_sub(App(Lam(Bv(0)), NZero), NZero))) {{
                λ h => absurd(Option::some_inj(NZero, App(Lam(Bv(0)), NZero), h))
            }}"
        ),
    );
    let msg = refused(
        "kernel_reduction_blocked",
        &format!(
            "{IMPORTS}
            theorem bad():
                    Tm::whnf(4, App(App(split_step(), NZero), NZero))
                        = Tm::whnf(4, Tm::probe(split_step())).map(λ (v: Tm) => v.inst(Tm::probe_sub(NZero, NZero))) {{
                Tm::probe_step(split_step(), And(trivial, And(trivial, trivial)), 4, NZero, trivial, trivial, NZero, trivial, trivial, refl)
            }}"
        ),
    );
    assert!(msg.contains("NotConvertible") && !msg.contains("Ground"), "{msg}");
}
