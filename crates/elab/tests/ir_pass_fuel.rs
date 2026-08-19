use std::cell::RefCell;
use std::rc::Rc;

use heather_elab::gate::{GateItem, KernelGate};
use heather_elab::Elaborator;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::{check_term, DEFAULT_FUEL};

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");

const PROBE: &str = r#"
theorem cong_probe<A, B>(g: A -> B, {a, b: A}, p: a = b): g(a) = g(b) {
    j(p, λ y q => g(a) = g(y), refl)
}

record IrAlgProbe<M> {
    ret: Refs -> M,
    letcon: Nat -> Refs -> M -> M,
    letmatch: Nat -> M -> M -> M,
    arm: M -> M -> M,
    noarm: M,
    letloop: Refs -> M -> M -> M,
    loopiter: M -> M,
    letcall: Nat -> Refs -> M -> M,
}

fn ir_fold_probe<M>(alg: IrAlgProbe<M>, ir: Ir) -> M {
    match ir {
        Ret(rs) => alg.ret(rs),
        LetCon(tag, args, rest) => alg.letcon(tag, args, ir_fold_probe(alg, rest)),
        LetMatch(scrut, arms, rest) => alg.letmatch(scrut, ir_fold_probe(alg, arms), ir_fold_probe(alg, rest)),
        Arm(body, next) => alg.arm(ir_fold_probe(alg, body), ir_fold_probe(alg, next)),
        NoArm => alg.noarm,
        LetLoop(init, body, rest) => alg.letloop(init, ir_fold_probe(alg, body), ir_fold_probe(alg, rest)),
        LoopIter(body) => alg.loopiter(ir_fold_probe(alg, body)),
        LetCall(callee, args, rest) => alg.letcall(callee, args, ir_fold_probe(alg, rest)),
    }
}

record IrPassLawsProbe<M>(R: Ir -> M -> Type, alg: IrAlgProbe<M>) {
    ret: (rs: Refs) -> R(Ret(rs), alg.ret(rs)),
    letcon: (tag: Nat) -> (args: Refs) -> (rest: Ir) -> (rest_r: M) ->
        R(rest, rest_r) -> R(LetCon(tag, args, rest), alg.letcon(tag, args, rest_r)),
    letmatch: (scrut: Nat) -> (arms: Ir) -> (arms_r: M) -> R(arms, arms_r) ->
        (rest: Ir) -> (rest_r: M) -> R(rest, rest_r) ->
        R(LetMatch(scrut, arms, rest), alg.letmatch(scrut, arms_r, rest_r)),
    arm: (body: Ir) -> (body_r: M) -> R(body, body_r) ->
        (next: Ir) -> (next_r: M) -> R(next, next_r) ->
        R(Arm(body, next), alg.arm(body_r, next_r)),
    noarm: R(NoArm, alg.noarm),
    letloop: (init: Refs) -> (body: Ir) -> (body_r: M) -> R(body, body_r) ->
        (rest: Ir) -> (rest_r: M) -> R(rest, rest_r) ->
        R(LetLoop(init, body, rest), alg.letloop(init, body_r, rest_r)),
    loopiter: (body: Ir) -> (body_r: M) -> R(body, body_r) ->
        R(LoopIter(body), alg.loopiter(body_r)),
    letcall: (callee: Nat) -> (args: Refs) -> (rest: Ir) -> (rest_r: M) ->
        R(rest, rest_r) -> R(LetCall(callee, args, rest), alg.letcall(callee, args, rest_r)),
}

theorem ir_fold_sound_probe<M>(R: Ir -> M -> Type, alg: IrAlgProbe<M>,
    laws: IrPassLawsProbe<M>(R, alg), ir: Ir): R(ir, ir_fold_probe(alg, ir))
{
    match ir {
        Ret(rs) => laws.ret(rs),
        LetCon(tag, args, rest) =>
            laws.letcon(tag, args, rest, ir_fold_probe(alg, rest),
                ir_fold_sound_probe(R, alg, laws, rest)),
        LetMatch(scrut, arms, rest) =>
            laws.letmatch(scrut, arms, ir_fold_probe(alg, arms),
                ir_fold_sound_probe(R, alg, laws, arms), rest, ir_fold_probe(alg, rest),
                ir_fold_sound_probe(R, alg, laws, rest)),
        Arm(body, next) =>
            laws.arm(body, ir_fold_probe(alg, body), ir_fold_sound_probe(R, alg, laws, body),
                next, ir_fold_probe(alg, next), ir_fold_sound_probe(R, alg, laws, next)),
        NoArm => laws.noarm,
        LetLoop(init, body, rest) =>
            laws.letloop(init, body, ir_fold_probe(alg, body),
                ir_fold_sound_probe(R, alg, laws, body), rest, ir_fold_probe(alg, rest),
                ir_fold_sound_probe(R, alg, laws, rest)),
        LoopIter(body) => laws.loopiter(body, ir_fold_probe(alg, body),
            ir_fold_sound_probe(R, alg, laws, body)),
        LetCall(callee, args, rest) =>
            laws.letcall(callee, args, rest, ir_fold_probe(alg, rest),
                ir_fold_sound_probe(R, alg, laws, rest)),
    }
}

record IrEqLawsProbe(alg: IrAlgProbe<Ir>) {
    ret: (rs: Refs) -> Ret(rs) = alg.ret(rs),
    letcon: (tag: Nat) -> (args: Refs) -> (rest, rest_r: Ir) -> rest = rest_r -> LetCon(tag, args, rest) = alg.letcon(tag, args, rest_r),
    letmatch: (scrut: Nat) -> (arms, arms_r: Ir) -> arms = arms_r -> (rest, rest_r: Ir) -> rest = rest_r -> LetMatch(scrut, arms, rest) = alg.letmatch(scrut, arms_r, rest_r),
    arm: (body, body_r: Ir) -> body = body_r -> (next, next_r: Ir) -> next = next_r -> Arm(body, next) = alg.arm(body_r, next_r),
    noarm: NoArm = alg.noarm,
    letloop: (init: Refs) -> (body, body_r: Ir) -> body = body_r -> (rest, rest_r: Ir) -> rest = rest_r -> LetLoop(init, body, rest) = alg.letloop(init, body_r, rest_r),
    loopiter: (body, body_r: Ir) -> body = body_r -> LoopIter(body) = alg.loopiter(body_r),
    letcall: (callee: Nat) -> (args: Refs) -> (rest, rest_r: Ir) -> rest = rest_r -> LetCall(callee, args, rest) = alg.letcall(callee, args, rest_r),
}

theorem ir_fold_same_probe(alg: IrAlgProbe<Ir>, laws: IrEqLawsProbe(alg), ir: Ir): ir = ir_fold_probe(alg, ir) {
    match ir {
        Ret(rs) => laws.ret(rs),
        LetCon(tag, args, rest) => laws.letcon(tag, args, rest, ir_fold_probe(alg, rest), ir_fold_same_probe(alg, laws, rest)),
        LetMatch(scrut, arms, rest) => laws.letmatch(scrut, arms, ir_fold_probe(alg, arms), ir_fold_same_probe(alg, laws, arms), rest, ir_fold_probe(alg, rest), ir_fold_same_probe(alg, laws, rest)),
        Arm(body, next) => laws.arm(body, ir_fold_probe(alg, body), ir_fold_same_probe(alg, laws, body), next, ir_fold_probe(alg, next), ir_fold_same_probe(alg, laws, next)),
        NoArm => laws.noarm,
        LetLoop(init, body, rest) => laws.letloop(init, body, ir_fold_probe(alg, body), ir_fold_same_probe(alg, laws, body), rest, ir_fold_probe(alg, rest), ir_fold_same_probe(alg, laws, rest)),
        LoopIter(body) => laws.loopiter(body, ir_fold_probe(alg, body), ir_fold_same_probe(alg, laws, body)),
        LetCall(callee, args, rest) => laws.letcall(callee, args, rest, ir_fold_probe(alg, rest), ir_fold_same_probe(alg, laws, rest)),
    }
}

fn IrSameProbe(source: Ir) -> Ir -> Type { λ (result: Ir) => source = result }

fn normalize_tags_alg_probe() -> IrAlgProbe<Ir> {
    IrAlgProbe<Ir> {
        ret: λ (rs: Refs) => Ret(rs),
        letcon: λ (tag: Nat) (args: Refs) (rest: Ir) => LetCon(add(0, tag), args, rest),
        letmatch: λ (scrut: Nat) (arms: Ir) (rest: Ir) => LetMatch(scrut, arms, rest),
        arm: λ (body: Ir) (next: Ir) => Arm(body, next),
        noarm: NoArm,
        letloop: λ (init: Refs) (body: Ir) (rest: Ir) => LetLoop(init, body, rest),
        loopiter: λ (body: Ir) => LoopIter(body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) => LetCall(callee, args, rest),
    }
}

fn normalize_tags_laws_probe() ->
    IrPassLawsProbe<Ir>(IrSameProbe, normalize_tags_alg_probe())
{
    IrPassLawsProbe {
        ret: λ (rs: Refs) => refl,
        letcon: λ (tag: Nat) (args: Refs) (rest: Ir) (rest_r: Ir) ih =>
            trans(
                cong_probe(λ (n: Nat) => LetCon(n, args, rest), sym(add_left_zero(tag))),
                cong_probe(λ (r: Ir) => LetCon(add(0, tag), args, r), ih)),
        letmatch: λ (scrut: Nat) (arms: Ir) (arms_r: Ir) ih_arms
                (rest: Ir) (rest_r: Ir) ih_rest =>
            trans(cong_probe(λ (a: Ir) => LetMatch(scrut, a, rest), ih_arms),
                cong_probe(λ (r: Ir) => LetMatch(scrut, arms_r, r), ih_rest)),
        arm: λ (body: Ir) (body_r: Ir) ih_body
                (next: Ir) (next_r: Ir) ih_next =>
            trans(cong_probe(λ (b: Ir) => Arm(b, next), ih_body),
                cong_probe(λ (n: Ir) => Arm(body_r, n), ih_next)),
        noarm: refl,
        letloop: λ (init: Refs) (body: Ir) (body_r: Ir) ih_body
                (rest: Ir) (rest_r: Ir) ih_rest =>
            trans(cong_probe(λ (b: Ir) => LetLoop(init, b, rest), ih_body),
                cong_probe(λ (r: Ir) => LetLoop(init, body_r, r), ih_rest)),
        loopiter: λ (body: Ir) (body_r: Ir) ih_body =>
            cong_probe(λ (b: Ir) => LoopIter(b), ih_body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) (rest_r: Ir) ih =>
            cong_probe(λ (r: Ir) => LetCall(callee, args, r), ih),
    }
}

theorem normalize_tags_sound_probe(ir: Ir):
    IrSameProbe(ir)(ir_fold_probe(normalize_tags_alg_probe(), ir))
{
    ir_fold_sound_probe(IrSameProbe, normalize_tags_alg_probe(), normalize_tags_laws_probe(), ir)
}
"#;

const BAD: &str = r#"
import ir_v1;
import nat;

fn bump_tags_alg_probe() -> IrAlgProbe<Ir> {
    IrAlgProbe<Ir> {
        ret: λ (rs: Refs) => Ret(rs),
        letcon: λ (tag: Nat) (args: Refs) (rest: Ir) => LetCon(Succ(tag), args, rest),
        letmatch: λ (scrut: Nat) (arms: Ir) (rest: Ir) => LetMatch(scrut, arms, rest),
        arm: λ (body: Ir) (next: Ir) => Arm(body, next),
        noarm: NoArm,
        letloop: λ (init: Refs) (body: Ir) (rest: Ir) => LetLoop(init, body, rest),
        loopiter: λ (body: Ir) => LoopIter(body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) => LetCall(callee, args, rest),
    }
}

fn bad_tags_laws_probe() -> IrPassLawsProbe<Ir>(IrSameProbe, bump_tags_alg_probe()) {
    normalize_tags_laws_probe()
}
"#;

#[derive(Clone)]
struct Captured {
    psi: GlobalCtx,
    ty: Type,
    level: Level,
    body: Term,
}

#[derive(Default)]
struct CaptureGate(RefCell<Option<Captured>>);

impl KernelGate for CaptureGate {
    fn admits(&self, psi: &GlobalCtx, item: &GateItem<'_>) -> bool {
        if item.name != "ir_fold_sound_probe" {
            return false;
        }
        *self.0.borrow_mut() = Some(Captured {
            psi: psi.clone(),
            ty: item.ty.clone(),
            level: item.level.clone(),
            body: item.body.clone(),
        });
        true
    }
    fn accepted(&self, _psi: &GlobalCtx, _item: &GateItem<'_>) {}
}

#[test]
fn relation_indexed_ir_fold_checks_with_the_default_kernel_budget() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).expect("logic");
    e.elab_module_source("bool", BOOL).expect("bool");
    e.elab_module_source("nat", NAT).expect("nat");
    let cut = LIB.find("\ntheorem ").expect("ir theorem section");
    e.elab_module_source("ir_v1", &LIB[..cut]).expect("ir declarations");
    let gate = Rc::new(CaptureGate::default());
    e.set_gate(gate.clone());
    e.elab_module_source("ir_v1", PROBE).expect("probe elaboration");
    let c = gate.0.borrow().clone().expect("captured theorem");
    let empty = LocalCtx::nil();
    assert_eq!(
        check_term(&c.psi, 0, Layer::Code, &empty, &c.body, &c.ty, &c.level, DEFAULT_FUEL),
        Ok(())
    );
    let err = e
        .elab_module_source("bad_ir_pass", BAD)
        .expect_err("wrong tag mutation checked");
    assert!(format!("{err:?}").contains("NotConvertible"), "{err:?}");
}
