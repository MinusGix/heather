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
import logic;

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

// Direct evaluation cannot observe an arm chain: `Arm` and `NoArm` are both
// stuck instructions.  A compositional execution relation therefore carries
// the second observation LetMatch makes, evaluation after `pick_arm`.
record IrExecForwardProbe(source: Ir, result: Ir) {
    eval_out: (fuel: Nat, prog: Prog, env, vs: Val) ->
        eval(fuel, prog)(env, source) = Out(vs) ->
        eval(fuel, prog)(env, result) = Out(vs),
    picked_out: (tag, fuel: Nat, prog: Prog, env, vs: Val) ->
        eval(fuel, prog)(env, pick_arm(source)(tag)) = Out(vs) ->
        eval(fuel, prog)(env, pick_arm(result)(tag)) = Out(vs),
}

fn IrExecForwardRelProbe(source: Ir) -> Ir -> Type {
    λ (result: Ir) => IrExecForwardProbe(source, result)
}

fn add_default_arm_alg_probe() -> IrAlgProbe<Ir> {
    IrAlgProbe<Ir> {
        ret: λ (rs: Refs) => Ret(rs),
        letcon: λ (tag: Nat) (args: Refs) (rest: Ir) => LetCon(tag, args, rest),
        letmatch: λ (scrut: Nat) (arms: Ir) (rest: Ir) => LetMatch(scrut, arms, rest),
        arm: λ (body: Ir) (next: Ir) => Arm(body, next),
        noarm: Arm(Ret(RNil), NoArm),
        letloop: λ (init: Refs) (body: Ir) (rest: Ir) => LetLoop(init, body, rest),
        loopiter: λ (body: Ir) => LoopIter(body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) => LetCall(callee, args, rest),
    }
}

theorem noarm_never_out_probe(fuel: Nat, prog: Prog, env, vs: Val):
    eval(fuel, prog)(env, NoArm) = Out(vs) -> False
{
    match fuel {
        Zero => λ q => absurd(q),
        Succ(k) => λ q => absurd(q),
    }
}

theorem loopiter_forward_probe(body, body_r: Ir,
    ih: IrExecForwardProbe(body, body_r), fuel: Nat):
    (prog: Prog, env, vs: Val) ->
        eval(fuel, prog)(env, LoopIter(body)) = Out(vs) ->
        eval(fuel, prog)(env, LoopIter(body_r)) = Out(vs)
{
    match fuel as λ n =>
        (prog: Prog, env, vs: Val) ->
            eval(n, prog)(env, LoopIter(body)) = Out(vs) ->
            eval(n, prog)(env, LoopIter(body_r)) = Out(vs) {
        Zero => λ prog env vs q => q,
        Succ(k) => λ prog env vs =>
            match h : eval(k, prog)(env, body) as λ r =>
                k_iter(eval(k, prog), body, r) = Out(vs) ->
                k_iter(eval(k, prog), body_r, eval(k, prog)(env, body_r)) = Out(vs) {
                Stuck => λ q => absurd(q),
                OutOfFuel => λ q => absurd(q),
                Out(ws) => λ q =>
                    j(sym(ih.eval_out(k, prog, env, ws, h)),
                      λ y p => k_iter(eval(k, prog), body_r, y) = Out(vs),
                      match ws as λ y =>
                          k_iter_vals(eval(k, prog), body, y) = Out(vs) ->
                          k_iter_vals(eval(k, prog), body_r, y) = Out(vs) {
                          VNil => λ q2 => q2,
                          VCon(t, f) => λ q2 => q2,
                          VCons(flag, carried) =>
                              match flag as λ g =>
                                  k_iter_flag(eval(k, prog), body, carried, g) = Out(vs) ->
                                  k_iter_flag(eval(k, prog), body_r, carried, g) = Out(vs) {
                                  VNil => λ q2 => q2,
                                  VCons(fh, ft) => λ q2 => q2,
                                  VCon(ftag, ffields) =>
                                      match ftag as λ n =>
                                          k_iter_tag(eval(k, prog), body, carried, n) = Out(vs) ->
                                          k_iter_tag(eval(k, prog), body_r, carried, n) = Out(vs) {
                                          Zero => λ q2 => q2,
                                          Succ(f2) => λ q2 =>
                                              loopiter_forward_probe(body, body_r, ih, k)
                                                  (prog, carried, vs, q2),
                                      },
                              },
                      }(q)),
            },
    }
}

theorem add_default_ret_law_probe(rs: Refs):
    IrExecForwardProbe(Ret(rs), Ret(rs))
{
    IrExecForwardProbe(
        λ fuel prog env vs q => q,
        λ tag fuel prog env vs q => q)
}

theorem add_default_noarm_eval_probe(fuel: Nat, prog: Prog, env, vs: Val):
    eval(fuel, prog)(env, NoArm) = Out(vs) ->
    eval(fuel, prog)(env, Arm(Ret(RNil), NoArm)) = Out(vs)
{
    match fuel {
        Zero => λ q => q,
        Succ(k) => λ q => q,
    }
}

theorem add_default_noarm_picked_probe(tag, fuel: Nat, prog: Prog, env, vs: Val):
    eval(fuel, prog)(env, pick_arm(NoArm)(tag)) = Out(vs) ->
    eval(fuel, prog)(env, pick_arm(Arm(Ret(RNil), NoArm))(tag)) = Out(vs)
{
    λ q => false_elim(noarm_never_out_probe(fuel, prog, env, vs, q))
}

theorem add_default_noarm_law_probe():
    IrExecForwardProbe(NoArm, Arm(Ret(RNil), NoArm))
{
    IrExecForwardProbe(
        add_default_noarm_eval_probe,
        add_default_noarm_picked_probe)
}

theorem add_default_letcon_law_probe(tag: Nat, args: Refs,
    rest, rest_r: Ir, ih: IrExecForwardProbe(rest, rest_r)):
    IrExecForwardProbe(LetCon(tag, args, rest), LetCon(tag, args, rest_r))
{
    IrExecForwardProbe(
        λ fuel prog env vs =>
            match fuel as λ n =>
                eval(n, prog)(env, LetCon(tag, args, rest)) = Out(vs) ->
                eval(n, prog)(env, LetCon(tag, args, rest_r)) = Out(vs) {
                Zero => λ q => q,
                Succ(k) =>
                    match gather(args, env) as λ o =>
                        k_letcon(eval(k, prog), env, tag, rest, o) = Out(vs) ->
                        k_letcon(eval(k, prog), env, tag, rest_r, o) = Out(vs) {
                        NoneV => λ q => q,
                        SomeV(ws) => λ q =>
                            ih.eval_out(k, prog, VCons(VCon(tag, ws), env), vs, q),
                    },
            },
        λ picked fuel prog env vs q => q)
}

theorem add_default_arm_cell_law_probe(body, body_r: Ir,
    ih_body: IrExecForwardProbe(body, body_r), next, next_r: Ir,
    ih_next: IrExecForwardProbe(next, next_r)):
    IrExecForwardProbe(Arm(body, next), Arm(body_r, next_r))
{
    IrExecForwardProbe(
        λ fuel prog env vs =>
            match fuel as λ n =>
                eval(n, prog)(env, Arm(body, next)) = Out(vs) ->
                eval(n, prog)(env, Arm(body_r, next_r)) = Out(vs) {
                Zero => λ q => q,
                Succ(k) => λ q => q,
            },
        λ tag fuel prog env vs =>
            match tag as λ n =>
                eval(fuel, prog)(env, pick_arm(Arm(body, next))(n)) = Out(vs) ->
                eval(fuel, prog)(env, pick_arm(Arm(body_r, next_r))(n)) = Out(vs) {
                Zero => λ q => ih_body.eval_out(fuel, prog, env, vs, q),
                Succ(k) => λ q => ih_next.picked_out(k, fuel, prog, env, vs, q),
            })
}

fn add_default_arm_laws_probe() ->
    IrPassLawsProbe<Ir>(IrExecForwardRelProbe, add_default_arm_alg_probe())
{
    IrPassLawsProbe {
        ret: add_default_ret_law_probe,
        letcon: add_default_letcon_law_probe,
        letmatch: λ (scrut: Nat) (arms: Ir) (arms_r: Ir) ih_arms
                (rest: Ir) (rest_r: Ir) ih_rest =>
            IrExecForwardProbe(
                λ fuel prog env vs =>
                    match fuel as λ n =>
                        eval(n, prog)(env, LetMatch(scrut, arms, rest)) = Out(vs) ->
                        eval(n, prog)(env, LetMatch(scrut, arms_r, rest_r)) = Out(vs) {
                        Zero => λ q => q,
                        Succ(k) =>
                            match lookup(env)(scrut) as λ o =>
                                k_letmatch(eval(k, prog), env, arms, rest, o) = Out(vs) ->
                                k_letmatch(eval(k, prog), env, arms_r, rest_r, o) = Out(vs) {
                                NoneV => λ q => q,
                                SomeV(v) =>
                                    match v as λ y =>
                                        k_letmatch_v(eval(k, prog), env, arms, rest, y) = Out(vs) ->
                                        k_letmatch_v(eval(k, prog), env, arms_r, rest_r, y) = Out(vs) {
                                        VNil => λ q => q,
                                        VCons(vh, vt) => λ q => q,
                                        VCon(tag2, fields) =>
                                            match h : eval(k, prog)(append(fields, env), pick_arm(arms)(tag2)) as λ r =>
                                                k_bind(eval(k, prog), env, rest, r) = Out(vs) ->
                                                k_bind(eval(k, prog), env, rest_r,
                                                    eval(k, prog)(append(fields, env), pick_arm(arms_r)(tag2))) = Out(vs) {
                                                Stuck => λ q => absurd(q),
                                                OutOfFuel => λ q => absurd(q),
                                                Out(ws) => λ q =>
                                                    j(sym(ih_arms.picked_out(tag2, k, prog,
                                                        append(fields, env), ws, h)),
                                                      λ y p => k_bind(eval(k, prog), env, rest_r, y) = Out(vs),
                                                      ih_rest.eval_out(k, prog, append(ws, env), vs, q)),
                                            },
                                    },
                            },
                    },
                λ picked fuel prog env vs q => q),
        arm: add_default_arm_cell_law_probe,
        noarm: add_default_noarm_law_probe(),
        letloop: λ (init: Refs) (body: Ir) (body_r: Ir) ih_body
                (rest: Ir) (rest_r: Ir) ih_rest =>
            IrExecForwardProbe(
                λ fuel prog env vs =>
                    match fuel as λ n =>
                        eval(n, prog)(env, LetLoop(init, body, rest)) = Out(vs) ->
                        eval(n, prog)(env, LetLoop(init, body_r, rest_r)) = Out(vs) {
                        Zero => λ q => q,
                        Succ(k) =>
                            match gather(init, env) as λ o =>
                                k_letloop(eval(k, prog), env, body, rest, o) = Out(vs) ->
                                k_letloop(eval(k, prog), env, body_r, rest_r, o) = Out(vs) {
                                NoneV => λ q => q,
                                SomeV(cs) =>
                                    match h : eval(k, prog)(cs, LoopIter(body)) as λ r =>
                                        k_bind(eval(k, prog), env, rest, r) = Out(vs) ->
                                        k_bind(eval(k, prog), env, rest_r,
                                            eval(k, prog)(cs, LoopIter(body_r))) = Out(vs) {
                                        Stuck => λ q => absurd(q),
                                        OutOfFuel => λ q => absurd(q),
                                        Out(ws) => λ q =>
                                            j(sym(loopiter_forward_probe(body, body_r, ih_body, k)
                                                (prog, cs, ws, h)),
                                              λ y p => k_bind(eval(k, prog), env, rest_r, y) = Out(vs),
                                              ih_rest.eval_out(k, prog, append(ws, env), vs, q)),
                                    },
                            },
                    },
                λ picked fuel prog env vs q => q),
        loopiter: λ (body: Ir) (body_r: Ir) ih_body =>
            IrExecForwardProbe(
                λ fuel prog env vs q =>
                    loopiter_forward_probe(body, body_r, ih_body, fuel)
                        (prog, env, vs, q),
                λ picked fuel prog env vs q => q),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) (rest_r: Ir) ih =>
            IrExecForwardProbe(
                λ fuel prog env vs =>
                    match fuel as λ n =>
                        eval(n, prog)(env, LetCall(callee, args, rest)) = Out(vs) ->
                        eval(n, prog)(env, LetCall(callee, args, rest_r)) = Out(vs) {
                        Zero => λ q => q,
                        Succ(k) =>
                            match gather(args, env) as λ o =>
                                k_letcall(eval(k, prog), prog, env, callee, rest, o) = Out(vs) ->
                                k_letcall(eval(k, prog), prog, env, callee, rest_r, o) = Out(vs) {
                                NoneV => λ q => q,
                                SomeV(cs) =>
                                    match h : eval(k, prog)(cs, find_fun(prog)(callee)) as λ r =>
                                        k_bind(eval(k, prog), env, rest, r) = Out(vs) ->
                                        k_bind(eval(k, prog), env, rest_r, r) = Out(vs) {
                                        Stuck => λ q => absurd(q),
                                        OutOfFuel => λ q => absurd(q),
                                        Out(ws) => λ q => ih.eval_out(k, prog, append(ws, env), vs, q),
                                    },
                            },
                    },
                λ picked fuel prog env vs q => q),
    }
}

theorem add_default_arm_sound_probe(ir: Ir):
    IrExecForwardProbe(ir, ir_fold_probe(add_default_arm_alg_probe(), ir))
{
    ir_fold_sound_probe(IrExecForwardRelProbe, add_default_arm_alg_probe(),
        add_default_arm_laws_probe(), ir)
}

record ConvergesProbe(prog: Prog, env: Val, ir: Ir, vs: Val) {
    n: Nat,
    h: eval(n, prog)(env, ir) = Out(vs),
}

fn RefinesProbe(prog: Prog, source, result: Ir) -> Type {
    (env, vs: Val) -> ConvergesProbe(prog, env, source, vs) ->
        ConvergesProbe(prog, env, result, vs)
}

theorem add_default_arm_refines_probe(prog: Prog, ir: Ir):
    RefinesProbe(prog, ir, ir_fold_probe(add_default_arm_alg_probe(), ir))
{
    λ env vs c => ConvergesProbe(c.n,
        add_default_arm_sound_probe(ir).eval_out(c.n, prog, env, vs, c.h))
}

theorem default_arm_changes_execution_probe():
    eval(4, PNil)(VCons(VCon(0, VNil), VNil),
        ir_fold_probe(add_default_arm_alg_probe(), LetMatch(0, NoArm, Ret(RNil))))
    = Out(VNil)
{ refl }
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

const BAD_DEFAULT: &str = r#"
import ir_v1;
import nat;

fn replace_existing_arms_alg_probe() -> IrAlgProbe<Ir> {
    IrAlgProbe<Ir> {
        ret: λ (rs: Refs) => Ret(rs),
        letcon: λ (tag: Nat) (args: Refs) (rest: Ir) => LetCon(tag, args, rest),
        letmatch: λ (scrut: Nat) (arms: Ir) (rest: Ir) => LetMatch(scrut, arms, rest),
        arm: λ (body: Ir) (next: Ir) => Arm(Ret(RNil), next),
        noarm: Arm(Ret(RNil), NoArm),
        letloop: λ (init: Refs) (body: Ir) (rest: Ir) => LetLoop(init, body, rest),
        loopiter: λ (body: Ir) => LoopIter(body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) => LetCall(callee, args, rest),
    }
}

fn bad_default_arm_laws_probe() ->
    IrPassLawsProbe<Ir>(IrExecForwardRelProbe, replace_existing_arms_alg_probe())
{
    add_default_arm_laws_probe()
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
fn ir_passes_check_at_default_fuel_and_carry_execution_refinement() {
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
    let err = e
        .elab_module_source("bad_default_arm_pass", BAD_DEFAULT)
        .expect_err("existing-arm mutation checked");
    assert!(format!("{err:?}").contains("NotConvertible"), "{err:?}");
}
