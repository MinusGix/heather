use std::cell::RefCell;
use std::sync::Arc as Rc;

use heather_elab::gate::{GateItem, KernelGate};
use heather_elab::Elaborator;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::{check_term, DEFAULT_FUEL};

const LIB: &str = include_str!("../../../lib/certgen/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");

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
        letcon: λ (tag: Nat) (args: Refs) (rest: Ir) => LetCon(Nat::add(0, tag), args, rest),
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
                cong_probe(λ (n: Nat) => LetCon(n, args, rest), sym(tag.add_left_zero())),
                cong_probe(λ (r: Ir) => LetCon(Nat::add(0, tag), args, r), ih)),
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

// Constant-match fusion.  The constructor itself remains bound, but a match
// on its freshly-bound slot can be removed when both the chosen arm and the
// match continuation are Ret.  The two reference compositions below account
// for the arm's `fields ++ con ++ env` view and the continuation's
// `arm_outputs ++ con ++ env` view.
fn succ_refs_probe(rs: Refs) -> Refs {
    match rs {
        RNil => RNil,
        RCons(i, next) => RCons(Succ(i), succ_refs_probe(next)),
    }
}

fn resolve_ref_probe(prefix: Refs) -> Nat -> Nat {
    match prefix {
        RNil => λ (i: Nat) => i,
        RCons(head, tail) => λ (i: Nat) =>
            match i {
                Zero => head,
                Succ(k) => resolve_ref_probe(tail)(k),
            },
    }
}

fn remap_refs_probe(prefix: Refs, rs: Refs) -> Refs {
    match rs {
        RNil => RNil,
        RCons(i, next) =>
            RCons(resolve_ref_probe(prefix)(i), remap_refs_probe(prefix, next)),
    }
}

fn arm_outputs_in_con_env_probe(args: Refs, arm_outputs: Refs) -> Refs {
    remap_refs_probe(succ_refs_probe(args), arm_outputs)
}

fn fused_outputs_probe(args: Refs, arm_outputs: Refs, outputs: Refs) -> Refs {
    remap_refs_probe(arm_outputs_in_con_env_probe(args, arm_outputs), outputs)
}

fn gather_step_probe(head: OptVal, tail: OptVal) -> OptVal {
    match head {
        NoneV => NoneV,
        SomeV(v) =>
            match tail {
                NoneV => NoneV,
                SomeV(vs) => SomeV(VCons(v, vs)),
            },
    }
}

theorem gather_is_step_probe(i: Nat, next: Refs, env: Val):
    gather(RCons(i, next), env)
    = gather_step_probe(lookup(env)(i), gather(next, env))
{ refl }

theorem resolve_lookup_probe(prefix: Refs):
    (env, ws: Val) -> gather(prefix, env) = SomeV(ws) -> (i: Nat) ->
        lookup(env)(resolve_ref_probe(prefix)(i))
        = lookup(append(ws, env))(i)
{
    match prefix as λ p =>
        (env, ws: Val) -> gather(p, env) = SomeV(ws) -> (i: Nat) ->
            lookup(env)(resolve_ref_probe(p)(i))
            = lookup(append(ws, env))(i) {
        RNil => λ env ws hg i =>
            j(inj(hg),
              λ y q => lookup(env)(i) = lookup(append(y, env))(i),
              refl),
        RCons(head, tail) => λ env ws =>
            match hl : lookup(env)(head) as λ o =>
                gather_step_probe(o, gather(tail, env)) = SomeV(ws) ->
                (i: Nat) -> lookup(env)(resolve_ref_probe(RCons(head, tail))(i))
                    = lookup(append(ws, env))(i) {
                NoneV => λ hg i => absurd(hg),
                SomeV(v) =>
                    match ht : gather(tail, env) as λ o =>
                        gather_step_probe(SomeV(v), o) = SomeV(ws) ->
                        (i: Nat) -> lookup(env)(resolve_ref_probe(RCons(head, tail))(i))
                            = lookup(append(ws, env))(i) {
                        NoneV => λ hg i => absurd(hg),
                        SomeV(vs) => λ hg i =>
                            j(inj(hg),
                              λ y q =>
                                  lookup(env)(resolve_ref_probe(RCons(head, tail))(i))
                                  = lookup(append(y, env))(i),
                              match i {
                                  Zero => hl,
                                  Succ(k) => resolve_lookup_probe(tail)(env, vs, ht, k),
                              }),
                    },
            },
    }
}

theorem gather_remap_probe(prefix: Refs, rs: Refs):
    (env, ws: Val) -> gather(prefix, env) = SomeV(ws) ->
        gather(remap_refs_probe(prefix, rs), env)
        = gather(rs, append(ws, env))
{
    match rs as λ refs =>
        (env, ws: Val) -> gather(prefix, env) = SomeV(ws) ->
            gather(remap_refs_probe(prefix, refs), env)
            = gather(refs, append(ws, env)) {
        RNil => λ env ws hg => refl,
        RCons(i, next) => λ env ws hg =>
            trans(
                cong_probe(
                    λ (h: OptVal) =>
                        gather_step_probe(h,
                            gather(remap_refs_probe(prefix, next), env)),
                    resolve_lookup_probe(prefix)(env, ws, hg, i)),
                cong_probe(
                    λ (t: OptVal) =>
                        gather_step_probe(lookup(append(ws, env))(i), t),
                    gather_remap_probe(prefix, next)(env, ws, hg))),
    }
}

theorem gather_succ_refs_probe(rs: Refs):
    (head, env: Val) ->
        gather(succ_refs_probe(rs), VCons(head, env)) = gather(rs, env)
{
    match rs as λ refs =>
        (head, env: Val) ->
            gather(succ_refs_probe(refs), VCons(head, env)) = gather(refs, env) {
        RNil => λ head env => refl,
        RCons(i, next) => λ head env =>
            cong_probe(
                λ (t: OptVal) => gather_step_probe(lookup(env)(i), t),
                gather_succ_refs_probe(next)(head, env)),
    }
}

theorem fused_outputs_gather_probe(tag: Nat, args, arm_outputs, outputs: Refs,
    env, fields, ws, vs: Val,
    hg: gather(args, env) = SomeV(fields),
    ha: gather(arm_outputs,
            append(fields, VCons(VCon(tag, fields), env))) = SomeV(ws),
    ho: gather(outputs,
            append(ws, VCons(VCon(tag, fields), env))) = SomeV(vs)):
    gather(fused_outputs_probe(args, arm_outputs, outputs),
        VCons(VCon(tag, fields), env)) = SomeV(vs)
{
    let con_env: Val = VCons(VCon(tag, fields), env);
    let shifted: (gather(succ_refs_probe(args), con_env) = SomeV(fields)) =
        trans(gather_succ_refs_probe(args)(VCon(tag, fields), env), hg);
    let arm_mapped: (gather(arm_outputs_in_con_env_probe(args, arm_outputs), con_env)
                     = SomeV(ws)) =
        trans(gather_remap_probe(succ_refs_probe(args), arm_outputs)
                  (con_env, fields, shifted), ha);
    trans(gather_remap_probe(arm_outputs_in_con_env_probe(args, arm_outputs), outputs)
              (con_env, ws, arm_mapped), ho)
}

theorem fused_candidate_eval_probe(tag: Nat, args: Refs, arms: Ir,
    arm_outputs, outputs: Refs, env, fields: Val,
    hg: gather(args, env) = SomeV(fields),
    hpick: pick_arm(arms)(tag) = Ret(arm_outputs), fuel: Nat):
    (prog: Prog, vs: Val) ->
        eval(fuel, prog)(VCons(VCon(tag, fields), env),
            LetMatch(0, arms, Ret(outputs))) = Out(vs) ->
        eval(fuel, prog)(VCons(VCon(tag, fields), env),
            Ret(fused_outputs_probe(args, arm_outputs, outputs))) = Out(vs)
{
    match fuel as λ n =>
        (prog: Prog, vs: Val) ->
            eval(n, prog)(VCons(VCon(tag, fields), env),
                LetMatch(0, arms, Ret(outputs))) = Out(vs) ->
            eval(n, prog)(VCons(VCon(tag, fields), env),
                Ret(fused_outputs_probe(args, arm_outputs, outputs))) = Out(vs) {
        Zero => λ prog vs q => q,
        Succ(k) => λ prog vs =>
            j(sym(hpick),
              λ selected q =>
                  k_bind(eval(k, prog), VCons(VCon(tag, fields), env), Ret(outputs),
                      eval(k, prog)(append(fields, VCons(VCon(tag, fields), env)), selected))
                  = Out(vs) ->
                  eval(Succ(k), prog)(VCons(VCon(tag, fields), env),
                      Ret(fused_outputs_probe(args, arm_outputs, outputs))) = Out(vs),
              match k as λ m =>
                  k_bind(eval(m, prog), VCons(VCon(tag, fields), env), Ret(outputs),
                      eval(m, prog)(append(fields, VCons(VCon(tag, fields), env)),
                          Ret(arm_outputs))) = Out(vs) ->
                  eval(Succ(m), prog)(VCons(VCon(tag, fields), env),
                      Ret(fused_outputs_probe(args, arm_outputs, outputs))) = Out(vs) {
                  Zero => λ q => absurd(q),
                  Succ(j) =>
                      match ha : gather(arm_outputs,
                              append(fields, VCons(VCon(tag, fields), env))) as λ a =>
                          k_bind(eval(Succ(j), prog), VCons(VCon(tag, fields), env),
                              Ret(outputs), k_ret(a)) = Out(vs) ->
                          eval(Succ(Succ(j)), prog)(VCons(VCon(tag, fields), env),
                              Ret(fused_outputs_probe(args, arm_outputs, outputs))) = Out(vs) {
                          NoneV => λ q => absurd(q),
                          SomeV(ws) =>
                              match ho : gather(outputs,
                                      append(ws, VCons(VCon(tag, fields), env))) as λ o =>
                                  k_ret(o) = Out(vs) ->
                                  eval(Succ(Succ(j)), prog)(VCons(VCon(tag, fields), env),
                                      Ret(fused_outputs_probe(args, arm_outputs, outputs)))
                                  = Out(vs) {
                                  NoneV => λ q => absurd(q),
                                  SomeV(out) => λ q =>
                                      j(sym(fused_outputs_gather_probe(tag, args,
                                          arm_outputs, outputs, env, fields, ws, out,
                                          hg, ha, ho)),
                                        λ gathered p => k_ret(gathered) = Out(vs),
                                        q),
                              },
                      },
              }),
    }
}

fn fuse_letcon_probe(tag: Nat, args: Refs, rest: Ir) -> Ir {
    match rest {
        LetMatch(scrut, arms, cont) =>
            match scrut {
                Zero =>
                    match cont {
                        Ret(outputs) =>
                            match pick_arm(arms)(tag) {
                                Ret(arm_outputs) =>
                                    LetCon(tag, args,
                                        Ret(fused_outputs_probe(args, arm_outputs, outputs))),
                                _ => LetCon(tag, args, rest),
                            },
                        _ => LetCon(tag, args, rest),
                    },
                Succ(k) => LetCon(tag, args, rest),
            },
        _ => LetCon(tag, args, rest),
    }
}

theorem fused_candidate_letcon_law_probe(tag: Nat, args: Refs, rest, arms: Ir,
    arm_outputs, outputs: Refs,
    ih: IrExecForwardProbe(rest, LetMatch(0, arms, Ret(outputs))),
    hpick: pick_arm(arms)(tag) = Ret(arm_outputs)):
    IrExecForwardProbe(LetCon(tag, args, rest),
        LetCon(tag, args, Ret(fused_outputs_probe(args, arm_outputs, outputs))))
{
    IrExecForwardProbe(
        λ fuel prog env vs =>
            match fuel as λ n =>
                eval(n, prog)(env, LetCon(tag, args, rest)) = Out(vs) ->
                eval(n, prog)(env,
                    LetCon(tag, args,
                        Ret(fused_outputs_probe(args, arm_outputs, outputs)))) = Out(vs) {
                Zero => λ q => q,
                Succ(k) =>
                    match hg : gather(args, env) as λ o =>
                        k_letcon(eval(k, prog), env, tag, rest, o) = Out(vs) ->
                        k_letcon(eval(k, prog), env, tag,
                            Ret(fused_outputs_probe(args, arm_outputs, outputs)), o) = Out(vs) {
                        NoneV => λ q => q,
                        SomeV(fields) => λ q =>
                            fused_candidate_eval_probe(tag, args, arms, arm_outputs,
                                outputs, env, fields, hg, hpick, k)
                                (prog, vs,
                                    ih.eval_out(k, prog,
                                        VCons(VCon(tag, fields), env), vs, q)),
                    },
            },
        λ picked fuel prog env vs q => q)
}

theorem constant_match_fusion_letcon_law_probe(tag: Nat, args: Refs,
    rest, rest_r: Ir, ih: IrExecForwardProbe(rest, rest_r)):
    IrExecForwardProbe(LetCon(tag, args, rest), fuse_letcon_probe(tag, args, rest_r))
{
    match rest_r as λ transformed =>
        IrExecForwardProbe(rest, transformed) ->
        IrExecForwardProbe(LetCon(tag, args, rest),
            fuse_letcon_probe(tag, args, transformed)) {
        Ret(rs) => λ ih1 => add_default_letcon_law_probe(tag, args, rest,
            Ret(rs), ih1),
        LetCon(t, a, r) => λ ih1 => add_default_letcon_law_probe(tag, args, rest,
            LetCon(t, a, r), ih1),
        Arm(b, n) => λ ih1 => add_default_letcon_law_probe(tag, args, rest,
            Arm(b, n), ih1),
        NoArm => λ ih1 => add_default_letcon_law_probe(tag, args, rest,
            NoArm, ih1),
        LetLoop(init, b, r) => λ ih1 => add_default_letcon_law_probe(tag, args,
            rest, LetLoop(init, b, r), ih1),
        LoopIter(b) => λ ih1 => add_default_letcon_law_probe(tag, args, rest,
            LoopIter(b), ih1),
        LetCall(c, a, r) => λ ih1 => add_default_letcon_law_probe(tag, args,
            rest, LetCall(c, a, r), ih1),
        LetMatch(scrut, arms, cont) => λ ih1 =>
            match scrut as λ slot =>
                IrExecForwardProbe(rest, LetMatch(slot, arms, cont)) ->
                IrExecForwardProbe(LetCon(tag, args, rest),
                    fuse_letcon_probe(tag, args, LetMatch(slot, arms, cont))) {
                Succ(k) => λ ih2 => add_default_letcon_law_probe(tag, args, rest,
                    LetMatch(Succ(k), arms, cont), ih2),
                Zero => λ ih2 =>
                    match cont as λ continuation =>
                        IrExecForwardProbe(rest, LetMatch(0, arms, continuation)) ->
                        IrExecForwardProbe(LetCon(tag, args, rest),
                            fuse_letcon_probe(tag, args,
                                LetMatch(0, arms, continuation))) {
                        LetCon(t, a, r) => λ ih3 => add_default_letcon_law_probe(tag,
                            args, rest, LetMatch(0, arms, LetCon(t, a, r)), ih3),
                        LetMatch(s, a, r) => λ ih3 => add_default_letcon_law_probe(tag,
                            args, rest, LetMatch(0, arms, LetMatch(s, a, r)), ih3),
                        Arm(b, n) => λ ih3 => add_default_letcon_law_probe(tag, args,
                            rest, LetMatch(0, arms, Arm(b, n)), ih3),
                        NoArm => λ ih3 => add_default_letcon_law_probe(tag, args,
                            rest, LetMatch(0, arms, NoArm), ih3),
                        LetLoop(init, b, r) => λ ih3 => add_default_letcon_law_probe(tag,
                            args, rest, LetMatch(0, arms, LetLoop(init, b, r)), ih3),
                        LoopIter(b) => λ ih3 => add_default_letcon_law_probe(tag, args,
                            rest, LetMatch(0, arms, LoopIter(b)), ih3),
                        LetCall(c, a, r) => λ ih3 => add_default_letcon_law_probe(tag,
                            args, rest, LetMatch(0, arms, LetCall(c, a, r)), ih3),
                        Ret(outputs) => λ ih3 =>
                            match hpick : pick_arm(arms)(tag) as λ selected =>
                                IrExecForwardProbe(LetCon(tag, args, rest),
                                    match selected {
                                        Ret(arm_outputs) => LetCon(tag, args,
                                            Ret(fused_outputs_probe(args,
                                                arm_outputs, outputs))),
                                        _ => LetCon(tag, args,
                                            LetMatch(0, arms, Ret(outputs))),
                                    }) {
                                Ret(arm_outputs) =>
                                    fused_candidate_letcon_law_probe(tag, args, rest,
                                        arms, arm_outputs, outputs, ih3, hpick),
                                _ => add_default_letcon_law_probe(tag, args, rest,
                                    LetMatch(0, arms, Ret(outputs)), ih3),
                            },
                    }(ih2),
            }(ih1),
    }(ih)
}

fn constant_match_fusion_alg_probe() -> IrAlgProbe<Ir> {
    IrAlgProbe<Ir> {
        ret: λ (rs: Refs) => Ret(rs),
        letcon: fuse_letcon_probe,
        letmatch: λ (scrut: Nat) (arms: Ir) (rest: Ir) => LetMatch(scrut, arms, rest),
        arm: λ (body: Ir) (next: Ir) => Arm(body, next),
        noarm: NoArm,
        letloop: λ (init: Refs) (body: Ir) (rest: Ir) => LetLoop(init, body, rest),
        loopiter: λ (body: Ir) => LoopIter(body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) => LetCall(callee, args, rest),
    }
}

theorem identity_noarm_law_probe(): IrExecForwardProbe(NoArm, NoArm) {
    IrExecForwardProbe(
        λ fuel prog env vs q => q,
        λ tag fuel prog env vs q => q)
}

fn constant_match_fusion_laws_probe() ->
    IrPassLawsProbe<Ir>(IrExecForwardRelProbe, constant_match_fusion_alg_probe())
{
    IrPassLawsProbe {
        ret: add_default_arm_laws_probe().ret,
        letcon: constant_match_fusion_letcon_law_probe,
        letmatch: add_default_arm_laws_probe().letmatch,
        arm: add_default_arm_laws_probe().arm,
        noarm: identity_noarm_law_probe(),
        letloop: add_default_arm_laws_probe().letloop,
        loopiter: add_default_arm_laws_probe().loopiter,
        letcall: add_default_arm_laws_probe().letcall,
    }
}

theorem constant_match_fusion_sound_probe(ir: Ir):
    IrExecForwardProbe(ir, ir_fold_probe(constant_match_fusion_alg_probe(), ir))
{
    ir_fold_sound_probe(IrExecForwardRelProbe, constant_match_fusion_alg_probe(),
        constant_match_fusion_laws_probe(), ir)
}

theorem constant_match_fusion_refines_probe(prog: Prog, ir: Ir):
    RefinesProbe(prog, ir, ir_fold_probe(constant_match_fusion_alg_probe(), ir))
{
    λ env vs c => ConvergesProbe(c.n,
        constant_match_fusion_sound_probe(ir).eval_out(c.n, prog, env, vs, c.h))
}

fn fusion_source_probe() -> Ir {
    LetCon(1, RCons(1, RNil),
        LetMatch(0,
            Arm(NoArm, Arm(Ret(RCons(0, RCons(2, RNil))), NoArm)),
            Ret(RCons(0, RCons(1, RCons(2, RCons(4, RNil)))))))
}

fn fusion_result_probe() -> Ir {
    LetCon(1, RCons(1, RNil),
        Ret(RCons(2, RCons(1, RCons(0, RCons(2, RNil))))))
}

theorem constant_match_fusion_computes_probe():
    ir_fold_probe(constant_match_fusion_alg_probe(), fusion_source_probe())
    = fusion_result_probe()
{ refl }

theorem constant_match_fusion_source_runs_probe():
    eval(8, PNil)(VCons(VCon(7, VNil), VCons(VCon(8, VNil), VNil)),
        fusion_source_probe())
    = Out(VCons(VCon(8, VNil),
          VCons(VCon(7, VNil),
          VCons(VCon(1, VCons(VCon(8, VNil), VNil)),
          VCons(VCon(8, VNil), VNil)))))
{ refl }

theorem constant_match_fusion_result_runs_probe():
    eval(8, PNil)(VCons(VCon(7, VNil), VCons(VCon(8, VNil), VNil)),
        fusion_result_probe())
    = Out(VCons(VCon(8, VNil),
          VCons(VCon(7, VNil),
          VCons(VCon(1, VCons(VCon(8, VNil), VNil)),
          VCons(VCon(8, VNil), VNil)))))
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

const BAD_FUSION: &str = r#"
import ir_v1;
import nat;

// Wrong: constructor arguments are references in the pre-constructor
// environment.  The fused Ret runs after the constructor is bound, so every
// one must be shifted by Succ.  This mutation deliberately omits that shift.
fn bad_arm_outputs_in_con_env_probe(args: Refs, arm_outputs: Refs) -> Refs {
    remap_refs_probe(args, arm_outputs)
}

fn bad_fused_outputs_probe(args: Refs, arm_outputs: Refs, outputs: Refs) -> Refs {
    remap_refs_probe(bad_arm_outputs_in_con_env_probe(args, arm_outputs), outputs)
}

fn bad_fuse_letcon_probe(tag: Nat, args: Refs, rest: Ir) -> Ir {
    match rest {
        LetMatch(scrut, arms, cont) =>
            match scrut {
                Zero =>
                    match cont {
                        Ret(outputs) =>
                            match pick_arm(arms)(tag) {
                                Ret(arm_outputs) =>
                                    LetCon(tag, args,
                                        Ret(bad_fused_outputs_probe(args,
                                            arm_outputs, outputs))),
                                _ => LetCon(tag, args, rest),
                            },
                        _ => LetCon(tag, args, rest),
                    },
                Succ(k) => LetCon(tag, args, rest),
            },
        _ => LetCon(tag, args, rest),
    }
}

fn bad_constant_match_fusion_alg_probe() -> IrAlgProbe<Ir> {
    IrAlgProbe<Ir> {
        ret: λ (rs: Refs) => Ret(rs),
        letcon: bad_fuse_letcon_probe,
        letmatch: λ (scrut: Nat) (arms: Ir) (rest: Ir) => LetMatch(scrut, arms, rest),
        arm: λ (body: Ir) (next: Ir) => Arm(body, next),
        noarm: NoArm,
        letloop: λ (init: Refs) (body: Ir) (rest: Ir) => LetLoop(init, body, rest),
        loopiter: λ (body: Ir) => LoopIter(body),
        letcall: λ (callee: Nat) (args: Refs) (rest: Ir) => LetCall(callee, args, rest),
    }
}

fn bad_constant_match_fusion_laws_probe() ->
    IrPassLawsProbe<Ir>(IrExecForwardRelProbe, bad_constant_match_fusion_alg_probe())
{
    constant_match_fusion_laws_probe()
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
    fn accepted(&self, _psi: &GlobalCtx, _item: &GateItem<'_>, _unsealed: &[usize]) {}
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
    let err = e
        .elab_module_source("bad_constant_match_fusion", BAD_FUSION)
        .expect_err("unshifted constructor-field remapping checked");
    assert!(format!("{err:?}").contains("NotConvertible"), "{err:?}");
}
