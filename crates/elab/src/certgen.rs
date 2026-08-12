//! The certifying generator, v2 (docs/certifying-generator-design.md §8
//! item 1; the v1 narrative is in the issue log).
//!
//! **Transcription lives in the language.** The fragment's definition — which
//! signatures and which bodies are transcribable, and what they transcribe to
//! — is `lib/certgen_code.hthr`, two `match code` shells over the reflected
//! declaration; there is no Rust walker any more
//! (`issues/retire-rust-transcriber.md` stage 2, 2026-08-12).
//!
//! **And so does the certificate fold.** *Which* kit lemma proves *which*
//! instruction, and whose certificate discharges a call, is
//! `lib/certgen_cert.hthr` — ordinary program-layer `fn`s folding the
//! transcriber's `Ir` into a first-order certificate expression
//! (docs/certgen-cert-expression-design.md, Round A of
//! `issues/in-language-certificate-emission.md`). What is left here is the
//! *rendering*: every argument of the emitted proof that is a name, which is
//! every argument the library could not know.
//!
//! What this module is, in the order the phases run:
//!
//!   1. the **reflection primitive** ([`body_code`], reached as
//!      [`Elaborator::fn_body_code`]): a declared fn's elaborated body as
//!      marked, closed, boxed code plus the callee tag→name table — the
//!      coordinate system an analyzer can actually read
//!      (docs/opaque-globals-analysis-design.md §2);
//!   2. the **invocation and readback** ([`run_sig_checker`],
//!      [`run_transcriber`], [`run_cert_fold`], [`Reader`],
//!      [`fn_ir_from_rir`]): apply the registered analyzers and the fold, read
//!      their answers back out of the kernel's value representation, and
//!      rebuild the `FnIr` and the `RCertOut` the emitters consume;
//!   3. the **emitters** ([`emit_with_model`] and below): *surface text* — the
//!      IR, the exactness fixtures, the ∃-form invariants ([`render_cert`],
//!      which is the certificate expression printed) and a `CompileNatK`
//!      instance value — to be checked appended to `lib/ir_v1.hthr` by the
//!      ordinary pipeline.
//!
//! The generator is untrusted by architecture: everything it emits is
//! kernel-checked, so every stage may decline (`Err` with a reason) and a bug
//! in any of them is a check failure, never an unsound theorem. The surface
//! AST is still consulted for exactly one thing the reflected declaration
//! cannot supply — the *names* ([`surface_params`]).
//!
//! v2's proof schema is the ∃-COMPOSITION KIT (`ret_conv` / `letcon_conv` /
//! `letmatch_conv` / `letcall_conv` in `lib/ir_v1.hthr`): an invariant is
//! `Converges(prog, env, body, out)` proved by folding the kit over the
//! instruction chain — every `gather`/`lookup` premise discharges by `refl`
//! on the concrete-spine environment, the self-call's certificate is the
//! induction hypothesis, and a foreign call's is the callee's invariant
//! *re-derived inside the caller's program* (same proof text, program
//! swapped — the workaround `issues/prog-extension-lemma.md` will retire).
//! No fuel bound appears in any statement; v1's bound functions are gone,
//! and literal fuels survive only in the exactness fixtures, computed by a
//! mini-evaluator over the transcribed IR.
//!
//! Cross-function calls: a caller's `Prog` is the ordered transitive
//! closure of its callees (self last), each member's body referenced by its
//! already-generated `_gen_body()`. Each callee's own closure must be a
//! prefix of the caller's, so every body's internal callee indices stay
//! valid in the combined program; a call DAG that breaks the prefix
//! property is declined — v2's honest boundary, with the linking lemma as
//! the general answer.
//!
//! Fuel model (for the fixture evaluator): every instruction dispatch costs
//! one fuel along its continuation, and a sub-run (a match arm, a callee, a
//! rebinding continuation) runs at the same decremented fuel — a *depth*
//! budget, `1 + max(sub, rest)` at the branching instructions.

use std::fmt::Write as _;

use heather_syntax::ast::{Decl, DeclKind};

/// One generated emission, carrying what later generations and the harness
/// need: the callee-closure metadata and the compiled IR model.
pub struct Emission {
    pub name: String,
    pub arity: usize,
    /// `Prog` members in order, self last.
    pub closure: Vec<String>,
    /// The rendered IR declarations (for the acceptance diff).
    pub ir_body: String,
    pub text: String,
    model: FnIr,
    /// The certificate expression the in-language fold produced for this
    /// function, kept because a *caller* re-derives this member's invariant
    /// inside its own program (docs/certgen-cert-expression-design.md §6).
    cert: RCertOut,
}

/// Previously generated emissions, consulted for foreign calls.
#[derive(Default)]
pub struct GenCtx {
    done: Vec<Emission>,
}

impl GenCtx {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn push(&mut self, e: Emission) {
        self.done.push(e);
    }
    pub fn iter(&self) -> impl Iterator<Item = &Emission> {
        self.done.iter()
    }
    fn get(&self, name: &str) -> Option<&Emission> {
        self.done.iter().find(|e| e.name == name)
    }
}

/// The per-arity certificate record, `CompileNatK`. `None` for K = 2:
/// `CompileNat2` is already declared in `lib/ir_v1.hthr`.
pub fn compile_record(arity: usize) -> Option<String> {
    if arity == 2 {
        return None;
    }
    let mut fty = String::from("Nat");
    for _ in 0..arity {
        fty = format!("Nat -> {fty}");
    }
    let params: Vec<String> = (1..=arity).map(|i| format!("a{i}")).collect();
    let env = env_text(&params, "VNil");
    let binders: String = params.iter().map(|p| format!("({p}: Nat) -> ")).collect();
    let app: String = params.iter().map(|p| format!("({p})")).collect();
    Some(format!(
        "record CompileNat{arity}(f: {fty}) {{\n    prog: Prog,\n    entry: Ir,\n    cert: {binders}Converges(prog, {env},\n                       entry, VCons(embed_nat(f{app}), VNil)),\n}}\n"
    ))
}

// ---------------------------------------------------------------------------
// The surface residue of the fragment check.

/// Names the emitted proofs bind; a source function whose parameters shadow
/// them is declined rather than renamed around.
const RESERVED: [&str; 3] = ["gz", "gk", "gih"];

/// Everything the fragment decision does **not** need the surface AST for is
/// gone: the signature rule is `lib/certgen_code.hthr`'s `check_sig`
/// (docs/fn-signature-reflection-design.md §4) and the body rule is the
/// walker's decline set, both reached through the reflection API. What no
/// reflected form can supply is the *names* — Ψ carries a body, not the
/// identifiers it was written with — and the spec expressions the emitted
/// proofs are spelled in are source identifiers. So this checks the two
/// facts that are about the written declaration and returns the parameter
/// names:
///
///   * a parameter may not shadow a binder the emitted proofs bind
///     (`RESERVED`), because the spec text would capture;
///   * a parameter may not be implicit, because the emitted `CompileNatK`
///     instance applies the spec function to all of them positionally.
///
/// A non-`Nat` parameter, a non-`Nat` result, a nullary fn, a type parameter
/// and every body-shape decline are the in-language verdicts', and reach the
/// caller with the in-language attribution.
fn surface_params(d: &Decl) -> Result<Vec<&str>, String> {
    if d.kind != DeclKind::Fn {
        return Err("not a fn".into());
    }
    for p in &d.params {
        if p.implicit {
            return Err(format!("parameter `{}` is implicit", p.name));
        }
        if RESERVED.contains(&p.name.as_str()) {
            return Err(format!("parameter `{}` collides with an emitted binder", p.name));
        }
    }
    Ok(d.params.iter().map(|p| p.name.as_str()).collect())
}

// ---------------------------------------------------------------------------
// Transcription model — the interface the readback rebuilds and the emitters
// consume. References are de Bruijn distances into a cons environment
// (0 = most recent). Pure structure: the SPEC expressions the emitted proofs
// are spelled with (the source sub-expression a slot denotes, with the
// Succ-arm binder spelled `gk`) used to be carried here too, and are now
// derived once, while the certificate expression is rendered
// (docs/certgen-cert-expression-design.md §3 — one derivation, at the rim).
// What is left is what the chain renderer, the closure and the fixture
// evaluator consume.

#[derive(Clone)]
enum Instr {
    Con { tag: u64, dists: Vec<usize> },
    Call { callee: String, dists: Vec<usize> },
}

#[derive(Clone)]
struct Chain {
    instrs: Vec<Instr>,
    ret_dist: usize,
    has_self_call: bool,
}

#[derive(Clone)]
struct RecIr {
    rec_idx: usize,
    zero: Chain,
    succ: Chain,
}

#[derive(Clone)]
enum FnIrKind {
    Plain(Chain),
    Rec(RecIr),
}

#[derive(Clone)]
struct FnIr {
    params: Vec<String>,
    kind: FnIrKind,
}

// ---------------------------------------------------------------------------
// Rendering helpers

fn refs(dists: &[usize]) -> String {
    let mut s = String::from("RNil");
    for d in dists.iter().rev() {
        s = format!("RCons({d}, {s})");
    }
    s
}

/// Render `instrs[from..] ; Ret`, callee indices resolved against a closure.
fn render_chain(instrs: &[Instr], from: usize, ret_dist: usize, closure: &[String]) -> String {
    let mut s = format!("Ret(RCons({ret_dist}, RNil))");
    for i in instrs[from..].iter().rev() {
        s = match i {
            Instr::Con { tag, dists } => format!("LetCon({tag}, {}, {s})", refs(dists)),
            Instr::Call { callee, dists } => {
                let idx = closure.iter().position(|c| c == callee).expect("callee in closure");
                format!("LetCall({idx}, {}, {s})", refs(dists))
            }
        };
    }
    s
}

/// `VCons(embed_nat(e0), … VCons(embed_nat(en), tail))` — slot 0 first.
fn env_text(exprs: &[String], tail: &str) -> String {
    let mut s = tail.to_string();
    for e in exprs.iter().rev() {
        s = format!("VCons(embed_nat({e}), {s})");
    }
    s
}

fn out_text(expr: &str) -> String {
    format!("VCons(embed_nat({expr}), VNil)")
}

// ---------------------------------------------------------------------------
// The fixture evaluator: exact minimal fuel at literal arguments, under the
// depth semantics.

#[derive(Clone)]
struct V(u64);

struct Evaluator<'a> {
    fns: Vec<(&'a str, &'a FnIr)>,
}

impl<'a> Evaluator<'a> {
    fn run_fn(&self, name: &str, args: &[V]) -> (V, usize) {
        let (_, f) = self.fns.iter().find(|(n, _)| *n == name).expect("fn in closure");
        match &f.kind {
            FnIrKind::Plain(c) => self.run_chain(c, args.to_vec()),
            FnIrKind::Rec(r) => {
                let scrut = args[r.rec_idx].clone();
                let (v, n) = if scrut.0 == 0 {
                    self.run_chain(&r.zero, args.to_vec())
                } else {
                    let mut env = vec![V(scrut.0 - 1)];
                    env.extend(args.iter().cloned());
                    self.run_chain(&r.succ, env)
                };
                // The LetMatch, over the deeper of the arm and the
                // rebinding Ret (cost 1).
                (v, 1 + n.max(1))
            }
        }
    }

    fn run_chain(&self, c: &Chain, env: Vec<V>) -> (V, usize) {
        self.run_from(c, 0, env)
    }

    fn run_from(&self, c: &Chain, from: usize, mut env: Vec<V>) -> (V, usize) {
        if from == c.instrs.len() {
            return (env[c.ret_dist].clone(), 1);
        }
        match &c.instrs[from] {
            Instr::Con { tag, dists } => {
                let v = if *tag == 0 { V(0) } else { V(env[dists[0]].0 + 1) };
                env.insert(0, v);
                let (out, n) = self.run_from(c, from + 1, env);
                (out, 1 + n)
            }
            Instr::Call { callee, dists } => {
                let args: Vec<V> = dists.iter().map(|&d| env[d].clone()).collect();
                let (cv, cn) = self.run_fn(callee, &args);
                env.insert(0, cv);
                let (out, n) = self.run_from(c, from + 1, env);
                (out, 1 + cn.max(n))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The ∃-proof emission: RENDER the certificate expression the in-language
// fold produced (docs/certgen-cert-expression-design.md).
//
// The fold itself is `lib/certgen_cert.hthr`: which kit lemma applies where,
// the order of the chain, the arm split, and — the interesting one — whether a
// call's hypothesis is the induction hypothesis or a callee's invariant. What
// is left here is every *name*: the program, the environment's spec
// expressions, the emitted `gk`/`gih`/`tail` binders, the arm-chain's
// generated fn names, and the closure indices a `LetCall` is spelled with.

struct ProofCx<'a> {
    prog: String,
    closure: &'a [String],
    conv_name: &'a dyn Fn(&str) -> String,
    ctx: &'a GenCtx,
    /// The closure member whose invariant is being proved: its self-calls
    /// consume `gih`, its arms are spelled `{self_name}_gen_arm_*`, and its
    /// own position in the program is what a self-call's `LetCall` names.
    self_name: &'a str,
    self_idx: usize,
    /// The recursion slot, when this member is recursive — the argument
    /// position `gih` does *not* take. `None` for a straight-line member, in
    /// which case a certificate that consumes an induction hypothesis is a
    /// fold/model disagreement rather than a decline.
    self_rec_idx: Option<usize>,
}

/// How a member's invariant theorem is applied at spec arguments.
fn cert_app(name: &str, model: &FnIr, arg_specs: &[String]) -> String {
    match &model.kind {
        FnIrKind::Plain(_) => format!("{name}({}, VNil)", arg_specs.join(", ")),
        FnIrKind::Rec(r) => {
            let rec_arg = &arg_specs[r.rec_idx];
            let mut others: Vec<String> = arg_specs
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != r.rec_idx)
                .map(|(_, s)| s.clone())
                .collect();
            others.push("VNil".into());
            format!("{name}({rec_arg})({})", others.join(", "))
        }
    }
}

/// The spec expression at distance `d`, or a decline: a certificate that
/// reads past its environment is one this readback cannot name, which is the
/// shape a wrong fold takes when it drops an instruction.
fn slot(env: &[String], d: usize) -> Result<String, String> {
    env.get(d).cloned().ok_or_else(|| "a certificate reading past the environment".to_string())
}

fn slots(env: &[String], dists: &[usize]) -> Result<Vec<String>, String> {
    dists.iter().map(|d| slot(env, *d)).collect()
}

/// The spec of a `letcon_conv` temporary: the fragment's constructors are
/// `Nat`'s, so slot-and-tag determine the source expression it stands for.
fn con_spec(tag: u64, args: &[String]) -> Result<String, String> {
    match tag {
        0 => Ok("Zero".to_string()),
        1 => {
            let a = args.first().ok_or("a `Succ` with no argument")?;
            Ok(format!("Succ({a})"))
        }
        other => Err(format!("constructor tag {other} is not a `Nat`")),
    }
}

impl ProofCx<'_> {
    fn callee_idx(&self, name: &str) -> Result<usize, String> {
        self.closure
            .iter()
            .position(|c| c == name)
            .ok_or_else(|| format!("`{name}` is not a member of the program"))
    }

    /// The IR the certificate is about, spelled as the emitted proofs spell
    /// it: `letcon_conv`/`letcall_conv` take the *remaining* region as an
    /// argument, and that region is exactly what the sub-certificate proves
    /// (`lib/certgen_cert.hthr` convention 3). Callee indices are the
    /// program closure's, which is where the walker's numbering is converted.
    fn cert_ir(&self, c: &RCert) -> Result<String, String> {
        Ok(match c {
            RCert::Ret { rs } => format!("Ret({})", refs(rs)),
            RCert::Con { tag, args, hr } => {
                format!("LetCon({tag}, {}, {})", refs(args), self.cert_ir(hr)?)
            }
            RCert::Ih { args, hr } => {
                format!("LetCall({}, {}, {})", self.self_idx, refs(args), self.cert_ir(hr)?)
            }
            RCert::Call { callee, args, hr } => {
                let idx = self.callee_idx(callee)?;
                format!("LetCall({idx}, {}, {})", refs(args), self.cert_ir(hr)?)
            }
            RCert::Match { .. } => {
                return Err("a `letmatch_conv` inside a straight-line region".into())
            }
        })
    }

    /// The spec of the value a straight-line certificate returns — the same
    /// walk `render_cert` makes, run for its answer alone because
    /// `letmatch_conv` needs it *before* its arm is rendered (it is the arm's
    /// `ws`, and the goal the arm's own chain is proved against).
    fn ret_spec(&self, c: &RCert, env: &[String]) -> Result<String, String> {
        match c {
            RCert::Ret { rs } => {
                let [d] = rs[..] else { return Err("a `Ret` with other than one output".into()) };
                slot(env, d)
            }
            RCert::Con { tag, args, hr } => {
                let spec = con_spec(*tag, &slots(env, args)?)?;
                let mut env2 = vec![spec];
                env2.extend(env.iter().cloned());
                self.ret_spec(hr, &env2)
            }
            RCert::Ih { args, hr } | RCert::Call { args, hr, .. } => {
                let name = match c {
                    RCert::Call { callee, .. } => callee.as_str(),
                    _ => self.self_name,
                };
                let spec = format!("{name}({})", slots(env, args)?.join(", "));
                let mut env2 = vec![spec];
                env2.extend(env.iter().cloned());
                self.ret_spec(hr, &env2)
            }
            RCert::Match { .. } => Err("a `letmatch_conv` inside a straight-line region".into()),
        }
    }
}

/// The `Converges` proof term the certificate `c` describes, in environment
/// `env_exprs ++ tail`, converging to `Out(out_text(final_spec))`.
///
/// One arm per `Cert` constructor, and the format strings are the ones the
/// Rust fold used: byte-identity to the previous output is this round's
/// acceptance bar (docs/certgen-cert-expression-design.md §8).
fn render_cert(
    cx: &ProofCx<'_>,
    c: &RCert,
    env_exprs: &[String],
    tail: &str,
    final_spec: &str,
) -> Result<String, String> {
    let p = &cx.prog;
    let env = env_text(env_exprs, tail);
    let vs = out_text(final_spec);
    Ok(match c {
        RCert::Ret { rs } => format!("ret_conv({p}, {env}, {}, {vs}, refl)", refs(rs)),
        RCert::Con { tag, args, hr } => {
            let arg_exprs = slots(env_exprs, args)?;
            let fs = env_text(&arg_exprs, "VNil");
            let rest_ir = cx.cert_ir(hr)?;
            let mut env2 = vec![con_spec(*tag, &arg_exprs)?];
            env2.extend(env_exprs.iter().cloned());
            let hr = render_cert(cx, hr, &env2, tail, final_spec)?;
            format!(
                "letcon_conv({p}, {env}, {tag}, {}, {rest_ir},\n        {fs}, {vs},\n        refl,\n        {hr})",
                refs(args)
            )
        }
        RCert::Ih { args, hr } | RCert::Call { args, hr, .. } => {
            let arg_exprs = slots(env_exprs, args)?;
            let (idx, name, hc) = match c {
                RCert::Call { callee, .. } => {
                    let cal = cx
                        .ctx
                        .get(callee)
                        .ok_or_else(|| format!("callee `{callee}` has no generated instance"))?;
                    (
                        cx.callee_idx(callee)?,
                        callee.clone(),
                        cert_app(&(cx.conv_name)(callee), &cal.model, &arg_exprs),
                    )
                }
                _ => {
                    // The structural self-call: its certificate is the
                    // induction hypothesis the emitted `match` binds, applied
                    // to every argument *except* the one it recurses on.
                    let rec_idx = cx
                        .self_rec_idx
                        .ok_or("a certificate consumes an induction hypothesis outside an induction")?;
                    let mut others: Vec<String> = arg_exprs
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != rec_idx)
                        .map(|(_, s)| s.clone())
                        .collect();
                    others.push("VNil".into());
                    (cx.self_idx, cx.self_name.to_string(), format!("gih({})", others.join(", ")))
                }
            };
            let cargs = env_text(&arg_exprs, "VNil");
            let spec = format!("{name}({})", arg_exprs.join(", "));
            let ws = out_text(&spec);
            let rest_ir = cx.cert_ir(hr)?;
            let mut env2 = vec![spec];
            env2.extend(env_exprs.iter().cloned());
            let hr = render_cert(cx, hr, &env2, tail, final_spec)?;
            format!(
                "letcall_conv({p}, {env}, {idx}, {}, {rest_ir},\n        {cargs}, {ws}, {vs},\n        refl,\n        {hc},\n        {hr})",
                refs(args)
            )
        }
        RCert::Match { scrut, ctag, ha, hr } => {
            // The arm-chain and the field list are the two arguments the
            // library cannot spell: the arms are named by their *generated*
            // definitions, and the fields are the emitted induction's binder
            // (design doc §3).
            let m = cx.self_name;
            let arms_text = format!("Arm({m}_gen_arm_zero(), Arm({m}_gen_arm_succ(), NoArm))");
            let after_ret = cx.cert_ir(hr)?;
            let fields = if *ctag == 0 {
                "VNil".to_string()
            } else {
                "VCons(embed_nat(gk), VNil)".to_string()
            };
            let mut arm_exprs = Vec::new();
            if *ctag != 0 {
                arm_exprs.push("gk".to_string());
            }
            arm_exprs.extend(env_exprs.iter().cloned());
            let arm_spec = cx.ret_spec(ha, &arm_exprs)?;
            let ws = out_text(&arm_spec);
            let arm_conv = render_cert(cx, ha, &arm_exprs, tail, &arm_spec)?;
            let mut after_exprs = vec![arm_spec];
            after_exprs.extend(env_exprs.iter().cloned());
            let after_conv = render_cert(cx, hr, &after_exprs, tail, final_spec)?;
            format!(
                "letmatch_conv({p}, {env}, {scrut}, {arms_text}, {after_ret},\n        {ctag}, {fields},\n        {ws}, {vs},\n        refl,\n        {arm_conv},\n        {after_conv})"
            )
        }
    })
}

// ---------------------------------------------------------------------------
// The emitters

/// Everything downstream of transcription: the callee closure, the IR
/// declarations, the fixtures, the ∃-kit folds and the instance. This was the
/// seam the port moved at (docs/certgen-transcriber-in-language-design.md §5):
/// the transcriber it is fed by is the in-language one, and phases 3 and 4 stay
/// here for the reasons that section's table gives.
fn emit_with_model(
    f: &str,
    arity: usize,
    model: FnIr,
    cert: RCertOut,
    ctx: &GenCtx,
) -> Result<Emission, String> {
    // Closure: callees' closures (prefix-compatible), then self.
    let mut closure: Vec<String> = Vec::new();
    for callee in callees(&model) {
        if callee == f {
            continue;
        }
        let cal = ctx
            .get(&callee)
            .ok_or_else(|| format!("callee `{callee}` has no generated instance"))?;
        if closure.is_empty() || cal.closure.starts_with(&closure[..]) {
            closure = cal.closure.clone();
        } else if closure.starts_with(&cal.closure[..]) {
            // already covered
        } else {
            return Err(format!(
                "callee `{callee}`'s program is not a prefix of the caller's \
                 (v2 boundary; issues/prog-extension-lemma.md is the general answer)"
            ));
        }
    }
    closure.push(f.to_string());

    // Emit.
    let mut text = String::new();
    let w = &mut text;
    writeln!(w, "// GENERATED by certgen v2 for `{f}` (docs/certifying-generator-design.md).").unwrap();
    writeln!(w).unwrap();

    let ir_body = emit_ir(w, f, &model, &closure);
    let mut prog = String::from("PNil");
    for m in closure.iter().rev() {
        prog = format!("PFun({m}_gen_body(), {prog})");
    }
    writeln!(w, "fn {f}_gen_prog() -> Prog {{ {prog} }}").unwrap();
    writeln!(w).unwrap();

    emit_fixtures(w, f, &model, &closure, ctx);

    // Invariants: every non-self closure member's, re-derived inside this
    // program, then self's.
    let fx = f.to_string();
    let conv_name = move |m: &str| -> String {
        if m == fx {
            format!("{fx}_gen_conv")
        } else {
            format!("{m}_gen_conv_in_{fx}")
        }
    };
    for m in closure.clone() {
        let (mm, mc): (FnIr, RCertOut) = if m == f {
            (model.clone(), cert.clone())
        } else {
            let e = ctx.get(&m).unwrap();
            (e.model.clone(), e.cert.clone())
        };
        emit_invariant(w, f, &m, &mm, &mc, &closure, ctx, &conv_name)?;
    }

    emit_instance(w, f, &model, arity);
    Ok(Emission { name: f.to_string(), arity, closure, ir_body, text, model, cert })
}

fn callees(model: &FnIr) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let chains: Vec<&Chain> = match &model.kind {
        FnIrKind::Plain(c) => vec![c],
        FnIrKind::Rec(r) => vec![&r.zero, &r.succ],
    };
    for c in chains {
        for i in &c.instrs {
            if let Instr::Call { callee, .. } = i {
                if !out.contains(callee) {
                    out.push(callee.clone());
                }
            }
        }
    }
    out
}

fn emit_ir(w: &mut String, f: &str, model: &FnIr, closure: &[String]) -> String {
    match &model.kind {
        FnIrKind::Plain(c) => {
            let body = render_chain(&c.instrs, 0, c.ret_dist, closure);
            writeln!(w, "fn {f}_gen_body() -> Ir {{ {body} }}").unwrap();
            writeln!(w).unwrap();
            format!("{f}_gen_body() = {body}")
        }
        FnIrKind::Rec(r) => {
            let zero = render_chain(&r.zero.instrs, 0, r.zero.ret_dist, closure);
            let succ = render_chain(&r.succ.instrs, 0, r.succ.ret_dist, closure);
            let body = format!(
                "LetMatch({}, Arm({f}_gen_arm_zero(), Arm({f}_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))",
                r.rec_idx
            );
            writeln!(w, "fn {f}_gen_arm_zero() -> Ir {{ {zero} }}").unwrap();
            writeln!(w).unwrap();
            writeln!(w, "fn {f}_gen_arm_succ() -> Ir {{").unwrap();
            writeln!(w, "    {succ}").unwrap();
            writeln!(w, "}}").unwrap();
            writeln!(w).unwrap();
            writeln!(w, "fn {f}_gen_body() -> Ir {{").unwrap();
            writeln!(w, "    {body}").unwrap();
            writeln!(w, "}}").unwrap();
            writeln!(w).unwrap();
            format!(
                "{f}_gen_arm_zero() = {zero}\n{f}_gen_arm_succ() = {succ}\n{f}_gen_body() = {body}"
            )
        }
    }
}

fn emit_fixtures(w: &mut String, f: &str, model: &FnIr, closure: &[String], ctx: &GenCtx) {
    let mut fns: Vec<(&str, &FnIr)> = Vec::new();
    for m in closure {
        if m == f {
            fns.push((f, model));
        } else {
            let e = ctx.get(m).unwrap();
            fns.push((e.name.as_str(), &e.model));
        }
    }
    let ev = Evaluator { fns };
    let lits: Vec<u64> = model
        .params
        .iter()
        .enumerate()
        .map(|(i, _)| match &model.kind {
            FnIrKind::Rec(r) if i == r.rec_idx => 2,
            _ => 3,
        })
        .collect();
    let args: Vec<V> = lits.iter().map(|&n| V(n)).collect();
    let (_, fuel) = ev.run_fn(f, &args);
    let lit_strs: Vec<String> = lits.iter().map(|n| n.to_string()).collect();
    let env = env_text(&lit_strs, "VNil");
    let call = format!("{f}({})", lit_strs.join(", "));
    writeln!(w, "theorem {f}_gen_fix():").unwrap();
    writeln!(w, "    eval({fuel}, {f}_gen_prog())({env}, {f}_gen_body())").unwrap();
    writeln!(w, "    = Out({})", out_text(&call)).unwrap();
    writeln!(w, "{{ refl }}").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "theorem {f}_gen_fix_short():").unwrap();
    writeln!(w, "    eval({}, {f}_gen_prog())({env}, {f}_gen_body())", fuel - 1).unwrap();
    writeln!(w, "    = OutOfFuel").unwrap();
    writeln!(w, "{{ refl }}").unwrap();
    writeln!(w).unwrap();
}

/// The invariant of closure member `m`'s body inside `f`'s program: for all
/// spec arguments and any environment tail, the body converges to the
/// embedded spec result.
///
/// The *proof* is `cert`, the certificate expression `lib/certgen_cert.hthr`
/// folded out of `m`'s IR; what this function writes around it is the
/// statement — binders, the induction's motive, and the `Zero`/`Succ(gk)`
/// spelling of the scrutinized parameter — every token of which is a name.
/// A certificate whose shape disagrees with the model's (a `CPlain` for a
/// recursive body, a `CRec` on the wrong slot) is an `Err`, not a decline:
/// the two come from the same `Ir`, so a disagreement is a bug in one of
/// them rather than a function outside the fragment.
fn emit_invariant(
    w: &mut String,
    f: &str,
    m: &str,
    model: &FnIr,
    cert: &RCertOut,
    closure: &[String],
    ctx: &GenCtx,
    conv_name: &dyn Fn(&str) -> String,
) -> Result<(), String> {
    let name = conv_name(m);
    let prog = format!("{f}_gen_prog()");
    let params = &model.params;
    let self_idx = closure
        .iter()
        .position(|c| c == m)
        .ok_or_else(|| format!("`{m}` is not a member of `{f}`'s program"))?;
    match (&model.kind, cert) {
        (FnIrKind::Plain(_), RCertOut::Plain(c)) => {
            let cx = ProofCx {
                prog: prog.clone(),
                closure,
                conv_name,
                ctx,
                self_name: m,
                self_idx,
                self_rec_idx: None,
            };
            let psig: String = params.iter().map(|p| format!("{p}: Nat, ")).collect();
            let env = env_text(params, "tail");
            let call = format!("{m}({})", params.join(", "));
            let proof = render_cert(&cx, c, params, "tail", &call)?;
            writeln!(w, "theorem {name}({psig}tail: Val)").unwrap();
            writeln!(w, "    : Converges({prog}, {env},").unwrap();
            writeln!(w, "                {m}_gen_body(), {})", out_text(&call)).unwrap();
            writeln!(w, "{{").unwrap();
            writeln!(w, "    {proof}").unwrap();
            writeln!(w, "}}").unwrap();
            writeln!(w).unwrap();
        }
        (FnIrKind::Rec(r), RCertOut::Rec { scrut, zero, succ }) if *scrut == r.rec_idx => {
            let rec_name = &params[r.rec_idx];
            let others: Vec<String> = params
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != r.rec_idx)
                .map(|(_, p)| p.clone())
                .collect();
            let other_binders: String = others.iter().map(|p| format!("({p}: Nat) -> ")).collect();
            let other_lams: String = others.iter().map(|p| format!("{p} ")).collect();
            let spell = |rec: &str| -> (Vec<String>, String, String) {
                let names: Vec<String> = params
                    .iter()
                    .enumerate()
                    .map(|(i, p)| if i == r.rec_idx { rec.to_string() } else { p.clone() })
                    .collect();
                let env = env_text(&names, "tail");
                let call = format!("{m}({})", names.join(", "));
                (names, env, call)
            };
            let (_, env_rec, call_rec) = spell(rec_name);
            let (_, env_z, call_z) = spell("gz");
            let cx = ProofCx {
                prog: prog.clone(),
                closure,
                conv_name,
                ctx,
                self_name: m,
                self_idx,
                self_rec_idx: Some(r.rec_idx),
            };

            // Per-constructor arm of the induction. The `letmatch_conv`
            // application is the certificate's own root (`CMatch`); what the
            // arm supplies is the environment the scrutinee is spelled into.
            let arm_proof = |ctor_tag: u64, c: &RCert| -> Result<String, String> {
                let (entry_exprs, _, call) =
                    spell(if ctor_tag == 0 { "Zero" } else { "Succ(gk)" });
                render_cert(&cx, c, &entry_exprs, "tail", &call)
            };

            writeln!(w, "theorem {name}({rec_name}: Nat):").unwrap();
            writeln!(w, "    {other_binders}(tail: Val)").unwrap();
            writeln!(w, "    -> Converges({prog},").unwrap();
            writeln!(w, "                 {env_rec},").unwrap();
            writeln!(w, "                 {m}_gen_body(), {})", out_text(&call_rec)).unwrap();
            writeln!(w, "{{").unwrap();
            writeln!(w, "    match {rec_name} as λ gz =>").unwrap();
            writeln!(w, "        {other_binders}(tail: Val)").unwrap();
            writeln!(w, "        -> Converges({prog},").unwrap();
            writeln!(w, "                     {env_z},").unwrap();
            writeln!(w, "                     {m}_gen_body(), {}) {{", out_text(&call_z)).unwrap();
            writeln!(w, "        Zero => λ {other_lams}tail =>").unwrap();
            writeln!(w, "        {},", arm_proof(0, zero)?).unwrap();
            writeln!(w, "        Succ(gk, gih) => λ {other_lams}tail =>").unwrap();
            writeln!(w, "        {},", arm_proof(1, succ)?).unwrap();
            writeln!(w, "    }}").unwrap();
            writeln!(w, "}}").unwrap();
            writeln!(w).unwrap();
        }
        _ => {
            return Err(format!(
                "the certificate fold and the transcription model disagree about `{m}`'s shape"
            ))
        }
    }
    Ok(())
}

fn emit_instance(w: &mut String, f: &str, model: &FnIr, arity: usize) {
    let params = &model.params;
    let lams: String = params.iter().map(|p| format!("λ ({p}: Nat) => ")).collect();
    let cert = cert_app(&format!("{f}_gen_conv"), model, params);
    writeln!(w, "fn {f}_gen_instance() -> CompileNat{arity}({f}) {{").unwrap();
    writeln!(w, "    CompileNat{arity} {{").unwrap();
    writeln!(w, "        prog: {f}_gen_prog(),").unwrap();
    writeln!(w, "        entry: {f}_gen_body(),").unwrap();
    writeln!(w, "        cert: {lams}{cert},").unwrap();
    writeln!(w, "    }}").unwrap();
    writeln!(w, "}}").unwrap();
}

// ---------------------------------------------------------------------------
// The in-language path (docs/certgen-transcriber-in-language-design.md).
//
// Transcription runs in the language: the elaborator marks the fn's elaborated
// body, an analyzer `meta fn` walks it with the code recursor, and its `Ir`
// value is read back into the `FnIr` the emitters above consume. There is no
// Rust walker beside it any more (issues/retire-rust-transcriber.md stage 2);
// everything after `FnIr` — chain rendering, the ∃-kit fold, the fixtures, the
// instance — is downstream of the seam, not an alternative to it.
//
// Untrusted at every step: an unrecognized shape *declines* (an `Err` with a
// reason), and a misread one produces an emission whose certificate the kernel
// refuses. Neither can produce a wrong theorem.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::reduce::{self, Defs};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    GlobalBinding, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type,
};

use crate::slots::Slot;
use crate::Elaborator;

/// Fuel for the transcriber's evaluation and readback — the kernel's own
/// default, deliberately not a bespoke larger one. Reduction is *recursive*,
/// so a fuel budget far above the ordinary one buys nothing but a stack
/// overflow on a term that does not reduce the way the reader expects, and
/// running out is a decline like any other.
const FUEL: u64 = heather_kernel::typing::DEFAULT_FUEL;

/// `(λ (x: Nat). x) ⌜n⌝` — the marker standing for the binder whose de Bruijn
/// **level** is `n` (§1 of the design doc).
///
/// Why a β-redex rather than a bare numeral: the fragment's own source
/// contains numerals, so a numeral marker would be ambiguous, while the only
/// applications in marked fragment code are the markers themselves and the
/// callee-marker spines of convention 3 ([`callee_marker`]), which the walker
/// tells apart by the λ's body. Code does not compute (`Layer::computes` is
/// `Prog | Meta`), so the redex is stable syntax: the recursor dispatches it
/// to the `tm_app` branch and no reduction can collapse it first.
fn marker(n: u32) -> Term {
    let mut num = Term::Zero;
    for _ in 0..n {
        num = Term::Succ(Rc::new(num));
    }
    Term::App {
        fun: Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Var(LocalVar(0))),
        }),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::new(Type::Nat),
        cod: Rc::new(Type::Nat),
        arg: Rc::new(num),
    }
}

/// `λ (x₁ : Nat). … λ (x_k : Nat). ⌜tag⌝` — the CALLEE marker, convention 3
/// (docs/opaque-globals-analysis-design.md §3): a closed term of the callee's
/// own fragment type `Nat → … → Nat`, carrying which callee it is as the
/// chain's numeral body. The argument spine stays in place around it, so the
/// walker reads the call by assembling applications onto the chain.
///
/// Same stability argument as [`marker`]: code does not compute, so the chain
/// never β-reduces against its arguments — `beta_elim_tm` dispatches the
/// `App`s to `tm_app` and the chain to `tm_lam`. And the same recognizer
/// stance: fragment source contains no λ at all, so a λ-chain ending in a
/// numeral is unambiguous *within the fragment* — which is why a nullary
/// callee (whose marker would be a bare numeral, ambiguous with literals) is
/// refused at [`MarkCx::callee`] instead of minted.
fn callee_marker(tag: u32, arity: usize) -> Term {
    let mut num = Term::Zero;
    for _ in 0..tag {
        num = Term::Succ(Rc::new(num));
    }
    // Innermost-out; a `Lam` carries only its domain annotation.
    let mut t = num;
    for _ in 0..arity {
        t = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(t),
        };
    }
    t
}

/// Callee resolution for [`mark`]: the caller's Ψ prefix, and the tag table
/// minted in first-occurrence order (tag `i + 1` is `callees[i]`; tag 0 is
/// the self-call's, which arrives as the ih marker, never through here).
struct MarkCx<'a> {
    e: &'a Elaborator,
    /// The analyzed fn's own binding index: its stored body is scoped to the
    /// Ψ prefix of this length, so `GlobalVar(v)` in it names binding
    /// `caller_abs - 1 - v` — `Defs::body`'s `shift_global(v + 1)`
    /// convention run backwards.
    caller_abs: usize,
    callees: Vec<String>,
}

impl MarkCx<'_> {
    /// `(marker tag, arity)` for the callee `v` names — or the decline that
    /// keeps the marker convention honest: a callee outside the fragment
    /// signature, a nullary callee (its marker would be a bare numeral), or
    /// a body-less global (proofs are opaque; a call to one is not fragment
    /// code) each refuse with the policy named.
    fn callee(&mut self, v: GlobalVar) -> Result<(u32, usize), String> {
        let abs = self
            .caller_abs
            .checked_sub(1 + v.0 as usize)
            .ok_or("a global reference outside the caller's Ψ prefix")?;
        let name = self
            .e
            .global_name_at(abs)
            .unwrap_or_else(|| format!("Ψ#{abs}"));
        let GlobalBinding::Tm { ty, body, .. } = &self.e.psi().bindings[abs] else {
            return Err(format!("`{name}` is not a term-level global"));
        };
        if body.is_none() {
            return Err(format!(
                "`{name}` has no elaborated body — proofs are opaque, so a call to \
                 it is outside the fragment"
            ));
        }
        let mut ty = &**ty;
        let mut arity = 0usize;
        while let Type::Pi { dom, cod, .. } = ty {
            if !matches!(&**dom, Type::Nat) {
                return Err(format!("callee `{name}`'s signature is outside the fragment"));
            }
            arity += 1;
            ty = cod;
        }
        if !matches!(ty, Type::Nat) {
            return Err(format!("callee `{name}`'s result type is not `Nat`"));
        }
        if arity == 0 {
            return Err(format!(
                "callee `{name}` is nullary: its marker would be a bare numeral, \
                 and a nullary fn is outside the fragment anyway"
            ));
        }
        let tag = match self.callees.iter().position(|c| *c == name) {
            Some(i) => i + 1,
            None => {
                self.callees.push(name);
                self.callees.len()
            }
        };
        Ok((tag as u32, arity))
    }
}

/// Replace every variable *occurrence* by a marker carrying its binder's
/// level and every cross-function call head by a callee marker, leaving
/// closed code (§1 of the transcriber design; §3 of the opaque-globals
/// design for the callee clause).
///
/// This is scope resolution, and it stays in Rust for a kernel reason rather
/// than for convenience: `elim^Trm`'s variable branch abstracts over the
/// variable at layer v (rec.rs `tm_var`) and its global scrutinee is neutral
/// (reduce.rs `is_neutral_term`), so nothing at layer m can observe *which*
/// variable or global an occurrence is. The pass itself is a mechanical
/// renaming to closed terms — no fragment knowledge beyond the callee
/// signature check, no walk order.
///
/// `depth` is the number of binders in scope, so the occupied levels are
/// `0..depth` and `Var(i)` is the binder at level `depth - 1 - i`.
fn mark(t: &Term, depth: u32, cx: &mut MarkCx<'_>) -> Result<Term, String> {
    Ok(match t {
        Term::Var(LocalVar(i)) => {
            if *i >= depth {
                return Err("a variable escapes the body's own binders".into());
            }
            marker(depth - 1 - i)
        }
        Term::Zero => Term::Zero,
        Term::Succ(p) => Term::Succ(Rc::new(mark(p, depth, cx)?)),
        // The fragment's one eliminator. Its motive must be `Nat` on the nose:
        // a motive that mentioned the scrutinee would put a *type* in the
        // walk's way, and this slice analyses terms (design doc §3).
        Term::ElimNat { level, motive, base, step, scrut } => {
            if !matches!(&**motive, Type::Nat) {
                return Err("the recursion's motive is not `Nat`".into());
            }
            Term::ElimNat {
                level: level.clone(),
                motive: Rc::clone(motive),
                base: Rc::new(mark(base, depth, cx)?),
                // `elim_Nat`'s step binds the predecessor and the induction
                // hypothesis, in that order, so their levels are `depth` and
                // `depth + 1` — which is the convention the walker reads back.
                step: Rc::new(mark(step, depth + 2, cx)?),
                scrut: Rc::new(mark(scrut, depth, cx)?),
            }
        }
        // A cross-function call: the head is a global reference, replaced by
        // a callee marker; the argument spine stays and is marked in place.
        // (`elim^Trm` is neutral on `box (u^δ)`, so a surviving reference
        // would stall the walk — the marker is what lifts the opacity, at
        // the reflection boundary and nowhere else.)
        Term::GlobalTm { var, .. } => {
            let (tag, arity) = cx.callee(*var)?;
            callee_marker(tag, arity)
        }
        Term::App { fun, dom_level, cod_level, dom, cod, arg } if global_head(t) => {
            Term::App {
                fun: Rc::new(mark(fun, depth, cx)?),
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
                arg: Rc::new(mark(arg, depth, cx)?),
            }
        }
        other => return Err(format!("`{other:?}` is outside the in-language fragment")),
    })
}

/// Is the head of this application spine a global reference?
fn global_head(mut t: &Term) -> bool {
    while let Term::App { fun, .. } = t {
        t = fun;
    }
    matches!(t, Term::GlobalTm { .. })
}

/// The Rust-side signature read: peel the body's `Lam` spine against the
/// type's Π spine, checking the fragment shape `Nat → … → Nat`, arity ≥ 1.
///
/// Since the reflection round (docs/fn-signature-reflection-design.md §§4–5)
/// this is **mechanical residue, not the fragment decision**: the decision is
/// `lib/certgen_code.hthr`'s `check_sig`, run by [`run_sig_checker`], and this
/// peel is kept because marking needs the body under its binders at a known
/// depth — its checks survive as the agreement oracle `generate_in_language`
/// compares the in-language verdict against.
fn sig_peel(e: &Elaborator, name: &str) -> Result<(usize, Term), String> {
    let Some((ty, body)) = e.global_body(name) else {
        return Err(format!("`{name}` has no elaborated body to analyse"));
    };
    let mut t = &*body;
    let mut ty = &*ty;
    let mut arity = 0usize;
    while let Term::Lam { body, .. } = t {
        let Type::Pi { dom, cod, .. } = ty else {
            return Err("the body has more binders than its type has parameters".into());
        };
        if !matches!(&**dom, Type::Nat) {
            return Err(format!("parameter {arity} of `{name}` is not `Nat`"));
        }
        arity += 1;
        t = body;
        ty = cod;
    }
    if !matches!(ty, Type::Nat) {
        return Err(format!("`{name}`'s result type is not `Nat`"));
    }
    if arity == 0 {
        return Err("a nullary fn has no calling convention to certify".into());
    }
    Ok((arity, t.clone()))
}

/// The body half of the pull reflection API
/// (docs/opaque-globals-analysis-design.md §2), reached publicly as
/// [`Elaborator::fn_body_code`]: arity, the callee-marker table, and the
/// marked body **boxed** — `Code(· ⊢ Nat)`, ready for the code recursor.
pub struct BodyCode {
    pub arity: usize,
    /// Callee-marker tags in first-occurrence order: tag `i + 1` is
    /// `callees[i]`; tag 0 is the enclosing fn itself (the ih marker's
    /// `PSelf`), which never appears here.
    pub callees: Vec<String>,
    pub code: Term,
}

/// [`sig_peel`] composed with [`mark`] and boxed — the primitive's body,
/// still run by `generate_in_language` after the agreement gate.
pub(crate) fn body_code(e: &Elaborator, name: &str) -> Result<BodyCode, String> {
    let (arity, body) = sig_peel(e, name)?;
    let caller_abs = e
        .global_abs(name)
        .ok_or_else(|| format!("`{name}` is not a declared global"))?;
    let mut cx = MarkCx { e, caller_abs, callees: Vec::new() };
    let marked = mark(&body, arity as u32, &mut cx)?;
    Ok(BodyCode { arity, callees: cx.callees, code: Term::BoxTm(Rc::new(marked)) })
}

// -- readback ---------------------------------------------------------------
//
// THE LOWERING SHAPES THIS READER ASSUMES, pinned here because they are an
// interface it cannot see change (docs/inductive-tier0-lowering.md §3.3,
// docs/inductive-tier1-wf-lowering.md §1):
//
//   * a tier-1 (recursive) inductive's value is `Supf { label, children }`;
//   * `label` is the tier-0 value of the constructor with its *recursive*
//     fields deleted: `inr^i(inl(payload))` picks constructor `i` of an
//     n-ary right-nested sum (the last constructor has no trailing `inl`),
//     and `payload` is `Pair(nominal tag, f₀, f₁, …, Triv)`, right-nested;
//   * `children` is the recursive fields in declaration order, as a
//     `Pair`-chain ending in `Triv`.
//
// If a lowering round changes any of that, every read here **declines** with
// the branch it could not recognize — it cannot silently read the wrong
// constructor, because a shape that is not one of these is not a shape it has
// a case for. That is the property that lets the reader be this literal.

/// The IR as read back: `certgen`'s own model, not the library's.
#[derive(Debug)]
enum RIr {
    Ret(Vec<u64>),
    LetCon { tag: u64, args: Vec<u64>, rest: Box<RIr> },
    LetMatch { scrut: u64, arms: Vec<RIr>, rest: Box<RIr> },
    LetCall { callee: u64, args: Vec<u64>, rest: Box<RIr> },
}

struct Reader<'a> {
    psi: &'a heather_kernel::term::GlobalCtx,
    /// Instructions read so far. The reader walks a value produced by a
    /// *library file*, which may be wrong in any way at all, so its own
    /// traversal is budgeted like everything else here: past the budget it
    /// declines rather than recursing (CLAUDE.md's runaway discipline —
    /// reduction is recursive, and a deep enough value overflows the stack
    /// before any fuel counter notices).
    budget: std::cell::Cell<u32>,
}

/// Instructions one transcription may contain. A fragment body compiles to a
/// handful; four figures is generous and still nowhere near the stack.
const READ_BUDGET: u32 = 4096;

impl Reader<'_> {
    fn whnf(&self, t: &Term) -> Result<Term, String> {
        let empty = LocalCtx::nil();
        reduce::whnf_term_delta(t, &empty, Defs::transparent(self.psi), FUEL)
            .map_err(|_| "the transcriber ran out of fuel".to_string())
    }

    /// `(constructor index, non-recursive fields, recursive children)`.
    fn ctor(&self, t: &Term, ctors: usize) -> Result<(usize, Vec<Term>, Vec<Term>), String> {
        let w = self.whnf(t)?;
        let (label, children) = match &w {
            Term::Supf { label, children, .. } => {
                ((**label).clone(), self.spine(children)?)
            }
            // A non-recursive inductive is the bare tier-0 value.
            other => (other.clone(), vec![]),
        };
        let mut v = self.whnf(&label)?;
        let mut idx = 0usize;
        loop {
            match v {
                Term::Inl { val, .. } => {
                    v = self.whnf(&val)?;
                    break;
                }
                Term::Inr { val, .. } => {
                    idx += 1;
                    if idx >= ctors {
                        return Err("a sum value deeper than the constructor list".into());
                    }
                    v = self.whnf(&val)?;
                }
                _ => break,
            }
        }
        // `Pair(nominal tag, fields…)`: the tag distinguishes structurally
        // identical declarations and says nothing about the value.
        let Term::Pair { snd, .. } = &v else {
            return Err(format!("a constructor payload that is not a pair: {v:?}"));
        };
        Ok((idx, self.spine(snd)?, children))
    }

    /// A right-nested `Pair` chain ending in `Triv`.
    fn spine(&self, t: &Term) -> Result<Vec<Term>, String> {
        let mut out = Vec::new();
        let mut v = self.whnf(t)?;
        loop {
            match v {
                Term::Triv { .. } => return Ok(out),
                Term::Pair { fst, snd, .. } => {
                    out.push((*fst).clone());
                    v = self.whnf(&snd)?;
                }
                other => return Err(format!("a tuple that is not a pair chain: {other:?}")),
            }
        }
    }

    fn nat(&self, t: &Term) -> Result<u64, String> {
        let mut v = self.whnf(t)?;
        let mut n = 0;
        loop {
            match v {
                Term::Zero => return Ok(n),
                Term::Succ(p) => {
                    n += 1;
                    if n > 1_000_000 {
                        return Err("an implausible numeral".into());
                    }
                    v = self.whnf(&p)?;
                }
                other => return Err(format!("a Nat that is not a numeral: {other:?}")),
            }
        }
    }

    /// `Refs { RNil, RCons(i: Nat, next: Refs) }`.
    fn refs(&self, t: &Term) -> Result<Vec<u64>, String> {
        let (idx, fields, children) = self.ctor(t, 2)?;
        match idx {
            0 => Ok(vec![]),
            1 => {
                let i = self.nat(fields.first().ok_or("RCons without its index")?)?;
                let mut rest = self.refs(children.first().ok_or("RCons without its tail")?)?;
                rest.insert(0, i);
                Ok(rest)
            }
            _ => Err("not a `Refs` value".into()),
        }
    }

    /// `Ir`, in `lib/ir_v1.hthr`'s declaration order. The instruction forms
    /// outside the fragment (`LetLoop`, `LoopIter`) decline: the in-language
    /// transcriber never emits them, so reading one means the value is not
    /// what this reader was pointed at.
    fn ir(&self, t: &Term) -> Result<RIr, String> {
        let left = self.budget.get();
        if left == 0 {
            return Err("the transcription is implausibly large — declining".into());
        }
        self.budget.set(left - 1);
        let (idx, fields, children) = self.ctor(t, 8)?;
        let f = |i: usize| fields.get(i).ok_or_else(|| "a missing field".to_string());
        let c = |i: usize| children.get(i).ok_or_else(|| "a missing sub-Ir".to_string());
        match idx {
            0 => Ok(RIr::Ret(self.refs(f(0)?)?)),
            1 => Ok(RIr::LetCon {
                tag: self.nat(f(0)?)?,
                args: self.refs(f(1)?)?,
                rest: Box::new(self.ir(c(0)?)?),
            }),
            2 => Ok(RIr::LetMatch {
                scrut: self.nat(f(0)?)?,
                arms: self.arms(c(0)?)?,
                rest: Box::new(self.ir(c(1)?)?),
            }),
            3 | 4 => Err("an arm cell where an instruction was expected".into()),
            7 => Ok(RIr::LetCall {
                callee: self.nat(f(0)?)?,
                args: self.refs(f(1)?)?,
                rest: Box::new(self.ir(c(0)?)?),
            }),
            _ => Err("an instruction outside the transcriber's fragment".into()),
        }
    }

    fn arms(&self, t: &Term) -> Result<Vec<RIr>, String> {
        let (idx, _, children) = self.ctor(t, 8)?;
        match idx {
            4 => Ok(vec![]),
            3 => {
                let head = self.ir(children.first().ok_or("an arm without a body")?)?;
                let mut rest = self.arms(children.get(1).ok_or("an arm without a tail")?)?;
                rest.insert(0, head);
                Ok(rest)
            }
            _ => Err("an arm chain that is neither `Arm` nor `NoArm`".into()),
        }
    }
}

// -- the certificate expression, as read back -------------------------------
//
// `lib/certgen_cert.hthr`'s `Cert`/`CertOut`, with the two things the readback
// owns already applied: the walker's callee TAGS resolved to names
// (convention 1 there), and `CStuck` turned into a decline. Everything else is
// carried across unchanged, because everything else is the fold's answer.

#[derive(Clone, Debug)]
enum RCert {
    Ret { rs: Vec<usize> },
    Con { tag: u64, args: Vec<usize>, hr: Box<RCert> },
    /// A self-call, whose certificate is the induction hypothesis.
    Ih { args: Vec<usize>, hr: Box<RCert> },
    Call { callee: String, args: Vec<usize>, hr: Box<RCert> },
    Match { scrut: usize, ctag: u64, ha: Box<RCert>, hr: Box<RCert> },
}

#[derive(Clone, Debug)]
enum RCertOut {
    Plain(RCert),
    Rec { scrut: usize, zero: RCert, succ: RCert },
}

impl Reader<'_> {
    /// `Cert`, in `lib/certgen_cert.hthr`'s declaration order. `callees` is
    /// the reflection table a foreign tag `c ≥ 1` indexes; the self-call
    /// carries no name, because `CIh` says whose it is.
    fn cert(&self, t: &Term, callees: &[String]) -> Result<RCert, String> {
        let left = self.budget.get();
        if left == 0 {
            return Err("the certificate is implausibly large — declining".into());
        }
        self.budget.set(left - 1);
        let (idx, fields, children) = self.ctor(t, 6)?;
        let f = |i: usize| fields.get(i).ok_or_else(|| "a missing field".to_string());
        let c = |i: usize| children.get(i).ok_or_else(|| "a missing sub-certificate".to_string());
        let dists = |rs: Vec<u64>| rs.into_iter().map(|d| d as usize).collect::<Vec<usize>>();
        match idx {
            // `CStuck`: the fold's decline, and the only one it makes. The
            // reasons live here, at the rim, as they do for `TNo`/`SigNo`.
            0 => Err("the in-language certificate fold declined this IR".into()),
            1 => Ok(RCert::Ret { rs: dists(self.refs(f(0)?)?) }),
            2 => Ok(RCert::Con {
                tag: self.nat(f(0)?)?,
                args: dists(self.refs(f(1)?)?),
                hr: Box::new(self.cert(c(0)?, callees)?),
            }),
            3 => Ok(RCert::Ih {
                args: dists(self.refs(f(0)?)?),
                hr: Box::new(self.cert(c(0)?, callees)?),
            }),
            4 => {
                let tag = self.nat(f(0)?)?;
                // Convention 1: tag 0 is the enclosing fn, and the fold routes
                // it to `CIh` — a `CCall(0, …)` is a fold that lost track of
                // whose certificate it was applying.
                let callee = callees
                    .get(tag.checked_sub(1).ok_or("a foreign call at the self tag")? as usize)
                    .cloned()
                    .ok_or("a callee tag outside the reflection table")?;
                Ok(RCert::Call {
                    callee,
                    args: dists(self.refs(f(1)?)?),
                    hr: Box::new(self.cert(c(0)?, callees)?),
                })
            }
            5 => Ok(RCert::Match {
                scrut: self.nat(f(0)?)? as usize,
                ctag: self.nat(f(1)?)?,
                ha: Box::new(self.cert(c(0)?, callees)?),
                hr: Box::new(self.cert(c(1)?, callees)?),
            }),
            _ => Err("not a `Cert` value".into()),
        }
    }

    fn cert_out(&self, t: &Term, callees: &[String]) -> Result<RCertOut, String> {
        let (idx, fields, _) = self.ctor(t, 2)?;
        let f = |i: usize| fields.get(i).ok_or_else(|| "a missing field".to_string());
        match idx {
            0 => Ok(RCertOut::Plain(self.cert(f(0)?, callees)?)),
            1 => Ok(RCertOut::Rec {
                scrut: self.nat(f(0)?)? as usize,
                zero: self.cert(f(1)?, callees)?,
                succ: self.cert(f(2)?, callees)?,
            }),
            _ => Err("the certificate fold's answer is not a `CertOut`".into()),
        }
    }
}

// -- invocation and reconstruction ------------------------------------------

/// Apply the analyzer registered at `slot` to `(Γ = ·, args…)`.
///
/// The application spine is built in the **slot's** canonical order, which is
/// what analyzer registration buys: whole-signature convertibility fixes the Π
/// order, so this code does not consult the template's own signature at all
/// (docs/meta-def-registration-design.md, analyzer extension).
fn analyzer_app(
    e: &Elaborator,
    slot: Slot,
    path: &str,
    args: Vec<Term>,
) -> Result<Term, String> {
    let md = e
        .analyzer_def(slot)
        .ok_or_else(|| format!("no `meta fn … for {path}` is registered"))?;
    let empty = LocalCtx::nil();
    // Rescoped to the Ψ this call sees: a meta definition is elaborator-held,
    // so its global references are stale by however much Ψ has grown since it
    // was registered (`MetaDef::psi_len`) — and an analyzer's arms are made of
    // calls to library globals, so every one of them is affected.
    let (md_term, md_stmt) = md.at(e.psi().bindings.len());
    let Type::CtxPi { body, .. } = &*md_stmt else {
        return Err(format!("the `{path}` analyzer does not open with a `Ctx` binder"));
    };
    let mut ty = body.apply_global(&GlobalSubst {
        entries: vec![GlobalEntry::Ctx(empty.clone())],
    });
    let mut term = Term::CtxApp { fun: md_term, ctx: empty.clone() };
    for arg in args {
        let Type::Pi { dom_level, cod_level, dom, cod } = ty else {
            return Err(format!("the `{path}` analyzer's signature ran out of parameters"));
        };
        let arg = Rc::new(arg);
        term = Term::App {
            fun: Rc::new(term),
            dom_level,
            cod_level: cod_level.clone(),
            dom,
            cod: Rc::clone(&cod),
            arg: Rc::clone(&arg),
        };
        ty = (*cod).clone().apply_local(&LocalSubst::id(&empty).extended(arg));
    }
    Ok(term)
}

/// Apply the registered transcriber to `(Γ = ·, arity, the boxed marked
/// body)` and read its answer back — both as `RIr`, the model the emitters
/// consume, and as the `Ir` **term** itself, which is what the certificate
/// fold is applied to (`run_cert_fold`). Handing the term over rather than
/// rebuilding one is what lets the fold see exactly the value the transcriber
/// produced: there is no second encoding of an `Ir` anywhere.
fn run_transcriber(e: &Elaborator, arity: usize, code: Term) -> Result<(RIr, Term), String> {
    let mut nat = Term::Zero;
    for _ in 0..arity {
        nat = Term::Succ(Rc::new(nat));
    }
    let term = analyzer_app(
        e,
        Slot::CertgenTranscribe,
        "certgen.transcribe",
        vec![nat, code],
    )?;
    // Evaluation is **spine-directed**: `Reader::whnf` reduces only what it is
    // about to inspect, so nothing ever normalizes a whole IR tree at once
    // (CLAUDE.md's memory discipline).
    let r = Reader { psi: e.psi(), budget: std::cell::Cell::new(READ_BUDGET) };
    let (idx, fields, _) = r.ctor(&term, 2)?;
    match idx {
        0 => Err("the in-language transcriber declined this body".into()),
        1 => {
            let ir = fields.first().ok_or("`TYes` without its IR")?;
            Ok((r.ir(ir)?, ir.clone()))
        }
        _ => Err("the transcriber's answer is not a `TOut`".into()),
    }
}

/// `u^δ` for a program-layer global, with its type, at the empty context —
/// the construction `resolve.rs`'s `derived_ref` makes for a written name
/// (`GlobalVar(|Ψ| - 1 - abs)` and the empty delayed substitution) and the
/// `shift_global` rescope `Elaborator::fn_type_code` makes for a reflected
/// one. A Ψ global needs no staleness bookkeeping of its own: unlike a
/// `MetaDef` it *is* Ψ-resident.
fn global_app(e: &Elaborator, name: &str, args: Vec<Term>) -> Result<Term, String> {
    let abs = e
        .global_abs(name)
        .ok_or_else(|| format!("`{name}` is not declared — the certificate fold is a library file"))?;
    let GlobalBinding::Tm { ty, .. } = &e.psi().bindings[abs] else {
        return Err(format!("`{name}` is not a term-level global"));
    };
    let len = e.psi().bindings.len();
    let empty = LocalCtx::nil();
    let mut ty = Rc::new(ty.shift_global((len - abs) as u32));
    let mut term = Term::GlobalTm {
        var: GlobalVar((len - 1 - abs) as u32),
        subst: LocalSubst::id(&empty),
    };
    for arg in args {
        let Type::Pi { dom_level, cod_level, dom, cod } = &*ty else {
            return Err(format!("`{name}`'s signature ran out of parameters"));
        };
        let arg = Rc::new(arg);
        term = Term::App {
            fun: Rc::new(term),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
            arg: Rc::clone(&arg),
        };
        ty = Rc::new((**cod).clone().apply_local(&LocalSubst::id(&empty).extended(arg)));
    }
    Ok(term)
}

/// The certificate fold (docs/certgen-cert-expression-design.md §5): apply
/// `lib/certgen_cert.hthr`'s `cert_body` to the transcriber's `Ir` and read
/// the certificate expression back.
///
/// No analyzer slot, and no `meta fn`: the fold is a program-layer function of
/// one `Ir`, so an ordinary application is the whole invocation — which is
/// also what keeps it off the 52-branch `rec_ga` gate every `match code` shell
/// pays. Evaluation is the same spine-directed WHNF under the same budgets as
/// every other readback here.
fn run_cert_fold(e: &Elaborator, ir: Term, callees: &[String]) -> Result<RCertOut, String> {
    let term = global_app(e, "cert_body", vec![ir])?;
    let r = Reader { psi: e.psi(), budget: std::cell::Cell::new(READ_BUDGET) };
    r.cert_out(&term, callees)
}

/// The in-language fragment-signature verdict
/// (docs/fn-signature-reflection-design.md §§1–2): **pull** the fn's type as
/// code (`Elaborator::fn_type_code`, the reflection primitive), apply the
/// registered `certgen.check_sig` analyzer to it, and read back its `SigOut` —
/// the fragment arity, or a decline.
///
/// The decline carries one honest sentence rather than a per-shape reason:
/// the library's decline discipline is a single value (`SigNo`, like the
/// walker's `TStuck`), and reasons live at this rim.
fn run_sig_checker(e: &Elaborator, name: &str) -> Result<u64, String> {
    let sig = e
        .fn_type_code(name)
        .ok_or_else(|| format!("`{name}` has no declared type to reflect"))?;
    let term = analyzer_app(e, Slot::CertgenCheckSig, "certgen.check_sig", vec![sig])?;
    let r = Reader { psi: e.psi(), budget: std::cell::Cell::new(READ_BUDGET) };
    let (idx, fields, _) = r.ctor(&term, 2)?;
    match idx {
        0 => Err(format!(
            "the in-language signature checker declined `{name}`: the fragment \
             signature is `Nat -> … -> Nat` with at least one parameter"
        )),
        1 => r.nat(fields.first().ok_or("`SigYes` without its arity")?),
        _ => Err("the signature checker's answer is not a `SigOut`".into()),
    }
}

/// One instruction chain as the emitters' model: slots, tags and callee
/// *names*. The spec expressions this used to derive alongside are the
/// certificate renderer's now (docs/certgen-cert-expression-design.md §3), so
/// what is left is the structure the chain renderer, the closure computation
/// and the fixture evaluator read — plus the environment-depth check, which
/// stays because a reference past the environment is a misread value, not a
/// naming question.
fn chain_from_rir(
    ir: &RIr,
    name: &str,
    callees: &[String],
    depth: usize,
) -> Result<Chain, String> {
    let mut depth = depth;
    let mut instrs = Vec::new();
    let mut has_self_call = false;
    let mut cur = ir;
    let inrange = |d: u64, depth: usize| -> Result<usize, String> {
        ((d as usize) < depth)
            .then_some(d as usize)
            .ok_or_else(|| "an instruction reading past the environment".to_string())
    };
    loop {
        match cur {
            RIr::Ret(rs) => {
                let [d] = rs[..] else {
                    return Err("a `Ret` with other than one output".into());
                };
                return Ok(Chain { instrs, ret_dist: inrange(d, depth)?, has_self_call });
            }
            RIr::LetCon { tag, args, rest } => {
                if !matches!(tag, 0 | 1) {
                    return Err(format!("constructor tag {tag} is not a `Nat`"));
                }
                let dists: Vec<usize> = args
                    .iter()
                    .map(|d| inrange(*d, depth))
                    .collect::<Result<_, _>>()?;
                instrs.push(Instr::Con { tag: *tag, dists });
                depth += 1;
                cur = rest;
            }
            RIr::LetCall { callee, args, rest } => {
                // The walker's numbering (lib/certgen_code.hthr convention
                // 3): 0 is the enclosing fn itself, `c ≥ 1` is
                // `callees[c - 1]` from the body-reflection table. Names,
                // not closure indices — this is the one place the walker's
                // numbering is converted, and the emitters compute the
                // program closure from the names, downstream.
                let cname = if *callee == 0 {
                    name
                } else {
                    callees
                        .get(*callee as usize - 1)
                        .map(String::as_str)
                        .ok_or("a callee tag outside the reflection table")?
                };
                let dists: Vec<usize> = args
                    .iter()
                    .map(|d| inrange(*d, depth))
                    .collect::<Result<_, _>>()?;
                has_self_call |= *callee == 0;
                instrs.push(Instr::Call { callee: cname.to_string(), dists });
                depth += 1;
                cur = rest;
            }
            RIr::LetMatch { .. } => {
                return Err("a nested `LetMatch` is outside the fragment".into());
            }
        }
    }
}

/// `FnIr` from the read-back IR. The recursion index, the arm split and every
/// spec expression are *recovered* from the instruction chain — the walker has
/// no names to hand over, and does not need any.
fn fn_ir_from_rir(
    ir: &RIr,
    name: &str,
    callees: &[String],
    params: &[String],
) -> Result<FnIr, String> {
    let params: Vec<String> = params.to_vec();
    match ir {
        RIr::LetMatch { scrut, arms, rest } => {
            if !matches!(&**rest, RIr::Ret(rs) if rs[..] == [0]) {
                return Err("a `LetMatch` whose continuation is not the rebinding `Ret`"
                    .into());
            }
            let [zero, succ] = &arms[..] else {
                return Err("a `LetMatch` with other than two arms is not a `Nat` match"
                    .into());
            };
            let zc = chain_from_rir(zero, name, callees, params.len())?;
            if zc.has_self_call {
                return Err("a self-call in the Zero arm cannot be structural".into());
            }
            let sc = chain_from_rir(succ, name, callees, params.len() + 1)?;
            Ok(FnIr {
                params,
                kind: FnIrKind::Rec(RecIr { rec_idx: *scrut as usize, zero: zc, succ: sc }),
            })
        }
        _ => {
            let c = chain_from_rir(ir, name, callees, params.len())?;
            if c.has_self_call {
                return Err("a self-call outside a match is outside the fragment".into());
            }
            Ok(FnIr { params, kind: FnIrKind::Plain(c) })
        }
    }
}

/// Generate for `d`: the elaborator marks `d`'s elaborated body, the
/// registered analyzer walks it, its `Ir` is read back into the model the
/// emitters consume, and the in-language fold turns that same `Ir` into the
/// certificate expression they render.
///
/// `d` must already be elaborated into `e` (it is an ordinary declaration) —
/// the analysis reads Ψ, not the AST, and a fn the elaborator has not seen has
/// nothing to analyse. Every failure is a decline.
pub fn generate_in_language(
    e: &Elaborator,
    d: &Decl,
    ctx: &GenCtx,
) -> Result<Emission, String> {
    // The signature DECISION is in-language (docs/fn-signature-reflection-
    // design.md §4), consulted before [`surface_params`]'s name checks so a
    // signature decline is the checker's — and compared against the Rust
    // peel, whose checks survive as the agreement oracle. Disagreement is a
    // fragment-definition drift: still an `Err` (the generator must not
    // panic), but one the tests assert never fires.
    let sig = run_sig_checker(e, &d.name);
    let peel = sig_peel(e, &d.name);
    let arity = match (&sig, &peel) {
        (Ok(k), Ok((arity, _))) if *k as usize == *arity => *arity,
        (Err(reason), Err(_)) => return Err(reason.clone()),
        (s, p) => {
            return Err(format!(
                "signature disagreement between the in-language checker and the Rust \
                 peel for `{}` — a fragment-definition drift, not a decline: \
                 in-language {s:?}, Rust {p:?}",
                d.name
            ));
        }
    };
    let names = surface_params(d)?;
    let f = d.name.as_str();
    // The pull primitive: marked, closed, boxed code plus the callee-marker
    // table the readback resolves `LetCall` tags against
    // (docs/opaque-globals-analysis-design.md §§2–4).
    let body = e.fn_body_code(f)?;
    debug_assert_eq!(body.arity, arity);
    if arity != names.len() {
        return Err("the elaborated body's arity disagrees with the declaration".into());
    }
    let (rir, ir) = run_transcriber(e, arity, body.code)?;
    let params: Vec<String> = names.iter().map(|s| s.to_string()).collect();
    let model = fn_ir_from_rir(&rir, f, &body.callees, &params)?;
    // The certificate FOLD, over the same `Ir` value the model came from
    // (docs/certgen-cert-expression-design.md): which kit lemma applies where,
    // and whether a call consumes the induction hypothesis, is decided in
    // `lib/certgen_cert.hthr`; what comes back is a certificate expression the
    // emitters render.
    let cert = run_cert_fold(e, ir, &body.callees)?;
    emit_with_model(f, arity, model, cert, ctx)
}
