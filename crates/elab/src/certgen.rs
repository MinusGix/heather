//! The certifying generator, v2 (docs/certifying-generator-design.md §8
//! item 1; the v1 narrative is in the issue log).
//!
//! A transpiler: it consumes the parsed surface AST of a `fn` in the
//! fragment (Nat-only signature, at most one `match` on one parameter, arms
//! built from constructors and calls with at most one structural self-call)
//! and emits *surface text* — the IR, the ∃-form invariant, and a
//! `CompileNatK` instance value — to be checked appended to
//! `lib/ir_v1.hthr` by the ordinary pipeline. The generator is untrusted by
//! architecture: everything it emits is kernel-checked, so it may decline
//! (`Err` with a reason) and a bug in it is a check failure, never an
//! unsound theorem.
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

use heather_syntax::ast::{Decl, DeclKind, Expr, ExprKind, TyKind};

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

pub fn generate(d: &Decl, ctx: &GenCtx) -> Result<Emission, String> {
    generate_inner(d, ctx, false)
}

/// Test-only in spirit: transcribe a call to an *unknown* function as if it
/// were the self-call. The emission is wrong by construction and its
/// certificate must fail to check — the fragment-honesty negative control.
pub fn generate_forced(d: &Decl, ctx: &GenCtx) -> Result<Emission, String> {
    generate_inner(d, ctx, true)
}

// ---------------------------------------------------------------------------
// Fragment check

struct Frag<'a> {
    name: &'a str,
    params: Vec<&'a str>,
    kind: FragKind<'a>,
}

enum FragKind<'a> {
    Plain(&'a Expr),
    Rec { rec_idx: usize, zero: &'a Expr, succ_binder: &'a str, succ: &'a Expr },
}

/// Names the emitted proofs bind; a source function whose parameters shadow
/// them is declined rather than renamed around.
const RESERVED: [&str; 3] = ["gz", "gk", "gih"];

fn fragment<'a>(d: &'a Decl) -> Result<Frag<'a>, String> {
    if d.kind != DeclKind::Fn {
        return Err("not a fn".into());
    }
    if !d.tyvars.is_empty() {
        return Err("type parameters are outside the fragment".into());
    }
    if d.params.is_empty() {
        return Err("a nullary fn has no calling convention to certify".into());
    }
    for p in &d.params {
        if !matches!(p.ty.kind, TyKind::Nat) {
            return Err(format!("parameter `{}` is not Nat", p.name));
        }
        if p.implicit {
            return Err(format!("parameter `{}` is implicit", p.name));
        }
        if RESERVED.contains(&p.name.as_str()) {
            return Err(format!("parameter `{}` collides with an emitted binder", p.name));
        }
    }
    if !matches!(d.result.kind, TyKind::Nat) {
        return Err("result type is not Nat".into());
    }
    if !d.body.stmts.is_empty() || !d.body.ons.is_empty() {
        return Err("let/on statements are outside the fragment".into());
    }
    let params: Vec<&str> = d.params.iter().map(|p| p.name.as_str()).collect();
    let kind = match &d.body.result.kind {
        ExprKind::Match { scrut, eqbind, motive, arms } => {
            if motive.is_some() {
                return Err("an explicit motive is outside the fragment".into());
            }
            if eqbind.is_some() {
                return Err("an equation binder is outside the fragment".into());
            }
            let ExprKind::Var(sname) = &scrut.kind else {
                return Err("the match scrutinee is not a parameter".into());
            };
            let Some(rec_idx) = params.iter().position(|p| p == sname) else {
                return Err("the match scrutinee is not a parameter".into());
            };
            let mut zero = None;
            let mut succ = None;
            for arm in arms {
                match arm.ctor.as_str() {
                    "Zero" if arm.binders.is_empty() => zero = Some(&arm.body),
                    "Succ" if arm.binders.len() == 1 => {
                        succ = Some((arm.binders[0].name(), &arm.body));
                    }
                    _ => return Err(format!("arm `{}` is not a fragment Nat arm", arm.ctor)),
                }
            }
            let (Some(zero), Some((succ_binder, succ))) = (zero, succ) else {
                return Err("match does not have exactly Zero and Succ(k) arms".into());
            };
            if RESERVED.contains(&succ_binder) {
                return Err(format!("binder `{succ_binder}` collides with an emitted binder"));
            }
            FragKind::Rec { rec_idx, zero, succ_binder, succ }
        }
        _ => FragKind::Plain(&d.body.result),
    };
    Ok(Frag { name: &d.name, params, kind })
}

// ---------------------------------------------------------------------------
// Transcription model. References are de Bruijn distances into a cons
// environment (0 = most recent). Bindings are tracked by birth order — id
// `i` at depth `d` is distance `d - 1 - i`. Each instruction carries the
// SPEC expression its result stands for (the source sub-expression, with
// the Succ-arm binder spelled `gk`), which is what the ∃-proof emission
// spells into environments, gathered fields and callee certificates.

#[derive(Clone)]
enum Instr {
    Con { tag: u64, dists: Vec<usize>, spec: String },
    Call { callee: String, dists: Vec<usize>, arg_specs: Vec<String>, spec: String },
}

#[derive(Clone)]
struct Chain {
    instrs: Vec<Instr>,
    ret_dist: usize,
    /// The spec expression of the value at the return slot.
    ret_spec: String,
    has_self_call: bool,
}

#[derive(Clone)]
enum Binding {
    Param(usize),
    Field,
    Temp(String),
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

struct Compiler<'a> {
    frag: &'a Frag<'a>,
    ctx: &'a GenCtx,
    ids: Vec<Binding>,
    instrs: Vec<Instr>,
    has_self_call: bool,
    in_succ_arm: bool,
    forced: bool,
}

impl<'a> Compiler<'a> {
    fn depth(&self) -> usize {
        self.ids.len()
    }

    fn dist(&self, id: usize) -> usize {
        self.depth() - 1 - id
    }

    fn succ_binder(&self) -> Option<&str> {
        match &self.frag.kind {
            FragKind::Rec { succ_binder, .. } => Some(succ_binder),
            FragKind::Plain(_) => None,
        }
    }

    fn lookup(&self, name: &str) -> Result<usize, String> {
        // The field shadows a same-named parameter, so scan newest-first.
        for (i, b) in self.ids.iter().enumerate().rev() {
            let hit = match b {
                Binding::Param(p) => self.frag.params[*p] == name,
                Binding::Field => self.in_succ_arm && self.succ_binder() == Some(name),
                Binding::Temp(_) => false,
            };
            if hit {
                return Ok(i);
            }
        }
        Err(format!("`{name}` is not in scope in the arm"))
    }

    /// The spec expression a binding stands for (arm binder spelled `gk`).
    fn spec_of(&self, id: usize) -> String {
        match &self.ids[id] {
            Binding::Param(p) => self.frag.params[*p].to_string(),
            Binding::Field => "gk".to_string(),
            Binding::Temp(s) => s.clone(),
        }
    }

    fn push(&mut self, b: Binding) -> usize {
        self.ids.push(b);
        self.ids.len() - 1
    }

    fn emit_con(&mut self, tag: u64, arg_ids: &[usize], spec: String) -> usize {
        let dists = arg_ids.iter().map(|&i| self.dist(i)).collect();
        self.instrs.push(Instr::Con { tag, dists, spec: spec.clone() });
        self.push(Binding::Temp(spec))
    }

    fn emit_call(&mut self, callee: &str, arg_ids: &[usize], spec: String) -> usize {
        let dists = arg_ids.iter().map(|&i| self.dist(i)).collect();
        let arg_specs = arg_ids.iter().map(|&i| self.spec_of(i)).collect();
        self.instrs.push(Instr::Call {
            callee: callee.to_string(),
            dists,
            arg_specs,
            spec: spec.clone(),
        });
        self.push(Binding::Temp(spec))
    }

    fn call_spec(&self, f: &str, arg_ids: &[usize]) -> String {
        let args: Vec<String> = arg_ids.iter().map(|&i| self.spec_of(i)).collect();
        format!("{f}({})", args.join(", "))
    }

    /// Compile an expression, returning the binding id of its value.
    fn compile(&mut self, e: &Expr) -> Result<usize, String> {
        match &e.kind {
            ExprKind::Var(x) if x == "Zero" => Ok(self.emit_con(0, &[], "Zero".into())),
            ExprKind::Var(x) => self.lookup(x),
            ExprKind::Num(n) => {
                let mut id = self.emit_con(0, &[], "0".into());
                for k in 0..*n {
                    id = self.emit_con(1, &[id], format!("{}", k + 1));
                }
                Ok(id)
            }
            _ => {
                let Some((head, args, _)) = e.as_named() else {
                    return Err("expression form outside the fragment".into());
                };
                match head {
                    "Succ" if args.len() == 1 => {
                        let a = self.compile(&args[0])?;
                        let spec = format!("Succ({})", self.spec_of(a));
                        Ok(self.emit_con(1, &[a], spec))
                    }
                    "Zero" if args.is_empty() => Ok(self.emit_con(0, &[], "Zero".into())),
                    name if name == self.frag.name => {
                        if self.has_self_call {
                            return Err("more than one self-call in an arm".into());
                        }
                        if !self.in_succ_arm {
                            return Err("a self-call outside the Succ arm".into());
                        }
                        let FragKind::Rec { rec_idx, succ_binder, .. } = &self.frag.kind else {
                            unreachable!()
                        };
                        if args.len() != self.frag.params.len() {
                            return Err("self-call arity mismatch".into());
                        }
                        let mut ids = Vec::new();
                        for (i, a) in args.iter().enumerate() {
                            let ExprKind::Var(v) = &a.kind else {
                                return Err("self-call argument is not a variable".into());
                            };
                            let want = if i == *rec_idx { *succ_binder } else { self.frag.params[i] };
                            if v != want {
                                return Err(format!(
                                    "self-call is not structural: argument {i} is `{v}`, wanted `{want}`"
                                ));
                            }
                            ids.push(self.lookup(v)?);
                        }
                        let spec = self.call_spec(self.frag.name, &ids);
                        self.has_self_call = true;
                        Ok(self.emit_call(self.frag.name, &ids, spec))
                    }
                    other => {
                        let known = self.ctx.get(other).is_some();
                        if !known && !self.forced {
                            return Err(format!(
                                "call to `{other}`, which has no generated instance in the context"
                            ));
                        }
                        let mut ids = Vec::new();
                        for a in args {
                            ids.push(self.compile(a)?);
                        }
                        if known {
                            if ids.len() != self.ctx.get(other).unwrap().arity {
                                return Err(format!("call to `{other}` has the wrong arity"));
                            }
                            let spec = self.call_spec(other, &ids);
                            Ok(self.emit_call(other, &ids, spec))
                        } else {
                            // Forced mode: transcribe an unknown call as if
                            // it were the self-call. Wrong on purpose.
                            if self.has_self_call {
                                return Err("more than one call in an arm (forced)".into());
                            }
                            let spec = self.call_spec(self.frag.name, &ids);
                            self.has_self_call = true;
                            Ok(self.emit_call(self.frag.name, &ids, spec))
                        }
                    }
                }
            }
        }
    }
}

fn compile_arm(
    frag: &Frag<'_>,
    ctx: &GenCtx,
    in_succ_arm: bool,
    body: &Expr,
    forced: bool,
) -> Result<Chain, String> {
    let mut ids: Vec<Binding> = (0..frag.params.len()).rev().map(Binding::Param).collect();
    if in_succ_arm {
        ids.push(Binding::Field);
    }
    let mut c = Compiler {
        frag,
        ctx,
        ids,
        instrs: Vec::new(),
        has_self_call: false,
        in_succ_arm,
        forced,
    };
    let result = c.compile(body)?;
    let ret_dist = c.dist(result);
    let ret_spec = c.spec_of(result);
    Ok(Chain { instrs: c.instrs, ret_dist, ret_spec, has_self_call: c.has_self_call })
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
            Instr::Con { tag, dists, .. } => format!("LetCon({tag}, {}, {s})", refs(dists)),
            Instr::Call { callee, dists, .. } => {
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
            Instr::Con { tag, dists, .. } => {
                let v = if *tag == 0 { V(0) } else { V(env[dists[0]].0 + 1) };
                env.insert(0, v);
                let (out, n) = self.run_from(c, from + 1, env);
                (out, 1 + n)
            }
            Instr::Call { callee, dists, .. } => {
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
// The ∃-proof emission: fold the composition kit over a chain.

struct ProofCx<'a> {
    prog: String,
    closure: &'a [String],
    conv_name: &'a dyn Fn(&str) -> String,
    ctx: &'a GenCtx,
    /// The closure member whose invariant is being proved (its self-calls
    /// consume `gih`); `None` outside a Succ arm.
    self_name: &'a str,
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

/// The `Converges` proof term for `instrs[from..] ; Ret`, in environment
/// `env_exprs ++ tail`, converging to `Out(out_text(final_spec))`.
fn conv_of_chain(
    cx: &ProofCx<'_>,
    c: &Chain,
    from: usize,
    env_exprs: &[String],
    tail: &str,
    final_spec: &str,
) -> String {
    let p = &cx.prog;
    let env = env_text(env_exprs, tail);
    let vs = out_text(final_spec);
    if from == c.instrs.len() {
        return format!("ret_conv({p}, {env}, RCons({}, RNil), {vs}, refl)", c.ret_dist);
    }
    let rest_ir = render_chain(&c.instrs, from + 1, c.ret_dist, cx.closure);
    match &c.instrs[from] {
        Instr::Con { tag, dists, spec } => {
            let arg_exprs: Vec<String> = dists.iter().map(|&d| env_exprs[d].clone()).collect();
            let fs = env_text(&arg_exprs, "VNil");
            let mut env2 = vec![spec.clone()];
            env2.extend(env_exprs.iter().cloned());
            let hr = conv_of_chain(cx, c, from + 1, &env2, tail, final_spec);
            format!(
                "letcon_conv({p}, {env}, {tag}, {}, {rest_ir},\n        {fs}, {vs},\n        refl,\n        {hr})",
                refs(dists)
            )
        }
        Instr::Call { callee, dists, arg_specs, spec } => {
            let idx = cx.closure.iter().position(|m| m == callee).expect("callee in closure");
            let arg_exprs: Vec<String> = dists.iter().map(|&d| env_exprs[d].clone()).collect();
            let cargs = env_text(&arg_exprs, "VNil");
            let ws = out_text(spec);
            let hc = if callee == cx.self_name {
                let rec_idx = cx.self_rec_idx.expect("self-call in a Succ arm");
                let mut others: Vec<String> = arg_specs
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != rec_idx)
                    .map(|(_, s)| s.clone())
                    .collect();
                others.push("VNil".into());
                format!("gih({})", others.join(", "))
            } else {
                let cal = cx.ctx.get(callee).expect("callee generated");
                cert_app(&(cx.conv_name)(callee), &cal.model, arg_specs)
            };
            let mut env2 = vec![spec.clone()];
            env2.extend(env_exprs.iter().cloned());
            let hr = conv_of_chain(cx, c, from + 1, &env2, tail, final_spec);
            format!(
                "letcall_conv({p}, {env}, {idx}, {}, {rest_ir},\n        {cargs}, {ws}, {vs},\n        refl,\n        {hc},\n        {hr})",
                refs(dists)
            )
        }
    }
}

// ---------------------------------------------------------------------------
// The generator

fn generate_inner(d: &Decl, ctx: &GenCtx, forced: bool) -> Result<Emission, String> {
    let frag = fragment(d)?;
    let f = frag.name;
    let arity = frag.params.len();

    let model = match &frag.kind {
        FragKind::Plain(body) => {
            let c = compile_arm(&frag, ctx, false, body, forced)?;
            if c.has_self_call {
                return Err("a self-call outside a match is outside the fragment".into());
            }
            FnIr {
                params: frag.params.iter().map(|s| s.to_string()).collect(),
                kind: FnIrKind::Plain(c),
            }
        }
        FragKind::Rec { zero, succ, rec_idx, .. } => {
            let zc = compile_arm(&frag, ctx, false, zero, forced)?;
            if zc.has_self_call {
                return Err("a self-call in the Zero arm cannot be structural".into());
            }
            let sc = compile_arm(&frag, ctx, true, succ, forced)?;
            if !sc.has_self_call && !forced {
                return Err("a Succ arm without a self-call is outside the fragment".into());
            }
            FnIr {
                params: frag.params.iter().map(|s| s.to_string()).collect(),
                kind: FnIrKind::Rec(RecIr { rec_idx: *rec_idx, zero: zc, succ: sc }),
            }
        }
    };

    emit_with_model(f, arity, model, ctx)
}

/// Everything downstream of transcription: the callee closure, the IR
/// declarations, the fixtures, the ∃-kit folds and the instance. Shared by the
/// Rust transcriber above and the in-language one below — the port moves one
/// phase, and this is the seam it moves at
/// (docs/certgen-transcriber-in-language-design.md §5).
fn emit_with_model(
    f: &str,
    arity: usize,
    model: FnIr,
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
        let mm: FnIr = if m == f { model.clone() } else { ctx.get(&m).unwrap().model.clone() };
        emit_invariant(w, f, &m, &mm, &closure, ctx, &conv_name);
    }

    emit_instance(w, f, &model, arity);
    Ok(Emission { name: f.to_string(), arity, closure, ir_body, text, model })
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
fn emit_invariant(
    w: &mut String,
    f: &str,
    m: &str,
    model: &FnIr,
    closure: &[String],
    ctx: &GenCtx,
    conv_name: &dyn Fn(&str) -> String,
) {
    let name = conv_name(m);
    let prog = format!("{f}_gen_prog()");
    let params = &model.params;
    match &model.kind {
        FnIrKind::Plain(c) => {
            let cx = ProofCx {
                prog: prog.clone(),
                closure,
                conv_name,
                ctx,
                self_name: m,
                self_rec_idx: None,
            };
            let psig: String = params.iter().map(|p| format!("{p}: Nat, ")).collect();
            let env = env_text(params, "tail");
            let call = format!("{m}({})", params.join(", "));
            let proof = conv_of_chain(&cx, c, 0, params, "tail", &call);
            writeln!(w, "theorem {name}({psig}tail: Val)").unwrap();
            writeln!(w, "    : Converges({prog}, {env},").unwrap();
            writeln!(w, "                {m}_gen_body(), {})", out_text(&call)).unwrap();
            writeln!(w, "{{").unwrap();
            writeln!(w, "    {proof}").unwrap();
            writeln!(w, "}}").unwrap();
            writeln!(w).unwrap();
        }
        FnIrKind::Rec(r) => {
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
            let arms_text = format!("Arm({m}_gen_arm_zero(), Arm({m}_gen_arm_succ(), NoArm))");
            let after_ret = "Ret(RCons(0, RNil))";

            // Per-constructor arm of the induction: apply `letmatch_conv`,
            // its `ha` the kit fold over the arm chain, its `hr` the
            // rebinding Ret.
            let arm_proof = |ctor_tag: u64| -> String {
                let (entry_exprs, chain, self_rec) = if ctor_tag == 0 {
                    let (names, _, _) = spell("Zero");
                    (names, &r.zero, None)
                } else {
                    let (names, _, _) = spell("Succ(gk)");
                    (names, &r.succ, Some(r.rec_idx))
                };
                let cx = ProofCx {
                    prog: prog.clone(),
                    closure,
                    conv_name,
                    ctx,
                    self_name: m,
                    self_rec_idx: self_rec,
                };
                let (arm_exprs, fields): (Vec<String>, String) = if ctor_tag == 0 {
                    (entry_exprs.clone(), "VNil".to_string())
                } else {
                    let mut e = vec!["gk".to_string()];
                    e.extend(entry_exprs.iter().cloned());
                    (e, "VCons(embed_nat(gk), VNil)".to_string())
                };
                let arm_conv =
                    conv_of_chain(&cx, chain, 0, &arm_exprs, "tail", &chain.ret_spec);
                let env_entry = env_text(&entry_exprs, "tail");
                let mut after_exprs = vec![chain.ret_spec.clone()];
                after_exprs.extend(entry_exprs.iter().cloned());
                let env_after = env_text(&after_exprs, "tail");
                let ws = out_text(&chain.ret_spec);
                let vs = out_text(&if ctor_tag == 0 { spell("Zero").2 } else { spell("Succ(gk)").2 });
                format!(
                    "letmatch_conv({prog}, {env_entry}, {}, {arms_text}, {after_ret},\n        {ctor_tag}, {fields},\n        {ws}, {vs},\n        refl,\n        {arm_conv},\n        ret_conv({prog}, {env_after}, RCons(0, RNil), {vs}, refl))",
                    r.rec_idx
                )
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
            writeln!(w, "        {},", arm_proof(0)).unwrap();
            writeln!(w, "        Succ(gk, gih) => λ {other_lams}tail =>").unwrap();
            writeln!(w, "        {},", arm_proof(1)).unwrap();
            writeln!(w, "    }}").unwrap();
            writeln!(w, "}}").unwrap();
            writeln!(w).unwrap();
        }
    }
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
// The transcriber above is Rust that walks a surface AST. This section runs
// the *same* phase in the language instead: the elaborator marks the fn's
// elaborated body, an analyzer `meta fn` walks it with the code recursor, and
// its `Ir` value is read back into the `FnIr` the emitters already consume.
// Everything after `FnIr` — chain rendering, the ∃-kit fold, the fixtures, the
// instance — is shared, so the two paths differ in exactly one phase.
//
// Untrusted at every step: an unrecognized shape *declines* (an `Err` with a
// reason), and a misread one produces an emission whose certificate the kernel
// refuses. Neither can produce a wrong theorem.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::reduce::{self, Defs};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    LocalCtx, LocalSubst, LocalVar, Term, Type,
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
/// contains numerals, so a numeral marker would be ambiguous, while an
/// application is a node the fragment never contains — every call in the
/// fragment is a global reference, which the recursor goes neutral on anyway.
/// Code does not compute (`Layer::computes` is `Prog | Meta`), so the redex is
/// stable syntax: the recursor dispatches it to the `tm_app` branch and no
/// reduction can collapse it first.
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

/// Replace every variable *occurrence* by a marker carrying its binder's
/// level, leaving closed code (§1).
///
/// This is scope resolution, and it stays in Rust for a kernel reason rather
/// than for convenience: `elim^Trm`'s variable branch abstracts over the
/// variable at layer v (rec.rs `tm_var`), so nothing at layer m can observe
/// *which* variable an occurrence is. The pass itself is a mechanical de
/// Bruijn→level renaming — no fragment knowledge, no declaration table.
///
/// `depth` is the number of binders in scope, so the occupied levels are
/// `0..depth` and `Var(i)` is the binder at level `depth - 1 - i`.
fn mark(t: &Term, depth: u32) -> Result<Term, String> {
    Ok(match t {
        Term::Var(LocalVar(i)) => {
            if *i >= depth {
                return Err("a variable escapes the body's own binders".into());
            }
            marker(depth - 1 - i)
        }
        Term::Zero => Term::Zero,
        Term::Succ(p) => Term::Succ(Rc::new(mark(p, depth)?)),
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
                base: Rc::new(mark(base, depth)?),
                // `elim_Nat`'s step binds the predecessor and the induction
                // hypothesis, in that order, so their levels are `depth` and
                // `depth + 1` — which is the convention the walker reads back.
                step: Rc::new(mark(step, depth + 2)?),
                scrut: Rc::new(mark(scrut, depth)?),
            }
        }
        // A call to another function is a *global reference*, and the recursor
        // is neutral on `box (u^δ)` (reduce.rs `is_neutral_term`) — so the walk
        // would stop there whatever this pass did. Named as the neutrality it
        // is, at the head of the spine, rather than as "some application".
        Term::GlobalTm { .. } | Term::App { .. } if global_head(t) => {
            return Err(
                "the body calls a global: `elim^Trm` is neutral on `box (u^δ)`, so a \
                 cross-function call is outside the in-language fragment (the Rust \
                 transcriber's v2 path serves it)"
                    .into(),
            );
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

/// The declaration's elaborated body, marked and closed, with its arity.
///
/// Peeling the `Lam` spine is also the signature check: the fragment is
/// `Nat → … → Nat`, and a parameter of any other type declines here rather
/// than confusing the walker.
fn marked_body(e: &Elaborator, name: &str) -> Result<(usize, Term), String> {
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
    Ok((arity, mark(t, arity as u32)?))
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

// -- invocation and reconstruction ------------------------------------------

/// Apply the registered analyzer to `(Γ = ·, arity, box marked)` and read its
/// answer back.
///
/// The application spine is built in the **slot's** canonical order, which is
/// what analyzer registration buys: whole-signature convertibility fixes the Π
/// order, so this code does not consult the template's own signature at all
/// (docs/meta-def-registration-design.md, analyzer extension).
fn run_transcriber(e: &Elaborator, arity: usize, marked: Term) -> Result<RIr, String> {
    let md = e
        .analyzer_def(Slot::CertgenTranscribe)
        .ok_or("no `meta fn … for certgen.transcribe` is registered")?;
    let empty = LocalCtx::nil();
    // Rescoped to the Ψ this call sees: a meta definition is elaborator-held,
    // so its global references are stale by however much Ψ has grown since it
    // was registered (`MetaDef::psi_len`) — and an analyzer's arms are made of
    // calls to library globals, so every one of them is affected.
    let (md_term, md_stmt) = md.at(e.psi().bindings.len());
    let Type::CtxPi { body, .. } = &*md_stmt else {
        return Err("the transcriber does not open with a `Ctx` binder".into());
    };
    let mut ty = body.apply_global(&GlobalSubst {
        entries: vec![GlobalEntry::Ctx(empty.clone())],
    });
    let mut term = Term::CtxApp { fun: md_term, ctx: empty.clone() };
    let mut nat = Term::Zero;
    for _ in 0..arity {
        nat = Term::Succ(Rc::new(nat));
    }
    for arg in [nat, Term::BoxTm(Rc::new(marked))] {
        let Type::Pi { dom_level, cod_level, dom, cod } = ty else {
            return Err("the transcriber's signature ran out of parameters".into());
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
    // Evaluation is **spine-directed**: `Reader::whnf` reduces only what it is
    // about to inspect, so nothing ever normalizes a whole IR tree at once
    // (CLAUDE.md's memory discipline).
    let r = Reader { psi: e.psi(), budget: std::cell::Cell::new(READ_BUDGET) };
    let (idx, fields, _) = r.ctor(&term, 2)?;
    match idx {
        0 => Err("the in-language transcriber declined this body".into()),
        1 => r.ir(fields.first().ok_or("`TYes` without its IR")?),
        _ => Err("the transcriber's answer is not a `TOut`".into()),
    }
}

/// The environment's spec expressions, **by distance** (0 = most recent): the
/// parameters as the arm sees them, with the `Succ` arm's field on top. This
/// is the layout `compile_arm` builds by pushing ids in reverse parameter
/// order, and it is where the marker convention and the IR's slots meet.
fn base_specs(params: &[String], field: bool) -> Vec<String> {
    let mut v: Vec<String> = params.to_vec();
    if field {
        v.insert(0, "gk".to_string());
    }
    v
}

/// One instruction chain, with the spec expressions **derived** rather than
/// carried: a temporary's spec is determined by its instruction and the specs
/// of the slots it reads, so the Rust transcriber's `Instr::spec` is redundant
/// with the IR (design doc §6, step 5) and the in-language path recomputes it
/// from the same rules.
fn chain_from_rir(ir: &RIr, name: &str, env: Vec<String>) -> Result<Chain, String> {
    let mut specs = env;
    let mut instrs = Vec::new();
    let mut has_self_call = false;
    let mut cur = ir;
    loop {
        match cur {
            RIr::Ret(rs) => {
                let [d] = rs[..] else {
                    return Err("a `Ret` with other than one output".into());
                };
                let ret_spec = specs
                    .get(d as usize)
                    .ok_or("a `Ret` reading past the environment")?
                    .clone();
                return Ok(Chain {
                    instrs,
                    ret_dist: d as usize,
                    ret_spec,
                    has_self_call,
                });
            }
            RIr::LetCon { tag, args, rest } => {
                let dists: Vec<usize> = args.iter().map(|d| *d as usize).collect();
                let spec = match tag {
                    0 => "Zero".to_string(),
                    1 => {
                        let a = specs
                            .get(dists[0])
                            .ok_or("a `Succ` reading past the environment")?;
                        format!("Succ({a})")
                    }
                    other => return Err(format!("constructor tag {other} is not a `Nat`")),
                };
                instrs.push(Instr::Con { tag: *tag, dists, spec: spec.clone() });
                specs.insert(0, spec);
                cur = rest;
            }
            RIr::LetCall { callee, args, rest } => {
                if *callee != 0 {
                    return Err(
                        "a call to a callee other than 0: the in-language slice is \
                         single-function"
                            .into(),
                    );
                }
                let dists: Vec<usize> = args.iter().map(|d| *d as usize).collect();
                let arg_specs: Vec<String> = dists
                    .iter()
                    .map(|d| {
                        specs.get(*d).cloned().ok_or("a call reading past the environment")
                    })
                    .collect::<Result<_, _>>()?;
                let spec = format!("{name}({})", arg_specs.join(", "));
                has_self_call = true;
                instrs.push(Instr::Call {
                    callee: name.to_string(),
                    dists,
                    arg_specs,
                    spec: spec.clone(),
                });
                specs.insert(0, spec);
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
fn fn_ir_from_rir(ir: &RIr, name: &str, params: &[String]) -> Result<FnIr, String> {
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
            let zc = chain_from_rir(zero, name, base_specs(&params, false))?;
            if zc.has_self_call {
                return Err("a self-call in the Zero arm cannot be structural".into());
            }
            let sc = chain_from_rir(succ, name, base_specs(&params, true))?;
            Ok(FnIr {
                params,
                kind: FnIrKind::Rec(RecIr { rec_idx: *scrut as usize, zero: zc, succ: sc }),
            })
        }
        _ => {
            let c = chain_from_rir(ir, name, base_specs(&params, false))?;
            if c.has_self_call {
                return Err("a self-call outside a match is outside the fragment".into());
            }
            Ok(FnIr { params, kind: FnIrKind::Plain(c) })
        }
    }
}

/// Generate for `d` with the **in-language** transcriber: the elaborator marks
/// `d`'s elaborated body, the registered analyzer walks it, and its `Ir` is
/// read back into the model the shared emitters consume.
///
/// `d` must already be elaborated into `e` (it is an ordinary declaration).
/// Every failure is a decline, and the Rust path serves the same input.
pub fn generate_in_language(
    e: &Elaborator,
    d: &Decl,
    ctx: &GenCtx,
) -> Result<Emission, String> {
    let frag = fragment(d)?;
    let f = frag.name;
    let (arity, marked) = marked_body(e, f)?;
    if arity != frag.params.len() {
        return Err("the elaborated body's arity disagrees with the declaration".into());
    }
    let rir = run_transcriber(e, arity, marked)?;
    let params: Vec<String> = frag.params.iter().map(|s| s.to_string()).collect();
    let model = fn_ir_from_rir(&rir, f, &params)?;
    emit_with_model(f, arity, model, ctx)
}
