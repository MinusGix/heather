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
        ExprKind::Match { scrut, motive, arms } => {
            if motive.is_some() {
                return Err("an explicit motive is outside the fragment".into());
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
                        succ = Some((arm.binders[0].as_str(), &arm.body));
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
