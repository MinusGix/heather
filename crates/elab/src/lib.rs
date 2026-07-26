//! The stage-1 elaborator: surface AST → fully explicit kernel core.
//!
//! Scope (issues/elaborator-design.md, order of attack, stage 1): name
//! resolution into the kernel's namespaces and bidirectional
//! annotation-filling — no metavariables, no level inference (everything in
//! stage 1 lives at level 0, though levels are tracked honestly), no modal
//! layer. The kernel remains the gate: every elaborated declaration is
//! re-checked from scratch by `heather_kernel::typing` before it is
//! recorded, so nothing here is trusted.
//!
//! Definition story (elaborator-design):
//! - `fn` (computes): elaborated once, then **inlined** at every use — the
//!   emitted term is substituted in place, shifted across whatever Ψ grew
//!   in between.
//! - `theorem` (never computes): the proof is kernel-checked against the
//!   statement, then the statement is bound as an **opaque Ψ-global**
//!   `u : Trm_c(· ⊢ Stmt @ l)` (ch. 04 admits referencing a layer-c global
//!   from any layer ≥ c: `i' ≤ i`, typing.rs:674). Later proofs refer to it
//!   as a neutral — proofs are transported, never evaluated.
//!
//! Everything is checked at layer c (full MLTT, no computation *rules* —
//! conversion still β-reduces during checking, which is all the Nat suite
//! needs) so that theorems are bindable as `Trm_c` globals.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_type;
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{self, TypeError, DEFAULT_FUEL};
use heather_syntax::{
    parse_file, Arm, Decl, DeclKind, Expr, ExprKind, Item, OnStmt, OnTarget, ParseError, Span,
    Stmt, Ty, TyKind,
};

mod inductive;

use inductive::Inductive;

/// The stage-1 prelude: `sym`/`trans`/`cong_succ`, monomorphic at `Nat`.
/// (The universe-polymorphic versions are layer-m `Λ ℓ⃗` territory — later
/// stage; the Nat suite only ever congs by `Succ`.)
pub const PRELUDE: &str = include_str!("prelude.hthr");

#[derive(Debug)]
pub enum ElabError {
    Parse(ParseError),
    /// A surface-level elaboration failure (unbound name, unsupported form,
    /// arity mismatch, missing motive, …).
    Elab { msg: String, span: Span },
    /// The kernel rejected an elaborated declaration. This is the trust
    /// boundary speaking: either the source is ill-typed or the elaborator
    /// has a bug — the kernel does not care which.
    Kernel { decl: String, err: TypeError },
    /// Goals raised in a block that no `on` statement discharged
    /// (issues/goal-holes.md). Not one error per goal: the *listing* is the
    /// point — it is how the checker shows goal state.
    UnsolvedGoals { decl: String, goals: Vec<GoalReport> },
}

/// One entry of the unsolved-goal listing. Types are rendered eagerly with
/// the kernel's budget-bounded `Debug` (crates/kernel/src/fmt.rs), so no
/// kernel type escapes into the public error.
#[derive(Debug)]
pub struct GoalReport {
    /// Discharge name: `on ?{name} := …`.
    pub name: String,
    /// The goal's statement.
    pub statement: String,
    /// The context captured at the hole — the names a discharge may use, which
    /// is not the same as what is lexically in scope at the `on`.
    pub context: Vec<(String, String)>,
    /// Where the goal came from, when it was an argument: "the `p` parameter
    /// of `sym`". Proof-parameter names are API precisely so this reads.
    pub origin: Option<String>,
    pub span: Span,
}

impl From<ParseError> for ElabError {
    fn from(e: ParseError) -> Self {
        ElabError::Parse(e)
    }
}

impl ElabError {
    /// The error with source positions resolved — what a front-end should
    /// print. [`std::fmt::Display`] gives the same text without them, for
    /// where the source is no longer at hand.
    pub fn render(&self, src: &str) -> String {
        let at = |span: Span| {
            let (line, col) = line_col(src, span.start);
            format!("{line}:{col}")
        };
        match self {
            ElabError::Parse(e) => format!("{}:{}: {}", at(e.span), "parse error", e.msg),
            ElabError::Elab { msg, span } => format!("{}: {msg}", at(*span)),
            ElabError::Kernel { .. } => self.to_string(),
            ElabError::UnsolvedGoals { decl, goals } => {
                let mut s = format!("unsolved goals in `{decl}`:\n");
                for g in goals {
                    s.push('\n');
                    s.push_str(&g.render(Some(&at(g.span))));
                }
                s.push_str("\ndischarge each with `on ?name := proof;`\n");
                s
            }
        }
    }
}

impl GoalReport {
    fn render(&self, at: Option<&str>) -> String {
        let mut s = match at {
            Some(at) => format!("  ?{} : {}   ({at})\n", self.name, self.statement),
            None => format!("  ?{} : {}\n", self.name, self.statement),
        };
        // The context is not decoration: a goal captured in a `match` arm is
        // discharged with that arm's binders in scope, which is not what is
        // lexically visible at the `on`.
        for (name, ty) in &self.context {
            s.push_str(&format!("      {name} : {ty}\n"));
        }
        if let Some(origin) = &self.origin {
            s.push_str(&format!("      from {origin}\n"));
        }
        s
    }
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ElabError::Parse(e) => write!(f, "parse error: {}", e.msg),
            ElabError::Elab { msg, .. } => write!(f, "{msg}"),
            ElabError::Kernel { decl, err } => {
                write!(f, "the kernel rejected `{decl}`: {err:?}")
            }
            ElabError::UnsolvedGoals { decl, goals } => {
                writeln!(f, "unsolved goals in `{decl}`:")?;
                for g in goals {
                    writeln!(f)?;
                    write!(f, "{}", g.render(None))?;
                }
                writeln!(f, "\ndischarge each with `on ?name := proof;`")
            }
        }
    }
}

/// 1-based line and column of a byte offset.
fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let upto = &src[..offset.min(src.len())];
    let line = upto.matches('\n').count() + 1;
    let col = upto.rfind('\n').map_or(upto.len(), |nl| upto.len() - nl - 1) + 1;
    (line, col)
}

type R<T> = Result<T, ElabError>;

fn err<T>(msg: impl Into<String>, span: Span) -> R<T> {
    Err(ElabError::Elab { msg: msg.into(), span })
}

/// One parameter of a callable global, in declaration/telescope order.
/// `implicit` flags a `{}`-parameter, filled by unification at call sites
/// (issues/elab-stage2-metas.md). The *name* is API: it is the default name of
/// a goal raised in that argument position (issues/goal-holes.md), so callers
/// discharge by it.
struct ParamMeta {
    name: String,
    implicit: bool,
}

/// What a global name refers to.
enum GlobalInfo {
    /// An inlined `fn`: the elaborated closed term, its type, level, and
    /// `|Ψ|` at elaboration time (for global-index shifting on use).
    Def {
        term: Rc<Term>,
        ty: Rc<Type>,
        level: Level,
        psi_len: u32,
        params: Rc<Vec<ParamMeta>>,
    },
    /// A `theorem`: absolute position of its `Trm_c` binding in Ψ.
    Theorem { abs: u32, params: Rc<Vec<ParamMeta>> },
}

pub struct Elaborator {
    psi: GlobalCtx,
    globals: HashMap<String, GlobalInfo>,
    /// Declared inductives by name, by nominal tag, and by constructor name.
    /// Constructor names are unqualified and globally unique — there is no
    /// path syntax yet, so a clash is a declaration error
    /// (docs/inductive-tier0-lowering.md).
    inductives: HashMap<String, Rc<Inductive>>,
    by_tag: HashMap<u32, Rc<Inductive>>,
    ctors: HashMap<String, (Rc<Inductive>, usize)>,
    next_tag: u32,
    fuel: u64,
    /// Number of Ψ slots reserved for the current declaration's goals — a
    /// syntactic pre-count of its holes. Goals occupy the *innermost* indices
    /// `[0, goal_base)` for the whole declaration, so every reference to a
    /// committed global is offset by it (see [`Self::resolve`]). Zero outside
    /// a declaration body, which makes the whole mechanism inert.
    goal_base: u32,
    /// Goals in creation order; goal `k` is `GlobalVar(goal_base - 1 - k)`.
    /// Interior mutability because the elaboration methods take `&self` and
    /// `Cx` is cloned at every binder.
    goals: RefCell<Vec<Goal>>,
    /// Hole span → goal index. The elaborator visits some expressions twice
    /// (motive synthesis; `calc`'s cloned `@trans` spine), and one syntactic
    /// hole must stay one goal.
    goal_spans: RefCell<HashMap<(usize, usize), usize>>,
    /// Set while elaborating an `on` right-hand side, where a *new* hole is
    /// refused. Load-bearing: it is what makes [`strengthen_global`] sound.
    frozen: Cell<bool>,
}

/// A goal: a hole that survives to the end of its block. Represented exactly
/// like the elaborator's other metavariables (issues/elab-stage2-metas.md) —
/// an innermost Ψ-binding `u : Trm(Γ ⊢ T @ l)` occurring as `u^{id_Γ}` — but
/// allocated for the whole declaration and discharged by an `on` statement
/// rather than by unification.
struct Goal {
    /// Discharge name (site-written `?first`, or checker-assigned).
    name: String,
    /// The context *at the hole*. This capture is the point of the design: an
    /// `on` written at block end elaborates here, so a goal raised inside a
    /// `match` arm is discharged with that arm's binders in scope.
    cx: Cx,
    ty: Type,
    level: Level,
    span: Span,
    /// `(callee, parameter)` when the hole is an argument — the provenance the
    /// listing reports, and where an anonymous hole's default name comes from.
    origin: Option<(String, String)>,
    solution: Option<Rc<Term>>,
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

impl Elaborator {
    /// An empty elaborator (no prelude).
    pub fn new() -> Self {
        Elaborator {
            psi: GlobalCtx::default(),
            globals: HashMap::new(),
            inductives: HashMap::new(),
            by_tag: HashMap::new(),
            ctors: HashMap::new(),
            next_tag: 0,
            fuel: DEFAULT_FUEL,
            goal_base: 0,
            goals: RefCell::new(Vec::new()),
            goal_spans: RefCell::new(HashMap::new()),
            frozen: Cell::new(false),
        }
    }

    /// An elaborator with the stage-1 prelude already elaborated and
    /// kernel-checked.
    pub fn with_prelude() -> R<Self> {
        let mut e = Self::new();
        e.elab_source(PRELUDE)?;
        Ok(e)
    }

    /// Parse and elaborate a source file, kernel-checking every declaration.
    pub fn elab_source(&mut self, src: &str) -> R<()> {
        let file = parse_file(src)?;
        for item in &file.items {
            match item {
                Item::Decl(d) => self.elab_decl(d)?,
                Item::Inductive(i) => self.elab_inductive(i)?,
            }
        }
        Ok(())
    }

    /// The accumulated global context (theorem statements).
    pub fn psi(&self) -> &GlobalCtx {
        &self.psi
    }

    // -- declarations -------------------------------------------------------

    /// Elaborate one declaration, always leaving the goal state clean — the
    /// `Elaborator` outlives a declaration (and an `elab_source` call), so a
    /// stale `goal_base` would silently corrupt the next one.
    fn elab_decl(&mut self, decl: &Decl) -> R<()> {
        let r = self.elab_decl_inner(decl);
        self.goal_base = 0;
        self.goals.borrow_mut().clear();
        self.goal_spans.borrow_mut().clear();
        self.frozen.set(false);
        r
    }

    fn elab_decl_inner(&mut self, decl: &Decl) -> R<()> {
        if self.globals.contains_key(&decl.name) {
            return err(format!("duplicate name `{}`", decl.name), decl.span);
        }
        // Reserve the goal prefix *before* anything is elaborated: the
        // telescope and result type are elaborated first and their types end
        // up embedded in the emitted term, so they must live in the same
        // (shifted) world as the body.
        self.goal_base = count_holes(decl);
        // Elaborate the parameter telescope.
        let mut cx = Cx::empty();
        let mut param_info: Vec<(Type, Level)> = Vec::new();
        for p in &decl.params {
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            cx.push(p.name.clone(), ty.clone(), lvl.clone());
            param_info.push((ty, lvl));
        }
        // Result type and body (checked against it). The declaration's own
        // name goes into scope for the body only: a self-call guarded by a
        // `match` on one of these parameters *is* the induction hypothesis
        // (issues/match-recursion.md), and the lowering constructs the
        // recursor, so there is no fixpoint and nothing new for the kernel.
        let (res_ty, res_lvl) = self.elab_ty(&cx, &decl.result)?;
        cx.selfref = Some(Rc::new(SelfRef {
            name: decl.name.clone(),
            params: decl.params.iter().map(|p| (p.name.clone(), p.implicit)).collect(),
        }));
        // `let` bindings, then the result expression. A `let` is an inlined
        // alias (the same doctrine as a `fn` definition), not a kernel binder.
        for stmt in &decl.body.stmts {
            let Stmt::Let { name, ty, expr, .. } = stmt;
            let (term, ty, level) = match ty {
                Some(t) => {
                    let (ty, lvl) = self.elab_ty(&cx, t)?;
                    let tm = self.elab_check(&cx, expr, &ty, &lvl)?;
                    (tm, ty, lvl)
                }
                None => self.elab_infer(&cx, expr)?,
            };
            cx.aliases.push(Rc::new(Alias {
                name: name.clone(),
                depth: cx.names.len(),
                term: Rc::new(term),
                ty,
                level,
            }));
        }
        let body = self.elab_check(&cx, &decl.body.result, &res_ty, &res_lvl)?;
        // Discharge every goal the block raised, then substitute them away.
        self.solve_goals(&decl.body.ons, &decl.name)?;
        let sigma = self.goal_subst();

        // Close over the telescope: statement = Π…, proof/body = λ….
        let mut stmt = res_ty;
        let mut stmt_lvl = res_lvl;
        let mut term = body;
        for (dom, dom_lvl) in param_info.into_iter().rev() {
            term = Term::Lam {
                dom_level: dom_lvl.clone(),
                cod_level: stmt_lvl.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(term),
            };
            stmt = Type::Pi {
                dom_level: dom_lvl.clone(),
                cod_level: stmt_lvl.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(stmt),
            };
            stmt_lvl = Level::max(dom_lvl, stmt_lvl);
        }

        // One global substitution fills every goal and renumbers the committed
        // globals back down out of the goal world (`GlobalSubst`'s
        // instantiation semantics). With no holes it is the identity.
        let term = term.apply_global(&sigma);
        let stmt = stmt.apply_global(&sigma);

        // The kernel is the gate: check the statement, then the term.
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        typing::check_type(&self.psi, 0, Layer::Prog, &empty, &stmt, &stmt_lvl, self.fuel)
            .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), err: e })?;
        typing::check_term(&self.psi, 0, Layer::Code, &empty, &term, &stmt, &stmt_lvl, self.fuel)
            .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), err: e })?;

        let params = Rc::new(
            decl.params
                .iter()
                .map(|p| ParamMeta { name: p.name.clone(), implicit: p.implicit })
                .collect::<Vec<_>>(),
        );
        match decl.kind {
            DeclKind::Fn => {
                self.globals.insert(
                    decl.name.clone(),
                    GlobalInfo::Def {
                        term: Rc::new(term),
                        ty: Rc::new(stmt),
                        level: stmt_lvl,
                        psi_len: self.psi.bindings.len() as u32,
                        params,
                    },
                );
            }
            DeclKind::Theorem => {
                let abs = self.psi.bindings.len() as u32;
                self.psi.bindings.push(GlobalBinding::Tm {
                    ctx: LocalCtx { base: CtxBase::Nil, entries: vec![] },
                    layer: Layer::Code,
                    ty: Rc::new(stmt),
                    level: stmt_lvl,
                });
                self.globals.insert(decl.name.clone(), GlobalInfo::Theorem { abs, params });
            }
        }
        Ok(())
    }

    // -- goals --------------------------------------------------------------

    /// Raise a goal for a hole, returning its occurrence `u^{id_Γ}`.
    fn new_goal(
        &self,
        cx: &Cx,
        name: Option<&str>,
        hint: Option<(&str, &str)>,
        ty: Type,
        level: Level,
        span: Span,
    ) -> R<Term> {
        if self.frozen.get() {
            return err(
                "a hole may not appear in an `on` right-hand side — give it its own `on`",
                span,
            );
        }
        let mut goals = self.goals.borrow_mut();
        let mut spans = self.goal_spans.borrow_mut();
        let k = match spans.get(&(span.start, span.end)) {
            // Re-elaboration of the same syntactic hole (motive synthesis,
            // `calc`'s cloned spine): the same goal, so long as it is the same
            // context — the occurrence's `id_Γ` is what the payload lands in.
            Some(&k) => {
                if goals[k].cx.gamma.entries.len() != cx.gamma.entries.len() {
                    return err("internal: a hole was re-elaborated in a different context", span);
                }
                k
            }
            None => {
                let k = goals.len();
                if k as u32 >= self.goal_base {
                    return err("internal: more goals than the pre-count reserved", span);
                }
                // A goal payload is a `Trm` entry, so a context *variable* base
                // would substitute a term for a `Ctx` binding (subst.rs).
                // Nothing can build one today; assert rather than discover it.
                debug_assert!(
                    matches!(cx.gamma.base, CtxBase::Nil),
                    "a goal context must be closed"
                );
                let name = match name {
                    Some(n) => {
                        if goals.iter().any(|g| g.name == n) {
                            return err(
                                format!(
                                    "hole `?{n}` is already used in this block; \
                                     each named hole is a distinct goal"
                                ),
                                span,
                            );
                        }
                        n.to_string()
                    }
                    // An anonymous hole takes the callee's parameter name,
                    // deduplicated with an ordinal (`bound`, `bound.1`, …);
                    // with no callee to name it after, a positional fallback.
                    None => {
                        let base = match hint {
                            Some((_, param)) => param.to_string(),
                            None => format!("g{}", k + 1),
                        };
                        let mut candidate = base.clone();
                        let mut ordinal = 0;
                        while goals.iter().any(|g| g.name == candidate) {
                            ordinal += 1;
                            candidate = format!("{base}.{ordinal}");
                        }
                        candidate
                    }
                };
                let origin =
                    hint.map(|(callee, param)| (callee.to_string(), param.to_string()));
                goals.push(Goal {
                    name,
                    cx: cx.clone(),
                    ty,
                    level,
                    span,
                    origin,
                    solution: None,
                });
                spans.insert((span.start, span.end), k);
                k
            }
        };
        Ok(Term::GlobalTm {
            var: GlobalVar(self.goal_base - 1 - k as u32),
            subst: LocalSubst::id(&cx.gamma),
        })
    }

    /// Run the block's `on` statements, then require that every goal is
    /// discharged.
    fn solve_goals(&self, ons: &[OnStmt], decl: &str) -> R<()> {
        // No new goals from here on: `on` right-hand sides are elaborated in
        // the goal world but their solutions are strengthened out of it.
        self.frozen.set(true);
        for on in ons {
            match &on.target {
                OnTarget::Name(name) => {
                    let (cx, ty, lvl) = {
                        let goals = self.goals.borrow();
                        let Some(g) = goals.iter().find(|g| g.name == *name) else {
                            let known: Vec<&str> =
                                goals.iter().map(|g| g.name.as_str()).collect();
                            return err(
                                if known.is_empty() {
                                    format!("no goal `?{name}` — this block raises none")
                                } else {
                                    format!(
                                        "no goal `?{name}` in this block; it raises: ?{}",
                                        known.join(", ?")
                                    )
                                },
                                on.span,
                            );
                        };
                        if g.solution.is_some() {
                            return err(format!("goal `?{name}` is discharged twice"), on.span);
                        }
                        (g.cx.clone(), g.ty.clone(), g.level.clone())
                    };
                    // In the goal's *own* context, not the one at the `on`.
                    let t = self.elab_check(&cx, &on.expr, &ty, &lvl)?;
                    let t = strengthen_global(&t, self.goal_base);
                    let mut goals = self.goals.borrow_mut();
                    let g = goals.iter_mut().find(|g| g.name == *name).expect("found above");
                    g.solution = Some(Rc::new(t));
                }
                // `on _: P := e;` — discharge *every* goal whose statement is
                // `P` (docs/sketches/surface-v2.md §2: one bound proof feeding
                // many sites). `P` is elaborated per goal, in that goal's own
                // context, since that is where its statement lives.
                OnTarget::Stmt(pat) => {
                    let psi = self.goal_psi();
                    let candidates: Vec<(usize, Cx, Type, Level)> = self
                        .goals
                        .borrow()
                        .iter()
                        .enumerate()
                        .filter(|(_, g)| g.solution.is_none())
                        .map(|(k, g)| (k, g.cx.clone(), g.ty.clone(), g.level.clone()))
                        .collect();
                    let mut matched = Vec::new();
                    for (k, cx, ty, lvl) in candidates {
                        // Not well-formed in this goal's context just means
                        // "not this goal" — a statement need not mention names
                        // every goal has.
                        let Ok((pat_ty, pat_lvl)) = self.elab_ty(&cx, pat) else {
                            continue;
                        };
                        if conv_type(&psi, &cx.gamma, Layer::Prog, &pat_ty, &ty, &pat_lvl, self.fuel)
                            .is_ok()
                        {
                            matched.push((k, cx, ty, lvl));
                        }
                    }
                    if matched.is_empty() {
                        return err(
                            "no outstanding goal has this statement".to_string(),
                            on.span,
                        );
                    }
                    for (k, cx, ty, lvl) in matched {
                        let t = self.elab_check(&cx, &on.expr, &ty, &lvl)?;
                        let t = strengthen_global(&t, self.goal_base);
                        self.goals.borrow_mut()[k].solution = Some(Rc::new(t));
                    }
                }
            }
        }
        let goals = self.goals.borrow();
        let unsolved: Vec<GoalReport> = goals
            .iter()
            .filter(|g| g.solution.is_none())
            .map(|g| GoalReport {
                name: g.name.clone(),
                statement: format!("{:?}", g.ty),
                context: g
                    .cx
                    .names
                    .iter()
                    .zip(&g.cx.gamma.entries)
                    // `#`-prefixed binders are the elaborator's own (a `match`
                    // arm's hidden ih); they are unspellable, so listing them
                    // would only mislead.
                    .filter(|(n, _)| !n.starts_with('#'))
                    .map(|(n, e)| (n.clone(), format!("{:?}", e.ty)))
                    .chain(g.cx.aliases.iter().map(|a| (a.name.clone(), format!("{:?}", a.ty))))
                    .collect(),
                origin: g
                    .origin
                    .as_ref()
                    .map(|(callee, param)| format!("the `{param}` parameter of `{callee}`")),
                span: g.span,
            })
            .collect();
        if unsolved.is_empty() {
            Ok(())
        } else {
            Err(ElabError::UnsolvedGoals { decl: decl.to_string(), goals: unsolved })
        }
    }

    /// Ψ as the goal world sees it: the committed bindings, then one `Trm`
    /// binding per goal in creation order, padded out to `goal_base`. With
    /// `L = |Ψ| + goal_base`, `GlobalVar(v)` is `bindings[L - 1 - v]`, so goal
    /// `k` at `GlobalVar(goal_base - 1 - k)` lands immediately after the
    /// committed ones. Well-scoped precisely because goals are numbered in
    /// creation order: goal `k`'s statement can only mention goals before it.
    ///
    /// Needed only where the kernel must look a global *up* — conversion. The
    /// term path never does (`whnf_type` takes no Ψ), which is why goals need
    /// no real binding for the rest of elaboration.
    fn goal_psi(&self) -> GlobalCtx {
        let goals = self.goals.borrow();
        let mut bindings = self.psi.bindings.clone();
        for k in 0..self.goal_base as usize {
            bindings.push(match goals.get(k) {
                Some(g) => GlobalBinding::Tm {
                    ctx: g.cx.gamma.clone(),
                    layer: Layer::Code,
                    ty: Rc::new(g.ty.clone()),
                    level: g.level.clone(),
                },
                // A reserved-but-unused slot (the pre-count is an upper
                // bound). Nothing refers to it.
                None => GlobalBinding::Tm {
                    ctx: LocalCtx { base: CtxBase::Nil, entries: vec![] },
                    layer: Layer::Code,
                    ty: Rc::new(Type::Nat),
                    level: Level::Zero,
                },
            });
        }
        GlobalCtx { bindings }
    }

    /// The substitution discharging the whole goal block: `entries[k]` is the
    /// payload for goal `k` at `GlobalVar(goal_base - 1 - k)`, matching
    /// `apply_global`'s convention. Reserved-but-unused slots (the pre-count
    /// is an upper bound) get a payload nothing can reach.
    fn goal_subst(&self) -> GlobalSubst {
        let goals = self.goals.borrow();
        let entries = (0..self.goal_base as usize)
            .map(|k| {
                GlobalEntry::Tm(match goals.get(k).and_then(|g| g.solution.clone()) {
                    Some(t) => t,
                    None => Rc::new(Term::Zero),
                })
            })
            .collect();
        GlobalSubst { entries }
    }

    // -- types --------------------------------------------------------------

    fn elab_ty(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
        match &ty.kind {
            TyKind::Nat => Ok((Type::Nat, Level::Zero)),
            TyKind::Named { name, args } => self.lower_named(cx, name, args, ty.span),
            TyKind::Eq(lhs, rhs) => {
                let (lhs_t, lhs_ty, lvl) = self.elab_infer(cx, lhs)?;
                let rhs_t = self.elab_check(cx, rhs, &lhs_ty, &lvl)?;
                Ok((
                    Type::Id {
                        level: lvl.clone(),
                        ty: Rc::new(lhs_ty),
                        lhs: Rc::new(lhs_t),
                        rhs: Rc::new(rhs_t),
                    },
                    lvl,
                ))
            }
        }
    }

    // -- terms --------------------------------------------------------------

    /// Checking mode. Structural only where the expected type is genuinely
    /// needed (`refl`, motive-less `match`); everything else infers, and
    /// the mismatch (if any) is caught by the kernel's final check of the
    /// declaration — the kernel converts at every application/eliminator
    /// premise, so errors cannot slip through, only be reported later.
    fn elab_check(&self, cx: &Cx, e: &Expr, expected: &Type, lvl: &Level) -> R<Term> {
        self.elab_check_hinted(cx, e, expected, lvl, None)
    }

    /// [`Self::elab_check`] plus, where the caller knows it, the `(callee,
    /// parameter)` this expression is an argument for — the provenance and
    /// default name of any goal raised inside it.
    fn elab_check_hinted(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
        hint: Option<(&str, &str)>,
    ) -> R<Term> {
        match &e.kind {
            // The expected type *is* the goal's statement, which is why holes
            // are checking-only (issues/goal-holes.md).
            ExprKind::Hole(name) => {
                self.new_goal(cx, name.as_deref(), hint, expected.clone(), lvl.clone(), e.span)
            }
            ExprKind::Refl => {
                let head = self.whnf(cx, expected, e.span)?;
                let Type::Id { level, ty, lhs, .. } = head else {
                    return err("`refl` needs an `=` expected type", e.span);
                };
                Ok(Term::Refl { level, ty, tm: lhs })
            }
            ExprKind::Match { motive: None, scrut, arms } => {
                // Stage-2 motive synthesis (issues/elab-stage2-metas.md): when
                // the scrutinee is a local variable, abstract it out of the
                // expected type so the motive is genuinely dependent; otherwise
                // fall back to the non-dependent motive (expected under `z`).
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                let motive = self.synth_motive(cx, &scrut_t, &scrut_ty, &scrut_lvl, expected);
                self.elab_match(
                    cx, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, lvl.clone(), e.span,
                )
            }
            // `absurd(p)`: from an equation between distinct constructors,
            // anything — so it needs the expected type
            // (docs/inductive-tier0-lowering.md §6.1).
            ExprKind::Call { name, args, .. }
                if name == "absurd" && !self.shadowed(cx, name) =>
            {
                let [arg] = args.as_slice() else {
                    return err("`absurd` takes exactly one argument", e.span);
                };
                self.build_absurd(cx, arg, expected, lvl, e.span)
            }
            // A constructor in checking position: the expected type *is* the
            // encoding, so every annotation of the injection and the field
            // tuple is read off it (docs/inductive-tier0-lowering.md §4).
            ExprKind::Var(name) if self.ctor_here(cx, name).is_some() => {
                let (ind, i) = self.ctor_here(cx, name).expect("just checked");
                self.build_ctor(cx, &ind, i, &[], expected, lvl, e.span)
            }
            ExprKind::Call { name, args, explicit: false }
                if self.ctor_here(cx, name).is_some() =>
            {
                let (ind, i) = self.ctor_here(cx, name).expect("just checked");
                self.build_ctor(cx, &ind, i, args, expected, lvl, e.span)
            }
            _ => {
                let (t, _, _) = self.elab_infer(cx, e)?;
                Ok(t)
            }
        }
    }

    /// Inference mode: returns the elaborated term with its canonical type
    /// and level.
    fn elab_infer(&self, cx: &Cx, e: &Expr) -> R<(Term, Type, Level)> {
        match &e.kind {
            // A goal is its statement; with nothing to check against there is
            // no statement to defer, so holes are checking-only (like `refl`).
            ExprKind::Hole(_) => err(
                "a hole here has no expected type — annotate it (`let p: T = ?;`) \
                 or write the call fully explicitly (`@f(a, b, ?p)`)",
                e.span,
            ),
            ExprKind::Num(n) => {
                let mut t = Term::Zero;
                for _ in 0..*n {
                    t = Term::Succ(Rc::new(t));
                }
                Ok((t, Type::Nat, Level::Zero))
            }
            ExprKind::Var(name) => self.resolve(cx, name, e.span),
            ExprKind::Call { name, args, explicit } => {
                if name == "Succ" {
                    let [arg] = args.as_slice() else {
                        return err("`Succ` takes exactly one argument", e.span);
                    };
                    let arg = self.elab_check(cx, arg, &Type::Nat, &Level::Zero)?;
                    return Ok((Term::Succ(Rc::new(arg)), Type::Nat, Level::Zero));
                }
                // `inj(p)` / `inj(k, p)`: the field equations of an equation
                // between the same constructor (§6.2). The field index is a
                // literal, so `p.inj(1)` reads as the second field's equation.
                if name == "inj" && !self.shadowed(cx, name) {
                    let (k, arg) = match args.as_slice() {
                        [arg] => (0, arg),
                        [k, arg] => match k.kind {
                            ExprKind::Num(k) => (k as usize, arg),
                            _ => return err("`inj`'s field index must be a numeral", k.span),
                        },
                        _ => return err("`inj` takes `(proof)` or `(field, proof)`", e.span),
                    };
                    return self.build_inj(cx, k, arg, e.span);
                }
                if name == "absurd" && !self.shadowed(cx, name) {
                    return err(
                        "`absurd` needs an expected type: use it in checking position \
                         (a `theorem` body, an annotated `let`, or an argument)",
                        e.span,
                    );
                }
                if let Some((ind, i)) = self.ctor_here(cx, name) {
                    return self.infer_ctor(cx, &ind, i, args, e.span);
                }
                if cx.selfref.as_ref().is_some_and(|s| s.name == *name) {
                    return self.elab_self_call(cx, args, *explicit, e.span);
                }
                let mask = self.implicit_mask(name);
                let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                // Fully-explicit call (`@f`, or a callee with no implicits):
                // apply the arguments positionally down the Π spine.
                if *explicit || !mask.iter().any(|&b| b) {
                    self.apply_explicit(cx, name, head, ty, lvl, args)
                } else {
                    self.apply_implicit(cx, name, head, ty, lvl, args, &mask, e.span)
                }
            }
            ExprKind::Match { motive: Some((bind, m)), scrut, arms } => {
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                let mut mcx = cx.clone();
                mcx.push(bind.clone(), scrut_ty.clone(), scrut_lvl.clone());
                let (motive, mlvl) = self.elab_ty(&mcx, m)?;
                let result = motive.apply_local(
                    &LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())),
                );
                let t = self.elab_match(
                    cx, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, mlvl.clone(), e.span,
                )?;
                Ok((t, result, mlvl))
            }
            ExprKind::Match { motive: None, .. } => err(
                "`match` in inference position needs a motive: `match e as z -> T { … }`",
                e.span,
            ),
            ExprKind::J { proof, y, p, motive, case } => {
                let (proof_t, proof_ty, _) = self.elab_infer(cx, proof)?;
                let head = self.whnf(cx, &proof_ty, proof.span)?;
                let Type::Id { level, ty, lhs, rhs } = head else {
                    return err("`j` needs a proof of an `=` type", proof.span);
                };
                // Motive context: Γ, y : S, p : Id(S, a, y).
                let mut mcx = cx.clone();
                mcx.push(y.clone(), (*ty).clone(), level.clone());
                let p_ty = Type::Id {
                    level: level.clone(),
                    ty: Rc::new(ty.shift_local(1)),
                    lhs: Rc::new(lhs.shift_local(1)),
                    rhs: Rc::new(Term::Var(LocalVar(0))),
                };
                mcx.push(p.clone(), p_ty, level.clone());
                let (motive_t, mlvl) = self.elab_ty(&mcx, motive)?;
                // case : M[a/y, refl/p]
                let refl = Term::Refl {
                    level: level.clone(),
                    ty: Rc::clone(&ty),
                    tm: Rc::clone(&lhs),
                };
                let case_ty = motive_t.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .extended(Rc::clone(&lhs))
                        .extended(Rc::new(refl)),
                );
                let case_t = self.elab_check(cx, case, &case_ty, &mlvl)?;
                // result : M[b/y, proof/p]
                let proof_rc = Rc::new(proof_t);
                let result = motive_t.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .extended(Rc::clone(&rhs))
                        .extended(Rc::clone(&proof_rc)),
                );
                let t = Term::J {
                    ty_level: level.clone(),
                    motive_level: mlvl.clone(),
                    ty,
                    lhs,
                    motive: Rc::new(motive_t),
                    case: Rc::new(case_t),
                    rhs,
                    proof: proof_rc,
                };
                Ok((t, result, mlvl))
            }
            ExprKind::Refl => err(
                "`refl` needs an expected type (checking position or `as` motive)",
                e.span,
            ),
        }
    }

    /// Elaborate a `match` given its scrutinee and its (already elaborated)
    /// motive, scoped over one extra local `z` of the scrutinee's type.
    /// Dispatch is by the scrutinee's type: `Nat` is the kernel's own
    /// recursor, a declared inductive is the tier-0 case tree
    /// (docs/inductive-tier0-lowering.md §5).
    #[allow(clippy::too_many_arguments)]
    fn elab_match(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let head = self.whnf(cx, scrut_ty, span)?;
        if let Some(ind) = self.tag_of(&head) {
            return self
                .elab_match_data(cx, &ind, arms, scrut_t, &head, scrut_lvl, motive, mlvl, span);
        }
        if matches!(head, Type::Empty { level: Level::Zero }) {
            // An inductive with no constructors: absurdity elimination. All of
            // them share the kernel type `Empty` (§3.3), and none has an
            // inhabitant to confuse, so no tag is needed to dispatch.
            if !arms.is_empty() {
                return err("this type has no constructors, so `match` takes no arms", span);
            }
            return Ok(Term::ElimEmpty {
                level: mlvl,
            scrut_level: Level::Zero,
                motive: Rc::new(motive),
                scrut: Rc::new(scrut_t),
            });
        }
        if !matches!(head, Type::Nat) {
            return err("`match` needs a `Nat` or a declared inductive", span);
        }
        self.elab_match_nat(cx, arms, scrut_t, motive, mlvl, span)
    }

    /// `match` on `Nat`: the kernel's `elim_Nat`, with the arms named `Zero`
    /// and `Succ(k)` (or the low-level `Succ(k, ih)`).
    fn elab_match_nat(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrut_t: Term,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let mut zero: Option<&Arm> = None;
        let mut succ: Option<&Arm> = None;
        for a in arms {
            let slot = match a.ctor.as_str() {
                "Zero" => &mut zero,
                "Succ" => &mut succ,
                other => {
                    return err(format!("`{other}` is not a constructor of `Nat`"), a.span)
                }
            };
            if slot.replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
        }
        let (Some(zero), Some(succ)) = (zero, succ) else {
            return err("`match` on `Nat` needs both a `Zero` and a `Succ(k)` arm", span);
        };
        if !zero.binders.is_empty() {
            return err("`Zero` binds no fields", zero.span);
        }
        // `Succ(k)` is the unified form (ih = guarded self-call); `Succ(k, ih)`
        // stays as the low-level explicit fallback (issues/match-recursion.md).
        let (k, ih) = match succ.binders.as_slice() {
            [k] => (k, None),
            [k, ih] => (k, Some(ih)),
            _ => return err("`Succ` binds `(k)` or `(k, ih)`", succ.span),
        };
        let (zero, succ_body) = (&zero.body, &succ.body);
        let _ = span;
        // base : M[Zero/z]
        let base_ty =
            motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero)));
        let base = self.elab_check(cx, zero, &base_ty, &mlvl)?;
        // step context: Γ, k : Nat, ih : M[k/z]  (M scoped in Γ,z).
        let mut scx = cx.clone();
        scx.push(k.clone(), Type::Nat, Level::Zero);
        let ih_ty = motive
            .apply_local(&embed(&cx.gamma, 1).extended(Rc::new(Term::Var(LocalVar(0)))));
        // The unified arm `Succ(k)` binds the ih anyway — the recursor demands
        // it — but under a name the surface cannot spell, because it is
        // reached by a guarded self-call instead.
        scx.push(ih.cloned().unwrap_or_else(|| "#ih".into()), ih_ty, mlvl.clone());
        if ih.is_none() {
            // Does this match descend on one of the declaration's own
            // parameters? If so, self-calls in the arm become the ih. If not
            // (a nested match on some other term), the enclosing arm's guard —
            // if any — still stands.
            scx.guard = self
                .descends_on_param(cx, &scrut_t)
                .map(|dec| {
                    Rc::new(Guard {
                        dec,
                        pred_pos: cx.names.len(),
                        ih_pos: cx.names.len() + 1,
                    })
                })
                .or_else(|| cx.guard.clone());
        }
        // step : M[Succ k/z] in Γ, k, ih.
        let step_ty = motive.apply_local(
            &embed(&cx.gamma, 2)
                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))),
        );
        let step = self.elab_check(&scx, succ_body, &step_ty, &mlvl)?;
        Ok(Term::ElimNat {
            level: mlvl,
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::new(scrut_t),
        })
    }

    /// Is `scrut` (already elaborated) exactly one of the enclosing
    /// declaration's parameters? Returns its parameter index — the argument
    /// position the recursion descends on.
    fn descends_on_param(&self, cx: &Cx, scrut: &Term) -> Option<usize> {
        let s = cx.selfref.as_ref()?;
        let Term::Var(LocalVar(i)) = scrut else { return None };
        let pos = cx.names.len() - 1 - *i as usize;
        (pos < s.params.len()).then_some(pos)
    }

    /// A local variable by absolute position (outermost first), as
    /// [`Self::resolve`] would return it.
    fn local(&self, cx: &Cx, pos: usize) -> (Term, Type, Level) {
        let idx = (cx.names.len() - 1 - pos) as u32;
        let entry = &cx.gamma.entries[pos];
        (Term::Var(LocalVar(idx)), entry.ty.shift_local(idx + 1), entry.level.clone())
    }

    /// Lower a call to the enclosing declaration's own name
    /// (issues/match-recursion.md). The termination analysis is deliberately
    /// strict: the call must sit inside a `match` arm that descends on one of
    /// the declaration's parameters, must be saturated, must pass the arm's
    /// predecessor in the decreasing position, and must pass every other
    /// parameter *unchanged*. Under exactly those conditions the recursive
    /// result is definitionally the arm's induction hypothesis, so the
    /// lowering is a variable — no motive surgery, no fixpoint.
    ///
    /// The analysis is untrusted: it can only *reject*. Anything it lets
    /// through still has to typecheck as an `elim_Nat` in the kernel.
    fn elab_self_call(
        &self,
        cx: &Cx,
        args: &[Expr],
        explicit: bool,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let s = Rc::clone(cx.selfref.as_ref().expect("self-call outside a declaration"));
        let name = &s.name;
        let Some(g) = cx.guard.clone() else {
            return err(
                format!(
                    "recursive call to `{name}` is not structurally guarded: it must occur \
                     inside a `match` on one of `{name}`'s own parameters"
                ),
                span,
            );
        };
        // Which parameter each surface argument fills: implicits are omitted
        // unless the call is `@`-marked.
        let positions: Vec<usize> = (0..s.params.len())
            .filter(|&j| explicit || !s.params[j].1)
            .collect();
        if !positions.contains(&g.dec) {
            return err(
                format!(
                    "`{name}` recurses on its implicit parameter `{}`; pass it explicitly \
                     (`@{name}(…)`) to make the recursive call",
                    s.params[g.dec].0
                ),
                span,
            );
        }
        if args.len() != positions.len() {
            return err(
                format!(
                    "recursive call to `{name}` must pass all {} argument(s), found {}",
                    positions.len(),
                    args.len()
                ),
                span,
            );
        }
        for (arg, j) in args.iter().zip(positions) {
            // Compare by *binder*, not by name, so shadowing cannot fake a
            // guarded call.
            let want = if j == g.dec { g.pred_pos } else { j };
            let (arg_t, _, _) = self.elab_infer(cx, arg)?;
            let matches_binder = matches!(
                arg_t, Term::Var(LocalVar(i)) if cx.names.len() - 1 - i as usize == want
            );
            if matches_binder {
                continue;
            }
            return if j == g.dec {
                err(
                    format!(
                        "recursive call to `{name}` must descend: argument `{}` has to be \
                         `{}`, the predecessor bound by the enclosing `match`",
                        s.params[j].0, cx.names[g.pred_pos]
                    ),
                    arg.span,
                )
            } else {
                err(
                    format!(
                        "recursive call to `{name}` must pass `{}` unchanged: the induction \
                         hypothesis fixes every non-decreasing parameter (generalizing a \
                         varying argument into the motive is not supported yet)",
                        s.params[j].0
                    ),
                    arg.span,
                )
            };
        }
        Ok(self.local(cx, g.ih_pos))
    }

    /// Synthesize the dependent motive for a motive-less `match` in checking
    /// position. If the scrutinee elaborates to a local variable `x`, the
    /// motive over `Γ, z : Nat` is the expected type with every occurrence of
    /// `x` abstracted to `z` (the "clear-and-generalize" move); otherwise the
    /// scrutinee is not a variable and no dependency can be recovered, so we
    /// fall back to the non-dependent motive (expected, weakened under `z`).
    ///
    /// Both branches are pure kernel substitutions — no metas. The abstraction
    /// is `expected↑¹` (weaken into `Γ, z`) composed with the swap
    /// `Var(x+1) ↦ z`; applying `[x/z]` to it recovers `expected`, which is
    /// exactly the eliminator's motive obligation `M[scrut/z] = expected`.
    fn synth_motive(
        &self,
        cx: &Cx,
        scrut_t: &Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        expected: &Type,
    ) -> Type {
        // Weaken the expected type into `Γ, z` (z = LocalVar 0, unused).
        let weak = expected.shift_local(1);
        let Term::Var(LocalVar(i)) = scrut_t else {
            return weak;
        };
        // Swap substitution over `Γ, z`: identity except the (shifted)
        // scrutinee `Var(i+1)` maps to `z = Var(0)`.
        let mut ext = cx.gamma.clone();
        ext.entries
            .push(CtxEntry { ty: Rc::new(scrut_ty.clone()), level: scrut_lvl.clone() });
        let mut swap = LocalSubst::id(&ext);
        // `id` puts the outermost entry at index 0: `Var(i+1)` sits at
        // position `|Γ| - 1 - i` (see LocalSubst::id).
        let g = cx.gamma.entries.len() as u32;
        swap.terms[(g - 1 - i) as usize] = Rc::new(Term::Var(LocalVar(0)));
        weak.apply_local(&swap)
    }

    /// Is this name bound by something the user wrote? Builtins give way to
    /// locals, `let` aliases and declarations, so none of them is a keyword.
    fn shadowed(&self, cx: &Cx, name: &str) -> bool {
        cx.names.iter().any(|n| n == name)
            || cx.aliases.iter().any(|a| a.name == *name)
            || self.globals.contains_key(name)
    }

    /// The constructor this name refers to *here* — `None` when it is not a
    /// constructor, or when a local binder or `let` alias shadows it.
    fn ctor_here(&self, cx: &Cx, name: &str) -> Option<(Rc<Inductive>, usize)> {
        if cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| a.name == *name) {
            return None;
        }
        self.ctor_of(name)
    }

    /// A constructor used where nothing is checking it. Only possible when the
    /// declaration has no type parameters — otherwise there is nothing to
    /// determine the instantiation, and an annotation is required (§2:
    /// parameters are monomorphized, not inferred).
    fn infer_ctor(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        // Type arguments are recovered only from a field whose type *is* a
        // parameter (`Some(A)`), by inferring that argument. Deliberately
        // narrow: anything deeper is unification, which belongs to
        // issues/elab-unifier-completeness.md, not here. A `None` on its own
        // is genuinely ambiguous and says so.
        let mut sols: Vec<Option<(Type, Level)>> = vec![None; ind.params.len()];
        for (f, arg) in self.ctor_fields(ind, i).iter().zip(args) {
            let TyKind::Named { name, args: targs } = &f.kind else { continue };
            if !targs.is_empty() {
                continue;
            }
            let Some(p) = ind.params.iter().position(|p| p == name) else { continue };
            if sols[p].is_none() {
                let (_, ty, lvl) = self.elab_infer(cx, arg)?;
                sols[p] = Some((ty, lvl));
            }
        }
        let mut targs = Vec::with_capacity(sols.len());
        for (p, sol) in ind.params.iter().zip(sols) {
            let Some(sol) = sol else {
                return err(
                    format!(
                        "cannot infer the type argument `{p}` of `{}` here — annotate the \
                         expression (`let x: {}<…> = …;`) or use it where a type is expected",
                        ind.name, ind.name
                    ),
                    span,
                );
            };
            targs.push(sol);
        }
        let (ty, lvl) = self.lower_instance(cx, ind, &targs, span)?;
        let t = self.build_ctor(cx, ind, i, args, &ty, &lvl, span)?;
        Ok((t, ty, lvl))
    }

    // -- application (explicit + implicit spines) ---------------------------

    /// The implicit-parameter mask of a callable global (empty for locals,
    /// builtins, and unknown names — none of which take implicits).
    fn implicit_mask(&self, name: &str) -> Vec<bool> {
        self.params_of(name).iter().map(|p| p.implicit).collect()
    }

    /// The parameters of a callable global, for defaulting goal names.
    fn params_of(&self, name: &str) -> Rc<Vec<ParamMeta>> {
        match self.globals.get(name) {
            Some(GlobalInfo::Def { params, .. } | GlobalInfo::Theorem { params, .. }) => {
                Rc::clone(params)
            }
            None => Rc::new(Vec::new()),
        }
    }

    /// Positional application down the Π spine — the stage-1 behaviour, reused
    /// for `@`-marked calls and callees with no implicits. Supports partial
    /// application (fewer args than parameters yields a function value).
    fn apply_explicit(
        &self,
        cx: &Cx,
        name: &str,
        head: Term,
        ty: Type,
        lvl: Level,
        args: &[Expr],
    ) -> R<(Term, Type, Level)> {
        let (mut t, mut ty, mut lvl) = (head, ty, lvl);
        // Positional, so argument `i` is parameter `i`: a hole here defaults
        // its name to that parameter's ("proof-parameter names are API").
        let params = self.params_of(name);
        for (i, arg) in args.iter().enumerate() {
            let head = self.whnf(cx, &ty, arg.span)?;
            let Type::Pi { dom_level, cod_level, dom, cod } = head else {
                return err(format!("`{name}` is applied to too many arguments"), arg.span);
            };
            let hint = params.get(i).map(|p| (name, p.name.as_str()));
            let arg_t = self.elab_check_hinted(cx, arg, &dom, &dom_level, hint)?;
            let arg_rc = Rc::new(arg_t);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
            lvl = cod_level.clone();
            t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg: arg_rc };
        }
        Ok((t, ty, lvl))
    }

    /// Application with implicit-argument insertion
    /// (issues/elab-stage2-metas.md). Each implicit parameter becomes a fresh
    /// metavariable — represented, per the architecture, as an *innermost*
    /// Ψ-binding: occurrences are `?m^{id_Γ}` (`GlobalTm` at index `< n`),
    /// solutions are recorded by unifying each explicit argument's inferred
    /// type against the parameter's domain, and the whole meta block is
    /// discharged by one global substitution σ (`apply_global`) that also
    /// renumbers the committed globals back down. The kernel re-checks the
    /// zonked term, so a mis-solved meta is a rejection, never unsoundness.
    ///
    /// Unlike [`Self::apply_explicit`] this requires *saturating* the spine
    /// (every explicit parameter needs an argument): mixing partial
    /// application with implicit insertion is ambiguous, so it is refused.
    #[allow(clippy::too_many_arguments)]
    fn apply_implicit(
        &self,
        cx: &Cx,
        name: &str,
        head: Term,
        callee_ty: Type,
        callee_lvl: Level,
        args: &[Expr],
        mask: &[bool],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let n = mask.iter().filter(|&&b| b).count() as u32;
        // Scratch world: the `n` metas take the innermost Ψ indices `[0, n)`;
        // committed globals shift up by `n` so nothing collides.
        let mut t = head.shift_global(n);
        let mut ty = callee_ty.shift_global(n);
        let mut lvl = callee_lvl;
        let mut sols: Vec<Option<Rc<Term>>> = vec![None; n as usize];
        let mut next_meta = 0u32;
        let mut args = args.iter();
        for &is_implicit in mask {
            let head_ty = self.whnf(cx, &ty, span)?;
            let Type::Pi { dom_level, cod_level, dom, cod } = head_ty else {
                return err(format!("`{name}` is applied to too many arguments"), span);
            };
            let arg_rc = if is_implicit {
                // A fresh metavariable `?m^{id_Γ}` at Ψ-index `next_meta`.
                let m = Term::GlobalTm {
                    var: GlobalVar(next_meta),
                    subst: LocalSubst::id(&cx.gamma),
                };
                next_meta += 1;
                Rc::new(m)
            } else {
                let arg = args.next().ok_or_else(|| ElabError::Elab {
                    msg: format!("`{name}` is applied to too few arguments"),
                    span,
                })?;
                let (arg_t, arg_ty, _) = self.elab_infer(cx, arg)?;
                // Drive meta solutions from the argument's actual type, then
                // splice the argument into the scratch world.
                unify_ty(&dom, &arg_ty, n, &mut sols);
                Rc::new(arg_t.shift_global(n))
            };
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
            lvl = cod_level.clone();
            t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg: arg_rc };
        }
        if args.next().is_some() {
            return err(format!("`{name}` is applied to too many arguments"), span);
        }
        // Discharge the meta block: `entries[k]` is the payload for Ψ-index
        // `n-1-k` (apply_global's convention), so it takes `sols[n-1-k]`.
        let mut entries = Vec::with_capacity(n as usize);
        for k in 0..n {
            let sol = sols[(n - 1 - k) as usize].clone().ok_or_else(|| ElabError::Elab {
                msg: format!("could not infer an implicit argument of `{name}`"),
                span,
            })?;
            entries.push(GlobalEntry::Tm(sol));
        }
        let sigma = GlobalSubst { entries };
        Ok((t.apply_global(&sigma), ty.apply_global(&sigma), lvl))
    }

    // -- names --------------------------------------------------------------

    fn resolve(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)> {
        if name == "Zero" {
            return Ok((Term::Zero, Type::Nat, Level::Zero));
        }
        // Locals and `let` aliases, innermost first. An alias bound at depth
        // `d` shadows every binder at position `< d` and is shadowed by the
        // rest, which is what compares the two here.
        let local_pos = cx.names.iter().rposition(|n| n == name);
        let alias = cx.aliases.iter().rev().find(|a| a.name == *name);
        match (local_pos, alias) {
            (Some(pos), Some(a)) if a.depth <= pos => return Ok(self.local(cx, pos)),
            (_, Some(a)) => {
                // Inlined at the use site, shifted across the binders pushed
                // since it was bound (same as a `fn` definition's globals).
                let by = (cx.names.len() - a.depth) as u32;
                return Ok(((*a.term).shift_local(by), a.ty.shift_local(by), a.level.clone()));
            }
            (Some(pos), None) => return Ok(self.local(cx, pos)),
            (None, None) => {}
        }
        if let Some((ind, i)) = self.ctor_of(name) {
            return self.infer_ctor(cx, &ind, i, &[], span);
        }
        // The enclosing declaration's own name: only a saturated, guarded
        // *call* means anything (it is the induction hypothesis, not a value).
        if cx.selfref.as_ref().is_some_and(|s| s.name == name) {
            return err(
                format!("`{name}` can only be used here as a saturated recursive call"),
                span,
            );
        }
        match self.globals.get(name) {
            Some(GlobalInfo::Def { term, ty, level, psi_len, .. }) => {
                // Shift global indices across whatever Ψ grew since the def
                // was elaborated (GlobalVar counts from the innermost end),
                // plus the current declaration's goal prefix.
                let by = self.psi.bindings.len() as u32 + self.goal_base - psi_len;
                Ok(((**term).shift_global(by), (**ty).shift_global(by), level.clone()))
            }
            Some(GlobalInfo::Theorem { abs, .. }) => {
                let len = self.psi.bindings.len() as u32;
                // The goals sit innermost, so a committed binding is that much
                // further out.
                let var = GlobalVar(len - 1 - abs + self.goal_base);
                let GlobalBinding::Tm { ty, level, .. } =
                    &self.psi.bindings[*abs as usize]
                else {
                    unreachable!("theorem index points at a non-Trm binding");
                };
                // Stored scoped in its prefix of Ψ; rescope to the full Ψ
                // (the kernel's own lookup convention, typing.rs). This needs
                // no goal offset of its own: `var.0` already carries it.
                let ty = ty.shift_global(var.0 + 1);
                // The theorem is closed (· ⊢), so the delayed substitution
                // is the empty map out of the current Γ.
                let subst = LocalSubst {
                    tail: SubstTail::Empty {
                        len: cx.gamma.entries.len() as u32,
                        base: cx.gamma.base,
                    },
                    terms: vec![],
                };
                Ok((Term::GlobalTm { var, subst }, ty, level.clone()))
            }
            None => err(format!("unbound name `{name}`"), span),
        }
    }

    // -- kernel oracle ------------------------------------------------------

    fn whnf(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type> {
        whnf_type(ty, &cx.gamma, self.fuel)
            .map_err(|_| ElabError::Elab { msg: "out of fuel reducing a type".into(), span })
    }
}

/// The enclosing declaration, in scope throughout its own body so that a
/// structurally guarded self-call can lower to the induction hypothesis
/// (issues/match-recursion.md). Nothing else can reference it: the name is
/// only registered as a global once the declaration is checked.
struct SelfRef {
    name: String,
    /// `(parameter name, implicit?)` in declaration order. Parameter `j` is
    /// bound at position `j` of the body's `Cx` (the telescope goes first).
    params: Vec<(String, bool)>,
}

/// What a guarded self-call must look like inside a `Succ(k)` arm, and what
/// it lowers to. Positions are *absolute* (indices into `cx.names`, outermost
/// first) so they stay valid as inner binders are pushed.
struct Guard {
    /// Index of the parameter the recursion descends on.
    dec: usize,
    /// Position of the predecessor `k` bound by the arm.
    pred_pos: usize,
    /// Position of the arm's (hidden) induction-hypothesis binder.
    ih_pos: usize,
}

/// Elaboration context: kernel Γ plus the parallel name list
/// (`names[j]` names `gamma.entries[j]`, outermost first).
#[derive(Clone)]
struct Cx {
    names: Vec<String>,
    gamma: LocalCtx,
    /// The declaration being elaborated, once its telescope is in scope.
    selfref: Option<Rc<SelfRef>>,
    /// Set inside a `Succ(k)` arm; `None` outside every such arm, where a
    /// self-call has no induction hypothesis to become.
    guard: Option<Rc<Guard>>,
    /// `let` bindings in scope, outermost first. Not kernel binders: an alias
    /// is inlined at each use, so `Γ` is unchanged.
    aliases: Vec<Rc<Alias>>,
    /// An `inductive`'s type parameters, while its field types are being
    /// lowered at an instantiation. Empty everywhere else: type parameters are
    /// monomorphized, so they never survive into a kernel term.
    tyvars: Vec<(String, Type, Level)>,
}

/// A `let`-bound name: the elaborated right-hand side, inlined at every use
/// (the same doctrine as an inlined `fn`). `depth` is `names.len()` at the
/// binding, which is what decides shadowing against ordinary binders and how
/// far a use must be shifted.
struct Alias {
    name: String,
    depth: usize,
    term: Rc<Term>,
    ty: Type,
    level: Level,
}

impl Cx {
    fn empty() -> Cx {
        Cx {
            names: vec![],
            gamma: LocalCtx { base: CtxBase::Nil, entries: vec![] },
            selfref: None,
            guard: None,
            aliases: vec![],
            tyvars: vec![],
        }
    }

    fn push(&mut self, name: String, ty: Type, level: Level) {
        self.names.push(name);
        self.gamma.entries.push(CtxEntry { ty: Rc::new(ty), level });
    }
}

/// Syntactic upper bound on the goals a declaration can raise: every `?` in
/// it. An *upper* bound, not the count — `calc` clones sub-expressions into
/// its `@trans` spine (parser.rs) and the elaborator visits some expressions
/// twice — which is why goals are numbered in creation order and the unused
/// slots are padded. Under-counting is impossible: nothing invents a hole.
fn count_holes(decl: &Decl) -> u32 {
    fn ty(t: &Ty, n: &mut u32) {
        match &t.kind {
            TyKind::Nat => {}
            TyKind::Eq(a, b) => {
                expr(a, n);
                expr(b, n);
            }
            TyKind::Named { args, .. } => args.iter().for_each(|a| ty(a, n)),
        }
    }
    fn expr(e: &Expr, n: &mut u32) {
        match &e.kind {
            ExprKind::Hole(_) => *n += 1,
            ExprKind::Var(_) | ExprKind::Num(_) | ExprKind::Refl => {}
            ExprKind::Call { args, .. } => args.iter().for_each(|a| expr(a, n)),
            ExprKind::Match { scrut, motive, arms } => {
                expr(scrut, n);
                if let Some((_, m)) = motive {
                    ty(m, n);
                }
                arms.iter().for_each(|a| expr(&a.body, n));
            }
            ExprKind::J { proof, motive, case, .. } => {
                expr(proof, n);
                ty(motive, n);
                expr(case, n);
            }
        }
    }
    let mut n = 0;
    for p in &decl.params {
        ty(&p.ty, &mut n);
    }
    ty(&decl.result, &mut n);
    for s in &decl.body.stmts {
        let Stmt::Let { ty: t, expr: e, .. } = s;
        if let Some(t) = t {
            ty(t, &mut n);
        }
        expr(e, &mut n);
    }
    expr(&decl.body.result, &mut n);
    for on in &decl.body.ons {
        if let OnTarget::Stmt(t) = &on.target {
            ty(t, &mut n);
        }
        expr(&on.expr, &mut n);
    }
    n
}

/// Strengthen a discharge out of the goal world. An `on` right-hand side is
/// elaborated *with* the goal prefix in scope — it has to be, since the goal's
/// context and statement live there — but a `GlobalSubst` payload is scoped in
/// the source Ψ, below the prefix (subst.rs). Applying a `g`-entry σ whose
/// payloads are never reached renumbers every committed global back down by
/// `g`. "Never reached" is exactly the `frozen` restriction: no new hole, so
/// no goal occurrence survives in the payload to meet a dummy.
fn strengthen_global(t: &Term, g: u32) -> Term {
    if g == 0 {
        return t.clone();
    }
    let entries = (0..g).map(|_| GlobalEntry::Tm(Rc::new(Term::Zero))).collect();
    t.apply_global(&GlobalSubst { entries })
}

/// The identity substitution of `gamma`, weakened so its source is `gamma`
/// extended by `extra` fresh entries: maps a term scoped in `gamma, z` (once
/// `extended`) into `gamma` + the extra binders.
fn embed(gamma: &LocalCtx, extra: u32) -> LocalSubst {
    let m = gamma.entries.len() as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty { len: m + extra, base: CtxBase::Nil },
        CtxBase::Var(g) => SubstTail::Wk { len: m + extra, ctx_var: g },
    };
    let terms = (0..m)
        .map(|j| Rc::new(Term::Var(LocalVar(m + extra - 1 - j))))
        .collect();
    LocalSubst { tail, terms }
}

/// Best-effort structural unification driving implicit-argument solutions
/// (issues/elab-stage2-metas.md). `pat` is a parameter domain in the scratch
/// world (metavariables at Ψ-indices `< n`); `subj` is an argument's inferred
/// type. Solving is deliberately incomplete: this mirrors the fragment of
/// `conv.rs` the Nat suite exercises (`Id`/`Nat` congruence), records a
/// solution whenever a meta meets a rigid subterm, and otherwise makes no
/// claim — an unsolved meta is reported by the caller, a *wrong* solution is
/// caught by the kernel's re-check. It never fails: it only ever *learns*.
fn unify_ty(pat: &Type, subj: &Type, n: u32, sols: &mut [Option<Rc<Term>>]) {
    if let (
        Type::Id { ty: t1, lhs: a1, rhs: b1, .. },
        Type::Id { ty: t2, lhs: a2, rhs: b2, .. },
    ) = (pat, subj)
    {
        unify_ty(t1, t2, n, sols);
        unify_tm(a1, a2, n, sols);
        unify_tm(b1, b2, n, sols);
    }
    // Nat vs Nat and every other pairing: nothing to solve here.
}

/// Term-level companion of [`unify_ty`]. When `pat` is an unsolved
/// metavariable under a variable renaming (the Miller pattern condition —
/// here always the identity `id_Γ`, so the solution is the subject verbatim),
/// record it; otherwise recurse through matching heads toward nested metas.
fn unify_tm(pat: &Term, subj: &Term, n: u32, sols: &mut [Option<Rc<Term>>]) {
    if let Term::GlobalTm { var, subst } = pat
        && var.0 < n
    {
        let is_pattern = subst.terms.iter().all(|t| matches!(**t, Term::Var(_)));
        if is_pattern && sols[var.0 as usize].is_none() {
            sols[var.0 as usize] = Some(Rc::new(subj.clone()));
        }
        return;
    }
    match (pat, subj) {
        (Term::Succ(a), Term::Succ(b)) => unify_tm(a, b, n, sols),
        (Term::App { fun: f1, arg: a1, .. }, Term::App { fun: f2, arg: a2, .. }) => {
            unify_tm(f1, f2, n, sols);
            unify_tm(a1, a2, n, sols);
        }
        _ => {}
    }
}
