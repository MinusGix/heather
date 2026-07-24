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

use std::collections::HashMap;
use std::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_type;
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{self, TypeError, DEFAULT_FUEL};
use heather_syntax::{parse_file, Decl, DeclKind, Expr, ExprKind, ParseError, Span, Ty, TyKind};

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
}

impl From<ParseError> for ElabError {
    fn from(e: ParseError) -> Self {
        ElabError::Parse(e)
    }
}

type R<T> = Result<T, ElabError>;

fn err<T>(msg: impl Into<String>, span: Span) -> R<T> {
    Err(ElabError::Elab { msg: msg.into(), span })
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
    },
    /// A `theorem`: absolute position of its `Trm_c` binding in Ψ.
    Theorem { abs: u32 },
}

pub struct Elaborator {
    psi: GlobalCtx,
    globals: HashMap<String, GlobalInfo>,
    fuel: u64,
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

impl Elaborator {
    /// An empty elaborator (no prelude).
    pub fn new() -> Self {
        Elaborator { psi: GlobalCtx::default(), globals: HashMap::new(), fuel: DEFAULT_FUEL }
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
        for decl in &file.decls {
            self.elab_decl(decl)?;
        }
        Ok(())
    }

    /// The accumulated global context (theorem statements).
    pub fn psi(&self) -> &GlobalCtx {
        &self.psi
    }

    // -- declarations -------------------------------------------------------

    fn elab_decl(&mut self, decl: &Decl) -> R<()> {
        if self.globals.contains_key(&decl.name) {
            return err(format!("duplicate name `{}`", decl.name), decl.span);
        }
        // Elaborate the parameter telescope.
        let mut cx = Cx::empty();
        let mut param_info: Vec<(Type, Level)> = Vec::new();
        for p in &decl.params {
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            cx.push(p.name.clone(), ty.clone(), lvl.clone());
            param_info.push((ty, lvl));
        }
        // Result type and body (checked against it).
        let (res_ty, res_lvl) = self.elab_ty(&cx, &decl.result)?;
        let body = self.elab_check(&cx, &decl.body, &res_ty, &res_lvl)?;

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

        // The kernel is the gate: check the statement, then the term.
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        typing::check_type(&self.psi, 0, Layer::Prog, &empty, &stmt, &stmt_lvl, self.fuel)
            .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), err: e })?;
        typing::check_term(&self.psi, 0, Layer::Code, &empty, &term, &stmt, &stmt_lvl, self.fuel)
            .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), err: e })?;

        match decl.kind {
            DeclKind::Fn => {
                self.globals.insert(
                    decl.name.clone(),
                    GlobalInfo::Def {
                        term: Rc::new(term),
                        ty: Rc::new(stmt),
                        level: stmt_lvl,
                        psi_len: self.psi.bindings.len() as u32,
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
                self.globals.insert(decl.name.clone(), GlobalInfo::Theorem { abs });
            }
        }
        Ok(())
    }

    // -- types --------------------------------------------------------------

    fn elab_ty(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
        match &ty.kind {
            TyKind::Nat => Ok((Type::Nat, Level::Zero)),
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
        match &e.kind {
            ExprKind::Refl => {
                let head = self.whnf(cx, expected, e.span)?;
                let Type::Id { level, ty, lhs, .. } = head else {
                    return err("`refl` needs an `==` expected type", e.span);
                };
                Ok(Term::Refl { level, ty, tm: lhs })
            }
            ExprKind::Match { motive: None, .. } => {
                // Non-dependent motive: the expected type, weakened under z.
                let motive = expected.shift_local(1);
                self.elab_match(cx, e, motive, lvl.clone())
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
            ExprKind::Num(n) => {
                let mut t = Term::Zero;
                for _ in 0..*n {
                    t = Term::Succ(Rc::new(t));
                }
                Ok((t, Type::Nat, Level::Zero))
            }
            ExprKind::Var(name) => self.resolve(cx, name, e.span),
            ExprKind::Call(name, args) => {
                if name == "Succ" {
                    let [arg] = args.as_slice() else {
                        return err("`Succ` takes exactly one argument", e.span);
                    };
                    let arg = self.elab_check(cx, arg, &Type::Nat, &Level::Zero)?;
                    return Ok((Term::Succ(Rc::new(arg)), Type::Nat, Level::Zero));
                }
                let (mut t, mut ty, mut lvl) = self.resolve(cx, name, e.span)?;
                for arg in args {
                    let head = self.whnf(cx, &ty, arg.span)?;
                    let Type::Pi { dom_level, cod_level, dom, cod } = head else {
                        return err(
                            format!("`{name}` is applied to too many arguments"),
                            arg.span,
                        );
                    };
                    let arg_t = self.elab_check(cx, arg, &dom, &dom_level)?;
                    let arg_rc = Rc::new(arg_t);
                    ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
                    lvl = cod_level.clone();
                    t = Term::App {
                        fun: Rc::new(t),
                        dom_level,
                        cod_level,
                        dom,
                        cod,
                        arg: arg_rc,
                    };
                }
                Ok((t, ty, lvl))
            }
            ExprKind::Match { motive: Some((bind, m)), .. } => {
                let mut mcx = cx.clone();
                mcx.push(bind.clone(), Type::Nat, Level::Zero);
                let (motive, mlvl) = self.elab_ty(&mcx, m)?;
                let ExprKind::Match { scrut, .. } = &e.kind else { unreachable!() };
                let (scrut_t, _, _) = self.elab_infer(cx, scrut)?;
                let result = motive
                    .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t)));
                let t = self.elab_match(cx, e, motive, mlvl.clone())?;
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
                    return err("`j` needs a proof of an `==` type", proof.span);
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

    /// Elaborate a `match` given its (already elaborated) motive, scoped
    /// over one extra local `z : Nat`.
    fn elab_match(&self, cx: &Cx, e: &Expr, motive: Type, mlvl: Level) -> R<Term> {
        let ExprKind::Match { scrut, zero, succ: (k, ih, succ_body), .. } = &e.kind else {
            unreachable!("elab_match on a non-match");
        };
        let (scrut_t, scrut_ty, _) = self.elab_infer(cx, scrut)?;
        let head = self.whnf(cx, &scrut_ty, scrut.span)?;
        if !matches!(head, Type::Nat) {
            return err("stage 1 `match` only eliminates `Nat`", scrut.span);
        }
        // base : M[Zero/z]
        let base_ty =
            motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero)));
        let base = self.elab_check(cx, zero, &base_ty, &mlvl)?;
        // step context: Γ, k : Nat, ih : M[k/z]  (M scoped in Γ,z).
        let mut scx = cx.clone();
        scx.push(k.clone(), Type::Nat, Level::Zero);
        let ih_ty = motive
            .apply_local(&embed(&cx.gamma, 1).extended(Rc::new(Term::Var(LocalVar(0)))));
        scx.push(ih.clone(), ih_ty, mlvl.clone());
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

    // -- names --------------------------------------------------------------

    fn resolve(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)> {
        if name == "Zero" {
            return Ok((Term::Zero, Type::Nat, Level::Zero));
        }
        // Locals, innermost first.
        if let Some(pos) = cx.names.iter().rposition(|n| n == name) {
            let idx = (cx.names.len() - 1 - pos) as u32;
            let entry = &cx.gamma.entries[pos];
            return Ok((
                Term::Var(LocalVar(idx)),
                entry.ty.shift_local(idx + 1),
                entry.level.clone(),
            ));
        }
        match self.globals.get(name) {
            Some(GlobalInfo::Def { term, ty, level, psi_len }) => {
                // Shift global indices across whatever Ψ grew since the def
                // was elaborated (GlobalVar counts from the innermost end).
                let by = self.psi.bindings.len() as u32 - psi_len;
                Ok(((**term).shift_global(by), (**ty).shift_global(by), level.clone()))
            }
            Some(GlobalInfo::Theorem { abs }) => {
                let len = self.psi.bindings.len() as u32;
                let var = GlobalVar(len - 1 - abs);
                let GlobalBinding::Tm { ty, level, .. } =
                    &self.psi.bindings[*abs as usize]
                else {
                    unreachable!("theorem index points at a non-Trm binding");
                };
                // Stored scoped in its prefix of Ψ; rescope to the full Ψ
                // (the kernel's own lookup convention, typing.rs).
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

/// Elaboration context: kernel Γ plus the parallel name list
/// (`names[j]` names `gamma.entries[j]`, outermost first).
#[derive(Clone)]
struct Cx {
    names: Vec<String>,
    gamma: LocalCtx,
}

impl Cx {
    fn empty() -> Cx {
        Cx { names: vec![], gamma: LocalCtx { base: CtxBase::Nil, entries: vec![] } }
    }

    fn push(&mut self, name: String, ty: Type, level: Level) {
        self.names.push(name);
        self.gamma.entries.push(CtxEntry { ty: Rc::new(ty), level });
    }
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
