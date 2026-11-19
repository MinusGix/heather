//! `decreases e` — termination by a `Nat` measure
//! (issues/termination-measures.md, docs/language/recursion/termination-measures-design.md).
//!
//! A declaration `fn f(x̄) -> T decreases e { body }` is elaborated as strong
//! induction on a bound for the measure, spelled entirely at the **surface**
//! and handed to the ordinary checker:
//!
//! ```text
//! match Succ(e) as λ z => (x̄) -> nat::Nat::Lt(e, z) -> T {
//!     Zero        => λ x̄ h => match h {},
//!     Succ(k, ih) => λ x̄ h => body[ f(ȳ) ↦ ih(ȳ, nat::Nat::le_trans(Succ(e[ȳ]), e, k, ?decN, h)) ],
//! }(x̄, nat::Nat::lt_succ_self(e))
//! ```
//!
//! …except that the three layers are **named**, not nested inline:
//! `f#body` is the `Succ` arm, `f#rec` is the eliminator, and `f` applies it
//! (`docs/language/recursion/decreases-unfolding-design.md` §2, which amends
//! `docs/language/recursion/termination-measures-design.md` §1/§5). The lifting is what makes the
//! unfolding companions of that document statable; nothing else changes, since
//! a `fn` is transparent and `f#rec(Succ k, …) ≡ f#body(k, f#rec(k), …)` is
//! `refl`.
//!
//! The wrapper is a written-motive `match` with the explicit-ih arm — two
//! features older than this one — and the parameters are re-bound under
//! their own names, so the body reads exactly as written. Each recursive
//! call owes one obligation, `e[ȳ] < e`, a goal hole named `decN` in source
//! order; it is discharged by `on ?decN := …`, and defaults to `omega` where
//! no `on` names it.
//!
//! The obligation is not spelled at the call: it is **lifted** into a
//! declaration of its own, `f#obl_N`, over the binders its statement names
//! (`docs/language/recursion/decreases-unfolding-design.md` §4). `f#body` and both unfolding
//! companions then reference the same opaque `f#obl_N(…)`, so the three
//! spellings of a self-call are identical by construction — which is what an
//! `omega`-defaulted obligation needs, since `omega` reconstructs its
//! certificate against the local context and the three contexts differ.
//!
//! Nothing here is trusted. The rewrite reads names — the declaration's own
//! name for a self-call, the parameters' names for the measure's arguments
//! — and where a name misleads it the emitted term fails to check: the ih's
//! hypothesis binder is at the *elaborated* measure, so a wrong obligation
//! type is refused where the call is written, never accepted.

use heather_syntax::{
    Arm, Block, Decl, DeclKind, Expr, ExprKind, LamBinder, MatchForm, OnStmt, OnTarget, Param,
    ParamOrigin, Pat, Span, Stmt, Ty, TyKind,
};

use crate::{R, err};

/// The obligations a wrapped body owes, one per recursive call in source
/// order: the call's span, the hole's name, the obligation rendered for a
/// diagnostic, and — for a group site the rank rule explains —
/// `docs/language/recursion/mutual-recursion-design.md` §8's sentence.
#[derive(Clone)]
pub(crate) struct Obligations {
    pub(crate) sites: Vec<(Span, String, String, Option<String>)>,
}

impl Obligations {
    /// Reword an `omega` failure at one of this declaration's obligations
    /// into a message that names the obligation and the way to discharge it
    /// by hand. Every other error passes through.
    pub(crate) fn explain(&self, error: crate::ElabError) -> crate::ElabError {
        let crate::ElabError::Elab { msg, span } = &error else {
            return error;
        };
        if !msg.starts_with("`omega` got stuck") {
            return error;
        }
        let Some((_, hole, text, hint)) = self.sites.iter().find(|(s, ..)| s == span) else {
            return error;
        };
        let rank = match hint {
            Some(h) => format!(". {h}"),
            None => String::new(),
        };
        let target = hole.strip_prefix("#decreasing:").map(|n| format!("decreasing {n}"))
            .unwrap_or_else(|| format!("?{hole}"));
        // A `help:` the closer added (the import that would let it read
        // the goal) leads, ahead of the search's own account.
        let (msg, help) = match msg.split_once("\nhelp: ") {
            Some((msg, help)) => (msg, format!(" To have it proved automatically, {help}.")),
            None => (msg.as_str(), String::new()),
        };
        crate::ElabError::Elab {
            msg: format!(
                "this recursive call must decrease the measure, and `{text}` was not \
                 proved automatically.{help} Discharge it by hand: \
                 `on {target} := …;` at the end of the body{rank}. The search said: {msg}"
            ),
            span: *span,
        }
    }
}

/// The closer an obligation nobody discharges by hand defaults to: `omega`,
/// then `bv_omega` where the obligation is over the `toNat` of a word
/// (`Checking::elab_measure_closer`, issues/decreases-word-measures-by-hand.md).
pub(crate) const CLOSER: &str = "__measure_closer";

const K: &str = "__dec_k";
const IH: &str = "__dec_ih";
const H: &str = "__dec_h";
const Z: &str = "__dec_z";

/// One generated declaration and the obligations its own body owes.
#[derive(Clone)]
pub(crate) struct Lowered {
    pub(crate) decl: Decl,
    pub(crate) obligations: Obligations,
}

/// What a `decreases` declaration lowers to: the lifted obligations of §4
/// first — they are what the rest references — then the family of §2.
pub(crate) struct Family {
    pub(crate) obligations: Vec<Lowered>,
    pub(crate) decls: Vec<Lowered>,
    /// How many matches the lowering could give an equation of its own
    /// ([`AutoEqs`]), numbered in walk order.
    pub(crate) auto_candidates: usize,
}

/// Which `match`es on a computed scrutinee, with a recursive call in an arm
/// and no written equation, the body rewrite gives the equation
/// `__dec_meqN : e = pattern` (docs/language/matching/dependent-match-compiler-design.md §4,
/// §8). A lifted obligation is stated over the telescope this rewrite
/// writes, not over the elaborator's context, so its arm's equation has to
/// be a binder there. The equation stays only where an obligation reads
/// it: the declaration is lowered with [`AutoEqs::All`], and again with
/// [`AutoEqs::Only`] the ones its lifted obligations quantify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AutoEqs {
    Off,
    All,
    Only(Vec<usize>),
}

impl AutoEqs {
    fn admits(&self, n: usize) -> bool {
        match self {
            AutoEqs::Off => false,
            AutoEqs::All => true,
            AutoEqs::Only(ns) => ns.contains(&n),
        }
    }
}

/// The candidate number of an [`AutoEqs`] equation binder.
pub(crate) fn auto_eq_index(name: &str) -> Option<usize> {
    name.strip_prefix("__dec_meq")?.parse().ok()
}

/// Type information supplied by ordinary elaboration: constructor fields and
/// inferred locals in a reconstructed telescope. Every recovered annotation
/// is checked again; no query commits a declaration or proof.
///
/// `None` is an honest decline — the site is then not lifted, and `f` falls
/// back to the obligation spelled at the call as it was before.
pub(crate) trait BinderTys {
    fn ctor_fields(&self, scrut: &Ty, ctor: &str) -> Option<Vec<Ty>>;
    fn local_evidence(&self, decl: &Decl, scope: &[Binder], goal: &Ty, arithmetic: bool) -> Option<Expr>;
    fn infer_local(&self, decl: &Decl, signatures: &[(String, Ty)], scope: &[Binder], expr: &Expr) -> Option<Ty>;
    /// The proofs `call` leaves to a default that searches its context, with
    /// their goals over the telescope `scope`. Empty where there is none, or
    /// where a goal has no spelling there.
    fn default_goals(&self, decl: &Decl, signatures: &[(String, Ty)], scope: &[Binder], call: &Expr) -> Vec<FoundGoal>;
    /// Whether the global `callee` has a parameter defaulted to such a search.
    fn has_context_default(&self, callee: &str) -> bool;
    /// Whether some type's member of this base name has one: a method call
    /// `v.name(…)` may then leave a proof to it.
    fn member_has_context_default(&self, name: &str) -> bool;
}

/// A proof a call leaves to its parameter's default: the parameter, the goal
/// at this call, and the default that searches for it.
pub(crate) struct FoundGoal {
    pub(crate) name: String,
    pub(crate) goal: Ty,
    pub(crate) default: Expr,
}

/// A binder in scope during the walk, with the surface type a lifted
/// obligation may quantify it at — `None` where [`BinderTys`] declines to
/// recover a complete annotation.
#[derive(Clone)]
pub(crate) struct Binder {
    pub(crate) name: String,
    pub(crate) ty: Option<Ty>,
    /// A block `let` (the walk's own shared scrutinee among them) is an
    /// alias of its value: a lifted obligation substitutes the value for it
    /// instead of quantifying over it, so that a hypothesis stated about the
    /// alias is still the one the body proves about the value
    /// (issues/decreases-unfold-convoy-scrutinee.md). `None` for a binder
    /// with no value, and for a `let` whose value calls a member (it has no
    /// meaning outside the body).
    pub(crate) value: Option<Expr>,
}

/// The smallest spellable dependent telescope for a goal and its evidence.
/// Unknown unrelated locals are deliberately absent from isolated queries.
pub(crate) fn select_scope<'a>(scope: &'a [Binder], goal: &Ty, evidence: Option<&Expr>) -> Option<Vec<&'a Binder>> {
    let mut needed: Vec<bool> = scope.iter().enumerate().map(|(i, b)| {
        !scope[i + 1..].iter().any(|c| c.name == b.name)
            && (mentions_ty(goal, &b.name)
                || evidence.is_some_and(|e| mentions_context(e, &b.name)))
    }).collect();
    // Only where the goal reads an alias (below).
    let through_alias = (0..scope.len()).any(|i| needed[i] && scope[i].value.is_some());
    loop {
        for i in (0..scope.len()).rev() {
            if !needed[i] { continue; }
            let ty = scope[i].ty.as_ref()?;
            let value = scope[i].value.as_ref();
            for j in (0..i).rev() {
                if mentions_ty(ty, &scope[j].name) || value.is_some_and(|v| mentions_context(v, &scope[j].name)) {
                    if scope[j + 1..].iter().any(|b| b.name == scope[j].name) { return None; }
                    needed[j] = true;
                }
            }
        }
        // An equation in scope about a needed binder — a `match h: e` arm's
        // `h` — is a fact the obligation may need even where neither the
        // goal nor the evidence names it: an argument passed through a `let`
        // alias reaches the goal as the alias, and the arm's equation about
        // the parameter behind it would otherwise be left out. Only then: a
        // goal over the parameters themselves gets its arms' equations by
        // the companions' own transport, which an extra hypothesis breaks.
        if !through_alias { break; }
        let mut grew = false;
        for i in 0..scope.len() {
            if needed[i] || scope[i + 1..].iter().any(|c| c.name == scope[i].name) { continue; }
            let Some(ty) = &scope[i].ty else { continue };
            if !matches!(ty.kind, TyKind::Eq(..)) { continue; }
            let about = (0..scope.len()).any(|j| needed[j] && mentions_ty(ty, &scope[j].name));
            if about {
                needed[i] = true;
                grew = true;
            }
        }
        if !grew { break; }
    }
    Some(scope.iter().zip(needed).filter_map(|(b, needed)| needed.then_some(b)).collect())
}

pub(crate) fn arithmetic_fact(ty: &Ty, goal: &Ty, scope: &[Binder]) -> bool {
    // A squashed fact (a loop's invariant) is read through its squash.
    if let TyKind::Squash(inner) = &ty.kind {
        return arithmetic_fact(inner, goal, scope);
    }
    let shares = || scope.iter().any(|b| mentions_ty(goal, &b.name) && mentions_ty(ty, &b.name));
    // A `match h: e { … }` arm's equation: `omega` reads `n.leb(m) = False`
    // as the guard it states (issues/decreases-measure-record-field-unspelled.md)
    // and `n = Succ(k)` as arithmetic. Any arm equation is a candidate; the
    // trial elaboration decides whether it is used
    // (docs/language/matching/dependent-match-compiler-design.md §8).
    if let TyKind::Eq(..) = &ty.kind {
        return shares();
    }
    let TyKind::OfExpr(e) = &ty.kind else { return false; };
    let ExprKind::App { head, .. } = &e.kind else { return false; };
    let relation = match &head.kind {
        ExprKind::Var(name) => matches!(name.as_str(), "nat::Nat::Lt" | "nat::Nat::Le" | "Lt" | "Le"),
        ExprKind::OpSymbol { symbol, .. } => matches!(symbol.as_str(), "<" | "<="),
        _ => false,
    };
    relation && shares()
}

/// A stored field type at the scrutinee's type arguments: type parameters are
/// monomorphized, so instantiation is a substitution on the surface type. A
/// shape this does not walk is left alone; a wrong instantiation costs a
/// refused `f#obl_N` and the un-lifted fallback, never a wrong proof.
pub(crate) fn instantiate_ty(t: &Ty, m: &[(String, Ty)]) -> Ty {
    let span = t.span;
    let go = |x: &Ty| instantiate_ty(x, m);
    let kind = match &t.kind {
        TyKind::Named { name, args } if args.is_empty() => {
            if let Some((_, ty)) = m.iter().find(|(p, _)| p == name) {
                return ty.clone();
            }
            TyKind::Named {
                name: name.clone(),
                args: Vec::new(),
            }
        }
        TyKind::Named { name, args } => TyKind::Named {
            name: name.clone(),
            args: args.iter().map(go).collect(),
        },
        TyKind::Fn {
            binder,
            implicit,
            dom,
            cod,
        } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(go(dom)),
            cod: Box::new(go(cod)),
        },
        TyKind::Vec { elem, len } => TyKind::Vec {
            elem: Box::new(go(elem)),
            len: len.clone(),
        },
        TyKind::Squash(x) => TyKind::Squash(Box::new(go(x))),
        other => other.clone(),
    };
    Ty { kind, span }
}

/// A local function signature's surface codomain after a saturated call.
/// Only a candidate: the type query rechecks it against the inferred type.
pub(crate) fn signature_result(signatures: &[(String, Ty)], e: &Expr) -> Option<Ty> {
    let ExprKind::App { head, args, named, .. } = &e.kind else { return None; };
    if !named.is_empty() { return None; }
    let ExprKind::Var(name) = &head.kind else { return None; };
    let mut result = signatures.iter().find(|(n, _)| n == name)?.1.clone();
    for arg in args {
        let TyKind::Fn { binder, cod, .. } = result.kind else { return None; };
        result = if let Some(binder) = binder {
            subst_surface_ty(&cod, &binder, arg)
        } else { *cod };
    }
    Some(result)
}

pub(crate) fn subst_surface_ty(ty: &Ty, name: &str, value: &Expr) -> Ty {
    let mut ty = ty.clone();
    match &mut ty.kind {
        TyKind::OfExpr(e) | TyKind::Fin(e) => **e = subst_candidate_expr(e, name, value),
        TyKind::Eq(a,b) => {
            **a = subst_candidate_expr(a, name, value);
            **b = subst_candidate_expr(b, name, value);
        }
        TyKind::Named { name: n, args } if n == name && args.is_empty() => return of_expr(value.clone()),
        TyKind::Named { args, .. } => for arg in args { *arg = subst_surface_ty(arg, name, value); },
        TyKind::Fn { binder, dom, cod, .. } => {
            **dom = subst_surface_ty(dom, name, value);
            if binder.as_deref() != Some(name) { **cod = subst_surface_ty(cod, name, value); }
        }
        TyKind::Vec { elem, len } => {
            **elem = subst_surface_ty(elem, name, value);
            **len = subst_candidate_expr(len, name, value);
        }
        TyKind::Squash(t) => **t = subst_surface_ty(t, name, value),
        _ => {}
    }
    ty
}

// The candidate's explicit type arguments participate in substitution too;
// the measure-expression substitution below intentionally leaves them alone.
fn subst_candidate_expr(e: &Expr, name: &str, value: &Expr) -> Expr {
    let mut out = e.clone();
    match &mut out.kind {
        ExprKind::App { head, args, named, .. } => {
            **head = subst_candidate_expr(head, name, value);
            for arg in args { *arg = subst_candidate_expr(arg, name, value); }
            for arg in named { arg.expr = subst_candidate_expr(&arg.expr, name, value); }
        }
        ExprKind::TyApp { head, args } => {
            **head = subst_candidate_expr(head, name, value);
            for ty in args { *ty = subst_surface_ty(ty, name, value); }
        }
        ExprKind::TyLit(ty) => **ty = subst_surface_ty(ty, name, value),
        _ => return subst(e, &[(name, value)], &mut Vec::new()),
    }
    out
}

/// `f#body` — the rewritten `Succ` arm, lifted out of the eliminator.
pub(crate) fn body_name(name: &str) -> String {
    format!("{name}#body")
}

/// `f#obl_N` — one self-call site's obligation, lifted out of the body (§4).
pub(crate) fn obl_name(name: &str, site: usize) -> String {
    format!("{name}#obl_{site}")
}

/// `f#found_N` — a proof one of the body's calls left to a default that
/// searches its context, lifted out so that the body and every companion
/// name the same term ([`lift_found`]).
pub(crate) fn found_name(name: &str, n: usize) -> String {
    format!("{name}#found_{n}")
}

/// `decl` with every proof its body's calls leave to a context-reading
/// default (`inside: i.toNat() < n := bv_omega`) found once, as a theorem
/// `f#found_N` over the binders its goal and facts name, and passed at the
/// call by name; and those theorems, to be elaborated first.
///
/// Why: the lowering elaborates the body's syntax once per generated
/// declaration (`f#body`, `f#ext`, the unfolding equation's right side), and
/// a search that reads its context returns a different proof term in each.
/// The kernel then has to compare two proofs argument by argument where the
/// companions need the calls to be the same term
/// (issues/found-proof-differs-across-recursion-companions.md). A lifted
/// proof is one name applied to the same binders everywhere.
///
/// `None` where no call leaves such a proof, or the walk declines (a binder
/// with no type): the declaration is then lowered as written.
pub(crate) fn lift_found(decl: &Decl, name: &str, measure: &Expr, tys: &dyn BinderTys) -> Option<(Decl, Vec<Lowered>)> {
    let mut any = false;
    let mut scan = |x: &Expr| {
        if let ExprKind::App { head, .. } = &x.kind {
            let callee = match &head.kind {
                ExprKind::TyApp { head, .. } => &head.kind,
                other => other,
            };
            if let ExprKind::Var(n) = callee && n != name && tys.has_context_default(n) {
                any = true;
            }
        }
        if let ExprKind::Dot { name: member, args: Some(_), .. } = &x.kind && tys.member_has_context_default(member) {
            any = true;
        }
        if let ExprKind::Index { .. } = &x.kind && tys.member_has_context_default("at") {
            any = true;
        }
    };
    for s in &decl.body.stmts {
        match s {
            Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } =>
                crate::surface::walk_expr(expr, &mut scan),
        }
    }
    crate::surface::walk_expr(&decl.body.result, &mut scan);
    if !any { return None; }
    let refs: Vec<&Param> = decl.params.iter().collect();
    let solo = solo(decl, name, measure);
    let mut state = Rewrite {
        decl,
        name,
        params: &refs,
        measure,
        ons: &decl.body.ons,
        omega_available: false,
        tys,
        lift: false,
        members: &solo,
        caller: 0,
        next: 1,
        eqs: 0,
        refinements: Vec::new(),
        scrut_aliases: Vec::new(),
        auto_eqs: AutoEqs::Off,
        auto_n: 0,
        scope: scope_of(decl),
        sites: Vec::new(),
        obls: Vec::new(),
        found_only: true,
        found: Vec::new(),
        found_values: Vec::new(),
        known: &[],
        error: None,
    };
    let stmts: Vec<Stmt> = decl.body.stmts.iter().map(|s| state.stmt(s)).collect();
    let result = state.expr(&decl.body.result);
    if state.error.is_some() || state.found.is_empty() { return None; }
    let mut lifted = decl.clone();
    lifted.body.stmts = stmts;
    lifted.body.result = Box::new(result);
    Some((lifted, state.found))
}

/// `bitvec_omega::found_fact<P>(fact: ∥P∥ := bv_omega) → ∥P∥`: a loop
/// passes its facts through it, with the search written, so a caller's
/// lowering lifts each into a found proof of its own (`Rewrite::found_fact`).
pub(crate) const FOUND_FACT: &str = "bitvec_omega::found_fact";

/// `f#rec` — the eliminator on the bound, lifted out of `f`.
pub(crate) fn rec_name(name: &str) -> String {
    format!("{name}#rec")
}

/// `f#grp` — a mutual group's product motive, keyed on its first member
/// (`docs/language/recursion/mutual-recursion-design.md` §3).
pub(crate) fn grp_name(name: &str) -> String {
    format!("{name}#grp")
}

/// `f#grp_rec` — the group's one eliminator on the shared bound (§3).
pub(crate) fn grp_rec_name(name: &str) -> String {
    format!("{name}#grp_rec")
}

/// One member of the recursion the walk may call: its self-name, the
/// parameters a call has to saturate, the measure a call's obligation is
/// stated at — both as written (`raw`) and scaled by §4's rank flattening —
/// and the projection of the shared induction hypothesis that reaches it.
///
/// A singleton has exactly one of these, with `proj: None`, and everything
/// below then spells what Part A spelled.
struct Sibling {
    name: String,
    params: Vec<Param>,
    result: Ty,
    raw: Expr,
    measure: Expr,
    /// `.snd` repeated `n` times then `.fst`/`.snd` (§3); `None` where the ih
    /// *is* the member's own motive.
    proj: Option<(usize, &'static str)>,
    rank: usize,
}

/// The clean statement a group's obligation is *written* at (§4): the
/// argument's own measure against the caller's, before the rank flattening,
/// and whether the call owes a strict decrease.
struct Clean {
    args: Expr,
    strict: bool,
    /// The callee's and the caller's ranks, the literals the scaled
    /// statement adds (`args * N + to < raw * N + from`).
    ranks: (usize, usize),
    /// §8's rank rule, where the site is one it explains.
    hint: Option<String>,
}

pub(crate) fn var(name: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Var(name.to_string()),
        span,
    }
}

pub(crate) fn app(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args,
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

fn of_expr(e: Expr) -> Ty {
    let span = e.span;
    Ty {
        kind: TyKind::OfExpr(Box::new(e)),
        span,
    }
}

/// `nat::Nat::Lt(a, b)` as a type.
fn lt_ty(a: Expr, b: Expr, span: Span) -> Ty {
    of_expr(app(var("nat::Nat::Lt", span), vec![a, b], span))
}

pub(crate) fn arrow(binder: Option<String>, dom: Ty, cod: Ty, span: Span) -> Ty {
    Ty {
        kind: TyKind::Fn {
            binder,
            implicit: false,
            dom: Box::new(dom),
            cod: Box::new(cod),
        },
        span,
    }
}

/// `(x̄) -> cod`, the declaration's value parameters quantified explicitly —
/// the shape the motive already had before the lifting.
fn pi_over(params: &[Param], cod: Ty, span: Span) -> Ty {
    let mut ty = cod;
    for p in params.iter().rev() {
        ty = arrow(Some(p.name.clone()), p.ty.clone(), ty, span);
    }
    ty
}

fn param(name: &str, ty: Ty, span: Span) -> Param {
    Param {
        name: name.to_string(),
        ty,
        implicit: false,
        is_self: false,
        solver: None,
        default: None,
        origin: ParamOrigin::Written,
        symbol: None,
        span,
    }
}

/// The declaration's value parameters as **explicit** binders: a companion
/// quantifies an implicit parameter the way the motive always has, and its
/// call sites pass every argument positionally.
fn value_params(decl: &Decl) -> Vec<Param> {
    decl.params
        .iter()
        .map(|p| Param {
            implicit: false,
            is_self: false,
            solver: None,
            default: None,
            symbol: None,
            ..p.clone()
        })
        .collect()
}

/// A reference to a companion with the declaration's type parameters pinned
/// (`g<A, B>`) rather than left to unification, since a companion's leading
/// arguments are `Nat`s that mention none of them.
pub(crate) fn companion_ref(decl: &Decl, name: &str, span: Span) -> Expr {
    let head = var(name, span);
    if decl.tyvars.is_empty() {
        return head;
    }
    Expr {
        kind: ExprKind::TyApp {
            head: Box::new(head),
            args: decl
                .tyvars
                .iter()
                .map(|t| Ty {
                    kind: TyKind::Named {
                        name: t.name.clone(),
                        args: Vec::new(),
                    },
                    span,
                })
                .collect(),
        },
        span,
    }
}

/// A companion declaration: the writer's type parameters, `params`, and a
/// body with no `on`s unless `ons` says otherwise.
fn companion(decl: &Decl, name: String, params: Vec<Param>, result: Ty, body: Block) -> Decl {
    Decl {
        kind: decl.kind,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
            value: false,
        elaborates: None,
        name,
        tyvars: decl.tyvars.clone(),
        params,
        result,
        decreases: None,
        unfolding: Vec::new(),
        body,
        span: decl.span,
    }
}

pub(crate) fn block(result: Expr, span: Span) -> Block {
    Block {
        stmts: Vec::new(),
        result: Box::new(result),
        ons: Vec::new(),
        span,
    }
}

/// The one-member "group" a singleton recurses in: `f` itself, at the measure
/// as written and with no projection, so every route below spells what Part A
/// spelled.
fn solo(decl: &Decl, name: &str, measure: &Expr) -> [Sibling; 1] {
    [Sibling {
        name: name.to_string(),
        params: decl.params.clone(),
        result: decl.result.clone(),
        raw: measure.clone(),
        measure: measure.clone(),
        proj: None,
        rank: 0,
    }]
}

/// `recv(args…)`, or `recv.snd…​.fst(args…)` where the member is reached
/// through the product motive (`docs/language/recursion/mutual-recursion-design.md` §3).
fn project(recv: Expr, proj: Option<(usize, &'static str)>, args: Vec<Expr>, span: Span) -> Expr {
    let Some((snds, last)) = proj else {
        return app(recv, args, span);
    };
    let mut r = recv;
    for _ in 0..snds {
        r = Expr {
            kind: ExprKind::Dot {
                recv: Box::new(r),
                name: "snd".into(),
                tyargs: Vec::new(),
                args: None,
                named: Vec::new(),
            },
            span,
        };
    }
    Expr {
        kind: ExprKind::Dot {
            recv: Box::new(r),
            name: last.to_string(),
            tyargs: Vec::new(),
            args: Some(args),
            named: Vec::new(),
        },
        span,
    }
}

/// Whether the obligations of a body may be lifted at all (§4): the plan
/// rests on each obligation being a *named* goal that one generated
/// declaration discharges, so a body that discharges goals by statement
/// (`on _: P := …`) keeps the obligations where they were.
fn liftable(decl: &Decl) -> bool {
    decl.body
        .ons
        .iter()
        .all(|o| matches!(o.target, OnTarget::Name(_)))
}

/// `decl` with its body deshadowed ([`crate::alpha::deshadow`]) against its
/// parameters and type parameters, which the lowering's measure, obligation
/// telescopes and unfolding walk all read by name.
pub(crate) fn deshadowed(decl: &Decl) -> Decl {
    let bound: Vec<String> = decl.tyvars.iter().map(|t| t.name.clone())
        .chain(decl.params.iter().map(|p| p.name.clone()))
        .collect();
    let mut decl = decl.clone();
    crate::alpha::deshadow(&mut decl.body, &bound);
    decl
}

/// Lower `decl`, whose body recurses under `decreases measure`, into the
/// lifted obligations of §4 and the `f#body` / `f#rec` / `f` family (module
/// docs, and `docs/language/recursion/decreases-unfolding-design.md` §2). `name` is the
/// declaration's self-name (the base name, for a member); `omega_available`
/// says whether an obligation nobody discharges by hand may default to
/// `omega`; `lift` is cleared to re-lower a declaration whose lifted
/// obligations the checker refused, which is the un-lifted spelling this
/// round replaced.
///
/// Purely syntactic: everything it builds is surface the writer could have
/// written, and a mis-generated program is refused by the ordinary checker.
pub(crate) fn lower(
    decl: &Decl,
    name: &str,
    measure: &Expr,
    omega_available: bool,
    tys: &dyn BinderTys,
    lift: bool,
    auto: &AutoEqs,
) -> R<Family> {
    let span = measure.span;
    let params = value_params(decl);
    let refs: Vec<&Param> = decl.params.iter().collect();
    let solo = solo(decl, name, measure);
    let mut state = Rewrite {
        decl,
        name,
        params: &refs,
        measure,
        ons: &decl.body.ons,
        omega_available,
        tys,
        lift: lift && liftable(decl),
        members: &solo,
        caller: 0,
        next: 1,
        eqs: 0,
        refinements: Vec::new(),
        scrut_aliases: Vec::new(),
        auto_eqs: auto.clone(),
        auto_n: 0,
        scope: scope_of(decl),
        sites: Vec::new(),
        obls: Vec::new(),
        found_only: false,
        found: Vec::new(),
        found_values: Vec::new(),
        known: &[],
        error: None,
    };
    let stmts: Vec<Stmt> = decl.body.stmts.iter().map(|s| state.stmt(s)).collect();
    let result = state.expr(&decl.body.result);
    state.validate_labels();
    if let Some(error) = state.error.take() {
        return Err(error);
    }
    let auto_candidates = state.auto_n;
    let sites = state.sites;
    let obligations: Vec<Lowered> = state.obls.into_iter().flatten().collect();
    // A lifted obligation takes its `on` with it; every other discharge —
    // including one whose site could not be lifted — stays on the body.
    let moved: Vec<&str> = obligations
        .iter()
        .flat_map(|o| o.obligations.sites.iter().map(|(_, h, ..)| h.as_str()))
        .collect();
    let body_ons = remaining_ons(&decl.body.ons, &moved);

    // `f#body(__dec_k, __dec_ih, x̄, __dec_h) -> T`, the `Succ` arm.
    let ih_ty = pi_over(
        &params,
        arrow(
            None,
            lt_ty(measure.clone(), var(K, span), span),
            decl.result.clone(),
            span,
        ),
        span,
    );
    let h_ty = lt_ty(
        measure.clone(),
        app(var("Succ", span), vec![var(K, span)], span),
        span,
    );
    let mut body_params = vec![
        param(
            K,
            Ty {
                kind: TyKind::Nat,
                span,
            },
            span,
        ),
        param(IH, ih_ty, span),
    ];
    body_params.extend(params.iter().cloned());
    body_params.push(param(H, h_ty, span));
    let body_decl = companion(
        decl,
        body_name(&decl.name),
        body_params,
        decl.result.clone(),
        Block {
            stmts,
            result: Box::new(result),
            // The writer's discharges follow their obligations into the
            // declaration that now raises them.
            ons: body_ons,
            span: decl.body.span,
        },
    );

    // `f#rec(__dec_z) -> (x̄) -> nat::Nat::Lt(e, __dec_z) -> T`, the eliminator.
    let motive_ty = pi_over(
        &params,
        arrow(
            None,
            lt_ty(measure.clone(), var(Z, span), span),
            decl.result.clone(),
            span,
        ),
        span,
    );
    let binder = |n: &str| LamBinder {
        name: n.to_string(),
        ty: None,
        implicit: false,
        span,
    };
    // λ x̄ __dec_h => e
    let lam = |body: Expr| Expr {
        kind: ExprKind::Lam {
            binders: params
                .iter()
                .map(|p| p.name.as_str())
                .chain([H])
                .map(binder)
                .collect(),
            body: Box::new(body),
        },
        span,
    };
    let motive = Expr {
        kind: ExprKind::Lam {
            binders: vec![binder(Z)],
            body: Box::new(Expr {
                kind: ExprKind::TyLit(Box::new(motive_ty.clone())),
                span,
            }),
        },
        span,
    };
    let absurd = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(H, span)),
            eqbind: None,
            motive: None,
            arms: Vec::new(),
        },
        span,
    };
    let pat = |n: &str| Pat::Var {
        name: n.to_string(),
        span,
    };
    let mut arm_args = vec![var(K, span), var(IH, span)];
    arm_args.extend(params.iter().map(|p| var(&p.name, span)));
    arm_args.push(var(H, span));
    let elim = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(Z, span)),
            eqbind: None,
            motive: Some(Box::new(motive)),
            arms: vec![
                Arm {
                    ctor: "Zero".into(),
                    default: false,
                    binders: Vec::new(),
                    body: lam(absurd),
                    span,
                },
                Arm {
                    ctor: "Succ".into(),
                    default: false,
                    binders: vec![pat(K), pat(IH)],
                    body: lam(app(
                        companion_ref(decl, &body_name(&decl.name), span),
                        arm_args,
                        span,
                    )),
                    span: decl.body.span,
                },
            ],
        },
        span,
    };
    let rec_decl = companion(
        decl,
        rec_name(&decl.name),
        vec![param(
            Z,
            Ty {
                kind: TyKind::Nat,
                span,
            },
            span,
        )],
        motive_ty,
        block(elim, decl.body.span),
    );

    // `f(x̄) = f#rec(Succ(e), x̄, nat::Nat::lt_succ_self(e))`.
    let mut call_args = vec![app(var("Succ", span), vec![measure.clone()], span)];
    call_args.extend(decl.params.iter().map(|p| var(&p.name, span)));
    call_args.push(app(
        var("nat::Nat::lt_succ_self", span),
        vec![measure.clone()],
        span,
    ));
    let f_decl = Decl {
        decreases: None,
        unfolding: Vec::new(),
        body: block(
            app(
                companion_ref(decl, &rec_name(&decl.name), span),
                call_args,
                span,
            ),
            decl.body.span,
        ),
        ..decl.clone()
    };

    Ok(Family {
        auto_candidates,
        obligations,
        decls: vec![
            Lowered {
                decl: body_decl,
                obligations: Obligations { sites },
            },
            Lowered {
                decl: rec_decl,
                obligations: Obligations { sites: Vec::new() },
            },
            Lowered {
                decl: f_decl,
                obligations: Obligations { sites: Vec::new() },
            },
        ],
    })
}

/// One member of a mutual `decreases` group, as the run scan of
/// `docs/language/recursion/mutual-recursion-design.md` §1 found it.
pub(crate) struct GroupMember<'a> {
    pub(crate) decl: &'a Decl,
    /// The base name the member recurses under, as `Cx.selfref` uses it.
    pub(crate) self_name: String,
    pub(crate) measure: Expr,
}

/// `e * N + r` — §4's flattening of the lexicographic `(measure, rank)` into
/// the one `Nat` Part A already recurses on. Spelled at `nat::Nat::mul`/`nat::Nat::add`
/// rather than through the operators, which is what `omega` reflects.
fn scaled(e: &Expr, n: usize, r: usize) -> Expr {
    let span = e.span;
    let num = |k: usize| Expr {
        kind: ExprKind::Num((k as u64).into()),
        span,
    };
    app(
        var("nat::Nat::add", span),
        vec![
            app(var("nat::Nat::mul", span), vec![e.clone(), num(n)], span),
            num(r),
        ],
        span,
    )
}

/// The group-shape guards of `docs/language/recursion/mutual-recursion-design.md` §§2–4, owed
/// before anything is elaborated — including before the members' measures are
/// checked, since a measure naming a member is an unbound name at that point
/// and "unbound" is the wrong thing to say about it.
pub(crate) fn check_group_shape(members: &[GroupMember<'_>]) -> R<()> {
    let first = members[0].decl;
    let tyvars = |d: &Decl| {
        d.tyvars
            .iter()
            .map(|t| t.name.clone())
            .collect::<Vec<String>>()
    };
    // §3: the helpers are shared, and a surface function type cannot quantify
    // a type parameter, so every member declares the same list.
    let want = tyvars(first);
    for m in &members[1..] {
        let got = tyvars(m.decl);
        if got != want {
            return err(
                format!(
                    "the members of a mutual `decreases` group share one recursion, so \
                     they declare the same type parameters: `{}` has <{}> and `{}` has \
                     <{}> (docs/language/recursion/mutual-recursion-design.md §3)",
                    first.name,
                    want.join(", "),
                    m.decl.name,
                    got.join(", ")
                ),
                m.decl.span,
            );
        }
    }
    for m in members {
        // §2: the motive quantifies over every member's measure, so a measure
        // defined by the recursion would be circular.
        if let Some(other) = members.iter().find(|o| mentions(&m.measure, &o.self_name)) {
            return err(
                format!(
                    "a `decreases` measure may not call `{}`: it is a member of this \
                     mutual group, and the group's motive is stated at every member's \
                     measure (docs/language/recursion/mutual-recursion-design.md §2)",
                    other.self_name
                ),
                m.measure.span,
            );
        }
        // §4: the group's obligations are stated at the scaled measure and
        // written at the unscaled one, which needs the lift.
        if !liftable(m.decl) {
            return err(
                format!(
                    "a mutual `decreases` group lifts every obligation into a \
                     declaration of its own, so `{}` cannot discharge one by statement: \
                     name the obligation instead (`on ?decN := …`, \
                     docs/language/recursion/mutual-recursion-design.md §4)",
                    m.decl.name
                ),
                m.decl.span,
            );
        }
    }
    Ok(())
}

/// Lower a mutual group of N > 1 adjacent `decreases` declarations into the
/// one recursion of `docs/language/recursion/mutual-recursion-design.md` §3: the lifted
/// obligations, the product motive `f#grp`, one `g#body` per member, the
/// shared `f#grp_rec`, and each member as a projection of it. Keyed on the
/// first member's name.
///
/// Purely syntactic, like [`lower`]: every declaration it returns is surface
/// the writer could have written, checked the ordinary way.
pub(crate) fn lower_group(
    members: &[GroupMember<'_>],
    omega_available: bool,
    tys: &dyn BinderTys,
) -> R<Family> {
    let n = members.len();
    debug_assert!(n > 1, "a singleton lowers by Part A");
    let first = members[0].decl;
    let span = members[0].measure.span;
    check_group_shape(members)?;
    // §4's arithmetic is `Nat::scaled_lt`/`Nat::scaled_le`, so `omega` is only
    // the default closer of a site nobody discharges, as in Part A.
    let sibs: Vec<Sibling> = members
        .iter()
        .enumerate()
        .map(|(i, m)| Sibling {
            name: m.self_name.clone(),
            params: m.decl.params.clone(),
            result: m.decl.result.clone(),
            raw: m.measure.clone(),
            measure: scaled(&m.measure, n, n - 1 - i),
            // `.snd` down to this component, then `.fst` — except the last,
            // which *is* the innermost `.snd` (§3).
            proj: Some(if i + 1 == n {
                (n - 2, "snd")
            } else {
                (i, "fst")
            }),
            rank: n - 1 - i,
        })
        .collect();

    // Every member's body rewritten against the shared ih, in declaration
    // order, and the obligations each one raises.
    let mut obligations: Vec<Lowered> = Vec::new();
    let mut bodies: Vec<(Vec<Stmt>, Expr, Vec<OnStmt>)> = Vec::new();
    for (i, m) in members.iter().enumerate() {
        let refs: Vec<&Param> = m.decl.params.iter().collect();
        let mut state = Rewrite {
            decl: m.decl,
            name: &m.self_name,
            params: &refs,
            measure: &sibs[i].measure,
            ons: &m.decl.body.ons,
            omega_available,
            tys,
            lift: true,
            members: &sibs,
            caller: i,
            next: 1,
            eqs: 0,
            refinements: Vec::new(),
            scrut_aliases: Vec::new(),
            auto_eqs: AutoEqs::Off,
            auto_n: 0,
            scope: scope_of(m.decl),
            sites: Vec::new(),
            obls: Vec::new(),
            found_only: false,
            found: Vec::new(),
            found_values: Vec::new(),
            known: &[],
            error: None,
        };
        let stmts: Vec<Stmt> = m.decl.body.stmts.iter().map(|s| state.stmt(s)).collect();
        let result = state.expr(&m.decl.body.result);
        state.validate_labels();
        if let Some(error) = state.error.take() {
            return Err(error);
        }
        // §4: unlike Part A, the un-lifted spelling is not generally
        // available to a group — `omega` inside `g#body` has the group's ih
        // in context and renders it back as source — so a site that cannot be
        // lifted is reported rather than worked around.
        if let Some(k) = state.obls.iter().position(Option::is_none) {
            let (site, ..) = state.sites[k];
            return err(
                "this recursive call's obligation names a binder the generator cannot \
                 type, and a mutual group cannot fall back to stating it at the call \
                 (docs/language/recursion/mutual-recursion-design.md §4): annotate the binder, or lift the \
                 call out of the pattern that introduces it",
                site,
            );
        }
        let lifted: Vec<Lowered> = state.obls.into_iter().flatten().collect();
        let moved: Vec<&str> = lifted
            .iter()
            .flat_map(|o| o.obligations.sites.iter().map(|(_, h, ..)| h.as_str()))
            .collect();
        let ons = remaining_ons(&m.decl.body.ons, &moved);
        // The sites travel with their own `g#obl_N`; `g#body` raises none.
        obligations.extend(lifted);
        bodies.push((stmts, result, ons));
    }

    let grp = grp_name(&first.name);
    let grp_rec = grp_rec_name(&first.name);
    let grp_at = |e: Expr| of_expr(app(companion_ref(first, &grp, span), vec![e], span));
    let nat_ty = Ty {
        kind: TyKind::Nat,
        span,
    };
    let binder = |n: &str| LamBinder {
        name: n.to_string(),
        ty: None,
        implicit: false,
        span,
    };
    // λ x̄_i __dec_h => body, at member i's own parameter names.
    let lam_at = |i: usize, body: Expr| Expr {
        kind: ExprKind::Lam {
            binders: members[i]
                .decl
                .params
                .iter()
                .map(|p| p.name.as_str())
                .chain([H])
                .map(binder)
                .collect(),
            body: Box::new(body),
        },
        span,
    };
    // `Pair(a, Pair(b, c))` / `Pair<A, Pair<B, C>>` — the product is nested
    // right, so member i's projection is `.snd`×i then `.fst` (§3).
    let nest_ty = |mut parts: Vec<Ty>| {
        let mut out = parts.pop().expect("a group has members");
        while let Some(t) = parts.pop() {
            out = Ty {
                kind: TyKind::Named {
                    name: "Pair".into(),
                    args: vec![t, out],
                },
                span,
            };
        }
        out
    };
    let nest = |mut parts: Vec<Expr>| {
        let mut out = parts.pop().expect("a group has members");
        while let Some(e) = parts.pop() {
            out = app(var("Pair", span), vec![e, out], span);
        }
        out
    };

    // `f#grp(__dec_z) -> Type`, the product of the members' own motives.
    let component = |i: usize, bound: Expr| {
        pi_over(
            &value_params(members[i].decl),
            arrow(
                None,
                lt_ty(sibs[i].measure.clone(), bound, span),
                members[i].decl.result.clone(),
                span,
            ),
            span,
        )
    };
    let product = nest_ty((0..n).map(|i| component(i, var(Z, span))).collect());
    let grp_decl = Decl {
        kind: DeclKind::Fn,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
            value: false,
        elaborates: None,
        name: grp.clone(),
        tyvars: first.tyvars.clone(),
        params: vec![param(Z, nat_ty.clone(), span)],
        result: Ty {
            kind: TyKind::Univ { level: 0 },
            span,
        },
        decreases: None,
        unfolding: Vec::new(),
        body: block(
            Expr {
                kind: ExprKind::TyLit(Box::new(product)),
                span,
            },
            span,
        ),
        span: first.span,
    };

    // One `g#body(__dec_k, __dec_ih: f#grp(__dec_k), x̄, __dec_h)` per member.
    let body_decls: Vec<Decl> = members
        .iter()
        .enumerate()
        .zip(bodies)
        .map(|((i, m), (stmts, result, ons))| {
            let mut ps = vec![
                param(K, nat_ty.clone(), span),
                param(IH, grp_at(var(K, span)), span),
            ];
            ps.extend(value_params(m.decl));
            ps.push(param(
                H,
                lt_ty(sibs[i].measure.clone(), succ(var(K, span), span), span),
                span,
            ));
            companion(
                m.decl,
                body_name(&m.decl.name),
                ps,
                m.decl.result.clone(),
                Block {
                    stmts,
                    result: Box::new(result),
                    ons,
                    span: m.decl.body.span,
                },
            )
        })
        .collect();

    // `f#grp_rec(__dec_z) -> f#grp(__dec_z)`, the group's one `elim_Nat`.
    let absurd = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(H, span)),
            eqbind: None,
            motive: None,
            arms: Vec::new(),
        },
        span,
    };
    let pat = |x: &str| Pat::Var {
        name: x.to_string(),
        span,
    };
    let arm_call = |i: usize| {
        let mut args = vec![var(K, span), var(IH, span)];
        args.extend(members[i].decl.params.iter().map(|p| var(&p.name, span)));
        args.push(var(H, span));
        app(
            companion_ref(first, &body_name(&members[i].decl.name), span),
            args,
            span,
        )
    };
    let motive = Expr {
        kind: ExprKind::Lam {
            binders: vec![binder(Z)],
            body: Box::new(Expr {
                kind: ExprKind::TyLit(Box::new(grp_at(var(Z, span)))),
                span,
            }),
        },
        span,
    };
    let elim = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            // The result type `f#grp(__dec_z)` already says what the motive
            // says, so the redundancy lint would fire on generated code.
            generated: true,
            scrut: Box::new(var(Z, span)),
            eqbind: None,
            motive: Some(Box::new(motive)),
            arms: vec![
                Arm {
                    ctor: "Zero".into(),
                    default: false,
                    binders: Vec::new(),
                    body: nest((0..n).map(|i| lam_at(i, absurd.clone())).collect()),
                    span,
                },
                Arm {
                    ctor: "Succ".into(),
                    default: false,
                    binders: vec![pat(K), pat(IH)],
                    body: nest((0..n).map(|i| lam_at(i, arm_call(i))).collect()),
                    span: first.body.span,
                },
            ],
        },
        span,
    };
    let rec_decl = Decl {
        kind: DeclKind::Fn,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
            value: false,
        elaborates: None,
        name: grp_rec.clone(),
        tyvars: first.tyvars.clone(),
        params: vec![param(Z, nat_ty, span)],
        result: grp_at(var(Z, span)),
        decreases: None,
        unfolding: Vec::new(),
        body: block(elim, first.body.span),
        span: first.span,
    };

    // Each member is a projection of the eliminator at its own bound (§3).
    let member_decls: Vec<Decl> = members
        .iter()
        .enumerate()
        .map(|(i, m)| {
            let bound = sibs[i].measure.clone();
            let mut args: Vec<Expr> = m.decl.params.iter().map(|p| var(&p.name, span)).collect();
            args.push(app(
                var("nat::Nat::lt_succ_self", span),
                vec![bound.clone()],
                span,
            ));
            Decl {
                decreases: None,
                unfolding: Vec::new(),
                body: block(
                    project(
                        app(
                            companion_ref(first, &grp_rec, span),
                            vec![succ(bound, span)],
                            span,
                        ),
                        sibs[i].proj,
                        args,
                        span,
                    ),
                    m.decl.body.span,
                ),
                ..m.decl.clone()
            }
        })
        .collect();

    let plain = |decl: Decl| Lowered {
        decl,
        obligations: Obligations { sites: Vec::new() },
    };
    let mut decls = vec![plain(grp_decl)];
    decls.extend(body_decls.into_iter().map(plain));
    decls.push(plain(rec_decl));
    decls.extend(member_decls.into_iter().map(plain));
    Ok(Family {
        obligations,
        decls,
        auto_candidates: 0,
    })
}

/// The discharges that stay where they were written: everything but the
/// `on ?decN` of a site whose obligation moved into `f#obl_N` (§4).
fn remaining_ons(ons: &[OnStmt], moved: &[&str]) -> Vec<OnStmt> {
    ons.iter()
        .filter(|o| !matches!(&o.target, OnTarget::Name(n) if moved.contains(&n.as_str())))
        .cloned()
        .collect()
}

/// The declaration's own binders, the seed of the walk's scope: a lifted
/// obligation quantifies these under their own names.
fn scope_of(decl: &Decl) -> Vec<Binder> {
    decl.params
        .iter()
        .map(|p| Binder {
            name: p.name.clone(),
            ty: Some(p.ty.clone()),
            value: None,
        })
        .collect()
}

/// The declaration-shape guards `decreases` owes before anything is built:
/// the forms whose lowering has no meaning rather than a wrong one.
pub(crate) fn check_shape(decl: &Decl, measure: &Expr) -> R<()> {
    if decl.is_meta {
        return err("`decreases` is for ordinary declarations, not `meta fn`", measure.span);
    }
    if let Some(p) = decl.params.iter().find(|p| p.solver.is_some()) {
        return err(
            format!(
                "`decreases` does not yet cover a declaration with a solver \
                 parameter (`{}`): the recursion re-binds every parameter \
                 explicitly, and a solver parameter is filled another way",
                p.name
            ),
            p.span,
        );
    }
    Ok(())
}

/// A member's self-calls spelled as method calls, `x.f(ā)`, respelled as the
/// calls `f(…, x, …)` they desugar to, with the receiver at its parameter's
/// position (the `self` parameter, or the first explicit one). Every route
/// below reads a self-call as an application of the self-name; the
/// elaborator's own desugaring of a method call happens after this
/// lowering, where `f` names nothing.
///
/// A method call names `f` only by its base name, so another type's member
/// of that name is the other reading. A receiver that is typed and does not
/// check at the receiver parameter's type is that one and is left alone;
/// one this pass cannot type is read as the self-call, which is what its
/// name says inside `f`, and a wrong reading is refused by the checker.
///
/// A `mut self` method's call on a mutable local, `let p = x.f(ā);` or the
/// statement `x.f(ā);` ([`heather_syntax::MUTATED`]), rebinds `x` to the
/// call's `after` and `p` to its `value`; that is spelled out here, with
/// the call bound once, as the statement elaborates it.
pub(crate) fn method_calls_as_calls(decl: &Decl, name: &str, tys: &dyn BinderTys) -> R<Decl> {
    if !decl.name.contains("::") {
        return Ok(decl.clone());
    }
    let explicit: Vec<&Param> = decl.params.iter().filter(|p| !p.implicit).collect();
    let Some(slot) = explicit.iter().position(|p| p.is_self).or((!explicit.is_empty()).then_some(0)) else {
        return Ok(decl.clone());
    };
    let subject_ty = explicit[slot].ty.clone();
    let mutated = matches!(&decl.result.kind, TyKind::Named { name, .. } if name == heather_syntax::MUTATED_RECORD);
    // The binders a receiver may be typed over: the parameters and every
    // annotated `let`. The body is deshadowed, so one name is one binder.
    let mut scope = scope_of(decl);
    for s in &decl.body.stmts {
        if let Stmt::Let { name, ty: Some(ty), .. } = s {
            scope.push(Binder { name: name.clone(), ty: Some(ty.clone()), value: None });
        }
    }
    let mut collect = |e: &Expr| {
        crate::surface::walk_expr(e, &mut |x| {
            if let ExprKind::Block(b) = &x.kind {
                for s in &b.stmts {
                    if let Stmt::Let { name, ty: Some(ty), .. } = s {
                        scope.push(Binder { name: name.clone(), ty: Some(ty.clone()), value: None });
                    }
                }
            }
        });
    };
    for s in &decl.body.stmts {
        if let Stmt::Let { expr, .. } = s {
            collect(expr);
        }
    }
    collect(&decl.body.result);
    let signatures = [(name.to_string(), pi_over(&decl.params, decl.result.clone(), decl.span))];
    let mut pass = MethodCalls {
        decl,
        name,
        slot,
        subject_ty,
        mutated,
        scope,
        signatures,
        tys,
        next: 0,
        error: None,
    };
    let mut out = decl.clone();
    pass.block(&mut out.body);
    match pass.error {
        Some(e) => Err(e),
        None => Ok(out),
    }
}

struct MethodCalls<'a> {
    decl: &'a Decl,
    name: &'a str,
    slot: usize,
    subject_ty: Ty,
    mutated: bool,
    scope: Vec<Binder>,
    signatures: [(String, Ty); 1],
    tys: &'a dyn BinderTys,
    next: usize,
    error: Option<crate::ElabError>,
}

impl MethodCalls<'_> {
    /// Is `recv.<name>(…)` this declaration's own call? See
    /// [`method_calls_as_calls`] for the rule.
    fn is_self_call(&self, recv: &Expr) -> bool {
        let span = recv.span;
        let at_subject = Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts: vec![Stmt::Let {
                    name: "__dec_receiver".into(),
                    ty: Some(self.subject_ty.clone()),
                    expr: recv.clone(),
                    span,
                    opaque: false,
                }],
                result: Box::new(var("__dec_receiver", span)),
                ons: Vec::new(),
                span,
            })),
            span,
        };
        let infer = |e: &Expr| self.tys.infer_local(self.decl, &self.signatures, &self.scope, e);
        infer(&at_subject).is_some() || infer(recv).is_none()
    }

    /// `recv.f(ā)` as `f(…, recv, …)`, or `None` where `e` is not a self-call.
    fn call(&mut self, e: &Expr) -> Option<Expr> {
        let ExprKind::Dot { recv, name, tyargs, args: Some(args), named } = &e.kind else {
            return None;
        };
        if name != self.name || !self.is_self_call(recv) {
            return None;
        }
        if !tyargs.is_empty() {
            self.fail(
                format!(
                    "a recursive call to `{name}` under `decreases` passes every parameter, \
                     type arguments included, by position: write `@{}(…)`",
                    self.name
                ),
                e.span,
            );
            return None;
        }
        if self.slot > args.len() {
            self.fail(
                format!(
                    "`{name}`'s receiver is its parameter number {}, so this method call leaves \
                     it nowhere to go: write the call `{name}(…)`",
                    self.slot + 1
                ),
                e.span,
            );
            return None;
        }
        let mut args = args.clone();
        args.insert(self.slot, (**recv).clone());
        Some(Expr {
            kind: ExprKind::App {
                head: Box::new(var(self.name, e.span)),
                args,
                named: named.clone(),
                explicit: false,
                goal_oriented: false,
            },
            span: e.span,
        })
    }

    fn fail(&mut self, msg: String, span: Span) {
        if self.error.is_none() {
            self.error = Some(crate::ElabError::Elab { msg, span });
        }
    }

    fn expr(&mut self, e: &mut Expr) {
        crate::alpha::walk_expr_mut(e, &mut |x| {
            if let ExprKind::Block(b) = &mut x.kind {
                self.block(b);
                return true;
            }
            if let Some(call) = self.whole(x).or_else(|| self.call(x)) {
                *x = call;
                // The receiver and the arguments may call again.
                if let ExprKind::App { args, named, .. } = &mut x.kind {
                    for a in args.iter_mut() {
                        self.expr(a);
                    }
                    for n in named.iter_mut() {
                        self.expr(&mut n.expr);
                    }
                }
                return true;
            }
            false
        });
    }

    /// A block's statements, a claimed self-call on a mutable local spelled
    /// out (see [`method_calls_as_calls`]), then its result and `on`s.
    fn block(&mut self, b: &mut Block) {
        let mut stmts = Vec::with_capacity(b.stmts.len());
        for mut st in std::mem::take(&mut b.stmts) {
            if let Stmt::Let { name, expr, span, .. } = &st
                && let Some((receiver, call)) = self.claimed(expr)
            {
                let (name, span) = (name.clone(), *span);
                let mut call = call;
                // `call`'s receiver is the bare local; its arguments may
                // call again.
                if let ExprKind::App { args, named, .. } = &mut call.kind {
                    for a in args.iter_mut() {
                        self.expr(a);
                    }
                    for n in named.iter_mut() {
                        self.expr(&mut n.expr);
                    }
                }
                let statement = name.starts_with("#seq");
                if !self.mutated {
                    if statement {
                        self.fail(
                            format!(
                                "`{receiver}.{}(…)` does not update `{receiver}` (`{}` is not a `mut self` \
                                 method), so this statement discards its value: bind it with `let`",
                                self.name, self.name
                            ),
                            span,
                        );
                    }
                    stmts.push(Stmt::Let { name, ty: None, expr: call, span, opaque: false });
                    continue;
                }
                let whole = format!("__dec_mutated{}", self.next);
                self.next += 1;
                let field = |f: &str| Expr {
                    kind: ExprKind::Dot {
                        recv: Box::new(var(&whole, span)),
                        name: f.into(),
                        tyargs: Vec::new(),
                        args: None,
                        named: Vec::new(),
                    },
                    span,
                };
                stmts.push(Stmt::Let { name: whole.clone(), ty: None, expr: call, span, opaque: false });
                stmts.push(Stmt::Let { name: receiver, ty: None, expr: field("after"), span, opaque: false });
                if !statement {
                    stmts.push(Stmt::Let { name, ty: None, expr: field("value"), span, opaque: false });
                }
                continue;
            }
            match &mut st {
                Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => self.expr(expr),
            }
            stmts.push(st);
        }
        b.stmts = stmts;
        self.expr(&mut b.result);
        for on in &mut b.ons {
            self.expr(&mut on.expr);
        }
    }

    /// `\0mutated_whole(x.f(ā))`, a self-call that ends a `mut self` body
    /// ([`heather_syntax::MUTATED_WHOLE`]): the call, which is the record the
    /// body returns, so the recursion is a tail call the companions follow.
    fn whole(&mut self, e: &Expr) -> Option<Expr> {
        if !self.mutated {
            return None;
        }
        let ExprKind::App { head, args, .. } = &e.kind else { return None };
        if !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::MUTATED_WHOLE) {
            return None;
        }
        let [inner] = args.as_slice() else { return None };
        self.call(inner)
    }

    /// `\0mutated(x.f(ā))`, a self-call the block declaring `x` claimed:
    /// the local and the call respelled.
    fn claimed(&mut self, e: &Expr) -> Option<(String, Expr)> {
        let ExprKind::App { head, args, .. } = &e.kind else { return None };
        if !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::MUTATED) {
            return None;
        }
        let [inner] = args.as_slice() else { return None };
        let ExprKind::Dot { recv, .. } = &inner.kind else { return None };
        let ExprKind::Var(receiver) = &recv.kind else { return None };
        let receiver = receiver.clone();
        Some((receiver, self.call(inner)?))
    }
}

/// The self-call rewrite (module docs), threaded through a surface walk that
/// tracks the names bound around each node so a shadowed parameter or
/// declaration name is left alone.
struct Rewrite<'a> {
    decl: &'a Decl,
    name: &'a str,
    params: &'a [&'a heather_syntax::Param],
    measure: &'a Expr,
    ons: &'a [OnStmt],
    /// Whether an obligation nobody discharges by hand may default to `omega`.
    omega_available: bool,
    tys: &'a dyn BinderTys,
    /// Whether an obligation is lifted into `f#obl_N` (§4).
    lift: bool,
    /// Every member of the recursion this body may call, in declaration
    /// order, and which of them this body is
    /// (`docs/language/recursion/mutual-recursion-design.md` §3). One entry for a singleton.
    members: &'a [Sibling],
    caller: usize,
    next: usize,
    eqs: usize,
    /// What the enclosing `match`es have established about the measure's
    /// variables, outermost first: `(variable, the arm's pattern as an
    /// expression, the equation binder that says so)`. An obligation is
    /// stated at the measure with all of these applied — the statement a
    /// reader expects inside the arm — and transported back through the
    /// equations to the ih's own hypothesis (§3 of the design).
    refinements: Vec<(String, Expr, String)>,
    /// The computed scrutinees this walk let-bound as `__dec_scrut_N`, with
    /// the expression each stands for. A `match` on one states its arms'
    /// equations about the expression, not the name: a lifted `f#obl_N`
    /// quantifies the equation without the `let`, and there the name would
    /// be an unrelated parameter (docs/language/matching/dependent-match-compiler-design.md §8).
    scrut_aliases: Vec<(String, Expr)>,
    /// [`AutoEqs`]: which candidates get an equation, and the next
    /// candidate's number.
    auto_eqs: AutoEqs,
    auto_n: usize,
    /// The binders in scope at the node being walked, outermost first.
    scope: Vec<Binder>,
    sites: Vec<(Span, String, String, Option<String>)>,
    /// One entry per site in source order: the lifted `f#obl_N`, or `None`
    /// where the site's obligation stayed at the call (§4).
    obls: Vec<Option<Lowered>>,
    /// [`lift_found`]'s walk: the body is kept as written (its recursive
    /// calls, its matches) and only a call's found proofs are lifted, into
    /// `found`.
    found_only: bool,
    found: Vec<Lowered>,
    /// [`lift_found`]'s walk: each `let` alias in scope with its value as
    /// the walk rewrote it, its reads given their lifted proofs —
    /// `(scope index, name, the written value's span, rewritten value)`. A
    /// later `f#found_N` binds the alias to this value, so it does not
    /// search for those proofs again.
    found_values: Vec<(usize, String, Span, Expr)>,
    /// The body's own lifted `f#obl_N`, where this walk is a companion's:
    /// its reference passes the binders the body's declaration quantified,
    /// so the two spellings are one term even where the companion's walk
    /// (its `let`s inlined) would select differently.
    known: &'a [Lowered],
    error: Option<crate::ElabError>,
}

impl<'a> Rewrite<'a> {
    fn fail(&mut self, msg: String, span: Span) {
        if self.error.is_none() {
            self.error = Some(crate::ElabError::Elab { msg, span });
        }
    }

    fn validate_labels(&mut self) {
        let mut seen = Vec::new();
        for on in self.ons {
            if let OnTarget::Name(name) = &on.target
                && let Some(label) = name.strip_prefix("#decreasing:")
            {
                if seen.contains(&name) {
                    self.fail(format!("duplicate discharge for decrease label `{label}`"), on.span);
                } else if !self.sites.iter().any(|(_, n, ..)| n == name) {
                    self.fail(format!("unknown decrease label `{label}` in this declaration"), on.span);
                }
                seen.push(name);
            }
        }
    }

    /// `f(ȳ, spill…)` ↦ `ih(ȳ, proof, spill…)`, and for a group member
    /// `j(ȳ, spill…)` ↦ `ih.<proj_j>(ȳ, proof, spill…)`
    /// (`docs/language/recursion/mutual-recursion-design.md` §3). Arguments were rewritten by
    /// the caller already, so a nested self-call is handled inside out.
    fn self_call(&mut self, target: usize, call: &Expr, args: Vec<Expr>, explicit: bool) -> Expr {
        let span = call.span;
        let to = &self.members[target];
        let tname = to.name.clone();
        let tparams = to.params.clone();
        let positions: Vec<usize> = (0..tparams.len())
            .filter(|&j| explicit || !tparams[j].implicit)
            .collect();
        if positions.len() < tparams.len() {
            self.fail(
                format!(
                    "a recursive call to `{tname}` under `decreases` passes every parameter, \
                     implicit ones included: write `@{tname}(…)`"
                ),
                span,
            );
        }
        if args.len() < positions.len() {
            self.fail(
                format!(
                    "a recursive call to `{tname}` under `decreases` is saturated: it takes \
                     {} argument(s), found {}",
                    positions.len(),
                    args.len()
                ),
                span,
            );
            return call.clone();
        }
        let (passed, spill) = args.split_at(positions.len());
        // e[ȳ]: the callee's measure with each of *its* parameters replaced by
        // the argument written at that position.
        let map: Vec<(&str, &Expr)> = positions
            .iter()
            .zip(passed)
            .map(|(&j, a)| (tparams[j].name.as_str(), a))
            .collect();
        let to = &self.members[target];
        let at_args = subst(&to.measure, &map, &mut Vec::new());
        // §4: a group states the obligation at the *scaled* measure but writes
        // it at the unscaled one, and a call that lowers the rank owes only
        // `<=`. A singleton has neither notion.
        let clean = (self.members.len() > 1).then(|| {
            let raw_args = subst(&to.raw, &map, &mut Vec::new());
            let strict = to.rank >= self.members[self.caller].rank;
            let caller = &self.members[self.caller];
            let hint = (to.rank > caller.rank
                && crate::traits::render_expr(&self.refine(&raw_args).pop().expect("seeded"))
                    == crate::traits::render_expr(
                        &self.refine(&caller.raw).pop().expect("seeded"),
                    ))
            .then(|| {
                format!(
                    "`{tname}` is declared above `{}`, so a call at an unchanged measure \
                     may only go forward in the group; reorder the declarations, or make \
                     the measure strictly decrease",
                    caller.name
                )
            });
            Clean {
                args: raw_args,
                strict,
                ranks: (to.rank, caller.rank),
                hint,
            }
        });
        let proj = self.members[target].proj;
        let label = call.named_args().iter().find(|a| a.name.starts_with("#decreasing:"))
            .map(|a| a.name.as_str());
        let acc = self.obligation(&at_args, clean, span, label);
        let var = |n: &str| Expr {
            kind: ExprKind::Var(n.to_string()),
            span,
        };
        let app = |head: Expr, args: Vec<Expr>| Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        // Succ(e[ȳ]) <= e, e <= k  ⊢  Succ(e[ȳ]) <= k, which is `e[ȳ] < k`;
        // `h : e < Succ k` *is* `e <= k` by reduction.
        let proof = app(
            var("nat::Nat::le_trans"),
            vec![
                app(var("Succ"), vec![at_args]),
                self.measure.clone(),
                var(K),
                acc,
                var(H),
            ],
        );
        let mut all: Vec<Expr> = passed.to_vec();
        all.push(proof);
        all.extend(spill.iter().cloned());
        project(var(IH), proj, all, span)
    }

    /// `Nat::scaled_lt(args, raw, to, from, N, __dec_clean, trivial)` — §4's
    /// arithmetic from the clean statement to the scaled one, at this site's
    /// literal ranks. The rank side condition (`to < N`, or `to < from` at a
    /// rank-lowering call) is over literals, so `trivial` computes it.
    fn scale(&self, c: &Clean, args: &Expr, raw: &Expr, span: Span) -> Expr {
        let num = |k: usize| Expr {
            kind: ExprKind::Num((k as u64).into()),
            span,
        };
        app(
            var(if c.strict { "nat::Nat::scaled_lt" } else { "nat::Nat::scaled_le" }, span),
            vec![
                args.clone(),
                raw.clone(),
                num(c.ranks.0),
                num(c.ranks.1),
                num(self.members.len()),
                var("__dec_clean", span),
                var("trivial", span),
            ],
            span,
        )
    }

    /// The obligation this self-call site owes, as the body will spell it: a
    /// reference to the site's lifted `f#obl_N` (§4), stated at the
    /// **refined** measure and transported back to the ih's own statement
    /// through the enclosing arms' equations.
    ///
    /// Separate from [`Self::self_call`] because the companions re-emit
    /// exactly this term — same numbering, same reference — under their own
    /// bound and hypothesis, which is what makes the three spellings of a
    /// self-call identical.
    fn obligation(&mut self, at_args: &Expr, clean: Option<Clean>, span: Span, label: Option<&str>) -> Expr {
        // The measure as the enclosing arms know it: `e[Succ(k)/n]` inside
        // `match n { Succ(k) => … }`, and so on down.
        let stages = self.stages();
        let refined = stages.last().expect("stage 0 is the measure itself").clone();
        // …and the *argument's* measure refined the same way
        // (`docs/language/recursion/mutual-recursion-design.md` §4): a sibling call at an
        // unchanged argument has `at_args` mentioning the scrutinee too, and
        // the unrefined statement is then unprovable. Where `at_args` names no
        // refined variable every stage is the same expression, which is the
        // one-sided behaviour this generalizes.
        let at_stages = self.refine(at_args);
        let at_args = at_stages.last().expect("stage 0 is the argument's measure");
        let site = self.next;
        let hole = label.map(str::to_owned).unwrap_or_else(|| format!("dec{site}"));
        self.next += 1;
        // What the writer is told they owe: for a group, the *unscaled*
        // statement of §4 — the one they wrote the measure to make true —
        // and not the flattening `omega` closes for them.
        let clean = clean.map(|c| {
            let refined_raw = self
                .refine(&self.members[self.caller].raw)
                .pop()
                .expect("seeded");
            let args = self.refine(&c.args).pop().expect("seeded");
            (c, args, refined_raw)
        });
        let text = match &clean {
            Some((c, args, raw)) => format!(
                "{} {} {}",
                crate::traits::render_expr(args),
                if c.strict { "<" } else { "<=" },
                crate::traits::render_expr(raw)
            ),
            None => format!(
                "{} < {}",
                crate::traits::render_expr(at_args),
                crate::traits::render_expr(&refined)
            ),
        };
        let hint = clean.as_ref().and_then(|(c, ..)| c.hint.clone());
        let on = self
            .ons
            .iter()
            .find(|o| matches!(&o.target, OnTarget::Name(n) if *n == hole))
            .cloned();
        // What the obligation is proved by, wherever it is raised: the
        // writer's hole where an `on` names it, `omega` where the closer is
        // available, and the bare hole otherwise (reported with its
        // statement, `docs/language/recursion/termination-measures-design.md` §2).
        let goal = match &clean {
            Some((c, args, raw)) => of_expr(app(var(if c.strict { "nat::Nat::Lt" } else { "nat::Nat::Le" }, span),
                vec![args.clone(), raw.clone()], span)),
            None => lt_ty(at_args.clone(), refined.clone(), span),
        };
        // A rank-lowering call at an unchanged argument owes `x <= x` — the
        // same-measure sibling call §4's rank exists for — which is
        // `Nat::le_refl` whatever else is imported.
        let reflexive = clean.as_ref().and_then(|(c, args, raw)| {
            (!c.strict && crate::traits::render_expr(args) == crate::traits::render_expr(raw))
                .then(|| app(var("nat::Nat::le_refl", span), vec![raw.clone()], span))
        });
        let automatic = if on.is_none() {
            reflexive.or_else(|| {
                self.tys.local_evidence(self.decl, &self.scope, &goal, self.omega_available)
            })
        } else { None };
        let closer = if let Some(proof) = &automatic {
            proof.clone()
        } else if on.is_some() || !self.omega_available {
            Expr {
                kind: ExprKind::Hole(Some(hole.clone())),
                span,
            }
        } else {
            Expr {
                kind: ExprKind::Var(CLOSER.into()),
                span,
            }
        };
        // The lifted declaration's body. Without a clean statement it is the
        // closer alone, as Part A had it; with one it binds the writer's
        // statement to the closer and does §4's arithmetic on top with
        // `Nat::scaled_lt`/`Nat::scaled_le`.
        let on_expr = on.as_ref().map(|o| self.with_read_facts(&o.expr, &goal)).or(automatic);
        let body = match &clean {
            None => Block {
                stmts: Vec::new(),
                result: Box::new(closer.clone()),
                ons: on.clone().into_iter().collect(),
                span,
            },
            Some((c, args, raw)) => Block {
                stmts: vec![Stmt::Let {
                    name: "__dec_clean".into(),
                    ty: Some(of_expr(Expr {
                        kind: ExprKind::App {
                            head: Box::new(var(
                                if c.strict { "nat::Nat::Lt" } else { "nat::Nat::Le" },
                                span,
                            )),
                            args: vec![args.clone(), raw.clone()],
                            named: Vec::new(),
                            explicit: false,
                            goal_oriented: false,
                        },
                        span,
                    })),
                    expr: closer.clone(),
                    span,
                    opaque: false,
                }],
                result: Box::new(self.scale(c, args, raw, span)),
                ons: on.clone().into_iter().collect(),
                span,
            },
        };
        let lifted = self
            .lift
            .then(|| {
                self.lift_obligation(
                    site,
                    &hole,
                    &text,
                    at_args,
                    &refined,
                    on_expr,
                    body,
                    hint.clone(),
                    span,
                )
            })
            .flatten();
        let obligation = match lifted {
            Some(reference) => reference,
            None => {
                self.obls.push(None);
                closer
            }
        };
        self.sites.push((span, hole, text, hint));
        let var = |n: &str| Expr {
            kind: ExprKind::Var(n.to_string()),
            span,
        };
        let app = |head: Expr, args: Vec<Expr>| Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let lt = |a: Expr, b: Expr| app(var("nat::Nat::Lt"), vec![a, b]);
        // Transport the obligation back from the refined measure to the
        // measure the ih's hypothesis is stated at, one equation at a time:
        // `j(sym(eq_i), λ y _ => e[ȳ] < e_{i-1}[y/v_i], acc)` turns a proof at
        // `e_i = e_{i-1}[pat_i/v_i]` into one at `e_{i-1}`.
        let mut acc = obligation;
        for (i, (v, _, eq)) in self.refinements.iter().enumerate().rev() {
            let below = &stages[i];
            let y = format!("__dec_y{i}");
            let at_y = subst(below, &[(v.as_str(), &var(&y))], &mut Vec::new());
            let arg_y = subst(&at_stages[i], &[(v.as_str(), &var(&y))], &mut Vec::new());
            let motive = Expr {
                kind: ExprKind::Lam {
                    binders: [y.as_str(), "__dec_q"]
                        .into_iter()
                        .map(|n| LamBinder {
                            name: n.to_string(),
                            ty: None,
                            implicit: false,
                            span,
                        })
                        .collect(),
                    body: Box::new(lt(arg_y, at_y)),
                },
                span,
            };
            acc = Expr {
                kind: ExprKind::J {
                    proof: Box::new(app(var("sym"), vec![var(eq)])),
                    motive: Box::new(motive),
                    case: Box::new(acc),
                },
                span,
            };
        }
        acc
    }

    /// The writer's discharge as the binders it reads: itself, and where a
    /// search in it reads its context (`{ let d = x.half_add_le(); omega }`)
    /// also the arithmetic facts in scope about the goal, as a found proof's
    /// are (`lift_found_proof`). The search names none of them, so without
    /// these the lifted `f#obl_N` would quantify none, and a test's `h: 0 < x`
    /// that the discharge reads at the call would be missing from it
    /// (issues/decreases-on-block-let-no-unfold.md). Used only to choose
    /// the binders, never as the proof.
    fn with_read_facts(&self, on: &Expr, goal: &Ty) -> Expr {
        let mut searches = false;
        crate::surface::walk_expr(on, &mut |e| {
            searches |= crate::defaults::is_context_search(e)
                || matches!(&e.kind, ExprKind::App { head, .. } if crate::defaults::is_context_search(head));
        });
        if !searches {
            return on.clone();
        }
        let span = on.span;
        let mut facts = Vec::new();
        for (i, b) in self.scope.iter().enumerate() {
            let Some(ty) = &b.ty else { continue };
            if self.scope[i + 1..].iter().any(|c| c.name == b.name) { continue; }
            if arithmetic_fact(ty, goal, &self.scope) {
                facts.push(Stmt::Let { name: format!("__read_fact_{}", facts.len()), ty: None,
                    expr: var(&b.name, span), span, opaque: false });
            }
        }
        if facts.is_empty() {
            return on.clone();
        }
        Expr { kind: ExprKind::Block(Box::new(Block { stmts: facts, result: Box::new(on.clone()), ons: Vec::new(), span })), span }
    }

    /// Lift one site's obligation into `f#obl_N` and return the reference that
    /// replaces it (§4). The declaration quantifies exactly the binders in
    /// scope its statement — or the writer's `on` — names, under their own
    /// names and in binding order, so that both the body and the companions
    /// spell the call `f#obl_N(ȳ)` with the same arguments.
    ///
    /// `None` where a binder the statement names has no type this walk can
    /// write: the obligation then stays at the call, and the companions
    /// decline the body.
    #[allow(clippy::too_many_arguments)]
    fn lift_obligation(
        &mut self,
        site: usize,
        hole: &str,
        text: &str,
        at_args: &Expr,
        refined: &Expr,
        on: Option<Expr>,
        body: Block,
        hint: Option<String>,
        span: Span,
    ) -> Option<Expr> {
        let name = obl_name(&self.decl.name, site);
        // A companion's site cites the body's declaration, over the binders
        // it quantified, wherever each is in scope here too.
        if let Some(known) = self.known.iter().find(|l| l.decl.name == name) {
            let names: Vec<&str> = known.decl.params.iter().map(|p| p.name.as_str()).collect();
            if names.iter().all(|n| self.scope.iter().any(|b| b.name == *n)) {
                self.obls.push(Some(known.clone()));
                let head = companion_ref(self.decl, &name, span);
                return Some(if names.is_empty() {
                    head
                } else {
                    app(head, names.iter().map(|n| var(n, span)).collect(), span)
                });
            }
        }
        let mut params = Vec::new();
        let mut args = Vec::new();
        let goal = lt_ty(at_args.clone(), refined.clone(), span);
        // The declaration's own parameters that state an arithmetic fact
        // (a lifted loop's invariant, `j <= i`) go with the obligation: an
        // alias it reads may hold a found proof that needs them
        // (`s.put(j, v)` in a `while` body).
        let facts: Vec<Expr> = self
            .decl
            .params
            .iter()
            .filter(|p| {
                let ty = match &p.ty.kind { TyKind::Squash(inner) => &**inner, _ => &p.ty };
                matches!(&ty.kind, TyKind::OfExpr(e)
                    if matches!(&e.kind, ExprKind::App { head, .. }
                        if matches!(&head.kind, ExprKind::OpSymbol { symbol, .. } if matches!(symbol.as_str(), "<" | "<="))))
            })
            .map(|p| var(&p.name, span))
            .collect();
        let evidence = match (&on, facts.is_empty()) {
            (_, true) => on.clone(),
            (on, false) => {
                let mut stmts: Vec<Stmt> = facts
                    .into_iter()
                    .enumerate()
                    .map(|(k, f)| Stmt::Let { name: format!("__obl_fact_{k}"), ty: None, expr: f, span, opaque: false })
                    .collect();
                if let Some(on) = on {
                    stmts.push(Stmt::Let { name: "__obl_on".into(), ty: None, expr: on.clone(), span, opaque: false });
                }
                Some(Expr { kind: ExprKind::Block(Box::new(Block { stmts, result: Box::new(var("__obl_on", span)), ons: Vec::new(), span })), span })
            }
        };
        let selected = select_scope(&self.scope, &goal, evidence.as_ref())?;
        // Aliases are substituted by their values, earlier aliases first, in
        // the later binders' types and in the statement; the body keeps them
        // as the `let`s they are, for whatever proof names them.
        let mut aliases: Vec<(String, Expr)> = Vec::new();
        let unalias_ty = |t: &Ty, aliases: &[(String, Expr)]| {
            aliases.iter().fold(t.clone(), |t, (n, v)| subst_surface_ty(&t, n, v))
        };
        let mut lets = Vec::new();
        for b in selected {
            let ty = b.ty.clone()?;
            if let Some(value) = &b.value {
                let mut seen = Vec::new();
                let value = aliases.iter().fold(value.clone(), |v, (n, a)| subst(&v, &[(n.as_str(), a)], &mut seen));
                lets.push(Stmt::Let { name: b.name.clone(), ty: Some(unalias_ty(&ty, &aliases)), expr: value.clone(), span, opaque: false });
                aliases.push((b.name.clone(), value));
                continue;
            }
            params.push(param(&b.name, unalias_ty(&ty, &aliases), span));
            args.push(var(&b.name, span));
        }
        let at_args = &aliases.iter().fold(at_args.clone(), |e, (n, v)| subst(&e, &[(n.as_str(), v)], &mut Vec::new()));
        let refined = &aliases.iter().fold(refined.clone(), |e, (n, v)| subst(&e, &[(n.as_str(), v)], &mut Vec::new()));
        let body = if lets.is_empty() {
            body
        } else {
            lets.extend(body.stmts);
            Block { stmts: lets, ..body }
        };
        let decl = Decl {
            kind: DeclKind::Theorem,
            is_meta: false,
            is_evidence: false,
            is_interface: false, partial: None,
            value: false,
            elaborates: None,
            name: name.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result: lt_ty(at_args.clone(), refined.clone(), span),
            decreases: None,
            unfolding: Vec::new(),
            body,
            span: self.decl.span,
        };
        self.obls.push(Some(Lowered {
            decl,
            // The site travels with the declaration, so an `omega` failure is
            // still reworded at the call it belongs to.
            obligations: Obligations {
                sites: vec![(span, hole.to_string(), text.to_string(), hint)],
            },
        }));
        let head = companion_ref(self.decl, &name, span);
        Some(if args.is_empty() {
            head
        } else {
            app(head, args, span)
        })
    }

    /// The proofs the call `e` leaves to a context-reading default, each
    /// lifted into `f#found_N` and given back as the named argument that
    /// passes it. `e` is the call as written: the query elaborates it whole,
    /// its arguments' own defaults included.
    fn found_proofs(&mut self, e: &Expr, named: &[heather_syntax::NamedArg]) -> Vec<heather_syntax::NamedArg> {
        let signatures: Vec<_> = self.members.iter().map(|m|
            (m.name.clone(), pi_over(&m.params, m.result.clone(), e.span))).collect();
        let goals = self.tys.default_goals(self.decl, &signatures, &self.scope, e);
        goals.into_iter().filter_map(|g| {
            if named.iter().any(|a| a.name == g.name) { return None; }
            let proof = self.lift_found_proof(&g, e.span)?;
            Some(heather_syntax::NamedArg { name: g.name, name_span: e.span, expr: proof, span: e.span })
        }).collect()
    }

    /// The named arguments of `found_fact<P>(fact := search)` (`head` is
    /// `found_fact<P>`) with the search lifted into `f#found_N`, whose goal
    /// is `∥P∥` as written: no query is needed to find it. `None` for any
    /// other call, or where the lift declines.
    fn found_fact(&mut self, head: &Expr, named: &[heather_syntax::NamedArg], span: Span) -> Option<Vec<heather_syntax::NamedArg>> {
        let ExprKind::TyApp { head: callee, args } = &head.kind else { return None };
        let (ExprKind::Var(n), [p]) = (&callee.kind, args.as_slice()) else { return None };
        if n != FOUND_FACT {
            return None;
        }
        let k = named.iter().position(|a| a.name == "fact" && crate::defaults::is_context_search(&a.expr))?;
        let goal = FoundGoal { name: "fact".into(), goal: Ty { kind: TyKind::Squash(Box::new(p.clone())), span }, default: named[k].expr.clone() };
        let proof = self.lift_found_proof(&goal, span)?;
        let mut named = named.to_vec();
        named[k].expr = proof;
        Some(named)
    }

    /// `theorem f#found_N(ȳ): goal { let fact… = …; default }` over the
    /// binders the goal and the facts in scope about them name, and the
    /// reference `f#found_N(ȳ)`. The facts are bound in the body so the
    /// search reads them, as a lifted obligation's are.
    fn lift_found_proof(&mut self, g: &FoundGoal, span: Span) -> Option<Expr> {
        let mut facts = Vec::new();
        for (i, b) in self.scope.iter().enumerate().rev() {
            let Some(ty) = &b.ty else { continue };
            if self.scope[i + 1..].iter().any(|c| c.name == b.name) { continue; }
            if facts.len() < 16 && arithmetic_fact(ty, &g.goal, &self.scope) {
                facts.push(Stmt::Let { name: format!("__found_fact_{}", facts.len()), ty: None,
                    expr: var(&b.name, span), span, opaque: false });
            }
        }
        let search = Block { stmts: facts, result: Box::new(g.default.clone()), ons: Vec::new(), span };
        let evidence = Expr { kind: ExprKind::Block(Box::new(search.clone())), span };
        // The aliases in scope at their rewritten values, whose reads name
        // the proofs lifted before this one.
        let view: Vec<Binder> = self
            .scope
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let rewritten = b.value.as_ref().and_then(|v| {
                    self.found_values.iter().rev().find(|(at, n, sp, _)| *at == i && *n == b.name && *sp == v.span)
                });
                match rewritten {
                    Some((.., v)) => Binder { value: Some(v.clone()), ..b.clone() },
                    None => b.clone(),
                }
            })
            .collect();
        let selected = select_scope(&view, &g.goal, Some(&evidence))?;
        let mut params = Vec::new();
        let mut args = Vec::new();
        let mut aliases: Vec<(String, Expr)> = Vec::new();
        let unalias_ty = |t: &Ty, aliases: &[(String, Expr)]| {
            aliases.iter().fold(t.clone(), |t, (n, v)| subst_surface_ty(&t, n, v))
        };
        let mut lets = Vec::new();
        for b in selected {
            let ty = b.ty.clone()?;
            if let Some(value) = &b.value {
                let mut seen = Vec::new();
                let value = aliases.iter().fold(value.clone(), |v, (n, a)| subst(&v, &[(n.as_str(), a)], &mut seen));
                lets.push(Stmt::Let { name: b.name.clone(), ty: Some(unalias_ty(&ty, &aliases)), expr: value.clone(), span, opaque: false });
                aliases.push((b.name.clone(), value));
                continue;
            }
            params.push(param(&b.name, unalias_ty(&ty, &aliases), span));
            args.push(var(&b.name, span));
        }
        lets.extend(search.stmts);
        let name = found_name(&self.decl.name, self.found.len() + 1);
        let decl = Decl {
            kind: DeclKind::Theorem,
            is_meta: false,
            is_evidence: false,
            is_interface: false, partial: None,
            value: false,
            elaborates: None,
            name: name.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result: unalias_ty(&g.goal, &aliases),
            decreases: None,
            unfolding: Vec::new(),
            body: Block { stmts: lets, ..search },
            span: self.decl.span,
        };
        self.found.push(Lowered { decl, obligations: Obligations { sites: Vec::new() } });
        let head = companion_ref(self.decl, &name, span);
        Some(if args.is_empty() { head } else { app(head, args, span) })
    }

    /// Query the ordinary elaborator in an isolated local telescope. Recursive
    /// signatures are neutral locals used only for recovering types; emitted
    /// calls still go through the well-founded induction hypothesis.
    fn infer_local(&self, e: &Expr) -> Option<Ty> {
        let signatures: Vec<_> = self.members.iter().map(|m|
            (m.name.clone(), pi_over(&m.params, m.result.clone(), e.span))).collect();
        self.tys.infer_local(self.decl, &signatures, &self.scope, e)
    }

    fn scrut_ty(&self, e: &Expr) -> Option<Ty> {
        if let ExprKind::Var(v) = &e.kind {
            return self.scope.iter().rev().find(|b| &b.name == v)?.ty.clone();
        }
        self.infer_local(e)
    }

    /// [`Self::scrut_ty`] for the scrutinee of a `match` with `arms`: a call
    /// under `When`'s constructors has the type of its test
    /// (docs/language/when-design.md §4), as the `match` elaborates it.
    fn match_scrut_ty(&self, e: &Expr, arms: &[Arm]) -> Option<Ty> {
        match crate::tested::tested_marker(e, arms) {
            Some(marked) => self.infer_local(&marked),
            None => self.scrut_ty(e),
        }
    }

    /// Bind one arm pattern, typing its binders from the scrutinee's type
    /// through [`BinderTys`]; a position the oracle declines binds untyped,
    /// which only costs the sites whose statements name it their lifting.
    fn bind_pat(&mut self, p: &Pat, ty: Option<&Ty>) {
        match p {
            Pat::Var { name, .. } => {
                // A bare nullary constructor is a pattern, not a local.
                if ty.and_then(|t| self.tys.ctor_fields(t, name)).is_some_and(|f| f.is_empty()) {
                    return;
                }
                self.scope.push(Binder { name: name.clone(), ty: ty.cloned(), value: None });
            },
            Pat::Ctor { name, args, .. } => {
                let fields = ty
                    .and_then(|t| self.tys.ctor_fields(t, name))
                    .filter(|f| f.len() == args.len());
                for (i, q) in args.iter().enumerate() {
                    self.bind_pat(q, fields.as_ref().map(|f| &f[i]));
                }
            }
            Pat::Named { pat, .. } => self.bind_pat(pat, None),
        }
    }

    /// The binders an arm introduces, typed at the scrutinee's type.
    fn bind_arm(&mut self, a: &Arm, scrut: Option<&Ty>) {
        let fields = scrut
            .and_then(|t| self.tys.ctor_fields(t, &a.ctor))
            .filter(|f| f.len() == a.binders.len());
        for (i, p) in a.binders.iter().enumerate() {
            self.bind_pat(p, fields.as_ref().map(|f| &f[i]));
        }
    }

    /// `e_0 = e`, `e_i = e_{i-1}[pat_i/v_i]` for each refinement in force.
    fn stages(&self) -> Vec<Expr> {
        self.refine(self.measure)
    }

    /// The same staging applied to any expression — the argument's measure as
    /// well as the caller's (`docs/language/recursion/mutual-recursion-design.md` §4).
    fn refine(&self, e: &Expr) -> Vec<Expr> {
        let mut stages = vec![e.clone()];
        for (v, pat, _) in &self.refinements {
            let last = stages.last().expect("seeded");
            stages.push(subst(last, &[(v.as_str(), pat)], &mut Vec::new()));
        }
        stages
    }

    /// A copy whose output is read and whose bookkeeping is thrown away: it
    /// spells a subterm exactly as `f#body` spells it (same obligation
    /// numbering, same transports) without advancing this walk.
    /// Whether a match is an [`AutoEqs`] candidate: a plain `match` or an
    /// `if` without an equation binding, on a computed scrutinee (let-aliased
    /// by the time it is walked), with an arm that calls a member. An `if`
    /// is the match on its test's bit, so a plain `if c` gets the equation
    /// `if h: c` writes (issues/measured-span-loop-plain-if.md).
    fn auto_candidate(&self, form: MatchForm, scrut: &Expr, eqbind: &Option<String>, arms: &[Arm]) -> bool {
        matches!(form, MatchForm::Match | MatchForm::If)
            && eqbind.is_none()
            && matches!(&scrut.kind, ExprKind::Var(v) if self.scrut_aliases.iter().any(|(n, _)| n == v))
            && arms.iter().any(|a| self.calls_member(&a.body))
    }

    /// Whether `e` calls a member of this recursion.
    pub(crate) fn calls_member(&self, e: &Expr) -> bool {
        let mut found = false;
        crate::surface::walk_expr(e, &mut |x| {
            if let ExprKind::App { head, .. } = &x.kind {
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if self.members.iter().any(|m| &m.name == n)) {
                    found = true;
                }
            }
        });
        found
    }

    fn fork(&self) -> Rewrite<'a> {
        Rewrite {
            decl: self.decl,
            name: self.name,
            params: self.params,
            measure: self.measure,
            ons: self.ons,
            omega_available: self.omega_available,
            tys: self.tys,
            lift: self.lift,
            members: self.members,
            caller: self.caller,
            next: self.next,
            eqs: self.eqs,
            refinements: self.refinements.clone(),
            scrut_aliases: self.scrut_aliases.clone(),
            auto_eqs: self.auto_eqs.clone(),
            auto_n: self.auto_n,
            scope: self.scope.clone(),
            sites: self.sites.clone(),
            obls: self.obls.iter().map(|_| None).collect(),
            found_only: self.found_only,
            found: Vec::new(),
            found_values: self.found_values.clone(),
            known: self.known,
            error: None,
        }
    }

    /// The `__dec_scrut_N` name the `match` arm of [`Self::expr`] gives a
    /// computed scrutinee, bound in scope as that arm binds it. `None` where
    /// that arm binds nothing (an untypable scrutinee).
    fn bind_scrut_alias(&mut self, node: &Expr, scrut: &Expr) -> Option<String> {
        let ty = self.scrut_ty(scrut)?;
        let mut name = format!("__dec_scrut_{}", scrut.span.start);
        while self.scope.iter().any(|b| b.name == name)
            || mentions_context(node, &name)
            || self.ons.iter().any(|o| mentions_context(&o.expr, &name))
        { name.push('_'); }
        let value = (!self.members.iter().any(|m| mentions_context(scrut, &m.name))).then(|| scrut.clone());
        self.scope.push(Binder { name: name.clone(), ty: Some(ty), value });
        self.scrut_aliases.push((name.clone(), scrut.clone()));
        Some(name)
    }

    /// A `match` on a variable the (refined) measure mentions is given an
    /// equation binding, so that each arm can state the obligation at the
    /// pattern and transport it back (module docs). Arms whose patterns are
    /// not expressions (`_`, a named field) get no refinement and see the
    /// measure as the enclosing arm did.
    fn refining_match(&self, scrut: &Expr, eqbind: &Option<String>) -> Option<String> {
        let ExprKind::Var(v) = &scrut.kind else {
            return None;
        };
        if eqbind.is_some() {
            return None;
        }
        let refined = self.stages().pop().expect("seeded");
        mentions(&refined, v).then(|| format!("__dec_eq{}", self.eqs))
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        let span = e.span;
        let kind = match &e.kind {
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                goal_oriented,
            } => {
                // Postfix `?` introduces a private callback whose domain is
                // the preceding Result's success payload. Recover it before
                // walking the callback (and its recursive call sites).
                let payload = args.first().and_then(|input| {
                    args.get(1).filter(|a| matches!(&a.kind, ExprKind::Lam { binders, .. }
                        if binders.len() == 1 && binders[0].name.starts_with("#try")))?;
                    let input_ty = self.scrut_ty(input)?;
                    self.tys.ctor_fields(&input_ty, "Ok")?.into_iter().next()
                });
                let args: Vec<Expr> = args.iter().enumerate().map(|(i, a)| {
                    if i == 1 && let Some(ty) = &payload {
                        let mut a = a.clone();
                        if let ExprKind::Lam { binders, .. } = &mut a.kind {
                            binders[0].ty = Some(ty.clone());
                        }
                        self.expr(&a)
                    } else { self.expr(a) }
                }).collect();
                let named: Vec<heather_syntax::NamedArg> = named
                    .iter()
                    .map(|n| heather_syntax::NamedArg {
                        name: n.name.clone(),
                        name_span: n.name_span,
                        expr: self.expr(&n.expr),
                        span: n.span,
                    })
                    .collect();
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                // A call to any member of the recursion — the caller itself
                // included — is rewritten to the shared induction hypothesis
                // (`docs/language/recursion/mutual-recursion-design.md` §3); a group has no
                // separate self-call route.
                if self.found_only {
                    let mut named = named;
                    // `found_fact<P>(fact := search)`, a loop's fact where the
                    // loop starts: the search, with its goal `∥P∥` written,
                    // found once like a default's.
                    if let Some(found) = self.found_fact(head, &named, span) {
                        named = found;
                    } else if let ExprKind::Var(n) = callee
                        && !self.scope.iter().any(|b| b.name == *n)
                        && !self.members.iter().any(|m| m.name == *n)
                        && self.tys.has_context_default(n)
                    {
                        let given = self.found_proofs(e, &named);
                        named.extend(given);
                    }
                    return Expr {
                        kind: ExprKind::App {
                            head: Box::new(self.expr(head)),
                            args,
                            named,
                            explicit: *explicit,
                            goal_oriented: *goal_oriented,
                        },
                        span,
                    };
                }
                let target = match callee {
                    ExprKind::Var(n) if !self.scope.iter().any(|b| b.name == *n) => {
                        self.members.iter().position(|m| m.name == *n)
                    }
                    _ => None,
                };
                if let Some(target) = target {
                    if named.iter().any(|a| !a.name.starts_with("#decreasing:")) {
                        self.fail(
                            format!(
                                "a recursive call to `{}` under `decreases` takes positional \
                                 arguments only",
                                self.members[target].name
                            ),
                            span,
                        );
                    }
                    return self.self_call(target, e, args, *explicit);
                }
                if let Some(label) = named.iter().find(|a| a.name.starts_with("#decreasing:")) {
                    self.fail("a decrease label must name a call to a member of this recursion".into(), label.name_span);
                }
                ExprKind::App {
                    head: Box::new(self.expr(head)),
                    args,
                    named,
                    explicit: *explicit,
                    goal_oriented: *goal_oriented,
                }
            }
            // A statement `if`'s test is a proposition handed to
            // `decide_bit<s[i] < s[j]>()`: the reads in it leave their
            // proofs to searches as any read does, so they are lifted too.
            // Left in place, every copy of the body the companions
            // elaborate searches for them again
            // (issues/store-under-if-in-lifted-loop-cost.md).
            ExprKind::TyApp { head, args } => ExprKind::TyApp {
                head: Box::new(self.expr(head)),
                args: if self.found_only {
                    args.iter()
                        .map(|t| match &t.kind {
                            TyKind::OfExpr(x) => Ty { kind: TyKind::OfExpr(Box::new(self.expr(x))), span: t.span },
                            _ => t.clone(),
                        })
                        .collect()
                } else {
                    args.clone()
                },
            },
            ExprKind::Lam { binders, body } => {
                let n = self.scope.len();
                self.scope.extend(binders.iter().map(|b| Binder { name: b.name.clone(), ty: b.ty.clone(), value: None }));
                let body = self.expr(body);
                self.scope.truncate(n);
                ExprKind::Lam {
                    binders: binders.clone(),
                    body: Box::new(body),
                }
            }
            ExprKind::CollectionLit(xs) => {
                ExprKind::CollectionLit(xs.iter().map(|x| self.expr(x)).collect())
            }
            ExprKind::Eq(a, b) => {
                ExprKind::Eq(Box::new(self.expr(a)), Box::new(self.expr(b)))
            }
            ExprKind::Ascribe { expr, ty } => {
                ExprKind::Ascribe { expr: Box::new(self.expr(expr)), ty: ty.clone() }
            }
            ExprKind::Match {
                form,
                generated,
                scrut,
                eqbind,
                motive,
                arms,
            } => {
                if !self.found_only
                    && !matches!(scrut.kind, ExprKind::Var(_))
                    && let Some(ty) = self.scrut_ty(scrut)
                {
                    // Give the dependent match one shared scrutinee in its
                    // local telescope, just as a written annotated let does.
                    let mut name = format!("__dec_scrut_{}", scrut.span.start);
                    while self.scope.iter().any(|b| b.name == name)
                        || mentions_context(e, &name)
                        || self.ons.iter().any(|o| mentions_context(&o.expr, &name))
                    { name.push('_'); }
                    let mut matched = e.clone();
                    if let ExprKind::Match { scrut, .. } = &mut matched.kind {
                        **scrut = var(&name, span);
                    }
                    self.scrut_aliases.push((name.clone(), (**scrut).clone()));
                    return self.expr(&Expr { kind: ExprKind::Block(Box::new(Block {
                        stmts: vec![Stmt::Let { name, ty: Some(ty), expr: (**scrut).clone(), span, opaque: false }],
                        result: Box::new(matched), ons: Vec::new(), span,
                    })), span });
                }
                let refine = if *form == MatchForm::Match && !self.found_only {
                    self.refining_match(scrut, eqbind)
                } else {
                    None
                };
                if refine.is_some() {
                    self.eqs += 1;
                }
                let mut eqbind = eqbind.clone().or(refine.clone());
                // A match on a computed scrutinee whose arms recurse may
                // owe its arms the equation (design §4): number it, and bind
                // one where the policy admits it.
                if !self.found_only && self.auto_candidate(*form, scrut, &eqbind, arms) {
                    let n = self.auto_n;
                    self.auto_n += 1;
                    if self.auto_eqs.admits(n) {
                        eqbind = Some(format!("__dec_meq{n}"));
                    }
                }
                let scrut_ty = self.match_scrut_ty(scrut, arms);
                let arms = arms
                    .iter()
                    .map(|a| {
                        let pattern = refine
                            .as_ref()
                            .filter(|_| !a.default)
                            .and_then(|eq| pattern_expr(a, span).map(|p| (eq.clone(), p)));
                        if let (Some((eq, p)), ExprKind::Var(v)) = (&pattern, &scrut.kind) {
                            self.refinements.push((v.clone(), p.clone(), eq.clone()));
                        }
                        let n = self.scope.len();
                        self.bind_arm(a, scrut_ty.as_ref());
                        if let Some(eq) = &eqbind {
                            // Stated about the alias's value, so that a
                            // query reading it as a fact (`omega` over
                            // `leb(n, 1) = False`) sees its locals.
                            let stated = match &scrut.kind {
                                ExprKind::Var(v) => self.scrut_aliases.iter().rev()
                                    .find(|(n, _)| n == v).map(|(_, e)| e.clone()),
                                _ => None,
                            }.unwrap_or_else(|| (**scrut).clone());
                            let ty = pattern_expr(a, span).map(|p| eq_ty(stated.clone(), p, span));
                            self.scope.push(Binder { name: eq.clone(), ty, value: None });
                        }
                        let mut arm = a.clone();
                        arm.body = self.expr(&a.body);
                        self.scope.truncate(n);
                        if pattern.is_some() {
                            self.refinements.pop();
                        }
                        arm
                    })
                    .collect();
                ExprKind::Match {
                    form: *form,
                    generated: *generated,
                    scrut: Box::new(self.expr(scrut)),
                    eqbind,
                    motive: motive.as_ref().map(|m| Box::new(self.expr(m))),
                    arms,
                }
            }
            ExprKind::MatchCode {
                scrut,
                motive,
                arms,
            } => ExprKind::MatchCode {
                scrut: Box::new(self.expr(scrut)),
                motive: motive.clone(),
                arms: arms.iter().map(|a| self.arm(a, None, None)).collect(),
            },
            ExprKind::Dot {
                recv,
                name,
                tyargs,
                args,
                named,
            } => {
                // A method call that may leave a proof to a search
                // (`v.at(i)`): asked as a call of a global is.
                let given = if self.found_only && args.is_some() && self.tys.member_has_context_default(name) {
                    self.found_proofs(e, named)
                } else {
                    Vec::new()
                };
                let mut named: Vec<heather_syntax::NamedArg> = named
                    .iter()
                    .map(|n| heather_syntax::NamedArg {
                        name: n.name.clone(),
                        name_span: n.name_span,
                        expr: self.expr(&n.expr),
                        span: n.span,
                    })
                    .collect();
                named.extend(given);
                ExprKind::Dot {
                    recv: Box::new(self.expr(recv)),
                    name: name.clone(),
                    tyargs: tyargs.clone(),
                    args: args
                        .as_ref()
                        .map(|xs| xs.iter().map(|x| self.expr(x)).collect()),
                    named,
                }
            }
            // `v[i]` at a word index is `v.at(i)` (`inference::index_by_method`),
            // whose proof is lifted as the method call's is.
            ExprKind::Index { recv, idx } if self.found_only && self.tys.member_has_context_default("at") && {
                let at = Expr {
                    kind: ExprKind::Dot { recv: recv.clone(), name: "at".into(), tyargs: vec![], args: Some(vec![(**idx).clone()]), named: vec![] },
                    span: e.span,
                };
                !self.found_proofs(&at, &[]).is_empty()
            } => {
                let at = Expr {
                    kind: ExprKind::Dot { recv: recv.clone(), name: "at".into(), tyargs: vec![], args: Some(vec![(**idx).clone()]), named: vec![] },
                    span: e.span,
                };
                return self.expr(&at);
            }
            ExprKind::Index { recv, idx } => ExprKind::Index {
                recv: Box::new(self.expr(recv)),
                idx: Box::new(self.expr(idx)),
            },
            ExprKind::RecordUpdate { base, fields } => ExprKind::RecordUpdate {
                base: Box::new(self.expr(base)),
                fields: fields
                    .iter()
                    .map(|f| heather_syntax::RecordLitField { name: f.name.clone(), expr: self.expr(&f.expr), span: f.span })
                    .collect(),
            },
            ExprKind::RecordLit {
                name,
                tyargs,
                fields,
            } => ExprKind::RecordLit {
                name: name.clone(),
                tyargs: tyargs.clone(),
                fields: fields
                    .iter()
                    .map(|f| heather_syntax::RecordLitField {
                        name: f.name.clone(),
                        expr: self.expr(&f.expr),
                        span: f.span,
                    })
                    .collect(),
            },
            ExprKind::Block(block) => {
                let n = self.scope.len();
                let stmts: Vec<Stmt> = block.stmts.iter().map(|s| self.stmt(s)).collect();
                let result = self.expr(&block.result);
                let ons = block
                    .ons
                    .iter()
                    .map(|o| heather_syntax::OnStmt {
                        target: o.target.clone(),
                        expr: self.expr(&o.expr),
                        span: o.span,
                    })
                    .collect();
                self.scope.truncate(n);
                ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(result),
                    ons,
                    span: block.span,
                }))
            }
            ExprKind::Quote(x) => ExprKind::Quote(Box::new(self.expr(x))),
            ExprKind::Splice(x) => ExprKind::Splice(Box::new(self.expr(x))),
            ExprKind::J {
                proof,
                motive,
                case,
            } => ExprKind::J {
                proof: Box::new(self.expr(proof)),
                motive: Box::new(self.expr(motive)),
                case: Box::new(self.expr(case)),
            },
            // §2: a member's name outside a call the walk rewrites has no
            // meaning here — the group's declarations do not exist yet — so
            // it is refused where it is written rather than left to surface
            // as an unbound name in generated code.
            ExprKind::Var(n)
                if !self.found_only
                    && self.members.len() > 1
                    && self.members.iter().any(|m| m.name == *n)
                    && !self.scope.iter().any(|b| b.name == *n) =>
            {
                self.fail(
                    format!(
                        "`{n}` is a member of this mutual `decreases` group, so it is \
                         only usable as a saturated call here \
                         (docs/language/recursion/mutual-recursion-design.md §2)"
                    ),
                    span,
                );
                ExprKind::Var(n.clone())
            }
            leaf @ (ExprKind::Var(_)
            | ExprKind::OpSymbol { .. }
            | ExprKind::Univ { .. }
            | ExprKind::Num(_)
            | ExprKind::SuffixedNum { .. }
            | ExprKind::Scaled(_)
            | ExprKind::Char(_)
            | ExprKind::Str(_)
            | ExprKind::ByteStr(_)
            | ExprKind::ByteChar(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::TyLit(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl
            | ExprKind::Hole(_)) => leaf.clone(),
        };
        Expr { kind, span }
    }

    fn arm(&mut self, a: &Arm, eqbind: Option<&str>, scrut: Option<&Ty>) -> Arm {
        let n = self.scope.len();
        self.bind_arm(a, scrut);
        self.scope.extend(eqbind.map(|e| Binder {
            name: e.to_string(),
            ty: None,
            value: None,
        }));
        let body = self.expr(&a.body);
        self.scope.truncate(n);
        Arm {
            ctor: a.ctor.clone(),
            default: a.default,
            binders: a.binders.clone(),
            body,
            span: a.span,
        }
    }

    /// A statement, **extending** the scope with what it binds (the caller
    /// truncates at the block's end).
    /// What a written `let name: ty = expr` binds in [`Self::scope`]: its
    /// type, from the source before recursive calls are replaced, and its
    /// value, unless that reads the recursion. [`Respell`] binds the same
    /// for a `let` it walks through, so an obligation it re-emits selects
    /// the binders `f#body`'s did.
    fn let_binder(&self, name: &str, ty: &Option<Ty>, expr: &Expr, opaque: bool) -> Binder {
        let inferred = ty.clone().or_else(|| self.scrut_ty(expr));
        // An opaque `let` is a binder of its type to every query after it:
        // its value (a proof found once) is not elaborated again by each.
        let value = (!opaque && !self.members.iter().any(|m| mentions_context(expr, &m.name))).then(|| expr.clone());
        Binder { name: name.to_string(), ty: inferred, value }
    }

    fn stmt(&mut self, s: &Stmt) -> Stmt {
        match s {
            Stmt::Let {
                name,
                ty,
                expr,
                span,
                opaque,
            } => {
                // Query the source before replacing recursive calls by IH
                // applications. The result is only a telescope annotation.
                let binder = self.let_binder(name, ty, expr, *opaque);
                let written = expr.span;
                let expr = self.expr(expr);
                if self.found_only && binder.value.is_some() {
                    let at = self.scope.len();
                    self.found_values.retain(|(i, ..)| *i < at);
                    self.found_values.push((at, name.clone(), written, expr.clone()));
                }
                self.scope.push(binder);
                Stmt::Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    expr,
                    span: *span,
                    opaque: *opaque,
                }
            }
            Stmt::LetRecord { fields, expr, span } => {
                let expr = self.expr(expr);
                for f in fields {
                    self.bind_pat(&f.pat, None);
                }
                Stmt::LetRecord {
                    fields: fields.clone(),
                    expr,
                    span: *span,
                }
            }
            Stmt::LetCode { name, expr, span } => {
                let expr = self.expr(expr);
                self.scope.push(Binder {
                    name: name.clone(),
                    ty: None,
                    value: None,
                });
                Stmt::LetCode {
                    name: name.clone(),
                    expr,
                    span: *span,
                }
            }
        }
    }
}

/// An arm's pattern as the expression it matches: `Succ(k)`, `Cons(h, t)`.
/// `None` for a pattern with no expression form (a named field).
fn pattern_expr(a: &Arm, span: Span) -> Option<Expr> {
    fn go(p: &Pat, span: Span) -> Option<Expr> {
        Some(match p {
            Pat::Var { name, .. } => Expr {
                kind: ExprKind::Var(name.clone()),
                span,
            },
            Pat::Ctor { name, args, .. } => Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr {
                        kind: ExprKind::Var(name.clone()),
                        span,
                    }),
                    args: args.iter().map(|q| go(q, span)).collect::<Option<Vec<_>>>()?,
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            },
            Pat::Named { .. } => return None,
        })
    }
    let args = a
        .binders
        .iter()
        .map(|p| go(p, span))
        .collect::<Option<Vec<_>>>()?;
    let head = Expr {
        kind: ExprKind::Var(a.ctor.clone()),
        span,
    };
    Some(if args.is_empty() {
        head
    } else {
        Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        }
    })
}

/// Does `e` mention the free variable `v`? Over the forms `subst` walks.
pub(crate) fn mentions(e: &Expr, v: &str) -> bool {
    let mut found = false;
    crate::surface::walk_expr(e, &mut |x| {
        if matches!(&x.kind, ExprKind::Var(n) if n == v) {
            found = true;
        }
    });
    found
}

// Include annotations and explicit type arguments when collecting a lifted
// telescope. The ordinary expression walker deliberately skips these. Also
// how a parameter default is found to mention a type parameter.
pub(crate) fn mentions_context(e: &Expr, name: &str) -> bool {
    let mut found = false;
    crate::surface::walk_expr(e, &mut |e| {
        found |= match &e.kind {
            ExprKind::Var(n) => n == name,
            ExprKind::TyLit(t) => mentions_ty(t, name),
            ExprKind::TyApp { args, .. } => args.iter().any(|t| mentions_ty(t, name)),
            ExprKind::Lam { binders, .. } => binders.iter().any(|b| b.ty.as_ref().is_some_and(|t| mentions_ty(t, name))),
            ExprKind::Match { motive, .. } => motive.as_ref().is_some_and(|e| mentions_context(e, name)),
            ExprKind::MatchCode { motive, .. } => mentions_ty(motive, name),
            ExprKind::RecordLit { tyargs, .. } => tyargs.iter().any(|t| mentions_ty(t, name)),
            ExprKind::J { proof, motive, case } => [proof, motive, case].iter().any(|e| mentions_context(e, name)),
            ExprKind::Block(b) => b.stmts.iter().any(|s| matches!(s, Stmt::Let { ty: Some(t), .. } if mentions_ty(t, name))),
            _ => false,
        };
    });
    found
}

pub(crate) fn mentions_ty(t: &Ty, name: &str) -> bool {
    match &t.kind {
        TyKind::Named { name: n, args } => n == name || args.iter().any(|t| mentions_ty(t, name)),
        TyKind::OfExpr(e) | TyKind::Fin(e) => mentions_context(e, name),
        TyKind::Eq(a, b) => mentions_context(a, name) || mentions_context(b, name),
        TyKind::Vec { elem, len } => mentions_ty(elem, name) || mentions_context(len, name),
        TyKind::Fn { binder, dom, cod, .. } => mentions_ty(dom, name)
            || (binder.as_deref() != Some(name) && mentions_ty(cod, name)),
        TyKind::Squash(t) | TyKind::Code { ty: t, .. } => mentions_ty(t, name),
        _ => false,
    }
}

pub(crate) fn pat_names(p: &Pat, out: &mut Vec<String>) {
    match p {
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Ctor { args, .. } => args.iter().for_each(|a| pat_names(a, out)),
        Pat::Named { pat, .. } => pat_names(pat, out),
    }
}

/// `e[ȳ/x̄]`: the measure with each parameter name replaced by an argument
/// expression, stopping under a binder that shadows the name. Capture the
/// other way — an argument mentioning a name the measure binds — is not
/// avoided; a measure is a small expression over the parameters, and a
/// wrong substitution here yields an obligation the ih's domain refuses.
pub(crate) fn subst(e: &Expr, map: &[(&str, &Expr)], bound: &mut Vec<String>) -> Expr {
    let span = e.span;
    let go = |x: &Expr, bound: &mut Vec<String>| subst(x, map, bound);
    let kind = match &e.kind {
        ExprKind::Var(n) => {
            if !bound.iter().any(|b| b == n)
                && let Some((_, a)) = map.iter().find(|(p, _)| p == n)
            {
                return (*a).clone();
            }
            ExprKind::Var(n.clone())
        }
        ExprKind::App {
            head,
            args,
            named,
            explicit,
            goal_oriented,
        } => ExprKind::App {
            head: Box::new(go(head, bound)),
            args: args.iter().map(|a| go(a, bound)).collect(),
            named: named
                .iter()
                .map(|n| heather_syntax::NamedArg {
                    name: n.name.clone(),
                    name_span: n.name_span,
                    expr: go(&n.expr, bound),
                    span: n.span,
                })
                .collect(),
            explicit: *explicit,
            goal_oriented: *goal_oriented,
        },
        // A type argument can spell an expression too: an `if` on a test is a
        // `match` on `decide_bit<test>`, whose proposition is one. Left alone,
        // a `let`'s variable substituted away everywhere else stays free there
        // (issues/runtime-mut-self-let-read-walk.md).
        ExprKind::TyApp { head, args } => ExprKind::TyApp {
            head: Box::new(go(head, bound)),
            args: args
                .iter()
                .map(|t| {
                    let mut t = t.clone();
                    for (p, a) in map.iter().filter(|(p, _)| !bound.iter().any(|b| b == p)) {
                        t = subst_surface_ty(&t, p, a);
                    }
                    t
                })
                .collect(),
        },
        ExprKind::Lam { binders, body } => {
            let n = bound.len();
            bound.extend(binders.iter().map(|b| b.name.clone()));
            let body = go(body, bound);
            bound.truncate(n);
            ExprKind::Lam {
                binders: binders.clone(),
                body: Box::new(body),
            }
        }
        ExprKind::Dot {
            recv,
            name,
            tyargs,
            args,
            named,
        } => ExprKind::Dot {
            recv: Box::new(go(recv, bound)),
            name: name.clone(),
            tyargs: tyargs.clone(),
            args: args
                .as_ref()
                .map(|xs| xs.iter().map(|x| go(x, bound)).collect()),
            named: named
                .iter()
                .map(|n| heather_syntax::NamedArg {
                    name: n.name.clone(),
                    name_span: n.name_span,
                    expr: go(&n.expr, bound),
                    span: n.span,
                })
                .collect(),
        },
        ExprKind::Index { recv, idx } => ExprKind::Index {
            recv: Box::new(go(recv, bound)),
            idx: Box::new(go(idx, bound)),
        },
        ExprKind::Eq(a, b) => ExprKind::Eq(Box::new(go(a, bound)), Box::new(go(b, bound))),
        ExprKind::CollectionLit(xs) => {
            ExprKind::CollectionLit(xs.iter().map(|x| go(x, bound)).collect())
        }
        ExprKind::Match {
            form,
            generated,
            scrut,
            eqbind,
            motive,
            arms,
        } => ExprKind::Match {
            form: *form,
            generated: *generated,
            scrut: Box::new(go(scrut, bound)),
            eqbind: eqbind.clone(),
            motive: motive.as_ref().map(|m| Box::new(go(m, bound))),
            arms: arms
                .iter()
                .map(|a| {
                    let n = bound.len();
                    for p in &a.binders {
                        pat_names(p, bound);
                    }
                    bound.extend(eqbind.clone());
                    let body = go(&a.body, bound);
                    bound.truncate(n);
                    Arm {
                        ctor: a.ctor.clone(),
                        default: a.default,
                        binders: a.binders.clone(),
                        body,
                        span: a.span,
                    }
                })
                .collect(),
        },
        // `j` and blocks are not measure shapes, but the companions of
        // `docs/language/recursion/decreases-unfolding-design.md` §4 push substitutions through
        // obligation *proofs*, which are exactly these two.
        ExprKind::J {
            proof,
            motive,
            case,
        } => ExprKind::J {
            proof: Box::new(go(proof, bound)),
            motive: Box::new(go(motive, bound)),
            case: Box::new(go(case, bound)),
        },
        ExprKind::Block(block) => {
            let n = bound.len();
            let mut stmts = Vec::new();
            for st in &block.stmts {
                match st {
                    Stmt::Let {
                        name,
                        ty,
                        expr,
                        span,
                        opaque,
                    } => {
                        let expr = go(expr, bound);
                        bound.push(name.clone());
                        stmts.push(Stmt::Let {
                            name: name.clone(),
                            ty: ty.clone(),
                            expr,
                            span: *span,
                            opaque: *opaque,
                        });
                    }
                    // Not substituted into, but what they bind still shadows.
                    Stmt::LetRecord { fields, .. } => {
                        for f in fields {
                            pat_names(&f.pat, bound);
                        }
                        stmts.push(st.clone());
                    }
                    Stmt::LetCode { name, .. } => {
                        bound.push(name.clone());
                        stmts.push(st.clone());
                    }
                }
            }
            let result = go(&block.result, bound);
            bound.truncate(n);
            ExprKind::Block(Box::new(Block {
                stmts,
                result: Box::new(result),
                ons: block.ons.clone(),
                span: block.span,
            }))
        }
        // A record built or updated: a field path assigned in a body is the
        // second (docs/language/sequencing-surface-design.md §20).
        ExprKind::RecordUpdate { base, fields } => ExprKind::RecordUpdate {
            base: Box::new(go(base, bound)),
            fields: fields
                .iter()
                .map(|f| heather_syntax::RecordLitField { name: f.name.clone(), expr: go(&f.expr, bound), span: f.span })
                .collect(),
        },
        ExprKind::RecordLit { name, tyargs, fields } => ExprKind::RecordLit {
            name: name.clone(),
            tyargs: tyargs.clone(),
            fields: fields
                .iter()
                .map(|f| heather_syntax::RecordLitField { name: f.name.clone(), expr: go(&f.expr, bound), span: f.span })
                .collect(),
        },
        // A measure is an expression over the parameters; the remaining forms
        // either bind nothing to substitute under or are not measures anyone
        // writes. Left as they are.
        other => other.clone(),
    };
    Expr { kind, span }
}

/// [`subst`] at once, from the top, except that a value `e` reads more than
/// once is bound once by a `let` around the result and read through it:
/// `r with { a = r.a + i }` at `r := v` is `{ let __dec_shared_r = v;
/// __dec_shared_r with { a = __dec_shared_r.a + i } }`, never `v with { a =
/// v.a + i }`. The two are equal by ζ, which is all a re-spelling walk needs
/// of a `let`'s value (§3), and the second doubles in size at every
/// statement that reads its local twice: a `for` over words assigning a
/// field `k` times was elaborated at size 2^k (issues/word-loop-body-exponential.md).
///
/// A value that is a variable or a literal is substituted as before, as is
/// one read once. The `let`'s name cannot capture: what is substituted
/// under it are the map's values, which bind it only inside a block of
/// their own.
pub(crate) fn subst_shared(e: &Expr, map: &[(&str, &Expr)]) -> Expr {
    let atomic = |v: &Expr| matches!(v.kind, ExprKind::Var(_) | ExprKind::Num(_) | ExprKind::SuffixedNum { .. });
    let reads = |n: &str| {
        let mut k = 0usize;
        crate::surface::walk_expr(e, &mut |x| {
            if matches!(&x.kind, ExprKind::Var(m) if m == n) {
                k += 1;
            }
        });
        k
    };
    let shared: Vec<(&str, &Expr, String)> = map
        .iter()
        .filter(|(n, v)| !atomic(v) && reads(n) > 1)
        .map(|(n, v)| (*n, *v, format!("__dec_shared_{n}")))
        .collect();
    if shared.is_empty() {
        return subst(e, map, &mut Vec::new());
    }
    let span = e.span;
    let reads_of: Vec<Expr> = shared.iter().map(|(_, _, fresh)| var(fresh, span)).collect();
    let renamed: Vec<(&str, &Expr)> = map
        .iter()
        .map(|(n, v)| match shared.iter().position(|(m, _, _)| m == n) {
            Some(k) => (*n, &reads_of[k]),
            None => (*n, *v),
        })
        .collect();
    let body = subst(e, &renamed, &mut Vec::new());
    let stmts = shared
        .iter()
        .map(|(_, v, fresh)| Stmt::Let { name: fresh.clone(), ty: None, expr: (*v).clone(), span, opaque: false })
        .collect();
    Expr { kind: ExprKind::Block(Box::new(Block { stmts, result: Box::new(body), ons: Vec::new(), span })), span }
}

/// A block's statements with each claimed method call on a mutable local
/// (`\0mutated(x.m(a))`, [`heather_syntax::MUTATED`]) spelled as the plain
/// `let`s it amounts to: `let p = \0mutated_value(x.m(a));` (none for a
/// `#seq` statement), then `let x = \0mutated_after(x.m(a));`, or for a call
/// on a field path `x.f.m(a)` (§20) `x` with that field replaced. An
/// unclaimed candidate (`\0mutcall`) is an ordinary call. With the receiver's
/// rebinding a `let`, [`subst`] stops at it like at any other, and the call
/// keeps its receiver's value before it.
///
/// A claimed call whose receiver is no place is refused when `strict`, and
/// left as written otherwise (the walk refuses it if it reaches it).
pub(crate) fn rebind_marked(stmts: &[Stmt], span: Span, strict: bool) -> Result<Vec<Stmt>, String> {
    let mut out = Vec::with_capacity(stmts.len());
    for st in stmts {
        let Stmt::Let { name, expr, span: at, .. } = st else {
            out.push(st.clone());
            continue;
        };
        let marked = match &expr.kind {
            ExprKind::App { head, args, .. } if args.len() == 1 => match &head.kind {
                ExprKind::Var(n) if n == heather_syntax::MUTATED || n == heather_syntax::MUTCALL => {
                    Some((n == heather_syntax::MUTATED, &args[0]))
                }
                _ => None,
            },
            _ => None,
        };
        let plain = |name: &str, expr: Expr| Stmt::Let { name: name.to_string(), ty: None, expr, span: *at, opaque: false };
        match marked {
            Some((true, call)) => {
                // The local rebound: the receiver, or the local it is a
                // field path of, with that field replaced (§20).
                let hole = "#after";
                let place = match &call.kind {
                    ExprKind::Dot { recv, .. } => heather_syntax::place_update(recv, var(hole, span)),
                    _ => None,
                };
                let Some((receiver, update)) = place else {
                    if strict {
                        return Err("a marked call this walk cannot read".into());
                    }
                    out.push(st.clone());
                    continue;
                };
                let part = |marker: &str| app(var(marker, span), vec![call.clone()], span);
                if !name.starts_with("#seq") {
                    out.push(plain(name, part(heather_syntax::MUTATED_VALUE)));
                }
                let after = part(heather_syntax::MUTATED_AFTER);
                out.push(plain(&receiver, subst(&update, &[(hole, &after)], &mut Vec::new())));
            }
            // An unclaimed candidate is an ordinary call.
            Some((false, call)) => out.push(plain(name, call.clone())),
            None => out.push(st.clone()),
        }
    }
    Ok(out)
}

/// `e` with [`rebind_marked`] applied to every block in it, so that a
/// substitution into `e` respects the rebindings its statements make.
fn explicit_rebinds(e: &Expr) -> Expr {
    let mut out = e.clone();
    crate::alpha::walk_expr_mut(&mut out, &mut |x| {
        if let ExprKind::Block(b) = &mut x.kind {
            let span = b.span;
            if let Ok(stmts) = rebind_marked(&b.stmts, span, false) {
                b.stmts = stmts;
            }
        }
        false
    });
    out
}

// -- the unfolding companions -------------------------------------------------
//
// `docs/language/recursion/decreases-unfolding-design.md` §3–§6: a congruence proof over the
// body's own structure, with the self-call sites as its leaves, generated
// twice — once relating the arm to itself under two induction hypotheses
// (`f#ext`), once relating `f` to its body as written (`f_unfold`).

const A: &str = "__dec_a";
const B: &str = "__dec_b";
const G1: &str = "__dec_g1";
const G2: &str = "__dec_g2";
const HG: &str = "__dec_hg";
const H1: &str = "__dec_h1";
const H2: &str = "__dec_h2";
const P: &str = "__dec_p";
const W: &str = "__dec_w";

/// `f#ext` — the arm is extensional in its induction hypothesis.
pub(crate) fn ext_name(name: &str) -> String {
    format!("{name}#ext")
}

/// `f#irrel` — the recursor does not depend on which bound it was given.
pub(crate) fn irrel_name(name: &str) -> String {
    format!("{name}#irrel")
}

/// `f_unfold` — the artifact users cite, and so an ordinary name (§2).
pub(crate) fn unfold_name(name: &str) -> String {
    format!("{name}_unfold")
}

pub(crate) fn eq_ty(a: Expr, b: Expr, span: Span) -> Ty {
    Ty {
        kind: TyKind::Eq(Box::new(a), Box::new(b)),
        span,
    }
}

fn eq_expr(a: Expr, b: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Eq(Box::new(a), Box::new(b)),
        span,
    }
}

pub(crate) fn lam(binders: &[&str], body: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Lam {
            binders: binders
                .iter()
                .map(|n| LamBinder {
                    name: (*n).to_string(),
                    ty: None,
                    implicit: false,
                    span,
                })
                .collect(),
            body: Box::new(body),
        },
        span,
    }
}

fn ty_lit(ty: Ty, span: Span) -> Expr {
    Expr {
        kind: ExprKind::TyLit(Box::new(ty)),
        span,
    }
}

/// `(n₁: T₁) -> … -> cod`.
fn pi(binders: Vec<(&str, Ty)>, cod: Ty, span: Span) -> Ty {
    let mut ty = cod;
    for (n, dom) in binders.into_iter().rev() {
        ty = arrow(Some(n.to_string()), dom, ty, span);
    }
    ty
}

fn succ(e: Expr, span: Span) -> Expr {
    app(var("Succ", span), vec![e], span)
}

/// Which of the two companions a walk is generating: they differ only in how
/// the right-hand side is rendered and in what closes a self-call leaf
/// (§3's table).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Ext,
    Unfold,
}

/// Where the walk is (§3).
#[derive(Clone, Copy, PartialEq, Eq)]
enum At {
    /// The whole of what the two anchors denote.
    Anchor,
    /// Below the anchor, but still a whole result of the declaration's
    /// result type: an arm of a match both sides spell out
    /// ([`Respell::match_spelled`]). A match here is spelled out again, at
    /// the same constant motive.
    Result,
    /// An argument of a call, whose type the walk does not know.
    Argument,
}

/// The re-spelling walk (§3): a proof of `lhs = rhs` over the body's own
/// structure. `lhs`/`rhs` come back with the proof because a congruence step
/// one level up has to spell both sides of the argument it transports.
struct Triple {
    lhs: Expr,
    rhs: Expr,
    proof: Expr,
}

struct Respell<'a> {
    /// The body rewrite, driven in lockstep so that each self-call's
    /// obligation is *re-emitted* exactly as `f#body` spells it (§4) — same
    /// numbering, same hole name, same transport chain.
    rw: Rewrite<'a>,
    mode: Mode,
    decl: &'a Decl,
    /// The body as written, for `f_unfold`'s right-hand side.
    source: &'a Expr,
    /// What the enclosing arms substituted, outermost first, applied in order.
    sigma: Vec<(String, Expr)>,
    /// The bound hypotheses the anchors are currently at: `[h1, h2]` for
    /// `f#ext`, `[lt_succ_self(e)]` — then the generalized binder — for
    /// `f_unfold`.
    hyps: Vec<Expr>,
    /// `let`s owed by the arm being walked: the convoy equations at `refl`
    /// and the obligations, bound once and used on both sides (§4).
    lets: Vec<Stmt>,
    fresh: usize,
    span: Span,
    /// Inside an arm of a match on a computed scrutinee or with an equation
    /// binding (`convoy_at_anchor`), the anchors are no longer the whole
    /// declaration: `f#rec(…)` does not reduce into the arm, because its
    /// scrutinee is stuck. They are the arm's own bodies instead: the
    /// rewritten one (`f#body`'s spelling, with `__dec_k`/`__dec_ih`/`__dec_h`
    /// still free) and the source one. `None` at the top.
    anchors: Option<(Expr, Expr)>,
    /// The `let`s walked through, outermost first, each value with the ones
    /// before it substituted, and the length of the rewrite's scope after
    /// it: substituted into what the body spells before `sigma` (§3: `let`
    /// is zeta-transparent), unless a binder after it shadows it.
    let_env: Vec<(String, Expr, usize)>,
}

impl Respell<'_> {
    fn sigma_apply(&self, e: &Expr) -> Expr {
        self.sigma_apply_ext(e, None)
    }

    /// `σ(e)`, optionally with one more substitution appended — the motive's
    /// abstraction of the scrutinee.
    ///
    /// `e` is read where the body has it, so the `let`s walked through
    /// (`let_env`) are substituted first: a `let` may shadow a parameter, so
    /// the anchors' own arguments are [`Self::refine_ext`]'s alone.
    fn sigma_apply_ext(&self, e: &Expr, ext: Option<(&str, &Expr)>) -> Expr {
        self.refine_ext(&self.let_apply(e), ext)
    }

    /// `e` with the `let`s it sees substituted, at once: those not shadowed
    /// by a binder the rewrite's scope took after them (an arm's pattern or
    /// equation, a later `let`).
    fn let_apply(&self, e: &Expr) -> Expr {
        let map: Vec<(&str, &Expr)> = (0..self.let_env.len())
            .filter(|&i| self.let_visible(i))
            .map(|i| (self.let_env[i].0.as_str(), &self.let_env[i].1))
            .collect();
        subst_shared(&explicit_rebinds(e), &map)
    }

    /// Whether `let_env[i]` is what its name means here.
    fn let_visible(&self, i: usize) -> bool {
        let (n, _, at) = &self.let_env[i];
        !self.let_env[i + 1..].iter().any(|(m, _, _)| m == n)
            && !self.rw.scope.get(*at..).is_some_and(|later| later.iter().any(|b| &b.name == n))
    }

    /// `σ(e)` for an `e` over the declaration's parameters: the enclosing
    /// arms' patterns, and `ext`.
    fn refine_ext(&self, e: &Expr, ext: Option<(&str, &Expr)>) -> Expr {
        let mut out = e.clone();
        for (v, pat) in &self.sigma {
            out = subst(&out, &[(v.as_str(), pat)], &mut Vec::new());
        }
        if let Some((v, pat)) = ext {
            out = subst(&out, &[(v, pat)], &mut Vec::new());
        }
        out
    }

    fn args(&self, ext: Option<(&str, &Expr)>) -> Vec<Expr> {
        self.rw
            .params
            .iter()
            .map(|p| self.refine_ext(&var(&p.name, self.span), ext))
            .collect()
    }

    fn measure_at(&self, ext: Option<(&str, &Expr)>) -> Expr {
        self.refine_ext(self.rw.measure, ext)
    }

    fn cref(&self, name: &str) -> Expr {
        companion_ref(self.decl, name, self.span)
    }

    /// The left anchor: `f#body(a, g1, x̄, h1)`, or `f#rec(Succ(e), x̄, p)`.
    fn anchor_l(&self, ext: Option<(&str, &Expr)>, hyp: &Expr) -> Expr {
        let span = self.span;
        if let Some((rewritten, _)) = &self.anchors {
            return self.inferable(self.sigma_apply_ext(&self.instantiate(rewritten, hyp, false), ext), ext);
        }
        let mut args = match self.mode {
            Mode::Ext => vec![var(A, span), var(G1, span)],
            Mode::Unfold => vec![succ(self.measure_at(ext), span)],
        };
        args.extend(self.args(ext));
        args.push(hyp.clone());
        let head = match self.mode {
            Mode::Ext => body_name(&self.decl.name),
            Mode::Unfold => rec_name(&self.decl.name),
        };
        app(self.cref(&head), args, span)
    }

    /// The right anchor: `f#body(b, g2, x̄, h2)`, or the body **as written**
    /// with the enclosing arms' patterns substituted (§5 — no `__dec_…`
    /// binder reaches it).
    fn anchor_r(&self, ext: Option<(&str, &Expr)>, hyp: &Expr) -> Expr {
        let span = self.span;
        if let Some((rewritten, source)) = &self.anchors {
            let at = match self.mode {
                Mode::Ext => self.sigma_apply_ext(&self.instantiate(rewritten, hyp, true), ext),
                Mode::Unfold => self.sigma_apply_ext(source, ext),
            };
            return self.inferable(at, ext);
        }
        match self.mode {
            Mode::Ext => {
                let mut args = vec![var(B, span), var(G2, span)];
                args.extend(self.args(ext));
                args.push(hyp.clone());
                app(self.cref(&body_name(&self.decl.name)), args, span)
            }
            Mode::Unfold => self.sigma_apply_ext(self.source, ext),
        }
    }

    /// A piece of `f#body`'s body at one anchor: `__dec_k`, `__dec_ih` and
    /// `__dec_h` replaced by what that anchor applies `f#body` to. For
    /// `f_unfold`'s left anchor `f#rec(Succ(e), x̄, p)` that is the measure,
    /// the recursor at it, and `p`; for `f#ext` it is `a, g1, h1` on the left
    /// and `b, g2, h2` on the right.
    fn instantiate(&self, rewritten: &Expr, hyp: &Expr, right: bool) -> Expr {
        let span = self.span;
        let (k, ih) = match self.mode {
            Mode::Ext if right => (var(B, span), var(G2, span)),
            Mode::Ext => (var(A, span), var(G1, span)),
            // The recursor at the bound, applied to nothing more: every use
            // of `__dec_ih` in the rewritten body is a call, so this is
            // `f#rec(e, ȳ, p)` at each, with no λ to annotate.
            Mode::Unfold => (
                self.rw.measure.clone(),
                app(self.cref(&rec_name(&self.decl.name)), vec![self.rw.measure.clone()], span),
            ),
        };
        subst(rewritten, &[(K, &k), (IH, &ih), (H, hyp)], &mut Vec::new())
    }

    /// An arm body standing as an anchor sits on one side of the motive's
    /// `=`, an inference position: a plain `match` there is given the
    /// constant motive at the result type it is checked against in the arm.
    fn inferable(&self, e: Expr, ext: Option<(&str, &Expr)>) -> Expr {
        let span = self.span;
        let mut e = e;
        if let ExprKind::Match { motive: motive @ None, .. } = &mut e.kind {
            let mut ty = self.sigma_apply_ty(&self.decl.result);
            if let Some((v, pat)) = ext {
                ty = subst_surface_ty(&ty, v, pat);
            }
            *motive = Some(Box::new(lam(&["_"], ty_lit(ty, span), span)));
        }
        e
    }

    fn sigma_apply_ty(&self, ty: &Ty) -> Ty {
        let mut out = ty.clone();
        for (v, pat) in &self.sigma {
            out = subst_surface_ty(&out, v, pat);
        }
        out
    }

    /// The generalized bound hypotheses at measure `m`, in `hyps` order.
    fn hyp_binders(&self, m: &Expr) -> Vec<(&'static str, Ty)> {
        let span = self.span;
        match self.mode {
            Mode::Ext => vec![
                (H1, lt_ty(m.clone(), succ(var(A, span), span), span)),
                (H2, lt_ty(m.clone(), succ(var(B, span), span), span)),
            ],
            Mode::Unfold => vec![(P, lt_ty(m.clone(), succ(m.clone(), span), span))],
        }
    }

    fn goal(&self, ext: Option<(&str, &Expr)>, hyps: &[Expr]) -> Ty {
        eq_ty(
            self.anchor_l(ext, &hyps[0]),
            self.anchor_r(ext, hyps.last().expect("a hypothesis per side")),
            self.span,
        )
    }

    fn fresh(&mut self, stem: &str) -> String {
        self.fresh += 1;
        format!("__dec_{stem}{}", self.fresh)
    }

    fn has_self_call(&self, e: &Expr) -> bool {
        let mut found = false;
        crate::surface::walk_expr(e, &mut |x| {
            if let ExprKind::App { head, .. } = &x.kind {
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if n == self.rw.name) {
                    found = true;
                }
            }
        });
        found
    }

    /// A block's `let`s substituted into its result (§3: `let` is
    /// zeta-transparent, so both sides still reduce alike), outermost first,
    /// each right-hand side under the substitutions before it.
    ///
    /// A claimed method call on a `let mut` local (`x.m(a);` at a `#seq`
    /// name, or `let p = x.m(a);`, [`heather_syntax::MUTATED`]) also rebinds
    /// its receiver (`statements::elaborate_mut_call`): from there on `x` is
    /// `\0mutated_after(x.m(a))` and `p` is `\0mutated_value(x.m(a))`, which
    /// the elaborator reads as the statement does. Dropping the statement as
    /// a `let` nothing reads would leave `x` the value before the call
    /// (issues/decreases-mut-call-statement-companions.md).
    ///
    /// Those rebindings are spelled as plain `let`s ([`explicit_rebinds`])
    /// in this block and in every block below it *before* anything is
    /// substituted: a claimed call names its receiver as a place, and a
    /// substitution from an enclosing block (`let x = c.total();` before the
    /// branch, which rebinds `c`) would otherwise put a value where the
    /// place was, and reach past the statement's rebinding into the uses
    /// after it (issues/runtime-mut-self-let-read-walk.md).
    fn inline_lets(&self, stmts: &[Stmt], result: &Expr) -> Result<Expr, String> {
        let mut env: Vec<(String, Expr)> = Vec::new();
        let apply = |env: &[(String, Expr)], e: &Expr| {
            let map: Vec<(&str, &Expr)> = env.iter().map(|(n, v)| (n.as_str(), v)).collect();
            subst_shared(&explicit_rebinds(e), &map)
        };
        for st in rebind_marked(stmts, self.span, true)? {
            let Stmt::Let { name, expr, .. } = &st else {
                return Err("a destructuring or `code` binding in the body".into());
            };
            if self.has_self_call(expr) {
                return Err("a recursive call in a `let` right-hand side".into());
            }
            let value = apply(&env, expr);
            match env.iter_mut().find(|(n, _)| n == name) {
                Some(slot) => slot.1 = value,
                None => env.push((name.clone(), value)),
            }
        }
        Ok(apply(&env, result))
    }

    /// The walk proper. `at` says what the current position is (see [`At`]):
    /// only at the anchor can a `match` be re-matched under a motive that
    /// mentions the anchors.
    fn walk(&mut self, e: &Expr, at: At) -> Result<Triple, String> {
        let span = self.span;
        if !self.has_self_call(e) {
            let x = self.sigma_apply(e);
            return Ok(Triple {
                lhs: x.clone(),
                rhs: x,
                proof: Expr {
                    kind: ExprKind::Refl,
                    span,
                },
            });
        }
        match &e.kind {
            // §3: a `let` whose right-hand side holds no self-call is
            // substituted — `let` is zeta-transparent, so the two sides still
            // reduce alike.
            //
            // It is substituted through `let_env`, so the terms this walk builds
            // read its value, while the walk itself goes on over the body as
            // written, with the `let` in the rewrite's scope as `f#body` has
            // it: a test after it, its alias and its equation are then the
            // ones `f#body` binds, and an obligation re-emitted below selects
            // the same hypotheses (issues/runtime-mut-self-let-read-walk.md).
            // A claimed `mut self` call rebinds its receiver by a `let` of its
            // own ([`rebind_marked`]); the rewrite's scope has the statement
            // as `f#body` does.
            ExprKind::Block(b) => {
                if !b.ons.is_empty() {
                    return Err("a nested `on` block".into());
                }
                let (scope_n, env_n) = (self.rw.scope.len(), self.let_env.len());
                let mut out = Ok(());
                for st in &b.stmts {
                    let Stmt::Let { name, ty, expr, opaque, .. } = st else {
                        out = Err("a destructuring or `code` binding in the body".to_string());
                        break;
                    };
                    if self.has_self_call(expr) {
                        out = Err("a recursive call in a `let` right-hand side".to_string());
                        break;
                    }
                    let plain = match rebind_marked(std::slice::from_ref(st), span, true) {
                        Ok(plain) => plain,
                        Err(e) => {
                            out = Err(e);
                            break;
                        }
                    };
                    let values: Vec<(String, Expr)> = plain
                        .iter()
                        .filter_map(|p| match p {
                            Stmt::Let { name, expr, .. } => Some((name.clone(), self.let_apply(expr))),
                            _ => None,
                        })
                        .collect();
                    let binder = self.rw.let_binder(name, ty, expr, *opaque);
                    self.rw.scope.push(binder);
                    let after = self.rw.scope.len();
                    // Each value is read before the statement's own
                    // rebindings: `let p = value(x.m(a)); let x = after(x.m(a))`.
                    self.let_env.extend(values.into_iter().map(|(n, v)| (n, v, after)));
                }
                let r = out.and_then(|()| self.walk(&b.result, at));
                self.rw.scope.truncate(scope_n);
                self.let_env.truncate(env_n);
                r
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                ..
            } => {
                if !named.is_empty() {
                    return Err("named arguments around a recursive call".into());
                }
                let callee = match &head.kind {
                    ExprKind::TyApp { head, .. } => &head.kind,
                    other => other,
                };
                if matches!(callee, ExprKind::Var(n) if n == self.rw.name) {
                    return self.leaf(args, *explicit);
                }
                if self.has_self_call(head) {
                    return Err("a recursive call in a callee position".into());
                }
                let head_s = self.sigma_apply(head);
                let mut parts = Vec::new();
                for a in args {
                    parts.push((self.has_self_call(a), self.walk(a, At::Argument)?));
                }
                let lhs = app(
                    head_s.clone(),
                    parts.iter().map(|(_, t)| t.lhs.clone()).collect(),
                    span,
                );
                let rhs = app(
                    head_s.clone(),
                    parts.iter().map(|(_, t)| t.rhs.clone()).collect(),
                    span,
                );
                // One `j` per changed argument (§3), rewriting the argument
                // list left to right from the left rendering to the right.
                let mut cur: Vec<Expr> = parts.iter().map(|(_, t)| t.lhs.clone()).collect();
                let mut proof = Expr {
                    kind: ExprKind::Refl,
                    span,
                };
                for (i, (changed, t)) in parts.iter().enumerate() {
                    if !changed {
                        continue;
                    }
                    let y = self.fresh("y");
                    let mut at_y = cur.clone();
                    at_y[i] = var(&y, span);
                    let motive = lam(
                        &[&y, "__dec_q"],
                        eq_expr(lhs.clone(), app(head_s.clone(), at_y, span), span),
                        span,
                    );
                    proof = Expr {
                        kind: ExprKind::J {
                            proof: Box::new(t.proof.clone()),
                            motive: Box::new(motive),
                            case: Box::new(proof),
                        },
                        span,
                    };
                    cur[i] = t.rhs.clone();
                }
                Ok(Triple { lhs, rhs, proof })
            }
            ExprKind::Match {
                form,
                scrut,
                eqbind,
                motive,
                arms,
                ..
            } => {
                if at == At::Argument {
                    return Err("a `match` holding a recursive call inside an argument".into());
                }
                // An `if` is the match on its decision (`MatchForm::If`
                // survives for diagnostics only), so it is walked as one.
                if !matches!(form, MatchForm::Match | MatchForm::If) {
                    return Err("a `split` or `if let` around a recursive call".into());
                }
                if motive.is_some() {
                    return Err("a `match` with a written motive".into());
                }
                if at == At::Result {
                    return self.match_below_anchor(e, *form, scrut, eqbind.as_deref(), arms);
                }
                // A computed scrutinee, or an equation binding: neither side
                // reduces into an arm, so both are spelled out (§3's
                // amendment; issues/decreases-unfold-convoy-scrutinee.md).
                // A computed scrutinee with no equation written goes through
                // the alias the rewrite gave it, which carries its
                // [`AutoEqs`] equation where an obligation reads one.
                // A `let`'s variable is its value, so a match on it is on a
                // computed scrutinee too.
                let let_var = matches!(&scrut.kind, ExprKind::Var(v)
                    if (0..self.let_env.len()).any(|i| &self.let_env[i].0 == v && self.let_visible(i)));
                if eqbind.is_none() && (let_var || !matches!(scrut.kind, ExprKind::Var(_))) && !self.has_self_call(scrut) {
                    return self.convoy_at_anchor(e, *form, scrut, None, arms);
                }
                if eqbind.is_some() || !matches!(scrut.kind, ExprKind::Var(_)) {
                    return self.match_spelled(e, scrut, eqbind.as_deref(), arms);
                }
                let ExprKind::Var(v) = &scrut.kind else {
                    return self.convoy_at_anchor(e, *form, scrut, eqbind.as_deref(), arms);
                };
                if eqbind.is_some() {
                    return self.convoy_at_anchor(e, *form, scrut, eqbind.as_deref(), arms);
                }
                if self.sigma.iter().any(|(n, _)| n == v) {
                    return Err("a second `match` on an already-refined variable".into());
                }
                self.match_at_anchor(v, arms)
            }
            // §3: a self-call under a `λ` is funext again, and refused.
            ExprKind::Lam { .. } => {
                Err("a recursive call under a `λ`, which is functional extensionality".into())
            }
            _ => Err("a body shape the walk does not cover".into()),
        }
    }

    /// A `match` below the anchor, as an arm of a match both sides spell out
    /// (issues/decreases-no-companions-nested-match-calls.md): `match flip
    /// { … }` under `match h: i < n { True => … }`. Neither anchor reaches
    /// it, but none needs to: [`Self::match_spelled`] is congruence alone,
    /// each side the match again over its arms' renderings, at the
    /// declaration's result type.
    ///
    /// It has to be spelled as `f#body` spells it, so the two cases where the
    /// body rewrite gives the match an equation binding the source lacks are
    /// refused: a variable the (refined) measure mentions, which the rewrite
    /// refines, and a computed scrutinee whose [`AutoEqs`] equation a lifted
    /// obligation reads.
    fn match_below_anchor(
        &mut self,
        node: &Expr,
        form: MatchForm,
        scrut: &Expr,
        eqbind: Option<&str>,
        arms: &[Arm],
    ) -> Result<Triple, String> {
        if eqbind.is_none() && matches!(form, MatchForm::Match | MatchForm::If) {
            if matches!(scrut.kind, ExprKind::Var(_)) {
                if self.rw.refining_match(scrut, &None).is_some() {
                    return Err("a `match` below another `match`'s arm on a variable the measure mentions".into());
                }
            } else if self.rw.scrut_ty(scrut).is_some() && arms.iter().any(|a| self.rw.calls_member(&a.body)) {
                // The rewrite numbers this candidate as it renders it: a
                // scrutinee it gives an alias (one whose type it can write),
                // with an arm that recurses (`Rewrite::auto_candidate`).
                let n = self.rw.auto_n;
                self.rw.auto_n += 1;
                if self.rw.auto_eqs.admits(n) {
                    // `f#body` binds the scrutinee's equation where the
                    // source binds none (issues/measured-loop-inner-if-companions.md):
                    // each side spells its own, `f_unfold`'s right side the
                    // source's, without.
                    let meq = format!("__dec_meq{n}");
                    let eq_r = match self.mode {
                        Mode::Ext => Some(meq.as_str()),
                        Mode::Unfold => None,
                    };
                    return self.match_spelled_eqs(node, scrut, Some(&meq), eq_r, arms);
                }
            }
        }
        self.match_spelled(node, scrut, eqbind, arms)
    }

    /// A `match` at the anchor that neither side reduces into: on a computed
    /// scrutinee `c` (which `f#body` binds to a `let` alias, as the rewrite
    /// does), or with an equation binding `h` (a convoy). Both sides are the
    /// same match with their own arms, so the proof is the match once more,
    /// at a motive spelling both, with the scrutinee generalized:
    ///
    /// `(match c as λ s => (e: c = s) → L(s, e) = R(s, e) { C => λ h => p_C })(refl)`
    ///
    /// for a convoy, where `L(s, e)` is `(match s as λ b => (c = b) → T
    /// { C => λ h => l_C })(e)` and `R` likewise, `l_C`/`r_C`/`p_C` the arm's
    /// walk; without an equation binding, the plain match at `λ s => L(s) =
    /// R(s)`. At `s := c, e := refl` the two sides are `f#body`'s convoy and
    /// the source's, by conversion. Each arm's `let`s (convoy equations at
    /// `refl`, obligations) are repeated around its renderings, since the
    /// motive sits outside the arm.
    fn match_spelled(&mut self, whole: &Expr, scrut: &Expr, eqbind: Option<&str>, arms: &[Arm]) -> Result<Triple, String> {
        self.match_spelled_eqs(whole, scrut, eqbind, eqbind, arms)
    }

    /// [`Self::match_spelled`] with each side's own equation binding: the
    /// left side's (`f#body`'s) may bind one the right side's (the source's)
    /// does not. The proof's arms take the equation where either side does.
    fn match_spelled_eqs(
        &mut self,
        whole: &Expr,
        scrut: &Expr,
        eq_l: Option<&str>,
        eq_r: Option<&str>,
        arms: &[Arm],
    ) -> Result<Triple, String> {
        let span = self.span;
        let eqbind = eq_l.or(eq_r);
        if self.has_self_call(scrut) {
            return Err("a recursive call in a `match` scrutinee".into());
        }
        let c = self.sigma_apply(scrut);
        // The rewrite's own alias for a computed scrutinee, named and typed as
        // `Rewrite::expr` names it, so that obligations below lift over the
        // binders `f#body`'s lifted over.
        let scrut_ty = self.rw.match_scrut_ty(scrut, arms);
        let depth0 = self.rw.scope.len();
        // As there, a scrutinee whose type the walk cannot write keeps no
        // alias.
        let alias = if let (false, Some(ty)) = (matches!(scrut.kind, ExprKind::Var(_)), scrut_ty.clone()) {
            let mut name = format!("__dec_scrut_{}", scrut.span.start);
            while self.rw.scope.iter().any(|b| b.name == name)
                || mentions_context(whole, &name)
                || self.rw.ons.iter().any(|o| mentions_context(&o.expr, &name))
            { name.push('_'); }
            self.rw.scope.push(Binder { name: name.clone(), ty: Some(ty), value: Some(scrut.clone()) });
            Some(name)
        } else {
            None
        };
        let mut walked = Vec::new();
        for a in arms {
            if a.default {
                self.rw.scope.truncate(depth0);
                return Err("a `_` arm around a recursive call".into());
            }
            let saved = std::mem::take(&mut self.lets);
            let depth = self.rw.scope.len();
            self.rw.bind_arm(a, scrut_ty.as_ref());
            if let Some(eq) = eqbind {
                // About the scrutinee itself, as `Rewrite::expr` states it.
                let ty = pattern_expr(a, span).map(|p| eq_ty((*scrut).clone(), p, span));
                self.rw.scope.push(Binder { name: eq.to_string(), ty, value: None });
            }
            let inner = self.walk(&a.body, At::Result);
            self.rw.scope.truncate(depth);
            let stmts = std::mem::replace(&mut self.lets, saved);
            let inner = match inner {
                Ok(t) => t,
                Err(why) => {
                    self.rw.scope.truncate(depth0);
                    return Err(why);
                }
            };
            walked.push((a, stmts, inner));
        }
        self.rw.scope.truncate(depth0);
        let s = self.fresh("s");
        let sv = var(&s, span);
        let e_name = self.fresh("e");
        let b = self.fresh("b");
        let result_ty = self.sigma_apply_ty(&self.decl.result);
        let with_eq = |body: Expr, eq: Option<&str>| match eq {
            Some(h) => lam(&[h], body, span),
            None => body,
        };
        // One side's match at scrutinee `at`, its convoy applied to `proof`,
        // binding the equation `eqbind` names.
        let side = |pick: &dyn Fn(&Triple) -> Expr, at: Expr, proof: Option<Expr>, eqbind: Option<&str>| {
            let proof = eqbind.and(proof);
            let arms_out: Vec<Arm> = walked.iter().map(|(a, stmts, t)| {
                // The arm's `let`s travel with its rendering (zeta-transparent,
                // and typed, which a bare `refl` substituted in would not be).
                // A side that binds no equation where the other does is the
                // source's, which names none of them: they may read the
                // equation it does not bind.
                let unread = eqbind.is_none()
                    && eq_l.or(eq_r).is_some()
                    && !stmts.iter().any(|st| matches!(st, Stmt::Let { name, .. } if mentions_context(&pick(t), name)));
                let x = if stmts.is_empty() || unread {
                    pick(t)
                } else {
                    Expr {
                        kind: ExprKind::Block(Box::new(Block { stmts: stmts.clone(), result: Box::new(pick(t)), ons: Vec::new(), span })),
                        span,
                    }
                };
                Arm { ctor: a.ctor.clone(), default: false, binders: a.binders.clone(), body: with_eq(x, eqbind), span: a.span }
            }).collect();
            let motive_body = match eqbind {
                Some(_) => arrow(None, eq_ty(c.clone(), var(&b, span), span), result_ty.clone(), span),
                None => result_ty.clone(),
            };
            let m = Expr {
                kind: ExprKind::Match {
                    form: MatchForm::Match,
                    generated: false,
                    scrut: Box::new(at),
                    eqbind: None,
                    motive: Some(Box::new(lam(&[&b], ty_lit(motive_body, span), span))),
                    arms: arms_out,
                },
                span,
            };
            match proof { Some(p) => app(m, vec![p], span), None => m }
        };
        let e_arg = eqbind.map(|_| var(&e_name, span));
        let l = side(&|t: &Triple| t.lhs.clone(), sv.clone(), e_arg.clone(), eq_l);
        let r = side(&|t: &Triple| t.rhs.clone(), sv.clone(), e_arg.clone(), eq_r);
        let goal = match eqbind {
            Some(_) => arrow(Some(e_name.clone()), eq_ty(c.clone(), sv.clone(), span), eq_ty(l, r, span), span),
            None => eq_ty(l, r, span),
        };
        let proof_arms: Vec<Arm> = walked.iter().map(|(a, stmts, t)| {
            let proof = Expr {
                kind: ExprKind::Block(Box::new(Block { stmts: stmts.clone(), result: Box::new(t.proof.clone()), ons: Vec::new(), span })),
                span,
            };
            Arm { ctor: a.ctor.clone(), default: false, binders: a.binders.clone(), body: with_eq(proof, eqbind), span: a.span }
        }).collect();
        let proof_match = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(c.clone()),
                eqbind: None,
                motive: Some(Box::new(lam(&[&s], ty_lit(goal, span), span))),
                arms: proof_arms,
            },
            span,
        };
        let refl = Expr { kind: ExprKind::Refl, span };
        let proof = match eqbind {
            Some(_) => app(proof_match, vec![refl.clone()], span),
            None => proof_match,
        };
        let refl_arg = eqbind.map(|_| refl.clone());
        Ok(Triple {
            lhs: side(&|t: &Triple| t.lhs.clone(), c.clone(), refl_arg.clone(), eq_l),
            rhs: side(&|t: &Triple| t.rhs.clone(), c.clone(), refl_arg, eq_r),
            proof,
        })
    }

    /// A `match` at the anchor: re-matched under the motive
    /// `λ s => lhs(s) = rhs(s)`, with the bound hypotheses generalized into it
    /// wherever the measure mentions the scrutinee (§3, probed).
    fn match_at_anchor(&mut self, v: &str, arms: &[Arm]) -> Result<Triple, String> {
        let span = self.span;
        let s = self.fresh("s");
        let sv = var(&s, span);
        let ext = Some((v, &sv));
        let m_at_s = self.measure_at(ext);
        let generalize = mentions(&m_at_s, &s);
        let in_arm = self.anchors.as_ref().is_some_and(|(l, r)| mentions(l, v) || mentions(r, v));
        if !generalize && !in_arm && !self.args(ext).iter().any(|a| mentions(a, &s)) {
            return Err(
                "a `match` on a variable neither the measure nor an argument mentions".into(),
            );
        }
        let hyp_names: Vec<&str> = self.hyp_binders(&m_at_s).iter().map(|(n, _)| *n).collect();
        let goal = if generalize {
            let hyps: Vec<Expr> = hyp_names.iter().map(|n| var(n, span)).collect();
            pi(self.hyp_binders(&m_at_s), self.goal(ext, &hyps), span)
        } else {
            self.goal(ext, &self.hyps.clone())
        };
        let motive = lam(&[&s], ty_lit(goal, span), span);
        // The rewrite's own bookkeeping, so that the obligations below are
        // numbered and transported exactly as `f#body` numbered and
        // transported them.
        let eq = self.rw.refining_match(&var(v, span), &None);
        if eq.is_some() {
            self.rw.eqs += 1;
        }
        let outer_hyps = self.hyps.clone();
        let mut out = Vec::new();
        for a in arms {
            if a.default {
                return Err("a `_` arm around a recursive call".into());
            }
            let Some(pat) = pattern_expr(a, span) else {
                return Err("an arm whose pattern has no expression form".into());
            };
            if let Some(eq) = &eq {
                self.rw
                    .refinements
                    .push((v.to_string(), pat.clone(), eq.clone()));
            }
            self.sigma.push((v.to_string(), pat));
            if generalize {
                self.hyps = hyp_names.iter().map(|n| var(n, span)).collect();
            }
            let saved = std::mem::take(&mut self.lets);
            // The arm's binders, typed as the body's own walk types them, so
            // that a leaf below lifts its obligation over the same binders.
            let depth = self.rw.scope.len();
            let scrut_ty = self.rw.scrut_ty(&var(v, span));
            self.rw.bind_arm(a, scrut_ty.as_ref());
            let inner = self.walk(&a.body, At::Anchor);
            self.rw.scope.truncate(depth);
            let stmts = std::mem::replace(&mut self.lets, saved);
            self.sigma.pop();
            if eq.is_some() {
                self.rw.refinements.pop();
            }
            self.hyps = outer_hyps.clone();
            let inner = inner?;
            // The convoy equation at this arm's pattern, bound to `refl` (§5).
            // Spelled as a `let` so the obligations below reach it by the same
            // name `f#body`'s body uses, and reduce to the same term.
            let proof = Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(inner.proof),
                    ons: Vec::new(),
                    span,
                })),
                span,
            };
            out.push(Arm {
                ctor: a.ctor.clone(),
                default: false,
                binders: a.binders.clone(),
                body: if generalize {
                    lam(&hyp_names, proof, span)
                } else {
                    proof
                },
                span: a.span,
            });
        }
        let matched = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(var(v, span)),
                eqbind: None,
                motive: Some(Box::new(motive)),
                arms: out,
            },
            span,
        };
        let proof = if generalize {
            app(matched, outer_hyps.clone(), span)
        } else {
            matched
        };
        Ok(Triple {
            lhs: self.anchor_l(None, &outer_hyps[0]),
            rhs: self.anchor_r(None, outer_hyps.last().expect("a hypothesis")),
            proof,
        })
    }

    /// A `match` at the anchor whose scrutinee is computed, or which binds its
    /// equation (docs/language/matching/dependent-match-compiler-design.md §8). Neither anchor
    /// reduces into an arm, because the scrutinee is stuck, so both sides
    /// are spelled out as the match itself at a fresh scrutinee `s`, and the
    /// match is re-matched on `s`:
    ///
    /// ```text
    /// (match e as λ s => (q: e = s) → L(s, q) = R(s, q) {
    ///     C(x̄) => λ h => ⟨the arm's walk, its anchors the two arm bodies⟩
    /// })(refl)
    /// ```
    ///
    /// `L(s, q)` is `f#body`'s own spelling of the match (a fork of the
    /// rewrite renders it) at the anchor's arguments, convoyed at `s` and
    /// applied to `q`; `R(s, q)` is the source's. At `s := e, q := refl` each
    /// is its side's match again, and at `C(x̄)` each steps to its arm. A match
    /// with no equation binding is the same without `q`.
    fn convoy_at_anchor(
        &mut self,
        node: &Expr,
        form: MatchForm,
        scrut: &Expr,
        eq: Option<&str>,
        arms: &[Arm],
    ) -> Result<Triple, String> {
        let span = self.span;
        if arms.iter().any(|a| a.default) {
            return Err("a `_` arm around a recursive call".into());
        }
        // `f#body`'s spelling of this match, with its `__dec_scrut_N` let (if
        // any) substituted back: the let is an alias, so the match is on the
        // expression either way.
        let rendered = self.rw.fork().expr(node);
        let rendered = match &rendered.kind {
            ExprKind::Block(b) if b.ons.is_empty() => self.inline_lets(&b.stmts, &b.result)?,
            _ => rendered,
        };
        let ExprKind::Match { scrut: r_scrut, arms: r_arms, eqbind: r_eq, .. } = &rendered.kind else {
            return Err("a rendered `match` this walk cannot read".into());
        };
        // `f#body`'s spelling may bind an equation the source does not (an
        // [`AutoEqs`] candidate a lifted obligation reads): each side's
        // convoy carries its own, and the proof generalizes over `q` when
        // either does.
        let eq_l: Option<String> = r_eq.clone();
        let eq_r: Option<String> = match self.mode {
            Mode::Ext => eq_l.clone(),
            Mode::Unfold => eq.map(str::to_string),
        };
        let eq_any: Option<String> = eq_l.clone().or_else(|| eq_r.clone());
        if r_arms.len() != arms.len() {
            return Err("a rendered `match` this walk cannot read".into());
        }
        // The enclosing refinements' equations, which the rendered spelling
        // still names: bound to `refl` at their patterns, as a leaf binds them
        // (§5 of the unfolding note), by `let`s around this proof, so that the
        // motive below can mention them too.
        let mut eq_map: Vec<(String, Expr)> = Vec::new();
        for (_, pat, eq_name) in self.rw.refinements.clone() {
            let at = self.sigma_apply(&pat);
            let name = self.fresh("eq");
            self.lets.push(Stmt::Let {
                name: name.clone(),
                ty: Some(eq_ty(at.clone(), at, span)),
                expr: Expr { kind: ExprKind::Refl, span },
                span,
                opaque: false,
            });
            eq_map.push((eq_name, var(&name, span)));
        }
        let rebind = |e: &Expr| {
            let map: Vec<(&str, &Expr)> = eq_map.iter().map(|(n, v)| (n.as_str(), v)).collect();
            subst(e, &map, &mut Vec::new())
        };
        let result_ty = self.sigma_apply_ty(&self.decl.result);
        let hyp_l = self.hyps[0].clone();
        let hyp_r = self.hyps.last().expect("a hypothesis per side").clone();
        let e_src = self.sigma_apply(scrut);
        let e_rw = rebind(&self.sigma_apply(r_scrut));
        let z = self.fresh("z");
        // `(match s as λ z => (e = z) → T { C(x̄) => λ h => b })(q)`, or the
        // same without the equation.
        let conv = |on: &Expr, e: &Expr, bodies: Vec<Expr>, eq: Option<&str>, q: Option<&Expr>| {
            let q = eq.and(q);
            let motive_ty = match eq {
                Some(_) => arrow(None, eq_ty(e.clone(), var(&z, span), span), result_ty.clone(), span),
                None => result_ty.clone(),
            };
            let conv_arms = arms
                .iter()
                .zip(bodies)
                .map(|(a, b)| Arm {
                    ctor: a.ctor.clone(),
                    default: false,
                    binders: a.binders.clone(),
                    body: match eq {
                        Some(h) => lam(&[h], b, span),
                        None => b,
                    },
                    span: a.span,
                })
                .collect();
            let m = Expr {
                kind: ExprKind::Match {
                    form: MatchForm::Match,
                    generated: false,
                    scrut: Box::new(on.clone()),
                    eqbind: None,
                    motive: Some(Box::new(lam(&[&z], ty_lit(motive_ty, span), span))),
                    arms: conv_arms,
                },
                span,
            };
            match q {
                Some(q) => app(m, vec![q.clone()], span),
                None => m,
            }
        };
        let l_bodies: Vec<Expr> = r_arms
            .iter()
            .map(|a| rebind(&self.sigma_apply(&self.instantiate(&a.body, &hyp_l, false))))
            .collect();
        let r_bodies: Vec<Expr> = match self.mode {
            Mode::Ext => r_arms
                .iter()
                .map(|a| rebind(&self.sigma_apply(&self.instantiate(&a.body, &hyp_r, true))))
                .collect(),
            Mode::Unfold => arms.iter().map(|a| self.sigma_apply(&a.body)).collect(),
        };
        let s = self.fresh("s");
        let q = self.fresh("q");
        let (sv, qv) = (var(&s, span), var(&q, span));
        let qa = eq_any.as_ref().map(|_| &qv);
        let goal = eq_ty(
            conv(&sv, &e_rw, l_bodies, eq_l.as_deref(), qa),
            conv(&sv, &e_src, r_bodies, eq_r.as_deref(), qa),
            span,
        );
        let goal = match &eq_any {
            Some(_) => arrow(Some(q.clone()), eq_ty(e_src.clone(), sv.clone(), span), goal, span),
            None => goal,
        };
        let motive = lam(&[&s], ty_lit(goal, span), span);
        // The rewrite's bookkeeping, as its own `match` arm keeps it: the
        // alias, then per arm the pattern's binders and the equation.
        let depth = self.rw.scope.len();
        if !matches!(scrut.kind, ExprKind::Var(_))
            && let Some(alias) = self.rw.bind_scrut_alias(node, scrut)
            && self.rw.auto_candidate(form, &var(&alias, span), &eq.map(str::to_string), arms)
        {
            // The rewrite numbered this candidate as it rendered it; keep
            // the nested ones' numbers in step.
            self.rw.auto_n += 1;
        }
        let scrut_ty = self.rw.match_scrut_ty(scrut, arms);
        let stated = match &scrut.kind {
            ExprKind::Var(v) => self.rw.scrut_aliases.iter().rev()
                .find(|(n, _)| n == v).map(|(_, e)| e.clone()),
            _ => None,
        }
        .unwrap_or_else(|| scrut.clone());
        let mut out = Vec::new();
        for (a, ra) in arms.iter().zip(r_arms) {
            let arm_depth = self.rw.scope.len();
            self.rw.bind_arm(a, scrut_ty.as_ref());
            if let Some(h) = &eq_any {
                let ty = pattern_expr(a, span).map(|p| eq_ty(stated.clone(), p, span));
                self.rw.scope.push(Binder { name: h.to_string(), ty, value: None });
            }
            let saved_lets = std::mem::take(&mut self.lets);
            let saved_anchors = self.anchors.replace((rebind(&ra.body), a.body.clone()));
            let inner = self.walk(&a.body, At::Anchor);
            self.anchors = saved_anchors;
            let stmts = std::mem::replace(&mut self.lets, saved_lets);
            self.rw.scope.truncate(arm_depth);
            let inner = inner?;
            let proof = Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(inner.proof),
                    ons: Vec::new(),
                    span,
                })),
                span,
            };
            out.push(Arm {
                ctor: a.ctor.clone(),
                default: false,
                binders: a.binders.clone(),
                body: match &eq_any {
                    Some(h) => lam(&[h], proof, span),
                    None => proof,
                },
                span: a.span,
            });
        }
        self.rw.scope.truncate(depth);
        let matched = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(e_src.clone()),
                eqbind: None,
                motive: Some(Box::new(motive)),
                arms: out,
            },
            span,
        };
        let proof = match &eq_any {
            Some(_) => app(matched, vec![Expr { kind: ExprKind::Refl, span }], span),
            None => matched,
        };
        Ok(Triple {
            lhs: self.anchor_l(None, &hyp_l),
            rhs: self.anchor_r(None, &hyp_r),
            proof,
        })
    }

    /// A self-call site: the leaf of the congruence (§3's table). Both sides
    /// need the *same* obligation proof, so it is bound once (§4).
    fn leaf(&mut self, args: &[Expr], explicit: bool) -> Result<Triple, String> {
        let span = self.span;
        if args.len() != self.rw.params.len() {
            return Err("an unsaturated recursive call".into());
        }
        if !explicit && self.rw.params.iter().any(|p| p.implicit) {
            return Err("a recursive call that does not pass its implicit parameters".into());
        }
        for a in args {
            if self.has_self_call(a) {
                return Err("a recursive call inside another recursive call's arguments".into());
            }
        }
        let map: Vec<(&str, &Expr)> = self
            .rw
            .params
            .iter()
            .map(|p| p.name.as_str())
            .zip(args)
            .collect();
        // `e[ȳ]` — built from the *unsubstituted* measure, then pushed through
        // the enclosing arms' patterns, so it reads as the rewritten body's
        // own copy does.
        let at_args = self.sigma_apply(&subst(self.rw.measure, &map, &mut Vec::new()));
        // The obligation is the site's lifted `f#obl_N` (§4), so the term
        // below and the body's are the same one — which is what an
        // `omega`-defaulted obligation needs, `omega` being a function of its
        // context and not of the goal alone.
        let mut acc = self
            .rw
            .obligation(&subst(self.rw.measure, &map, &mut Vec::new()), None, span, None);
        if !self.rw.obls.last().is_some_and(Option::is_some) {
            return Err(
                "a recursive call whose obligation cannot be lifted into a declaration \
                 of its own: its statement names a binder this generator cannot type"
                    .into(),
            );
        }
        // The convoy equations at their arms' patterns, bound to `refl` (§5)
        // **here** and not at the arm: only at the leaf is every enclosing
        // pattern substituted, and `Succ(k)` two arms up is `Succ(Succ(l))`
        // by the time the innermost arm binds `l`.
        for (_, pat, eq) in self.rw.refinements.clone() {
            let at = self.sigma_apply(&pat);
            let name = self.fresh("eq");
            self.lets.push(Stmt::Let {
                name: name.clone(),
                ty: Some(eq_ty(at.clone(), at, span)),
                expr: Expr {
                    kind: ExprKind::Refl,
                    span,
                },
                span,
                opaque: false,
            });
            acc = subst(&acc, &[(eq.as_str(), &var(&name, span))], &mut Vec::new());
        }
        let acc = self.sigma_apply(&acc);
        let m = self.measure_at(None);
        let name = self.fresh("o");
        self.lets.push(Stmt::Let {
            name: name.clone(),
            ty: Some(lt_ty(at_args.clone(), m.clone(), span)),
            expr: acc,
            span,
            opaque: false,
        });
        let ys: Vec<Expr> = args.iter().map(|a| self.sigma_apply(a)).collect();
        let trans = |bound: Expr, hyp: Expr| {
            app(
                var("nat::Nat::le_trans", span),
                vec![
                    succ(at_args.clone(), span),
                    m.clone(),
                    bound,
                    var(&name, span),
                    hyp,
                ],
                span,
            )
        };
        match self.mode {
            Mode::Ext => {
                let q1 = trans(var(A, span), self.hyps[0].clone());
                let q2 = trans(var(B, span), self.hyps[1].clone());
                let mut l = ys.clone();
                l.push(q1.clone());
                let mut r = ys.clone();
                r.push(q2.clone());
                let mut p = ys.clone();
                p.push(q1);
                p.push(q2);
                Ok(Triple {
                    lhs: app(var(G1, span), l, span),
                    rhs: app(var(G2, span), r, span),
                    proof: app(var(HG, span), p, span),
                })
            }
            Mode::Unfold => {
                let q = trans(m.clone(), self.hyps[0].clone());
                let mut l = vec![m.clone()];
                l.extend(ys.iter().cloned());
                l.push(q.clone());
                let mut irrel = vec![m.clone(), succ(at_args.clone(), span)];
                irrel.extend(ys.iter().cloned());
                irrel.push(q);
                irrel.push(app(
                    var("nat::Nat::lt_succ_self", span),
                    vec![at_args.clone()],
                    span,
                ));
                // The right-hand side is the call **as written** (§5).
                let mut rhs_args = ys;
                let head = self.cref(&self.decl.name);
                Ok(Triple {
                    lhs: app(self.cref(&rec_name(&self.decl.name)), l, span),
                    rhs: Expr {
                        kind: ExprKind::App {
                            head: Box::new(head),
                            args: std::mem::take(&mut rhs_args),
                            named: Vec::new(),
                            explicit,
                            goal_oriented: false,
                        },
                        span,
                    },
                    proof: app(self.cref(&irrel_name(&self.decl.name)), irrel, span),
                })
            }
        }
    }
}

/// The unfolding companions for `decl` (§2's last three rows): `f#ext`,
/// `f#irrel`, `f_unfold`.
///
/// `Err(reason)` is §3's refusal, not an error on `f`: the companions are
/// simply not emitted, `f` checks exactly as it does today, and the reason is
/// what a later reference to `f_unfold` reports.
pub(crate) fn companions(
    decl: &Decl,
    name: &str,
    measure: &Expr,
    omega_available: bool,
    tys: &dyn BinderTys,
    auto: &AutoEqs,
    lifted: &[Lowered],
) -> Result<Vec<Lowered>, String> {
    let span = measure.span;
    // §7: `fn` only. A `theorem` is opaque, so `f(ȳ)` in the equation's
    // right-hand side would never unfold — and nothing rewrites with a
    // proof's value anyway.
    if decl.kind != DeclKind::Fn {
        return Err("a `theorem`, whose value nothing rewrites with".into());
    }
    // §4: every obligation is lifted, and a body that discharges its goals by
    // statement rather than by name keeps them where they were written.
    if !liftable(decl) {
        return Err("an `on` clause naming a statement rather than an obligation".into());
    }
    let params = value_params(decl);
    let refs: Vec<&Param> = decl.params.iter().collect();
    // The body **as written** — the `on`s dropped, since they discharge the
    // measure's obligations and are no part of the equation (§5).
    let source = if decl.body.stmts.is_empty() {
        (*decl.body.result).clone()
    } else {
        Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts: decl.body.stmts.clone(),
                result: decl.body.result.clone(),
                ons: Vec::new(),
                span: decl.body.span,
            })),
            span: decl.body.span,
        }
    };
    // A member recurses under its base name (`nth(t)` inside `fn List::nth`),
    // and that name is in scope only for its own body. The equation's
    // right-hand side is read outside it, so the self-calls there are
    // qualified — the same declaration, spelled the way a reader must spell it.
    let qualified = var(&decl.name, span);
    let rhs_source = if decl.name == name {
        source.clone()
    } else {
        subst(&source, &[(name, &qualified)], &mut Vec::new())
    };
    let solo = solo(decl, name, measure);
    let fresh = || Rewrite {
        decl,
        name,
        params: &refs,
        measure,
        ons: &decl.body.ons,
        omega_available,
        tys,
        lift: true,
        members: &solo,
        caller: 0,
        next: 1,
        eqs: 0,
        refinements: Vec::new(),
        scrut_aliases: Vec::new(),
        auto_eqs: auto.clone(),
        auto_n: 0,
        scope: scope_of(decl),
        sites: Vec::new(),
        obls: Vec::new(),
        found_only: false,
        found: Vec::new(),
        found_values: Vec::new(),
        known: lifted,
        error: None,
    };
    let arg_vars: Vec<Expr> = params.iter().map(|p| var(&p.name, span)).collect();
    let explicit = decl.params.iter().any(|p| p.implicit);
    let apply = |head: Expr, args: Vec<Expr>| Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args,
            named: Vec::new(),
            explicit,
            goal_oriented: false,
        },
        span,
    };

    // -- `f#ext` --------------------------------------------------------------
    let mut ext = Respell {
        rw: fresh(),
        mode: Mode::Ext,
        decl,
        source: &source,
        sigma: Vec::new(),
        hyps: vec![var(H1, span), var(H2, span)],
        lets: Vec::new(),
        fresh: 0,
        span,
        anchors: None,
        let_env: Vec::new(),
    };
    let ext_proof = ext.walk(&source, At::Anchor)?;
    let ext_sites = std::mem::take(&mut ext.rw.sites);
    // Every obligation moved into its own declaration (§4), so the discharges
    // that raised them are no part of a companion; anything else the writer
    // wrote about a goal in the body still is.
    let moved: Vec<&str> = ext_sites.iter().map(|(_, h, ..)| h.as_str()).collect();
    let companion_ons = remaining_ons(&decl.body.ons, &moved);
    let ext_body = Block {
        stmts: std::mem::take(&mut ext.lets),
        result: Box::new(ext_proof.proof),
        ons: companion_ons.clone(),
        span: decl.body.span,
    };
    let ih_ty = |k: &str| {
        pi_over(
            &params,
            arrow(
                None,
                lt_ty(measure.clone(), var(k, span), span),
                decl.result.clone(),
                span,
            ),
            span,
        )
    };
    let hg_ty = pi_over(
        &params,
        pi(
            vec![
                ("__dec_p1", lt_ty(measure.clone(), var(A, span), span)),
                ("__dec_q1", lt_ty(measure.clone(), var(B, span), span)),
            ],
            {
                let mut l = arg_vars.clone();
                l.push(var("__dec_p1", span));
                let mut r = arg_vars.clone();
                r.push(var("__dec_q1", span));
                eq_ty(
                    app(var(G1, span), l, span),
                    app(var(G2, span), r, span),
                    span,
                )
            },
            span,
        ),
        span,
    );
    let body_at = |k: &str, g: &str, h: &str| {
        let mut args = vec![var(k, span), var(g, span)];
        args.extend(arg_vars.iter().cloned());
        args.push(var(h, span));
        app(
            companion_ref(decl, &body_name(&decl.name), span),
            args,
            span,
        )
    };
    let nat = Ty {
        kind: TyKind::Nat,
        span,
    };
    let mut ext_params = vec![
        param(A, nat.clone(), span),
        param(B, nat.clone(), span),
        param(G1, ih_ty(A), span),
        param(G2, ih_ty(B), span),
        param(HG, hg_ty, span),
    ];
    ext_params.extend(params.iter().cloned());
    ext_params.push(param(
        H1,
        lt_ty(measure.clone(), succ(var(A, span), span), span),
        span,
    ));
    ext_params.push(param(
        H2,
        lt_ty(measure.clone(), succ(var(B, span), span), span),
        span,
    ));
    let ext_decl = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
            value: false,
        elaborates: None,
        name: ext_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: ext_params,
        result: eq_ty(body_at(A, G1, H1), body_at(B, G2, H2), span),
        decreases: None,
        unfolding: Vec::new(),
        body: ext_body,
        span: decl.span,
    };

    // -- `f#irrel` ------------------------------------------------------------
    let rec_at = |z: Expr, h: Expr| {
        let mut args = vec![z];
        args.extend(arg_vars.iter().cloned());
        args.push(h);
        app(companion_ref(decl, &rec_name(&decl.name), span), args, span)
    };
    // The motive of the induction on the bound: everything but the bound
    // generalized, as bound irrelevance needs (§1).
    let outer_motive = |z: Expr| {
        let mut binders: Vec<(&str, Ty)> = vec![(W, nat.clone())];
        binders.extend(params.iter().map(|p| (p.name.as_str(), p.ty.clone())));
        binders.push((H1, lt_ty(measure.clone(), z.clone(), span)));
        binders.push((H2, lt_ty(measure.clone(), var(W, span), span)));
        pi(
            binders,
            eq_ty(
                rec_at(z, var(H1, span)),
                rec_at(var(W, span), var(H2, span)),
                span,
            ),
            span,
        )
    };
    let inner_motive = |w: Expr| {
        pi(
            vec![(H2, lt_ty(measure.clone(), w.clone(), span))],
            eq_ty(
                rec_at(succ(var(K, span), span), var(H1, span)),
                rec_at(w, var(H2, span)),
                span,
            ),
            span,
        )
    };
    let absurd = |h: &str| Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(h, span)),
            eqbind: None,
            motive: None,
            arms: Vec::new(),
        },
        span,
    };
    let pat = |n: &str| Pat::Var {
        name: n.to_string(),
        span,
    };
    let ihz = "__dec_ihz";
    let l = "__dec_l";
    // `f#ext(k, l, f#rec(k), f#rec(l), λ ȳ p q => ih(l, ȳ, p, q), x̄, h1, h2)`
    let ext_call = {
        let side = |bound: &str, p: &str| {
            let mut binders: Vec<&str> = params.iter().map(|q| q.name.as_str()).collect();
            binders.push(p);
            lam(
                &binders,
                rec_at(var(bound, span), var(p, span)),
                span,
            )
        };
        let hg = {
            let mut binders: Vec<&str> = params.iter().map(|q| q.name.as_str()).collect();
            binders.push("__dec_p1");
            binders.push("__dec_q1");
            let mut args = vec![var(l, span)];
            args.extend(arg_vars.iter().cloned());
            args.push(var("__dec_p1", span));
            args.push(var("__dec_q1", span));
            lam(&binders, app(var(ihz, span), args, span), span)
        };
        let mut args = vec![
            var(K, span),
            var(l, span),
            side(K, "__dec_p1"),
            side(l, "__dec_q1"),
            hg,
        ];
        args.extend(arg_vars.iter().cloned());
        args.push(var(H1, span));
        args.push(var(H2, span));
        app(companion_ref(decl, &ext_name(&decl.name), span), args, span)
    };
    let inner = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(W, span)),
            eqbind: None,
            motive: Some(Box::new(lam(
                &["__dec_ww"],
                ty_lit(inner_motive(var("__dec_ww", span)), span),
                span,
            ))),
            arms: vec![
                Arm {
                    ctor: "Zero".into(),
                    default: false,
                    binders: Vec::new(),
                    body: lam(&[H2], absurd(H2), span),
                    span,
                },
                Arm {
                    ctor: "Succ".into(),
                    default: false,
                    binders: vec![pat(l)],
                    body: lam(&[H2], ext_call, span),
                    span,
                },
            ],
        },
        span,
    };
    let mut zero_binders: Vec<&str> = vec![W];
    zero_binders.extend(params.iter().map(|p| p.name.as_str()));
    zero_binders.push(H1);
    zero_binders.push(H2);
    let mut succ_binders: Vec<&str> = vec![W];
    succ_binders.extend(params.iter().map(|p| p.name.as_str()));
    succ_binders.push(H1);
    let irrel_elim = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: false,
            scrut: Box::new(var(Z, span)),
            eqbind: None,
            motive: Some(Box::new(lam(
                &["__dec_zz"],
                ty_lit(outer_motive(var("__dec_zz", span)), span),
                span,
            ))),
            arms: vec![
                Arm {
                    ctor: "Zero".into(),
                    default: false,
                    binders: Vec::new(),
                    body: lam(&zero_binders, absurd(H1), span),
                    span,
                },
                Arm {
                    ctor: "Succ".into(),
                    default: false,
                    binders: vec![pat(K), pat(ihz)],
                    body: lam(&succ_binders, inner, span),
                    span,
                },
            ],
        },
        span,
    };
    let mut irrel_args = vec![var(W, span)];
    irrel_args.extend(arg_vars.iter().cloned());
    irrel_args.push(var(H1, span));
    irrel_args.push(var(H2, span));
    let mut irrel_params = vec![param(Z, nat.clone(), span), param(W, nat.clone(), span)];
    irrel_params.extend(params.iter().cloned());
    irrel_params.push(param(H1, lt_ty(measure.clone(), var(Z, span), span), span));
    irrel_params.push(param(H2, lt_ty(measure.clone(), var(W, span), span), span));
    let irrel_decl = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
            value: false,
        elaborates: None,
        name: irrel_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: irrel_params,
        result: eq_ty(
            rec_at(var(Z, span), var(H1, span)),
            rec_at(var(W, span), var(H2, span)),
            span,
        ),
        decreases: None,
        unfolding: Vec::new(),
        body: block(app(irrel_elim, irrel_args, span), decl.body.span),
        span: decl.span,
    };

    // -- `f_unfold` -----------------------------------------------------------
    let mut unfold = Respell {
        rw: fresh(),
        mode: Mode::Unfold,
        decl,
        source: &rhs_source,
        sigma: Vec::new(),
        hyps: vec![app(
            var("nat::Nat::lt_succ_self", span),
            vec![measure.clone()],
            span,
        )],
        lets: Vec::new(),
        fresh: 0,
        span,
        anchors: None,
        let_env: Vec::new(),
    };
    let unfold_proof = unfold.walk(&source, At::Anchor)?;
    let unfold_sites = std::mem::take(&mut unfold.rw.sites);
    let unfold_decl = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        is_interface: false, partial: None,
            value: false,
        elaborates: None,
        name: unfold_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: eq_ty(
            apply(
                companion_ref(decl, &decl.name, span),
                decl.params.iter().map(|p| var(&p.name, span)).collect(),
            ),
            rhs_source.clone(),
            span,
        ),
        decreases: None,
        unfolding: Vec::new(),
        body: Block {
            stmts: std::mem::take(&mut unfold.lets),
            result: Box::new(unfold_proof.proof),
            ons: companion_ons,
            span: decl.body.span,
        },
        span: decl.span,
    };

    Ok(vec![
        Lowered {
            decl: ext_decl,
            obligations: Obligations { sites: ext_sites },
        },
        Lowered {
            decl: irrel_decl,
            obligations: Obligations { sites: Vec::new() },
        },
        Lowered {
            decl: unfold_decl,
            obligations: Obligations {
                sites: unfold_sites,
            },
        },
    ])
}

// -- the step equations -------------------------------------------------------
//
// `f_unfold`'s right-hand side is the body as written, so where the body is a
// test with an equation (`if h: P { … } else { … }`, `match h: b { True => …,
// False => … }`), it is the convoy match on the test's bit. A proof about the
// loop wants the arm the test picks, with the test as its hypothesis: one
// equation per arm, `f::step` where the arm calls `f` again and `f::done` where
// it does not (issues/loop-invariant-rules.md). Each is `f_unfold` followed
// by `Bool::convoy_true`/`convoy_false`, which choose the arm at the
// hypothesis's own proof, so the arm is stated exactly as `f_unfold` spells
// it: the found proofs it passes are the same `f#found_N` terms.

/// `f#step`, spelled `f::step` — the arm of the body's test that recurses,
/// under the test. A designed spelling, as `f::ext` is, so that no name a
/// module may declare is taken.
pub(crate) fn step_name(name: &str) -> String {
    format!("{name}#step")
}

/// `f#done`, spelled `f::done` — the arm of the body's test that does not
/// recurse, under the test's failure.
pub(crate) fn done_name(name: &str) -> String {
    format!("{name}#done")
}

/// What one arm of the test is stated under: the hypothesis's name and type,
/// and the test's bit equation as an expression over that hypothesis.
struct ArmHyp {
    name: String,
    ty: Ty,
    bit_eq: Expr,
}

/// `f::step` and `f::done` for `decl`, whose `f_unfold` was built: `Err` names
/// why the body has no test to split (a `let` before it, a test that is not
/// on a `Bool`, both arms or neither recursing), and nothing is generated.
pub(crate) fn step_equations(decl: &Decl, name: &str) -> Result<Vec<Lowered>, String> {
    let span = decl.body.span;
    // The `let`s before the test (a `mut self` body opens with
    // `let s__1 = s;`) are kept before each side's arm, so that the equation
    // differs from `f_unfold`'s only in the arm; the test itself must not
    // read them, since the hypothesis is stated outside them.
    let qualified = var(&decl.name, span);
    let mut top = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span };
    if decl.name != name {
        top = subst(&top, &[(name, &qualified)], &mut Vec::new());
    }
    let mut lets: Vec<Stmt> = Vec::new();
    while let ExprKind::Block(b) = &top.kind {
        lets.extend(b.stmts.iter().cloned());
        top = (*b.result).clone();
    }
    let bound: Vec<String> = lets.iter().map(|st| match st {
        Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => Ok(name.clone()),
        Stmt::LetRecord { .. } => Err(()),
    }).collect::<Result<_, _>>().map_err(|_| "the body destructures a record before its test".to_string())?;
    let top = &top;
    let ExprKind::Match { scrut, eqbind: Some(eq), motive: None, arms, .. } = &top.kind else {
        return Err("the body is not a test with an equation (`if h: P`, `match h: b`)".into());
    };
    let arm = |ctor: &str| arms.iter().find(|a| a.ctor == ctor && !a.default && a.binders.is_empty());
    let (Some(yes), Some(no)) = (arm("True"), arm("False")) else {
        return Err("the test is not on a `Bool`".into());
    };
    if arms.len() != 2 {
        return Err("the test is not on a `Bool`".into());
    }
    let calls = |e: &Expr| {
        let mut found = false;
        crate::surface::walk_expr(e, &mut |x: &Expr| {
            if let ExprKind::Var(n) = &x.kind && n == &decl.name {
                found = true;
            }
        });
        found
    };
    let yes_steps = match (calls(&yes.body), calls(&no.body)) {
        (true, false) => true,
        (false, true) => false,
        _ => return Err("both arms or neither call the function again".into()),
    };
    let taken: Vec<&str> = decl.params.iter().map(|p| p.name.as_str()).collect();
    let fresh_hyp = |want: &str| {
        let mut n = want.to_string();
        while taken.contains(&n.as_str()) {
            n.push('\'');
        }
        n
    };
    // `if h: P` is `match e: decide_bit<P>()` with `let h = decide_true<P>(e)`
    // opening an arm that names `h`: the hypothesis is `P` (or `¬P`), and the
    // bit's equation is read back from it. A written `match h: b` keeps `h`.
    let decided = match &scrut.kind {
        ExprKind::App { head, args, named, .. } if args.is_empty() && named.is_empty() => match &head.kind {
            ExprKind::TyApp { head, args } if args.len() == 1 && matches!(&head.kind, ExprKind::Var(v) if v == "decide_bit") => Some(args[0].clone()),
            _ => None,
        },
        _ => None,
    };
    let is_evidence = |e: &Expr| match &e.kind {
        ExprKind::App { head, .. } => matches!(&head.kind, ExprKind::TyApp { head, .. }
            if matches!(&head.kind, ExprKind::Var(v) if v == "decide_true" || v == "decide_false")),
        _ => false,
    };
    let reads_lets = bound.iter().any(|x| match &decided {
        Some(prop) => crate::inductive::ty_mentions(prop, x),
        None => crate::inductive::expr_mentions(scrut, x),
    });
    if reads_lets {
        return Err("the test reads a name the body binds before it".into());
    }
    let with_lets = |e: Expr| if lets.is_empty() { e } else {
        Expr { kind: ExprKind::Block(Box::new(Block { stmts: lets.clone(), result: Box::new(e), ons: Vec::new(), span })), span }
    };
    let hyp = |body: &Expr, truth: bool| -> ArmHyp {
        match &decided {
            Some(prop) => {
                let evidence = match &body.kind {
                    ExprKind::Block(b) => match b.stmts.first() {
                        Some(Stmt::Let { name, expr, .. }) if is_evidence(expr) => Some(name.clone()),
                        _ => None,
                    },
                    _ => None,
                };
                let name = fresh_hyp(evidence.as_deref().unwrap_or("h"));
                let ty = if truth {
                    prop.clone()
                } else {
                    arrow(None, prop.clone(), Ty { kind: TyKind::Named { name: "False".into(), args: Vec::new() }, span }, span)
                };
                let lemma = if truth { "bool::decide_bit_of" } else { "bool::decide_bit_of_not" };
                let head = Expr { kind: ExprKind::TyApp { head: Box::new(var(lemma, span)), args: vec![prop.clone()] }, span };
                let bit_eq = app(head, vec![var(&name, span)], span);
                ArmHyp { name, ty, bit_eq }
            }
            None => {
                let name = fresh_hyp(eq);
                let ctor = var(if truth { "True" } else { "False" }, span);
                let ty = eq_ty((**scrut).clone(), ctor, span);
                let bit_eq = var(&name, span);
                ArmHyp { name, ty, bit_eq }
            }
        }
    };
    let explicit = decl.params.iter().any(|p| p.implicit);
    let call = |head: Expr, args: Vec<Expr>| Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: Vec::new(), explicit, goal_oriented: false },
        span,
    };
    let args: Vec<Expr> = decl.params.iter().map(|p| var(&p.name, span)).collect();
    let lhs = call(companion_ref(decl, &decl.name, span), args.clone());
    let unfold = call(companion_ref(decl, &unfold_name(&decl.name), span), args);
    let arm_fn = |a: &Arm| lam(&[eq.as_str()], a.body.clone(), span);
    let mut out = Vec::new();
    for (arm, truth) in [(yes, true), (no, false)] {
        let h = hyp(&arm.body, truth);
        let rhs = with_lets(subst(&arm.body, &[(eq.as_str(), &h.bit_eq)], &mut Vec::new()));
        let chooser = if truth { "bool::Bool::convoy_true" } else { "bool::Bool::convoy_false" };
        let chosen = app(var(chooser, span), vec![(**scrut).clone(), arm_fn(yes), arm_fn(no), h.bit_eq.clone()], span);
        let proof = app(var("trans", span), vec![unfold.clone(), with_lets(chosen)], span);
        let mut params = decl.params.clone();
        params.push(Param {
            name: h.name.clone(),
            ty: h.ty,
            implicit: false,
            is_self: false,
            solver: None,
            default: None,
            origin: ParamOrigin::Written,
            symbol: None,
            span,
        });
        let steps = truth == yes_steps;
        out.push(Lowered {
            decl: Decl {
                kind: DeclKind::Theorem,
                is_meta: false,
                is_evidence: false,
                is_interface: false,
                partial: None,
                value: false,
                elaborates: None,
                name: if steps { step_name(&decl.name) } else { done_name(&decl.name) },
                tyvars: decl.tyvars.clone(),
                params,
                result: eq_ty(lhs.clone(), rhs, span),
                decreases: None,
                unfolding: Vec::new(),
                body: block(proof, span),
                span: decl.span,
            },
            obligations: Obligations { sites: Vec::new() },
        });
    }
    Ok(out)
}
