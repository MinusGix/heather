//! `subst(h, e)`: eliminate a local variable along an equation
//! (`docs/tactics/equation-rewrite-design.md` §8, `issues/subst-local-equation.md`).
//!
//! At a checking position with goal `G` in `Γ = Γ₀, x : A, Δ`, with
//! `h : t = x` (or `x = t`) and `t` not mentioning `x`: every later local
//! whose type mentions `x` — directly or through another such local — is
//! *reverted* into the motive as a `Π`, `x` becomes the motive's `y`, and one
//! kernel `J` from `t` to `x` closes the goal. `e` is checked where `x` means
//! `t`: the reverted locals are bound again under their names at their types
//! with `t` for `x`, `x` itself is a `let` alias of `t`, and `h` one of
//! `refl`. Nothing leaves `Γ`: `x` stays a binder the case no longer
//! mentions, so no local has to move and no de Bruijn index is renumbered
//! outside the motive.
//!
//! Nothing here is trusted: the declaration passes the kernel gate.

use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, NamedArg, Span};

use crate::context::Alias;
use crate::{Cx, ElabError, Elaborator, R};

/// Local substitution's part of the elaborator.
pub(crate) struct LocalSubsts<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for LocalSubsts<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl LocalSubsts<'_> {
    /// `subst(h, e)` at `goal`.
    pub(crate) fn elab_subst(
        &self,
        cx: &Cx,
        args: &[Expr],
        named: &[NamedArg],
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let fail = |msg: String, span: Span| Err(ElabError::Elab { msg, span });
        let [h, body] = args else {
            return fail(
                "`subst` takes one equation between a local variable and a term, then the \
                 proof of the goal with the variable replaced: `subst(h, e)`"
                    .into(),
                span,
            );
        };
        if let Some(arg) = named.first() {
            return fail(format!("`subst` takes no named arguments, and not `{} :=`", arg.name), arg.name_span);
        }
        let (proof, proof_ty, _) = self.elab_infer(cx, h)?;
        let Type::Id { level, ty, lhs, rhs } = self.whnf(cx, &proof_ty, h.span)? else {
            return fail(
                format!(
                    "`subst` eliminates a variable along an equation `x = t`, and this proof is \
                     of `{}`",
                    self.display_type(cx, &proof_ty)
                ),
                h.span,
            );
        };
        let n = cx.names.len();
        let gamma = &cx.gamma;
        // The side that is a local not occurring in the other: the right one
        // first, as Lean's `subst` reads `h : a = b`.
        let local = |side: &Term, other: &Term| match side {
            Term::Var(v) if (v.0 as usize) < n => {
                let pos = n - 1 - v.0 as usize;
                (!mentions(gamma, other, &marked(n, &[pos]))).then_some(pos)
            }
            _ => None,
        };
        let (pos_x, t, var_on_right) = match (local(&rhs, &lhs), local(&lhs, &rhs)) {
            (Some(p), _) => (p, lhs, true),
            (None, Some(p)) => (p, rhs, false),
            // A side that only reduces to a local — a pattern variable
            // re-bound by a split below — is that local.
            (None, None) if let Some(p) = self.reduces_to_local(cx, &rhs, h.span)
                .filter(|&p| !mentions(gamma, &lhs, &marked(n, &[p]))) => (p, lhs, true),
            (None, None) if let Some(p) = self.reduces_to_local(cx, &lhs, h.span)
                .filter(|&p| !mentions(gamma, &rhs, &marked(n, &[p]))) => (p, rhs, false),
            (None, None) => {
                // A pattern variable is a projection of the matched value:
                // take the value apart into locals, and eliminate there
                // (issues/pattern-variables-not-rewritable.md).
                if let Some(split) = self
                    .split_projection(cx, &rhs, goal, h.span)
                    .or_else(|| self.split_projection(cx, &lhs, goal, h.span))
                {
                    let term = self.elab_subst(&split.cx, args, named, &split.goal, lvl, span)?;
                    return Ok(split.close(&term));
                }
                let shown = |t: &Term| self.spell_term_clean(cx, t).unwrap_or_else(|| "?".into());
                return fail(
                    format!(
                        "`subst`: neither side of `{} = {}` is a local variable the other side \
                         does not mention\n  hint: `rewrite(h, e)` rewrites a goal along an \
                         equation between terms",
                        shown(&lhs),
                        shown(&rhs)
                    ),
                    h.span,
                );
            }
        };
        let x_name = &cx.names[pos_x];
        // `h` itself, when it is a local: it is eliminated along with `x`
        // (it becomes `J`'s own proof variable), never reverted, unless its
        // orientation would make that `sym(sym(h))` somewhere it is mentioned.
        let pos_h = match &proof {
            Term::Var(v) if (v.0 as usize) < n => Some(n - 1 - v.0 as usize),
            _ => None,
        };

        // The locals to revert: every later one whose type mentions `x`, `h`
        // or an earlier reverted one, in context order.
        let mut moved = marked(n, &[pos_x]);
        if let Some(p) = pos_h {
            moved[p] = true;
        }
        let mut reverted = Vec::new();
        for p in pos_x + 1..n {
            if Some(p) == pos_h {
                continue;
            }
            if mentions_ty(gamma, &entry_ty(cx, p), &moved) {
                reverted.push(p);
                moved[p] = true;
            }
        }
        if mentions(gamma, &t, &moved) {
            return fail(
                format!(
                    "`subst`: `{}` mentions a local whose type depends on `{x_name}`, so `{x_name}` \
                     cannot be replaced by it",
                    self.spell_term_clean(cx, &t).unwrap_or_else(|| "the other side".into())
                ),
                h.span,
            );
        }
        // `h : x = t` would be eliminated as `sym(q)`, which is not `h` again
        // at `q := sym(h)`. When anything mentions it, it is reverted
        // instead, and the case sees it at `t = t`.
        let h_elim = match pos_h {
            Some(p) if !var_on_right => {
                let only_h = marked(n, &[p]);
                let mentioned = mentions_ty(gamma, goal, &only_h)
                    || reverted.iter().any(|&d| mentions_ty(gamma, &entry_ty(cx, d), &only_h));
                if mentioned {
                    let at = reverted.partition_point(|&d| d < p);
                    reverted.insert(at, p);
                }
                None
            }
            other => other,
        };
        let k = reverted.len();

        // The motive, over Γ, y : A, q : t = y: the goal with `x` as `y`, `h`
        // as `q`, under a `Π` for each reverted local.
        let mut mcx = cx.clone();
        mcx.push("_".into(), (*ty).clone(), level.clone());
        let q_ty = Type::Id {
            level: level.clone(),
            ty: Rc::new(ty.shift_local(1)),
            lhs: Rc::new(t.shift_local(1)),
            rhs: Rc::new(Term::Var(LocalVar(0))),
        };
        mcx.push("_".into(), q_ty, level.clone());
        let ycx = mcx.clone();
        // From Γ to Γ, y, q, d'₁ … d'ⱼ.
        let sigma = |at: &LocalCtx, j: usize| {
            let mut s = LocalSubst::id(at);
            s.terms.truncate(n);
            s.terms[pos_x] = Rc::new(Term::Var(LocalVar(j as u32 + 1)));
            if let Some(p) = h_elim {
                s.terms[p] = Rc::new(Term::Var(LocalVar(j as u32)));
            }
            for (i, &p) in reverted.iter().enumerate() {
                s.terms[p] = Rc::new(if i < j { Term::Var(LocalVar((j - 1 - i) as u32)) } else { Term::Zero });
            }
            s
        };
        let mut doms = Vec::with_capacity(k);
        for (j, &p) in reverted.iter().enumerate() {
            let dom = entry_ty(cx, p).apply_local(&sigma(&mcx.gamma, j));
            let dom_level = cx.gamma.entries[p].level.clone();
            mcx.push(cx.names[p].to_string(), dom.clone(), dom_level.clone());
            doms.push((dom, dom_level));
        }
        let mut motive = goal.apply_local(&sigma(&mcx.gamma, k));
        let mut motive_level = lvl.clone();
        for (dom, dom_level) in doms.into_iter().rev() {
            motive = Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: motive_level.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(motive),
            };
            motive_level = Level::max(dom_level, motive_level);
        }
        let psi = self.goal_psi();
        typing::check_type(&psi, 0, Layer::Prog, &ycx.gamma, &motive, &motive_level, self.policy.fuel).map_err(|_| {
            ElabError::Elab {
                msg: format!(
                    "`subst`: generalising the goal over `{x_name}` and the locals that depend on it \
                     does not leave a type\n  hint: write the motive by hand with `j`"
                ),
                span: h.span,
            }
        })?;

        // The case: the motive at `t` and `refl`, its reverted locals bound
        // again under their own names.
        let refl_t = Term::Refl { level: level.clone(), ty: Rc::clone(&ty), tm: Rc::clone(&t) };
        let mut cur = motive.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(&t)).extended(Rc::new(refl_t.clone())));
        let mut ccx = cx.clone();
        let mut lams = Vec::with_capacity(k);
        for &p in &reverted {
            let Type::Pi { dom_level, cod_level, dom, cod } = cur else {
                unreachable!("the motive opens with one Π per reverted local");
            };
            let name = if visible(cx, p) { cx.names[p].to_string() } else { "#subst".to_string() };
            ccx.push_skel(name, (*dom).clone(), dom_level.clone(), cx.names.skel(p).cloned());
            lams.push((dom_level, cod_level, dom));
            cur = (*cod).clone();
        }
        // `x` means `t` now, `h` means `refl`, and a `let` that mentioned
        // either (or a reverted local) means what it does at them.
        let mut tau = LocalSubst::id(&ccx.gamma);
        tau.terms.truncate(n);
        tau.terms[pos_x] = Rc::new(t.shift_local(k as u32));
        if let Some(p) = h_elim {
            tau.terms[p] = Rc::new(refl_t.shift_local(k as u32));
        }
        for (i, &p) in reverted.iter().enumerate() {
            tau.terms[p] = Rc::new(Term::Var(LocalVar((k - 1 - i) as u32)));
        }
        let mut stale = marked(n, &[pos_x]);
        for &p in h_elim.iter().chain(&reverted) {
            stale[p] = true;
        }
        let depth = ccx.names.len();
        let mut aliases = Vec::new();
        if visible(cx, pos_x) {
            aliases.push(Alias {
                name: x_name.to_string(),
                depth,
                term: Rc::new(t.shift_local(k as u32)),
                ty: ty.shift_local(k as u32),
                level: level.clone(),
                skel: None,
                spliced: None,
                shifted: Default::default(),
            });
        }
        if let Some(p) = pos_h.filter(|p| !reverted.contains(p) && visible(cx, *p)) {
            aliases.push(Alias {
                name: cx.names[p].to_string(),
                depth,
                term: Rc::new(refl_t.shift_local(k as u32)),
                ty: Type::Id { level: level.clone(), ty: Rc::clone(&ty), lhs: Rc::clone(&t), rhs: Rc::clone(&t) }
                    .shift_local(k as u32),
                level: level.clone(),
                skel: None,
                spliced: None,
                shifted: Default::default(),
            });
        }
        for (i, a) in cx.aliases.iter().enumerate() {
            let later = cx.aliases.iter().skip(i + 1).any(|b| b.name == a.name);
            let by = (n - a.depth) as u32;
            let (term, ty) = a.at(by);
            if a.depth <= pos_x
                || later
                || cx.names.iter().skip(a.depth).any(|later| later == a.name)
                || !(mentions(gamma, &term, &stale) || mentions_ty(gamma, &ty, &stale))
            {
                continue;
            }
            aliases.push(Alias {
                name: a.name.clone(),
                depth,
                term: Rc::new(term.apply_local(&tau)),
                ty: ty.apply_local(&tau),
                level: a.level.clone(),
                skel: a.skel.clone(),
                spliced: None,
                shifted: Default::default(),
            });
        }
        ccx.aliases.extend(aliases.into_iter().map(Rc::new));
        let mut case = self.elab_check(&ccx, body, &cur, lvl)?;
        for (dom_level, cod_level, dom) in lams.into_iter().rev() {
            case = Term::Lam { dom_level, cod_level, dom, body: Rc::new(case) };
        }

        // `J(p; y q. M; case) : M[x/y, p/q]`, with `p : t = x` — `h` itself,
        // or `sym(h)` written out — then applied to the reverted locals.
        let x = Rc::new(Term::Var(LocalVar((n - 1 - pos_x) as u32)));
        let proof = Rc::new(proof);
        let p = if var_on_right {
            proof
        } else {
            Rc::new(Term::J {
                ty_level: level.clone(),
                motive_level: level.clone(),
                ty: Rc::clone(&ty),
                lhs: Rc::clone(&x),
                motive: Rc::new(Type::Id {
                    level: level.clone(),
                    ty: Rc::new(ty.shift_local(2)),
                    lhs: Rc::new(Term::Var(LocalVar(1))),
                    rhs: Rc::new(x.shift_local(2)),
                }),
                case: Rc::new(Term::Refl { level: level.clone(), ty: Rc::clone(&ty), tm: Rc::clone(&x) }),
                rhs: Rc::clone(&t),
                proof,
            })
        };
        let mut result_ty = motive.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(&x)).extended(Rc::clone(&p)));
        let mut term = Term::J {
            ty_level: level.clone(),
            motive_level,
            ty,
            lhs: t,
            motive: Rc::new(motive),
            case: Rc::new(case),
            rhs: x,
            proof: p,
        };
        for &d in &reverted {
            let Type::Pi { dom_level, cod_level, dom, cod } = result_ty else {
                unreachable!("the motive opens with one Π per reverted local");
            };
            let arg = Rc::new(Term::Var(LocalVar((n - 1 - d) as u32)));
            result_ty = cod.inst_top(0, &arg);
            term = crate::spelling::checked_app(Rc::new(term), dom_level, cod_level, dom, cod, arg);
        }
        Ok(term)
    }
}

/// The type of the local at position `p`, scoped in the whole of `cx`.
fn entry_ty(cx: &Cx, p: usize) -> Type {
    cx.gamma.entries[p].ty.shift_local((cx.names.len() - p) as u32)
}

/// Positions `ps` of a context of length `n`, marked.
fn marked(n: usize, ps: &[usize]) -> Vec<bool> {
    let mut out = vec![false; n];
    for &p in ps {
        out[p] = true;
    }
    out
}

/// The marker substitution of [`crate::mentions_binder`], over every marked
/// position at once: a marked variable becomes `Zero`, so the result differs
/// from the input exactly when one occurred.
fn markers(gamma: &LocalCtx, marked: &[bool]) -> LocalSubst {
    let mut s = LocalSubst::id(gamma);
    for (p, &m) in marked.iter().enumerate() {
        if m {
            s.terms[p] = Rc::new(Term::Zero);
        }
    }
    s
}

/// Does `t`, scoped in `gamma`, mention a marked local?
fn mentions(gamma: &LocalCtx, t: &Term, marked: &[bool]) -> bool {
    t.apply_local(&markers(gamma, marked)) != *t
}

/// [`mentions`] at the type level.
fn mentions_ty(gamma: &LocalCtx, t: &Type, marked: &[bool]) -> bool {
    t.apply_local(&markers(gamma, marked)) != *t
}

/// Is the local at `p` what its name means here — not shadowed by a later
/// binder or a `let` bound after it?
fn visible(cx: &Cx, p: usize) -> bool {
    let name = &cx.names[p];
    cx.names.lookup(name) == Some(p) && !cx.aliases.iter_inner().any(|a| a.name == *name && a.depth > p)
}

/// A local of pair type taken apart into its components, so that a pattern
/// variable — an alias of a projection of the matched value — is a local
/// (issues/pattern-variables-not-rewritable.md).
///
/// A `match` arm binds its fields as aliases of `fst(sndʲ(v))` for the arm's
/// value `v` (`elab_arm`, `wf.rs`), and the arm's goal and hypotheses mention
/// `v` whole. So `subst` finds no local in `t = []`, and `rewrite` along it
/// finds no `t` in a goal that displays one. [`LocalSubsts::split_projection`]
/// answers both by the move Lean's `cases` makes for a structure: a context
/// in which `v`'s components are binders `c₀ … c_L`, every later local that
/// mentions `v` is bound again at `v := (c₀, …, c_L)`, the goal likewise,
/// and the aliases that were `v`'s components are the binders themselves.
/// The caller elaborates there; [`Split::close`] substitutes the projections
/// of `v` back, and the result has the goal's type up to Σ-η — the kernel's
/// surjective pairing, so the gate judges it like any other term.
///
/// Reached only where `subst` or `rewrite` was about to refuse, so a
/// declaration that elaborated before is untouched.
pub(crate) struct Split {
    pub(crate) cx: Cx,
    pub(crate) goal: Type,
    /// From the split context back to the original one.
    sigma: LocalSubst,
}

impl Split {
    pub(crate) fn close(&self, t: &Term) -> Term {
        t.apply_local(&self.sigma)
    }
}

/// `t` as a chain of pair projections from a local: the local's position and
/// the projections from it outward (`true` for `fst`). Each layer is read
/// at its weak-head form, so a child read through `nth` counts.
fn projection_path(el: &Elaborator, cx: &Cx, t: &Term, span: Span) -> Option<(usize, Vec<bool>)> {
    let n = cx.names.len();
    let mut ops = Vec::new();
    let mut cur = el.whnf_tm(cx, t, span).ok()?;
    loop {
        let next = match &*cur {
            Term::Fst { pair, .. } | Term::FstAt { pair } => {
                ops.push(true);
                pair
            }
            Term::Snd { pair, .. } | Term::SndAt { pair } => {
                ops.push(false);
                pair
            }
            Term::Var(v) if (v.0 as usize) < n && !ops.is_empty() => {
                ops.reverse();
                return Some((n - 1 - v.0 as usize, ops));
            }
            _ => return None,
        };
        cur = el.whnf_tm(cx, next, span).ok()?;
    }
}

impl LocalSubsts<'_> {
    /// `t`, when it is not a local itself but reduces to one: the local's
    /// position.
    pub(crate) fn reduces_to_local(&self, cx: &Cx, t: &Term, span: Span) -> Option<usize> {
        let n = cx.names.len();
        match &*self.whnf_tm(cx, t, span).ok()? {
            Term::Var(v) if (v.0 as usize) < n => Some(n - 1 - v.0 as usize),
            _ => None,
        }
    }

    /// The split of the local that `side` projects out of, at `goal` — see
    /// [`Split`]. `None` when `side` is no such projection, the local's type
    /// is not that deep a Σ, or the split would not make `side` any closer
    /// to a local (which also bounds a caller that splits again).
    pub(crate) fn split_projection(&self, cx: &Cx, side: &Term, goal: &Type, span: Span) -> Option<Split> {
        if self.under_quotation() {
            return None;
        }
        let (pos, ops) = projection_path(self, cx, side, span)?;
        let n = cx.names.len();
        let gamma = &cx.gamma;
        // Σ levels walked: the leading `snd`s, and the `fst` after them.
        let snds = ops.iter().take_while(|op| !**op).count();
        let levels = if snds < ops.len() { snds + 1 } else { snds };
        let k = levels + 1;
        // The components, each at its Σ level's first type in the context of
        // the ones before it, and the tail after the last level.
        let mut wcx = cx.clone();
        let mut sigmas: Vec<Type> = Vec::with_capacity(levels);
        let mut comps: Vec<(Type, Level)> = Vec::with_capacity(k);
        let mut cur = entry_ty(cx, pos);
        for i in 0..levels {
            let head = self.whnf(&wcx, &cur, span).ok()?;
            let Type::Sigma { fst_level, snd_level, fst, snd } = &head else {
                return None;
            };
            comps.push(((**fst).clone(), fst_level.clone()));
            wcx.push(format!("#split{i}"), (**fst).clone(), fst_level.clone());
            sigmas.push(head.clone());
            cur = (**snd).clone();
            if i + 1 == levels {
                comps.push((cur.clone(), snd_level.clone()));
            }
        }
        // The aliases that are a component outright give it their name.
        let mut comp_names: Vec<Option<String>> = vec![None; k];
        let comp_ops = |i: usize| -> Vec<bool> {
            let mut ops = vec![false; i];
            if i < levels {
                ops.push(true);
            }
            ops
        };
        let mut reverted = Vec::new();
        let mut moved = marked(n, &[pos]);
        for p in pos + 1..n {
            if mentions_ty(gamma, &entry_ty(cx, p), &moved) {
                reverted.push(p);
                moved[p] = true;
            }
        }
        let shadowed = |i: usize, a: &Alias| {
            cx.aliases.iter().skip(i + 1).any(|b| b.name == a.name)
                || cx.names.iter().skip(a.depth).any(|later| later == a.name)
        };
        let mut repush: Vec<Rc<Alias>> = Vec::new();
        for (i, a) in cx.aliases.iter().enumerate() {
            if shadowed(i, a) {
                continue;
            }
            let (term, ty) = a.at((n - a.depth) as u32);
            if !(mentions(gamma, &term, &moved) || mentions_ty(gamma, &ty, &moved)) {
                continue;
            }
            match projection_path(self, cx, &term, span) {
                Some((q, path)) if q == pos && (0..k).any(|c| comp_ops(c) == path) => {
                    let c = (0..k).find(|&c| comp_ops(c) == path).expect("just found");
                    if comp_names[c].is_none() {
                        comp_names[c] = Some(a.name.clone());
                        continue;
                    }
                    repush.push(Rc::clone(a));
                }
                _ => repush.push(Rc::clone(a)),
            }
        }
        // The components as binders, named.
        let mut ncx = cx.clone();
        for (i, (ty, level)) in comps.iter().enumerate() {
            let name = comp_names[i].clone().unwrap_or_else(|| format!("#split{i}"));
            ncx.push(name, ty.clone(), level.clone());
        }
        // `v` rebuilt from them, scoped over Γ, c₀ … c_L.
        let mut tuple = Term::Var(LocalVar(0));
        for i in (0..levels).rev() {
            tuple = Term::PairAt {
                ty: Some(Rc::new(sigmas[i].shift_local((k - i) as u32))),
                fst: Rc::new(Term::Var(LocalVar((k - 1 - i) as u32))),
                snd: Rc::new(tuple),
            };
        }
        // From Γ to the split context as it stands with `j` locals bound
        // again: `v` is the tuple, a re-bound local its new binder, and a
        // later one (which no earlier type mentions) a dummy.
        let rho = |at: &Cx, j: usize| {
            let mut s = LocalSubst::id(&at.gamma);
            s.terms.truncate(n);
            s.terms[pos] = Rc::new(tuple.shift_local(j as u32));
            for (i, &p) in reverted.iter().enumerate() {
                s.terms[p] = Rc::new(if i < j { Term::Var(LocalVar((j - 1 - i) as u32)) } else { Term::Zero });
            }
            s
        };
        for (j, &p) in reverted.iter().enumerate() {
            let ty = entry_ty(cx, p).apply_local(&rho(&ncx, j));
            let name = if visible(cx, p) { cx.names[p].to_string() } else { "#split".to_string() };
            ncx.push_skel(name, ty, cx.gamma.entries[p].level.clone(), cx.names.skel(p).cloned());
        }
        let m = reverted.len();
        let full = rho(&ncx, m);
        let goal = goal.apply_local(&full);
        let depth = ncx.names.len();
        let mut aliases = Vec::new();
        if visible(cx, pos) && !cx.names[pos].starts_with('#') {
            aliases.push(Alias {
                name: cx.names[pos].to_string(),
                depth,
                term: Rc::new(tuple.shift_local(m as u32)),
                ty: entry_ty(cx, pos).apply_local(&full),
                level: cx.gamma.entries[pos].level.clone(),
                skel: None,
                spliced: None,
                shifted: Default::default(),
            });
        }
        for a in repush {
            let (term, ty) = a.at((n - a.depth) as u32);
            aliases.push(Alias {
                name: a.name.clone(),
                depth,
                term: Rc::new(term.apply_local(&full)),
                ty: ty.apply_local(&full),
                level: a.level.clone(),
                skel: a.skel.clone(),
                spliced: None,
                shifted: Default::default(),
            });
        }
        ncx.aliases.extend(aliases.into_iter().map(Rc::new));
        // Progress: in the split context `side` is a local, or a projection
        // path shorter than the one it was.
        let moved_side = side.apply_local(&full);
        let progressed = self.reduces_to_local(&ncx, &moved_side, span).is_some()
            || projection_path(self, &ncx, &moved_side, span).is_some_and(|(_, o)| o.len() < ops.len());
        if !progressed {
            return None;
        }
        // Back: each component is its projection of `v`, each re-bound local
        // the one it re-binds.
        let v = Rc::new(Term::Var(LocalVar((n - 1 - pos) as u32)));
        let mut sigma = LocalSubst::id(gamma);
        for i in 0..k {
            let mut proj = Rc::clone(&v);
            for _ in 0..i {
                proj = Rc::new(Term::SndAt { pair: proj });
            }
            if i < levels {
                proj = Rc::new(Term::FstAt { pair: proj });
            }
            sigma = sigma.extended(proj);
        }
        for &p in &reverted {
            sigma = sigma.extended(Rc::new(Term::Var(LocalVar((n - 1 - p) as u32))));
        }
        Some(Split { cx: ncx, goal, sigma })
    }
}
