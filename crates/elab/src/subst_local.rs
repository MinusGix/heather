//! `subst(h, e)`: eliminate a local variable along an equation
//! (`docs/equation-rewrite-design.md` §8, `issues/subst-local-equation.md`).
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

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, NamedArg, Span};

use crate::context::Alias;
use crate::{Cx, ElabError, Elaborator, R};

impl Elaborator {
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
            (None, None) => {
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
            mcx.push(cx.names[p].clone(), dom.clone(), dom_level.clone());
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
            motive_level = Level::join(dom_level, motive_level);
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
            let name = if visible(cx, p) { cx.names[p].clone() } else { "#subst".to_string() };
            ccx.push_skel(name, (*dom).clone(), dom_level.clone(), cx.skels[p].clone());
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
                name: x_name.clone(),
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
                name: cx.names[p].clone(),
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
            let later = cx.aliases[i + 1..].iter().any(|b| b.name == a.name);
            let by = (n - a.depth) as u32;
            let (term, ty) = a.at(by);
            if a.depth <= pos_x
                || later
                || cx.names[a.depth..].contains(&a.name)
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
    cx.names.iter().rposition(|m| m == name) == Some(p) && !cx.aliases.iter().any(|a| a.name == *name && a.depth > p)
}
