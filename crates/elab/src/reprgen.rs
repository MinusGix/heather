//! `reprgen` — the transfer generator (`docs/datarepr-design.md` §3).
//!
//! Certgen's sibling, and untrusted for the same reason: it emits **surface
//! source** — a derived body, its closing lemma, its `refines` theorem and the
//! `impl` that registers them — which the ordinary pipeline then checks. A
//! wrong emission is a failed declaration, never a wrong certificate. Declining
//! with a reason is a supported answer (§3.3).
//!
//! Phases, per §3.1: 0 resolution, 1 eligibility, 2 transcription,
//! 3 obligation synthesis, 4 certificate emission. What §3.1 did not say, and
//! the hand-run found (`crates/elab/tests/reprgen.rs`), is that phase 4 is not
//! only a fold over laws: the spec function does **not** definitionally equal
//! its own recursor unfolding — both are recursive globals — so the generator
//! has to emit an *induction* linking them, and the congruence steps of that
//! induction have to be explicit `j` motives, because the prelude's
//! anti-unifying `cong` cannot generalize two sides that differ inside the
//! recursor's own algebra arguments.

use std::collections::HashMap;

use heather_syntax::{Decl, Expr, ExprKind};

use crate::datarepr::{appc, lams, spec_rec_name, spell_ty, CtorView};
use crate::Elaborator;

/// One transfer: the surface source, plus what a caller needs to key it.
pub struct ReprEmission {
    /// The spec function transferred.
    pub op: String,
    /// The repr it was transferred to.
    pub repr: String,
    /// The emitted declarations, in dependency order.
    pub text: String,
}

/// One arm of the recursion, as phases 2 and 4 both need it.
struct Arm<'a> {
    ctor: &'a CtorView,
    /// The arm's pattern binders, in field order, as the source wrote them.
    binders: Vec<String>,
    /// The arm's body.
    body: &'a Expr,
}

/// A self-call occurrence inside an arm body: the recursive child it
/// descends on. The order is the spelling walk's, which is what the
/// certificate's rewrite chain indexes.
struct SelfCall {
    child: String,
}

/// The one shape v1 transfers: `f(q⃗, x: S)` defined by a total `match` on
/// `x`. Everything else declines with a reason (§3.3).
struct Fragment<'a> {
    /// The recursion parameter's name.
    rec_param: String,
    /// The other parameters, `(name, spelled type)`, none of them at `S`.
    others: Vec<(String, String)>,
    /// The result type, spelled. Never `S` this round — see the as-landed
    /// note on §3.3.
    result: String,
    arms: Vec<Arm<'a>>,
}

impl Elaborator {
    /// Transfer `op` to repr `repr`, emitting a derived `Impl` (§3).
    ///
    /// Pure: it reads the registries and returns text. Nothing is declared
    /// until a caller elaborates the emission, which is what keeps a declined
    /// or wrong transfer from leaving anything behind.
    pub fn reprgen(&self, op: &str, repr: &str) -> Result<ReprEmission, String> {
        // -- phase 0: resolution ------------------------------------------
        let rp = self
            .datarepr_by_name
            .get(repr)
            .ok_or_else(|| format!("`{repr}` is not a `datarepr` in scope"))?;
        let f = self
            .decls
            .get(op)
            .ok_or_else(|| format!("`{op}` is not a declared function here"))?;
        if self.impl_global(repr, op).is_some() {
            return Err(format!(
                "`{op}` already has an `Impl` at `{repr}`: a transfer does not overwrite \
                 a hand override"
            ));
        }
        if !f.tyvars.is_empty() {
            return Err(format!("`{op}` is polymorphic: v1 transfers monomorphic operations"));
        }
        let frag = self.fragment(op, f, &rp.written, &rp.ctors)?;
        // The callee closure, restricted to what v1 can close a certificate
        // over: a callee that *touches* `S` needs its own `Impl`'s `refines`
        // to close the step, and that is the stage after this one.
        for arm in &frag.arms {
            for callee in callees(arm.body) {
                if callee == op {
                    continue;
                }
                if let Some(d) = self.decls.get(&callee) {
                    if touches(d, &rp.written) {
                        return Err(format!(
                            "`{op}` calls `{callee}`, which touches `{}`: a callee at the \
                             repr'd type has to be resolved against the `Impl` registry, \
                             which is the stage after this one \
                             (docs/datarepr-design.md §3.1 phase 0)",
                            rp.written
                        ));
                    }
                }
            }
        }

        // -- phase 2: transcription ---------------------------------------
        //
        // The structural match becomes the anchor fold: one step per
        // constructor, the arm's fields as the step's leading binders and the
        // recursive occurrences at the accumulator slots.
        let s = &rp.written;
        let c = &rp.carrier;
        let rec = &rp.record;
        let sr = spec_rec_name(repr);
        let abs = format!("{rec}::abs()");
        let inv = format!("{rec}::inv()");
        let b = &frag.result;

        let mut steps: Vec<String> = Vec::new();
        let mut spec_steps_v: Vec<String> = Vec::new();
        for arm in &frag.arms {
            let mut bs: Vec<(String, String)> = Vec::new();
            let mut sbs: Vec<(String, String)> = Vec::new();
            for (i, fld) in arm.ctor.fields.iter().enumerate() {
                bs.push((
                    arm.binders[i].clone(),
                    if fld.rec { c.clone() } else { fld.spell.clone() },
                ));
                sbs.push((arm.binders[i].clone(), fld.spell.clone()));
            }
            let occ = self_calls(arm.body, op);
            // Each recursive field gets an accumulator binder; a self-call on
            // that field reads it. v1 requires the correspondence to be exact,
            // which `fragment` has already checked.
            let recs: Vec<&str> = arm
                .ctor
                .fields
                .iter()
                .enumerate()
                .filter(|(_, f)| f.rec)
                .map(|(i, _)| arm.binders[i].as_str())
                .collect();
            for (k, _) in recs.iter().enumerate() {
                bs.push((format!("b{k}"), b.clone()));
                sbs.push((format!("b{k}"), b.clone()));
            }
            let mut sub: HashMap<usize, String> = HashMap::new();
            for (n, sc) in occ.iter().enumerate() {
                let k = recs
                    .iter()
                    .position(|r| *r == sc.child)
                    .expect("checked in `fragment`");
                sub.insert(n, format!("b{k}"));
            }
            let Some(body) = spell_with(arm.body, op, &sub) else {
                return Err(format!(
                    "`{op}`'s `{}` arm is not a shape this round can spell: an arm is an \
                     application over its binders, the other parameters, self-calls on a \
                     recursive child, and globals that do not touch `{s}`",
                    arm.ctor.name
                ));
            };
            steps.push(lams(&bs, &body));
            // The SPEC-side algebra: the same body, with the recursive fields
            // bound at `S` instead of the carrier. It is what `fold_law`
            // quantifies over, and the adaptation (`abs` at the child
            // position) beta-reduces it back to the repr step above — which
            // holds precisely because the fragment forbids an arm from
            // mentioning a recursive child outside a self-call, so the binder
            // whose type differs is never used.
            spec_steps_v.push(lams(&sbs, &body));
        }
        let spec_steps = &spec_steps_v;

        // -- phase 3: obligation synthesis (§1.2's schema) -----------------
        let mut params: Vec<(String, String)> = frag
            .others
            .iter()
            .cloned()
            .collect();
        params.push((frag.rec_param.clone(), c.clone()));
        let derived = format!("{op}_derived");
        let arglist: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        let spec_call = {
            let mut a: Vec<String> = frag.others.iter().map(|(n, _)| n.clone()).collect();
            a.push(appc(&abs, &[frag.rec_param.clone()]));
            format!("{op}({})", a.join(", "))
        };
        let mut law_binders = params.clone();
        law_binders.push(("h0".to_string(), appc(&inv, &[frag.rec_param.clone()])));

        // -- phase 4: certificate emission --------------------------------
        let mut out = String::new();
        let mut fargs = vec![b.clone()];
        fargs.extend(steps.iter().cloned());
        fargs.push(frag.rec_param.clone());
        out.push_str(&format!(
            "fn {derived}({}) -> {} {{\n    {}\n}}\n\n",
            params.iter().map(|(n, t)| format!("{n}: {t}")).collect::<Vec<_>>().join(", "),
            frag.result,
            appc(&format!("{rec}::fold()"), &fargs)
        ));

        // The lemma §3.1 phase 4 did not name: the spec function agrees with
        // its own recursor unfolding. An induction, one arm at a time, each
        // recursive occurrence rewritten by an explicit `j` motive.
        let is_rec = format!("{op}_is_rec");
        let mut rec_args = vec![b.clone()];
        rec_args.extend(spec_steps.iter().cloned());
        let spec_rec_at = |x: &str| {
            let mut a = rec_args.clone();
            a.push(x.to_string());
            format!("{sr}({})", a.join(", "))
        };
        let mut lem_params: Vec<(String, String)> = frag.others.clone();
        lem_params.push(("x".to_string(), s.clone()));
        let lem_call = |x: &str| {
            let mut a: Vec<String> = frag.others.iter().map(|(n, _)| n.clone()).collect();
            a.push(x.to_string());
            format!("{is_rec}({})", a.join(", "))
        };
        let plain_call = |x: &str| {
            let mut a: Vec<String> = frag.others.iter().map(|(n, _)| n.clone()).collect();
            a.push(x.to_string());
            format!("{op}({})", a.join(", "))
        };
        let mut arms_src = String::new();
        for arm in &frag.arms {
            let pat = if arm.binders.is_empty() {
                arm.ctor.name.clone()
            } else {
                format!("{}({})", arm.ctor.name, arm.binders.join(", "))
            };
            let occ = self_calls(arm.body, op);
            let proof = arm_proof(arm, op, &occ, &spec_rec_at, &lem_call, &plain_call)
                .ok_or_else(|| {
                    format!("`{op}`'s `{}` arm is not a shape this round can spell", arm.ctor.name)
                })?;
            arms_src.push_str(&format!("        {pat} => {proof},\n"));
        }
        out.push_str(&format!(
            "theorem {is_rec}({}): {} = {} {{\n    match x {{\n{arms_src}    }}\n}}\n\n",
            lem_params.iter().map(|(n, t)| format!("{n}: {t}")).collect::<Vec<_>>().join(", "),
            spec_rec_at("x"),
            plain_call("x")
        ));

        // `fold_law` opens the anchor, the lemma closes it.
        let mut fl_args = vec![b.clone()];
        fl_args.extend(spec_steps.iter().cloned());
        fl_args.push(frag.rec_param.clone());
        fl_args.push("h0".to_string());
        let refines = format!("{op}_derived_refines");
        out.push_str(&format!(
            "theorem {refines}({}):\n    {} = {spec_call}\n{{\n    trans({},\n          {})\n}}\n\n",
            law_binders.iter().map(|(n, t)| format!("{n}: {t}")).collect::<Vec<_>>().join(", "),
            appc(&derived, &arglist),
            appc(&format!("{rec}::fold_law()"), &fl_args),
            lem_call(&appc(&abs, &[frag.rec_param.clone()]))
        ));
        out.push_str(&format!(
            "impl {op} for {repr} {{\n    body := {derived},\n    refines := {refines},\n}}\n"
        ));
        Ok(ReprEmission { op: op.to_string(), repr: repr.to_string(), text: out })
    }

    /// Phase 1 — eligibility. An honest syntactic predicate, not a soundness
    /// boundary (§3.1): everything it lets through is still kernel-checked.
    fn fragment<'a>(
        &self,
        op: &str,
        f: &'a Decl,
        s: &str,
        ctors: &'a [CtorView],
    ) -> Result<Fragment<'a>, String> {
        let Some(result) = spell_ty(&f.result) else {
            return Err(format!("`{op}`'s result type cannot be spelled"));
        };
        if result == s {
            return Err(format!(
                "`{op}` returns `{s}`, the repr'd type: a transfer whose result is \
                 repr-typed needs the image-law chain in its closing lemma, which is \
                 deferred (docs/datarepr-design.md §3.3, as-landed)"
            ));
        }
        let mut rec_param = None;
        let mut others = Vec::new();
        for p in &f.params {
            let Some(t) = spell_ty(&p.ty) else {
                return Err(format!("`{op}`'s parameter `{}` has an unspellable type", p.name));
            };
            if t == s {
                if rec_param.is_some() {
                    return Err(format!(
                        "`{op}` takes two parameters at `{s}`: v1 recurses on one \
                         (docs/datarepr-design.md §3.3, as-landed)"
                    ));
                }
                rec_param = Some(p.name.clone());
            } else {
                others.push((p.name.clone(), t));
            }
        }
        let Some(rec_param) = rec_param else {
            return Err(format!("`{op}` takes no parameter at `{s}`: nothing to transfer"));
        };
        // The body must be a bare `match` on the recursion parameter.
        if !f.body.stmts.is_empty() {
            return Err(format!("`{op}`'s body is not a bare `match`"));
        }
        let ExprKind::Match { scrut, arms, .. } = &f.body.result.kind else {
            return Err(format!(
                "`{op}`'s body is not a structural `match` on `{rec_param}`: outside the \
                 fragment (docs/datarepr-design.md §3.3)"
            ));
        };
        if !matches!(&scrut.kind, ExprKind::Var(v) if *v == rec_param) {
            return Err(format!("`{op}` does not match on its `{s}` parameter"));
        }
        if arms.len() != ctors.len() {
            return Err(format!(
                "`{op}`'s match has {} arms for {} constructors: the fragment needs a total \
                 match in declaration order",
                arms.len(),
                ctors.len()
            ));
        }
        let mut out = Vec::new();
        for (arm, ctor) in arms.iter().zip(ctors) {
            let (name, binders) = pattern_of(arm)
                .ok_or_else(|| format!("`{op}` has an arm this round cannot read"))?;
            if name != ctor.name {
                return Err(format!(
                    "`{op}`'s arms are not in declaration order: expected `{}`, found `{name}`",
                    ctor.name
                ));
            }
            if binders.len() != ctor.fields.len() {
                return Err(format!(
                    "`{op}`'s `{name}` arm binds {} of {} fields: the fragment binds all of \
                     them",
                    binders.len(),
                    ctor.fields.len()
                ));
            }
            let body = arm_body(arm)
                .ok_or_else(|| format!("`{op}`'s `{name}` arm has a body this round cannot read"))?;
            // Every self-call descends on a recursive child of *this* arm and
            // passes the other parameters through unchanged; anything else is
            // a recursion the fold cannot express.
            let recs: Vec<&str> = ctor
                .fields
                .iter()
                .enumerate()
                .filter(|(_, fl)| fl.rec)
                .map(|(i, _)| binders[i].as_str())
                .collect();
            // A recursive child is at the CARRIER on the repr side and at
            // `S` on the spec side, so it may only be reached through a
            // self-call — the one position the fold's accumulator stands in
            // for it. Using one directly would put a carrier value where the
            // spec body has a spec value; at the naive repr that is harmless
            // and at every other repr it is wrong, so it declines at both.
            for used in vars_outside_self_calls(body, op) {
                if recs.contains(&used.as_str()) {
                    return Err(format!(
                        "`{op}`'s `{name}` arm uses the recursive child `{used}` \
                         outside a self-call: only the recursion's result crosses to \
                         the repr side (docs/datarepr-design.md §3.3, as-landed)"
                    ));
                }
            }
            for sc in self_calls(body, op) {
                if !recs.contains(&sc.child.as_str()) {
                    return Err(format!(
                        "`{op}` calls itself on `{}`, which is not a recursive child of \
                         `{name}`: non-structural recursion is outside the fragment \
                         (docs/datarepr-design.md §3.3)",
                        sc.child
                    ));
                }
            }
            out.push(Arm { ctor, binders, body });
        }
        Ok(Fragment { rec_param, others, result, arms: out })
    }
}

/// Does this declaration mention the repr'd type anywhere in its signature?
/// A callee that does needs its own `Impl` to close a certificate step.
fn touches(d: &Decl, s: &str) -> bool {
    d.params.iter().any(|p| spell_ty(&p.ty).as_deref() == Some(s))
        || spell_ty(&d.result).as_deref() == Some(s)
}

/// Every global applied anywhere in an expression.
fn callees(e: &Expr) -> Vec<String> {
    let mut out = Vec::new();
    walk(e, &mut |x| {
        if let ExprKind::App { head, .. } = &x.kind {
            if let ExprKind::Var(n) = &head.kind {
                out.push(n.clone());
            }
        }
    });
    out
}

/// The self-calls of `op`, in the spelling walk's order — the order the
/// certificate's rewrite chain indexes.
fn self_calls(e: &Expr, op: &str) -> Vec<SelfCall> {
    let mut out = Vec::new();
    walk(e, &mut |x| {
        if let ExprKind::App { head, args, .. } = &x.kind {
            if matches!(&head.kind, ExprKind::Var(n) if n == op) {
                if let Some(last) = args.last() {
                    if let ExprKind::Var(v) = &last.kind {
                        out.push(SelfCall { child: v.clone() });
                    }
                }
            }
        }
    });
    out
}

/// Pre-order walk. Deliberately total over the shapes the fragment admits and
/// silent elsewhere: the spelling pass is what refuses an unreadable body, so
/// a shape missed here can never become a wrong emission, only a decline.
fn walk(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::App { head, args, .. } => {
            walk(head, f);
            for a in args {
                walk(a, f);
            }
        }
        ExprKind::TyApp { head, .. } => walk(head, f),
        ExprKind::Dot { recv, .. } => walk(recv, f),
        _ => {}
    }
}

/// Spell an arm body, replacing the `n`-th self-call by `sub[&n]`. `None` for
/// any shape outside the fragment — the emission is re-parsed, so a lossy
/// spelling would be a silently wrong artifact.
fn spell_with(e: &Expr, op: &str, sub: &HashMap<usize, String>) -> Option<String> {
    let mut n = 0;
    spell_go(e, op, sub, &mut n)
}

fn spell_go(
    e: &Expr,
    op: &str,
    sub: &HashMap<usize, String>,
    n: &mut usize,
) -> Option<String> {
    Some(match &e.kind {
        ExprKind::Var(v) => v.clone(),
        ExprKind::Num(k) => k.to_string(),
        ExprKind::App { head, args, .. } => {
            if matches!(&head.kind, ExprKind::Var(h) if h == op) {
                let i = *n;
                *n += 1;
                // The self-call's arguments are still walked, so that the
                // occurrence counter agrees with `self_calls`'s order.
                for a in args {
                    spell_go(a, op, sub, n)?;
                }
                return sub.get(&i).cloned();
            }
            let h = spell_go(head, op, sub, n)?;
            let mut a = Vec::new();
            for x in args {
                a.push(spell_go(x, op, sub, n)?);
            }
            if a.is_empty() {
                format!("{h}()")
            } else {
                format!("{h}({})", a.join(", "))
            }
        }
        ExprKind::Dot { recv, name, .. } => format!("{}.{name}", spell_go(recv, op, sub, n)?),
        _ => return None,
    })
}

/// One arm of the closing lemma's induction: rewrite each recursive
/// occurrence from the recursor's spelling to the spec function's, one
/// explicit `j` motive at a time.
///
/// `j` and not `cong`: the two sides differ inside the recursor's algebra
/// arguments, where anti-unification cannot find the function
/// (`issues/congruence-by-anti-unification.md` §3, confirmed by the hand-run).
fn arm_proof(
    arm: &Arm<'_>,
    op: &str,
    occ: &[SelfCall],
    spec_rec_at: &impl Fn(&str) -> String,
    lem_call: &impl Fn(&str) -> String,
    plain_call: &impl Fn(&str) -> String,
) -> Option<String> {
    if occ.is_empty() {
        return Some("refl".to_string());
    }
    // `state(k)` spells the arm with the first `k` occurrences already
    // rewritten to the spec function's side.
    let state = |k: usize| -> Option<String> {
        let mut sub = HashMap::new();
        for (i, sc) in occ.iter().enumerate() {
            sub.insert(
                i,
                if i < k { plain_call(&sc.child) } else { spec_rec_at(&sc.child) },
            );
        }
        spell_with(arm.body, op, &sub)
    };
    let mut steps: Vec<String> = Vec::new();
    for (k, sc) in occ.iter().enumerate() {
        let from = state(k)?;
        // The motive abstracts exactly the occurrence being rewritten.
        let mut sub = HashMap::new();
        for (i, s2) in occ.iter().enumerate() {
            sub.insert(
                i,
                if i < k {
                    plain_call(&s2.child)
                } else if i == k {
                    "y".to_string()
                } else {
                    spec_rec_at(&s2.child)
                },
            );
        }
        let motive = spell_with(arm.body, op, &sub)?;
        steps.push(format!(
            "j({}, \u{3bb} y q => {from} = {motive}, refl)",
            lem_call(&sc.child)
        ));
    }
    let mut proof = steps.pop().expect("non-empty");
    while let Some(s) = steps.pop() {
        proof = format!("trans({s}, {proof})");
    }
    Some(proof)
}

// -- reading the surface `match` --------------------------------------------

fn pattern_of(arm: &heather_syntax::Arm) -> Option<(String, Vec<String>)> {
    use heather_syntax::Pat;
    // A default arm stands for several constructors and binds nothing; the
    // fragment asks for them written out (§3.3 — an honest syntactic
    // predicate, so it declines rather than expanding).
    if arm.default {
        return None;
    }
    let mut bs = Vec::new();
    for b in &arm.binders {
        match b {
            Pat::Var { name, .. } => bs.push(name.clone()),
            Pat::Ctor { .. } => return None,
        }
    }
    Some((arm.ctor.clone(), bs))
}

fn arm_body(arm: &heather_syntax::Arm) -> Option<&Expr> {
    Some(&arm.body)
}

/// Every variable occurrence that is *not* the recursion argument of a
/// self-call. What the fragment checks its recursive binders against.
fn vars_outside_self_calls(e: &Expr, op: &str) -> Vec<String> {
    let mut out = Vec::new();
    go(e, op, &mut out);
    return out;

    fn go(e: &Expr, op: &str, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Var(v) => out.push(v.clone()),
            ExprKind::App { head, args, .. } => {
                if matches!(&head.kind, ExprKind::Var(h) if h == op) {
                    // The recursion argument is the one position a recursive
                    // child legitimately appears in.
                    for a in &args[..args.len().saturating_sub(1)] {
                        go(a, op, out);
                    }
                    return;
                }
                go(head, op, out);
                for a in args {
                    go(a, op, out);
                }
            }
            ExprKind::TyApp { head, .. } => go(head, op, out),
            ExprKind::Dot { recv, .. } => go(recv, op, out),
            _ => {}
        }
    }
}
