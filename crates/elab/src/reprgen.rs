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
//!
//! There are **two** closing-lemma shapes, chosen by the result type. When the
//! result is the repr'd type the fold's algebra lives at the carrier, so there
//! is no "the spec fn equals its recursor unfolding" to state — the recursor's
//! result is a repr value. The lemma is `abs` pushed through the image spine
//! instead, and it costs a third lemma: every commutation law demands `inv` at
//! its recursive arguments, and the fold's accumulator satisfies `inv` only by
//! an induction of its own (§3.3's second as-landed note).

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
    /// At a **repr-typed result** only: the body read as an image spine, which
    /// is what both extra lemmas recurse over. `None` when the result is not
    /// repr-typed, where the body is spelled directly instead.
    spine: Option<Spine>,
}

/// An arm body whose value is at the repr'd type: a spine of `S`-constructor
/// nodes whose recursive positions bottom out in the recursion's own results.
/// The repr side reads it with the constructor *images* and the accumulator;
/// the spec side reads it with the constructors and the spec function; the two
/// closing lemmas walk it in step.
enum Spine {
    /// The result of the recursion on this child — the fold's accumulator.
    Acc(String),
    /// `C(…)`, at `ctors[i]`.
    Node(usize, Vec<SArg>),
}

enum SArg {
    /// A non-recursive field, spelled once and identical on both sides.
    NonRec(String),
    Rec(Spine),
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
    /// *All* parameters in declaration order, the recursion one spelled at
    /// `S`. Calls to `f` are built from this and not from `others + rec`: the
    /// `S` parameter need not be the last one, and the `Impl` record restates
    /// the signature in declaration order.
    params: Vec<(String, String)>,
    /// The result type, spelled. `S` itself is the repr-typed-result case,
    /// which takes the second closing-lemma shape (§3.3, as-landed).
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
        // The result at `S` is the repr-typed case: the fold's algebra lives at
        // the *carrier*, so `B` is the carrier and the closing lemma is `abs`
        // pushed through the image spine rather than the spec fn's recursor
        // unfolding (§3.3, as-landed).
        let res_is_spec = frag.result == *s;
        let b = if res_is_spec { c.clone() } else { frag.result.clone() };
        let b = &b;

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
            let slot = |child: &str| {
                let k = recs.iter().position(|r| *r == child).expect("checked in `fragment`");
                format!("b{k}")
            };
            let body = if let Some(sp) = &arm.spine {
                // The repr side of the spine: constructor images, and the
                // accumulator where the recursion's result belongs.
                Spelling { ctors: rp.ctors.as_slice(), rec, abs: &abs, acc: &slot }.repr(sp)
            } else {
                let mut sub: HashMap<usize, String> = HashMap::new();
                for (n, sc) in occ.iter().enumerate() {
                    sub.insert(n, slot(&sc.child));
                }
                let Some(body) = spell_with(arm.body, op, &sub) else {
                    return Err(format!(
                        "`{op}`'s `{}` arm is not a shape this round can spell: an arm is an \
                         application over its binders, the other parameters, self-calls on a \
                         recursive child, and globals that do not touch `{s}`",
                        arm.ctor.name
                    ));
                };
                body
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
        //
        // The signature restated with `S ↦ R`, in declaration order — the same
        // order the `Impl` record restates it in.
        let params: Vec<(String, String)> = frag
            .params
            .iter()
            .map(|(n, t)| {
                (n.clone(), if *n == frag.rec_param { c.clone() } else { t.clone() })
            })
            .collect();
        let derived = format!("{op}_derived");
        let arglist: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        // A call to `f` itself, with `x` at the recursion parameter's position.
        let plain_call = |x: &str| {
            let a: Vec<String> = frag
                .params
                .iter()
                .map(|(n, _)| if *n == frag.rec_param { x.to_string() } else { n.clone() })
                .collect();
            format!("{op}({})", a.join(", "))
        };
        let spec_call = plain_call(&appc(&abs, &[frag.rec_param.clone()]));
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
            if res_is_spec { c } else { &frag.result },
            appc(&format!("{rec}::fold()"), &fargs)
        ));

        let mut rec_args = vec![b.clone()];
        rec_args.extend(spec_steps.iter().cloned());
        let spec_rec_at = |x: &str| {
            let mut a = rec_args.clone();
            a.push(x.to_string());
            format!("{sr}({})", a.join(", "))
        };
        // Every closing lemma quantifies over the non-recursion parameters and
        // the spec value it inducts on.
        let mut lem_params: Vec<(String, String)> = frag.others.clone();
        lem_params.push(("x".to_string(), s.clone()));
        let lem_params_src =
            lem_params.iter().map(|(n, t)| format!("{n}: {t}")).collect::<Vec<_>>().join(", ");
        let lem_at = |name: &str, x: &str| {
            let mut a: Vec<String> = frag.others.iter().map(|(n, _)| n.clone()).collect();
            a.push(x.to_string());
            format!("{name}({})", a.join(", "))
        };
        let pat_of = |arm: &Arm<'_>| {
            if arm.binders.is_empty() {
                arm.ctor.name.clone()
            } else {
                format!("{}({})", arm.ctor.name, arm.binders.join(", "))
            }
        };
        // The anchor law at this transfer, which both routes open with.
        let mut fl_args = vec![b.clone()];
        fl_args.extend(spec_steps.iter().cloned());
        fl_args.push(frag.rec_param.clone());
        fl_args.push("h0".to_string());
        let fold_law = appc(&format!("{rec}::fold_law()"), &fl_args);
        let law_binders_src =
            law_binders.iter().map(|(n, t)| format!("{n}: {t}")).collect::<Vec<_>>().join(", ");
        let refines = format!("{op}_derived_refines");

        if !res_is_spec {
            // The lemma §3.1 phase 4 did not name: the spec function agrees
            // with its own recursor unfolding. An induction, one arm at a
            // time, each recursive occurrence rewritten by an explicit `j`
            // motive.
            let is_rec = format!("{op}_is_rec");
            let lem_call = |x: &str| lem_at(&is_rec, x);
            let mut arms_src = String::new();
            for arm in &frag.arms {
                let occ = self_calls(arm.body, op);
                let proof = arm_proof(arm, op, &occ, &spec_rec_at, &lem_call, &plain_call)
                    .ok_or_else(|| {
                        format!(
                            "`{op}`'s `{}` arm is not a shape this round can spell",
                            arm.ctor.name
                        )
                    })?;
                arms_src.push_str(&format!("        {} => {proof},\n", pat_of(arm)));
            }
            out.push_str(&format!(
                "theorem {is_rec}({lem_params_src}): {} = {} {{\n    match x {{\n{arms_src}    }}\n}}\n\n",
                spec_rec_at("x"),
                plain_call("x")
            ));

            // `fold_law` opens the anchor, the lemma closes it.
            out.push_str(&format!(
                "theorem {refines}({law_binders_src}):\n    {} = {spec_call}\n{{\n    trans({fold_law},\n          {})\n}}\n\n",
                appc(&derived, &arglist),
                lem_call(&appc(&abs, &[frag.rec_param.clone()]))
            ));
            out.push_str(&format!(
                "impl {op} for {repr} {{\n    body := {derived},\n    refines := {refines},\n}}\n"
            ));
            return Ok(ReprEmission { op: op.to_string(), repr: repr.to_string(), text: out });
        }

        // -- the repr-typed result (§3.3, as-landed) ----------------------
        //
        // The fold's algebra is at the carrier, so there is no "the spec fn
        // equals its recursor unfolding" to state: the recursor's result is a
        // *repr* value. The closing lemma is `abs` pushed through the image
        // spine instead, and it needs `inv` at every recursive argument of
        // every commutation law — which the accumulator satisfies only by an
        // induction of its own. Three lemmas, in dependency order.
        let inv_pres = format!("{op}_inv_pres");
        let abs_alg = format!("{op}_abs_alg");
        let acc_repr = |child: &str| spec_rec_at(child);
        let sp_ctx =
            Spelling { ctors: rp.ctors.as_slice(), rec, abs: &abs, acc: &acc_repr };
        let acc_inv = |child: &str| lem_at(&inv_pres, child);
        let acc_abs = |child: &str| lem_at(&abs_alg, child);

        // Third lemma: the fold's accumulator satisfies `inv`. At `inv = True`
        // every arm is an image closure law applied to `refl`s and the lemma
        // says nothing; at a canonical-form `inv` it is what the commutation
        // laws below are paid with.
        let mut arms_src = String::new();
        for arm in &frag.arms {
            let sp = arm.spine.as_ref().expect("a repr-typed result has a spine");
            arms_src.push_str(&format!(
                "        {} => {},\n",
                pat_of(arm),
                sp_ctx.inv_proof(sp, &acc_inv)
            ));
        }
        out.push_str(&format!(
            "theorem {inv_pres}({lem_params_src}): {} {{\n    match x {{\n{arms_src}    }}\n}}\n\n",
            appc(&inv, &[spec_rec_at("x")])
        ));

        // Second closing-lemma shape: one commutation law per constructor
        // node, a `j` chain over the recursive argument positions.
        let mut arms_src = String::new();
        for arm in &frag.arms {
            let sp = arm.spine.as_ref().expect("a repr-typed result has a spine");
            arms_src.push_str(&format!(
                "        {} => {},\n",
                pat_of(arm),
                sp_ctx.abs_proof(sp, &acc_inv, &acc_abs, &plain_call)
            ));
        }
        out.push_str(&format!(
            "theorem {abs_alg}({lem_params_src}): {} = {} {{\n    match x {{\n{arms_src}    }}\n}}\n\n",
            appc(&abs, &[spec_rec_at("x")]),
            plain_call("x")
        ));

        // `refines` at a repr-typed result is `abs(body(x̄)) = f(⟦x̄⟧)`
        // (§1.2). The congruence that carries `abs` over the anchor law is an
        // explicit `j` motive, for §3.1 correction 2's reason.
        let derived_call = appc(&derived, &arglist);
        out.push_str(&format!(
            "theorem {refines}({law_binders_src}):\n    {} = {spec_call}\n{{\n    \
             trans(j({fold_law},\n            \u{3bb} y q => {} = {}, refl),\n          {})\n}}\n\n",
            appc(&abs, &[derived_call.clone()]),
            appc(&abs, &[derived_call.clone()]),
            appc(&abs, &["y".to_string()]),
            lem_at(&abs_alg, &appc(&abs, &[frag.rec_param.clone()]))
        ));
        // …and the second half of §1.2's conclusion: an implementation that
        // *builds* a repr owes `inv` of what it built. The anchor law carries
        // the third lemma back across it.
        let refines_inv = format!("{op}_derived_inv");
        out.push_str(&format!(
            "theorem {refines_inv}({law_binders_src}):\n    {}\n{{\n    \
             j(sym({fold_law}),\n      \u{3bb} y q => {}, {})\n}}\n\n",
            appc(&inv, &[derived_call]),
            appc(&inv, &["y".to_string()]),
            lem_at(&inv_pres, &appc(&abs, &[frag.rec_param.clone()]))
        ));
        out.push_str(&format!(
            "impl {op} for {repr} {{\n    body := {derived},\n    refines := {refines},\n    \
             refines_inv := {refines_inv},\n}}\n"
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
        let res_is_spec = result == s;
        let mut rec_param = None;
        let mut others = Vec::new();
        let mut params = Vec::new();
        for p in &f.params {
            let Some(t) = spell_ty(&p.ty) else {
                return Err(format!("`{op}`'s parameter `{}` has an unspellable type", p.name));
            };
            params.push((p.name.clone(), t.clone()));
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
            // At a repr-typed result the arm's *value* is at `S`, and the two
            // closing lemmas walk it as an image spine: constructor nodes down
            // to the recursion's own results. Anything else — a global
            // returning `S`, a bare binder — is outside the fragment.
            let spine = if res_is_spec {
                Some(spine_of(body, op, ctors).ok_or_else(|| {
                    format!(
                        "`{op}`'s `{name}` arm is not an image spine: with the result at \
                         `{s}` an arm is `{s}`'s constructors applied down to self-calls on \
                         a recursive child (docs/datarepr-design.md §3.3, as-landed)"
                    )
                })?)
            } else {
                None
            };
            out.push(Arm { ctor, binders, body, spine });
        }
        Ok(Fragment { rec_param, others, params, result, arms: out })
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

/// Read an arm body as an image spine, or decline. Only reachable at a
/// repr-typed result, where the arm's value is a constructor of `S`.
fn spine_of(e: &Expr, op: &str, ctors: &[CtorView]) -> Option<Spine> {
    match &e.kind {
        // A constructor with no fields is a bare name, not an application.
        ExprKind::Var(v) => {
            let i = ctors.iter().position(|c| c.name == *v && c.fields.is_empty())?;
            Some(Spine::Node(i, Vec::new()))
        }
        ExprKind::App { head, args, .. } => {
            let ExprKind::Var(h) = &head.kind else { return None };
            if h == op {
                // The recursion's result on this child — the accumulator.
                let ExprKind::Var(v) = &args.last()?.kind else { return None };
                return Some(Spine::Acc(v.clone()));
            }
            let i = ctors.iter().position(|c| c.name == *h)?;
            if ctors[i].fields.len() != args.len() {
                return None;
            }
            let mut out = Vec::new();
            for (fld, a) in ctors[i].fields.iter().zip(args) {
                out.push(if fld.rec {
                    SArg::Rec(spine_of(a, op, ctors)?)
                } else {
                    // A non-recursive field is ordinary data: spelled once,
                    // identical on both sides. A self-call inside one is not
                    // spellable (no accumulator stands for it), so it declines.
                    SArg::NonRec(spell_with(a, op, &HashMap::new())?)
                });
            }
            Some(Spine::Node(i, out))
        }
        _ => None,
    }
}

/// Spelling an image spine, and the two proofs that walk it. The `acc` closure
/// says what the recursion's result on a child *is* on the repr side: the
/// fold's accumulator inside the derived body, the spec recursor at that child
/// inside the lemmas.
struct Spelling<'a> {
    ctors: &'a [CtorView],
    /// The generated record, whose namespace holds the images and their laws.
    rec: &'a str,
    abs: &'a str,
    acc: &'a dyn Fn(&str) -> String,
}

impl Spelling<'_> {
    /// The spine at the carrier: constructor images over the accumulator.
    fn repr(&self, sp: &Spine) -> String {
        match sp {
            Spine::Acc(child) => (self.acc)(child),
            Spine::Node(i, args) => {
                let c = &self.ctors[*i];
                let a: Vec<String> = args.iter().map(|x| self.arg(x, &|sp| self.repr(sp))).collect();
                appc(&format!("{}::mk_{}()", self.rec, c.name), &a)
            }
        }
    }

    /// The same spine at the spec type: constructors over the spec function.
    fn spec(&self, sp: &Spine, acc_spec: &dyn Fn(&str) -> String) -> String {
        match sp {
            Spine::Acc(child) => acc_spec(child),
            Spine::Node(i, args) => {
                let c = &self.ctors[*i];
                let a: Vec<String> =
                    args.iter().map(|x| self.arg(x, &|sp| self.spec(sp, acc_spec))).collect();
                ctor_app(&c.name, &a)
            }
        }
    }

    fn arg(&self, a: &SArg, f: &dyn Fn(&Spine) -> String) -> String {
        match a {
            SArg::NonRec(t) => t.clone(),
            SArg::Rec(sp) => f(sp),
        }
    }

    /// `inv` of the spine's repr side: each node's closure law applied to the
    /// `inv` proofs of its recursive arguments, bottoming out in the
    /// `inv`-preservation lemma at the accumulator.
    fn inv_proof(&self, sp: &Spine, acc_inv: &dyn Fn(&str) -> String) -> String {
        match sp {
            Spine::Acc(child) => acc_inv(child),
            Spine::Node(i, args) => {
                let c = &self.ctors[*i];
                let a: Vec<String> = args.iter().map(|x| self.arg(x, &|sp| self.repr(sp))).collect();
                let mut app = appc(&format!("{}::{}_inv()", self.rec, c.name), &a);
                for sp in rec_args(args) {
                    app = appc(&app, &[self.inv_proof(sp, acc_inv)]);
                }
                app
            }
        }
    }

    /// `abs` pushed through the spine: at each node the commutation law, then
    /// one `j` step per recursive position rewriting `abs(child)` to the spec
    /// function's value there. Explicit motives, for §3.1 correction 2's
    /// reason — the sides differ inside the recursor's algebra arguments.
    fn abs_proof(
        &self,
        sp: &Spine,
        acc_inv: &dyn Fn(&str) -> String,
        acc_abs: &dyn Fn(&str) -> String,
        acc_spec: &dyn Fn(&str) -> String,
    ) -> String {
        let (i, args) = match sp {
            Spine::Acc(child) => return acc_abs(child),
            Spine::Node(i, args) => (*i, args),
        };
        let c = &self.ctors[i];
        let a: Vec<String> = args.iter().map(|x| self.arg(x, &|sp| self.repr(sp))).collect();
        let mut proof = appc(&format!("{}::{}_abs()", self.rec, c.name), &a);
        let recs = rec_args(args);
        for sp in &recs {
            proof = appc(&proof, &[self.inv_proof(sp, acc_inv)]);
        }
        // `side(k, y)`: the spec-side node with the first `k` recursive
        // positions already rewritten, and position `k` shown as `y` when a
        // motive is being spelled.
        let side = |k: usize, y: Option<&str>| -> String {
            let mut rank = 0;
            let a: Vec<String> = args
                .iter()
                .map(|x| match x {
                    SArg::NonRec(t) => t.clone(),
                    SArg::Rec(sp) => {
                        let r = rank;
                        rank += 1;
                        match (r.cmp(&k), y) {
                            (std::cmp::Ordering::Less, _) => self.spec(sp, acc_spec),
                            (std::cmp::Ordering::Equal, Some(y)) => y.to_string(),
                            _ => appc(self.abs, &[self.repr(sp)]),
                        }
                    }
                })
                .collect();
            ctor_app(&c.name, &a)
        };
        for (k, sp) in recs.iter().enumerate() {
            proof = format!(
                "trans({proof}, j({}, \u{3bb} y q => {} = {}, refl))",
                self.abs_proof(sp, acc_inv, acc_abs, acc_spec),
                side(k, None),
                side(k, Some("y"))
            );
        }
        proof
    }
}

fn rec_args(args: &[SArg]) -> Vec<&Spine> {
    args.iter()
        .filter_map(|a| if let SArg::Rec(sp) = a { Some(sp) } else { None })
        .collect()
}

/// `C` or `C(a, b)` — a constructor is applied n-ary, unlike a record field.
fn ctor_app(name: &str, args: &[String]) -> String {
    if args.is_empty() {
        name.to_string()
    } else {
        format!("{name}({})", args.join(", "))
    }
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
