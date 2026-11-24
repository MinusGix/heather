//! Declarations' part of the elaborator: the readings a declaration's head and recursion plan need.

use std::collections::HashMap;

use heather_kernel::typing;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::subst::GlobalSubst;
use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalRef, GlobalVar, LocalCtx, LocalSubst, LocalVar, Term, Type};

use heather_syntax::{Decl, DeclKind, Expr, ExprKind, InstanceDecl, MatchForm, Span, Ty, TyKind};

use crate::{
    Elaborator, IMPLICIT_MARK_REFUSED, PendingDecl, R, TopAttempt, application, base_name, branch_equations, function_induction, datarepr,
    emission_walk, err, gate, inductive, loops, meaning, measure, names, partial, pool, recursion,
    recursion_at_top_hoisted, sealing, statements, stats,
};
use crate::application::{ParamMeta, has_implicit_mark, skel_of_ty};
use crate::codata::Codata;
use crate::context::{Cx, DictBinder, TyVar};
use crate::defaults::Defaults;
use crate::diagnostics::ElabError;
use crate::dispatch::{Carriers, Operators};
use crate::interfaces::{InterfaceDefs, InterfaceDefsMut};
use crate::lint::Lint;
use crate::meaning::{Meaning, MeaningMut};
use crate::module_delta::DeltasMut;
use crate::name_lookup::NameLookup;
use crate::names::{GlobalRegistration, NameKind, NameRes, qkey, split_qual};
use crate::quote::QuotationMut;
use crate::recursion::SelfRef;
use crate::refusals::Refusals;
use crate::resolve::{Resolution, ResolutionMut};
use crate::surface::{count_holes, count_tactic_slots};
use crate::traits::Classes;

/// Declarations' part of the elaborator: the readings a declaration's head and recursion plan need.
pub(crate) struct Declarations<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Declarations<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

/// Declarations' part of the elaborator that writes: elaborating, checking and committing one declaration.
pub(crate) struct DeclarationsMut<'e>(pub(crate) &'e mut Elaborator);

impl std::ops::Deref for DeclarationsMut<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl std::ops::DerefMut for DeclarationsMut<'_> {
    fn deref_mut(&mut self) -> &mut Elaborator {
        self.0
    }
}

impl DeclarationsMut<'_> {
    /// A declaration an `instance` synthesizes: its qualified name is the
    /// instance's, not a member of a type or function, so its body names no
    /// siblings (docs/language/sections-design.md §6).
    pub(crate) fn elab_decl_unowned(&mut self, decl: &Decl) -> R<()> {
        self.elab_decl_as(decl, None)
    }

    pub(crate) fn elab_decl_as(&mut self, decl: &Decl, owner: Option<String>) -> R<()> {
        // The induction principles the declaration's `induct` steps and
        // `f::induct` references name, built first (`demand_principles`).
        self.demand_principles(decl);
        self.scoped(|s| &mut s.member_owner, owner, |me| {
            DeclarationsMut(me).elab_decl_owned(decl)?;
            // A definition's own equations, one per branch of the test its
            // body is (`branch_equations`): beside every `fn` that has one,
            // so a proof cites `f::True` and never restates `f`.
            if decl.decreases.is_none() && decl.partial.is_none() && branch_equations::candidate(decl) && !loops::has_loop(decl) {
                let self_name = base_name(&decl.name).to_string();
                // A recursion's equations and principle are built on demand
                // (`demand_principles`): most recursive functions are never
                // proved about by induction, and the generators' are large.
                // One lowered by a measure was recorded by that route.
                if branch_equations::recursive(decl, &self_name) {
                    if decl.kind == DeclKind::Fn && !me.pass.recursions.borrow().contains_key(&decl.name) {
                        me.pass.recursions.borrow_mut().insert(decl.name.clone(), (Rc::new(decl.clone()), branch_equations::Recursion::Structural));
                    }
                } else {
                    DeclarationsMut(me).elab_branch_equations(decl, branch_equations::Recursion::None, true);
                }
            }
            Ok(())
        })
    }

    /// `f::True`, `f::False`, … (`branch_equations`), after `f`. Never an
    /// error: the generator is untrusted, so an equation the checker refuses
    /// leaves `f` as it is, with the reason recorded under the designed
    /// spelling for a reference to report. A condition read as a `Bool`
    /// where it is not a proposition (`if xs.is_empty()`) is tried second,
    /// as the elaborator tries it.
    /// Returns the equations built, which are designated only where
    /// `designate` says so: a recursion's principle (`function_induction`)
    /// is elaborated from them first, and spells them by their minted names.
    fn elab_branch_equations(&mut self, decl: &Decl, recursion: branch_equations::Recursion, designate: bool) -> Option<Vec<branch_equations::BranchEquation>> {
        // The equations spell what they are proved from by qualified name,
        // which a module reaches through its import closure
        // (issues/branch-equations-silent-without-logic.md); one that does
        // not reach them is told which import builds them.
        let needs = ["bool::Bool::convoy_true", "bool::Bool::picked_true", "bool::decide_bit_of", "bool::decide_bit_of_not", "logic::False"];
        if let Some(missing) = needs.iter().find(|n| !matches!(NameLookup(self).resolve_declared(n), NameRes::Found(_))) {
            let module = missing.split("::").next().unwrap_or(missing);
            let why = format!("`{missing}` is not reached from this module: `import {module};`");
            for name in branch_equations::head_names(decl) {
                self.pass.unfold_refusals.borrow_mut().entry(name).or_insert_with(|| why.clone());
            }
            return None;
        }
        let self_name = base_name(&decl.name).to_string();
        let warn_mark = self.pass.warnings.borrow().len();
        let mut why = String::new();
        // A reading through matches on results (`branch_equations::
        // Walk::result_arms`) that the checker refuses is tried again
        // without them, so a function keeps the equations it had; the
        // refusal is recorded under the names only that reading has.
        let mut refused_results: Option<(Vec<String>, String)> = None;
        let attempts = [
            (branch_equations::Reading::Proposition, true),
            (branch_equations::Reading::Proposition, false),
            (branch_equations::Reading::Bool, true),
            (branch_equations::Reading::Bool, false),
        ];
        for (reading, with_results) in attempts {
            if !with_results && refused_results.as_ref().is_none_or(|(_, r)| r.is_empty()) {
                continue;
            }
            let fields = |ty: &Ty, ctor: &str| -> Option<Vec<(Option<String>, Ty)>> {
                let base = ctor.rsplit("::").next().unwrap_or(ctor);
                let nat = |span| Ty { kind: TyKind::Nat, span };
                let named = match &ty.kind {
                    TyKind::Nat => None,
                    TyKind::Named { name, args } if !(args.is_empty() && (name == "Nat" || name == "nat::Nat")) => Some((name, args)),
                    TyKind::Named { .. } => None,
                    _ => return None,
                };
                let Some((name, args)) = named else {
                    return match base {
                        "Zero" => Some(Vec::new()),
                        "Succ" => Some(vec![(None, nat(ty.span))]),
                        _ => None,
                    };
                };
                let ind = self.lookup_inductive(name)?;
                if ind.codata || ind.index.is_some() || ind.skel.is_some() || !ind.valparams.is_empty() || ind.params.len() != args.len() {
                    return None;
                }
                let ctor = ind.ctors.iter().find(|c| c.name.rsplit("::").next() == Some(base))?;
                let at: Vec<(String, Ty)> = ind.params.iter().cloned().zip(args.iter().cloned()).collect();
                Some(ctor.fields.iter().map(|(n, t)| (n.clone(), measure::instantiate_ty(t, &at))).collect())
            };
            // A matched term that is not a parameter (a call's result) is
            // typed by the elaborator over the binders on the way, the
            // answer spelled and checked (`infer_local`).
            let elab: &Elaborator = self.0;
            let results = |e: &Expr, known: &[(String, Ty)]| -> Option<Ty> {
                let scope: Vec<measure::Binder> = known.iter().map(|(n, t)| measure::Binder { name: n.clone(), ty: Some(t.clone()), value: None }).collect();
                measure::BinderTys::infer_local(elab, decl, &[], &scope, e)
            };
            let results: Option<branch_equations::ScrutTypes<'_>> = if with_results { Some(&results) } else { None };
            let equations = match branch_equations::branch_equations(decl, &self_name, reading, &fields, results, recursion) {
                Ok(e) => e,
                // Read without the results there is nothing to read: the
                // refusal of the reading with them is the one to report,
                // and the next reading may still read them.
                Err(_) if !with_results && refused_results.take().is_some() => continue,
                Err(e) => {
                    why = e;
                    break;
                }
            };
            let built = self.session_transaction(|me| {
                for eq in &equations {
                    // A function that does not recur had its equations built
                    // with it; its case principle, asked for later, reads them.
                    if recursion == branch_equations::Recursion::None && !designate
                        && matches!(NameLookup(me).resolve_declared(&eq.decl.name), NameRes::Found(_))
                    {
                        continue;
                    }
                    me.elab_decl_one(&eq.decl, None).map_err(|e| {
                        ElabError::Elab { msg: format!("the generated `{}` was refused ({e})", eq.designed), span: eq.decl.span }
                    })?;
                }
                Ok(())
            });
            self.pass.warnings.borrow_mut().truncate(warn_mark);
            let read_results = equations.iter().any(|eq| eq.path.iter().any(|s| matches!(s.test, branch_equations::PathTest::Result { .. })));
            match built {
                Ok(()) => {
                    if designate {
                        self.designate_equations(&equations);
                    }
                    if let Some((names, why)) = refused_results.take() {
                        for name in names.into_iter().filter(|n| !equations.iter().any(|eq| &eq.designed == n)) {
                            self.pass.unfold_refusals.borrow_mut().insert(name, why.clone());
                        }
                    }
                    return Some(equations);
                }
                Err(e) if read_results => {
                    refused_results = Some((equations.iter().map(|eq| eq.designed.clone()).collect(), e.to_string()));
                    if why.is_empty() {
                        why = e.to_string();
                    }
                }
                // The proposition reading's refusal is the one to report: the
                // `Bool` reading is a fallback for conditions that are not one.
                Err(e) if why.is_empty() => why = e.to_string(),
                Err(_) => {}
            }
            if !with_results {
                refused_results = None;
            }
        }
        for name in branch_equations::head_names(decl) {
            self.pass.unfold_refusals.borrow_mut().insert(name, why.clone());
        }
        None
    }

    fn designate_equations(&mut self, equations: &[branch_equations::BranchEquation]) {
        for eq in equations {
            let free = match self.access_alias(&eq.designed) {
                Some(minted) => minted == eq.decl.name,
                None => !matches!(NameLookup(self).resolve_declared(&eq.designed), NameRes::Found(_)),
            };
            if free {
                self.designate_access(&eq.designed, &eq.decl.name);
            }
        }
    }

    /// A recursive `fn`'s branch equations and its induction principle
    /// `f::induct` (`function_induction`), both from the tests its body is.
    /// Never an error: what the checker refuses is recorded under the
    /// designed spelling for a reference to report.
    /// `f::induct` and the equations it is proved from, for every `f` the
    /// declaration does induction along (`induct f(…)`, or `f::induct`
    /// named), built before it the first time one is asked for
    /// (docs/tactics/functional-induction-design.md §6). Built in the
    /// module that asks, where `f` is declared or imported; a later
    /// declaration, or an importer, finds it by its designed name. A
    /// function that has none gets the reason recorded once, for the step
    /// to report.
    fn demand_principles(&mut self, decl: &Decl) {
        let mut heads: Vec<String> = Vec::new();
        // The heads an `induct` or an `f::induct` names, whose refusal is
        // reported; an equation's path asks only of a recorded recursion.
        let mut asked: Vec<String> = Vec::new();
        let mut note = |e: &Expr| {
            let head = match &e.kind {
                ExprKind::App { head, args, .. } => match &head.kind {
                    ExprKind::Var(n) if n == heather_syntax::INDUCT_ALL_GOALS || n == heather_syntax::INDUCT_CASES => {
                        let call = match args.first().map(|a| &a.kind) {
                            Some(ExprKind::Match { scrut, .. }) => Some(&**scrut),
                            _ => args.first(),
                        };
                        call.and_then(|c| c.as_named()).map(|(h, _, _)| {
                            if !asked.iter().any(|a| a == h) {
                                asked.push(h.to_string());
                            }
                            h.to_string()
                        })
                    }
                    _ => None,
                },
                // `f::induct`, or a branch equation `f::True`, `f::Cons`,
                // `f::Seq::Some` (every arm on the path is capitalized): a
                // structural recursion's are built with its principle.
                ExprKind::Var(n) => n.rsplit_once("::")
                    .filter(|(_, last)| *last == "induct" || last.starts_with(char::is_uppercase))
                    .map(|(f, last)| {
                        if last == "induct" && !asked.iter().any(|a| a == f) {
                            asked.push(f.to_string());
                        }
                        let mut f = f;
                        if last != "induct" {
                            while let Some((g, arm)) = f.rsplit_once("::")
                                && arm.starts_with(char::is_uppercase)
                                && g.rsplit("::").next().is_some_and(|s| !s.starts_with(char::is_uppercase))
                            {
                                f = g;
                            }
                        }
                        f.to_string()
                    }),
                _ => None,
            };
            if let Some(h) = head && !heads.contains(&h) {
                heads.push(h);
            }
        };
        for st in &decl.body.stmts {
            match st {
                heather_syntax::ast::Stmt::Let { expr, .. }
                | heather_syntax::ast::Stmt::LetRecord { expr, .. }
                | heather_syntax::ast::Stmt::LetCode { expr, .. } => crate::surface::walk_expr(expr, &mut note),
            }
        }
        crate::surface::walk_expr(&decl.body.result, &mut note);
        decl.body.ons.iter().for_each(|o| crate::surface::walk_expr(&o.expr, &mut note));
        for head in heads {
            let designed = format!("{head}::induct");
            let lookup = NameLookup(self);
            if lookup.key_of_kinds(&designed, crate::names::ANY_KIND).is_some() || self.pass.unfold_refusals.borrow().contains_key(&designed) {
                continue;
            }
            let Some((module, base)) = lookup.key_of_kinds(&head, crate::names::ANY_KIND)
                .and_then(|key| crate::names::split_qual(&key).map(|(m, b)| (m.to_string(), b.to_string()))) else { continue };
            // This module's own recursion, as recorded; an imported one, as
            // its module's image keeps it. A structural function's stored
            // declaration is the one written (a `decreases` loop's is its
            // lowering, and it built its principle with itself), so the
            // importer builds the principle from it, as the function's own
            // module would have.
            let recorded = if module == self.names.module() {
                self.pass.recursions.borrow().get(&base).cloned()
                    .or_else(|| asked.contains(&head).then(|| self.cases_only(&module, &base)).flatten())
            } else {
                self.names.surface_decl_in(&module, &base).filter(|f| {
                    f.kind == DeclKind::Fn && f.decreases.is_none() && f.partial.is_none() && branch_equations::candidate(f)
                        && !loops::has_loop(f) && branch_equations::recursive(f, base_name(&f.name))
                }).map(|f| (Rc::new(f.clone()), branch_equations::Recursion::Structural))
                    .or_else(|| asked.contains(&head).then(|| self.cases_only(&module, &base)).flatten())
            };
            // A path that only looked like an equation (`Nat::Succ`) names
            // no recursion and asks for nothing.
            if recorded.is_none() && !asked.contains(&head) {
                continue;
            }
            let Some((function, recursion)) = recorded else {
                self.pass.unfold_refusals.borrow_mut().insert(designed, format!("`{head}` is not a recursive function whose body is a tree of tests"));
                continue;
            };
            let owner = function.name.rsplit_once("::").map(|(owner, _)| owner.to_string());
            self.scoped(|s| &mut s.member_owner, owner, |me| DeclarationsMut(me).elab_recursion_equations(&function, recursion));
            // Asked for under a designed name (a loop's `f::step`), the
            // principle is reached under that name too.
            let built = format!("{}::induct", function.name);
            if built != designed {
                if let Some(target) = self.access_alias(&built).map(str::to_string) {
                    self.designate_access(&designed, &target);
                } else {
                    let why = self.pass.unfold_refusals.borrow().get(&built).cloned();
                    if let Some(why) = why {
                        self.pass.unfold_refusals.borrow_mut().insert(designed.clone(), why);
                    }
                }
            }
        }
    }

    /// A function that does not recur and whose body is a tree of tests:
    /// `induct f(…)` follows its cases (a loop's step,
    /// docs/language/loop-combinator-design.md §4).
    fn cases_only(&self, module: &str, base: &str) -> Option<(Rc<Decl>, branch_equations::Recursion)> {
        // A designed name (`f::step`) stands for its minted declaration.
        let minted = self.access_alias(base).map(str::to_string);
        let base = minted.as_deref().unwrap_or(base);
        self.names.surface_decl_in(module, base).filter(|f| {
            f.kind == DeclKind::Fn && f.decreases.is_none() && f.partial.is_none() && branch_equations::candidate(f)
                && !loops::has_loop(f) && !branch_equations::recursive(f, base_name(&f.name))
        }).map(|f| (Rc::new(f.clone()), branch_equations::Recursion::None))
    }

    fn elab_recursion_equations(&mut self, decl: &Decl, recursion: branch_equations::Recursion) {
        let designed = format!("{}::induct", decl.name);
        let self_name = base_name(&decl.name).to_string();
        // The calls a principle follows are read as calls, as the measure
        // route reads them.
        let normalized;
        let decl = if recursion == branch_equations::Recursion::Structural {
            match measure::method_calls_as_calls(&measure::deshadowed(decl), &self_name, self.0) {
                Ok(d) => {
                    normalized = d;
                    &normalized
                }
                Err(e) => {
                    self.pass.unfold_refusals.borrow_mut().insert(designed, e.to_string());
                    return;
                }
            }
        } else {
            decl
        };
        let Some(equations) = self.elab_branch_equations(decl, recursion, false) else {
            let why = branch_equations::head_names(decl)
                .first()
                .and_then(|n| self.pass.unfold_refusals.borrow().get(n).cloned())
                .unwrap_or_else(|| "the body has no branch equations".to_string());
            self.pass.unfold_refusals.borrow_mut().insert(designed, format!("its branch equations were not built: {why}"));
            return;
        };
        let principle = match function_induction::induct(decl, &self_name, &equations, recursion) {
            Ok(p) => p,
            Err(why) => {
                self.designate_equations(&equations);
                self.pass.unfold_refusals.borrow_mut().insert(designed, why);
                return;
            }
        };
        let warn_mark = self.pass.warnings.borrow().len();
        let built = self.session_transaction(|me| {
            let r = if recursion == branch_equations::Recursion::Measure {
                DeclarationsMut(me).elab_measure_decl_as(&principle, false)
            } else if recursion == branch_equations::Recursion::None {
                // Its equations were designated when the function was: the
                // principle cites them by their minted names.
                me.generated_mode(|me| DeclarationsMut(me).elab_decl_owned(&principle))
            } else {
                DeclarationsMut(me).elab_decl_owned(&principle)
            };
            r.map_err(|e| ElabError::Elab { msg: format!("the generated `{designed}` was refused ({e})"), span: principle.span })
        });
        self.pass.warnings.borrow_mut().truncate(warn_mark);
        self.designate_equations(&equations);
        match built {
            Ok(()) if self.access_alias(&designed).is_none_or(|m| m == principle.name) => self.designate_access(&designed, &principle.name),
            Ok(()) => {}
            Err(e) => {
                self.pass.unfold_refusals.borrow_mut().insert(designed, e.to_string());
            }
        }
    }

    fn elab_decl_owned(&mut self, decl: &Decl) -> R<()> {
        // `unfolding f, g`: the declaration sees through these interface
        // definitions, its gate included (docs/language/interface-definitions-design.md §4).
        if !decl.unfolding.is_empty() {
            let keys = InterfaceDefs(self).unfolding_keys(decl)?;
            let mut inner = decl.clone();
            inner.unfolding.clear();
            self.scope.unfolded.extend(keys.iter().cloned());
            self.refresh_delta_psi();
            let out = self.elab_decl_owned(&inner);
            let keep = self.scope.unfolded.len() - keys.len();
            self.scope.unfolded.truncate(keep);
            self.refresh_delta_psi();
            return out;
        }
        // A `meta fn` is a different declaration form: modal signature,
        // quotation body, `Layer::Meta` check, elaborator-side registration
        // (docs/metaprogramming/in-language-map-design.md §3–4).
        if decl.is_meta {
            return QuotationMut(self).elab_meta_decl(decl);
        }
        // An `evidence theorem` is an ordinary theorem, registered for
        // `:= infer` once it has passed its gate
        // (docs/library/positivity-evidence-design.md §6 A).
        if decl.is_evidence {
            Resolution(self).evidence_shape(decl)?;
            self.elab_decl_one(decl, None)?;
            return ResolutionMut(self).register_evidence(decl);
        }
        // An `interface fn` is elaborated as the `fn` it is, then registered,
        // with its unfolding equations beside it
        // (docs/language/interface-definitions-design.md).
        if decl.is_interface {
            InterfaceDefs(self).interface_shape(decl)?;
            let mut plain = decl.clone();
            plain.is_interface = false;
            return self.session_transaction(|me| {
                DeclarationsMut(me).elab_decl_owned(&plain)?;
                let equations = InterfaceDefsMut(me).interface_equations(decl)?;
                InterfaceDefsMut(me).register_interface(decl, equations)
            });
        }
        // `decreases e` is not one declaration but a family of them
        // (docs/language/recursion/decreases-unfolding-design.md §2): the arm, the eliminator,
        // the declaration itself, and — for a `fn` whose body the walk of §3
        // handles — the unfolding companions.
        // `for` loops lift into a named step over a fold, and the
        // declaration is the family that results (crates/elab/src/loops.rs).
        // `partial fn` is the family of crates/elab/src/partial.rs: its body
        // over the carrier of its own calls, and `f` as `CoTree::rec` of it.
        if decl.partial.is_some() {
            return self.session_transaction(|me| DeclarationsMut(me).elab_partial_decl(decl));
        }
        if loops::has_loop(decl) {
            if let Some(nu) = &decl.depth {
                return err("a `depth` bound on a declaration with loops is not built yet: its loops lift into steps of their own", nu.span);
            }
            return self.session_transaction(|me| DeclarationsMut(me).elab_loop_decl(decl));
        }
        if decl.decreases.is_some() {
            return self.session_transaction(|me| DeclarationsMut(me).elab_measure_decl(decl));
        }
        // A `fn` whose structural lowering would not mean its source is
        // lowered by measure, or refused where that has no unfolding equation
        // either (issues/fn-recursion-means-the-function.md).
        // A `fn` returning codata recurses *guardedly*, not structurally: its
        // self-calls become one `corec` (docs/inductives/codata-elaborator-design.md §5),
        // so a `match` reading a parameter is the step's own observation.
        let corecursive = matches!(&decl.result.kind,
            heather_syntax::ast::TyKind::Named { name, .. }
                if self.lookup_inductive(name).is_some_and(|i| i.codata));
        if decl.kind == DeclKind::Fn && !corecursive {
            if self.policy.recursion_plan_skipped {
                return self.elab_structural_fn(decl);
            }
            let self_ref = recursion::SelfRef::of_decl(decl);
            let types: Vec<Option<&Ty>> = decl
                .tyvars
                .iter()
                .map(|_| None)
                .chain(decl.params.iter().map(|p| Some(&p.ty)))
                .collect();
            let plan = recursion::plan(&self_ref, &types, &decl.body);
            // Recursion at the top is the lowering of every structural
            // recursion on an explicit `Nat` parameter
            // (issues/recursion-at-top-nat-default.md); the plain lowering is
            // the fallback where it does not elaborate. A `ByMeasure` plan
            // keeps its route below, which tries the top first and keeps
            // the `f_unfold` its clients cite.
            if !matches!(plan, recursion::RecursionPlan::ByMeasure { .. })
                && let Some(dec) = recursion::top_default_param(&self_ref, &decl.body)
                && Declarations(self).at_top_candidate(decl, dec)
                && self.try_recursion_at_top(decl, dec, TopAttempt::Default)
            {
                return MeaningMut(self).check_recursion_meaning(decl);
            }
            match plan {
                recursion::RecursionPlan::Structural => {}
                recursion::RecursionPlan::ByMeasure { dec, read, name, from } => {
                    // Recursion at the top means the source wherever it
                    // elaborates, and unfolds by conversion; the measure is
                    // the fallback (docs/language/recursion/recursion-at-the-top-design.md §4).
                    if Declarations(self).at_top_candidate(decl, dec) && self.try_recursion_at_top(decl, dec, TopAttempt::Fallback) {
                        return MeaningMut(self).check_recursion_meaning(decl);
                    }
                    return self.elab_recursion_by_measure(decl, &self_ref, dec, read, &name, from);
                }
                // Refused only at a self-call lowered under a guard on
                // `dec`, so the plain lowering goes first; its refusal is
                // what recursion at the top answers.
                recursion::RecursionPlan::Misplaced { dec, msg } => {
                    let misplaced = Some((self_ref.name.clone(), dec, msg.clone()));
                    return self.elab_at_top_on_refusal(decl, Some(&msg), |me| {
                        me.scoped(|s| s.misplaced_recursion.get_mut(), misplaced, |me| me.elab_decl_one(decl, None))
                    });
                }
            }
            return self.elab_at_top_on_refusal(decl, None, |me| me.elab_structural_fn(decl));
        }
        if decl.kind == DeclKind::Theorem {
            return self.elab_at_top_on_refusal(decl, None, |me| me.elab_decl_one(decl, None));
        }
        self.elab_decl_one(decl, None)
    }
}

impl Declarations<'_> {
    /// Can `decl` recurse at the top on parameter `dec` (an index into the
    /// type parameters then the value parameters)? Slice 1 is an explicit
    /// `Nat` parameter (docs/language/recursion/recursion-at-the-top-design.md §4).
    fn at_top_candidate(&self, decl: &Decl, dec: usize) -> bool {
        dec.checked_sub(decl.tyvars.len())
            .and_then(|i| decl.params.get(i))
            .is_some_and(|p| !p.implicit && (matches!(p.ty.kind, TyKind::Nat) || self.top_wf(&p.ty).is_some()))
    }

    /// The tier-1 `Wf` inductive a parameter of type `ty` is, if recursion
    /// at the top can take it apart (slice 3): recursive, not codata, not
    /// an indexed family, the `IWf` route, a mutual group or infinitary.
    fn top_wf(&self, ty: &Ty) -> Option<Rc<inductive::Inductive>> {
        let TyKind::Named { name, .. } = &ty.kind else { return None };
        let ind = self.lookup_inductive(name)?;
        (ind.recursive
            && !ind.codata
            && ind.index.is_none()
            && ind.skel.is_none()
            && ind.members.is_empty()
            && !ind.infinitary()
            && ind.ctors.iter().all(|c| c.res.is_none()))
        .then(|| Rc::clone(ind))
    }
}

impl DeclarationsMut<'_> {
    /// Elaborate `decl` by `elaborate`; where that refuses a self-call (a
    /// structural refusal: the call does not descend at the guard the
    /// lowering chose), try each explicit `Nat` parameter at the top before
    /// reporting it (docs/language/recursion/recursion-at-the-top-design.md §4, slice 1).
    fn elab_at_top_on_refusal(
        &mut self,
        decl: &Decl,
        misplaced: Option<&str>,
        elaborate: impl FnOnce(&mut Self) -> R<()>,
    ) -> R<()> {
        let error = match elaborate(self) {
            Ok(()) => return Ok(()),
            Err(error) => error,
        };
        let refused_call = matches!(&error, ElabError::Elab { msg, .. }
            if msg.starts_with(&format!("recursive call to `{}`", recursion::SelfRef::of_decl(decl).name))
                || Some(msg.as_str()) == misplaced);
        if !refused_call {
            return Err(error);
        }
        let first = decl.tyvars.len();
        for dec in first..first + decl.params.len() {
            if Declarations(self).at_top_candidate(decl, dec) && self.try_recursion_at_top(decl, dec, TopAttempt::Fallback) {
                return MeaningMut(self).check_recursion_meaning(decl);
            }
        }
        Err(error)
    }

    /// One attempt at recursion at the top on `dec`: elaborated and gated
    /// like any declaration, and on failure rolled back with everything it
    /// raised, since the caller has another lowering (or the original
    /// refusal) to fall back to.
    ///
    /// A [`TopAttempt::Fallback`] answers a refusal or replaces the measure
    /// route: it is gated inline, as the meaning check is, since at a wider
    /// pool a kernel refusal would fail the module's join instead of this
    /// attempt, and on success `f_unfold` follows, the source equation the
    /// measure route's clients cite. A [`TopAttempt::Default`] is every
    /// ordinary Nat recursion, gated at the pool's width: the rare kernel
    /// refusal fails the parallel pass, and the serial replay (width one)
    /// falls back as the inline gate would, so the answer is the same at
    /// every width.
    fn try_recursion_at_top(&mut self, decl: &Decl, dec: usize, attempt: TopAttempt) -> bool {
        let Some(lowered) = Declarations(self).recursion_at_top_body(decl, dec) else {
            return false;
        };
        let warn_mark = self.pass.warnings.borrow().len();
        let inline = attempt == TopAttempt::Fallback;
        let at = Some((dec, lowered.span, inline));
        let width = inline.then(|| self.pass.kernel_pool.swap_width(1));
        let r = self.session_transaction(|me| {
            me.scoped(|s| &mut s.recursion_at_top_surface, Some(std::rc::Rc::new(decl.clone())), |me| {
                me.scoped(|s| &mut s.recursion_at_top, at, |me| me.elab_decl_one(&lowered, None))
            })
        });
        if let Some(width) = width {
            self.pass.kernel_pool.swap_width(width);
        }
        if r.is_err() {
            self.pass.warnings.borrow_mut().truncate(warn_mark);
            stats::count(stats::Counter::RecursionAtTopFallbacks);
            return false;
        }
        stats::count(stats::Counter::RecursionAtTop);
        // The meaning check (issues/recursion-meaning-check.md) is the
        // caller's: an attempt that succeeded is the definition, and a
        // refusal of its equation is the declaration's error, not a reason
        // to try another lowering under the same name.
        if !inline {
            return true;
        }
        // `f(x̄) = { body }`, by one split on the parameter: each side takes
        // the same step, which is the lowering's whole claim (§3).
        let param = &decl.params[dec - decl.tyvars.len()];
        let proof = Meaning(self).meaning_split(&param.name, &param.ty, 1, &mut 0, decl.span);
        let mut unfold = meaning::meaning_decl(decl, proof);
        unfold.name = measure::unfold_name(&decl.name);
        if let Err(e) = self.elab_decl_one(&unfold, None) {
            self.pass.unfold_refusals.borrow_mut().insert(
                unfold.name.clone(),
                format!("the generated `{}` was refused ({e})", unfold.name),
            );
        }
        true
    }
}

impl Declarations<'_> {
    /// `decl` with its body under one `match` on parameter `dec`, each arm
    /// rebinding the parameter's name to that arm's constructor term:
    ///
    /// ```text
    /// match z { Zero => { let z = Zero; body }, Succ(z#pred) => { let z = Succ(z#pred); body } }
    /// ```
    ///
    /// Elaborated under [`DynamicScope::recursion_at_top`](crate::lifetimes::DynamicScope::recursion_at_top), this `match` is
    /// the recursion and every other explicit parameter is generalized, so
    /// the body recomputes at each level with this level's values: a read of
    /// `z` is this level's `z`, and a `match z` inside takes its arm, whose
    /// predecessor is the guard's (docs/language/recursion/recursion-at-the-top-design.md §3).
    fn recursion_at_top_body(&self, decl: &Decl, dec: usize) -> Option<Decl> {
        let param = &decl.params[dec - decl.tyvars.len()];
        if let Some(ind) = self.top_wf(&param.ty) {
            return recursion_at_top_hoisted(decl, dec, &ind);
        }
        Some(self.recursion_at_top_nat(decl, dec))
    }

    fn recursion_at_top_nat(&self, decl: &Decl, dec: usize) -> Decl {
        let span = decl.span;
        let z = decl.params[dec - decl.tyvars.len()].name.clone();
        let pred = format!("{z}#pred");
        let var = |name: &str| Expr { kind: ExprKind::Var(name.to_string()), span };
        let arm = |ctor: &str, binders: Vec<heather_syntax::Pat>, value: Expr| {
            let mut stmts = vec![heather_syntax::Stmt::Let { name: z.clone(), ty: None, expr: value, span, opaque: false }];
            stmts.extend(decl.body.stmts.iter().cloned());
            heather_syntax::Arm {
                ctor: ctor.to_string(),
                default: false,
                binders,
                body: Expr {
                    kind: ExprKind::Block(Box::new(heather_syntax::Block {
                        stmts,
                        result: decl.body.result.clone(),
                        ons: decl.body.ons.clone(),
                        span: decl.body.span,
                    })),
                    span: decl.body.span,
                },
                span,
            }
        };
        let succ = Expr {
            kind: ExprKind::App {
                head: Box::new(var("Succ")),
                args: vec![var(&pred)],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let arms = vec![
            arm("Zero", Vec::new(), var("Zero")),
            arm("Succ", vec![heather_syntax::Pat::Var { name: pred.clone(), span }], succ),
        ];
        let mut lowered = decl.clone();
        lowered.body = heather_syntax::Block {
            stmts: Vec::new(),
            result: Box::new(Expr {
                kind: ExprKind::Match {
                    form: MatchForm::Match,
                    generated: true,
                    scrut: Box::new(var(&z)),
                    eqbind: None,
                    motive: None,
                    arms,
                    test: None,
                },
                span,
            }),
            ons: Vec::new(),
            span: decl.body.span,
        };
        lowered
    }

    /// The parameter a `match` at `span` recurses on, if it is the `match`
    /// [`Self::recursion_at_top_body`] wrapped the declaration in.
    pub(crate) fn top_guard(&self, span: Span) -> Option<usize> {
        self.scope.recursion_at_top.filter(|&(_, at, _)| at == span).map(|(dec, _, _)| dec)
    }

    /// What recursion at the top generalizes: every explicit value
    /// parameter but the one it recurses on, ascending.
    pub(crate) fn top_positions(cx: &Cx, dec: usize) -> Vec<usize> {
        let Some(s) = cx.selfref.as_ref() else { return Vec::new() };
        (s.n_tyvars..s.params.len()).filter(|&p| p != dec && !s.params[p].1).collect()
    }
}

impl DeclarationsMut<'_> {
    /// A `fn` the planner lowers structurally, then checked to mean its
    /// source (issues/recursion-meaning-check.md).
    fn elab_structural_fn(&mut self, decl: &Decl) -> R<()> {
        self.elab_decl_one(decl, None)?;
        MeaningMut(self).check_recursion_meaning(decl)
    }

    /// A `fn` whose recursive `match` reads its own parameter, lowered as if
    /// it had been written `decreases p` (`p.len()` for a list), which gives
    /// the source's meaning (issues/fn-recursion-means-the-function.md). The
    /// measure's obligations are left to `omega`, the route's own default, so
    /// the route needs `nat` and `omega` in scope; without them, or at a type
    /// with no measure, the reading is refused with what to write instead.
    fn elab_recursion_by_measure(
        &mut self,
        decl: &Decl,
        self_ref: &recursion::SelfRef,
        dec: usize,
        read: Span,
        name: &str,
        from: usize,
    ) -> R<()> {
        let fname = &self_ref.name;
        let param = &self_ref.params[dec].0;
        let source = &self_ref.params[from].0;
        let what = if from != dec {
            format!(
                "`{name}`, bound from `{source}` above the recursive `match`, is read inside \
                 it, and the recursive call passes `{source}` a different value \
                 (issues/recursion-let-reads-changing-parameter.md)"
            )
        } else if name == param {
            format!("`{param}` is read inside its own recursive `match`")
        } else {
            format!("`{name}`, bound from `{param}` above the recursive `match`, is read inside it")
        };
        let keep = if from != dec {
            format!("bind `{name}` inside each arm that reads it")
        } else {
            "name this level's value by its pattern (`Succ(k)`, `Cons(h, t)`)".to_string()
        };
        let refuse = |why: &str| {
            err(
                format!(
                    "{what}: the structural lowering compiles the recursion at the `match`, \
                     so there it would be the value `{fname}` was first called with, not this \
                     level's. {why} Or {keep} (issues/fn-recursion-means-the-function.md)"
                ),
                read,
            )
        };
        let measure = decl
            .params
            .get(dec - decl.tyvars.len())
            .and_then(|p| match &p.ty.kind {
                TyKind::Nat => Some(Expr { kind: ExprKind::Var(param.clone()), span: p.span }),
                TyKind::Named { name, .. } if name.rsplit("::").next() == Some("List") => {
                    Some(Expr {
                        kind: ExprKind::Dot {
                            recv: Box::new(Expr { kind: ExprKind::Var(param.clone()), span: p.span }),
                            name: "len".into(),
                            tyargs: Vec::new(),
                            args: Some(Vec::new()),
                            named: Vec::new(),
                        },
                        span: p.span,
                    })
                }
                _ => None,
            });
        let Some(measure) = measure else {
            return refuse(&format!(
                "It would be lowered by a measure instead, but `{param}` is neither a `Nat` nor \
                 a `List`: declare `decreases` with a measure on it yourself."
            ));
        };
        let available = [
            "nat::Nat::le_trans",
            "omega::nat_le_of_not_not_le",
            "int::Int::negsucc_lt_ofnat",
        ]
        .iter()
        .all(|n| matches!(NameLookup(self).resolve_declared(n), NameRes::Found(_)));
        if !available {
            return refuse(
                "It would be lowered by a measure on it instead, whose obligations `omega` \
                 discharges: `import nat; import int; import omega;` for that.",
            );
        }
        self.emit_lint(
            Lint::RecursionByMeasure,
            format!(
                "{what}, so `{fname}` is compiled as if it had been declared `decreases`: it \
                 computes what it says, but at a symbolic argument it no longer unfolds by \
                 conversion; cite `{fname}_unfold` for that, or {keep} to keep the \
                 structural lowering (issues/fn-recursion-means-the-function.md)"
            ),
            read,
        );
        let mut by_measure = decl.clone();
        by_measure.decreases = Some(measure);
        // The source wrote no `decreases`: a refusal that names it says why
        // the declaration is under one, and what keeps it structural.
        self.session_transaction(|me| DeclarationsMut(me).elab_measure_decl(&by_measure)).map_err(|e| match e {
            ElabError::Elab { msg, span } if msg.contains("under `decreases`") => ElabError::Elab {
                msg: format!(
                    "{msg}\n(`{fname}` is compiled as if declared `decreases` because {what}; \
                     or {keep} to keep the structural lowering, \
                     issues/fn-recursion-means-the-function.md)"
                ),
                span,
            },
            other => other,
        })
    }

    /// A declaration whose body holds `for` loops: each loop's step and
    /// state, then the declaration over folds (crates/elab/src/loops.rs).
    /// Each part goes through [`Elaborator::elab_decl`], so a step with loops of
    /// its own is lowered the same way.
    fn elab_loop_decl(&mut self, decl: &Decl) -> R<()> {
        // A range of numerals lists `Nat`s, and counts words where the body
        // needs its index to be one (docs/language/sequencing-surface-design.md §21):
        // read at `Nat` first, which every range read before, and at `u64`
        // where that is refused.
        let lists = self.session_transaction(|me| DeclarationsMut(me).elab_loop_family(decl, loops::Ranges::Lists));
        match lists {
            Ok(()) => Ok(()),
            Err(e) if loops::has_numeral_range(decl) => {
                self.session_transaction(|me| DeclarationsMut(me).elab_loop_family(decl, loops::Ranges::Words)).map_err(|w| match (e, w) {
                    (ElabError::Elab { msg, span }, ElabError::Elab { msg: wmsg, .. }) => ElabError::Elab {
                        msg: format!("{msg}\n(read with the range counting `u64` words instead: {wmsg})"),
                        span,
                    },
                    (e, _) => e,
                })
            }
            Err(e) => Err(e),
        }
    }

    fn elab_loop_family(&mut self, decl: &Decl, ranges: loops::Ranges) -> R<()> {
        // Under a prefix generator (`runtime fn`), which reflects the lifted
        // loops as programs, a loop is given no fact it did not state.
        let free = self.scope.loop_methods.is_none();
        let family = loops::lower(decl, self.0, ranges, free)?;
        // A `while` is spelled with the library's loop combinator, which
        // the module has to import (`Pass` alone would be refused as a
        // name that takes no type arguments, which says nothing).
        if let Some((span, _)) = family.decreases.first()
            && !matches!(NameLookup(self).resolve_declared("Pass"), NameRes::Found(_))
        {
            return Err(ElabError::Elab {
                msg: "a `while` is a loop of the library's combinator (`Loop`, `Pass`): this module needs `import loop;`".into(),
                span: *span,
            });
        }
        for part in &family.parts {
            match part {
                loops::Part::State(d) => self.elab_inductive(d)?,
                loops::Part::Decl(d) => self.elab_decl(d).map_err(|e| match e {
                    // A pass that goes round owes the measure's decrease
                    // (docs/language/loop-combinator-design.md §5).
                    ElabError::Elab { msg, span } if family.decreases.iter().any(|(s, _)| *s == span)
                        && (msg.starts_with("`omega` got stuck") || msg.starts_with("`bv_omega`")) =>
                    {
                        let text = family.decreases.iter().find(|(s, _)| *s == span).map(|(_, t)| t.clone()).unwrap_or_default();
                        ElabError::Elab {
                            msg: format!("this pass of the loop must decrease the measure `{text}`, and that was not proved \
                                          automatically. The search said: {msg}"),
                            span,
                        }
                    }
                    e => e,
                })?,
            }
        }
        // §7.1: always attempted, and never a reason to refuse `f` — the
        // generated statement is untrusted, so a refusal is recorded for a
        // later `f_unfold` reference to report.
        if let Some(unfold) = &family.unfold
            && let Err(e) = self.elab_decl_one(unfold, None)
        {
            self.pass.unfold_refusals.borrow_mut().insert(unfold.name.clone(), format!("the generated `{}` was refused ({e})", unfold.name));
        }
        // Designated last: the generated parts above are spelled with the
        // minted names, which a designation takes out of the surface.
        for (designed, minted) in &family.designations {
            self.designate_access(designed, minted);
            // A lifted `while` or counted loop is a `decreases` function:
            // its companions, designated under the minted name, are
            // designated under the loop's own too (`f::run::body`), which
            // is where a generator over `f::run` looks them up.
            for part in ["body", "rec", "ext", "irrel"] {
                if let Some(target) = self.access_alias(&format!("{minted}::{part}")).map(str::to_string) {
                    self.designate_access(&format!("{designed}::{part}"), &target);
                }
            }
            // A combinator loop's step's branch equations (`f::step::True`),
            // which `induct f::step(…)` and a proof cite.
            let prefix = format!("{minted}::");
            let members = self.access_aliases_under(&prefix);
            for (member, target) in members {
                let name = format!("{designed}::{member}");
                if self.access_alias(&name).is_none() {
                    self.designate_access(&name, &target);
                }
            }
        }
        // Recorded once the family stands: a prefix generator runs over the
        // loops lifted as methods (`HostMut::elab_prefixed`).
        if let Some(methods) = self.scope.loop_methods.as_mut() {
            methods.extend(family.methods.iter().cloned());
        }
        Ok(())
    }

    /// A `partial fn`: `f#body`, then `f` over `CoTree::rec`, then
    /// `f_unfold` (crates/elab/src/partial.rs). Each part goes through
    /// [`Elaborator::elab_decl`], so a body with loops is lowered as any is.
    fn elab_partial_decl(&mut self, decl: &Decl) -> R<()> {
        let family = partial::lower(decl)?;
        for part in &family.parts {
            self.elab_decl(part)?;
        }
        if let Err(e) = self.elab_decl_one(&family.unfold, None) {
            self.pass.unfold_refusals.borrow_mut().insert(family.unfold.name.clone(), format!("the generated `{}` was refused ({e})", family.unfold.name));
        }
        for (designed, minted) in &family.designations {
            self.designate_access(designed, minted);
        }
        Ok(())
    }

    /// `fn f(x̄) -> T decreases e { body }` is not one declaration but the
    /// family of `docs/language/recursion/decreases-unfolding-design.md` §2 — `f#body`, `f#rec`,
    /// `f` — elaborated in order. Each member is an ordinary declaration
    /// checked the ordinary way, so nothing the generator writes is trusted.
    fn elab_measure_decl(&mut self, decl: &Decl) -> R<()> {
        self.elab_measure_decl_as(decl, true)
    }

    /// `companions: false` builds the recursion alone, with no unfolding
    /// equations and nothing generated from them: a generated principle's
    /// own recursion (`function_induction`) is cited, never unfolded.
    fn elab_measure_decl_as(&mut self, decl: &Decl, companions: bool) -> R<()> {
        // The lowering reads names by their last binding, so a `let m = m - 1`
        // would shadow the measure's `m` (issues/decreases-shadowed-let.md).
        let decl = &measure::deshadowed(decl);
        let measure = decl.decreases.clone().expect("a measure declaration");
        measure::check_shape(decl, &measure)?;
        // A member's self-call may be written as a method call on its
        // receiver; every route below reads the call it desugars to.
        let decl = &measure::method_calls_as_calls(decl, base_name(&decl.name), self.0)?;
        // A `depth ν` clause and its discharges (`on ?depthN := …`) are
        // lowered on their own, after the family (`elab_depth_bound`): the
        // recursion itself is the measure's alone.
        let (plain, depth) = measure::split_depth(decl);
        let decl = &plain;
        // The wrapper spells `nat::Nat::Lt`, `nat::Nat::le_trans` and `nat::Nat::lt_succ_self`;
        // the default closer spells `omega`'s certificates, which name the
        // `omega` module. Neither is the prelude's, so the module has to import
        // them — checked here so the message says so.
        if !matches!(NameLookup(self).resolve_declared("nat::Nat::le_trans"), NameRes::Found(_)) {
            return err(
                "`decreases` states its obligations with `nat::Nat::Lt` and discharges them \
                 through `nat::Nat::le_trans`: `import nat;` first",
                measure.span,
            );
        }
        // `omega`'s certificates name `omega::` and `int::` lemmas, so the
        // default closer is available only where both modules are imported;
        // otherwise every obligation is an ordinary unsolved goal, reported
        // with its statement.
        let omega_available = ["omega::nat_le_of_not_not_le", "int::Int::negsucc_lt_ofnat"]
            .iter()
            .all(|n| matches!(NameLookup(self).resolve_declared(n), NameRes::Found(_)));
        self.check_measure_is_nat(decl, &measure)?;
        // A member recurses under its **base** name, as `SelfRef` does.
        let self_name = decl.name.rsplit("::").next().unwrap_or(&decl.name).to_string();
        // §4: each self-call site's obligation is a declaration of its own,
        // elaborated first because the body and both companions reference it.
        // A lifted obligation the *checker* refuses is not an error on `f` —
        // the generated statement may be one this syntactic pass got wrong —
        // so the declaration is re-lowered with its obligations back at the
        // calls, exactly as it was before this round, and the companions are
        // declined with the reason. An obligation that is genuinely unprovable
        // fails again there, with the message §2 of the measures doc pins.
        // A computed scrutinee's equation enters the lowering only where a
        // lifted obligation reads it (design §13): lowered with every
        // candidate bound, then again with just the ones the obligations
        // quantify, so a body whose obligations never read one keeps the
        // plain match it was written with.
        // A proof a call leaves to a search that reads its context is found
        // once, in a declaration of its own, so the body and the companions
        // name one term (`measure::lift_found`). Where the checker refuses a
        // lifted proof the declaration is lowered as written, and the proof
        // is searched for at its call as before.
        let with_found;
        let decl = match measure::lift_found(decl, &self_name, &measure, self.0) {
            Some((lifted, proofs)) if proofs.iter().all(|p| self.elab_decl_one(&p.decl, Some(&p.obligations)).is_ok()) => {
                with_found = lifted;
                &with_found
            }
            _ => decl,
        };
        let mut auto = measure::AutoEqs::All;
        let mut family = measure::lower(decl, &self_name, &measure, omega_available, self.0, true, &auto)?;
        if family.auto_candidates > 0 {
            let mut used: Vec<usize> = family
                .obligations
                .iter()
                .flat_map(|o| o.decl.params.iter().filter_map(|p| measure::auto_eq_index(&p.name)))
                .collect();
            used.sort_unstable();
            used.dedup();
            let all = used.len() == family.auto_candidates;
            auto = measure::AutoEqs::Only(used);
            if !all {
                family = measure::lower(decl, &self_name, &measure, omega_available, self.0, true, &auto)?;
            }
        }
        let mut lifted = true;
        for part in &family.obligations {
            if let Err(why) = self.elab_decl_one(&part.decl, Some(&part.obligations)) {
                self.pass.unfold_refusals.borrow_mut().insert(
                    measure::unfold_name(&decl.name),
                    format!("the lifted `{}` was refused ({why})", part.decl.name),
                );
                lifted = false;
                break;
            }
        }
        if !lifted {
            family = measure::lower(decl, &self_name, &measure, omega_available, self.0, false, &measure::AutoEqs::Off)?;
        }
        for part in &family.decls {
            self.elab_decl_one(&part.decl, Some(&part.obligations))?;
        }
        // §7: the unfolding companions are **always attempted** and silently
        // skipped where §3's walk refuses the body — a hard error would
        // regress programs that are accepted today for the sake of a theorem
        // they never cite. The refusal is recorded so a later reference to
        // `f_unfold` reports the shape rather than an unknown name.
        //
        // A companion that the walk builds but the *checker* refuses is
        // treated the same way (amends §3): the generator is untrusted, so a
        // term it got wrong must not take `f` down with it. The recorded
        // reason quotes the checker, so the case stays diagnosable.
        let unfold = measure::unfold_name(&decl.name);
        if lifted && companions {
            match measure::companions(decl, &self_name, &measure, omega_available, self.0, &auto, &family.obligations) {
                Err(why) => {
                    self.pass.unfold_refusals.borrow_mut().insert(unfold.clone(), why);
                }
                Ok(parts) => {
                    let mut built = true;
                    for part in parts {
                        if let Err(e) = self.elab_decl_one(&part.decl, Some(&part.obligations)) {
                            self.pass.unfold_refusals
                                .borrow_mut()
                                .insert(unfold.clone(), format!("the generated `{}` was refused ({e})", part.decl.name));
                            built = false;
                            break;
                        }
                    }
                    // `f::ext` (the step's extensionality in its recursion)
                    // and `f::irrel` (the recursor's bound irrelevance) are
                    // what a `runtime fn`'s measured loop is proved from
                    // (docs/native/runtime-fn-setups-design.md §16.10).
                    if built {
                        self.designate_access(&format!("{}::ext", decl.name), &measure::ext_name(&decl.name));
                        self.designate_access(&format!("{}::irrel", decl.name), &measure::irrel_name(&decl.name));
                        // `f::step` and `f::done`: `f_unfold` at the arm its
                        // test picks (issues/loop-invariant-rules.md). Built
                        // where the body is one test, and, like the
                        // companions, skipped with the reason recorded where
                        // the checker refuses one.
                        self.elab_step_equations(decl, &self_name);
                        // `f::True`, `f::False`, … and `f::induct`: the
                        // equations at every leaf, and induction along the
                        // recursion (`function_induction`). Built with the
                        // loop, so a module that imports it can do induction
                        // along it; a structural recursion's are built on
                        // demand (`demand_principles`).
                        if decl.kind == DeclKind::Fn {
                            self.pass.recursions.borrow_mut().insert(decl.name.clone(), (Rc::new(decl.clone()), branch_equations::Recursion::Measure));
                            self.elab_recursion_equations(decl, branch_equations::Recursion::Measure);
                        }
                    }
                }
            }
        }
        // Without `f_unfold` there are no branch equations and no
        // `f::induct` either, since both are proved from it: a reference to
        // one reports why `f_unfold` was not built, not that `f` is not a
        // recursion (issues/decreases-on-block-let-no-unfold.md).
        if companions && decl.kind == DeclKind::Fn {
            let refused = self.pass.unfold_refusals.borrow().get(&unfold).cloned();
            if let Some(why) = refused {
                let why = format!("its unfolding `{unfold}` was not built: {why}");
                let mut refusals = self.pass.unfold_refusals.borrow_mut();
                for name in branch_equations::head_names(decl).into_iter().chain([format!("{}::induct", decl.name)]) {
                    refusals.entry(name).or_insert_with(|| why.clone());
                }
            }
        }
        // The recursor and its step have designed spellings, `f::rec` and
        // `f::body`: `f` at a bound on its measure, and one step of it with
        // its recursion any function, which a proof by induction on the
        // bound states its claims about where no `f_unfold` exists
        // (docs/language/recursion/decreases-unfolding-design.md §11). Designated last: the
        // companions above are spelled with the minted names, which a
        // designation takes out of the surface.
        self.designate_access(&format!("{}::rec", decl.name), &measure::rec_name(&decl.name));
        self.designate_access(&format!("{}::body", decl.name), &measure::body_name(&decl.name));
        // Each lifted obligation as `f::obl_N`: the decrease at that call,
        // which a `runtime fn` reads its depth from
        // (docs/native/runtime-fn-recursion-design.md §3.2).
        if lifted {
            for part in &family.obligations {
                if let Some(site) = part.decl.name.strip_prefix(&format!("{}#obl_", decl.name)) {
                    self.designate_access(&format!("{}::obl_{site}", decl.name), &part.decl.name);
                }
            }
        }
        if let Some((nu, ons)) = depth
            && companions
        {
            self.elab_depth_bound(decl, &self_name, &nu, ons, omega_available, &auto, family.obligations.len())?;
        }
        Ok(())
    }

    /// `decreases μ depth ν` (docs/native/runtime-fn-recursion-design.md
    /// §3.3): every recursive call owes `ν(y) < ν(x)` as it owes the
    /// measure's decrease, so the body is lowered once more with `ν` as its
    /// measure and only the lifted obligations are kept, as `f::depth_obl_N`,
    /// with the writer's `on ?depthN := …` as their discharges and the
    /// measure's default closer otherwise. `f::depth_rank` is `ν` as a
    /// function of the parameters. Nothing here is the recursion's: a
    /// `runtime fn` reads the two to publish `f::depth` at `ν`.
    #[allow(clippy::too_many_arguments)]
    fn elab_depth_bound(&mut self, decl: &Decl, self_name: &str, nu: &Expr, ons: Vec<heather_syntax::OnStmt>,
                        omega_available: bool, auto: &measure::AutoEqs, calls: usize) -> R<()> {
        let as_depth = |e: ElabError| match e {
            ElabError::Elab { msg, span } => ElabError::Elab {
                msg: msg.replace("a `decreases` measure is a `Nat`", "a `depth` bound is a `Nat`")
                    .replace("must decrease the measure", "must decrease the `depth` bound")
                    .replace("`on ?dec", "`on ?depth"),
                span,
            },
            other => other,
        };
        self.check_measure_is_nat(decl, nu).map_err(as_depth)?;
        let mut bound = decl.clone();
        bound.name = measure::depth_name(&decl.name);
        bound.decreases = Some(nu.clone());
        bound.body.ons = ons;
        let family = measure::lower(&bound, self_name, nu, omega_available, self.0, true, auto).map_err(as_depth)?;
        if family.obligations.len() != calls {
            return err(
                "a `depth` bound's obligations are lifted one per recursive call, as the measure's are, \
                 and here they could not all be: discharge each by name (`on ?depthN := …`)",
                nu.span,
            );
        }
        for part in &family.obligations {
            self.elab_decl_one(&part.decl, Some(&part.obligations)).map_err(as_depth)?;
        }
        let span = nu.span;
        let rank = Decl {
            kind: DeclKind::Fn,
            value: false,
            elaborates: None,
            name: measure::depth_rank_name(&decl.name),
            result: Ty { kind: TyKind::Nat, span },
            decreases: None,
            depth: None,
            body: heather_syntax::Block { stmts: Vec::new(), result: Box::new(nu.clone()), ons: Vec::new(), span },
            ..decl.clone()
        };
        self.elab_decl_one(&rank, None).map_err(as_depth)?;
        self.designate_access(&format!("{}::depth_rank", decl.name), &rank.name);
        let prefix = format!("{}#obl_", bound.name);
        for part in &family.obligations {
            if let Some(site) = part.decl.name.strip_prefix(&prefix) {
                self.designate_access(&format!("{}::depth_obl_{site}", decl.name), &part.decl.name);
            }
        }
        Ok(())
    }

    /// `f::step` and `f::done` (`measure::step_equations`), elaborated after
    /// `f_unfold`, which they are proved from. They need `Bool::convoy_true`
    /// and the decision lemmas, so a module that cannot name those gets
    /// neither; a refusal is recorded under the designed spelling, which a
    /// reference then reports.
    fn elab_step_equations(&mut self, decl: &Decl, self_name: &str) {
        let needs = ["bool::Bool::convoy_true", "bool::Bool::convoy_false", "bool::decide_bit_of", "bool::decide_bit_of_not", "logic::False"];
        let designed = [format!("{}::step", decl.name), format!("{}::done", decl.name)];
        let refuse = |this: &mut Self, why: String| {
            for n in &designed {
                this.pass.unfold_refusals.borrow_mut().insert(n.clone(), why.clone());
            }
        };
        if let Some(missing) = needs.iter().find(|n| !matches!(NameLookup(self).resolve_declared(n), NameRes::Found(_))) {
            let module = missing.split("::").next().unwrap_or(missing);
            return refuse(self, format!("`{missing}` is not reached from this module: `import {module};`"));
        }
        let parts = match measure::step_equations(decl, self_name) {
            Ok(parts) => parts,
            Err(why) => return refuse(self, why),
        };
        for part in &parts {
            if let Err(e) = self.elab_decl_one(&part.decl, Some(&part.obligations)) {
                let why = format!("the generated `{}` was refused ({e})", part.decl.name);
                return refuse(self, why);
            }
        }
        self.designate_access(&designed[0], &measure::step_name(&decl.name));
        self.designate_access(&designed[1], &measure::done_name(&decl.name));
    }

    /// N > 1 adjacent `decreases` declarations that call one another
    /// (`docs/language/recursion/mutual-recursion-design.md` §1) are one recursion: the product
    /// motive `f#grp`, one `g#body` per member, the shared `f#grp_rec`, and
    /// each member as a projection (§3). Every generated declaration is
    /// checked the ordinary way, so nothing the generator writes is trusted.
    pub(crate) fn elab_measure_group(&mut self, members: &[&Decl]) -> R<()> {
        let span = members[0].span;
        // As `elab_measure_decl`: every name in a member's body means one binder.
        let owned: Vec<Decl> = members.iter().map(|d| measure::deshadowed(d)).collect();
        let owned: Vec<Decl> = owned.iter()
            .map(|d| measure::method_calls_as_calls(d, base_name(&d.name), self.0))
            .collect::<R<_>>()?;
        let members: Vec<&Decl> = owned.iter().collect();
        let members = &members[..];
        let mut gm: Vec<measure::GroupMember<'_>> = Vec::new();
        for d in members {
            if let Some(nu) = &d.depth {
                return err("a `depth` bound on a mutual recursion is not built yet: give it to a recursion of one declaration", nu.span);
            }
            let measure = d.decreases.clone().expect("a measure declaration");
            measure::check_shape(d, &measure)?;
            gm.push(measure::GroupMember {
                decl: d,
                self_name: base_name(&d.name).to_string(),
                measure,
            });
        }
        // §2's circularity check runs before the measures are elaborated: a
        // measure calling a member is an unbound name at this point, and
        // "unbound" is the wrong thing to say about it.
        measure::check_group_shape(&gm)?;
        for m in &gm {
            self.check_measure_is_nat(m.decl, &m.measure)?;
        }
        if !matches!(NameLookup(self).resolve_declared("nat::Nat::le_trans"), NameRes::Found(_)) {
            return err(
                "`decreases` states its obligations with `nat::Nat::Lt` and discharges them \
                 through `nat::Nat::le_trans`: `import nat;` first",
                span,
            );
        }
        // §3: the group's motive is a nested `Pair`, and its members are
        // reached by `.fst`/`.snd`.
        if self.lookup_inductive("Pair").is_none() {
            return err(
                "a mutual `decreases` group shares one recursion whose motive is the \
                 product of its members' (docs/language/recursion/mutual-recursion-design.md §3): \
                 `import pair;` first",
                span,
            );
        }
        let omega_available = ["omega::nat_le_of_not_not_le", "int::Int::negsucc_lt_ofnat"]
            .iter()
            .all(|n| matches!(NameLookup(self).resolve_declared(n), NameRes::Found(_)));
        let family = measure::lower_group(&gm, omega_available, self.0)?;
        for part in &family.obligations {
            self.elab_decl_one(&part.decl, Some(&part.obligations))?;
        }
        for part in &family.decls {
            self.elab_decl_one(&part.decl, Some(&part.obligations))?;
        }
        // §6: the unfolding companions do not extend to a group this round.
        // Each member records the refusal on its own `f_unfold`, so a citation
        // reports the reason rather than an unknown name.
        for d in members {
            self.pass.unfold_refusals.borrow_mut().insert(
                measure::unfold_name(&d.name),
                format!(
                    "`{}` is a member of a mutual `decreases` group, whose unfolding \
                     equations are deferred (docs/language/recursion/mutual-recursion-design.md §6)",
                    base_name(&d.name)
                ),
            );
        }
        Ok(())
    }
}

impl Declarations<'_> {
    /// A written type as the declaration it names, where it names one.
    pub(crate) fn ctor_fields_of(&self, scrut: &Ty, ctor: &str) -> Option<Vec<Ty>> {
        match &scrut.kind {
            TyKind::Nat => match ctor {
                "Zero" => Some(Vec::new()),
                "Succ" => Some(vec![scrut.clone()]),
                _ => None,
            },
            TyKind::Named { name, args } => {
                let ind = self.lookup_inductive(name)?;
                // Only the plain parameterized shape: an index or a value
                // parameter puts the field types under binders this
                // substitution does not carry.
                if ind.index.is_some() || !ind.valparams.is_empty() || ind.params.len() != args.len()
                {
                    return None;
                }
                let c = ind.ctors.iter().find(|c| c.name == ctor)?;
                let m: Vec<(String, Ty)> = ind
                    .params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                Some(
                    c.fields
                        .iter()
                        .map(|(_, t)| measure::instantiate_ty(t, &m))
                        .collect(),
                )
            }
            _ => None,
        }
    }
}

impl DeclarationsMut<'_> {
    /// The measure is a `Nat`, checked in the declaration's own parameter
    /// context and *before* anything is generated, so the message says so
    /// rather than surfacing as a mismatch inside a generated `nat::Nat::Lt`.
    fn check_measure_is_nat(&mut self, decl: &Decl, measure: &Expr) -> R<()> {
        self.attempt.prepare();
        self.attempt.goal_arena.configure(count_holes(decl), 0);
        self.refresh_delta_psi();
        let r = Declarations(self).decl_head_cx(decl).map(|cx| {
            self.elab_check(&cx, measure, &Type::Nat, &Level::Zero)
                .map(|_| ())
                .map_err(|error| match error {
                    ElabError::Elab { msg, span } => ElabError::Elab {
                        msg: format!("a `decreases` measure is a `Nat`: {msg}"),
                        span,
                    },
                    other => other,
                })
        });
        self.attempt.finish();
        self.refresh_delta_psi();
        r?
    }
}

impl Declarations<'_> {
    /// The binders a declaration's *measure* is written against: its type
    /// parameters, then its value parameters. This is the prefix of
    /// [`DeclarationsMut::check_decl`]'s telescope builder, as `instance_head_cx` is —
    /// used only for the `decreases` preflight, where the constraint slots and
    /// notation installations a body needs are not yet in play.
    pub(crate) fn decl_head_cx(&self, decl: &Decl) -> R<Cx> {
        let mut cx = Cx::empty();
        for tv in &decl.tyvars {
            let level = Level::constant(tv.level);
            cx.push(
                tv.name.clone(),
                Type::Ty(level.clone()),
                Level::constant(tv.level + 1),
            );
            cx.tyvars.push(TyVar {
                name: tv.name.clone(),
                ty: Type::El {
                    level: level.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
                level,
                depth: cx.names.len(),
            });
        }
        for p in &decl.params {
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            cx.push_skel(p.name.clone(), ty.clone(), lvl, skel_of_ty(&p.ty));
            if let Type::Ty(level) = &ty {
                cx.tyvars.push(TyVar {
                    name: p.name.clone(),
                    ty: Type::El {
                        level: level.clone(),
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    },
                    level: level.clone(),
                    depth: cx.names.len(),
                });
            }
        }
        Ok(cx)
    }
}

impl DeclarationsMut<'_> {
    /// The sole commit point for a checked ordinary declaration.
    ///
    /// Every operation here is infallible. In particular, no declaration can
    /// become visible to later source unless `check_decl` returned a complete
    /// value after the kernel gate.
    pub(crate) fn commit_decl(&mut self, pending: PendingDecl) {
        // Registration bookkeeping as its own column: the Ψ push, the name
        // and provenance tables, the module journal's event, and the δ-world
        // rebuild that follows them (`docs/infrastructure/instrumentation-design.md` §5).
        let _commit = stats::guard(stats::Timer::DeclCommit);
        let PendingDecl {
            aux,
            binding,
            sealed,
            export_proof,
            registration,
            is_axiom,
            direct_dependencies,
        } = pending;
        // A lifted proof has no name to register: like a key-less generated
        // definition, it travels in the module's Ψ suffix.
        for lemma in aux {
            self.psi.commit(lemma);
        }
        let abs = self.psi.bindings.len() as u32;
        if let (Some(kept), Some(proof), GlobalBinding::Tm { ty, .. }) = (&mut self.pass.export_proofs, export_proof, &binding) {
            kept.insert(abs as usize, (Rc::clone(ty), proof));
        }
        match sealed {
            Some(proof) => self.psi.commit_sealed(binding, proof),
            None => self.psi.commit(binding),
        }
        DeltasMut(self).semantic_commit_global(abs, registration, is_axiom, direct_dependencies);
        self.refresh_delta_psi();
    }
}

impl Declarations<'_> {
    /// The binders available in an instance's **head**, for declaration-time
    /// inspection that must elaborate the carrier before the generated
    /// instance declarations exist. Equality carriers need this to infer the
    /// endpoints' type and use its resolved declaration as their registry key
    /// (issues/decidable-equation-carrier.md).
    ///
    /// This is the prefix of [`DeclarationsMut::check_decl`]'s telescope builder:
    /// type parameters, then value parameters. `requires` dictionaries do not
    /// occur in an instance head and therefore deliberately are not in scope.
    pub(crate) fn instance_head_cx(&self, decl: &InstanceDecl) -> R<Cx> {
        let mut cx = Cx::empty();
        for (i, tv) in decl.tyvars.iter().enumerate() {
            if decl.tyvars[..i].iter().any(|other| other.name == tv.name) {
                return err(format!("duplicate type parameter `{}`", tv.name), tv.span);
            }
            let level = Level::constant(tv.level);
            cx.push(
                tv.name.clone(),
                Type::Ty(level.clone()),
                Level::constant(tv.level + 1),
            );
            cx.tyvars.push(TyVar {
                name: tv.name.clone(),
                ty: Type::El {
                    level: level.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
                level,
                depth: cx.names.len(),
            });
        }
        for p in &decl.valparams {
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            cx.push_skel(p.name.clone(), ty.clone(), lvl, skel_of_ty(&p.ty));
            if let Type::Ty(level) = &ty {
                cx.tyvars.push(TyVar {
                    name: p.name.clone(),
                    ty: Type::El {
                        level: level.clone(),
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    },
                    level: level.clone(),
                    depth: cx.names.len(),
                });
            }
        }
        Ok(cx)
    }

    /// A `def`'s value with no written type, inferred: its term, which is
    /// the body, and its type, which is the statement
    /// (docs/metaprogramming/value-definitions-design.md §2.2). A value whose type inference
    /// cannot find is refused with the spelling that fixes it.
    fn infer_value(&self, cx: &Cx, decl: &Decl, e: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, e).map_err(|error| match error {
            ElabError::Elab { msg, span } if msg.contains("infer") => ElabError::Elab {
                msg: format!(
                    "{msg} (`{}` has no written type, so its value must infer one: write it \
                     as `def {}: T = …;`)",
                    decl.name, decl.name
                ),
                span,
            },
            other => other,
        })
    }
}

impl DeclarationsMut<'_> {
    pub(crate) fn check_decl(
        &mut self,
        decl: &Decl,
        reserved_goals: u32,
    ) -> R<PendingDecl> {
        // Keep the writer's declaration, not the constraint-expanded working
        // copy: representation obligations later restate the surface API.
        let surface = match &self.scope.recursion_at_top_surface {
            Some(written) if written.name == decl.name => (**written).clone(),
            _ => decl.clone(),
        };
        // The constraint binders' desugaring at an **indexed** class
        // (docs/language/classes/operation-indexed-classes-design.md §4): the index binders in
        // front of the dictionary, or the dictionary floated past the
        // parameters its index links to. `None` — every declaration with no
        // indexed-class constraint — is the identity and costs one walk of the
        // parameter list.
        let expanded;
        let (decl, ambiguous, symbols) = match Classes(self).expand_constraints(decl)? {
            None => (decl, Vec::new(), Vec::new()),
            Some(x) => {
                expanded = Decl {
                    params: x.params,
                    ..decl.clone()
                };
                (&expanded, x.ambiguous, x.symbols)
            }
        };
        if NameLookup(self).own_declares(&decl.name, &[NameKind::Global]) {
            return err(format!("duplicate name `{}`", decl.name), decl.span);
        }
        NameLookup(self).check_declarable(&decl.name, decl.span)?;
        // `fn D::m(…)` — a member of `D`'s namespace. The attachment is
        // *checked*: `D` has to name a type visible here, which is the whole
        // difference between this and a naming convention
        // (issues/type-owned-members-receiver-slice.md). What is declared is
        // the qualified string, so the base name stays out of the ambient
        // namespace and is reached through the receiver or by qualification.
        // A name with two qualifiers (an instance's member,
        // `Le::Judge::verdict`, or a member function's `Pos` fact,
        // `T::f::pos`) splits at its first `::` like any other: the type owns
        // it, and the declared string is the whole name.
        let member = split_qual(&decl.name);
        if let Some((owner, base)) = member {
            // A **type former** owns a namespace too, as of the 2026-08-17
            // carrier widening (docs/language/classes/decide-class-design.md §2): `Le::Decide` is
            // the canonical name of the decidability instance at `Le`, and it is
            // an ordinary member declaration like every other instance value.
            // Widened here rather than only on the instance path, so that the
            // owner rule is one rule — an instance's canonical name has never
            // been a special kind of declaration, and making it one to avoid
            // this line would be the first time it was.
            //
            // A **function** owns one as well (issues/function-owned-members.md):
            // `theorem ten_pow::pos(i): 0 < ten_pow(i)` is a fact about
            // `ten_pow` named under it, not about its result type. The receiver
            // never reaches it — `f.pos` dispatches on the type of `f`, a
            // function type with no namespace — so qualification is its one
            // route, and the declared string is the same `f::pos` a type's
            // member would be.
            if !Carriers(self).names_a_carrier(owner) {
                if Carriers(self).names_a_function(owner) {
                    // `f::pos` is read as module `f`'s `pos` first
                    // (`names::resolve_kinds`), and functions share modules'
                    // lower-case spelling, so a function named like a visible
                    // module could declare a member its own module could never
                    // reach.
                    let scope = self.names.scope();
                    if owner == scope.module
                        || scope.imports_module(owner)
                        || owner == names::PRELUDE_MODULE
                    {
                        return err(
                            format!(
                                "`{}` would read as `{base}` in the module `{owner}`, not \
                                 as a member of the function `{owner}` — rename the \
                                 function or the module",
                                decl.name
                            ),
                            decl.span,
                        );
                    }
                } else if self.lookup_global(owner).is_some() {
                    return err(
                        format!(
                            "`{owner}` is a theorem, so `{}` attaches to nothing — \
                             members belong to types and functions; name a lemma \
                             about it on its own",
                            decl.name
                        ),
                        decl.span,
                    );
                } else {
                    return err(
                        format!(
                            "`{owner}` is not a type, a type former or a function in \
                             scope, so `{}` attaches to nothing — a member declaration \
                             is `fn <Type>::{base}(…)` or `theorem <function>::{base}(…)`, \
                             and the owner must be declared (or be a kernel type) \
                             before it",
                            decl.name
                        ),
                        decl.span,
                    );
                }
            }
            if base.is_empty() {
                return err("a member needs a name after `::`", decl.span);
            }
        }
        // Reserve the goal prefix *before* anything is elaborated: the
        // telescope and result type are elaborated first and their types end
        // up embedded in the emitted term, so they must live in the same
        // (shifted) world as the body.
        self.attempt
            .goal_arena
            .configure(count_holes(decl) + count_tactic_slots(decl), reserved_goals);
        self.refresh_delta_psi();
        // Elaborate the parameter telescope. Type parameters come first and
        // are ordinary kernel binders at `Ty 0` — level-0 parametric
        // polymorphism, Tarski-style, so a *use* of one in type position is
        // `El A` (docs/language/surface-polymorphism.md §2). They are registered in
        // `cx.tyvars`, the same table an `inductive`'s parameters use while
        // its fields are lowered; the difference is only that these survive
        // into the kernel term.
        //
        // The telescope and the result type are one attributed phase
        // (`docs/infrastructure/instrumentation-design.md` §5): everything a declaration's
        // *statement* costs, as against what its proof costs. The bracket is
        // exclusive, so the resolution, unification and generated-definition
        // work it contains stays in those columns and this one is the walk's
        // own share.
        // A default runs at the call, where an earlier parameter's name is
        // bound to the call's argument for it (`defaults::elab_param_default`).
        // So a default may mention the value parameters before it, and is
        // refused here, rather than at every call, when it mentions its own
        // parameter or a later one (the telescope is ordered, §9.4) or a type
        // parameter, which no alias can bind
        // (issues/parameter-defaults-mention-type-parameters.md).
        for (i, p) in decl.params.iter().enumerate() {
            let Some(default) = p.default.as_deref() else { continue };
            let mentions = |n: &String| datarepr::mentions_free(default, std::slice::from_ref(n), &mut Vec::new());
            if let Some(t) = decl.tyvars.iter().map(|t| &t.name).find(|n| measure::mentions_context(default, n)) {
                return err(
                    format!(
                        "`{}`'s default mentions the type parameter `{t}`, and a default cannot \
                         mention a type parameter yet (issues/parameter-defaults-mention-type-parameters.md): \
                         its expected type already says what `{t}` is at each call",
                        p.name
                    ),
                    default.span,
                );
            }
            if let Some(later) = decl.params[i..].iter().map(|q| &q.name).find(|n| mentions(n)) {
                let whose = if *later == p.name { "its own parameter".to_string() } else { format!("the later parameter `{later}`") };
                return err(
                    format!(
                        "`{}`'s default mentions {whose}: a default reads only the parameters \
                         before it, whose arguments the call has already given",
                        p.name
                    ),
                    default.span,
                );
            }
        }
        let decl_type = stats::guard(stats::Timer::DeclType);
        let mut cx = Cx::empty();
        cx.index_ambiguity = ambiguous.into();
        // The constraint slots' symbols, checked against each other on the way
        // in: §5.2's uniqueness rule runs over the symbol namespace by any mix
        // of slots and `as` (issues/binder-symbol-as-notation.md), and one loop
        // over one table is the whole of it.
        for s in symbols {
            Operators::check_symbol_free(&cx.op_locals, &s.0, decl.span)?;
            cx.op_locals.push(s);
        }
        let mut param_info: Vec<(Type, Level)> = Vec::new();
        for (i, tv) in decl.tyvars.iter().enumerate() {
            let name = &tv.name;
            if decl.tyvars[..i].iter().any(|o| o.name == *name) {
                return err(format!("duplicate type parameter `{name}`"), decl.span);
            }
            if decl.params.iter().any(|p| p.name == *name) {
                return err(
                    format!(
                        "`{name}` is both a type parameter and a parameter of `{}`",
                        decl.name
                    ),
                    decl.span,
                );
            }
            // `<A: Type<n>>`, defaulting to `Type<0>` — the binder is at
            // `Ty n`, which is itself a type at level `n + 1`
            // (docs/language/surface-universe.md §2).
            let level = Level::constant(tv.level);
            let (ty, lvl) = (Type::Ty(level.clone()), Level::constant(tv.level + 1));
            cx.push(name.clone(), ty.clone(), lvl.clone());
            // `El^n A`, scoped at the binder just pushed. `lower_named`
            // weakens by `names.len() - depth`, so recording the depth *after*
            // the push makes `Var(0)` correct here and correct everywhere
            // deeper — the device `Alias` and the inductive `TyVar` both use.
            cx.tyvars.push(TyVar {
                name: name.clone(),
                ty: Type::El {
                    level: level.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
                level,
                depth: cx.names.len(),
            });
            param_info.push((ty, lvl));
        }
        for p in &decl.params {
            // `<A: Monoid>` — the inline constraint form. Its class is checked
            // before its type is elaborated, so `<A: Nat>` complains about the
            // annotation the user wrote and not about `Nat<A>`.
            Classes(self).check_constraint_param(p)?;
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            // A default is checked here, in the telescope of the parameters
            // before it, as well as at each call that leaves it out, so one no
            // call uses is still checked (docs/language/named-arguments-design.md §9.7).
            if let Some(default) = p.default.as_deref() {
                Defaults(self).check_default_at_declaration(&cx, &decl.name, &p.name, default, &ty, &lvl)?;
            }
            // A binder of a class type at a written index is what fills a value
            // slot that unification left open (§5's ladder step 2), for the dot
            // sugars here and for a call's goal in `apply_implicit`.
            if let Some(r) = Classes(self).class_ref_of_ty(&p.ty)
                && !r.args.is_empty()
            {
                cx.dicts.push(Rc::new(DictBinder {
                    name: p.name.clone(),
                    class: r.name,
                    carrier: r.args[0].clone(),
                    index: r.index,
                }));
            }
            cx.push_skel(p.name.clone(), ty.clone(), lvl.clone(), skel_of_ty(&p.ty));
            // `op as ∙` — the binder's **body** spelling, installed for the
            // rest of its scope: the remaining telescope, the result type (so a
            // theorem's *statement* may use it), and the body
            // (issues/binder-symbol-as-notation.md). This is exactly the
            // installation the constraint symbol slot performs
            // (docs/language/classes/operators-onto-classes-design.md §5(b)) into exactly the
            // same table, which is the point — `as` adds a place to *write* a
            // symbol and never a second way to resolve one. The identifier is
            // untouched: `op` still binds the parameter, so the constraint
            // slot, the call sites and every diagnostic go on as before.
            if let Some(sym) = &p.symbol {
                Operators::check_symbol_free(&cx.op_locals, sym, p.span)?;
                cx.op_locals.push((sym.clone(), p.name.clone()));
            }
            // An ordinary parameter *at a universe* — `(A: Type<n>, x: A)` —
            // is usable as a type for the rest of the telescope, by exactly
            // the machinery a declaration's `<A>` uses. That generalization is
            // the round: a type name is any binder whose type is `Type<n>`,
            // not only one bound by `<…>` (docs/language/surface-universe.md §2).
            if let Type::Ty(level) = &ty {
                cx.tyvars.push(TyVar {
                    name: p.name.clone(),
                    ty: Type::El {
                        level: level.clone(),
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    },
                    level: level.clone(),
                    depth: cx.names.len(),
                });
            }
            param_info.push((ty, lvl));
        }
        // Result type and body (checked against it). The declaration's own
        // name goes into scope for the body only: a self-call guarded by a
        // `match` on one of these parameters *is* the induction hypothesis
        // (issues/match-recursion.md), and the lowering constructs the
        // recursor, so there is no fixpoint and nothing new for the kernel.
        //
        // A result-position implicit mark has no consumer this round —
        // callers of `f()` get a computed head with no skeleton — and is
        // refused rather than dropped (docs/language/implicit-binders-design.md §3.4;
        // result-position skeletons on `GlobalInfo` are the named follow-on).
        if has_implicit_mark(&decl.result) {
            return err(IMPLICIT_MARK_REFUSED, decl.result.span);
        }
        // `def x = e;` (docs/metaprogramming/value-definitions-design.md §2.2): the type is
        // `e`'s, so `e` is inferred once and is the body as well.
        let inferred = match &decl.result.kind {
            TyKind::TypeOf(e)
                if decl.value
                    && decl.body.stmts.is_empty()
                    && decl.body.ons.is_empty()
                    && decl.body.result.span == e.span =>
            {
                Some(Declarations(self).infer_value(&cx, decl, e)?)
            }
            _ => None,
        };
        let (res_ty, res_lvl) = match &inferred {
            Some((_, ty, level)) => (ty.clone(), level.clone()),
            None => self.elab_ty(&cx, &decl.result)?,
        };
        drop(decl_type);
        *self.attempt.telescope.borrow_mut() = cx.names.clone();
        // The graph records what the checked proof/body references, not names
        // appearing only in its public statement (issues/axiom-provenance.md).
        self.attempt.direct_dependencies.borrow_mut().clear();
        if decl.kind != DeclKind::Axiom {
            cx.selfref = Some(Rc::new(SelfRef::of_decl(decl)));
        }
        // An axiom has no term to check. Ordinary definitions and theorems
        // elaborate their block exactly as before.
        //
        // The proof/body walk, the other half of the declaration's own work
        // and on every workload measured so far the larger one. Exclusive, so
        // the diagnostic probes, the whnf probes, resolution and the
        // generated definitions minted while walking keep their own columns.
        let decl_body = stats::guard(stats::Timer::DeclBody);
        let body = if decl.kind == DeclKind::Axiom {
            self.solve_goals(&[], &decl.name)?;
            None
        } else if let Some((term, _, _)) = inferred {
            self.solve_goals(&decl.body.ons, &decl.name)?;
            Some(term)
        } else {
            // A `decreases` declaration never reaches here: `elab_measure_decl`
            // has already replaced it by the family of `measure.rs`.
            debug_assert!(decl.decreases.is_none());
            // A corecursive definition (docs/inductives/codata-elaborator-design.md §5):
            // the result is codata and the body calls itself, so the body is
            // one `corec`'s step, checked at the step type with the
            // self-reference turned into seeds rather than induction
            // hypotheses.
            let corec = match cx.selfref.as_ref() {
                Some(selfref) => Codata(self).corec_plan(&cx, decl, selfref, &res_ty, decl.span)?,
                None => None,
            };
            let body = if let Some(site) = &corec {
                let mut bcx = cx.clone();
                bcx.selfref = None;
                bcx.corec = Some(Rc::clone(site));
                let (step_ty, step_lvl) = Codata::corec_body_ty(site);
                let step = statements::check_block(
                    self.0,
                    &bcx,
                    &decl.body,
                    &step_ty,
                    &step_lvl,
                    None,
                    None,
                    true,
                )?;
                Codata(self).corec_close(&cx, decl.tyvars.len(), site, step, decl.span)?
            } else {
                statements::check_block(
                    self.0,
                    &cx,
                    &decl.body,
                    &res_ty,
                    &res_lvl,
                    None,
                    None,
                    true,
                )?
            };
            self.solve_goals(&decl.body.ons, &decl.name)?;
            Some(body)
        };
        // A capacity restart discards this attempt: none of it is gated.
        if self.attempt.goal_arena.restart_requested() {
            return err("internal: restarting declaration for goal capacity", decl.span);
        }
        let (sigma, aux, lifted_world) = self.lift_proved(&decl.name, decl.span)?;
        let lifted = aux.len() as u32;
        let goal_base = self.attempt.goal_arena.base();
        drop(decl_body);

        // Close over the telescope: statement = Π…, proof/body = λ….
        //
        // The binder and result types are **respelled** on the way out
        // (`docs/elaborator/annotation-component-respell-design.md` §2.1): every
        // component that is a registered declaration's lowering becomes
        // `El (D#tycode^δ)`, in the Ψ statement and the body's outer λs both.
        // This runs *after* the body is elaborated — every structural read
        // during elaboration saw the inline types — and *before*
        // `apply_global`, so the references' goal padding is renumbered with
        // everything else. The payoff cascades: an `App` at a call site
        // copies its `dom`/`cod` annotations out of the callee's statement,
        // so respelling the statement once shrinks every later application
        // for free. References are minted against the empty context (the
        // statement's own) at each binder's depth. Through the one emission
        // chokepoint (§2.5), so a statement component that arrived as a code
        // literal is spelled the way every slot copied off it is; the
        // reflection boundary reads a statement back through
        // `unspell_ty_deep`, which is the inverse of the reference half and
        // sees a decoded literal exactly as it would have seen an inline one.
        //
        // Respelling, closing the telescope and the one global substitution
        // are one phase — what the elaborator spends turning a checked pair
        // into the pair the kernel is handed
        // (`docs/infrastructure/instrumentation-design.md` §5).
        let decl_emit = stats::guard(stats::Timer::DeclEmit);
        let empty_cx = Cx::empty();
        let n_params = param_info.len() as u32;
        let mut stmt = match self.emit_ty(&empty_cx, &res_ty, n_params) {
            Some(r) => r,
            None => res_ty,
        };
        let mut stmt_lvl = res_lvl;
        let mut term = body;
        for (i, (dom, dom_lvl)) in param_info.into_iter().enumerate().rev() {
            let dom = match self.emit_ty(&empty_cx, &dom, i as u32) {
                Some(r) => r,
                None => dom,
            };
            term = term.map(|term| Term::Lam {
                dom_level: dom_lvl.clone(),
                cod_level: stmt_lvl.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(term),
            });
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
        // With lifted proofs, their globals sit between Ψ and the goal
        // prefix: shift the committed globals up past them first.
        let term = term.map(|term| term.shift_global_above(lifted, goal_base).apply_global(&sigma));
        let stmt = stmt.shift_global_above(lifted, goal_base).apply_global(&sigma);
        // The declaration is checked in the world its lifted proofs extend.
        // The spike checks it inline and asks no cache.
        let lifted_psi = lifted_world.unwrap_or_else(|| Rc::clone(&self.psi.0));
        drop(decl_emit);

        // The emission audit, on exactly the pair the kernel is about to be
        // handed (`emission_walk`; design §2.5). Off unless asked for.
        if let Some(found) = self.policy.emission_findings.as_ref() {
            let findings =
                emission_walk::walk_decl(self, &decl.name, &stmt, term.as_ref());
            found.borrow_mut().extend(findings);
        }
        self.attribute_image(&decl.name, &stmt, term.as_ref());

        // The kernel is the gate: check the statement, then the term.
        // `stats::time_kernel` attributes exactly this to the kernel half of
        // the frontend suite's phase split (crates/elab/src/stats.rs).
        //
        // An installed gate oracle (`gate.rs`) may vouch for the declaration
        // instead, in which case neither call runs. Nothing installs one by
        // default; `heather check --cache` is the only caller today.
        let empty = LocalCtx::nil();
        if let Some(term) = term.as_ref() {
            let opaque = matches!(decl.kind, DeclKind::Theorem);
            self.gate_bodied(&lifted_psi, &decl.name, decl.span, &empty, &stmt, &stmt_lvl, term, opaque)?;
        } else {
            // Axioms extend the trusted assumptions, but their statements are
            // still required to be well-formed kernel types.
            stats::time_kernel(|| {
                self.kernel_check_type(&self.psi, Layer::Prog, &empty, &stmt, &stmt_lvl)
            })
            .map_err(|e| {
                Refusals(self).kernel_refusal(&decl.name, decl.span, e, &self.psi, Layer::Prog, &empty, None, &stmt, &stmt_lvl)
            })?;
        }

        // A default's names resolve where the declaration was written, at
        // every call (docs/language/named-arguments-design.md §9.4).
        let default_scope = Rc::new(self.names.scope().clone());
        let params = Rc::new(
            decl.tyvars
                .iter()
                .map(|t| ParamMeta {
                    name: t.name.clone(),
                    implicit: true,
                    is_type: true,
                    is_self: false,
                    skel: None,
                    solver: None,
                    default: None,
                })
                .chain(decl.params.iter().enumerate().map(|(i, p)| ParamMeta {
                    name: p.name.clone(),
                    implicit: p.implicit,
                    is_type: false,
                    is_self: p.is_self,
                    // The parameter's own domain skeleton — what argument
                    // lambdas are checked against and what suppresses
                    // bare-reference insertion at this argument (§5.3/§6.1).
                    skel: skel_of_ty(&p.ty),
                    solver: p.solver.map(|_| Rc::new(p.ty.clone())),
                    default: p.default.as_ref().map(|e| Rc::new(application::ParamDefault {
                        expr: (**e).clone(),
                        scope: Rc::clone(&default_scope),
                        owner: qkey(self.names.module(), &decl.name),
                        index: decl.tyvars.len() + i,
                    })),
                }))
                .collect::<Vec<_>>(),
        );
        // All three kinds bind a closed `Trm_c` global; the `fn` is the one that
        // keeps its body, so later declarations reference it as `u^δ` and
        // conversion δ-unfolds it at p when — and only when — running it is
        // what the comparison needs.
        //
        // A `theorem` stays opaque even though its proof is right here:
        // proofs are transported, never evaluated, and a transparent proof
        // would put the whole proof term back into every conversion that
        // mentions the theorem.
        //
        // Its proof is kept *sealed* beside the binding when the statement
        // carries data (`sealing.rs`): still invisible to δ, to every
        // comparison and to the binding's interface, but opened where an
        // elimination is stuck on the theorem — a witness projected, a
        // branch matched on (`issues/theorem-witness-unfolding.md`, D).
        let sealed = match (decl.kind, &term) {
            (DeclKind::Theorem, Some(proof)) if sealing::carries_data(&lifted_psi, &stmt) => {
                Some(Rc::new(proof.clone()))
            }
            _ => None,
        };
        let export_proof = match (decl.kind, &term) {
            (DeclKind::Theorem, Some(proof)) if self.pass.export_proofs.is_some() => Some(Rc::new(proof.clone())),
            _ => None,
        };
        let binding = GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(stmt),
            level: stmt_lvl,
            body: match decl.kind {
                DeclKind::Fn => Some(Rc::new(term.expect("a function has a body"))),
                DeclKind::Theorem | DeclKind::Axiom => None,
            },
        };
        if decl.kind == DeclKind::Axiom
            && let Some(gate) = self.policy.gate.as_ref()
        {
            gate.assumption(&self.psi, &decl.name, &binding);
        }
        let direct_dependencies = self
            .attempt
            .direct_dependencies
            .borrow()
            .iter()
            .cloned()
            .collect();
        Ok(PendingDecl {
            aux,
            binding,
            sealed,
            export_proof,
            is_axiom: decl.kind == DeclKind::Axiom,
            direct_dependencies,
            registration: GlobalRegistration {
                name: decl.name.clone(),
                key: qkey(self.names.module(), &decl.name),
                params,
                member_base: member.map(|(_, base)| base.to_string()),
                surface,
            },
        })
    }

    /// Record every recorded declaration the term the gate is about to be
    /// handed reaches, as a dependency of the declaration being checked.
    ///
    /// The edges recorded where a written name resolves are the ones the
    /// source spells. A tactic builds its references from name strings, a
    /// reduction can leave a callee's references in the term, and neither
    /// passes a resolution site: `--deny-axioms` accepted a theorem whose
    /// `simp` set named an axiom
    /// (`issues/axiom-provenance-misses-tactic-references.md`). So the
    /// edges are read off the term itself, which is exactly what the verdict
    /// is about. Called for a declaration and for each proof it lifts, whose
    /// own references reach the declaration this way.
    ///
    /// `scope` is the length of the Ψ the term is scoped in; a reference past
    /// the committed bindings is one of this declaration's own lifted proofs,
    /// which this has already read.
    fn record_reached(&self, scope: usize, body: &Term) {
        let mut reached = Vec::new();
        for abs in global_positions(body, scope) {
            self.reached_from(abs, &mut reached);
        }
        let mut direct = self.attempt.direct_dependencies.borrow_mut();
        for key in reached {
            direct.insert(key);
        }
    }

    /// The recorded declarations a reference to Ψ position `abs` stands for:
    /// itself when it has a provenance record, and otherwise what it was
    /// made from.
    ///
    /// A global with no record and a body (a generated definition, a
    /// transparent lifted value) reaches what its body reaches. One with
    /// neither is a proof lifted out of a declaration, committed just before
    /// it (`commit_decl`): it stands for that declaration, the next recorded
    /// one, whose record holds everything the lifted proof reached.
    fn reached_from(&self, abs: usize, out: &mut Vec<String>) {
        let Ok(at) = u32::try_from(abs) else { return };
        if let Some(key) = self.names.global_name_at(at)
            && self.provenance.is_recorded(key)
        {
            out.push(key.to_string());
            return;
        }
        match self.psi.bindings.get(abs) {
            Some(GlobalBinding::Tm { body: Some(body), .. }) => {
                let through = self.provenance.reached_through(at, body, || {
                    let mut inner = Vec::new();
                    // A binding is scoped in its own prefix of Ψ.
                    for below in global_positions(body, abs) {
                        self.reached_from(below, &mut inner);
                    }
                    inner.sort();
                    inner.dedup();
                    inner
                });
                out.extend(through.iter().cloned());
            }
            Some(GlobalBinding::Tm { body: None, .. }) => {
                let owner = (at + 1..self.psi.bindings.len() as u32)
                    .filter_map(|later| self.names.global_name_at(later))
                    .find(|key| self.provenance.is_recorded(key));
                if let Some(key) = owner {
                    out.push(key.to_string());
                }
            }
            _ => {}
        }
    }

    /// The kernel gate for one bodied global in `psi`: the cache oracle, then
    /// the statement here, then the body here or on the pool. Shared by a
    /// declaration and the tactic proofs it lifts, which extend Ψ before it
    /// (`docs/tactics/bv-omega-design.md` §7).
    #[allow(clippy::too_many_arguments)]
    fn gate_bodied(
        &mut self,
        psi: &Rc<GlobalCtx>,
        name: &str,
        span: Span,
        ctx: &LocalCtx,
        ty: &Type,
        level: &Level,
        body: &Term,
        opaque: bool,
    ) -> R<()> {
        // A declaration of a module that imports interface definitions is
        // checked with their bodies withheld, as the elaborator's worlds are
        // (docs/language/interface-definitions-design.md §3): the gate's conversion is
        // where a proof's unfolding actually happens. Withholding only takes
        // δ-steps away, so the gate never accepts more than it would without.
        self.record_reached(psi.bindings.len(), body);
        let gated;
        let psi = match self.delta_psi.withheld.clone() {
            Some(withheld) => {
                gated = Rc::new(psi.withholding(Some(withheld)));
                &gated
            }
            None => psi,
        };
        let item = gate::GateItem { name, ctx, ty, level, body, opaque, layer: Layer::Code, lands_in_psi: true };
        if self.policy.gate.as_ref().is_some_and(|g| g.admits(psi, &item)) {
            return Ok(());
        }
        // Whatever sealed proofs the statement or the body open are part of
        // what the verdict is about (`KernelGate::accepted`).
        let recording = heather_kernel::unseal::Recording::start();
        // The statement is checked here, synchronously, whatever the pool is
        // doing: every dependent needs it, and it is the cheap half
        // (`docs/kernel/parallel-kernel-gate-design.md` §2).
        stats::time_kernel(|| self.kernel_check_type(psi, Layer::Prog, ctx, ty, level))
            .map_err(|e| Refusals(self).kernel_refusal(name, span, e, psi, Layer::Prog, ctx, None, ty, level))?;
        if self.gate_is_inline() {
            // A serial replay may already hold this exact obligation's
            // verdict, earned by a worker of the pass it replaces
            // (`docs/kernel/parallel-kernel-gate-design.md` §5.2). `None` — which is
            // every ordinary run — asks the kernel.
            let verdict = match self.pass.kernel_replay.reuse(psi.bindings.len(), self.policy.fuel, &item) {
                Some(verdict) => verdict,
                None => stats::time_kernel(|| self.kernel_check_term(psi, Layer::Code, ctx, body, ty, level)),
            };
            verdict.map_err(|e| {
                let refusal = Refusals(self).kernel_refusal(name, span, e, psi, Layer::Code, ctx, Some(body), ty, level);
                InterfaceDefs(self).withheld_note(refusal, psi, ty, Some(body))
            })?;
            let unsealed = recording.finish();
            if let Some(g) = self.policy.gate.as_ref() {
                g.accepted(psi, &item, &unsealed);
            }
        } else {
            // Queued against the Ψ the binding is about to extend;
            // `accepted` travels with it and is replayed at the join.
            drop(item);
            stats::count(stats::Counter::DeclsGated);
            self.0.pass.kernel_pool.submit(pool::Deferred {
                name: name.to_string(),
                span,
                psi: Rc::clone(psi),
                ctx: ctx.clone(),
                ty: ty.clone(),
                level: level.clone(),
                body: body.clone(),
                opaque,
                layer: Layer::Code,
                lands_in_psi: true,
                fuel: self.0.policy.fuel,
                unsealed: recording.finish(),
                row: stats::current_item(),
            });
        }
        Ok(())
    }

    /// The declaration's goal substitution, with every lifted tactic proof
    /// (`docs/tactics/bv-omega-design.md` §7) kernel-checked as a global of its own,
    /// in its own context, and substituted as a reference to it. Returns the
    /// substitution, the lifted globals in order, and the world they extend
    /// Ψ to (`None` when nothing was lifted). The substitution's payloads are
    /// scoped in that world: a caller shifts its term's committed globals up
    /// past the lifted ones before applying it.
    fn lift_proved(&mut self, name: &str, span: Span) -> R<(GlobalSubst, Vec<GlobalBinding>, Option<Rc<GlobalCtx>>)> {
        let mut sigma = self.goal_subst();
        let lifted = self.attempt.goal_arena.lifted();
        if lifted.is_empty() {
            return Ok((sigma, Vec::new(), None));
        }
        let base = self.attempt.goal_arena.base();
        let originals: Vec<bool> = vec![true; sigma.entries.len()];
        let mut originals = originals;
        // Out of the goal world, into Ψ and the lifted slots before this
        // one: an earlier lifted proof or value is referred to (a `let`
        // bound to one is inlined into what follows it, and `omega` names
        // its atom list), and any other goal is refused, which the two
        // dummies would disagree about.
        let mut world: GlobalCtx = (*self.psi).clone();
        // A lifted proof is committed like any declaration: the `j`th is the
        // constant just past Ψ's.
        let first = world.bindings.len() as u32;
        let mut aux = Vec::new();
        let mut earlier: HashMap<usize, (usize, LocalCtx)> = HashMap::new();
        // Slots kept inline, each with how many were lifted before it: its
        // payload is scoped past those, and shifted past the rest at the end.
        let mut inline: Vec<(usize, u32)> = Vec::new();
        for slot in lifted.into_iter() {
            let j = aux.len();
            let out = |dummy: Term| out_of_goals(base, first, &earlier, dummy);
            let (zero, one) = (out(Term::Zero), out(Term::Succ(Rc::new(Term::Zero))));
            let into = |sigma: &GlobalSubst| (
                slot.gamma.shift_global_above(j as u32, base).apply_global(sigma),
                slot.ty.shift_global_above(j as u32, base).apply_global(sigma),
                slot.body.shift_global_above(j as u32, base).apply_global(sigma),
            );
            let (gamma, ty, body) = into(&zero);
            if (gamma.clone(), ty.clone(), body.clone()) != into(&one) {
                return err("internal: a lifted proof mentions a goal", span);
            }
            // Its context is checked here too: a declaration's own gate never
            // sees a nonempty one. A context or statement the kernel cannot
            // type on its own (one the body's checking direction supplied, as
            // a `λ r f` against a coinductive goal's step does) keeps the
            // proof inline, where it was checked before lifting.
            let at = Rc::new(world.clone());
            let standalone = stats::time_kernel(|| typing::check_local_ctx(&at, 0, Layer::Prog, &gamma, self.policy.fuel)).is_ok()
                && stats::time_kernel(|| self.kernel_check_type(&at, Layer::Prog, &gamma, &ty, &slot.level)).is_ok();
            if !standalone {
                if slot.transparent {
                    return err("internal: a named value's context does not check on its own", span);
                }
                sigma.entries[slot.slot] = heather_kernel::subst::GlobalEntry::Tm(Rc::new(body));
                originals[slot.slot] = false;
                inline.push((slot.slot, j as u32));
                continue;
            }
            self.gate_bodied(&at, &format!("{name}#aux{j}"), span, &gamma, &ty, &slot.level, &body, !slot.transparent)?;
            let binding = GlobalBinding::Tm {
                ctx: gamma.clone(),
                layer: Layer::Code,
                ty: Rc::new(ty),
                level: slot.level,
                body: slot.transparent.then(|| Rc::new(body)),
            };
            world.commit(binding.clone());
            aux.push(binding);
            earlier.insert(slot.slot, (j, gamma.clone()));
            sigma.entries[slot.slot] = heather_kernel::subst::GlobalEntry::Tm(Rc::new(Term::GlobalTm {
                var: GlobalVar::constant(first + j as u32),
                subst: LocalSubst::id(&gamma),
            }));
            originals[slot.slot] = false;
        }
        let m = aux.len() as u32;
        // The goal substitution's own payloads are scoped in Ψ: past every
        // lifted proof. An inline proof's, past the ones after it.
        for (k, entry) in sigma.entries.iter_mut().enumerate() {
            if originals[k]
                && let heather_kernel::subst::GlobalEntry::Tm(t) = entry
            {
                *t = Rc::new(t.shift_global(m));
            }
        }
        for (k, before) in inline {
            if let heather_kernel::subst::GlobalEntry::Tm(t) = &mut sigma.entries[k] {
                *t = Rc::new(t.shift_global(m - before));
            }
        }
        // A discharge (`on ?g := …`) is elaborated in the goal world, and a
        // goal's statement can mention a lifted slot (a search in the
        // declaration's statement, `f(x, p := bv_omega)`), which its proof
        // then mentions too: re-scope it like a lifted proof, the lifted
        // slots as the constants just committed
        // (issues/goal-hole-beside-a-search-in-the-statement.md).
        for (slot, solution) in self.attempt.goal_arena.discharged() {
            let out = |dummy: Term| out_of_goals(base, first, &earlier, dummy);
            let shifted = solution.shift_global_above(m, base);
            let body = shifted.apply_global(&out(Term::Zero));
            if body != shifted.apply_global(&out(Term::Succ(Rc::new(Term::Zero)))) {
                return err("internal: a goal's discharge mentions another goal", span);
            }
            sigma.entries[slot] = heather_kernel::subst::GlobalEntry::Tm(Rc::new(body));
        }
        Ok((sigma, aux, Some(Rc::new(world))))
    }
}

/// The way out of the goal world for a lifted slot's term or a discharge:
/// the `base` slots replaced, each lifted one in `earlier` (slot ↦ its order
/// among the lifted and its context) by a reference to the constant committed
/// for it at `first + order`, every other by `dummy`. Its caller compares the
/// results for two dummies, so a term that reaches any other goal is refused.
fn out_of_goals(base: u32, first: u32, earlier: &HashMap<usize, (usize, LocalCtx)>, dummy: Term) -> GlobalSubst {
    GlobalSubst {
        entries: (0..base as usize)
            .map(|k| {
                heather_kernel::subst::GlobalEntry::Tm(Rc::new(match earlier.get(&k) {
                    Some((i, delta)) => Term::GlobalTm { var: GlobalVar::constant(first + *i as u32), subst: LocalSubst::id(delta) },
                    None => dummy.clone(),
                }))
            })
            .collect(),
    }
}

impl Declarations<'_> {
    /// `cx` with every binder's type in the emission spelling
    /// ([`Elaborator::annotation_type`]), the context a lifted proof or a named
    /// value is committed in. The kernel types the body's binders by the
    /// spellings the declaration emitted (its statement's `Π` domains, its
    /// `λ` annotations), and a slot reference `u^{id}` checks each of those
    /// binders against the slot's own context: stored as the elaborator
    /// keeps it, with a coded declaration inline, every reference converted
    /// an inline copy of `X86Profile` or `Stack<M>` against its `El` name,
    /// once per binder per tactic call (`omega`'s atom list is one such
    /// reference per call). Respelled, the two are one syntax and the
    /// conversion is the reflexivity shortcut.
    pub(crate) fn emitted_cx(&self, cx: &Cx) -> Cx {
        let n = cx.gamma.len();
        let scope = self.psi.bindings.len();
        let mut entries = Vec::with_capacity(n);
        let mut changed = false;
        for i in 0..n {
            let entry = cx.gamma.entries.get(i).expect("a binder in range");
            let key = (Rc::as_ptr(&entry.ty) as usize, i, scope);
            let known = self.attempt.emitted_entries.borrow().get(&key).map(|(_, ty)| Rc::clone(ty));
            let ty = match known {
                Some(ty) => ty,
                None => {
                    let ty = self.emit_ty(&cx.prefix(i), &entry.ty, 0).map_or_else(|| Rc::clone(&entry.ty), Rc::new);
                    self.attempt.emitted_entries.borrow_mut().insert(key, (Rc::clone(&entry.ty), Rc::clone(&ty)));
                    ty
                }
            };
            changed |= !Rc::ptr_eq(&ty, &entry.ty);
            entries.push(heather_kernel::term::CtxEntry { ty, level: entry.level.clone() });
        }
        if !changed {
            return cx.clone();
        }
        let mut out = cx.clone();
        out.gamma = LocalCtx::from_vec(cx.gamma.base, entries);
        out
    }
}

/// The Ψ positions of the free global references in `t`, a term scoped in a
/// Ψ of length `scope`, each once and in order.
fn global_positions(t: &Term, scope: usize) -> Vec<usize> {
    let mut found = std::collections::BTreeSet::new();
    let _ = t.reindex_global(&mut |r| {
        let position = match r {
            GlobalRef::Var(i) => scope.checked_sub(1 + i as usize),
            GlobalRef::Const(p) => Some(p as usize),
        };
        found.extend(position);
        Some(r)
    });
    found.into_iter().collect()
}
