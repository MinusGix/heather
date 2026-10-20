//! Indexed dictionary-goal construction for dispatch.
//!
//! Value indices are filled from the nearest compatible dictionary binder or
//! an explicit designation. This module owns that ladder and its refusal.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, OpFixity, Span, Ty, TyKind};

use super::Carrier;
use crate::inductive::Inductive;
use crate::{Cx, ElabError, Elaborator, ParamMeta, Sol, traits, zonked};

impl Elaborator {
    /// The value-slot ladder's **step 2** at a goal the dot sugars are
    /// building (`docs/operation-indexed-classes-design.md` §5, §5.1): a
    /// binder in scope of the goal's class — or of a descendant, whose
    /// `extends` chain passes the index up unchanged — answers what the index
    /// is. Innermost first, exactly as the resolver's own scope pass.
    ///
    /// The index comes back as **surface** expressions at the goal's class, so
    /// the goal is built by the ordinary value-argument path and nothing here
    /// has to re-scope a kernel term. `None` is "no scope binder pins the
    /// slot", and its consumer refuses by name.
    pub(crate) fn scope_index(
        &self,
        cx: &Cx,
        target: &str,
        carrier: &Type,
        clvl: &Level,
    ) -> Option<Vec<Expr>> {
        let tkey = self.key_of(target)?;
        for d in cx.dicts.iter().rev() {
            let Some(dkey) = self.key_of(&d.class) else {
                continue;
            };
            let Some(dinfo) = self.traits.class(&dkey) else {
                continue;
            };
            let index = if dkey == tkey {
                d.index.clone()
            } else {
                // Not this binder's class and not one of its ancestors: try the
                // next binder out rather than giving up on the scope.
                let mut matching = dinfo
                    .ancestors
                    .iter()
                    .filter(|r| self.key_of(&r.name).as_deref() == Some(tkey.as_str()));
                let Some(anc) = matching.next() else {
                    continue;
                };
                // A descendant containing two fibers does not determine an
                // unqualified index. The caller will issue the ordinary
                // value-slot ambiguity diagnostic; an explicit tagged
                // projection remains available.
                if matching.next().is_some() {
                    continue;
                }
                // The ancestor's index is written in the child's own
                // value-parameter names (layer 1's `extends` restriction), so
                // instantiating it is the positional lookup.
                anc.index
                    .iter()
                    .map(|a| match &a.kind {
                        ExprKind::Var(n) => dinfo
                            .valparams
                            .iter()
                            .position(|p| p.name == *n)
                            .and_then(|i| d.index.get(i).cloned())
                            .unwrap_or_else(|| a.clone()),
                        _ => a.clone(),
                    })
                    .collect()
            };
            // The carrier has to be *this* one: a second class binder at an
            // unrelated type is not an answer.
            let Ok((dc, dlvl)) = self.elab_ty(cx, &d.carrier) else {
                continue;
            };
            if !self.conv_types(cx, &dc, carrier, clvl) || dlvl != *clvl {
                continue;
            }
            return Some(index);
        }
        None
    }

    /// The value arguments of a dot sugar's goal
    /// (`docs/operation-indexed-classes-design.md` §5.1): empty at an
    /// unindexed class (every goal that predates this design), the scope
    /// binder's index at an indexed one, and the value-slot refusal where
    /// scope has no answer. `Ok(None)` is "this candidate cannot be built at
    /// all", which the caller skips as it always did.
    pub(crate) fn index_vargs(
        &self,
        cx: &Cx,
        info: &traits::ClassInfo,
        ind: &Inductive,
        targs: &[(Type, Level)],
        subject: &str,
        span: Span,
    ) -> Result<Option<Vec<(Term, Type, Level)>>, ElabError> {
        if info.valparams.is_empty() {
            return Ok(Some(Vec::new()));
        }
        let (carrier, clvl) = &targs[0];
        let Some(index) = self.scope_index(cx, &info.name, carrier, clvl) else {
            // The carrier's head where it has one: at `Bool` the refusal lists
            // the two Bool structures and not every instance of the class.
            let head = self.carrier_of_ty(cx, carrier, span);
            return Err(self.value_slot_refusal(info, subject, head.as_ref(), span));
        };
        match self.valparam_args(cx, ind, targs, &index, span) {
            Ok(v) => Ok(Some(v)),
            Err(_) => Ok(None),
        }
    }

    /// Fill a blocked goal's **index slots** from a dictionary in scope
    /// (`docs/operation-indexed-classes-design.md` §5, ladder step 2).
    ///
    /// The goal's carrier is itself a scratch-world meta here, so the scope
    /// binder is chosen by class alone — innermost first, the goal's class or
    /// a descendant. That is a *proposal* and not a decision: the filled goal
    /// still has to resolve, and the answer still passes the kernel gate, so a
    /// wrong guess costs a refusal and never a wrong term.
    ///
    /// `true` when it filled at least one slot.
    pub(crate) fn fill_index_from_scope(
        &self,
        cx: &Cx,
        goal: Option<&Ty>,
        params: &[ParamMeta],
        slot_param: &[usize],
        sols: &mut [Sol],
    ) -> bool {
        let Some(r) = goal.and_then(|t| self.class_ref_of_ty(t)) else {
            return false;
        };
        if r.index.is_empty() {
            return false;
        }
        let Some(tkey) = self.key_of(&r.name) else {
            return false;
        };
        let mut filled = false;
        for a in &r.index {
            let ExprKind::Var(nm) = &a.kind else { continue };
            let Some(pi) = params.iter().position(|p| p.name == *nm) else {
                continue;
            };
            let Some(slot) = slot_param.iter().position(|&s| s == pi) else {
                continue;
            };
            if sols[slot].solved().is_some() || matches!(sols[slot], Sol::Withheld) {
                continue;
            }
            let Some(e) = self.scope_dict_index(cx, &tkey) else {
                continue;
            };
            let Some(idx) = r.index.iter().position(|x| std::ptr::eq(x, a)) else {
                continue;
            };
            let Some(e) = e.get(idx).cloned() else {
                continue;
            };
            let Ok((t, _, _)) = self.elab_infer(cx, &e) else {
                continue;
            };
            sols[slot] = Sol::Solved(Rc::new(t));
            filled = true;
        }
        filled
    }

    /// Fill a blocked goal's **index slots** from the designation table —
    /// the value-slot ladder's step 3
    /// (`docs/operation-indexed-classes-design.md` §5, built in
    /// `docs/operators-onto-classes-design.md` §5).
    ///
    /// This is what makes `sum_all(ns)` work at a caller who names no
    /// operation: `sum_all`'s constraint was written `<A: Monoid(+)>`, so its
    /// index binder carries the symbol `+`, the carrier is already pinned to
    /// `Nat` by the argument, and the table says `+` at `Nat` is `add`. The
    /// source is **named in the callee's signature** — this is not a search
    /// over instances and not a default: with no `(+)` written there is
    /// nothing here to consult.
    ///
    /// `true` when it filled at least one slot.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn fill_index_from_designation(
        &self,
        cx: &Cx,
        goal: Option<&Ty>,
        params: &[ParamMeta],
        slot_param: &[usize],
        sols: &mut [Sol],
        meta_doms: &[Type],
        n: u32,
        applied: Option<&Term>,
        span: Span,
    ) -> bool {
        let Some(r) = goal.and_then(|t| self.class_ref_of_ty(t)) else {
            return false;
        };
        if r.index.is_empty() {
            return false;
        }
        // Only a slot the callee designated is fillable, so decide that before
        // paying for the carrier.
        if !r.index.iter().any(|a| match &a.kind {
            ExprKind::Var(n) => traits::op_index_symbol(n).is_some(),
            _ => false,
        }) {
            return false;
        }
        let Some(head) = self.goal_carrier_head(cx, r.args.first(), params, slot_param, sols, n, applied, span)
        else {
            return false;
        };
        let mut filled = false;
        for a in &r.index {
            let ExprKind::Var(nm) = &a.kind else { continue };
            let Some(sym) = traits::op_index_symbol(nm) else {
                continue;
            };
            let Some(pi) = params.iter().position(|p| p.name == *nm) else {
                continue;
            };
            let Some(slot) = slot_param.iter().position(|&s| s == pi) else {
                continue;
            };
            if sols[slot].solved().is_some() || matches!(sols[slot], Sol::Withheld) {
                continue;
            }
            let Some(op) = self.designated(sym, OpFixity::Infix, &head.key) else {
                continue;
            };
            // **Checked** against the slot's own domain, not inferred: the
            // designated operation is emitted bare (§3.2), so a generic one
            // — `append` at `List<B>` — has an element type that only the
            // domain can pin. The domain is the index binder's declared type
            // at the carrier this call solved, which is meta-free exactly
            // when the carrier is, and a failure here is a rung that did not
            // fire rather than an error.
            let Some(dom) = meta_doms.get(slot).and_then(|d| zonked(d, n, sols)) else {
                continue;
            };
            let e = Expr {
                kind: ExprKind::Var(op),
                span,
            };
            let Ok(t) = self.elab_check(cx, &e, &dom, &Level::Zero) else {
                continue;
            };
            sols[slot] = Sol::Solved(Rc::new(t));
            filled = true;
        }
        filled
    }

    /// The head of a blocked goal's carrier, where the goal's *written* carrier
    /// is one of the callee's own type parameters and that parameter has
    /// already been solved. The one thing step 3 needs that scope's step 2 did
    /// not: a designation is keyed on the carrier, so the carrier has to be
    /// known before the table can be asked.
    ///
    /// A solved type-parameter slot holds the carrier's **code**, so `El` of it
    /// is the type and the kernel's own `El ⌜T⌝ ⇝ T` does the decoding — no
    /// second decoder, and nothing to drift. A carrier given as an explicit
    /// type argument (`le_of_lt<Rat>(…)`) has no slot: its code is read off
    /// `applied`, the call's spine up to the goal, in the scratch world.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn goal_carrier_head(
        &self,
        cx: &Cx,
        carrier: Option<&Ty>,
        params: &[ParamMeta],
        slot_param: &[usize],
        sols: &[Sol],
        n: u32,
        applied: Option<&Term>,
        span: Span,
    ) -> Option<Carrier> {
        let TyKind::Named { name, args } = &carrier?.kind else {
            return None;
        };
        if !args.is_empty() {
            return None;
        }
        // A carrier written concretely in the signature needs no lookup — but
        // it does need resolving, since the name is a *spelling* the callee's
        // module wrote and the table is keyed on declarations.
        if !params.iter().any(|p| p.name == *name) {
            return self.names_a_type(name).then(|| Carrier {
                written: name.clone(),
                key: self.carrier_key(name),
            });
        }
        let pi = params.iter().position(|p| p.name == *name)?;
        let code = match slot_param.iter().position(|&s| s == pi) {
            Some(slot) => Rc::clone(sols[slot].solved()?),
            None => {
                let mut spine = Vec::new();
                let mut head = applied?;
                while let Some((fun, arg)) = crate::spelling::app_of(head) {
                    spine.push(&**arg);
                    head = fun;
                }
                spine.reverse();
                Rc::new(crate::unification::zonked_tm(spine.get(pi)?, n, sols)?)
            }
        };
        let ty = Type::El {
            level: Level::Zero,
            tm: code,
        };
        self.carrier_of_ty(cx, &ty, span)
    }

    /// The innermost dictionary in scope whose class is `tkey` or a descendant
    /// of it, with its index expressed **at that class**.
    pub(crate) fn scope_dict_index(&self, cx: &Cx, tkey: &str) -> Option<Vec<Expr>> {
        for d in cx.dicts.iter().rev() {
            let Some(dkey) = self.key_of(&d.class) else {
                continue;
            };
            let Some(dinfo) = self.traits.class(&dkey) else {
                continue;
            };
            if dkey == tkey {
                return Some(d.index.clone());
            }
            let mut matching = dinfo
                .ancestors
                .iter()
                .filter(|r| self.key_of(&r.name).as_deref() == Some(tkey));
            let Some(anc) = matching.next() else {
                continue;
            };
            if matching.next().is_some() {
                continue;
            }
            return Some(
                anc.index
                    .iter()
                    .map(|a| match &a.kind {
                        ExprKind::Var(nm) => dinfo
                            .valparams
                            .iter()
                            .position(|p| p.name == *nm)
                            .and_then(|i| d.index.get(i).cloned())
                            .unwrap_or_else(|| a.clone()),
                        _ => a.clone(),
                    })
                    .collect(),
            );
        }
        None
    }

    /// `d.op` — the index of a named dictionary in scope, as the expression
    /// its binder was written at (§5.2). `None` for every name that is not a
    /// dictionary binder and every `.f` that is not one of its class's
    /// indices, so an ordinary field projection is untouched.
    pub(crate) fn index_of_dict(&self, cx: &Cx, dict: &str, name: &str) -> Option<Expr> {
        let d = cx.dicts.iter().rev().find(|d| d.name == dict)?;
        let info = self.lookup_class(&d.class)?;
        let k = info.valparams.iter().position(|p| p.name == name)?;
        d.index.get(k).cloned()
    }

    /// The value-slot refusal (`docs/operation-indexed-classes-design.md` §5,
    /// §11): the slot, the class, and **every registered instance that would
    /// answer**, as data. This is the diagnostic the whole design leans on —
    /// at `Bool` it names both monoids with their indices, which is what makes
    /// refusing better than nominating.
    pub(crate) fn value_slot_refusal(
        &self,
        class: &traits::ClassInfo,
        subject: &str,
        head: Option<&Carrier>,
        span: Span,
    ) -> ElabError {
        let Some(ckey) = self.key_of(&class.name) else {
            return ElabError::Elab {
                msg: format!("`{}` is not in scope", class.name),
                span,
            };
        };
        // Both registries key the carrier by its *resolved* declaration
        // (docs/instance-resolved-key-design.md §3), and the carrier read off
        // the lowered type carries that key beside its spelling, so this
        // filter and the designation lookup below use the same string the
        // declarations registered.
        let hkey = head.map(|h| h.key.clone());
        let listed: Vec<String> = self
            .traits
            .instances_answering(&ckey, hkey.as_deref())
            .into_iter()
            .map(|written| format!("`{written}`"))
            .collect();
        let slots = class
            .valparams
            .iter()
            .map(|p| format!("`{}`", p.name))
            .collect::<Vec<_>>()
            .join(", ");
        // The designations at this carrier, where it has any
        // (docs/operators-onto-classes-design.md §6, §7). This is §11's polish
        // and it is the difference between a refusal reading as principled and
        // as obtuse: a designation cannot *fill* this slot — the dot sugar
        // names no symbol, and choosing among the symbols at a carrier would
        // be the nomination this whole design deletes — but naming the ones
        // that exist tells the reader, in one line, the binder that works.
        let desig = head
            .map(|h| self.designations_at(&h.key))
            .unwrap_or_default();
        let fix = if desig.is_empty() {
            String::new()
        } else {
            format!(
                " Here {}: take the class as a constraint that names the symbol \
                 (`<A: {}({})>`), which is the spelling that pins the slot.",
                desig
                    .iter()
                    .map(|(s, op)| format!("`{s}` designates `{op}`"))
                    .collect::<Vec<_>>()
                    .join(" and "),
                class.name,
                desig[0].0
            )
        };
        ElabError::Elab {
            msg: format!(
                "the index {slots} of `{}` at `{subject}` is not pinned here: a value slot \
                 is filled by unification, by a binder in scope of the goal's class, or by \
                 a designation the binder names — and never by search, so nothing \
                 nominates and nothing guesses. Registered: {}.{fix} Write the dictionary \
                 you meant (`{subject}::{}(⟨index⟩).⟨field⟩`) or take the class as a \
                 constraint",
                class.name,
                if listed.is_empty() {
                    "no instances".into()
                } else {
                    listed.join(", ")
                },
                class.name
            ),
            span,
        }
    }
}
