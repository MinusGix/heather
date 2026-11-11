//! Built-in match routing and Nat/Fin lowering.
//!
//! This is the central route owner after pattern preparation. Declared,
//! indexed, forded, and Wf matches remain delegated to their existing owners;
//! this module owns built-in dispatch, Nat course-of-values recursion, and the
//! unfolded sum reading of Fin.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Arm, Expr, ExprKind, MatchForm, Span};

use crate::recursion::{Guard, GuardKind};
use crate::surface::walk_expr;
use crate::{Cx, Elaborator, R, embed, err};

/// The enclosing recursion's window of past values, as a nested `match` on the
/// chain's end needs it — see [`Elaborator::chain_convoy`], which builds one,
/// and `docs/course-of-values-recursion-design.md` §5 for why passing it
/// through the `match` is what makes the deeper values usable.
struct Convoy {
    dec: usize,
    preds: Vec<usize>,
    /// How many values are carried.
    d: usize,
    lvl: Level,
    /// The recursion's motive reindexed into the context the nested `match`
    /// sits in, scoped in (that context, z).
    motive: Type,
    /// …and as it was written, for the guards this `match` hands to its arms:
    /// they must be able to reindex it again, deeper in.
    outer_motive: Rc<Type>,
    gamma: LocalCtx,
    /// The window itself, at the nested `match`'s context.
    tuple: Term,
    /// How far the window's **anchor** sits above this `match`'s scrutinee.
    ///
    /// The window always holds the values at the chain read from its head:
    /// component `i` is the value at `preds[i]`, so it is anchored at
    /// `preds[0]` however deep the nesting has gone. The first nested `match`
    /// scrutinizes that head and lifts by nothing; the second scrutinizes the
    /// value one below it, so its window is the same window at `Succ` of its
    /// own scrutinee — and so on down. Re-indexing at the scrutinee instead
    /// would slide every component by one and typecheck nowhere.
    lift: usize,
    /// The recursion's generalized parameters, handed down unchanged
    /// (`generalize.rs`): the arms of a nested `match` were wrapped by the
    /// outer one, and their self-calls apply the same ih.
    generalized: Option<Rc<Vec<usize>>>,
}

impl Convoy {
    /// `Succ^lift(t)` — where the window's head sits, seen from a term at this
    /// `match`'s scrutinee.
    fn anchor(&self, t: Term) -> Term {
        (0..self.lift).fold(t, |t, _| Term::Succ(Rc::new(t)))
    }

    /// The guard for one arm: the window is now the arm's own binder, and
    /// `new_pred` is the predecessor that arm binds — `None` for the `Zero`
    /// arm, which extends the chain by nothing.
    fn guard_at(&self, comps: &[Type], depth: usize, new_pred: Option<usize>) -> Rc<Guard> {
        let mut preds = self.preds.clone();
        preds.extend(new_pred);
        Rc::new(Guard {
            dec: self.dec,
            kind: GuardKind::Nat {
                preds,
                // Shifted past the convoy binder itself, which every caller
                // pushes immediately before asking for this.
                comps: comps.iter().map(|c| c.shift_local(1)).collect(),
                tuple: Term::Var(LocalVar(0)),
                mlvl: self.lvl.clone(),
                depth,
                motive: Rc::clone(&self.outer_motive),
                gamma: self.gamma.clone(),
            },
            rebind: None,
            generalized: self.generalized.clone(),
        })
    }
}

impl Elaborator {
    pub(crate) fn elab_match(
        &self,
        cx: &Cx,
        form: MatchForm,
        // Diagnostics only (`docs/diagnostic-warnings-design.md` §7.1):
        // whether the pattern compiler built this node.
        generated: bool,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        // Deep patterns and the `_` arm, compiled away before the dispatch
        // below sees anything (docs/nested-match-patterns-design.md §9). The
        // pass is idempotent and its fast path is every `match` written
        // before it existed, so calling it here *and* at the two direct
        // `elab_infer` entry points costs nothing.
        let result =
            motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())));
        let independent = motive == result.shift_local(1);
        let prepared = self.prepare_arms(
            cx,
            form,
            generated,
            arms,
            &scrut_t,
            scrut_ty,
            scrut_lvl,
            &result,
            independent,
            &mlvl,
            span,
        )?;
        let (cx, arms) = match &prepared {
            Some((c, a)) => (c, a.as_slice()),
            None => (cx, arms),
        };
        let split = crate::recursion::case_split(cx, &scrut_t, arms);
        let cx = split.as_ref().unwrap_or(cx);
        let head = self.whnf(cx, scrut_ty, span)?;
        // An indexed family in family form (docs/inductive-indexed-lowering.md
        // §6) — checked on the *raw* type, since whnf at a literal index
        // reduces the family away, index and all. The `Empty` case wins
        // first: a family whose branch at this literal index is `Empty`
        // (`Fin(0)`) is matched as the empty type, arms and all.
        if let Some((ind, fam)) = self.iwf_of_at(cx, scrut_ty) {
            let (motive2, how) = self.iwf_match_motive(cx, &ind, &fam, &motive, &mlvl, span)?;
            return self
                .elab_match_iwf(cx, form, &ind, &fam, arms, scrut_t, motive2, mlvl, how, span);
        }
        if !matches!(head, Type::Empty { .. })
            && let Some((ind, fam)) = self.indexed_of_at(cx, scrut_ty)
        {
            let motive2 = self.generalize_index(cx, &motive, &fam.idx);
            return self
                .elab_match_indexed(cx, form, &ind, &fam, arms, scrut_t, motive2, mlvl, span);
        }
        if let Some(ind) = self.tag_of(&head) {
            return self.elab_match_data(
                cx, form, &ind, arms, scrut_t, &head, scrut_lvl, motive, mlvl, span,
            );
        }
        // `Fin(n)` (docs/surface-fin-indexing-design.md §4.2). Tested on the
        // **raw** scrutinee type for the same reason `indexed_of_at` is: the
        // whnf of `Fin(Succ k)` is a bare `Type::Sum`, which carries no hint
        // that its arms should be called `FZ`/`FS`. After the `tag_of` check,
        // so a declared inductive still wins, and before the `Nat`
        // fall-through.
        if let Type::Fin { len } = &*crate::inductive::decoded(scrut_ty) {
            let len_w = self.whnf_tm(cx, len, span)?;
            match crate::inductive::nat_head(&len_w) {
                // `Fin(0) ⇝ Empty⁰` is a whnf step, so `head` is already
                // `Type::Empty` and `match i { }` *is* `elim_Empty` — the arm
                // below, unchanged (§1.1 finding 1). Nothing to write here.
                crate::inductive::NatHead::Zero => {}
                crate::inductive::NatHead::Succ(k) => {
                    return self.elab_match_fin(cx, form, arms, scrut_t, &k, motive, mlvl, span);
                }
                // Permanent, not a gap: `Fin` has no eliminator of its own
                // (§1.2), so at an open length there is no canonical form to
                // case on. The message names the fix rather than the
                // limitation, and the fix is the shape `nth` itself has.
                crate::inductive::NatHead::Neutral => {
                    let here = match &*len_w {
                        Term::Var(LocalVar(i)) => cx
                            .names
                            .len()
                            .checked_sub(1 + *i as usize)
                            .and_then(|p| cx.names.get(p))
                            .map(|n| format!("; here it is `{n}`"))
                            .unwrap_or_default(),
                        _ => String::new(),
                    };
                    return err(
                        format!(
                            "`{}` on a `Fin` needs its length to reduce to `0` or a \
                             successor{here}. Recurse on the length first \
                             (`match n as \u{3bb} z => \u{2026}`), which is how the index \
                             becomes matchable",
                            form.keyword()
                        ),
                        span,
                    );
                }
            }
        }
        if let Type::Empty { level: empty_lvl } = &head {
            // An inductive with no constructors: absurdity elimination. All of
            // them share the kernel type `Empty` (§3.3), and none has an
            // inhabitant to confuse, so no tag is needed to dispatch.
            //
            // `Empty` is level-indexed, so the scrutinee's level comes off the
            // *type* and is independent of the motive's `mlvl`.
            if !arms.is_empty() {
                return err(
                    format!(
                        "this type has no constructors, so `{}` takes no arms",
                        form.keyword()
                    ),
                    span,
                );
            }
            return Ok(Term::ElimEmpty {
                level: mlvl,
                scrut_level: empty_lvl.clone(),
                motive: Rc::new(motive),
                scrut: Rc::new(scrut_t),
            });
        }
        if !matches!(head, Type::Nat) {
            return err(
                format!("`{}` needs a `Nat` or a declared inductive", form.keyword()),
                span,
            );
        }
        self.elab_match_nat(cx, form, arms, scrut_t, motive, mlvl, span)
    }

    /// `match` on `Nat`: the kernel's `elim_Nat`, with the arms named `Zero`
    /// and `Succ(k)` (or the low-level `Succ(k, ih)`).
    fn elab_match_nat(
        &self,
        cx: &Cx,
        form: MatchForm,
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
                other => return err(format!("`{other}` is not a constructor of `Nat`"), a.span),
            };
            if slot.replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
        }
        let (Some(zero), Some(succ)) = (zero, succ) else {
            return err(
                format!(
                    "`{}` on `Nat` needs both a `Zero` and a `Succ(k)` arm",
                    form.keyword()
                ),
                span,
            );
        };
        if !zero.binders.is_empty() {
            return err("`Zero` binds no fields", zero.span);
        }
        // `Succ(k)` is the unified form (ih = guarded self-call); `Succ(k, ih)`
        // stays as the low-level explicit fallback (issues/match-recursion.md).
        let (k, ih) = match succ.binders.as_slice() {
            [k] => (k.name().to_string(), None),
            [k, ih] => (k.name().to_string(), Some(ih.name().to_string())),
            _ => return err("`Succ` binds `(k)` or `(k, ih)`", succ.span),
        };
        let (zero, succ_body) = (&zero.body, &succ.body);
        // Inside recursion at the top, the body's own `match` on the
        // recursion's parameter meets that parameter's constructor term, and
        // takes its arm: `Succ(k)` binds `k` to the predecessor the guard
        // already holds, so a self-call at `k` is the ih
        // (docs/recursion-at-the-top-design.md §3). The term is the arm the
        // recursor would reduce to.
        if ih.is_none() && self.scope.recursion_at_top.is_some() {
            let at = motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())));
            match &scrut_t {
                Term::Zero => return self.elab_check(cx, zero, &at, &mlvl),
                Term::Succ(t) => {
                    let mut acx = cx.clone();
                    acx.aliases.push(Rc::new(crate::Alias {
                        name: k.clone(),
                        depth: acx.names.len(),
                        term: Rc::clone(t),
                        ty: Type::Nat,
                        level: Level::Zero,
                        skel: None,
                        spliced: None,
                        shifted: Default::default(),
                    }));
                    return self.elab_check(&acx, succ_body, &at, &mlvl);
                }
                _ => {}
            }
        }
        // Does this match descend on one of the declaration's own parameters?
        // If so, self-calls in the arm become the ih. If not (a nested match on
        // some other term), the enclosing arm's guard — if any — still stands,
        // possibly *extended* by this match (§ course-of-values below).
        let dec = if ih.is_none() {
            self.top_guard(span).or_else(|| crate::recursion::guard_param(cx, &scrut_t, arms))
        } else {
            None
        };
        // How many past values the arm reads. `1` is the ordinary recursion and
        // emits exactly the term it always did; more makes the recursor carry a
        // tuple (`cov_*` below, issues/recursion-at-deeper-subterms.md).
        let d = match dec {
            // At the top the chain starts at the parameter itself, which the
            // body's own `match` takes apart (`recursion_at_top_body`): seeded
            // there, every depth is one more than it is below the arm.
            Some(dec) if self.top_guard(span).is_some() => match cx.selfref.as_ref() {
                Some(s) => self.cov_depth(cx, succ_body, &s.params[dec].0, dec, None).saturating_sub(1).max(1),
                None => 1,
            },
            Some(dec) => self.cov_depth(cx, succ_body, &k, dec, None),
            None => 1,
        };
        // A nested `match` on the chain's end, with values below it still
        // uncollected: it must **convoy** them, or its arms cannot see that the
        // value one below `k` is the value at `l`
        // (docs/course-of-values-recursion-design.md §5).
        let convoy = if ih.is_none() && dec.is_none() {
            self.chain_convoy(cx, &scrut_t)
        } else {
            None
        };
        // The motive of the recursor actually emitted. Three shapes, and the
        // first is what every ordinary `match` on `Nat` has always emitted:
        //   d = 1, no convoy : M
        //   d > 1            : Σ(M[z], M[pred z], …)   — the carried window
        //   convoy           : T_outer(z) -> M[z]      — the window passed in
        let comps_z = cov_comps(
            &cx.gamma,
            &ChainStep::Pred,
            &motive,
            d,
            1,
            &Term::Var(LocalVar(0)),
        );
        let (rec_motive, rec_lvl) = match &convoy {
            None => (cov_ty(&comps_z, &mlvl), mlvl.clone()),
            Some(c) => {
                let carried = cov_ty(
                    &cov_comps(
                        &cx.gamma,
                        &ChainStep::Pred,
                        &c.motive,
                        c.d,
                        1,
                        &c.anchor(Term::Var(LocalVar(0))),
                    ),
                    &c.lvl,
                );
                (
                    Type::Pi {
                        dom_level: c.lvl.clone(),
                        cod_level: mlvl.clone(),
                        dom: Rc::new(carried),
                        cod: Rc::new(motive.shift_local(1)),
                    },
                    Level::max(c.lvl.clone(), mlvl.clone()),
                )
            }
        };
        // base : M[Zero/z] — under the convoy binder where there is one, and
        // tupled where `d > 1`, since every component of F(0) is at the same
        // `Zero` (`pred 0` is `0`).
        let base_ty = motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero)));
        let base = match &convoy {
            None => self.elab_check(cx, zero, &base_ty, &mlvl)?,
            Some(c) => {
                let comps = cov_comps(&cx.gamma, &ChainStep::Pred, &c.motive, c.d, 0, &c.anchor(Term::Zero));
                let dom = cov_ty(&comps, &c.lvl);
                let mut bcx = cx.clone();
                bcx.push("#cov".into(), dom.clone(), c.lvl.clone());
                bcx.guard = Some(c.guard_at(&comps, bcx.names.len(), None));
                let body = self.elab_check(&bcx, zero, &base_ty.shift_local(1), &mlvl)?;
                Term::Lam {
                    dom_level: c.lvl.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(dom),
                    body: Rc::new(body),
                }
            }
        };
        // step context: Γ, k : Nat, ih : rec_motive[k/z].
        let mut scx = cx.clone();
        scx.push(k.clone(), Type::Nat, Level::Zero);
        let ih_ty =
            rec_motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(Term::Var(LocalVar(0)))));
        // The unified arm `Succ(k)` binds the ih anyway — the recursor demands
        // it — but under a name the surface cannot spell, because it is
        // reached by a guarded self-call instead.
        scx.push(
            ih.clone().unwrap_or_else(|| "#ih".into()),
            ih_ty,
            rec_lvl.clone(),
        );
        // The window this arm carries, scoped in Γ, k, ih: the ih itself at
        // `d = 1`, its projections above that.
        let comps_ih: Vec<Type> = comps_z
            .iter()
            .map(|c| c.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(Term::Var(LocalVar(1))))))
            .collect();
        let ih_at = |i: usize| {
            (
                cov_proj(&comps_ih, &mlvl, Term::Var(LocalVar(0)), i),
                comps_ih[i].clone(),
                mlvl.clone(),
            )
        };
        // step : M[Succ k/z] in Γ, k, ih (+ the convoy binder) — the arm the
        // writer wrote, whatever the recursor is carrying underneath it.
        let step_ty = motive.apply_local(
            &embed(&cx.gamma, 2).extended(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))),
        );
        let step = match &convoy {
            Some(c) => {
                // The convoyed window at `Succ k`, where `pred (Succ k) ⇝ k`
                // makes the component one below this arm's scrutinee *reduce*
                // to the motive at the variable the arm binds. That reduction
                // is the whole point of passing it in.
                let comps = cov_comps(
                    &cx.gamma,
                    &ChainStep::Pred,
                    &c.motive,
                    c.d,
                    2,
                    &c.anchor(Term::Succ(Rc::new(Term::Var(LocalVar(1))))),
                );
                let dom = cov_ty(&comps, &c.lvl);
                let mut bcx = scx.clone();
                bcx.push("#cov".into(), dom.clone(), c.lvl.clone());
                bcx.guard = Some(c.guard_at(&comps, bcx.names.len(), Some(cx.names.len())));
                let body = self.elab_check(&bcx, succ_body, &step_ty.shift_local(1), &mlvl)?;
                Term::Lam {
                    dom_level: c.lvl.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(dom),
                    body: Rc::new(body),
                }
            }
            None => {
                if ih.is_none() {
                    scx.guard = dec
                        .map(|dec| {
                            Rc::new(Guard {
                                dec,
                                kind: GuardKind::Nat {
                                    preds: vec![cx.names.len()],
                                    depth: scx.names.len(),
                                    tuple: Term::Var(LocalVar(0)),
                                    comps: comps_ih.clone(),
                                    mlvl: mlvl.clone(),
                                    motive: Rc::new(motive.clone()),
                                    gamma: cx.gamma.clone(),
                                },
                                rebind: None,
                                generalized: crate::generalize::guard_gen(cx, dec, Some(span)),
                            })
                        })
                        .or_else(|| cx.guard.clone());
                }
                let step = self.elab_check(&scx, succ_body, &step_ty, &mlvl)?;
                if d == 1 {
                    step
                } else {
                    // F(Succ k) = (step, π₀ ih, …, π_{d-2} ih): the value just
                    // computed, then the window slid by one. Annotated at
                    // `Succ k`, where the kernel checks it; the shifted
                    // components differ from those annotations only by
                    // `pred (Succ k) ⇝ k`, which conversion does.
                    let comps_succ = cov_comps(
                        &cx.gamma,
                        &ChainStep::Pred,
                        &motive,
                        d,
                        2,
                        &Term::Succ(Rc::new(Term::Var(LocalVar(1)))),
                    );
                    let mut vals = vec![step];
                    vals.extend((0..d - 1).map(|i| ih_at(i).0));
                    cov_tuple(&comps_succ, &mlvl, vals)
                }
            }
        };
        // F(0) = (f(0), …, f(0)): the deeper components stand for values before
        // the start, which no arm can read — a call at depth `i` is only in
        // scope inside `i` nested `Succ` arms, so reaching one would need the
        // scrutinee to be at least `i`. The `Zero` arm's own value is the one
        // term of the right type already to hand.
        let base = if d == 1 {
            base
        } else {
            let comps_0 = cov_comps(&cx.gamma, &ChainStep::Pred, &motive, d, 0, &Term::Zero);
            cov_tuple(&comps_0, &mlvl, vec![base; d])
        };
        let elim = Term::ElimNat {
            level: rec_lvl,
            motive: Rc::new(rec_motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::new(scrut_t.clone()),
        };
        if let Some(c) = &convoy {
            // …and the window goes in, which is what refines it.
            let comps = cov_comps(&cx.gamma, &ChainStep::Pred, &c.motive, c.d, 0, &c.anchor(scrut_t.clone()));
            return Ok(crate::spelling::checked_app(
                Rc::new(elim),
                c.lvl.clone(),
                mlvl.clone(),
                Rc::new(cov_ty(&comps, &c.lvl)),
                Rc::new(
                    motive.apply_local(
                        &embed(&cx.gamma, 1).extended(Rc::new(scrut_t.shift_local(1))),
                    ),
                ),
                Rc::new(c.tuple.clone()),
            ));
        }
        if d == 1 {
            return Ok(elim);
        }
        // The source's `match` is the *first* component of what the recursor
        // now computes, so the transformation stays local to this expression:
        // its type is still `M[scrut/z]`.
        let comps_at = cov_comps(&cx.gamma, &ChainStep::Pred, &motive, d, 0, &scrut_t);
        Ok(cov_proj(&comps_at, &mlvl, elim, 0))
    }

    /// A nested `match` on the enclosing arm's predecessor continues the chain:
    /// inside `match n { Succ(k) => match k { Succ(l) => … } }` the variable
    /// `l` is the value two below `n`, and a self-call at it is guarded — but
    /// only if the values the enclosing recursion carries are *passed through*
    /// this match, since only then does the component one below `k` reduce, at
    /// the arm that knows `k` is `Succ l`, to the value at `l`.
    ///
    /// `None` when the enclosing recursion has nothing left to hand down —
    /// every ordinary one-step recursion, which therefore emits exactly the
    /// term it always did.
    fn chain_convoy(&self, cx: &Cx, scrut: &Term) -> Option<Convoy> {
        let g = cx.guard.clone()?;
        let GuardKind::Nat {
            preds,
            depth,
            tuple,
            comps,
            mlvl,
            motive,
            gamma,
        } = &g.kind
        else {
            return None;
        };
        // Nothing below the chain's end is carried: this is the ordinary
        // recursion, and a nested `match` changes nothing about it.
        if comps.len() <= preds.len() {
            return None;
        }
        // By *binder*, never by name: an inner `k` that shadows the arm's own
        // is a different variable and does not continue the chain.
        let Term::Var(LocalVar(i)) = scrut else {
            return None;
        };
        if cx.names.len() - 1 - *i as usize != *preds.last()? {
            return None;
        }
        let by = (cx.names.len() - depth) as u32;
        // The motive is scoped over the recursion's own context (`gamma`, the
        // `match`'s, plus z), so it is reindexed past every binder since that
        // `match`, the arm's `k` and ih included; `by` counts only those since
        // the guard, and a motive mentioning a variable of `gamma` read the
        // wrong binder with it (issues/cov-convoy-motive-second-ambient.md).
        let from_match = (cx.gamma.entries.len() - gamma.entries.len()) as u32;
        Some(Convoy {
            dec: g.dec,
            preds: preds.clone(),
            d: comps.len(),
            lvl: mlvl.clone(),
            motive: motive
                .apply_local(&embed(gamma, from_match + 1).extended(Rc::new(Term::Var(LocalVar(0))))),
            outer_motive: Rc::clone(motive),
            gamma: gamma.clone(),
            tuple: tuple.shift_local(by),
            lift: preds.len() - 1,
            generalized: g.generalized.clone(),
        })
    }

    /// How deep into the predecessor chain the arm's self-calls reach: `1` for
    /// `f(k)`, `2` for an `f(l)` under a nested `match k`, and so on
    /// (issues/recursion-at-deeper-subterms.md).
    ///
    /// **Syntactic, and deliberately only a sizing decision.** It reads names,
    /// so a shadowed binder can make it wrong in either direction — and
    /// neither direction can produce a wrong term. Too small, and the real
    /// check refuses the call for want of an ih (the same message as before
    /// this existed); too large, and the recursor carries a component nothing
    /// reads. What a call *lowers to* is decided by [`Self::elab_self_call`]
    /// comparing binder positions, which no spelling can fool.
    ///
    /// `link` selects how the scan walks one step down: `None` is `Nat`'s
    /// `Succ(k)` arm, `Some(ind)` a chain-shaped declaration's recursive
    /// constructor and the binder at its recursive field
    /// (`docs/list-course-of-values-design.md` §5).
    pub(crate) fn cov_depth(
        &self,
        cx: &Cx,
        body: &Expr,
        k: &str,
        dec: usize,
        link: Option<&crate::inductive::Inductive>,
    ) -> usize {
        let Some(s) = cx.selfref.as_ref() else {
            return 1;
        };
        // The binder a `match` arm on `cur` gives to the next link, if it has
        // one: `Succ`'s predecessor, or the recursive field's binder.
        let next_link = |arms: &[Arm]| -> Option<String> {
            match link {
                None => arms
                    .iter()
                    .find(|a| a.ctor == "Succ")
                    .and_then(|a| match a.binders.as_slice() {
                        [p] => Some(p.name().to_string()),
                        _ => None,
                    }),
                Some(ind) => arms.iter().find_map(|a| {
                    let i = ind.ctors.iter().position(|c| c.name == a.ctor)?;
                    let field = ind.ctors[i]
                        .kind
                        .iter()
                        .position(|k| *k == crate::inductive::FieldKind::Plain)?;
                    Some(a.binders.get(field)?.name().to_string())
                }),
            }
        };
        // name of a chain predecessor -> its depth, `k` being depth 1.
        let mut chain: Vec<(String, usize)> = vec![(k.to_string(), 1)];
        let mut found = 1usize;
        // Descend the chain first, then look for calls: the map has to be
        // complete before a call at `l` can be recognised as one.
        loop {
            let (cur, at) = chain.last().cloned().expect("seeded above");
            let mut next: Option<String> = None;
            walk_expr(body, &mut |e| {
                if let ExprKind::Match { scrut, arms, .. } = &e.kind
                    && matches!(&scrut.kind, ExprKind::Var(n) if *n == cur)
                    && let Some(p) = next_link(arms)
                {
                    next.get_or_insert(p);
                }
            });
            match next {
                Some(n) if !chain.iter().any(|(m, _)| *m == n) => chain.push((n, at + 1)),
                _ => break,
            }
        }
        walk_expr(body, &mut |e| {
            let Some((args, explicit)) = crate::recursion::surface_self_call(s, e) else {
                return;
            };
            let positions: Vec<usize> = (s.n_tyvars..s.params.len())
                .filter(|&j| explicit || !s.params[j].1)
                .collect();
            let Some(slot) = positions.iter().position(|&j| j == dec) else {
                return;
            };
            let Some(arg) = args.get(slot) else { return };
            if let ExprKind::Var(n) = &arg.kind
                && let Some((_, at)) = chain.iter().find(|(m, _)| m == n)
            {
                found = found.max(*at);
            }
        });
        found
    }

    /// `match` on `Fin(Succ k)`: the kernel's `Case` over the sum that
    /// `Fin(Succ k)` unfolds to, with the arms named `FZ` and `FS(j)`
    /// (docs/surface-fin-indexing-design.md §4.2).
    ///
    /// `Fin` has no eliminator of its own — it is a former whose whnf is
    /// `Unit⁰ + Fin(k)` — so the summands are written **unfolded** here while
    /// the scrutinee's own type stays the folded `Fin(Succ k)`, and conversion
    /// bridges the two. That is the same asymmetry `term::nth` lives with.
    #[allow(clippy::too_many_arguments)]
    fn elab_match_fin(
        &self,
        cx: &Cx,
        form: MatchForm,
        arms: &[Arm],
        scrut_t: Term,
        k: &Rc<Term>,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let mut fz: Option<&Arm> = None;
        let mut fs: Option<&Arm> = None;
        for a in arms {
            let slot = match a.ctor.as_str() {
                "FZ" => &mut fz,
                "FS" => &mut fs,
                other => return err(format!("`{other}` is not an index of a `Fin`"), a.span),
            };
            if slot.replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
        }
        let (Some(fz), Some(fs)) = (fz, fs) else {
            return err(
                format!(
                    "`{}` on a `Fin` needs both an `FZ` and an `FS(i)` arm",
                    form.keyword()
                ),
                span,
            );
        };
        if !fz.binders.is_empty() {
            return err("`FZ` binds no fields", fz.span);
        }
        let [j] = fs.binders.as_slice() else {
            return err(
                "`FS` binds exactly one field, the predecessor index",
                fs.span,
            );
        };
        let j = j.name().to_string();
        let (lhs, rhs) = (
            Type::Unit { level: Level::Zero },
            Type::Fin { len: Rc::clone(k) },
        );
        // The two arm types, as the kernel's `Case` rule states them:
        // `M[inl x/z]` in `Γ, x : Unit⁰` and `M[inr y/z]` in `Γ, y : Fin(k)`.
        let injected = |left: bool| {
            let (lhs, rhs) = (Rc::new(lhs.shift_local(1)), Rc::new(rhs.shift_local(1)));
            let val = Rc::new(Term::Var(LocalVar(0)));
            let (lhs_level, rhs_level) = (Level::Zero, Level::Zero);
            if left {
                Term::Inl {
                    lhs_level,
                    rhs_level,
                    lhs,
                    rhs,
                    val,
                }
            } else {
                Term::Inr {
                    lhs_level,
                    rhs_level,
                    lhs,
                    rhs,
                    val,
                }
            }
        };
        // The `FZ` arm binds nothing at the surface but the kernel's `case_l`
        // binds one local, so a `#`-prefixed dummy stands in — the convention
        // `build_absurd` already uses for `#y`/`#p`. Unspellable, and filtered
        // out of the goal listing.
        let mut lcx = cx.clone();
        lcx.push("#fz".to_string(), lhs.clone(), Level::Zero);
        let left_ty = motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(injected(true))));
        let case_l = self.elab_check(&lcx, &fz.body, &left_ty, &mlvl)?;
        let mut rcx = cx.clone();
        rcx.push(j.clone(), rhs.clone(), Level::Zero);
        let right_ty = motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(injected(false))));
        let case_r = self.elab_check(&rcx, &fs.body, &right_ty, &mlvl)?;
        Ok(Term::Case {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            motive_level: mlvl,
            lhs: Rc::new(lhs),
            rhs: Rc::new(rhs),
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut: Rc::new(scrut_t),
        })
    }
}

/// One step down the recursion's chain, which is what the window's components
/// are indexed by: component `i` at `z` is the motive at `step^i z`.
///
/// The two spellings share the two computation facts the whole scheme rests on
/// (`docs/course-of-values-recursion-design.md` §3,
/// `docs/list-course-of-values-design.md` §2): at a *recursive* constructor
/// the step is that constructor's own child, so the step's annotation reduces
/// to the arm's binder; at a *base* constructor it is the scrutinee itself, so
/// every component of the base tuple sits at one and the same type.
pub(crate) enum ChainStep {
    /// `Nat`: `pred`.
    Pred,
    /// A chain-shaped `Wf`: `tail_D`, as a term over `(gamma, z : ⟦D⟧)` —
    /// `wf::tail_term` builds it, and it is carried rather than rebuilt
    /// because building one runs the whole `elim_Wf` lowering.
    Tail(Rc<Term>),
}

impl ChainStep {
    /// One step down from `t`, which is scoped `extra` binders past `gamma`.
    pub(crate) fn at(&self, gamma: &LocalCtx, extra: u32, t: Term) -> Term {
        match self {
            ChainStep::Pred => pred_tm(t),
            ChainStep::Tail(body) => {
                body.apply_local(&embed(gamma, extra).extended(Rc::new(t)))
            }
        }
    }
}

/// `pred(t)`, as the kernel spells it: `elim_Nat(λ _. Nat; 0; λ k ih. k; t)`.
/// Needed because a course-of-values tuple's `i`-th component is the motive at
/// `pred^i z` — and `pred (Succ k) ⇝ k` and `pred 0 ⇝ 0` by computation, which
/// is what makes the step's and the base's annotations line up
/// (issues/recursion-at-deeper-subterms.md).
fn pred_tm(t: Term) -> Term {
    Term::ElimNat {
        level: Level::Zero,
        motive: Rc::new(Type::Nat),
        base: Rc::new(Term::Zero),
        // Scoped in (Γ, k : Nat, ih : Nat): the predecessor, ignoring the ih.
        step: Rc::new(Term::Var(LocalVar(1))),
        scrut: Rc::new(t),
    }
}

/// The component types of the course-of-values tuple at `at`: `M[step^i at/z]`
/// for `i < d`, scoped in `gamma` extended by `extra` binders (where `at`
/// lives). `d = 1` gives back the plain motive, which is why every caller can
/// use these unconditionally.
pub(crate) fn cov_comps(
    gamma: &LocalCtx,
    step: &ChainStep,
    motive: &Type,
    d: usize,
    extra: u32,
    at: &Term,
) -> Vec<Type> {
    (0..d)
        .map(|i| {
            let mut t = at.clone();
            for _ in 0..i {
                t = step.at(gamma, extra, t);
            }
            motive.apply_local(&embed(gamma, extra).extended(Rc::new(t)))
        })
        .collect()
}

/// `Σ(comps[0], Σ(comps[1], …))`, right-nested and non-dependent — the tuple
/// the recursor carries. One component is the motive itself, so the ordinary
/// recursion emits no `Σ` at all.
pub(crate) fn cov_ty(comps: &[Type], lvl: &Level) -> Type {
    let (last, rest) = comps
        .split_last()
        .expect("a tuple has at least one component");
    rest.iter()
        .rev()
        .fold(last.clone(), |snd, fst| Type::Sigma {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst: Rc::new(fst.clone()),
            snd: Rc::new(snd.shift_local(1)),
        })
}

/// The tuple of `vals` at [`cov_ty`]'s type.
pub(crate) fn cov_tuple(comps: &[Type], lvl: &Level, vals: Vec<Term>) -> Term {
    debug_assert_eq!(comps.len(), vals.len());
    let mut vals = vals;
    let mut acc = vals.pop().expect("a tuple has at least one component");
    for (i, fst) in vals.into_iter().enumerate().rev() {
        acc = Term::Pair {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst_ty: Rc::new(comps[i].clone()),
            snd_ty: Rc::new(cov_ty(&comps[i + 1..], lvl).shift_local(1)),
            fst: Rc::new(fst),
            snd: Rc::new(acc),
        };
    }
    acc
}

/// `π_i p` — `snd` down to the `i`-th component and `fst` off it, except at the
/// last, which the nesting leaves bare.
pub(crate) fn cov_proj(comps: &[Type], lvl: &Level, p: Term, i: usize) -> Term {
    let ann = |at: usize| {
        (
            Rc::new(comps[at].clone()),
            Rc::new(cov_ty(&comps[at + 1..], lvl).shift_local(1)),
        )
    };
    let mut cur = p;
    for at in 0..i {
        let (fst_ty, snd_ty) = ann(at);
        cur = Term::Snd {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst_ty,
            snd_ty,
            pair: Rc::new(cur),
        };
    }
    if i + 1 < comps.len() {
        let (fst_ty, snd_ty) = ann(i);
        cur = Term::Fst {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst_ty,
            snd_ty,
            pair: Rc::new(cur),
        };
    }
    cur
}
