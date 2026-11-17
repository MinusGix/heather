//! Application's part of the elaborator: heads, spines and solving arguments from an expected type.

use std::cell::RefCell;

use heather_kernel::typing;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{GlobalBinding, GlobalVar, LocalSubst, SubstTail, Term, Type};

use heather_syntax::{Expr, ExprKind, NamedArg, Span, Ty, TyKind};

use crate::{
    EL_AGAINST_CODE, Elaborator, IMPLICIT_MARK_REFUSED, R, application, code, defaults, err, lgg,
    self_name_refusal, spelling, surface, unification, with_self_shadow_note,
};
use crate::application::{Callables, Skel, has_implicit_mark, skel_params};
use crate::constructor::Constructors;
use crate::context::Cx;
use crate::diagnostics::ElabError;
use crate::dispatch::Operators;
use crate::gendefs::GeneratedDefs;
use crate::name_lookup::NameLookup;
use crate::names::GlobalInfo;
use crate::oracle::Unfold;
use crate::solution_check::SolutionCheck;
use crate::unification::{Guesses, Sol, strengthen_tm, unify_ty_root, zonked, zonked_tm};

/// Application's part of the elaborator: heads, spines and solving arguments from an expected type.
pub(crate) struct AppUnify<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for AppUnify<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl AppUnify<'_> {
    /// Explain a failed `let` annotation that turned out to name a **term**.
    ///
    /// `let p: a = b = pf;` used to parse as annotation `a = b`, binder `=`.
    /// The annotation position now suppresses the comparison rung
    /// (docs/language/let-and-blocks-design.md §3), so it parses as annotation `a`,
    /// binder `=`, value `b = pf` — and `a` is a term, whose only report from
    /// `elab_ty` is `unknown type \`a\``. That is diagnosable but says nothing
    /// about what actually happened, so this appends the spelling that works.
    /// Pass-through for every other failure.
    pub(crate) fn let_ty_hint(&self, cx: &Cx, t: &Ty, e: ElabError) -> ElabError {
        let TyKind::Named { name, args } = &t.kind else {
            return e;
        };
        if !args.is_empty() || !self.shadowed(cx, name) {
            return e;
        }
        let ElabError::Elab { msg, span } = e else {
            return e;
        };
        ElabError::Elab {
            msg: format!(
                "{msg} — `{name}` is a term, not a type. If this annotation was meant \
                 to be an equation, parenthesise it: `let p: ({name} = b) = pf;`, since \
                 an annotation does not extend across the `let`'s `=`"
            ),
            span,
        }
    }

    /// A projected record field applied to arguments: `w.f(3)`. Routes to
    /// implicit insertion when the field's stored surface type carried marks
    /// (docs/language/implicit-binders-design.md §5.1), and to the explicit path —
    /// with the skeleton-synthesized hint table when there is one —
    /// otherwise. The field name is the display name; `@w.f(…)` stays out of
    /// the grammar this round (§7.1), so there is no explicit flag here.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn apply_projection(
        &self,
        cx: &Cx,
        name: &str,
        t: Term,
        ty: Type,
        lvl: Level,
        fskel: Option<Rc<Skel>>,
        args: &[Expr],
        named: &[NamedArg],
        expected: Option<&Type>,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        match fskel {
            Some(skel) if skel.params.iter().any(|b| b.implicit) => {
                let mask: Vec<bool> = skel.params.iter().map(|b| b.implicit).collect();
                let params = skel_params(&skel);
                let r =
                    application::resolve_named(name, true, &params, 0, &mask, args, named, span)?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (args, &mask[..]),
                };
                application::apply_implicit(
                    self.0, cx, name, params, true, 0, false, t, ty, lvl, args, mask, expected,
                    false, span,
                )
            }
            Some(skel) => {
                let params = skel_params(&skel);
                let flat = vec![false; params.len()];
                let r =
                    application::resolve_named(name, true, &params, 0, &flat, args, named, span)?;
                let args = r.as_ref().map_or(args, |(a, _)| &a[..]);
                application::apply_explicit(self.0, cx, Some(name), params, 0, t, ty, lvl, args)
            }
            None => {
                application::refuse_named(
                    &format!("`{name}`"),
                    "its type binds no parameter names, so its arguments are positional                      (docs/language/named-arguments-design.md §7)",
                    named,
                )?;
                application::apply_explicit(
                    self.0,
                    cx,
                    None,
                    Rc::new(Vec::new()),
                    0,
                    t,
                    ty,
                    lvl,
                    args,
                )
            }
        }
    }

    /// `f<T, …>` — fill a declaration's leading type parameters with the
    /// codes of the written types (docs/language/surface-polymorphism.md §1).
    ///
    /// Returns the callee's name (for diagnostics downstream), the applied
    /// head with its type and level, and the implicit mask of the parameters
    /// that are *left* — so a call can still infer whatever `{}`-implicits
    /// follow the type arguments.
    pub(crate) fn elab_ty_app(
        &self,
        cx: &Cx,
        callee: &Expr,
        tyargs: &[Ty],
        span: Span,
    ) -> R<(String, Term, Type, Level, Vec<bool>)> {
        let ExprKind::Var(name) = &callee.kind else {
            return err(
                "type arguments need a named callee: write `f<T, …>(…)`, where `f` is a \
                 `fn` or `theorem` with type parameters",
                span,
            );
        };
        // The enclosing declaration's own name, with no call after it. A
        // *saturated* self-call at written type arguments is handled before
        // this function is reached; a bare `f<A>` is the self-name used as a
        // value, which it never is (it is the induction hypothesis). Said here
        // because `params_of` finds no global for a self-name and the arity
        // complaint below would otherwise deny a declaration the reader is
        // looking at (issues/recursive-self-call-type-arguments.md).
        if let Some(selfref) = cx.selfref.as_ref().filter(|s| s.matches(name)) {
            let note = NameLookup(self).self_shadow_note(selfref, name);
            return err(self_name_refusal(selfref, name), span).map_err(|e| with_self_shadow_note(e, note.as_deref()));
        }
        let params = Callables(self).params_of(name);
        let n_ty = params.iter().take_while(|p| p.is_type).count();
        if n_ty == 0 {
            return err(
                format!(
                    "`{name}` takes no type arguments (only a `fn` or `theorem` declared \
                     `{name}<A, …>` does)"
                ),
                span,
            );
        }
        if tyargs.len() != n_ty {
            return err(
                format!(
                    "`{name}` takes {n_ty} type argument(s), found {}",
                    tyargs.len()
                ),
                span,
            );
        }
        let (mut t, mut ty, mut lvl) = self.resolve(cx, name, span)?;
        for a in tyargs {
            // A written type argument becomes a code — a kernel value with
            // no skeleton slot — so a mark in one is refused (§3.4).
            if has_implicit_mark(a) {
                return err(IMPLICIT_MARK_REFUSED, a.span);
            }
            let (a_ty, _) = self.elab_ty(cx, a)?;
            // Quoted from the type the emission sites would write
            // (`docs/inductives/per-instantiation-type-codes-design.md` §5): a written
            // `f<List<Nat>>` carries `El (List#tycode_fn^δ ⌜Nat⌝)` rather than
            // the boxed literal every emission walk still finds here.
            let emitted = self.emit_ty(cx, &a_ty, 0);
            let Some(c) = code::code_of(emitted.as_ref().unwrap_or(&a_ty)) else {
                return err("this type cannot be a type argument", a.span);
            };
            let head = self.whnf(cx, &ty, span)?;
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = head
            else {
                return err(
                    format!("internal: `{name}`'s type parameter is not a `Π`"),
                    span,
                );
            };
            let arg = Rc::new(c);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
            lvl = cod_level.clone();
            t = crate::spelling::checked_app(Rc::new(t), dom_level, cod_level, dom, cod, arg);
        }
        let mask = params.iter().skip(n_ty).map(|p| p.implicit).collect();
        Ok((name.clone(), t, ty, lvl, mask))
    }

    /// Is `e` a form the elaborator can only *check*, never infer — the
    /// deferral trigger's syntactic half (docs/elaborator/unifier-completeness-design.md
    /// §4.1)? The set is closed and enumerated by the refusing arms of
    /// [`Inference::elab_infer_at`](crate::inference::Inference::elab_infer_at)/[`Elaborator::elab_infer`]; deferring exactly these
    /// forms loses no solving power, because in inference mode they *error*
    /// rather than contribute a solution. Each variant, tied to its arm:
    ///
    /// - `Hole` — "a hole here has no expected type" (`elab_infer_at`).
    /// - `Refl`, when not shadowed — "`refl` needs an `=` expected type"
    ///   (the shadowed reading is a `Var` and infers).
    /// - `AutoRefl` — checking-only by construction (a speculative `refl`
    ///   against the expected `Id`).
    /// - `CollectionLit` — "a collection literal needs an expected container type".
    /// - a `Lam` with any unannotated binder — nothing to take the domain
    ///   from (`elab_lam_infer` requires every annotation; `elab_lam_check`
    ///   reads the domain off the expected `Π`).
    /// - `FZ` / `FS(j)`, under their existing not-shadowed/not-a-ctor
    ///   guards — "needs an expected `Fin` type".
    /// - `absurd(p)`, when not shadowed — "needs an expected type".
    /// - a bare reference to a global with a leading implicit prefix
    ///   ([`Callables::bare_implicit_prefix`]). This one *can* infer — but only at
    ///   its uninstantiated polymorphic Π, which against a meta-bearing
    ///   domain can just mis-teach (`El ?B ≟ Ty 0` "solves" `?B := ⌜Type 0⌝`
    ///   and the kernel rejects a term nobody meant). Checking position is
    ///   where its instantiation is decidable (the §5.3 route). At a
    ///   meta-bearing domain it waits, then the obligation retry may infer
    ///   its instance from the domain's already solved parts.
    /// - a **bare operator symbol** that no binder named and that some
    ///   designation covers ([`Operators::symbol_needs_a_carrier`]). The same
    ///   sentence as the entry above, at the notation layer: `+` infers to
    ///   `add`, whose type would pin a `Bool` call's carrier to `Nat`, so at a
    ///   meta-bearing domain it waits for the carrier a later argument
    ///   produces (docs/language/classes/bare-symbol-checking-carrier-design.md §3.2).
    ///
    /// `Num` is deliberately **excluded**: it infers at `Nat` today and that
    /// default is load-bearing for the suite (`xs[2]`'s `Fin` reading exists
    /// only in checking position, as before).
    pub(crate) fn is_checking_only(&self, cx: &Cx, e: &Expr) -> bool {
        if defaults::is_param_default(e) {
            return true;
        }
        match &e.kind {
            ExprKind::Hole(_) | ExprKind::AutoRefl | ExprKind::CollectionLit(_) => true,
            // A bare operator symbol that needs a carrier
            // (docs/language/classes/bare-symbol-checking-carrier-design.md §3.2, §4.3). Same
            // sentence as the bare implicit prefix two arms down: it *can*
            // infer — `+` infers to `add` — but only at a shape that
            // mis-teaches, since `add`'s type would pin the call's carrier to
            // `Nat` at a call whose carrier is `Bool`. Checking position is
            // where its resolution is decidable, so at a meta-bearing domain it
            // waits for one, and the per-argument deferral is what hands it the
            // carrier a later argument produced.
            ExprKind::OpSymbol {
                symbol: sym,
                fixity,
            } => Operators(self).symbol_needs_a_carrier(cx, sym, *fixity),
            ExprKind::Refl => !self.shadowed(cx, "refl"),
            ExprKind::Lam { binders, .. } => binders.iter().any(|b| b.ty.is_none()),
            ExprKind::Var(name) => {
                (name == "rel_derive" && !self.shadowed(cx, name) && Constructors(self).ctor_here(cx, name).is_none())
                    || (name == "FZ"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here(cx, name).is_none())
                    || Callables(self).bare_implicit_prefix(cx, name).is_some()
                    // The value analog (docs/language/implicit-binders-design.md
                    // §4.3): a bare local/alias whose skeleton has a leading
                    // implicit prefix is checking-only for the same reason
                    // the bare-global member is — it *can* infer, but only
                    // at its uninstantiated Π, which against a meta-bearing
                    // domain mis-teaches.
                    || Callables(self)
                        .value_skel(cx, name)
                        .is_some_and(|s| s.leading_implicit() > 0)
            }
            // A cast takes its target from the checking position, as a
            // numeral does (docs/language/casting-design.md §5.2).
            ExprKind::App { .. } if surface::is_cast(e) => true,
            ExprKind::App { .. } => match e.as_named() {
                Some(("absurd", _, _)) => !self.shadowed(cx, "absurd"),
                Some((name @ ("rel_cong" | "rel_derive"), _, false)) => !self.shadowed(cx, name) && Constructors(self).ctor_here(cx, name).is_none(),
                Some(("FS", _, false)) => {
                    !self.shadowed(cx, "FS") && Constructors(self).ctor_here(cx, "FS").is_none()
                }
                // A call with a **result-only implicit**
                // ([`Self::call_defers_for_result_only`]): the semantic member
                // of this set, and the only one that can still elaborate if
                // deferral does not pay off — which is why it, alone, carries
                // the inference fallback in [`application::apply_implicit`].
                Some((n, args, false)) => Callables(self).call_defers_for_result_only(cx, n, args.len(), e.named_args()),
                _ => false,
            },
            _ => false,
        }
    }

    /// Was this argument deferred by the **result-only implicit** rule — the
    /// one member of [`Self::is_checking_only`] that can still be elaborated
    /// in inference mode? See [`DeferredArg::fallback_infer`].
    pub(crate) fn deferral_can_fall_back(&self, cx: &Cx, e: &Expr) -> bool {
        if defaults::is_param_default(e) {
            return false;
        }
        match e.as_named() {
            Some(("absurd", _, _)) | Some(("FS", _, false)) => false,
            Some((n, args, false)) => Callables(self).call_defers_for_result_only(cx, n, args.len(), e.named_args()),
            _ => false,
        }
    }

    /// [`unification::U::type_args`]: which arguments of the rigid spine `t`
    /// — in the committed world, `d` binders past `cx.gamma` — sit at a `Ty`
    /// domain, read off the **head's** type. An `app(…)` node states its
    /// domain; an `app@` node's is its head's (`docs/elaborator/app-by-head-type-design.md`
    /// §6.2), so the unifier's type-argument prefix asks here. The domain is
    /// read as the `app` emitter would have written it: the Π of the running
    /// type's weak head, instantiated at the earlier arguments. `None` under
    /// binders (their types are not in `cx.gamma`) and for a head whose type
    /// does not expose a Π per argument — the refusal the rule already gives
    /// a head it cannot read.
    pub(crate) fn spine_type_args(&self, cx: &Cx, t: &Term, d: u32, span: Span) -> Option<Vec<bool>> {
        if d != 0 {
            return None;
        }
        let doms = self.app_domains(cx, t, span)?;
        Some(doms.iter().map(|(dom, _)| matches!(&**dom, Type::Ty(_))).collect())
    }

    /// The domain, and its level, of every argument of the application spine
    /// `t` in `cx`, outermost last — what an `app(…)` node would state, read
    /// off the head's type instead (`docs/elaborator/app-by-head-type-design.md` §6.2's
    /// `app_domains`): the head is inferred, and each argument peels one Π
    /// off the weak head of the running type, which is then instantiated at
    /// it — the walk `application.rs` makes when it writes the node. `None`
    /// when the head does not infer in `cx` or its type runs out of Π's.
    pub(crate) fn app_domains(
        &self,
        cx: &Cx,
        t: &Term,
        span: Span,
    ) -> Option<Vec<(Rc<Type>, Level)>> {
        self.app_walk(cx, t, span).map(|(domains, _)| domains)
    }

    /// The type of the application spine `t` in `cx`, read the way
    /// [`Self::app_domains`] reads its domains: the head inferred, then one Π
    /// instantiated per argument. For a caller that only needs to know what
    /// `t` is — the speller naming a field read off it — this costs the
    /// head's inference and the substitutions, never a check of the
    /// arguments.
    pub(crate) fn spine_type(&self, cx: &Cx, t: &Term, span: Span) -> Option<Type> {
        self.app_walk(cx, t, span).map(|(_, ty)| ty)
    }

    fn app_walk(&self, cx: &Cx, t: &Term, span: Span) -> Option<(Vec<(Rc<Type>, Level)>, Type)> {
        let (head, args) = spelling::app_spine(t);
        let oracle = self.semantic_oracle();
        let (mut ty, _) =
            typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, head, self.policy.fuel).ok()?;
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            // A syntactic Π is read as it stands, as the kernel's fast path
            // reads it; only a type that has to reduce is whnf'd.
            let w = if matches!(ty, Type::Pi { .. }) { ty } else { self.whnf(cx, &ty, span).ok()? };
            let Type::Pi { dom, cod, dom_level, .. } = w else {
                return None;
            };
            out.push((dom, dom_level));
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(a)));
        }
        Some((out, ty))
    }

    /// [`unification::U::canonical_head`]: the weak head of a rigid term,
    /// when reduction exposes a canonical form. Under the stuck-spelling
    /// budget, since the answer is discarded whenever it is not one, and
    /// `None` under binders, whose types are not in `cx.gamma` — the same
    /// scope [`Self::spine_type_args`] reads.
    pub(crate) fn canonical_head(&self, cx: &Cx, t: &Term, d: u32) -> Option<Term> {
        if d != 0 {
            return None;
        }
        let w = self.semantic_oracle().whnf_term_bounded(&cx.gamma, t).ok()?;
        unification::canonical(&w).then_some(w)
    }

    /// [`unification::U::next_head`]: `t`, in `cx`, unfolded to the first
    /// reduct whose spine is headed by another global or local, or by a
    /// former or constructor. A β-redex or an eliminator on the way is
    /// stepped through, as a whnf would: a definition whose body is a
    /// `match` on a constructor argument reaches the arm it selects. One
    /// stuck on a neutral is no next head (`None`), and nor is a walk past
    /// [`Unfold::NextHead`] head reducts or the oracle's fuel.
    pub(crate) fn next_head(&self, cx: &Cx, t: &Term) -> Option<Term> {
        let head = spelling::app_spine(t).0.clone();
        let mut last = None;
        for r in self.semantic_oracle().unfold(&cx.gamma, t, Unfold::NextHead) {
            let exposed = match spelling::app_spine(&r).0 {
                h @ (Term::GlobalTm { .. } | Term::Var(_)) => *h != head,
                h => !unification::steps_through(h),
            };
            if exposed {
                return Some(r);
            }
            last = Some(r);
        }
        // A walk that ends on a case analysis it cannot take — on a neutral
        // scrutinee, the `match h:` of a `decreases` body — ends on a head
        // a pattern can meet arm by arm (issues/unify-through-match-arms.md).
        last.filter(|r| matches!(spelling::app_spine(r).0, Term::Case { .. }))
    }

    /// [`unification::U::succ_pred`]: `a + k` at a positive numeral `k`,
    /// one successor down — `a + (k - 1)`, or `a` at `k = 1`.
    pub(crate) fn succ_pred(&self, t: &Term) -> Option<Term> {
        let (fun, k) = spelling::app_of(t)?;
        let pred = match &**k {
            Term::Succ(j) => (**j).clone(),
            Term::NatLit(j) if !j.is_zero() => heather_kernel::term::nat_lit_pred(j),
            _ => return None,
        };
        let (_, a) = spelling::app_of(fun)?;
        crate::omega_cert::named_args(self, t, "nat::Nat::add")?;
        Some(match (pred, t) {
            (Term::Zero, _) => (**a).clone(),
            (pred, Term::App { fun, dom_level, cod_level, dom, cod, .. }) => Term::App {
                fun: Rc::clone(fun),
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
                arg: Rc::new(pred),
            },
            (pred, _) => Term::AppAt { fun: Rc::clone(fun), arg: Rc::new(pred) },
        })
    }

    /// [`unification::U::unfold_constant`]: a closed constant of Σ, `t`,
    /// unfolded one δ step to its definition, when it is transparent.
    pub(crate) fn unfold_constant(&self, cx: &Cx, t: &Term) -> Option<Term> {
        self.semantic_oracle().unfold(&cx.gamma, t, Unfold::NextHead).next()
    }

    /// The unifier's context for a root attempt in `cx`: the scope, and
    /// [`Self::spine_type_args`] for the `app@` nodes of a subject. Every
    /// solution is held to its slot's declared type in `doms` (the call's
    /// scratch world; a slot past its end is not judged), and `true` means a
    /// write was refused for not inhabiting it ([`SolutionCheck`]).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn unify_root(&self, cx: &Cx, pat: &Type, subj: &Type, n: u32, sols: &mut [Sol], doms: &[Type], span: Span) -> bool {
        self.unify_checked(cx, pat, subj, n, 0, sols, doms, None, Guesses::Take, None, span)
    }

    /// Does the registered instance `global`'s **conclusion** — its type
    /// past every parameter, each parameter a fresh slot — decidedly differ
    /// from `goal` ([`unification::Clash`])? Instance search asks before it
    /// builds the candidate (issues/instance-conclusion-matched-first.md):
    /// building elaborates a reference at the goal, premises and all, and
    /// then the kernel refuses it, which is the whole cost of a candidate
    /// that could never have matched. A closed instance is its own
    /// conclusion. `false` is "may match", always the answer when the
    /// conclusion cannot be read (a universe-polymorphic instance's `UΠ`, a
    /// binding out of reach) or the unifier could not decide.
    pub(crate) fn conclusion_clashes(&self, cx: &Cx, global: &str, goal: &Type, span: Span) -> bool {
        let Some(GlobalInfo { abs, .. }) = self.names.global(global) else { return false };
        let Some(GlobalBinding::Tm { ty, .. }) = self.psi.bindings.get(*abs as usize) else { return false };
        // The use-site type, as a reference to the global would carry it
        // (`elab_var`): a committed statement as stored, out of the empty
        // context it was declared in into this Γ.
        let empty = LocalSubst {
            tail: SubstTail::Empty,
            terms: vec![],
        };
        let ty = ty.apply_local(&empty);
        // One slot per leading binder, instantiated as an application's
        // implicits are: the slots sit innermost, under the identity.
        let mut n = 0u32;
        let mut t = &ty;
        while let Type::Pi { cod, .. } = t {
            n += 1;
            t = cod;
        }
        let mut doms = Vec::with_capacity(n as usize);
        let mut conclusion = ty.shift_global(n);
        for slot in 0..n {
            let Type::Pi { dom, cod, .. } = conclusion else { return false };
            doms.push((*dom).clone());
            let meta = Term::GlobalTm { var: GlobalVar::index(slot), subst: LocalSubst::id(&cx.gamma) };
            conclusion = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(meta)));
        }
        let pat = GeneratedDefs(self).unspell_ty_deep(&conclusion).unwrap_or(conclusion);
        let subj = GeneratedDefs(self).unspell_ty_deep(goal);
        let subj = subj.as_ref().unwrap_or(goal);
        let mut sols = vec![Sol::Unsolved; n as usize];
        let clash = unification::Clash::default();
        self.unify_checked(cx, &pat, subj, n, 0, &mut sols, &doms, None, Guesses::Take, Some(&clash), span);
        clash.seen()
    }

    /// [`Self::unify_root`] for a subject `d` binders past `cx`: the
    /// metavariables are scoped in `cx`, and a solution that mentions one of
    /// the `d` is not learned. The tactic host's holes, made in a scope
    /// enclosing the one a comparison happens in, are unified this way.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn unify_under(&self, cx: &Cx, pat: &Type, subj: &Type, n: u32, d: u32, sols: &mut [Sol], doms: &[Type], span: Span) -> bool {
        self.unify_checked(cx, pat, subj, n, d, sols, doms, None, Guesses::Take, None, span)
    }

    /// The one root of the unifier: its context in `cx`, its writes held to
    /// `doms` by a [`SolutionCheck`], `disagree` told of a later subject a
    /// solved slot meets ([`unification::U::disagree`]), and its guesses
    /// taken, postponed or recorded as `guesses` says.
    #[allow(clippy::too_many_arguments)]
    fn unify_checked(
        &self,
        cx: &Cx,
        pat: &Type,
        subj: &Type,
        n: u32,
        d: u32,
        sols: &mut [Sol],
        doms: &[Type],
        disagree: Option<&dyn Fn(usize, &Term)>,
        guesses: Guesses<'_>,
        clash: Option<&unification::Clash>,
        span: Span,
    ) -> bool {
        let type_args = |t: &Term, e: u32| self.spine_type_args(cx, t, e, span);
        let canonical_head = |t: &Term, e: u32| self.canonical_head(cx, t, e);
        let respell = |t: &Type| GeneratedDefs(self).respell_ty(cx, t);
        let constructor = |t: &Type| GeneratedDefs(self).constructor_spelling(cx, t, span);
        let slot_view = |t: &Term| GeneratedDefs(self).slot_view(t);
        let check = SolutionCheck::new(self, cx, doms, n);
        let admit = |i: usize, s: &Term, sols: &[Sol]| check.admit(i, s, sols);
        let slot_type = |i: usize, sols: &[Sol]| doms.get(i).and_then(|t| unification::zonked(t, n, sols));
        let next_head = |t: &Term| self.next_head(cx, t);
        let unfold_constant = |t: &Term| self.unfold_constant(cx, t);
        let succ_pred = |t: &Term| self.succ_pred(t);
        let u = unification::U {
            gamma: &cx.gamma,
            subject_metas: None,
            type_args: &type_args,
            canonical_head: &canonical_head,
            respell: &respell,
            constructor: &constructor,
            slot_view: &slot_view,
            slot_type: &slot_type,
            admit: &admit,
            disagree,
            next_head: &next_head,
            unfold_constant: &unfold_constant,
            succ_pred: &succ_pred,
            guesses,
            clash,
        };
        unify_ty_root(&u, pat, subj, n, d, sols);
        check.settle(sols)
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
    /// application with implicit insertion is ambiguous, so it is refused —
    /// except that `mask` may cover only a *prefix* of the remaining
    /// parameters (the bare-reference route of
    /// docs/elaborator/unifier-completeness-design.md §5.3), in which case the
    /// parameters past the mask are simply left unapplied.
    ///
    /// `param_offset` is how many leading parameters the head has already
    /// consumed (the type arguments of an `f<T, …>(…)` call) — passed rather
    /// than recovered from `all_params.len() - mask.len()`, which is only
    /// right when the mask is a suffix. `bare_ref` selects the §7.1 message
    /// flavor for the zero-argument checking-position route.
    #[allow(clippy::too_many_arguments)]
    /// Read implicit solutions off an argument's type
    /// (docs/elaborator/argument-type-reduction-design.md): one read, in which the
    /// unifier itself unfolds the argument's type wherever it does not meet
    /// the parameter's as it stands (the δ-lazy order,
    /// issues/unifier-lazy-delta.md).
    ///
    /// There used to be a second read against the type's weak head normal
    /// form, taken when the first learned *nothing*: for an argument whose
    /// type is a **motive applied** (`P(OfNat(k))`, a β-redex
    /// `(λ (z: Int) => add(a, z) = add(z, a))(OfNat(k))`,
    /// issues/motive-application-hides-hypothesis-type.md), a field type read
    /// through a projection, or a definition's body. The unifier's own step
    /// reaches each of those, at the place the read stops meeting and only
    /// while it has a slot to learn, so the retry is gone. The *expected*
    /// type's whnf in [`Self::solve_from_expected`] stays: a higher-kinded
    /// carrier (`?M(?B)` against `Tac<Nat>`) is matched by its spelling, not
    /// by unfolding.
    ///
    /// Every read is **held to the slots' declared types** (`meta_doms`):
    /// a slot whose type is already known takes only a solution that
    /// inhabits it ([`SolutionCheck`], at the unifier's one write), so a
    /// read never records what the call could not keep.
    /// When it refused something, the argument was written in other symbols —
    /// `x ≈ y` at `Rat` against `a * d ≈ c * b` at `Int` — and the read
    /// walks the type's first [`Unfold::IndexRead`] reducts,
    /// stopping at the first declaration application that teaches something
    /// that fits: `Dyadic::Le(a, b)` is `Rat::Le(a.rat(), b.rat())` one δ
    /// step on (issues/index-inference-through-unfolding.md).
    #[allow(clippy::too_many_arguments)]
    ///
    /// Returns the slots already solved that the argument's own type met
    /// with another subject ([`application::SlotClash`]): read off the
    /// first read only, since the reduct walk runs only when it learned
    /// nothing.
    pub(crate) fn unify_arg_ty(
        &self,
        cx: &Cx,
        dom_orig: &Type,
        arg_ty: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        guesses: Guesses<'_>,
        span: Span,
    ) -> Vec<(usize, Rc<Term>)> {
        let clashes = RefCell::new(Vec::new());
        self.unify_arg_reads(cx, dom_orig, arg_ty, n, sols, meta_doms, &clashes, guesses, span);
        clashes.into_inner()
    }

    #[allow(clippy::too_many_arguments)]
    fn unify_arg_reads(
        &self,
        cx: &Cx,
        dom_orig: &Type,
        arg_ty: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        clashes: &RefCell<Vec<(usize, Rc<Term>)>>,
        guesses: Guesses<'_>,
        span: Span,
    ) {
        let learned = |sols: &[Sol]| sols.iter().filter(|s| s.solved().is_some()).count();
        let before = learned(sols);
        // Both sides in the **inline** spelling first
        // (`docs/inductives/per-instantiation-type-codes-design.md` §4.2, amended
        // 2026-09-10): the congruence below is syntactic, and a callee's
        // domain arrives off its respelled statement, where a parameterized
        // instantiation is `El (app(D#tycode_fn^δ; ā))` and the argument's own
        // type is the former. Unspelled, `Iff<P, ?Q>` meets `Σ…` and solves;
        // spelled, it solves nothing and the writer is told to give the type
        // argument. The pattern is in the call's scratch world and the subject
        // in the committed one, which is the whole of the bookkeeping.
        let dom_inline = GeneratedDefs(self).unspell_ty_deep(dom_orig);
        let dom = dom_inline.as_ref().unwrap_or(dom_orig);
        let arg_inline = GeneratedDefs(self).unspell_ty_deep(arg_ty);
        let arg_ty = arg_inline.as_ref().unwrap_or(arg_ty);
        let unify_checked =
            |sols: &mut [Sol], subject: &Type| -> bool { self.unify_checked(cx, dom, subject, n, 0, sols, meta_doms, None, guesses, None, span) };
        let record = |slot: usize, later: &Term| clashes.borrow_mut().push((slot, Rc::new(later.clone())));
        let rejected = self.unify_checked(cx, dom, arg_ty, n, 0, sols, meta_doms, Some(&record), guesses, None, span);
        if learned(sols) != before || !sols.iter().any(|s| matches!(s, Sol::Unsolved)) {
            return;
        }
        // An operation slot the syntactic read filled with a declaration of
        // another type: `Rat::Same(x, y)` read as `?≈(?*(a, d), ?*(c, b))` at
        // `Int` pairs `?≈` with `Rat::Same` (issues/index-inference-through-
        // unfolding.md). The argument's type was written in its own symbols,
        // and the parameter's are a step or two of unfolding away; read those
        // reducts, nearest first, while they are still applications of a
        // declaration, and stop at the first that teaches something that
        // fits. Bounded, and only on this path, so no call that read cleanly
        // ever steps.
        if rejected
            && let Type::El { level, tm } = arg_ty
        {
            let oracle = self.goal_oracle();
            for reduct in oracle.unfold(&cx.gamma, tm, Unfold::IndexRead) {
                if !unification::global_spine(&reduct) {
                    continue;
                }
                let unfolded = Type::El { level: level.clone(), tm: Rc::new(reduct) };
                unify_checked(sols, &unfolded);
                if learned(sols) != before {
                    return;
                }
            }
        }
    }


    /// Expected-type-directed solving (docs/elaborator/unifier-completeness-design.md
    /// §5): the expected type, consulted for the implicits an argument's type
    /// cannot reach. Called from [`application::apply_implicit`] with the call's
    /// scratch world (`n` metas, `sols` their solutions so far) just before
    /// the deferred-argument retry and the discharge.
    ///
    /// Two rules, the LGG trigger read first and keeping priority for its
    /// shape (design §5.2):
    ///
    /// - **The LGG hook** (issues/congruence-by-anti-unification.md, interim
    ///   round): when the result type is `?f(s) = ?f(t)` with the *same*
    ///   unsolved meta at both heads and `s`, `t` meta-free, and the expected
    ///   type whnf's to an `Id`, run the first-order harvest with `?f`
    ///   withheld, then solve `?f := λz. LGG(X, Y)` with every hole's witness
    ///   pair required to be exactly `(s, t)`. `?f(s) ≟ X` is outside the
    ///   Miller fragment, so no first-order rule may touch it — the
    ///   flex-head guard in [`unify_tm`] now enforces that at the source.
    ///   Once the trigger fires the outcome is **committed**: a mismatching
    ///   witness is reported here, not swallowed into "could not infer".
    ///   This half is still the documented throwaway: the LGG itself lives in
    ///   [`crate::lgg`] and outlives it, but the hook is deleted when a
    ///   layer-m goal solver can construct the call instead.
    ///
    /// - **The general harvest** (design §5.1), the else branch: unify the
    ///   scratch-world result type against the written expected type, then
    ///   its weak head normal form, learn-only. This is the same call the LGG path makes as its step 1,
    ///   run also when the flex-`Id` trigger does not fire — the general rule
    ///   of which that harvest was the special case. It is what solves
    ///   `sym(?p)`'s endpoints and the bare polymorphic reference's type
    ///   argument (design D1/D2), and it can only *learn*: a wrong solution
    ///   is a kernel rejection, an absent one keeps the caller's message.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn solve_from_expected(
        &self,
        cx: &Cx,
        result_ty: &Type,
        expected: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        guesses: Guesses<'_>,
        span: Span,
    ) -> R<()> {
        // The LGG trigger, read off the scratch-world result type.
        let flex = (|| {
            let Type::Id { lhs, rhs, .. } = result_ty else {
                return None;
            };
            let (Some((f_lhs, s_raw)), Some((f_rhs, t_raw))) =
                (spelling::app_of(lhs), spelling::app_of(rhs))
            else {
                return None;
            };
            let Term::GlobalTm { var, subst } = &**f_lhs else {
                return None;
            };
            // Unsolved, one of *this* call's metas, the same on both sides,
            // and at the identity substitution — a solution is scoped in Γ,
            // so anything else is not ours to solve.
            let slot = var.innermost(n)? as usize;
            (f_lhs == f_rhs && matches!(sols[slot], Sol::Unsolved) && *subst == LocalSubst::id(&cx.gamma))
                .then(|| (slot, Rc::clone(s_raw), Rc::clone(t_raw)))
        })();
        // The general harvest (design §5.1): the LGG's step 1 run on its own
        // whenever the flex-`Id` shape is not in play. This is the answer to
        // the old "nothing else gets to consult the expected type" comment —
        // solving result-only implicits in general *was*
        // elab-unifier-completeness's question, and this round answered it.
        // The same inline-spelling pre-pass `unify_arg_ty` takes, for the same
        // reason (§4.2, amended 2026-09-10).
        let inline_result = GeneratedDefs(self).unspell_ty_deep(result_ty);
        let result_ty = inline_result.as_ref().unwrap_or(result_ty);
        let inline_expected = GeneratedDefs(self).unspell_ty_deep(expected);
        let expected = inline_expected.as_ref().unwrap_or(expected);
        let Some((m, s_raw, t_raw)) = flex else {
            // Preserve named relations and operation applications before
            // unfolding a transparent relation into its definition. Held to
            // the slots' types as an argument's read is: `x ≈ z` at `Rat`
            // against `?≈(?*(a, f), ?*(e, b))` at `Int` pairs `?≈` with
            // `Rat::Same` (issues/index-inference-through-unfolding.md).
            self.unify_checked(cx, result_ty, expected, n, 0, sols, meta_doms, None, guesses, None, span);
            // The expected type's weak head can teach only the metas the
            // result type still mentions: unification records into the
            // pattern's metas and nowhere else. Once it mentions none, the
            // read would learn nothing, and at a closed verdict it is the
            // verdict's whole evaluation, which the kernel is about to run
            // again — `decide_yes(refl)` at `heavy(300).IsTrue()`, whose
            // result `P` the line above has just solved
            // (issues/closed-verdict-evaluated-twice.md).
            if zonked(result_ty, n, sols).is_some() {
                return Ok(());
            }
            let head = self.whnf(cx, expected, span)?;
            let head = GeneratedDefs(self).unspell_ty_deep(&head).unwrap_or(head);
            self.unify_checked(cx, result_ty, &head, n, 0, sols, meta_doms, None, guesses, None, span);
            return Ok(());
        };
        // Step 1, with `?f` withheld (unsolved-but-untouchable — `unify_tm`
        // records only into `Unsolved`, and the flex-head guard skips the
        // spines it heads). The pattern is in the scratch world and the
        // subject in the committed one, exactly as at an argument's domain.
        sols[m] = Sol::Withheld;
        self.unify_root(cx, result_ty, expected, n, sols, meta_doms, span);
        let expected_head = self.whnf(cx, expected, span)?;
        let expected_head = GeneratedDefs(self).unspell_ty_deep(&expected_head).unwrap_or(expected_head);
        self.unify_root(cx, result_ty, &expected_head, n, sols, meta_doms, span);
        sols[m] = Sol::Unsolved;
        // `s` and `t` must be meta-*free* once the solved metas are
        // substituted away: the witnesses are compared with `==`, and an
        // unsolved meta is not a term (decision 2).
        let (Some(s), Some(t)) = (zonked_tm(&s_raw, n, sols), zonked_tm(&t_raw, n, sols)) else {
            return Ok(());
        };
        let Type::Id { lhs: x, rhs: y, .. } = expected_head else {
            return Ok(());
        };
        // The abstraction's domain is `?f`'s *declared* parameter type — the
        // only place it can come from, since no argument has it. It is a `Π`
        // by construction of the trigger (a meta that is applied), and its
        // own metas are solved by now or the call could not have got here.
        let dom_ty = &meta_doms[m];
        let Some(dom_ty) = zonked(dom_ty, n, sols) else {
            return Ok(());
        };
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            ..
        } = self.whnf(cx, &dom_ty, span)?
        else {
            return Ok(());
        };
        // Two attempts, in this order, and no more
        // (docs/elaborator/congruence-in-inference-position-design.md §3).
        //
        // 1. The endpoints **as written**. This is the whole of decision 2 as
        //    it landed, and it stays first so that no goal that generalized
        //    before now generalizes differently: reducing can only destroy a
        //    match (`f(a) = f(b)` at a transparent `f` unfolds into two
        //    unrelated-looking bodies), so a syntactic success is never
        //    thrown away for a reduced one.
        // 2. The endpoints in **weak head normal form**, once each. This is a
        //    deliberate, bounded loosening of "exactly `(s, t)` is `==`": the
        //    *witness* comparison is still syntactic, and still `==` — what
        //    reduces is the goal, and only its two outermost nodes.
        //
        // Why the second attempt exists at all: a library statement is
        // written in the reader's terms, not the elaborator's.
        // `mul(OfNat(m), OfNat(n)) = mul(OfNat(n), OfNat(m))` names no
        // congruence context anywhere in its syntax; one whnf apiece turns
        // both sides into `OfNat(…)` and the context is `OfNat(□)`. Without
        // this the rule fires only at goals that were *already* spelled
        // through the function being abstracted, which is the minority of
        // them (issues/congruence-by-anti-unification.md, 2026-08-18).
        //
        // Why *only* the goal and not `s`/`t`: the witnesses come from the
        // proof's type and the goal's payload comes from the statement, and
        // both are written in the same unreduced terms. Reducing one side of
        // that comparison and not the other is what would break the match.
        //
        // Why whnf and not conversion: an unbounded `conv` call per `cong`
        // is the memory-superlinear hazard this project keeps out of the
        // elaborator, and it would also make failure quiet. Two whnfs are
        // linear and terminating, which is the property §3 of the issue
        // claims for this solver.
        //
        // 3. The reduced goal again with the **witness up to conversion**
        //    (`lgg::lgg_body_up_to_conversion`), only after both of the above
        //    failed: at a differing node that mentions none of the walk's
        //    binders, the sides convert to `(s, t)`. Conversion runs only
        //    there, top-down, so typically once per side, and the abstraction
        //    is kept only if it kernel-checks at `?f`'s type. A failure
        //    reports attempt 2's mismatch, so the message is the one it always
        //    was. A goal on a family reaches this: its reduct carries the
        //    constructor's pieces as each function spelled them
        //    (issues/cong-inference-through-iwf-w-children.md).
        let body = match lgg::lgg_body(&x, &y, &s, &t) {
            Ok(body) => body,
            Err(first) => {
                let rx = self.whnf_tm(cx, &x, span)?;
                let ry = self.whnf_tm(cx, &y, span)?;
                let reduced = *rx != *x || *ry != *y;
                let second = if reduced { lgg::lgg_body(&rx, &ry, &s, &t) } else { Err(first) };
                match second {
                    Ok(body) => body,
                    Err(mismatch) => {
                        let fits = |body: &Term| {
                            let f = Term::Lam {
                                dom_level: dom_level.clone(),
                                cod_level: cod_level.clone(),
                                dom: Rc::clone(&dom),
                                body: Rc::new(body.clone()),
                            };
                            let fl = Level::max(dom_level.clone(), cod_level.clone());
                            typing::check_term(&self.goal_psi(), 0, Layer::Prog, &cx.gamma, &f, &dom_ty, &fl, self.policy.fuel)
                                .is_ok()
                        };
                        // `(a, b)`, scoped in `Γ`: `(s, t)` up to conversion
                        // there, at `?f`'s domain.
                        let oracle = self.goal_oracle();
                        let witness = |a: &Term, b: &Term| {
                            let conv = |l: &Term, r: &Term| {
                                oracle.convert_term(&cx.gamma, Layer::Prog, l, r, &dom, &dom_level).is_ok()
                            };
                            conv(a, &s) && conv(b, &t)
                        };
                        let witness_fst = |a: &Term, b: &Term, s1: &Term, t1: &Term, ty: &Type, level: &Level| {
                            let conv = |l: &Term, r: &Term| {
                                oracle.convert_term(&cx.gamma, Layer::Prog, l, r, ty, level).is_ok()
                            };
                            conv(a, s1) && conv(b, t1)
                        };
                        match lgg::lgg_body_up_to_conversion(&rx, &ry, &s, &t, &witness, &witness_fst).ok().filter(|body| fits(body)) {
                            Some(body) => body,
                            None => {
                                let msg = self.cong_mismatch(cx, &mismatch, expected, &s, &t);
                                return Err(ElabError::Elab { msg, span });
                            }
                        }
                    }
                }
            }
        };
        sols[m] = Sol::Solved(Rc::new(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body),
        }));
        Ok(())
    }

    /// The `cannot generalize` message
    /// (issues/lgg-diagnostic-dumps-kernel-terms.md).
    ///
    /// The solver reports a *position* and this reads it out: the goal as
    /// surface, the proof's endpoints as surface, and the two sides at the
    /// stopping node where they can be read in the goal's own context. What it
    /// deliberately never does is print a kernel term — at a lowered inductive
    /// that was four multi-thousand-character walls, and the useful fact was
    /// not recoverable from any of them.
    ///
    /// Every spelling is optional and its absence costs a clause, not the
    /// message: `spell_*` declines rather than half-spelling
    /// (`docs/elaborator/surface-type-display-design.md` §2), and the position — which is
    /// the part the reader could not get before — needs no context at all.
    fn cong_mismatch(
        &self,
        cx: &Cx,
        m: &lgg::Mismatch,
        expected: &Type,
        s: &Term,
        t: &Term,
    ) -> String {
        let mut msg = m.to_string();
        // The two sides at the stopping node, when the walk stopped somewhere
        // that mentions none of the binders it descended under. A subterm that
        // *does* mention them has no reading in `cx` at all, and inventing one
        // would name the reader's variables wrongly — so the formers, already
        // in `m`'s own sentence, are the whole of what is said about it.
        if let Some((a, b)) = &m.at
            && let (Some(a), Some(b)) = (
                strengthen_tm(&cx.gamma, a, m.depth),
                strengthen_tm(&cx.gamma, b, m.depth),
            )
            && let (Some(a), Some(b)) =
                (self.spell_term_clean(cx, &a), self.spell_term_clean(cx, &b))
            // `#scrut` and its kin are elaborator-internal binder names. A
            // reader cannot look one up, and a clause built on one reads as
            // the kernel wall wearing surface syntax — which is what the
            // *clean* spellings below are there to refuse. The formers in
            // `m`'s own sentence still say what the node is.
            && !a.contains('#')
            && !b.contains('#')
        {
            msg.push_str(&format!(" (`{a}` against `{b}`)"));
        }
        // *Clean* spellings throughout: every clause here makes a claim about
        // a term, and a half-spelled one is the kernel wall wearing surface
        // syntax (`issues/check-fallback-discards-expected-type.md`). A clause
        // that cannot be said cleanly is not said.
        // No bare `.` in the `else`: the next clause opens with `, and the
        // proof's endpoints`, so a period here punctuates the sentence into
        // `against \`Nil\`., and the proof's …`. A clause that cannot be said
        // is not said, and it leaves no mark either.
        if let Some(goal) = self.spell_type_clean(cx, expected) {
            msg.push_str(&format!(". The goal is `{goal}`"));
        }
        match (self.spell_term_clean(cx, s), self.spell_term_clean(cx, t)) {
            (Some(s), Some(t)) => {
                msg.push_str(&format!(", and the proof's endpoints are `{s}` and `{t}`"));
            }
            _ => msg.push_str(", and the proof's endpoints do not spell as surface"),
        }
        msg.push_str(
            " — every differing position has to be exactly the proof's endpoints \
             (issues/congruence-by-anti-unification.md §3)",
        );
        if let Some(why) = self.cong_invisible_difference(cx, m, s, t) {
            msg.push_str(&why);
        } else if let Some(why) = self.cong_goal_sides_look_equal(cx, expected) {
            msg.push_str(&why);
        } else if m.sides.0 == "El" || m.sides.1 == "El" {
            msg.push_str(EL_AGAINST_CODE);
        }
        msg
    }

    /// The other half of the same complaint: the *goal* prints as `X = X`.
    ///
    /// `. The goal is \`wrap(c, Red) = wrap(c, Red)\`` above a sentence that
    /// says those two sides differ reads as a lie, and the reader has no way
    /// to see what parts them — for the same reason as in
    /// [`Self::cong_invisible_difference`]: the walk compares terms and the
    /// message renders surface (issues/lgg-error-hides-the-implicit.md).
    fn cong_goal_sides_look_equal(&self, cx: &Cx, expected: &Type) -> Option<String> {
        let Type::Id { lhs, rhs, .. } = expected else {
            return None;
        };
        if lhs == rhs {
            return None;
        }
        let (l, r) = (
            self.spell_term_clean(cx, lhs)?,
            self.spell_term_clean(cx, rhs)?,
        );
        if l != r {
            return None;
        }
        let d = lgg::first_difference(lhs, rhs);
        let mut why =
            format!(". The goal's own two sides both spell `{l}` and are not the same term");
        if let Some(d) = &d {
            why.push_str(&format!(" — they part {d:#}"));
        }
        why.push_str(", so the difference the walk stopped at is one the spelling does not show");
        if matches!(&d, Some(d) if d.sides.0 == "El" || d.sides.1 == "El") {
            why.push_str(EL_AGAINST_CODE);
        }
        Some(why)
    }

    /// The clause that keeps the message above from contradicting itself.
    ///
    /// When the walk stops at the very position the proof witnesses — the two
    /// sides there *spell* exactly like the two endpoints — the sentence names
    /// the same two strings as both the difference and the match, and a reader
    /// following it concludes the condition is already met
    /// (issues/lgg-error-hides-the-implicit.md). The difference is real and
    /// invisible: the witness test is structural `==` with no conversion
    /// (decision 2), so a type argument spelled two convertible ways is a
    /// difference the surface speller drops.
    ///
    /// So: find the side whose spelling matches its endpoint but whose term
    /// does not, and say where the two actually part. [`lgg::first_difference`]
    /// answers that in the same vocabulary the rest of the message uses, which
    /// is why this stays a *position* and never prints a kernel term — the
    /// wall `issues/lgg-diagnostic-dumps-kernel-terms.md` exists to stop.
    fn cong_invisible_difference(
        &self,
        cx: &Cx,
        m: &lgg::Mismatch,
        s: &Term,
        t: &Term,
    ) -> Option<String> {
        let (a, b) = m.at.as_ref()?;
        // Read both sides in `cx` — the same strengthening the `(a against b)`
        // clause above uses, and for the same reason: a subterm that mentions
        // a binder the walk descended under has no reading here at all.
        let a = strengthen_tm(&cx.gamma, a, m.depth)?;
        let b = strengthen_tm(&cx.gamma, b, m.depth)?;
        for (side, goal, endpoint) in [("left", &a, s), ("right", &b, t)] {
            if goal == endpoint {
                continue;
            }
            let (Some(g), Some(e)) = (
                self.spell_term_clean(cx, goal),
                self.spell_term_clean(cx, endpoint),
            ) else {
                continue;
            };
            if g != e {
                continue;
            }
            let mut why = format!(
                ". That position is the one the proof witnesses, and it looks like it: \
                 the {side} side there and the proof's {side} endpoint both spell `{g}`, \
                 but they are not the same term"
            );
            if let Some(d) = lgg::first_difference(goal, endpoint) {
                why.push_str(&format!(" — they part {d:#}"));
            }
            why.push_str(
                ". The witness test is structural, never up to conversion \
                 (issues/congruence-by-anti-unification.md §3 decision 2), so a difference \
                 the surface spelling drops still declines. Spell the endpoint the way the \
                 goal does, or use an explicit congruence lemma",
            );
            if m.sides.0 == "El" || m.sides.1 == "El" {
                why.push_str(EL_AGAINST_CODE);
            }
            return Some(why);
        }
        None
    }
}
