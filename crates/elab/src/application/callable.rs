//! Callable declaration metadata queries.
//!
//! These queries interpret one canonical parameter table for implicit masks,
//! receiver placement, bare-value skeletons, and result-only deferral. They do
//! not elaborate an application; the explicit and implicit spine engines own
//! that mechanism.

use heather_kernel::rc::Rc;

use heather_kernel::term::{CtxBase, GlobalBinding, Type};

use super::{ParamMeta, Skel};
use crate::{Cx, Elaborator, GlobalInfo, mentions_binder};

/// Callable heads' part of the elaborator.
pub(crate) struct Callables<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Callables<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Callables<'_> {
    // -- application (explicit + implicit spines) ---------------------------

    /// The implicit-parameter mask of a callable global (empty for locals,
    /// builtins, and unknown names — none of which take implicits).
    pub(crate) fn implicit_mask(&self, name: &str) -> Vec<bool> {
        self.params_of(name).iter().map(|p| p.implicit).collect()
    }

    /// Where a method call's receiver goes in the *explicit* argument list:
    /// the position of the `self`-marked parameter among the explicit,
    /// non-type-variable ones, or `0` when nothing is marked.
    ///
    /// Counting over explicit parameters only is the whole subtlety. The
    /// receiver is inserted into the surface argument list, which is what the
    /// writer typed — implicits are filled later, by the name-directed mask
    /// ([`Self::implicit_mask`]), and type arguments are never passed at all
    /// (issues/at-and-type-arguments.md). So a `self` sitting behind two
    /// `{}`-implicits is still explicit-index 0.
    ///
    /// Unmarked is `0` rather than "no method call", so every declaration
    /// that predates the marker keeps working and a one-premise lemma never
    /// has to write it (issues/method-receiver-position.md).
    pub(crate) fn subject_index(&self, name: &str) -> usize {
        subject_index_in(&self.params_of(name))
    }

    /// The parameters of a callable global, for defaulting goal names.
    pub(crate) fn params_of(&self, name: &str) -> Rc<Vec<ParamMeta>> {
        match self.lookup_global(name) {
            Some(GlobalInfo { params, .. }) => Rc::clone(params),
            None => Rc::new(Vec::new()),
        }
    }

    /// Does a bare `name` in this context resolve to a **committed global**
    /// with a non-empty *leading implicit prefix* in its parameter list — the
    /// precondition of the bare-reference route
    /// (docs/unifier-completeness-design.md §5.3)? Returns the prefix length.
    ///
    /// The precedence checks replicate [`Self::resolve`]'s order exactly:
    /// locals, aliases and constructors keep their existing wins, `Zero`/
    /// `Succ` stay primitives, a `meta fn` slice stays pure quotation, and
    /// the enclosing declaration's own name stays a recursion marker. The
    /// route runs only when `resolve` would land on the global anyway.
    /// The implicitness skeleton a bare `name` offers as a *value* head: the
    /// local binder's `Cx` entry or the alias's, following [`Self::resolve`]'s
    /// precedence exactly (an alias bound at depth `d` shadows every binder
    /// at position `< d`), so a skeleton is consulted only for the entity the
    /// name resolves to (docs/implicit-binders-design.md §4.1). `None` for
    /// anything that is not a local or alias — a global's metadata is
    /// `ParamMeta`, not a skeleton.
    pub(crate) fn value_skel(&self, cx: &Cx, name: &str) -> Option<Rc<Skel>> {
        if name == "Zero" || name == "Succ" {
            return None;
        }
        let local_pos = cx.names.lookup(name);
        let alias = cx.aliases.iter_inner().find(|a| a.name == *name);
        match (local_pos, alias) {
            (Some(pos), Some(a)) if a.depth <= pos => cx.names.skel(pos).cloned(),
            (_, Some(a)) => a.skel.clone(),
            (Some(pos), None) => cx.names.skel(pos).cloned(),
            (None, None) => None,
        }
    }

    /// The committed global a bare `name` resolves to here, as an absolute Ψ
    /// index — `None` whenever [`Self::resolve`] would land anywhere else
    /// (a local, an alias, a constructor, a primitive, the declaration's own
    /// name, a `meta fn` slice). The precedence is [`Self::bare_implicit_prefix`]'s,
    /// for its reason: the answer is about the entity the name *resolves to*.
    /// Receiver dispatch asks it of the reading it races
    /// (issues/receiver-dispatch-coinciding-readings.md).
    pub(crate) fn bare_global_abs(&self, cx: &Cx, name: &str) -> Option<usize> {
        if name == "Zero" || name == "Succ" || cx.meta.is_some() {
            return None;
        }
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || self.ctor_of(name).is_some()
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return None;
        }
        self.global_abs(name)
    }

    pub(crate) fn bare_implicit_prefix(&self, cx: &Cx, name: &str) -> Option<usize> {
        if name == "Zero" || name == "Succ" || cx.meta.is_some() {
            return None;
        }
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || self.ctor_of(name).is_some()
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return None;
        }
        self.lookup_global(name)?;
        let prefix = self
            .params_of(name)
            .iter()
            .take_while(|p| p.implicit)
            .count();
        (prefix > 0).then_some(prefix)
    }

    /// Does a saturated call `name(a⃗)` carry an implicit parameter that **no
    /// explicit parameter's domain mentions** — a *result-only* implicit
    /// (docs/congruence-in-inference-position-design.md §2)?
    ///
    /// This is the semantic half of [`Self::is_checking_only`]'s sentence.
    /// The syntactic members of that set are forms whose `elab_infer` arm
    /// *refuses*; a call with a result-only implicit is a form whose
    /// `apply_implicit` refuses, for the same reason and with the same
    /// consequence: in inference mode it cannot contribute a solution,
    /// because the only evidence that could fill the slot is an expected
    /// type. `cong(p)` is the motivating instance — `f` occurs in `f(a) =
    /// f(b)` and in its own domain, and in nothing an argument carries — and
    /// the test is deliberately *not* keyed to `cong`: any declaration of
    /// that shape gets the same deferral.
    ///
    /// Note what the test does **not** say. `sym<A>({a},{b}, p: a = b)`'s `A`
    /// is not result-only: the kernel's `Id` carries its type, so `A` occurs
    /// in `p`'s domain and an inferred argument solves it. That is the whole
    /// reason the test is an occurrence check on the *kernel* telescope
    /// rather than on the written surface types — the written `a = b` hides
    /// the `A`, and a surface-level reading would defer every `sym` in the
    /// library for nothing.
    ///
    /// Three guards, each keeping a call that infers today on its old path:
    ///
    /// - `@name(…)` (`explicit`) fills every parameter by hand, so nothing is
    ///   left to infer;
    /// - a call with **spill** (more arguments than declared parameters) is
    ///   the curried-tail route of [`application::apply_implicit`], where the
    ///   over-applied argument's type is exactly the evidence a result-only
    ///   implicit is missing (issues/curried-tail-type-arg-inference.md);
    /// - a **solver** parameter is filled by resolution, not unification, so
    ///   its being result-only says nothing.
    ///
    /// `name<…>(…)` needs no guard: it parses as an `App` whose head is a
    /// `TyApp`, which [`Expr::as_named`] already declines.
    pub(crate) fn call_defers_for_result_only(&self, cx: &Cx, name: &str, n_args: usize) -> bool {
        if name == "Zero" || name == "Succ" || cx.meta.is_some() {
            return false;
        }
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || self.ctor_of(name).is_some()
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return false;
        }
        let Some(info) = self.lookup_global(name) else {
            return false;
        };
        let params = Rc::clone(&info.params);
        // Spill: the over-applied argument is evidence this test cannot see.
        if n_args > params.iter().filter(|p| !p.implicit).count() {
            return false;
        }
        if !params.iter().any(|p| p.implicit && p.solver.is_none()) {
            return false;
        }
        // Everything past here depends only on the declaration, so it is
        // computed once (see [`Elaborator::result_only_memo`]).
        if let Some(&hit) = self.memos.result_only_memo.borrow().get(&info.abs) {
            return hit;
        }
        let hit = self.walk_for_result_only(info.abs, &params);
        self.memos.result_only_memo.borrow_mut().insert(info.abs, hit);
        hit
    }

    /// The declaration-only half of [`Self::call_defers_for_result_only`],
    /// behind that method's memo.
    fn walk_for_result_only(&self, abs: u32, params: &[ParamMeta]) -> bool {
        let GlobalBinding::Tm { ctx, ty, .. } = &self.psi.bindings[abs as usize] else {
            return false;
        };
        // The declaration's own Δ must be `·`, or the local indices below are
        // not the parameters' (every ordinary `fn`/`theorem` is closed).
        if !matches!(ctx.base, CtxBase::Nil) || ctx.len() != 0 {
            return false;
        }
        // The declared telescope, one domain per parameter. Read off the
        // *stored* type, which is closed, so the local indices below are the
        // parameters' own and nothing has to be rescoped. A declaration whose
        // type is not a syntactic `Π` chain that far is simply not tested.
        let mut doms: Vec<Type> = Vec::with_capacity(params.len());
        let mut cur: Type = ty.as_ref().clone();
        for _ in 0..params.len() {
            let Type::Pi { dom, cod, .. } = cur else {
                return false;
            };
            doms.push((*dom).clone());
            cur = (*cod).clone();
        }
        params.iter().enumerate().any(|(i, p)| {
            p.implicit
                && p.solver.is_none()
                && !params.iter().enumerate().skip(i + 1).any(|(j, q)| {
                    !q.implicit && mentions_binder(&doms[j], j as u32, (j - 1 - i) as u32)
                })
        })
    }
}

/// [`Elaborator::subject_index`] over a parameter table already in hand, so a
/// caller that also reads the table's `self` markers looks it up once.
pub(crate) fn subject_index_in(params: &[ParamMeta]) -> usize {
    params
        .iter()
        .filter(|p| !p.implicit && !p.is_type)
        .position(|p| p.is_self)
        .unwrap_or(0)
}
