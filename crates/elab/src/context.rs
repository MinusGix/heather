//! The kernel local context and its parallel surface-level bindings.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, LocalCtx, Term, Type};
use heather_syntax::{Expr, Ty};

use crate::recursion::{Guard, SelfRef};
use crate::{Skel, quote};

/// Elaboration context: kernel Γ plus the parallel name list
/// (`names[j]` names `gamma.entries[j]`, outermost first).
#[derive(Clone)]
pub(crate) struct Cx {
    pub(crate) names: Vec<String>,
    pub(crate) gamma: LocalCtx,
    /// Parallel to `names`/`gamma.entries`: the implicitness skeleton of the
    /// binder's *written* type, where it had one
    /// (docs/implicit-binders-design.md §3.1). Maintained by [`Cx::push`]
    /// (defaulting `None`) and [`Cx::push_skel`] — one push path, so the
    /// vectors cannot desync. Nothing in a skeleton is subject to
    /// substitution or shifting (§3.2), so entries are never updated.
    pub(crate) skels: Vec<Option<Rc<Skel>>>,
    /// The declaration being elaborated, once its telescope is in scope.
    pub(crate) selfref: Option<Rc<SelfRef>>,
    /// Set inside a `Succ(k)` arm; `None` outside every such arm, where a
    /// self-call has no induction hypothesis to become.
    pub(crate) guard: Option<Rc<Guard>>,
    /// A `match` in checking position whose self-calls vary a parameter
    /// plans its generalization here for the route that builds the arms'
    /// guards (`generalize.rs`). Keyed by the `match`'s span, so it is inert
    /// for every other `match` it is cloned into.
    pub(crate) generalized: Option<Rc<crate::generalize::Generalization>>,
    /// `let` bindings in scope, outermost first. Not kernel binders: an alias
    /// is inlined at each use, so `Γ` is unchanged.
    pub(crate) aliases: Vec<Rc<Alias>>,
    /// An `inductive`'s type parameters, while its field types are being
    /// lowered at an instantiation. Empty everywhere else: type parameters are
    /// monomorphized, so they never survive into a kernel term.
    pub(crate) tyvars: Vec<TyVar>,
    /// Class dictionaries in scope, outermost first, **as written**
    /// (docs/operation-indexed-classes-design.md §5, ladder step 2). A value
    /// index is never searched for; where it is not already ground it comes
    /// from a binder of the goal's class — or of a descendant — whose own index
    /// pins it, and that index is a surface expression valid in this very
    /// context. Empty for every declaration with no class binder, which is what
    /// keeps the whole mechanism off code that has nothing to do with classes.
    pub(crate) dicts: Vec<Rc<DictBinder>>,
    /// Index names that a *repeated* constraint left bound to nothing
    /// (`docs/operation-indexed-classes-design.md` §5.2), with the refusal
    /// each one owes. Consulted only where the answer would otherwise have
    /// been "unbound name".
    pub(crate) index_ambiguity: Vec<(String, String)>,
    /// Operator symbols a constraint binder **installed**, as (symbol, the
    /// index binder's generated name) — the first rung of a symbol's
    /// resolution (docs/operators-onto-classes-design.md §4, §5).
    ///
    /// `<A: Monoid(+)>` puts `("+", "#op+@0_0")` here for the whole
    /// declaration, signature and body alike, which is what makes
    /// `x + A.unit` in a *result type* the bound index rather than an ambient
    /// operator. Later entries shadow earlier ones. Empty for every
    /// declaration that names no symbol, which is every declaration written
    /// before this round.
    pub(crate) op_locals: Vec<(String, String)>,
    /// The meta-layer binder environment, present exactly while a `meta fn`'s
    /// body — or a quote payload inside it — elaborates
    /// (docs/in-language-map-design.md §5). `None` everywhere else, which is
    /// what keeps the entire quotation machinery inert for ordinary code.
    pub(crate) meta: Option<Rc<quote::MetaEnv>>,
}

/// One type parameter, bound to the type it is instantiated at
/// (`docs/inductive-tier0-lowering.md` §3.1).
///
/// `depth` is `names.len()` at the binding — the same device [`Alias`] uses,
/// and needed for the same reason. The instantiation is lowered in the
/// *ambient* context, and the constructor's field spine then pushes the
/// nominal tag and every earlier field on top of it, so a use in field `j`
/// sits `1 + j` binders deeper than where its type is scoped and must be
/// weakened by exactly that.
///
/// Getting this wrong is invisible for a *closed* instantiation, which is
/// every instantiation the suite had until 2026-07-26
/// (issues/tyvar-scoping-in-lowered-fields.md). The surface's one
/// context-dependent type is `=`, whose endpoints are terms.
#[derive(Clone)]
pub(crate) struct TyVar {
    pub(crate) name: String,
    pub(crate) ty: Type,
    pub(crate) level: Level,
    pub(crate) depth: usize,
}

/// A `let`-bound name: the elaborated right-hand side, inlined at every use
/// (the same doctrine as an inlined `fn`). `depth` is `names.len()` at the
/// binding, which is what decides shadowing against ordinary binders and how
/// far a use must be shifted.
pub(crate) struct Alias {
    pub(crate) name: String,
    pub(crate) depth: usize,
    pub(crate) term: Rc<Term>,
    pub(crate) ty: Type,
    pub(crate) level: Level,
    /// The alias's implicitness skeleton, when its `let` annotation, its
    /// RHS lambda's written marks, or the record field it projects carried
    /// one (docs/implicit-binders-design.md §3.1). `None` everywhere else.
    pub(crate) skel: Option<Rc<Skel>>,
}

impl Cx {
    pub(crate) fn empty() -> Cx {
        Cx {
            names: vec![],
            gamma: LocalCtx::nil(),
            skels: vec![],
            selfref: None,
            guard: None,
            generalized: None,
            aliases: vec![],
            tyvars: vec![],
            dicts: vec![],
            index_ambiguity: vec![],
            op_locals: vec![],
            meta: None,
        }
    }

    pub(crate) fn push(&mut self, name: String, ty: Type, level: Level) {
        self.push_skel(name, ty, level, None);
    }

    /// This context cut back to its first `n` binders — the context in which a
    /// binder at position `n`, or an [`Alias`] bound at `depth == n`, has its
    /// type scoped. Display only: a stored type is scoped in the *prefix* of Γ
    /// that precedes its binder, so rendering it against the whole of Γ reads
    /// every de Bruijn index one or more names too late
    /// (issues/goal-context-entry-printed-in-the-wrong-context.md). The
    /// context's base is kept — a prefix of Γ shares it — and everything that
    /// is not a binder rides along unchanged, since nothing on the display
    /// path indexes into those positionally.
    pub(crate) fn prefix(&self, n: usize) -> Cx {
        let mut out = self.clone();
        out.names.truncate(n);
        out.gamma.entries = self.gamma.entries.prefix(n);
        out.skels.truncate(n);
        out
    }

    /// [`Cx::push`] for the sites that carry an implicitness skeleton: the
    /// declaration telescope loop, `elab_ty`'s `Fn` arm, and the lambda
    /// binder pushes (docs/implicit-binders-design.md §3.1).
    pub(crate) fn push_skel(
        &mut self,
        name: String,
        ty: Type,
        level: Level,
        skel: Option<Rc<Skel>>,
    ) {
        self.names.push(name);
        self.gamma.entries.push(CtxEntry {
            ty: Rc::new(ty),
            level,
        });
        self.skels.push(skel);
    }
}

/// A class dictionary in scope, as the declaration wrote it
/// (`docs/operation-indexed-classes-design.md` §5). The carrier and the index
/// are **surface** and are re-elaborated in the context that consults them,
/// which is what keeps the index an ordinary expression of the use site rather
/// than a kernel term that would have to be re-scoped.
#[derive(Clone)]
pub(crate) struct DictBinder {
    /// The binder's own name, where it has a spellable one — what `d.op`
    /// looks itself up by. `#`-prefixed for an inline constraint, which
    /// deliberately offers no way to project the dictionary and therefore no
    /// way to reach this either.
    pub(crate) name: String,
    /// The class, as written — resolved through the ordinary name regime.
    pub(crate) class: String,
    pub(crate) carrier: Ty,
    pub(crate) index: Vec<Expr>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_kernel_push_keeps_surface_metadata_parallel() {
        let mut cx = Cx::empty();
        cx.push("x".into(), Type::Nat, Level::Zero);
        cx.push("y".into(), Type::Nat, Level::Zero);

        assert_eq!(cx.names.len(), cx.gamma.entries.len());
        assert_eq!(cx.skels.len(), cx.gamma.entries.len());
    }

    #[test]
    fn a_prefix_keeps_non_positional_dynamic_scope() {
        let mut cx = Cx::empty();
        cx.push("x".into(), Type::Nat, Level::Zero);
        cx.push("y".into(), Type::Nat, Level::Zero);
        cx.op_locals.push(("+".into(), "#plus".into()));

        let prefix = cx.prefix(1);
        assert_eq!(prefix.names, ["x"]);
        assert_eq!(prefix.gamma.entries.len(), 1);
        assert_eq!(prefix.skels.len(), 1);
        assert_eq!(prefix.op_locals, [("+".into(), "#plus".into())]);
    }
}
