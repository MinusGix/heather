//! The kernel local context and its parallel surface-level bindings.

use std::sync::Arc as Rc;
use std::cell::{OnceCell, RefCell};
use std::collections::BTreeMap;
use std::borrow::Cow;

use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, LocalCtx, Term, Type};
use heather_syntax::{Expr, ExprKind, Ty};

use crate::recursion::{Guard, SelfRef};
use crate::{R, Skel, quote};

/// Elaboration context: kernel Γ plus the parallel name list
/// (`names[j]` names `gamma.entries[j]`, outermost first).
#[derive(Clone)]
pub(crate) struct Cx {
    /// One enclosing dot call's chain, shared by lookup and its cloned
    /// desugared argument. Only source dots are keyed by span: desugaring
    /// builds applications, so generated nodes cannot alias this key.
    pub(crate) dot_receiver: Option<Rc<DotReceivers>>,
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
    /// Set while a **quotation payload** elaborates (`quote.rs`'s `pcx`), and
    /// nowhere else. The checked spellings of
    /// `docs/intro-by-type-design.md` §2.3 may not appear inside a `box`: the
    /// code grammar, `code_eq` and the 56 recursor branches range over that
    /// payload, and `tm_pair`'s branch telescope types its field
    /// sub-structures by `U_S`/`U_T`, which a collapsed annotation cannot
    /// state (§2.2). The design spelled this restriction as "layers p and m",
    /// which does not transcribe: Heather checks **every** declaration body at
    /// `Layer::Code` (`lib.rs` ~3637, and `DESIGN.md`'s δ-layer-preservation
    /// argument is why), so a layer predicate is constantly false. "Under a
    /// quotation" is the property §2.2 actually needs.
    pub(crate) quoted: bool,
}

type ReceiverInference = OnceCell<R<(Term, Type, Level)>>;

pub(crate) struct DotReceivers {
    gamma: LocalCtx,
    aliases: Vec<Rc<Alias>>,
    inferred: RefCell<BTreeMap<(usize, usize), Rc<ReceiverInference>>>,
}

impl DotReceivers {
    fn matches(&self, cx: &Cx) -> bool {
        cx.gamma == self.gamma && cx.aliases.len() == self.aliases.len()
            && cx.aliases.iter().zip(&self.aliases).all(|(a, b)| Rc::ptr_eq(a, b))
    }

    pub(crate) fn inference(&self, cx: &Cx, e: &Expr) -> Option<Rc<ReceiverInference>> {
        if !matches!(e.kind, ExprKind::Dot { .. }) || !self.matches(cx) {
            return None;
        }
        self.inferred.borrow().get(&(e.span.start, e.span.end)).cloned()
    }

    fn register(&self, e: &Expr) {
        self.inferred.borrow_mut().entry((e.span.start, e.span.end))
            .or_insert_with(|| Rc::new(OnceCell::new()));
    }
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
            dot_receiver: None,
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
            quoted: false,
        }
    }

    pub(crate) fn with_dot_receiver(&self, recv: &Expr) -> Cow<'_, Cx> {
        if !matches!(recv.kind, ExprKind::Dot { .. }) || crate::has_free_slots(recv) {
            return Cow::Borrowed(self);
        }
        // Keep all prefix outcomes through checking retries of this chain,
        // rather than recreating each inner receiver's cache on every retry.
        if let Some(receivers) = &self.dot_receiver
            && receivers.matches(self)
        {
            receivers.register(recv);
            return Cow::Borrowed(self);
        }
        let mut cx = self.clone();
        let receivers = Rc::new(DotReceivers {
            gamma: self.gamma.clone(),
            aliases: self.aliases.clone(),
            inferred: RefCell::new(BTreeMap::new()),
        });
        receivers.register(recv);
        cx.dot_receiver = Some(receivers);
        Cow::Owned(cx)
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
        out.dot_receiver = None;
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
        self.dot_receiver = None;
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
    use heather_syntax::Span;

    #[test]
    fn receiver_outcomes_are_shared_only_in_their_original_scope() {
        let recv = Expr {
            kind: ExprKind::Dot {
                recv: Box::new(Expr { kind: ExprKind::Var("x".into()), span: Span { start: 0, end: 1 } }),
                name: "f".into(), tyargs: vec![], args: Some(vec![]), named: vec![],
            },
            span: Span { start: 0, end: 5 },
        };
        let mut cx = Cx::empty();
        cx.push("x".into(), Type::Nat, Level::Zero);
        let scoped = cx.with_dot_receiver(&recv).into_owned();
        let receivers = scoped.dot_receiver.as_ref().unwrap();
        let first = receivers.inference(&scoped, &recv).unwrap();
        first.set(Ok((Term::Var(heather_kernel::term::LocalVar(0)), Type::Nat, Level::Zero))).unwrap();
        let retry = scoped.with_dot_receiver(&recv);
        let second = retry.dot_receiver.as_ref().unwrap().inference(&retry, &recv.clone()).unwrap();
        assert!(Rc::ptr_eq(&first, &second));
        assert!(second.get().unwrap().is_ok());

        let mut changed = scoped.clone();
        changed.gamma.base = heather_kernel::term::CtxBase::Var(heather_kernel::term::GlobalVar(0));
        assert!(receivers.inference(&changed, &recv).is_none());
        changed = scoped.clone();
        changed.aliases.push(Rc::new(Alias {
            name: "x".into(), depth: 1, term: Rc::new(Term::Zero),
            ty: Type::Nat, level: Level::Zero, skel: None,
        }));
        assert!(receivers.inference(&changed, &recv).is_none());
        changed = scoped.clone();
        changed.push("y".into(), Type::Nat, Level::Zero);
        assert!(changed.dot_receiver.is_none());
        assert!(scoped.prefix(1).dot_receiver.is_none());
    }

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
