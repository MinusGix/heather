// State carried while elaborating structurally recursive matches.

/// The enclosing declaration, in scope throughout its own body so that a
/// structurally guarded self-call can lower to the induction hypothesis
/// (issues/match-recursion.md). Nothing else can reference it: the name is
/// only registered as a global once the declaration is checked.
struct SelfRef {
    name: String,
    /// `(parameter name, implicit?)` in declaration order. Parameter `j` is
    /// bound at position `j` of the body's `Cx` (the telescope goes first).
    params: Vec<(String, bool)>,
    /// How many leading entries of [`Self::params`] are `<A, …>` type
    /// parameters. They are never passed at a call site — neither implicitly
    /// nor under `@`, which now controls only the *value* implicits
    /// (issues/at-and-type-arguments.md) — so they are skipped wholesale
    /// rather than filtered by implicitness.
    n_tyvars: usize,
}

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
        })
    }
}

/// What a guarded self-call must look like inside a `match` arm, and what it
/// lowers to (issues/match-recursion.md).
struct Guard {
    /// Index of the parameter the recursion descends on.
    dec: usize,
    kind: GuardKind,
    /// An indexed `match`'s index parameter, *rebound* by the arm
    /// (docs/inductive-indexed-lowering.md §6): a self-call must pass the
    /// arm's pattern variable there, not the original parameter.
    ///
    /// `(parameter position, one index term per descendant)` — parallel to
    /// [`GuardKind::Wf`]'s `children` and scoped at the same `depth`, because
    /// a branching index constructor gives each recursive field its *own*
    /// pattern variable (`Bal(SNode(l, r))`), and the ih at descendant `t`
    /// lives at exactly that one. `None` for every non-indexed guard.
    rebind: Option<(usize, Vec<Rc<Term>>)>,
}

/// The two arm shapes a self-call can sit in. They differ in how many
/// descendants an arm has — one for `Nat`, `mᵢ` for a branching constructor —
/// and correspondingly in whether the ih is a variable or a function of the
/// index (`docs/inductive-tier1-wf-lowering.md` §6.4).
enum GuardKind {
    /// A `Succ(k)` arm. Positions are *absolute* (indices into `cx.names`,
    /// outermost first) so they stay valid as inner binders are pushed.
    Nat {
        /// The chain of predecessors this arm makes available, outermost
        /// first: `preds[0]` is the `k` the arm itself binds, `preds[1]` the
        /// `l` a nested `match k` binds, and so on
        /// (issues/recursion-at-deeper-subterms.md). A self-call descending to
        /// `preds[i]` lowers to the `i`-th component of [`Self::tuple`].
        ///
        /// One entry for the ordinary one-step recursion; the chain grows only
        /// where the arm's own body scrutinizes the predecessor again, and
        /// only by being convoyed through that `match`
        /// (docs/course-of-values-recursion-design.md §5).
        preds: Vec<usize>,
        /// The window of past values in scope: the ih binder itself for the
        /// ordinary recursion, a Σ-tuple of the last `comps.len()` values
        /// above that. Scoped at [`Self::depth`] binders, like
        /// [`GuardKind::Wf`]'s `children`, so a call from deeper inside the
        /// arm shifts it by the difference.
        tuple: Term,
        /// Its component types, at the same scope. `comps.len()` is the depth
        /// the recursion was *elaborated* for: a call below the chain's end
        /// but within it is what a nested `match` unlocks, and a call below
        /// `comps.len()` has no component to become — the refusal
        /// `elab_self_call` reports.
        comps: Vec<Type>,
        /// The level every component lives at.
        mlvl: Level,
        /// Binder count at the arm's ih — the scope [`Self::tuple`] lives in.
        depth: usize,
        /// The recursion's motive, scoped in ([`Self::gamma`], z), kept so a
        /// nested `match` can rebuild the window's type at *its* scrutinee.
        /// The pair travels together because reindexing a family needs the
        /// context it was written in, which a shift cannot recover.
        motive: Rc<Type>,
        gamma: LocalCtx,
    },
    /// A `Wf` arm: one entry per recursive field, as
    /// `(the child's term, `ih' ι_t`, its type, that type's level)`. All four
    /// are scoped at `depth` binders, so a call from deeper inside the arm
    /// shifts them by the difference.
    ///
    /// The match is on the *term*, not the name: an arm binder is an alias
    /// (tier 0 §5.1), not a kernel binder, so there is no position to compare,
    /// and comparing terms is what keeps shadowing from faking a guarded call.
    Wf {
        depth: usize,
        children: Vec<(Rc<Term>, Rc<Term>, Type, Level)>,
        /// The arm's *container* field, if it has one
        /// (`docs/container-fields.md` §4.2). A container is a group of
        /// children rather than one, so a self-call over it maps rather than
        /// descends — and the thing it maps to is the ih *tabulated* over the
        /// container's index range.
        container: Option<ContainerIh>,
    },
}

/// What a self-call over a container binder needs, gathered at the arm and
/// scoped like the rest of [`GuardKind::Wf`], at `depth` binders.
#[derive(Clone)]
struct ContainerIh {
    /// The container binder's own term (`snd^m cs`), matched against the
    /// call's elaborated argument exactly as a plain child's term is.
    term: Rc<Term>,
    /// Its length.
    len: Rc<Term>,
    /// The ih function `Π(i : Fin (Succ^m len)). M`, as a term.
    ih: Rc<Term>,
    /// `m`: how many plain children precede the container, and so how far the
    /// container's indices are offset inside `Fin (Succ^m len)`.
    plain: usize,
    /// The motive, *strengthened* — a self-call over a container maps to a
    /// `Vec` of results, which requires a motive independent of the scrutinee
    /// (`docs/container-fields.md` §4.3). `None` when it depends, in which case
    /// [`ContainerIh::eq`] decides whether this is phase 3 or a diagnostic.
    result: Option<Type>,
    /// The motive read as an **equation**, when it is one — phase 3
    /// (`docs/container-proofs.md` §5). Set only when `result` is `None`: a
    /// dependent motive `Id^l(A; lhs(z); rhs(z))` whose *type* `A` does not
    /// mention `z` still relates the two children vectors pointwise, which is
    /// what `vec::tab_cong` turns into an equation between them.
    eq: Option<EqSplit>,
    /// The ih's own Π type, so a call site annotates its application with the
    /// codomain the eliminator actually gave rather than rebuilding it — the
    /// rebuild is only correct for a strengthened motive, and phase 3's is not.
    ih_ty: Type,
    /// `⟦D⟧`, the container's element type, for `nth` at the call site.
    elem: Type,
    /// `l`: the declaration's level, which is `⟦D⟧`'s. Not `mlvl`, which is the
    /// motive's — `nth` and the endpoint applications need this one.
    level: Level,
    mlvl: Level,
}

/// A dependent motive that is an equation, split into its two endpoints
/// (`docs/container-proofs.md` §5).
#[derive(Clone)]
struct EqSplit {
    /// The level `Id^l` is at, which is `A`'s.
    level: Level,
    /// `A`, the type the equation is at — strengthened, so it may not mention
    /// the scrutinee. A heterogeneous motive is out of scope and diagnosed
    /// (`issues/dependent-field-injectivity.md` holds the transport question).
    ty: Type,
    /// `λ(z : ⟦D⟧). lhs` and `λ(z : ⟦D⟧). rhs`. Kept as *functions* rather than
    /// as open terms so that a call site can shift them like any other term and
    /// apply them to a child; the β-redex this leaves is what conversion is for.
    lhs: Rc<Term>,
    rhs: Rc<Term>,
}
