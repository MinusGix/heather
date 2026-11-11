//! `rewrite(h, e)` along a relation: setoid rewriting, built bottom-up
//! (`docs/equation-rewrite-design.md` §9, `issues/rewrite-setoid-relations.md`).
//!
//! `h : R(a, b)` for a homogeneous relation `R` other than `=`. Each node of
//! the goal is rewritten once, children first: an occurrence of `a` becomes
//! `b` with `h` as its proof, an application whose arguments changed gets one
//! congruence step (`Respects2` over its last two arguments,
//! `PreservesRelation` over one), and an unchanged node gets nothing. Results
//! are kept per node, so a goal that shares a subterm rewrites it once and the
//! proof shares that node's step: the work and the term are linear in the goal
//! as a DAG, not as a tree (mengine's rewriter, `docs/mengine-survey.md` §4.3).
//!
//! The goal is a relation application `S(l, r)`, or an implication between
//! goals. A side's step composes with `S` by `Transitive` (or `Trans` when
//! `S` is not `R`); the right side's, which runs the other way, through
//! `Symmetric` evidence for `R`. An implication's premise is rewritten the
//! other way round from its conclusion, so the walk carries a polarity.
//!
//! Below a λ the body is rewritten one binder down and the two λs are related
//! pointwise, `Pointwise(R)`; the λ's consumer crosses that by
//! `PreservesRelation(Pointwise(R), R, …)` evidence, as `∑` does by
//! `MonoidRel::range_pointwise` (§10). A codata constructor is a node whose
//! arguments are its children, crossed by evidence about `λ z. C(…, z, …)`
//! (§11.5).
//!
//! The proof is kernel terms (`app@` spines over the evidence), not source
//! text, and nothing in it is trusted: the declaration gate checks it.
//! Evidence that resolution does not find is an obligation, as `rel_cong`
//! leaves it, discharged by `on ?label := …`.

use std::collections::HashMap;
use heather_kernel::rc::Rc;
use std::sync::Arc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::{Expr, Item, Span, parse_file};

use super::{CANDIDATES, MAX_OPEN, same_key};
use crate::relational_context::proof::Relation;
use crate::{Alias, Cx, ElabError, Elaborator, R, TyVar};
use crate::relational_context::proof::RelationalProof;
use crate::rewrite::Rewrites;

/// Relational rewriting's part of the elaborator.
pub(crate) struct Relations<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Relations<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Relations<'_> {
    /// The relation step `proof` gives, when its type, as written below a Π
    /// telescope, is a relation application `R(a, b)`; `None` leaves the
    /// proof to the equation form, which reads its type up to weak head
    /// normal form. A telescope is instantiated as the equation form's is
    /// (§6.1): the first node of `goal` that matches the left side fixes the
    /// arguments.
    pub(super) fn relation_step<'a>(
        &'a self,
        cx: &'a Cx,
        h: &Expr,
        proof: &Term,
        proof_ty: &Type,
        goal: &Type,
        what: &str,
    ) -> R<Option<RelationRewrite<'a>>> {
        self.relation_step_or(cx, h, proof, proof_ty, goal, None)
            .map_err(|miss| miss.into_error(self.0, cx, goal, what, "relation", h.span))
    }

    /// [`Self::relation_step`] with its misses told apart and `premise`
    /// asked for a side condition, as [`Rewrites::rewrite_instance_or`].
    pub(super) fn relation_step_or<'a>(
        &'a self,
        cx: &'a Cx,
        h: &Expr,
        proof: &Term,
        proof_ty: &Type,
        goal: &Type,
        premise: Option<super::Premise<'_>>,
    ) -> Result<Option<RelationRewrite<'a>>, super::Miss> {
        let mut pcx = cx.clone();
        let mut k = 0u32;
        let mut telescope = Vec::new();
        let mut cur = proof_ty.clone();
        let pattern = loop {
            let unfolded = self.whnf(&pcx, &cur, h.span)?;
            if let Some(rel) = Relation::of_type(self, &pcx, &cur, h.span) {
                // A relation that unfolds to equality of its own two sides
                // (`RelId(a, b)`, `Steps(R, 0, a, b)`) is that equality, and
                // rewrites as one: one transport, no evidence.
                if matches!(&unfolded, Type::Id { lhs, rhs, .. } if *lhs == rel.left && *rhs == rel.right) {
                    return Ok(None);
                }
                break rel;
            }
            match unfolded {
                Type::Pi { dom_level, dom, cod, .. } if k < MAX_OPEN => {
                    telescope.push(((*dom).clone(), dom_level.clone()));
                    pcx.push(format!("_{k}"), (*dom).clone(), dom_level);
                    k += 1;
                    cur = (*cod).clone();
                }
                _ => return Ok(None),
            }
        };
        let holds = match &cur {
            Type::El { level, .. } => level.clone(),
            Type::M { sig, .. } => sig.family_level(),
            _ => unreachable!("a relation is an `El` or a family"),
        };
        if k == 0 {
            return Ok(RelationRewrite::new(self, cx, h.span, pattern, proof.clone(), 0, holds).map(Some)?);
        }
        if matches!(&*pattern.left, Term::Var(x) if x.0 < k) {
            return Err(ElabError::Elab {
                msg: "`rewrite`: this relation's left side is one of its own arguments, so it \
                      would match every subterm; apply it to that argument"
                    .into(),
                span: h.span,
            }
            .into());
        }
        // The first node the walk meets that matches fixes the arguments, at
        // whatever depth below the goal's binders it sits (§10.3): the
        // pattern's own context is shifted past them, and the match is asked
        // in the binders' context.
        let nodes = GoalNodes::of(self, cx, goal);
        let mut shifted: Vec<Option<Rc<Term>>> = Vec::new();
        let mut found = None;
        let mut candidates = 0;
        for (t, scope) in &nodes.terms {
            let d = nodes.depth(*scope);
            if shifted.len() <= d as usize {
                shifted.resize(d as usize + 1, None);
            }
            let left = shifted[d as usize]
                .get_or_insert_with(|| Rc::new(pattern.left.shift_local_above(d, k)))
                .clone();
            if !same_key(&left, t, k) {
                continue;
            }
            candidates += 1;
            if candidates > CANDIDATES {
                break;
            }
            let here = nodes.context(cx, *scope);
            let mut binds = vec![None; k as usize];
            let at_depth: Vec<_> =
                telescope.iter().enumerate().map(|(j, (dom, level))| (dom.shift_local_above(d, j as u32), level.clone())).collect();
            if Rewrites(self).match_pattern(&here, &left, t, k, &mut binds, &at_depth, h.span) {
                found = Some((binds, here, d));
                break;
            }
        }
        let Some((binds, here, depth)) = found else {
            return Err(super::Miss::NoInstance);
        };
        // Binder `j` (outermost first) is `Var(k - 1 - j)` in `pcx`.
        let mut term = Rc::new(proof.shift_local(depth));
        let mut ty_now = proof_ty.shift_local(depth);
        for j in 0..k {
            let Type::Pi { dom_level, dom, cod, .. } = self.whnf(&here, &ty_now, h.span)? else {
                unreachable!("opened as a Π above")
            };
            let arg = match binds[(k - 1 - j) as usize].clone() {
                Some(arg) => arg,
                None => {
                    let side = crate::strengthen_ty(&here.gamma, &cod, 1).is_some();
                    // A side condition is discharged in the goal's own
                    // context: below a binder the proof would have to be
                    // found there, which is not attempted.
                    match premise.filter(|_| side && depth == 0).and_then(|p| p(&here, &dom, &dom_level)) {
                        Some(found) => Rc::new(found),
                        None => {
                            return Err(super::Miss::Unbound {
                                index: j + 1,
                                premise: (side && depth == 0).then(|| ((*dom).clone(), dom_level.clone())),
                            });
                        }
                    }
                }
            };
            ty_now = cod.inst_top(0, &arg);
            term = apply(term, [arg]);
        }
        let instance = Relation::of_type(self, &here, &ty_now, h.span).expect("instantiated from a relation");
        // The instance is kept relative to the innermost binders it mentions
        // (§10.3): `x(n) + 0` found under `λ n` is that sum under whichever
        // binder the walk is below, not one fixed `n`.
        let base = (0..=depth)
            .find(|&b| {
                [&instance.left, &instance.right, &term].iter().all(|t| relocated(t, b, depth).is_some())
            })
            .expect("every term is scoped at its own depth");
        let to_root = |t: &Term| crate::strengthen_tm(&cx.gamma, t, depth);
        let (Some(head), Some(carrier)) =
            (to_root(&instance.head), crate::strengthen_ty(&cx.gamma, &instance.carrier, depth))
        else {
            return Err(ElabError::Elab {
                msg: "`rewrite`: this instance's relation mentions a variable bound in the goal; \
                      a relation rewrite rewrites along one relation throughout"
                    .into(),
                span: h.span,
            }
            .into());
        };
        let at_base = |t: &Term| Rc::new(relocated(t, base, depth).expect("checked above"));
        let relation = Relation {
            head: Rc::new(head),
            left: at_base(&instance.left),
            right: at_base(&instance.right),
            carrier: Rc::new(carrier),
            level: instance.level,
        };
        let proof = Rc::unwrap_or_clone(at_base(&term));
        Ok(RelationRewrite::new(self, cx, h.span, relation, proof, base, holds).map(Some)?)
    }
}

/// `t`, scoped `depth` binders below the goal's context, with the binders
/// between its innermost `base` and that context dropped: scoped `base`
/// binders below it. `None` when `t` mentions one of the dropped binders.
fn relocated(t: &Term, base: u32, depth: u32) -> Option<Term> {
    let mut cur = t.clone();
    for _ in base..depth {
        let dropped = cur.inst_top_above(0, base, &Term::Zero);
        if dropped.shift_local_above(1, base) != cur {
            return None;
        }
        cur = dropped;
    }
    Some(cur)
}

/// The terms of a goal the relation walk can reach — relation sides, a
/// non-dependent implication's two halves, application arguments below them,
/// and λ bodies — each once per binder scope, in the order the walk first
/// meets them. A scope is a λ the walk enters: its parent scope, and its
/// binder's type and level.
struct GoalNodes {
    terms: Vec<(Rc<Term>, usize)>,
    scopes: Vec<(usize, Rc<Type>, Level)>,
}

impl GoalNodes {
    fn of(e: &Elaborator, cx: &Cx, goal: &Type) -> GoalNodes {
        let mut nodes = GoalNodes { terms: Vec::new(), scopes: Vec::new() };
        let mut seen = std::collections::HashSet::new();
        nodes.types(e, cx, goal, &mut seen);
        nodes
    }

    fn types(&mut self, e: &Elaborator, cx: &Cx, ty: &Type, seen: &mut std::collections::HashSet<(*const Term, usize)>) {
        match ty {
            Type::El { tm, .. } => self.walk(e, cx, tm, 0, seen),
            Type::M { .. } => {
                if let Some(rel) = Relation::of_family(ty) {
                    self.walk(e, cx, &rel.left, 0, seen);
                    self.walk(e, cx, &rel.right, 0, seen);
                }
            }
            Type::Pi { dom, cod, .. } => {
                self.types(e, cx, dom, seen);
                if let Some(cod) = crate::strengthen_ty(&cx.gamma, cod, 1) {
                    self.types(e, cx, &cod, seen);
                }
            }
            _ => {}
        }
    }

    fn walk(&mut self, e: &Elaborator, cx: &Cx, t: &Rc<Term>, scope: usize, seen: &mut std::collections::HashSet<(*const Term, usize)>) {
        if !seen.insert((Rc::as_ptr(t), scope)) {
            return;
        }
        self.terms.push((Rc::clone(t), scope));
        if let Term::Lam { dom_level, dom, body, .. } = &**t {
            self.scopes.push((scope, Rc::clone(dom), dom_level.clone()));
            let inner = self.scopes.len();
            self.walk(e, cx, body, inner, seen);
            return;
        }
        // A constructor's children, as written (§11.5).
        if let Some(node) = crate::codata::CtorNode::read(t) {
            for child in &node.children {
                self.walk(e, cx, &child.term, scope, seen);
            }
            return;
        }
        // An inductive constructor's value is not an application: its
        // fields are read off the lowered value, as the walk reads them.
        if let Some((_, _, fields)) = e.view_ctor(cx, t) {
            for f in &fields {
                self.walk(e, cx, f, scope, seen);
            }
            return;
        }
        let (head, args) = crate::spelling::app_spine(t);
        if !matches!(head, Term::Lam { .. }) {
            for a in args {
                self.walk(e, cx, a, scope, seen);
            }
        }
    }

    /// How many binders `scope` is below the goal's context.
    fn depth(&self, mut scope: usize) -> u32 {
        let mut d = 0;
        while scope != 0 {
            scope = self.scopes[scope - 1].0;
            d += 1;
        }
        d
    }

    /// `cx` extended by `scope`'s binders, outermost first.
    fn context(&self, cx: &Cx, scope: usize) -> Cx {
        let mut chain = Vec::new();
        let mut at = scope;
        while at != 0 {
            chain.push(at - 1);
            at = self.scopes[at - 1].0;
        }
        let mut here = cx.clone();
        for (i, s) in chain.into_iter().rev().enumerate() {
            let (_, dom, level) = &self.scopes[s];
            here.push(format!("__bound_{i}"), (**dom).clone(), level.clone());
        }
        here
    }
}

/// Which way a goal is rewritten: a goal to prove is reached *from* its
/// rewritten form, a hypothesis is carried *to* it.
#[derive(Clone, Copy)]
pub(super) enum Polarity {
    /// `G' → G`: the goal form.
    Backward,
    /// `G → G'`: the hypothesis form, and an implication's premise.
    Forward,
}

impl Polarity {
    fn flipped(self) -> Polarity {
        match self {
            Polarity::Backward => Polarity::Forward,
            Polarity::Forward => Polarity::Backward,
        }
    }
}

/// A term after the walk: unchanged, or rewritten to `term` with `proof`
/// relating the two. `over` is empty for `proof : R(original, term)`; for a
/// λ it lists the binders' types and levels, outermost first, and the proof
/// is of `Pointwise(…Pointwise(R))(original, term)`, one `Pointwise` per
/// binder (§10.1).
#[derive(Clone)]
enum Node {
    Same,
    /// `rel` is the relation `proof` relates by when it is not the
    /// rewrite's own: a context that leaves the carrier relates its result
    /// by whatever its evidence names (§11.4).
    Changed { term: Rc<Term>, proof: Rc<Term>, over: Domains, rel: Option<Rc<Rel>> },
}

/// A relation a node changed by other than the rewrite's own `R`, with its
/// carrier, both scoped in the rewrite's context, and the level of an
/// application `rel(x, y)`. `identity` when it is `RelId` at its carrier (up
/// to conversion): every context preserves it, and a chain meets it as an
/// `=` step (§11.6).
#[derive(PartialEq, Eq)]
pub(super) struct Rel {
    head: Rc<Term>,
    carrier: Rc<Type>,
    level: Level,
    holds: Level,
    identity: bool,
}

/// The binders' types and levels a pointwise relation ranges over,
/// outermost first, each scoped where the λ they bind sits.
type Domains = Arc<[(Rc<Type>, Level)]>;

impl Node {
    fn changed(&self) -> bool {
        matches!(self, Node::Changed { .. })
    }

    /// A change related by `R` itself.
    fn related(term: Rc<Term>, proof: Rc<Term>) -> Node {
        Node::Changed { term, proof, over: Arc::from([]), rel: None }
    }

    /// A change related by `rel`, `None` for `R` itself.
    fn related_by(term: Rc<Term>, proof: Rc<Term>, rel: Option<Rc<Rel>>) -> Node {
        Node::Changed { term, proof, over: Arc::from([]), rel }
    }

    /// The relation the change is by, `None` for `R` itself.
    fn rel(&self) -> Option<&Rc<Rel>> {
        match self {
            Node::Changed { rel, .. } => rel.as_ref(),
            Node::Same => None,
        }
    }

    /// A λ that changed: related pointwise.
    fn pointwise(&self) -> bool {
        matches!(self, Node::Changed { over, .. } if !over.is_empty())
    }
}

/// How a goal's rewritten form is reached from it, built once and emitted at
/// whatever binder depth and polarity its context needs.
pub(super) enum Plan {
    Same,
    /// `S(l, r)`, each side with its step when it changed.
    Relation { relation: Rc<Term>, carrier: Rc<Type>, level: Level, left: Side, right: Side },
    /// `P → Q`: `from` and `to` are the implication before and after.
    Arrow { from: Type, to: Type, premise: Box<Plan>, conclusion: Box<Plan> },
}

pub(super) struct Side {
    from: Rc<Term>,
    to: Rc<Term>,
    /// `R(from, to)`; `None` when the side did not change.
    proof: Option<Rc<Term>>,
    /// The relation `proof` is by, when not `R`.
    rel: Option<Rc<Rel>>,
}

/// The congruence a node asks for: over its last argument, or its last two,
/// or over a λ argument, which changed pointwise.
#[derive(Clone, PartialEq)]
enum Shape {
    Unary,
    Binary,
    Pointwise(Domains),
}

impl Shape {
    /// The shape with its domains scoped `d` binders further out, when they
    /// mention none of those binders.
    fn strengthened(&self, gamma: &heather_kernel::term::LocalCtx, d: u32) -> Option<Shape> {
        let Shape::Pointwise(over) = self else { return Some(self.clone()) };
        let lowered = over
            .iter()
            .map(|(dom, level)| crate::strengthen_ty(gamma, dom, d).map(|t| (Rc::new(t), level.clone())))
            .collect::<Option<Vec<_>>>()?;
        Some(Shape::Pointwise(lowered.into()))
    }
}

/// What resolution says about one context's congruence.
#[derive(Clone)]
enum Lookup {
    /// The context does not map the carrier to itself: no evidence of this
    /// shape can be stated.
    Untyped,
    /// Evidence, ready to apply to `x, x', h` (twice, for `Binary`), and
    /// the relation the result changes by when it is not `R`.
    Found(Rc<Term>, Option<Rc<Rel>>),
    /// The statement, which resolution did not prove, and the relation it
    /// names for the result.
    Missing(Type, Level, Option<Rc<Rel>>),
}

impl Lookup {
    /// The same answer `d` binders further in.
    fn shifted(self, d: u32) -> Lookup {
        match self {
            Lookup::Untyped => Lookup::Untyped,
            Lookup::Found(ev, rel) => Lookup::Found(Rc::new(ev.shift_local(d)), rel),
            Lookup::Missing(ty, level, rel) => Lookup::Missing(ty.shift_local(d), level, rel),
        }
    }
}

/// A context asked about: its shape, the relation its argument changes by,
/// the context, and whether its result was asked at another carrier.
type ContextKey = (Shape, Option<Rc<Rel>>, Rc<Term>, bool);

/// A λ the walk is below.
struct Binder {
    /// The rewrite's context extended by every binder down to this one.
    here: Cx,
    dom: Rc<Type>,
    level: Level,
    /// The node memo's scope for terms below it: a λ's body is rewritten in
    /// its own binder's context, once per λ node.
    scope: usize,
}

/// One rewrite step along `h : R(a, b)`.
pub(super) struct RelationRewrite<'a> {
    e: &'a Elaborator,
    /// The context the rewrite was asked in: obligations are its goals.
    original: &'a Cx,
    /// `original` with the carrier as a type variable and every term an
    /// evidence statement mentions as an alias, so statements are written as
    /// text.
    cx: Cx,
    span: Span,
    relation: Rc<Term>,
    carrier: Rc<Type>,
    level: Level,
    carrier_name: String,
    lhs: Rc<Term>,
    rhs: Rc<Term>,
    proof: Rc<Term>,
    /// `lhs`, `rhs` and `proof` are scoped `base` binders below `original`,
    /// the innermost ones the walk is below (an instance found under a
    /// binder that mentions it, §10.3); 0 for every other step.
    base: u32,
    /// The level of a relation application `R(x, y)`: of `proof`'s type.
    holds: Level,
    /// Keyed conversion is asked only of a left side headed by a global or a
    /// local variable, as in the equation form (§6.2), and at most
    /// [`CANDIDATES`] times.
    keyed: bool,
    conversions: usize,
    occurrences: usize,
    /// Every node met, by identity and binder scope, with the node kept
    /// alive so the address is not reused.
    memo: HashMap<(*const Term, usize), (Rc<Term>, Node)>,
    /// The λs the walk is below, outermost first.
    binders: Vec<Binder>,
    scopes: usize,
    /// `lhs`, `rhs` and `proof` at each depth from `base` down, each shifted
    /// once.
    at_depth: Vec<(Rc<Term>, Rc<Term>, Rc<Term>)>,
    /// While evidence is stated below binders a context mentions: `cx` is
    /// extended by them, and a missing statement is refused, not raised.
    deep: bool,
    contexts: Vec<(ContextKey, Lookup)>,
    /// `Reflexive<C>(R)`'s `rel_refl`, once looked for.
    reflexive: Option<Option<Rc<Term>>>,
    /// Relation terms and the aliases that spell them.
    relations: Vec<(Rc<Term>, String)>,
    /// Binder types and the type variables that spell them.
    domains: Vec<(Rc<Type>, String)>,
    /// Goal-level class fields, by class, relations and field.
    fields: Vec<(&'static str, Vec<Rc<Term>>, Rc<Term>)>,
    serial: usize,
    goals: usize,
    /// `Some` when missing evidence is refused rather than raised as a goal
    /// (a simplifier's step either fires whole or not at all): the
    /// statements that were missing.
    pub(super) refused: Option<Vec<String>>,
}

impl<'a> RelationRewrite<'a> {
    /// The step along `proof : R(lhs, rhs)`, or an error when `R` is not a
    /// relation on one carrier. `relation`'s sides and `proof` are scoped
    /// `base` binders below `cx`; its relation and carrier in `cx`.
    pub(super) fn new(
        e: &'a Elaborator,
        cx: &'a Cx,
        span: Span,
        relation: Relation,
        proof: Term,
        base: u32,
        holds: Level,
    ) -> R<Self> {
        let keyed = super::keyable_head(crate::spelling::app_spine(&relation.left).0);
        let mut rw = RelationRewrite {
            e,
            original: cx,
            cx: cx.clone(),
            span,
            relation: relation.head,
            carrier: relation.carrier,
            level: relation.level,
            carrier_name: String::new(),
            lhs: relation.left,
            rhs: relation.right,
            proof: Rc::new(proof),
            base,
            holds,
            keyed,
            conversions: 0,
            occurrences: 0,
            memo: HashMap::new(),
            binders: Vec::new(),
            scopes: 0,
            at_depth: Vec::new(),
            deep: false,
            contexts: Vec::new(),
            reflexive: None,
            relations: Vec::new(),
            domains: Vec::new(),
            fields: Vec::new(),
            serial: 0,
            goals: 0,
            refused: None,
        };
        rw.carrier_name = rw.fresh();
        rw.cx.tyvars.push(TyVar {
            name: rw.carrier_name.clone(),
            ty: (*rw.carrier).clone(),
            level: rw.level.clone(),
            depth: cx.names.len(),
        });
        let relation = Rc::clone(&rw.relation);
        rw.relation_alias(&relation)?;
        Ok(rw)
    }

    /// After [`Self::goal`]: an error unless the walk rewrote something, with
    /// the equation form's hint when the goal holds the right side instead.
    /// `R(x, x)` by the relation's `Reflexive` evidence.
    pub(super) fn reflexive_at(&mut self, x: &Rc<Term>) -> R<Rc<Term>> {
        self.reflexivity(x)
    }

    /// How many nodes the walk rewrote.
    pub(super) fn occurrences(&self) -> usize {
        self.occurrences
    }

    /// The step's two sides, where they are scoped in the rewrite's own
    /// context.
    pub(super) fn sides(&self) -> Option<(Rc<Term>, Rc<Term>)> {
        (self.base == 0).then(|| (Rc::clone(&self.lhs), Rc::clone(&self.rhs)))
    }

    pub(super) fn require_occurrence(&self, goal: &Type, what: &str) -> R<()> {
        if self.occurrences > 0 {
            return Ok(());
        }
        let hint = if self.base == 0 && goal.abstract_local(&self.rhs).is_some() {
            format!(
                "\n  hint: {what} mentions its right side{}; to rewrite right to left, give \
                 the relation's symmetry the proof (`Symmetric`'s `rel_sym`)",
                self.shown(&self.rhs)
            )
        } else {
            String::new()
        };
        Err(ElabError::Elab {
            msg: format!(
                "`rewrite`: {what} `{}` does not mention the relation's left side{}\n  \
                 note: an occurrence is a subterm with the left side's head that converts to \
                 it, as written{hint}",
                self.e.display_type(self.original, goal),
                // An instance found below a binder is scoped there.
                if self.base == 0 { self.shown(&self.lhs) } else { String::new() }
            ),
            span: self.span,
        })
    }

    // ---------------------------------------------------------------------
    // The goal

    /// `goal` with every occurrence of the left side rewritten, and the plan
    /// that connects the two. `what` names the goal in errors.
    pub(super) fn goal(&mut self, goal: &Type, what: &str) -> R<(Type, Plan)> {
        if let Some(rel) = Relation::of_type(self.e, self.original, goal, self.span) {
            let left = self.term(&rel.left)?;
            let right = self.term(&rel.right)?;
            if !left.changed() && !right.changed() {
                return Ok((goal.clone(), Plan::Same));
            }
            if let Some(side) = [(&left, &rel.left), (&right, &rel.right)].into_iter().find(|(n, _)| n.pointwise()) {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite`: the side{} of {what} is a λ, which the rewrite relates \
                         pointwise, not by the goal's relation",
                        self.shown(side.1)
                    ),
                    span: self.span,
                });
            }
            let to = |node: &Node, from: &Rc<Term>| match node {
                Node::Changed { term, .. } => Rc::clone(term),
                Node::Same => Rc::clone(from),
            };
            let next = Relation::with_sides(goal, to(&left, &rel.left), to(&right, &rel.right))
                .expect("a relation application has two sides");
            let side = |from: Rc<Term>, node: Node| match node {
                Node::Same => Side { to: Rc::clone(&from), from, proof: None, rel: None },
                Node::Changed { term, proof, rel, .. } => Side { from, to: term, proof: Some(proof), rel },
            };
            let plan = Plan::Relation {
                relation: rel.head,
                carrier: rel.carrier,
                level: rel.level,
                left: side(rel.left, left),
                right: side(rel.right, right),
            };
            return Ok((next, plan));
        }
        if let Type::Pi { dom_level, cod_level, dom, cod } = goal
            && let Some(conclusion) = crate::strengthen_ty(&self.original.gamma, cod, 1)
        {
            let (dom2, premise) = self.goal(dom, what)?;
            let (cod2, conclusion) = self.goal(&conclusion, what)?;
            if matches!((&premise, &conclusion), (Plan::Same, Plan::Same)) {
                return Ok((goal.clone(), Plan::Same));
            }
            let to = Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(dom2),
                cod: Rc::new(cod2.shift_local(1)),
            };
            let plan = Plan::Arrow {
                from: goal.clone(),
                to: to.clone(),
                premise: Box::new(premise),
                conclusion: Box::new(conclusion),
            };
            return Ok((to, plan));
        }
        if self.base == 0 && goal.abstract_local(&self.lhs).is_some() {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: {what} `{}` mentions the left side{}, but is not a relation \
                     application `S(l, r)` or an implication between such goals, so nothing \
                     says how it respects the relation{}",
                    self.e.display_type(self.original, goal),
                    self.shown(&self.lhs),
                    self.shown(&self.relation),
                ),
                span: self.span,
            });
        }
        Ok((goal.clone(), Plan::Same))
    }

    /// The proof `plan` describes, at `polarity`, from `input` — scoped
    /// `depth` binders below the goal's context, where every term the plan
    /// holds is shifted to.
    pub(super) fn emit(&mut self, plan: &Plan, polarity: Polarity, input: Rc<Term>, depth: u32) -> R<Rc<Term>> {
        let up = |t: &Rc<Term>| if depth == 0 { Rc::clone(t) } else { Rc::new(t.shift_local(depth)) };
        match plan {
            Plan::Same => Ok(input),
            Plan::Relation { relation, carrier, level, left, right } => {
                // Each side's relation: `R`, or what a context that left
                // `R`'s carrier named, at the goal's carrier either way.
                let by = |side: &Side| {
                    side.rel.as_ref().map_or_else(|| (Rc::clone(&self.relation), false), |r| (Rc::clone(&r.head), r.identity))
                };
                let ((rl, il), (rr, ir)) = (by(left), by(right));
                let at = (carrier, level);
                let mut acc = input;
                match polarity {
                    // From `S(l', r')`: `R(r, r')` turned round closes the
                    // right side, then `R(l, l')` the left.
                    Polarity::Backward => {
                        if let Some(pr) = &right.proof {
                            let back = self.symmetric(pr, &right.from, &right.to, &rr, ir, at)?;
                            let chain = self.chain((relation, false), (&rr, ir), relation, at)?;
                            acc = apply(up(&chain), [up(&left.to), up(&right.to), up(&right.from), acc, up(&back)]);
                        }
                        if let Some(pl) = &left.proof {
                            let chain = self.chain((&rl, il), (relation, false), relation, at)?;
                            acc = apply(up(&chain), [up(&left.from), up(&left.to), up(&right.from), up(pl), acc]);
                        }
                    }
                    // From `S(l, r)`: `R(l, l')` turned round opens the left
                    // side, then `R(r, r')` the right.
                    Polarity::Forward => {
                        if let Some(pl) = &left.proof {
                            let back = self.symmetric(pl, &left.from, &left.to, &rl, il, at)?;
                            let chain = self.chain((&rl, il), (relation, false), relation, at)?;
                            acc = apply(up(&chain), [up(&left.to), up(&left.from), up(&right.from), up(&back), acc]);
                        }
                        if let Some(pr) = &right.proof {
                            let chain = self.chain((relation, false), (&rr, ir), relation, at)?;
                            acc = apply(up(&chain), [up(&left.to), up(&right.from), up(&right.to), acc, up(pr)]);
                        }
                    }
                }
                Ok(acc)
            }
            // `λ (p : P). Q-step(input(P-step(p)))`, the premise's step the
            // other way round: a proof of the implication takes the premise
            // it was given to the one the input expects.
            Plan::Arrow { from, to, premise, conclusion } => {
                let (outer, inner) = match polarity {
                    Polarity::Backward => (from, to),
                    Polarity::Forward => (to, from),
                };
                let Type::Pi { dom_level, cod_level, dom, .. } = outer.shift_local(depth) else {
                    unreachable!("an arrow plan is between `Π`s")
                };
                let Type::Pi { dom_level: il, cod_level: ic, dom: idom, cod: icod } = inner.shift_local(depth + 1) else {
                    unreachable!("an arrow plan is between `Π`s")
                };
                let var = Rc::new(Term::Var(LocalVar(0)));
                let arg = self.emit(premise, polarity.flipped(), var, depth + 1)?;
                let fun = Rc::new(input.shift_local(1));
                let applied = Rc::new(crate::spelling::checked_app(fun, il, ic, idom, icod, arg));
                let body = self.emit(conclusion, polarity, applied, depth + 1)?;
                Ok(Rc::new(Term::Lam { dom_level, cod_level, dom, body }))
            }
        }
    }

    // ---------------------------------------------------------------------
    // Terms

    /// How many binders the walk is below.
    fn depth(&self) -> u32 {
        self.binders.len() as u32
    }

    /// The context at the walk's depth: the rewrite's, extended by the
    /// binders it is below.
    fn here(&self) -> &Cx {
        self.binders.last().map_or(self.original, |b| &b.here)
    }

    /// The left side, the right side and the step's proof at the walk's
    /// depth, shifted once per depth; `None` above the binders an instance
    /// found below them mentions.
    fn pattern(&mut self) -> Option<(Rc<Term>, Rc<Term>, Rc<Term>)> {
        let d = self.depth().checked_sub(self.base)? as usize;
        while self.at_depth.len() <= d {
            let by = self.at_depth.len() as u32;
            let base = self.base;
            let up = |t: &Rc<Term>| if by == 0 { Rc::clone(t) } else { Rc::new(t.shift_local_above(by, base)) };
            let shifted = (up(&self.lhs), up(&self.rhs), up(&self.proof));
            self.at_depth.push(shifted);
        }
        Some(self.at_depth[d].clone())
    }

    /// `t` rewritten, once per node and binder scope.
    fn term(&mut self, t: &Rc<Term>) -> R<Node> {
        let key = (Rc::as_ptr(t), self.binders.last().map_or(0, |b| b.scope));
        if let Some((_, node)) = self.memo.get(&key) {
            return Ok(node.clone());
        }
        let node = self.node(t)?;
        self.memo.insert(key, (Rc::clone(t), node.clone()));
        Ok(node)
    }

    fn node(&mut self, t: &Rc<Term>) -> R<Node> {
        if let Some((lhs, rhs, proof)) = self.pattern()
            && self.is_occurrence(t, &lhs)
        {
            self.occurrences += 1;
            return Ok(Node::related(rhs, proof));
        }
        if let Term::Lam { dom_level, cod_level, dom, body } = &**t {
            return self.lambda(t, dom_level, cod_level, dom, body);
        }
        if let Some(node) = crate::codata::CtorNode::read(t) {
            return self.constructor(t, node);
        }
        if let Some((ind, i, fields)) = self.e.view_ctor(self.here(), t)
            && !fields.is_empty()
        {
            return self.inductive(t, &ind, i, &fields);
        }
        let (head, args) = crate::spelling::app_spine(t);
        if args.is_empty() || matches!(head, Term::Lam { .. }) {
            return self.opaque(t);
        }
        let nodes = args.iter().map(|a| self.term(a)).collect::<R<Vec<_>>>()?;
        if !nodes.iter().any(Node::changed) {
            return Ok(Node::Same);
        }
        self.congruence(t, &args, &nodes)
    }

    /// Is `t` the left side `lhs`: itself, or a term with its global head
    /// whose arguments convert to its arguments, one by one? Argument-wise,
    /// not the whole term: the head is the same operation on both sides, so a
    /// miss would otherwise unfold it on both (rational arithmetic, say) only
    /// to compare the parts that differ — Lean's keyed matching likewise
    /// unfolds no head. A respelled argument (an implicit width) still
    /// matches.
    fn is_occurrence(&mut self, t: &Rc<Term>, lhs: &Rc<Term>) -> bool {
        if Rc::ptr_eq(t, lhs) {
            return true;
        }
        if !same_key(lhs, t, 0) {
            return false;
        }
        if **t == **lhs {
            return true;
        }
        if !self.keyed || self.conversions >= CANDIDATES {
            return false;
        }
        self.conversions += 1;
        let (lhs_head, lhs_args) = crate::spelling::app_spine(lhs);
        let (head, args) = crate::spelling::app_spine(t);
        head == lhs_head
            && args.iter().zip(&lhs_args).all(|(a, b)| a == b || Rewrites(self.e).terms_convert(self.here(), b, a))
    }

    /// A value of an inductive's constructor: its fields are rewritten, and
    /// the constructor is crossed as the function it is, `T::C(x, y)`, by
    /// the evidence registered at that name (`Respects2<…>(R, R, R, T::C)`,
    /// `PreservesRelation(R, R, T::C)`), which is what `rel_cong` reads
    /// there (§10.7). A lowered constructor value is not an application, so
    /// the congruence is stated over the call and the result read back as a
    /// value.
    fn inductive(&mut self, t: &Rc<Term>, ind: &crate::inductive::Inductive, i: usize, fields: &[Rc<Term>]) -> R<Node> {
        let nodes = fields.iter().map(|f| self.term(f)).collect::<R<Vec<_>>>()?;
        if !nodes.iter().any(Node::changed) {
            return self.opaque(t);
        }
        let name = format!("{}::{}", ind.name, ind.ctors[i].name);
        let Some(op) = self.constructor_function(&name, t, fields) else {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: a field of the constructor value{} changes, and `{name}` does \
                     not name its constructor as a function of those fields here, so no \
                     evidence can be stated for it",
                    self.shown(t)
                ),
                span: self.span,
            });
        };
        let d = self.depth();
        let op = Rc::new(op.shift_local(d));
        let after = fields.iter().zip(&nodes).map(|(f, node)| match node {
            Node::Changed { term, .. } => Rc::clone(term),
            Node::Same => Rc::clone(f),
        });
        let term = apply(Rc::clone(&op), after);
        let own = nodes.iter().all(|n| !n.changed() || (n.rel().is_none() && !n.pointwise()));
        let shape = match (fields.len(), own) {
            (1, true) => Shape::Unary,
            (2, true) => Shape::Binary,
            _ => {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite`: a field of the constructor value{} changes; a relation \
                         rewrite crosses a constructor of one field (`PreservesRelation`) or \
                         of two (`Respects2`), each changed by the rewrite's own relation",
                        self.shown(t)
                    ),
                    span: self.span,
                });
            }
        };
        if matches!(self.lookup_here(&shape, None, &op, None)?, Lookup::Untyped) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: a field of the constructor value{} changes, and `{name}` is \
                     not an operation on the relation's carrier",
                    self.shown(t)
                ),
                span: self.span,
            });
        }
        let (evidence, _) = self.discharge_here(&shape, None, &op, None)?;
        let mut args = Vec::new();
        for (f, node) in fields.iter().zip(&nodes) {
            let (x, x2, hx) = self.side(f, node)?;
            args.extend([x, x2, hx]);
        }
        Ok(Node::related(term, apply(evidence, args)))
    }

    /// The constructor `name` as a function of `fields`, at the rewrite's
    /// own scope: a constructor's name alone has no inferred type (it is a
    /// function only where one is expected), so it is checked against the
    /// arrow from the fields' types to the value's. `None` when a type
    /// mentions a binder the walk is below.
    fn constructor_function(&self, name: &str, t: &Rc<Term>, fields: &[Rc<Term>]) -> Option<Term> {
        let (mut ty, mut level) = self.result_type(t)?;
        for (k, f) in fields.iter().enumerate().rev() {
            let (dom, dom_level) = self.result_type(f)?;
            ty = Rc::new(Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: level.clone(),
                dom: Rc::new(dom.shift_local(k as u32)),
                cod: ty,
            });
            level = Level::max(dom_level, level);
        }
        // Each codomain sits under the binders before it.
        let ty = arrow_shifted(&ty, fields.len() as u32);
        let source = format!("fn generated() -> Type {{ {name} }}");
        let mut file = parse_file(&source).ok()?;
        let Some(Item::Decl(d)) = file.items.pop() else { unreachable!("one declaration") };
        self.e.generated_scope(|e| e.elab_check(&self.cx, &d.body.result, &ty, &level)).ok()
    }

    /// A λ: its body rewritten one binder down, and the two λs related by
    /// the pointwise relation, `λ z. p : Pointwise(R)(λ z. t, λ z. t')` from
    /// `p : R(t, t')` (§10.1).
    fn lambda(&mut self, t: &Rc<Term>, dom_level: &Level, cod_level: &Level, dom: &Rc<Type>, body: &Rc<Term>) -> R<Node> {
        if let Some((lhs, ..)) = self.pattern()
            && dom.abstract_local(&lhs).is_some()
        {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: the left side{} occurs in the type of the binder of{}; a \
                     relation rewrite rewrites terms, not the types they are bound at",
                    self.shown(&lhs),
                    self.shown(t),
                ),
                span: self.span,
            });
        }
        let mut here = self.here().clone();
        here.push(format!("__bound_{}", self.depth()), (**dom).clone(), dom_level.clone());
        self.scopes += 1;
        self.binders.push(Binder { here, dom: Rc::clone(dom), level: dom_level.clone(), scope: self.scopes });
        let inner = self.term(body);
        self.binders.pop();
        let Node::Changed { term, proof, over, rel } = inner? else {
            return Ok(Node::Same);
        };
        // The body's own binders, if it is a λ too, scoped where this λ sits:
        // a pointwise relation does not let one binder's type depend on
        // another's.
        let mut doms = vec![(Rc::clone(dom), dom_level.clone())];
        for (inner_dom, level) in over.iter() {
            let Some(lowered) = crate::strengthen_ty(&self.here().gamma, inner_dom, 1) else {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite`: inside{}, a binder's type depends on the one before it; the \
                         pointwise relation a rewrite crosses binders by is not dependent",
                        self.shown(t),
                    ),
                    span: self.span,
                });
            };
            doms.push((Rc::new(lowered), level.clone()));
        }
        // The level of `p`'s type: `R(t, t')`, or for a λ body the `Π` the
        // pointwise relation unfolds to.
        let base = rel.as_ref().map_or_else(|| self.holds.clone(), |r| r.holds.clone());
        let holds = over.iter().rev().fold(base, |l, (_, dl)| Level::join(dl.clone(), l));
        Ok(Node::Changed {
            term: Rc::new(Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                body: term,
            }),
            proof: Rc::new(Term::Lam { dom_level: dom_level.clone(), cod_level: holds, dom: Rc::clone(dom), body: proof }),
            over: doms.into(),
            rel,
        })
    }

    /// A node the walk does not enter: a former that is no application. An
    /// occurrence inside one would be left behind, and half a rewrite is
    /// worse than none.
    fn opaque(&mut self, t: &Rc<Term>) -> R<Node> {
        let Some((lhs, ..)) = self.pattern() else { return Ok(Node::Same) };
        let probe = Type::El { level: Level::Zero, tm: Rc::clone(t) };
        if probe.abstract_local(&lhs).is_none() {
            return Ok(Node::Same);
        }
        Err(ElabError::Elab {
            msg: format!(
                "`rewrite`: the left side{} occurs inside{}, a form that is no application or \
                 λ; a relation rewrite rewrites through applications and binders only",
                self.shown(&lhs),
                self.shown(t),
            ),
            span: self.span,
        })
    }

    /// One step for an application whose arguments `nodes` changed.
    fn congruence(&mut self, t: &Rc<Term>, args: &[&Rc<Term>], nodes: &[Node]) -> R<Node> {
        let n = args.len();
        let changed: Vec<usize> = (0..n).filter(|&i| nodes[i].changed()).collect();
        let term = rebuild(t, nodes);
        let last = n - 1;
        let pointwise = changed.iter().any(|&i| nodes[i].pointwise());
        // `Respects2` is over `R` alone: an argument a context carried to
        // another relation crosses only unary evidence.
        let own = changed.iter().all(|&i| nodes[i].rel().is_none());
        if n >= 2 && changed[0] >= n - 2 && !pointwise && own {
            let op = prefix(t, 2);
            let binary = self.lookup_here(&Shape::Binary, None, &op, None)?;
            // A binary operation with only its last argument changed may have
            // unary evidence instead; with neither, the obligation is the
            // binary one, as `rel_cong` leaves it.
            let use_binary = match &binary {
                Lookup::Found(..) => true,
                Lookup::Untyped => false,
                Lookup::Missing(..) => {
                    changed != [last]
                        || !matches!(self.lookup_here(&Shape::Unary, None, &prefix(t, 1), None)?, Lookup::Found(..))
                }
            };
            if use_binary {
                let (respects, _) = self.discharge_here(&Shape::Binary, None, &op, None)?;
                let (x, x2, hx) = self.side(args[n - 2], &nodes[n - 2])?;
                let (y, y2, hy) = self.side(args[last], &nodes[last])?;
                return Ok(Node::related(term, apply(respects, [x, x2, hx, y, y2, hy])));
            }
        }
        // The last two arguments changed by other relations than `R`, or
        // into a result outside `R`'s carrier: `Respects2` over the
        // relations each changed by, the result's named as a context's is
        // (§11.6).
        if n >= 2 && changed == [n - 2, last] && !pointwise
            && let Some(node) = self.binary_across(t, args, nodes, &term)?
        {
            return Ok(node);
        }
        let [i] = changed[..] else {
            // Each changed argument's relation, when one is not `R`.
            let by = if own {
                String::new()
            } else {
                let shown: Vec<String> = changed
                    .iter()
                    .map(|&i| {
                        let r = nodes[i].rel().map_or(&self.relation, |r| &r.head);
                        self.e.spell_term_clean(self.original, r).map_or_else(|| "?".into(), |s| format!("`{s}`"))
                    })
                    .collect();
                format!(" (by {})", shown.join(" and "))
            };
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`:{} changes in {} of its arguments{}{by}; a relation rewrite has \
                     congruence over one argument (`PreservesRelation`) or over the last two \
                     (`Respects2`)",
                    self.shown(t),
                    changed.len(),
                    if pointwise { ", a λ among them" } else { "" },
                ),
                span: self.span,
            });
        };
        let partial = (!nodes[i].pointwise() && i == last).then(|| prefix(t, 1));
        self.crossing(t, args[i], &nodes[i], term, partial, &|rw, dom, dom_level, cod_level| {
            rw.context(t, i, dom, dom_level, cod_level)
        })
    }

    /// The step for node `t` whose last two arguments both changed, by
    /// relations not both `R` or into a result type other than `R`'s
    /// carrier: `Respects2<A, B, D>(RA, RB, S, op)` over the relations the
    /// two changed by, `S` the first of the rewrite's own relation (when `D`
    /// is its carrier), either argument's (when `D` is that one's carrier),
    /// and `RelId<D>` that resolves; `RelId<D>` from both arguments changed
    /// by `=` holds for every operation. `None` when `op` is not typed so.
    fn binary_across(&mut self, t: &Rc<Term>, args: &[&Rc<Term>], nodes: &[Node], term: &Rc<Term>) -> R<Option<Node>> {
        let n = args.len();
        let Some(target) = self.result_type(t) else { return Ok(None) };
        let (ra, rb) = (nodes[n - 2].rel().cloned(), nodes[n - 1].rel().cloned());
        let op = prefix(t, 2);
        let found = self.scoped(&Shape::Binary, &op, |rw, _, op| rw.respects_across(ra.as_ref(), rb.as_ref(), op, &target), |found, d| {
            found.map(|(ev, rel)| (Rc::new(ev.shift_local(d)), rel))
        })?;
        let Some((respects, rel)) = found else { return Ok(None) };
        let (x, x2, hx) = self.side(args[n - 2], &nodes[n - 2])?;
        let (y, y2, hy) = self.side(args[n - 1], &nodes[n - 1])?;
        Ok(Some(Node::related_by(Rc::clone(term), apply(respects, [x, x2, hx, y, y2, hy]), rel)))
    }

    /// [`Self::binary_across`]'s evidence for `op` (scoped where `cx` is):
    /// the `respects2` field, and the relation the result changes by.
    fn respects_across(
        &mut self,
        ra: Option<&Rc<Rel>>,
        rb: Option<&Rc<Rel>>,
        op: &Rc<Term>,
        (target, target_level): &(Rc<Type>, Level),
    ) -> R<Option<(Rc<Term>, Option<Rc<Rel>>)>> {
        // Each argument's carrier, its spelling, its relation's, and whether
        // that relation is `RelId`.
        let mut spelled = Vec::new();
        for r in [ra, rb] {
            let (carrier, level, head, identity) = match r {
                Some(r) => (Rc::clone(&r.carrier), r.level.clone(), Rc::clone(&r.head), r.identity),
                None => (Rc::clone(&self.carrier), self.level.clone(), Rc::clone(&self.relation), false),
            };
            let c = self.carrier_named(&carrier, &level);
            let name = self.relation_alias_at(&head, &c, &carrier)?;
            spelled.push((carrier, head, c, name, identity));
        }
        let [(ca, ha, a, sa, ia), (cb, hb, b, sb, ib)] = &spelled[..] else { unreachable!("two arguments") };
        let out = self.carrier_named(target, target_level);
        let (op_ty, op_level) = self.statement(&format!("{a} → {b} → {out}"))?;
        if !self.checks(op, &op_ty, &op_level) {
            return Ok(None);
        }
        let opn = self.alias(Rc::clone(op), op_ty, op_level);
        // Candidates for the result's relation, scoped where `cx` is.
        let here = |rw: &Self, r: &Rc<Term>| if rw.deep { Rc::new(r.shift_local(rw.depth())) } else { Rc::clone(r) };
        let mut candidates: Vec<Rc<Term>> = Vec::new();
        let both_identity = *ia && *ib;
        if both_identity {
            candidates.push(self.relid_here(&out)?);
        }
        if **target == *self.carrier {
            candidates.push(here(self, &self.relation));
        }
        for (carrier, head) in [(ca, ha), (cb, hb)] {
            if carrier == target {
                candidates.push(here(self, head));
            }
        }
        if candidates.is_empty() {
            candidates.push(self.relid_here(&out)?);
        }
        let mut first = None;
        let mut seen: Vec<Rc<Term>> = Vec::new();
        for candidate in candidates {
            if seen.contains(&candidate) {
                continue;
            }
            seen.push(Rc::clone(&candidate));
            let Some((root, rel)) = self.candidate_rel(&candidate, target, target_level, &out)? else { continue };
            let s = self.relation_alias_at(&root, &out, target)?;
            let (ty, level) = self.statement(&format!("algebra_rel::Respects2<{a}, {b}, {out}>({sa}, {sb}, {s}, {opn})"))?;
            let out_identity = rel.as_ref().is_some_and(|r| r.identity);
            let dict = match self.resolve(&ty, &level) {
                Some(dict) => Some((dict, ty.clone(), level.clone())),
                None if both_identity && out_identity => {
                    Some(self.expr(&format!("algebra_rel::relid_respects2({opn})"))?)
                }
                None => None,
            };
            if let Some((dict, ty, level)) = dict {
                return Ok(Some((self.project(dict, ty, level, "respects2")?, rel)));
            }
            first.get_or_insert((ty, level, rel));
        }
        let Some((ty, level, rel)) = first else { return Ok(None) };
        let goal = self.obligation_here(ty.clone(), level.clone(), "compatibility")?;
        Ok(Some((self.project(goal, ty, level, "respects2")?, rel)))
    }

    /// A codata constructor (§11.5): its children walked as the arguments
    /// they were written as, and one that changed crossed by the context
    /// `λ z. C(…, z, …)` — `λ k. CVis(c, k)` for a function child, which
    /// changed pointwise — as `Eutt::tau_respects` and `Eutt::vis_respects`
    /// state it.
    fn constructor(&mut self, t: &Rc<Term>, node: crate::codata::CtorNode) -> R<Node> {
        // The label's payload is not walked: an occurrence there would be
        // left behind.
        if let Some((lhs, ..)) = self.pattern()
            && (Type::El { level: Level::Zero, tm: Rc::clone(&node.label) }).abstract_local(&lhs).is_some()
        {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: the left side{} occurs in a payload field of the constructor{}; a \
                     relation rewrite goes into a constructor's children only",
                    self.shown(&lhs),
                    self.shown(t),
                ),
                span: self.span,
            });
        }
        let nodes = node.children.iter().map(|c| self.term(&c.term)).collect::<R<Vec<_>>>()?;
        let changed: Vec<usize> = (0..nodes.len()).filter(|&i| nodes[i].changed()).collect();
        let [r] = changed[..] else {
            if changed.is_empty() {
                return Ok(Node::Same);
            }
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: the constructor{} changes in {} of its children; a relation \
                     rewrite crosses a constructor by one child's evidence (`PreservesRelation`)",
                    self.shown(t),
                    changed.len(),
                ),
                span: self.span,
            });
        };
        let Node::Changed { term: new, .. } = &nodes[r] else { unreachable!() };
        let rebuilt = crate::codata::CtorNode::replaced(t, r, new).expect("read as a constructor above");
        // The context is `λ z. t` with child `r` the binder, as a rule
        // writes it, also for a constructor's only child.
        self.crossing(t, &node.children[r].term, &nodes[r], Rc::new(rebuilt), None, &|_, dom, dom_level, cod_level| {
            let body = crate::codata::CtorNode::replaced(&t.shift_local(1), r, &Rc::new(Term::Var(LocalVar(0))))
                .expect("read as a constructor above");
            Rc::new(Term::Lam { dom_level, cod_level, dom, body: Rc::new(body) })
        })
    }

    /// The step for node `t` whose one argument `arg` changed as `node`
    /// says, `term` being `t` rebuilt: evidence about its context, which is
    /// `partial` (the partial application, for a last argument that is not
    /// a λ) or `lam(dom, dom_level, cod_level)`, the context as a λ over
    /// the argument's type.
    #[allow(clippy::type_complexity)]
    fn crossing(
        &mut self,
        t: &Rc<Term>,
        arg: &Rc<Term>,
        node: &Node,
        term: Rc<Term>,
        partial: Option<Rc<Term>>,
        lam: &dyn Fn(&Self, Rc<Type>, Level, Level) -> Rc<Term>,
    ) -> R<Node> {
        let Node::Changed { term: x2, proof: hx, over, rel } = node else { unreachable!("crossed only when changed") };
        let input = rel.clone();
        // The argument's carrier: `R`'s, or that of the relation a context
        // below carried it to.
        let (carrier, level) = match &input {
            Some(r) => (Rc::clone(&r.carrier), r.level.clone()),
            None => (Rc::clone(&self.carrier), self.level.clone()),
        };
        // A λ argument crosses its consumer by pointwise evidence, its
        // context written as a λ (`λ g. f(…, g, …)`) as the library's rules
        // state it (`MonoidRel::range_pointwise`); any other argument by
        // `PreservesRelation(R, R, …)`.
        let (shape, dom, dom_level) = if over.is_empty() {
            (Shape::Unary, Rc::new(carrier.shift_local(self.depth())), level.clone())
        } else {
            let (fun, flevel) = self.function_type(over, &carrier, &level);
            (Shape::Pointwise(Arc::clone(over)), Rc::new(fun), flevel)
        };
        let unary = partial.is_some();
        let mut context = match partial {
            Some(p) => p,
            None => lam(self, Rc::clone(&dom), dom_level.clone(), level.clone()),
        };
        let mut found = self.lookup_here(&shape, input.as_ref(), &context, None)?;
        let mut target = None;
        if matches!(found, Lookup::Untyped) {
            // The context leaves the carrier (`bind(t, h)` at another result
            // type): its result changes by whatever relation its evidence
            // names at the type it maps into (§11.4).
            if let Some((d, d_level)) = self.result_type(t) {
                if !unary {
                    context = lam(self, Rc::clone(&dom), dom_level.clone(), d_level.clone());
                }
                let at = (d, d_level);
                found = self.lookup_here(&shape, input.as_ref(), &context, Some(&at))?;
                target = Some(at);
            }
        }
        if matches!(found, Lookup::Untyped) {
            let carrier_shown = self.e.display_type(self.original, &carrier);
            return Err(ElabError::Elab {
                msg: match &target {
                    None => format!(
                        "`rewrite`: rewriting inside{} changes an argument of a context that does \
                         not map {} to `{carrier_shown}`; a relation rewrite stays in the relation's carrier",
                        self.shown(t),
                        if over.is_empty() { "it" } else { "functions into it" },
                    ),
                    Some((d, _)) => format!(
                        "`rewrite`: rewriting inside{} changes an argument of a context from {}`{carrier_shown}` \
                         to `{}`, and no evidence about it names the relation its result changes by\n  \
                         hint: state `PreservesRelation(R, S, f)` for its context as an `evidence theorem`, \
                         with the relation `S` at `{}`",
                        self.shown(t),
                        if over.is_empty() { "" } else { "functions into " },
                        self.e.display_type(self.original, d),
                        self.e.display_type(self.original, d),
                    ),
                },
                span: self.span,
            });
        }
        let (preserves, out) = self.discharge_here(&shape, input.as_ref(), &context, target.as_ref())?;
        Ok(Node::related_by(term, apply(preserves, [Rc::clone(arg), Rc::clone(x2), Rc::clone(hx)]), out))
    }

    /// The type of node `t` and its level, scoped in the rewrite's context:
    /// what a context that leaves the carrier maps into. `None` when it
    /// mentions a binder the walk is below.
    fn result_type(&self, t: &Rc<Term>) -> Option<(Rc<Type>, Level)> {
        let oracle = self.e.goal_oracle();
        let (ty, level) = heather_kernel::typing::infer_term(
            oracle.world(),
            0,
            heather_kernel::layer::Layer::Prog,
            &self.here().gamma,
            t,
            self.e.policy.fuel,
        )
        .ok()?;
        let lowered = crate::strengthen_ty(&self.original.gamma, &ty, self.depth())?;
        Some((Rc::new(lowered), level))
    }

    /// `x`, what it became, and `R(x, x')` — reflexivity for an argument that
    /// stayed.
    fn side(&mut self, x: &Rc<Term>, node: &Node) -> R<(Rc<Term>, Rc<Term>, Rc<Term>)> {
        Ok(match node {
            Node::Changed { term, proof, .. } => (Rc::clone(x), Rc::clone(term), Rc::clone(proof)),
            Node::Same => (Rc::clone(x), Rc::clone(x), self.reflexivity(x)?),
        })
    }

    /// `λ z. f(…, z, …)` with `z : dom` at argument `i` of `t`'s spine: the
    /// context of a change that is not in the last argument, or of a λ.
    fn context(&self, t: &Rc<Term>, i: usize, dom: Rc<Type>, dom_level: Level, cod_level: Level) -> Rc<Term> {
        let (head, args) = crate::spelling::app_spine(t);
        let body = args.iter().enumerate().fold(Rc::new(head.shift_local(1)), |fun, (j, a)| {
            let arg = if j == i { Rc::new(Term::Var(LocalVar(0))) } else { Rc::new(a.shift_local(1)) };
            Rc::new(Term::AppAt { fun, arg })
        });
        Rc::new(Term::Lam { dom_level, cod_level, dom, body })
    }

    /// `D₁ → … → Dₙ → C` for a λ's binder types, at the walk's depth, and
    /// its level.
    fn function_type(&self, over: &[(Rc<Type>, Level)], carrier: &Type, level: &Level) -> (Type, Level) {
        let m = over.len() as u32;
        let start = (carrier.shift_local(self.depth() + m), level.clone());
        over.iter().enumerate().rev().fold(start, |(ty, level), (j, (dom, dl))| {
            let ty = Type::Pi {
                dom_level: dl.clone(),
                cod_level: level.clone(),
                dom: Rc::new(dom.shift_local(j as u32)),
                cod: Rc::new(ty),
            };
            (ty, Level::join(dl.clone(), level))
        })
    }

    // ---------------------------------------------------------------------
    // Evidence

    /// [`Self::lookup`] at the walk's depth.
    fn lookup_here(&mut self, shape: &Shape, input: Option<&Rc<Rel>>, context: &Rc<Term>, target: Option<&(Rc<Type>, Level)>) -> R<Lookup> {
        self.scoped(shape, context, |rw, shape, context| rw.lookup(shape, input, context, target), Lookup::shifted)
    }

    /// [`Self::discharge`] at the walk's depth.
    fn discharge_here(
        &mut self,
        shape: &Shape,
        input: Option<&Rc<Rel>>,
        context: &Rc<Term>,
        target: Option<&(Rc<Type>, Level)>,
    ) -> R<(Rc<Term>, Option<Rc<Rel>>)> {
        self.scoped(shape, context, |rw, shape, context| rw.discharge(shape, input, context, target), |(ev, rel), d| {
            (Rc::new(ev.shift_local(d)), rel)
        })
    }

    /// Evidence for a context met below binders: asked at the rewrite's own
    /// context when the context mentions none of them — once for every depth
    /// it is met at, then shifted — and otherwise in the binders' context,
    /// where nothing is kept and a missing statement is refused, since a goal
    /// raised there would have nothing to bind its variables to.
    fn scoped<T>(
        &mut self,
        shape: &Shape,
        context: &Rc<Term>,
        at: impl FnOnce(&mut Self, &Shape, &Rc<Term>) -> R<T>,
        shifted: impl FnOnce(T, u32) -> T,
    ) -> R<T> {
        let d = self.depth();
        if d == 0 {
            return at(self, shape, context);
        }
        let gamma = &self.original.gamma;
        if let Some(lowered) = crate::strengthen_tm(gamma, context, d)
            && let Some(shape) = shape.strengthened(gamma, d)
        {
            return at(self, &shape, &Rc::new(lowered)).map(|found| shifted(found, d));
        }
        self.in_binders(|rw| at(rw, shape, context))
    }

    /// `f` with `cx` extended by the binders the walk is below, so evidence
    /// is stated where the walk is. Nothing it makes is kept: aliases and
    /// answers made there mention those binders.
    fn in_binders<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = (self.cx.clone(), self.contexts.len(), self.relations.len(), self.domains.len());
        for (i, b) in self.binders.iter().enumerate() {
            self.cx.push(format!("__bound_{i}"), (*b.dom).clone(), b.level.clone());
        }
        self.deep = true;
        let found = f(self);
        self.deep = false;
        self.cx = saved.0;
        self.contexts.truncate(saved.1);
        self.relations.truncate(saved.2);
        self.domains.truncate(saved.3);
        found
    }

    /// What resolution says about `context`'s congruence of `shape`, asked
    /// once per context. The argument changes by `input` (`R` when `None`);
    /// the result by the same relation, or, with a `target` type the context
    /// maps into, by a relation its evidence names there (§11.4).
    fn lookup(&mut self, shape: &Shape, input: Option<&Rc<Rel>>, context: &Rc<Term>, target: Option<&(Rc<Type>, Level)>) -> R<Lookup> {
        let key = (shape.clone(), input.cloned(), Rc::clone(context), target.is_some());
        if let Some((_, found)) = self.contexts.iter().find(|(k, _)| *k == key) {
            return Ok(found.clone());
        }
        let (carrier, level, relation) = match input {
            Some(r) => (Rc::clone(&r.carrier), r.level.clone(), Rc::clone(&r.head)),
            None => (Rc::clone(&self.carrier), self.level.clone(), Rc::clone(&self.relation)),
        };
        let c = self.carrier_named(&carrier, &level);
        let rel = self.relation_alias_at(&relation, &c, &carrier)?;
        // The relation the context's argument changes by, and its type.
        let (input_text, argument) = match shape {
            Shape::Unary | Shape::Binary => (rel.clone(), c.clone()),
            Shape::Pointwise(over) => {
                let mut input = rel.clone();
                let mut fun = c.clone();
                for (dom, level) in over.iter().rev() {
                    let d = self.domain(dom, level);
                    input = format!("relation_props::Pointwise<{d}, {fun}>({input})");
                    fun = format!("{d} → {fun}");
                }
                (input, format!("({fun})"))
            }
        };
        let out = match target {
            Some((d, l)) => self.carrier_named(d, l),
            None => c.clone(),
        };
        let operation = match shape {
            Shape::Binary => format!("{c} → {c} → {c}"),
            Shape::Unary | Shape::Pointwise(_) => format!("{argument} → {out}"),
        };
        let (op_ty, op_level) = self.statement(&operation)?;
        // An argument changed by `=` crosses every context (§11.6).
        let identity = matches!(shape, Shape::Unary) && input.is_some_and(|r| r.identity);
        let found = if !self.checks(context, &op_ty, &op_level) {
            Lookup::Untyped
        } else if let Some((d, l)) = target {
            let op = self.alias(Rc::clone(context), op_ty, op_level);
            self.leaving(&input_text, identity, &op, context, d, l, &out)?
        } else {
            let op = self.alias(Rc::clone(context), op_ty, op_level);
            let statement = match shape {
                Shape::Unary | Shape::Pointwise(_) => format!("relation_props::PreservesRelation({input_text}, {rel}, {op})"),
                Shape::Binary => format!("algebra_rel::Respects2<{c}, {c}, {c}>({rel}, {rel}, {rel}, {op})"),
            };
            let (ty, level) = self.statement(&statement)?;
            let ev = match shape {
                Shape::Binary => self.resolve(&ty, &level),
                Shape::Unary | Shape::Pointwise(_) => self.preserves(&ty, &level, identity, identity, &rel, &c, &op)?,
            };
            match ev {
                Some(ev) => Lookup::Found(self.applicable(shape, ev, ty, level)?, input.cloned()),
                None => Lookup::Missing(ty, level, input.cloned()),
            }
        };
        self.contexts.push((key, found.clone()));
        Ok(found)
    }

    /// The evidence for a context `op` that maps the argument's carrier
    /// into `target` (spelled `out`): each relation `S` at `target` that a
    /// hypothesis in scope or an evidence rule about `op` names, then the
    /// rewrite's own relation when `target` is its carrier, and `RelId` at
    /// `target` when nothing named one (§11.6) — in turn, with
    /// `PreservesRelation(input, S, op)` resolved; the first relation's
    /// statement as the obligation when none resolves. `identity` when the
    /// argument changed by `=`, which every context preserves into a
    /// reflexive relation.
    #[allow(clippy::too_many_arguments)]
    fn leaving(
        &mut self,
        input: &str,
        identity: bool,
        op: &str,
        context: &Rc<Term>,
        target: &Rc<Type>,
        target_level: &Level,
        out: &str,
    ) -> R<Lookup> {
        let mut candidates = self.named_relations(context);
        if **target == *self.carrier {
            let own = if self.deep { Rc::new(self.relation.shift_local(self.depth())) } else { Rc::clone(&self.relation) };
            if !candidates.contains(&own) {
                candidates.push(own);
            }
        }
        if candidates.is_empty() {
            candidates.push(self.relid_here(out)?);
        }
        let mut first = None;
        for candidate in candidates {
            let Some((root, rel)) = self.candidate_rel(&candidate, target, target_level, out)? else { continue };
            let s = self.relation_alias_at(&root, out, target)?;
            let (ty, level) = self.statement(&format!("relation_props::PreservesRelation({input}, {s}, {op})"))?;
            let out_identity = rel.as_ref().is_some_and(|r| r.identity);
            if let Some(ev) = self.preserves(&ty, &level, identity, out_identity, &s, out, op)? {
                return Ok(Lookup::Found(Rc::new(ev), rel));
            }
            first.get_or_insert((ty, level, rel));
        }
        Ok(first.map_or(Lookup::Untyped, |(ty, level, rel)| Lookup::Missing(ty, level, rel)))
    }

    /// A relation `candidate` at `target` (spelled `out`), scoped where `cx`
    /// is, as a node keeps it: scoped in the rewrite's context, `None` for
    /// the rewrite's own relation. `None` altogether when it mentions a
    /// binder the walk is below (a node's parents are above it) or is no
    /// relation on `target`.
    fn candidate_rel(
        &mut self,
        candidate: &Rc<Term>,
        target: &Rc<Type>,
        target_level: &Level,
        out: &str,
    ) -> R<Option<(Rc<Term>, Option<Rc<Rel>>)>> {
        let Some(root) = (if self.deep {
            crate::strengthen_tm(&self.original.gamma, candidate, self.depth()).map(Rc::new)
        } else {
            Some(Rc::clone(candidate))
        }) else {
            return Ok(None);
        };
        if **target == *self.carrier && self.same_relation(&root, &self.relation) {
            return Ok(Some((root, None)));
        }
        let Some(holds) = self.relation_level(candidate) else { return Ok(None) };
        if self.relation_alias_at(&root, out, target).is_err() {
            return Ok(None);
        }
        let identity = self.is_identity_here(candidate, out)?;
        let rel = Rel { head: Rc::clone(&root), carrier: Rc::clone(target), level: target_level.clone(), holds, identity };
        Ok(Some((root, Some(Rc::new(rel)))))
    }

    /// `PreservesRelation(input, S, op)` (`ty`): resolved, or, for an
    /// argument changed by `=` (`identity`), every function's — into `=`
    /// itself, or into `S` (spelled `s`, at `out`) by its reflexivity.
    #[allow(clippy::too_many_arguments)]
    fn preserves(
        &mut self,
        ty: &Type,
        level: &Level,
        identity: bool,
        out_identity: bool,
        s: &str,
        out: &str,
        op: &str,
    ) -> R<Option<Term>> {
        if let Some(ev) = self.resolve(ty, level) {
            return Ok(Some(ev));
        }
        if !identity {
            return Ok(None);
        }
        if out_identity {
            return self.expr(&format!("relation_props::preserves_relid_relid({op})")).map(|(t, ..)| Some(t));
        }
        let (rty, rlevel) = self.statement(&format!("relation_props::Reflexive<{out}>({s})"))?;
        let Some(dict) = self.resolve(&rty, &rlevel) else { return Ok(None) };
        let r = self.alias(Rc::new(dict), rty, rlevel);
        self.expr(&format!("relation_props::preserves_relid({s}, {op}, {r})")).map(|(t, ..)| Some(t))
    }

    /// `RelId` at the carrier spelled `c`, scoped where `cx` is, as the λ a
    /// relation argument spells it.
    fn relid_here(&self, c: &str) -> R<Rc<Term>> {
        self.expr(&format!("relation::RelId<{c}>")).map(|(t, ..)| Rc::new(t))
    }

    /// Is relation `r` at the carrier spelled `c`, scoped where `cx` is,
    /// `RelId` there?
    fn is_identity_here(&self, r: &Rc<Term>, c: &str) -> R<bool> {
        let id = self.relid_here(c)?;
        Ok(Rewrites(self.e).terms_convert(&self.cx, r, &id))
    }

    /// The relations evidence about `PreservesRelation` names for the result
    /// of `context` (their `S` in `PreservesRelation(R, S, f)`), scoped where
    /// `cx` is: first the hypotheses in scope whose `f` converts to
    /// `context`, then the evidence rules, each rule's `f` matched against
    /// `context` and `S` instantiated by the match. A rule whose `S` the
    /// match leaves open names none.
    fn named_relations(&mut self, context: &Rc<Term>) -> Vec<Rc<Term>> {
        let Some(info) = self.e.names.global(&crate::names::qkey("relation_props", "PreservesRelation")) else {
            return Vec::new();
        };
        let abs = info.abs as usize;
        let mut out: Vec<Rc<Term>> = Vec::new();
        // Hypotheses: `p : PreservesRelation(R, S, f)` as written, each
        // entry's type scoped over the entries before it.
        let n = self.cx.gamma.len();
        for (i, entry) in self.cx.gamma.entries.iter().enumerate() {
            let Type::El { tm, .. } = &*entry.ty else { continue };
            let (head, args) = crate::spelling::app_spine(tm);
            let Term::GlobalTm { var, .. } = head else { continue };
            if self.e.global_abs_of(*var) != Some(abs) {
                continue;
            }
            let [.., _, s, f] = args.as_slice() else { continue };
            let by = (n - i) as u32;
            let (s, f) = (s.shift_local(by), f.shift_local(by));
            if (f == **context || Rewrites(self.e).terms_convert(&self.cx, &f, context)) && !out.iter().any(|o| **o == s) {
                out.push(Rc::new(s));
            }
        }
        let Some(key) = self.e.names.global_name_at(info.abs).map(str::to_string) else { return out };
        let rules: Vec<String> = self.e.traits.evidence_rules(&key).iter().map(|r| r.global.clone()).collect();
        for g in rules {
            let e = Expr { kind: heather_syntax::ExprKind::Var(g), span: self.span };
            let Ok((_, ty, _)) = self.e.generated_scope(|el| el.elab_infer(&self.cx, &e)) else { continue };
            // The rule's telescope, opened as written.
            let mut k = 0u32;
            let mut cur = ty;
            while let Type::Pi { cod, .. } = cur {
                cur = (*cod).clone();
                k += 1;
            }
            let Type::El { tm, .. } = &cur else { continue };
            let (_, args) = crate::spelling::app_spine(tm);
            let [.., _, s, f] = args.as_slice() else { continue };
            let mut binds = vec![None; k as usize];
            if !Rewrites(self.e).match_deep(&self.cx, f, context, k, 0, &mut binds) {
                continue;
            }
            if let Some(named) = super::instantiate(&self.cx.gamma, s, k, &binds) {
                let named = Rc::new(named);
                if !out.contains(&named) {
                    out.push(named);
                }
            }
        }
        out
    }

    /// `h` for a relation `C → C → Type<h>`, read off its type.
    fn relation_level(&self, r: &Term) -> Option<Level> {
        let oracle = self.e.goal_oracle();
        let (ty, _) = heather_kernel::typing::infer_term(
            oracle.world(),
            0,
            heather_kernel::layer::Layer::Prog,
            &self.cx.gamma,
            r,
            self.e.policy.fuel,
        )
        .ok()?;
        let mut cur = ty;
        for _ in 0..2 {
            let Type::Pi { cod, .. } = self.e.whnf(&self.cx, &cur, self.span).ok()? else { return None };
            cur = (*cod).clone();
        }
        match self.e.whnf(&self.cx, &cur, self.span).ok()? {
            Type::Ty(h) => Some(h),
            _ => None,
        }
    }

    /// The evidence for a context [`Self::lookup`] typed, an obligation when
    /// resolution did not find it, and the relation its result changes by.
    fn discharge(
        &mut self,
        shape: &Shape,
        input: Option<&Rc<Rel>>,
        context: &Rc<Term>,
        target: Option<&(Rc<Type>, Level)>,
    ) -> R<(Rc<Term>, Option<Rc<Rel>>)> {
        match self.lookup(shape, input, context, target)? {
            Lookup::Found(ev, rel) => Ok((ev, rel)),
            Lookup::Untyped => unreachable!("discharged only once typed"),
            Lookup::Missing(ty, level, rel) => {
                let goal = self.obligation_here(ty.clone(), level.clone(), "compatibility")?;
                let ev = self.applicable(shape, goal, ty, level)?;
                let key = (shape.clone(), input.cloned(), Rc::clone(context), target.is_some());
                let entry = self.contexts.iter_mut().find(|(k, _)| *k == key);
                entry.expect("looked up above").1 = Lookup::Found(Rc::clone(&ev), rel.clone());
                Ok((ev, rel))
            }
        }
    }

    /// Evidence as a function of `x, x', h, …`: `PreservesRelation` is one,
    /// a `Respects2` dictionary through its field.
    fn applicable(&mut self, shape: &Shape, ev: Term, ty: Type, level: Level) -> R<Rc<Term>> {
        match shape {
            Shape::Unary | Shape::Pointwise(_) => Ok(Rc::new(ev)),
            Shape::Binary => self.project(ev, ty, level, "respects2"),
        }
    }

    /// `R(x, x)` at the walk's depth: `Reflexive<C>(R)`'s field, or an
    /// obligation of its own, as `rel_cong` leaves an unchanged argument.
    fn reflexivity(&mut self, x: &Rc<Term>) -> R<Rc<Term>> {
        if self.reflexive.is_none() {
            let rel = self.relation_alias(&Rc::clone(&self.relation))?;
            let (ty, level) = self.statement(&format!("relation_props::Reflexive<{}>({rel})", self.carrier_name))?;
            self.reflexive = Some(match self.resolve(&ty, &level) {
                Some(dict) => Some(self.project(dict, ty, level, "rel_refl")?),
                None => None,
            });
        }
        let d = self.depth();
        if let Some(Some(refl)) = &self.reflexive {
            return Ok(apply(Rc::new(refl.shift_local(d)), [Rc::clone(x)]));
        }
        if let Some(lowered) = crate::strengthen_tm(&self.original.gamma, x, d) {
            let fixed = self.fixed(Rc::new(lowered))?;
            return Ok(Rc::new(fixed.shift_local(d)));
        }
        self.in_binders(|rw| rw.fixed(Rc::clone(x))).map(Rc::new)
    }

    /// The obligation `R(x, x)`, `x` scoped where `cx` is.
    fn fixed(&mut self, x: Rc<Term>) -> R<Term> {
        let rel = self.relation_alias(&Rc::clone(&self.relation))?;
        let carrier = self.carrier.shift_local(if self.deep { self.depth() } else { 0 });
        let xa = self.alias(x, carrier, self.level.clone());
        let (ty, level) = self.statement(&format!("{rel}({xa}, {xa})"))?;
        self.obligation_here(ty, level, "fixed")
    }

    /// `R(y, x)` from `p : R(x, y)`, `R` at `carrier`.
    /// `identity` when `R` is `RelId`, whose symmetry is `relid_equivalence`'s.
    fn symmetric(
        &mut self,
        p: &Rc<Term>,
        x: &Rc<Term>,
        y: &Rc<Term>,
        r: &Rc<Term>,
        identity: bool,
        carrier: (&Rc<Type>, &Level),
    ) -> R<Rc<Term>> {
        let sym = if identity {
            self.identity_field("relid_equivalence", |c, _| format!("relation_props::relid_equivalence<{c}>()"), r, "rel_sym", carrier)?
        } else {
            self.class_field("Symmetric", &[Rc::clone(r)], "rel_sym", "symmetry", carrier)?
        };
        Ok(apply(sym, [Rc::clone(x), Rc::clone(y), Rc::clone(p)]))
    }

    /// The step that chains `first(x, y)` and `second(y, z)` into
    /// `goal(x, z)`: `Transitive`'s when all three are one relation, else
    /// `Trans`'s, the classes `calc` chains with. A step by `RelId` (each
    /// relation comes with whether it is) is the `=` step `calc` transports
    /// along, as `Trans` dictionaries (`trans_relid_l`/`_r`).
    fn chain(
        &mut self,
        (first, first_id): (&Rc<Term>, bool),
        (second, second_id): (&Rc<Term>, bool),
        goal: &Rc<Term>,
        carrier: (&Rc<Type>, &Level),
    ) -> R<Rc<Term>> {
        if first_id {
            return self.identity_field("trans_relid_l", |c, g| format!("relation_props::trans_relid_l<{c}>({g})"), goal, "rel_chain", carrier);
        }
        if second_id {
            return self.identity_field("trans_relid_r", |c, g| format!("relation_props::trans_relid_r<{c}>({g})"), goal, "rel_chain", carrier);
        }
        if self.same_relation(first, goal) && self.same_relation(second, goal) {
            self.class_field("Transitive", &[Rc::clone(goal)], "rel_trans", "transitivity", carrier)
        } else {
            let relations = [Rc::clone(first), Rc::clone(second), Rc::clone(goal)];
            self.class_field("Trans", &relations, "rel_chain", "transitivity", carrier)
        }
    }

    /// Are two relations, scoped in the rewrite's context, the same: as
    /// written, or by conversion (`Eutt::Rel<R>(E)` and the λ a goal
    /// `Eutt<R>(E, t, u)` is read by).
    fn same_relation(&self, a: &Rc<Term>, b: &Rc<Term>) -> bool {
        a == b || Rewrites(self.e).terms_convert(self.original, a, b)
    }

    /// `class<C>(relations…)`'s `field`, resolved or an obligation, once.
    fn class_field(
        &mut self,
        class: &'static str,
        relations: &[Rc<Term>],
        field: &str,
        label: &str,
        (carrier, level): (&Rc<Type>, &Level),
    ) -> R<Rc<Term>> {
        if let Some((_, _, t)) = self.fields.iter().find(|(c, rs, _)| *c == class && rs.as_slice() == relations) {
            return Ok(Rc::clone(t));
        }
        let c = self.carrier_named(carrier, level);
        let mut names = Vec::new();
        for r in relations {
            names.push(self.relation_alias_at(r, &c, carrier)?);
        }
        let (ty, level) = self.statement(&format!("relation_props::{class}<{c}>({})", names.join(", ")))?;
        let dict = match self.resolve(&ty, &level) {
            Some(dict) => dict,
            None => self.obligation(ty.clone(), level.clone(), label)?,
        };
        let projected = self.project(dict, ty, level, field)?;
        self.fields.push((class, relations.to_vec(), Rc::clone(&projected)));
        Ok(projected)
    }

    /// `field` of the dictionary `text(c, r)` builds for relation `r` at
    /// `carrier` (spelled `c`, `r` by its alias), once: what stands in for a
    /// class every `RelId` step has.
    fn identity_field(
        &mut self,
        what: &'static str,
        text: impl Fn(&str, &str) -> String,
        r: &Rc<Term>,
        field: &str,
        (carrier, level): (&Rc<Type>, &Level),
    ) -> R<Rc<Term>> {
        let key = [Rc::clone(r)];
        if let Some((_, _, t)) = self.fields.iter().find(|(c, rs, _)| *c == what && rs.as_slice() == key) {
            return Ok(Rc::clone(t));
        }
        let c = self.carrier_named(carrier, level);
        let name = self.relation_alias_at(r, &c, carrier)?;
        let (dict, ty, level) = self.expr(&text(&c, &name))?;
        let projected = self.project(dict, ty, level, field)?;
        self.fields.push((what, key.to_vec(), Rc::clone(&projected)));
        Ok(projected)
    }

    fn resolve(&self, ty: &Type, level: &Level) -> Option<Term> {
        self.e.resolve_goal(
            &self.cx,
            ty,
            level,
            &self.e.display_type(if self.deep { &self.cx } else { self.original }, ty),
            None,
            self.span,
            &mut Vec::new(),
        )
    }

    /// [`Self::obligation`] for a statement scoped where `cx` is: below the
    /// walk's binders (§10.4) it is closed over them — a goal at the
    /// rewrite's own context, `(z₁: D₁) → … → statement` — and applied back
    /// to them.
    fn obligation_here(&mut self, ty: Type, level: Level, label: &str) -> R<Term> {
        if !self.deep {
            return self.obligation(ty, level, label);
        }
        let (closed, closed_level) = self.binders.iter().rev().fold((ty, level), |(cod, cod_level), b| {
            let pi = Type::Pi {
                dom_level: b.level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(&b.dom),
                cod: Rc::new(cod),
            };
            (pi, Level::join(b.level.clone(), cod_level))
        });
        let goal = self.obligation(closed, closed_level, label)?;
        let d = self.depth();
        let bound = (0..d).rev().map(|i| Rc::new(Term::Var(LocalVar(i))));
        Ok(Rc::unwrap_or_clone(apply(Rc::new(goal.shift_local(d)), bound)))
    }

    fn obligation(&mut self, ty: Type, level: Level, label: &str) -> R<Term> {
        if let Some(refused) = &mut self.refused {
            let statement = self.e.spell_type_clean(self.original, &ty).unwrap_or_else(|| self.e.display_type(self.original, &ty));
            let msg = format!("needs `?{label}`: `{statement}`");
            refused.push(statement);
            return Err(ElabError::Elab { msg, span: self.span });
        }
        self.goals += 1;
        RelationalProof(self.e).relation_obligation(self.original, "rewrite", label, self.goals - 1, ty, level, self.span)
    }

    /// `dict.field`, elaborated as written.
    fn project(&mut self, dict: Term, ty: Type, level: Level, field: &str) -> R<Rc<Term>> {
        let name = self.alias(Rc::new(dict), ty, level);
        self.expr(&format!("{name}.{field}")).map(|(t, ..)| Rc::new(t))
    }

    /// An expression written as text in `cx`, inferred.
    fn expr(&self, text: &str) -> R<(Term, Type, Level)> {
        let source = format!("fn generated() -> Type {{ {text} }}");
        let mut file = parse_file(&source).map_err(|e| ElabError::Elab { msg: e.msg, span: self.span })?;
        let Some(Item::Decl(d)) = file.items.pop() else { unreachable!("one declaration") };
        self.e.generated_scope(|e| e.elab_infer(&self.cx, &d.body.result))
    }

    // ---------------------------------------------------------------------
    // Spelling evidence statements

    /// A type written as text in `cx`: an evidence statement over the
    /// carrier and aliases.
    fn statement(&self, text: &str) -> R<(Type, Level)> {
        if let Some(module) = ["relation_props", "algebra_rel"].into_iter().find(|m| !self.e.names.has_module(m)) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite` along a relation states its evidence with `relation_props` and \
                     `algebra_rel`, and `{module}` is not in this run's import closure\n  \
                     hint: import both modules"
                ),
                span: self.span,
            });
        }
        let source = format!("fn generated(x: {text}) -> Type {{ Type }}");
        let mut file = parse_file(&source).map_err(|e| ElabError::Elab { msg: e.msg, span: self.span })?;
        let Some(Item::Decl(d)) = file.items.pop() else { unreachable!("one declaration") };
        self.e.elab_ty(&self.cx, &d.params[0].ty).map_err(|e| ElabError::Elab {
            msg: format!(
                "`rewrite` along a relation states its evidence with `relation_props` and \
                 `algebra_rel`, and could not state `{text}`: {}\n  hint: import both modules",
                e.message()
            ),
            span: self.span,
        })
    }

    /// The alias that spells relation `r` (`C → C → Type`), made once.
    fn relation_alias(&mut self, r: &Rc<Term>) -> R<String> {
        let (c, carrier) = (self.carrier_name.clone(), Rc::clone(&self.carrier));
        self.relation_alias_at(r, &c, &carrier)
    }

    /// The type variable that spells `carrier`: the rewrite's own, or one
    /// made for it.
    fn carrier_named(&mut self, carrier: &Rc<Type>, level: &Level) -> String {
        if **carrier == *self.carrier {
            return self.carrier_name.clone();
        }
        // Carriers are scoped in the rewrite's context; below binders `cx`
        // is extended by them.
        let here = if self.deep { Rc::new(carrier.shift_local(self.depth())) } else { Rc::clone(carrier) };
        self.domain(&here, level)
    }

    /// [`Self::relation_alias`] for a relation on `carrier`, spelled `c`.
    fn relation_alias_at(&mut self, r: &Rc<Term>, c: &str, carrier: &Rc<Type>) -> R<String> {
        if let Some((_, name)) = self.relations.iter().find(|(t, _)| t == r) {
            return Ok(name.clone());
        }
        let (ty, level) = self.statement(&format!("{c} → {c} → Type"))?;
        // Relations are scoped in the rewrite's context; below binders `cx`
        // is extended by them.
        let here = if self.deep { Rc::new(r.shift_local(self.depth())) } else { Rc::clone(r) };
        if !self.checks(&here, &ty, &level) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`:{} is not a relation on `{}` alone; a relation rewrite needs \
                     a non-dependent `C → C → Type`",
                    self.shown(r),
                    self.e.display_type(self.original, carrier),
                ),
                span: self.span,
            });
        }
        let name = self.alias(here, ty, level);
        self.relations.push((Rc::clone(r), name.clone()));
        Ok(name)
    }

    /// The type variable that spells binder type `dom`, made once.
    fn domain(&mut self, dom: &Rc<Type>, level: &Level) -> String {
        if let Some((_, name)) = self.domains.iter().find(|(t, _)| t == dom) {
            return name.clone();
        }
        let name = self.fresh();
        self.cx.tyvars.push(TyVar { name: name.clone(), ty: (**dom).clone(), level: level.clone(), depth: self.cx.names.len() });
        self.domains.push((Rc::clone(dom), name.clone()));
        name
    }

    fn alias(&mut self, term: Rc<Term>, ty: Type, level: Level) -> String {
        let name = self.fresh();
        self.cx.aliases.push(Rc::new(Alias {
            name: name.clone(),
            depth: self.cx.names.len(),
            term,
            ty,
            level,
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        name
    }

    fn fresh(&mut self) -> String {
        loop {
            let name = format!("__rewrite_{}", self.serial);
            self.serial += 1;
            if !self.cx.names.contains(&name)
                && !self.cx.aliases.iter_inner().any(|a| a.name == name)
                && !self.cx.tyvars.iter_inner().any(|a| a.name == name)
            {
                return name;
            }
        }
    }

    /// Does `t` check at `ty` in the kernel?
    fn checks(&self, t: &Term, ty: &Type, level: &Level) -> bool {
        crate::stats::timed(crate::stats::Timer::KernelGate, || {
            self.e
                .kernel_check_term(
                    self.e.semantic_oracle().world(),
                    heather_kernel::layer::Layer::Prog,
                    &self.cx.gamma,
                    t,
                    ty,
                    level,
                )
                .is_ok()
        })
    }

    fn shown(&self, t: &Term) -> String {
        self.e.spell_term_clean(self.here(), t).map_or_else(String::new, |s| format!(" `{s}`"))
    }
}

/// `f` applied to `args`, as `app@` nodes: the kernel reads each Π off the
/// head's type, so no argument is spelled again in an annotation. A `λ` head
/// (a local proof written as one) is contracted instead, since `app@` takes
/// no `λ`.
fn apply(f: Rc<Term>, args: impl IntoIterator<Item = Rc<Term>>) -> Rc<Term> {
    args.into_iter().fold(f, |f, a| match &*f {
        Term::Lam { body, .. } => Rc::new(body.inst_top(0, &a)),
        _ => Rc::new(Term::AppAt { fun: f, arg: a }),
    })
}

/// `t`'s spine with `k` arguments taken off the end, the node itself.
fn prefix(t: &Rc<Term>, k: usize) -> Rc<Term> {
    (0..k).fold(Rc::clone(t), |t, _| Rc::clone(crate::spelling::app_of(&t).expect("a spine this long").0))
}

/// `t`'s spine with each changed argument replaced: the nodes below the first
/// change are `t`'s own, the rest `app@`.
fn rebuild(t: &Rc<Term>, nodes: &[Node]) -> Rc<Term> {
    let first = nodes.iter().position(Node::changed).expect("something changed");
    let (_, args) = crate::spelling::app_spine(t);
    let base = prefix(t, nodes.len() - first);
    nodes[first..].iter().zip(&args[first..]).fold(base, |fun, (node, arg)| {
        let arg = match node {
            Node::Changed { term, .. } => Rc::clone(term),
            Node::Same => Rc::clone(arg),
        };
        Rc::new(Term::AppAt { fun, arg })
    })
}

/// An arrow built innermost-first from closed-over types, with each
/// codomain moved under the binders written before it: the last of `n`
/// codomains sits under `n` binders.
fn arrow_shifted(ty: &Rc<Type>, n: u32) -> Type {
    fn go(ty: &Type, under: u32, left: u32) -> Type {
        match ty {
            Type::Pi { dom_level, cod_level, dom, cod } if left > 0 => Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::new(go(cod, under + 1, left - 1)),
            },
            _ => ty.shift_local(under),
        }
    }
    go(ty, 0, n)
}
