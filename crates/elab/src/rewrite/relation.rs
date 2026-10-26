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
//! The proof is kernel terms (`app@` spines over the evidence), not source
//! text, and nothing in it is trusted: the declaration gate checks it.
//! Evidence that resolution does not find is an obligation, as `rel_cong`
//! leaves it, discharged by `on ?label := …`.

use std::collections::HashMap;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::{Expr, Item, Span, parse_file};

use super::{CANDIDATES, MAX_OPEN, same_key};
use crate::relational_context::proof::Relation;
use crate::{Alias, Cx, ElabError, Elaborator, R, TyVar};

impl Elaborator {
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
        let mut pcx = cx.clone();
        let mut k = 0u32;
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
                    pcx.push(format!("_{k}"), (*dom).clone(), dom_level);
                    k += 1;
                    cur = (*cod).clone();
                }
                _ => return Ok(None),
            }
        };
        if k == 0 {
            return RelationRewrite::new(self, cx, h.span, pattern, proof.clone()).map(Some);
        }
        if matches!(&*pattern.left, Term::Var(x) if x.0 < k) {
            return Err(ElabError::Elab {
                msg: "`rewrite`: this relation's left side is one of its own arguments, so it \
                      would match every subterm; apply it to that argument"
                    .into(),
                span: h.span,
            });
        }
        let found = goal_nodes(cx, goal)
            .into_iter()
            .filter(|t| same_key(&pattern.left, t, k))
            .take(CANDIDATES)
            .find_map(|t| {
                let mut binds = vec![None; k as usize];
                self.match_pattern(cx, &pattern.left, &t, k, &mut binds).then_some(binds)
            });
        let Some(binds) = found else {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: no subterm of {what} `{}` is an instance of this relation's \
                     left side\n  note: an instance has the left side's head, and its other \
                     parts convert",
                    self.display_type(cx, goal)
                ),
                span: h.span,
            });
        };
        // Binder `j` (outermost first) is `Var(k - 1 - j)` in `pcx`.
        let mut term = Rc::new(proof.clone());
        let mut ty_now = proof_ty.clone();
        for j in 0..k {
            let Some(arg) = binds[(k - 1 - j) as usize].clone() else {
                return Err(ElabError::Elab {
                    msg: format!(
                        "`rewrite`: matching the left side does not determine this relation's \
                         argument {}, which only its right side mentions; give it explicitly",
                        j + 1
                    ),
                    span: h.span,
                });
            };
            let Type::Pi { cod, .. } = self.whnf(cx, &ty_now, h.span)? else {
                unreachable!("opened as a Π above")
            };
            ty_now = cod.inst_top(0, &arg);
            term = apply(term, [arg]);
        }
        let instance = Relation::of_type(self, cx, &ty_now, h.span).expect("instantiated from a relation");
        RelationRewrite::new(self, cx, h.span, instance, Rc::unwrap_or_clone(term)).map(Some)
    }
}

/// The terms of `goal` the relation walk can reach — relation sides, a
/// non-dependent implication's two halves, and application arguments below
/// them — each once, in the order the walk first meets them.
fn goal_nodes(cx: &Cx, goal: &Type) -> Vec<Rc<Term>> {
    fn types(cx: &Cx, ty: &Type, seen: &mut std::collections::HashSet<*const Term>, out: &mut Vec<Rc<Term>>) {
        match ty {
            Type::El { tm, .. } => terms(tm, seen, out),
            Type::Pi { dom, cod, .. } => {
                types(cx, dom, seen, out);
                if let Some(cod) = crate::strengthen_ty(&cx.gamma, cod, 1) {
                    types(cx, &cod, seen, out);
                }
            }
            _ => {}
        }
    }
    fn terms(t: &Rc<Term>, seen: &mut std::collections::HashSet<*const Term>, out: &mut Vec<Rc<Term>>) {
        if !seen.insert(Rc::as_ptr(t)) {
            return;
        }
        out.push(Rc::clone(t));
        let (head, args) = crate::spelling::app_spine(t);
        if !matches!(head, Term::Lam { .. }) {
            for a in args {
                terms(a, seen, out);
            }
        }
    }
    let mut out = Vec::new();
    types(cx, goal, &mut std::collections::HashSet::new(), &mut out);
    out
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

/// A term after the walk: unchanged, or rewritten to `term` with
/// `proof : R(original, term)`.
#[derive(Clone)]
enum Node {
    Same,
    Changed { term: Rc<Term>, proof: Rc<Term> },
}

impl Node {
    fn changed(&self) -> bool {
        matches!(self, Node::Changed { .. })
    }
}

/// How a goal's rewritten form is reached from it, built once and emitted at
/// whatever binder depth and polarity its context needs.
pub(super) enum Plan {
    Same,
    /// `S(l, r)`, each side with its step when it changed.
    Relation { relation: Rc<Term>, left: Side, right: Side },
    /// `P → Q`: `from` and `to` are the implication before and after.
    Arrow { from: Type, to: Type, premise: Box<Plan>, conclusion: Box<Plan> },
}

pub(super) struct Side {
    from: Rc<Term>,
    to: Rc<Term>,
    /// `R(from, to)`; `None` when the side did not change.
    proof: Option<Rc<Term>>,
}

/// The congruence a node asks for: over its last argument, or its last two.
#[derive(Clone, Copy, PartialEq)]
enum Shape {
    Unary,
    Binary,
}

/// What resolution says about one context's congruence.
#[derive(Clone)]
enum Lookup {
    /// The context does not map the carrier to itself: no evidence of this
    /// shape can be stated.
    Untyped,
    /// Evidence, ready to apply to `x, x', h` (twice, for `Binary`).
    Found(Rc<Term>),
    /// The statement, which resolution did not prove.
    Missing(Type, Level),
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
    /// Keyed conversion is asked only of a left side headed by a global, as
    /// in the equation form (§6.2), and at most [`CANDIDATES`] times.
    keyed: bool,
    conversions: usize,
    occurrences: usize,
    /// Every node met, by identity, with the node kept alive so the address
    /// is not reused.
    memo: HashMap<*const Term, (Rc<Term>, Node)>,
    contexts: Vec<(Shape, Rc<Term>, Lookup)>,
    /// `Reflexive<C>(R)`'s `rel_refl`, once looked for.
    reflexive: Option<Option<Rc<Term>>>,
    /// Relation terms and the aliases that spell them.
    relations: Vec<(Rc<Term>, String)>,
    /// Goal-level class fields, by class, relations and field.
    fields: Vec<(&'static str, Vec<Rc<Term>>, Rc<Term>)>,
    serial: usize,
    goals: usize,
}

impl<'a> RelationRewrite<'a> {
    /// The step along `proof : R(lhs, rhs)`, or an error when `R` is not a
    /// relation on one carrier.
    pub(super) fn new(e: &'a Elaborator, cx: &'a Cx, span: Span, relation: Relation, proof: Term) -> R<Self> {
        let keyed = matches!(crate::spelling::app_spine(&relation.left).0, Term::GlobalTm { .. });
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
            keyed,
            conversions: 0,
            occurrences: 0,
            memo: HashMap::new(),
            contexts: Vec::new(),
            reflexive: None,
            relations: Vec::new(),
            fields: Vec::new(),
            serial: 0,
            goals: 0,
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
    pub(super) fn require_occurrence(&self, goal: &Type, what: &str) -> R<()> {
        if self.occurrences > 0 {
            return Ok(());
        }
        let hint = if goal.abstract_local(&self.rhs).is_some() {
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
                self.shown(&self.lhs)
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
            let Type::El { level, tm } = goal else { unreachable!("a relation is an `El`") };
            let left = self.term(&rel.left)?;
            let right = self.term(&rel.right)?;
            if !left.changed() && !right.changed() {
                return Ok((goal.clone(), Plan::Same));
            }
            let (_, args) = crate::spelling::app_spine(tm);
            let mut nodes = vec![Node::Same; args.len() - 2];
            nodes.extend([left.clone(), right.clone()]);
            let next = Type::El { level: level.clone(), tm: rebuild(tm, &nodes) };
            let side = |from: Rc<Term>, node: Node| match node {
                Node::Same => Side { to: Rc::clone(&from), from, proof: None },
                Node::Changed { term, proof } => Side { from, to: term, proof: Some(proof) },
            };
            let plan = Plan::Relation {
                relation: rel.head,
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
        if goal.abstract_local(&self.lhs).is_some() {
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
            Plan::Relation { relation, left, right } => {
                let r = Rc::clone(&self.relation);
                let mut acc = input;
                match polarity {
                    // From `S(l', r')`: `R(r, r')` turned round closes the
                    // right side, then `R(l, l')` the left.
                    Polarity::Backward => {
                        if let Some(pr) = &right.proof {
                            let back = self.symmetric(pr, &right.from, &right.to)?;
                            let chain = self.chain(relation, &r, relation)?;
                            acc = apply(up(&chain), [up(&left.to), up(&right.to), up(&right.from), acc, up(&back)]);
                        }
                        if let Some(pl) = &left.proof {
                            let chain = self.chain(&r, relation, relation)?;
                            acc = apply(up(&chain), [up(&left.from), up(&left.to), up(&right.from), up(pl), acc]);
                        }
                    }
                    // From `S(l, r)`: `R(l, l')` turned round opens the left
                    // side, then `R(r, r')` the right.
                    Polarity::Forward => {
                        if let Some(pl) = &left.proof {
                            let back = self.symmetric(pl, &left.from, &left.to)?;
                            let chain = self.chain(&r, relation, relation)?;
                            acc = apply(up(&chain), [up(&left.to), up(&left.from), up(&right.from), up(&back), acc]);
                        }
                        if let Some(pr) = &right.proof {
                            let chain = self.chain(relation, &r, relation)?;
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

    /// `t` rewritten, once per node.
    fn term(&mut self, t: &Rc<Term>) -> R<Node> {
        let key = Rc::as_ptr(t);
        if let Some((_, node)) = self.memo.get(&key) {
            return Ok(node.clone());
        }
        let node = self.node(t)?;
        self.memo.insert(key, (Rc::clone(t), node.clone()));
        Ok(node)
    }

    fn node(&mut self, t: &Rc<Term>) -> R<Node> {
        if self.is_occurrence(t) {
            self.occurrences += 1;
            return Ok(Node::Changed { term: Rc::clone(&self.rhs), proof: Rc::clone(&self.proof) });
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

    /// Is `t` the left side: itself, or a term with its global head whose
    /// arguments convert to its arguments, one by one? Argument-wise, not the
    /// whole term: the head is the same operation on both sides, so a miss
    /// would otherwise unfold it on both (rational arithmetic, say) only to
    /// compare the parts that differ — Lean's keyed matching likewise unfolds
    /// no head. A respelled argument (an implicit width) still matches.
    fn is_occurrence(&mut self, t: &Rc<Term>) -> bool {
        if Rc::ptr_eq(t, &self.lhs) {
            return true;
        }
        if !same_key(&self.lhs, t, 0) {
            return false;
        }
        if **t == *self.lhs {
            return true;
        }
        if !self.keyed || self.conversions >= CANDIDATES {
            return false;
        }
        self.conversions += 1;
        let (lhs_head, lhs_args) = crate::spelling::app_spine(&self.lhs);
        let (head, args) = crate::spelling::app_spine(t);
        head == lhs_head
            && args.iter().zip(&lhs_args).all(|(a, b)| a == b || self.e.terms_convert(self.original, b, a))
    }

    /// A node the walk does not enter: a binder, or a former that is no
    /// application. An occurrence inside one would be left behind, and half a
    /// rewrite is worse than none.
    fn opaque(&self, t: &Rc<Term>) -> R<Node> {
        let probe = Type::El { level: Level::Zero, tm: Rc::clone(t) };
        if probe.abstract_local(&self.lhs).is_none() {
            return Ok(Node::Same);
        }
        Err(ElabError::Elab {
            msg: format!(
                "`rewrite`: the left side{} occurs inside{}, under a binder or a form that is no \
                 application; a relation rewrite rewrites through applications only\n  \
                 hint: rewriting under a binder needs the pointwise relation \
                 (issues/rewrite-setoid-under-binders.md)",
                self.shown(&self.lhs),
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
        if n >= 2 && changed[0] >= n - 2 {
            let op = prefix(t, 2);
            let binary = self.lookup(Shape::Binary, &op)?;
            // A binary operation with only its last argument changed may have
            // unary evidence instead; with neither, the obligation is the
            // binary one, as `rel_cong` leaves it.
            let use_binary = match &binary {
                Lookup::Found(_) => true,
                Lookup::Untyped => false,
                Lookup::Missing(..) => {
                    changed != [last] || !matches!(self.lookup(Shape::Unary, &prefix(t, 1))?, Lookup::Found(_))
                }
            };
            if use_binary {
                let respects = self.discharge(Shape::Binary, &op)?;
                let (x, x2, hx) = self.side(args[n - 2], &nodes[n - 2])?;
                let (y, y2, hy) = self.side(args[last], &nodes[last])?;
                return Ok(Node::Changed { term, proof: apply(respects, [x, x2, hx, y, y2, hy]) });
            }
        }
        let [i] = changed[..] else {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`:{} changes in {} of its arguments; a relation rewrite has \
                     congruence over one argument (`PreservesRelation`) or over the last two \
                     (`Respects2`)",
                    self.shown(t),
                    changed.len()
                ),
                span: self.span,
            });
        };
        let context = if i == last { prefix(t, 1) } else { self.context(t, i) };
        if matches!(self.lookup(Shape::Unary, &context)?, Lookup::Untyped) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`: rewriting inside{} changes an argument of a context that does \
                     not map `{}` to itself; a relation rewrite stays in the relation's carrier",
                    self.shown(t),
                    self.e.display_type(self.original, &self.carrier),
                ),
                span: self.span,
            });
        }
        let preserves = self.discharge(Shape::Unary, &context)?;
        let Node::Changed { term: x2, proof: hx } = &nodes[i] else { unreachable!() };
        Ok(Node::Changed { term, proof: apply(preserves, [Rc::clone(args[i]), Rc::clone(x2), Rc::clone(hx)]) })
    }

    /// `x`, what it became, and `R(x, x')` — reflexivity for an argument that
    /// stayed.
    fn side(&mut self, x: &Rc<Term>, node: &Node) -> R<(Rc<Term>, Rc<Term>, Rc<Term>)> {
        Ok(match node {
            Node::Changed { term, proof } => (Rc::clone(x), Rc::clone(term), Rc::clone(proof)),
            Node::Same => (Rc::clone(x), Rc::clone(x), self.reflexivity(x)?),
        })
    }

    /// `λ z. f(…, z, …)` with `z` at argument `i` of `t`'s spine: the
    /// context of a change that is not in the last argument.
    fn context(&self, t: &Rc<Term>, i: usize) -> Rc<Term> {
        let (head, args) = crate::spelling::app_spine(t);
        let body = args.iter().enumerate().fold(Rc::new(head.shift_local(1)), |fun, (j, a)| {
            let arg = if j == i { Rc::new(Term::Var(LocalVar(0))) } else { Rc::new(a.shift_local(1)) };
            Rc::new(Term::AppAt { fun, arg })
        });
        Rc::new(Term::Lam {
            dom_level: self.level.clone(),
            cod_level: self.level.clone(),
            dom: Rc::clone(&self.carrier),
            body,
        })
    }

    // ---------------------------------------------------------------------
    // Evidence

    /// What resolution says about `context`'s congruence of `shape`, asked
    /// once per context.
    fn lookup(&mut self, shape: Shape, context: &Rc<Term>) -> R<Lookup> {
        if let Some((_, _, found)) = self.contexts.iter().find(|(s, c, _)| *s == shape && c == context) {
            return Ok(found.clone());
        }
        let c = self.carrier_name.clone();
        let operation = match shape {
            Shape::Unary => format!("{c} → {c}"),
            Shape::Binary => format!("{c} → {c} → {c}"),
        };
        let (op_ty, op_level) = self.statement(&operation)?;
        let found = if !self.checks(context, &op_ty, &op_level) {
            Lookup::Untyped
        } else {
            let op = self.alias(Rc::clone(context), op_ty, op_level);
            let rel = self.relation_alias(&Rc::clone(&self.relation))?;
            let statement = match shape {
                Shape::Unary => format!("relation_props::PreservesRelation({rel}, {rel}, {op})"),
                Shape::Binary => format!("algebra_rel::Respects2<{c}, {c}, {c}>({rel}, {rel}, {rel}, {op})"),
            };
            let (ty, level) = self.statement(&statement)?;
            match self.resolve(&ty, &level) {
                Some(ev) => Lookup::Found(self.applicable(shape, ev, ty, level)?),
                None => Lookup::Missing(ty, level),
            }
        };
        self.contexts.push((shape, Rc::clone(context), found.clone()));
        Ok(found)
    }

    /// The evidence for a context [`Self::lookup`] typed, an obligation when
    /// resolution did not find it.
    fn discharge(&mut self, shape: Shape, context: &Rc<Term>) -> R<Rc<Term>> {
        match self.lookup(shape, context)? {
            Lookup::Found(ev) => Ok(ev),
            Lookup::Untyped => unreachable!("discharged only once typed"),
            Lookup::Missing(ty, level) => {
                let goal = self.obligation(ty.clone(), level.clone(), "compatibility")?;
                let ev = self.applicable(shape, goal, ty, level)?;
                let entry = self.contexts.iter_mut().find(|(s, c, _)| *s == shape && c == context);
                entry.expect("looked up above").2 = Lookup::Found(Rc::clone(&ev));
                Ok(ev)
            }
        }
    }

    /// Evidence as a function of `x, x', h, …`: `PreservesRelation` is one,
    /// a `Respects2` dictionary through its field.
    fn applicable(&mut self, shape: Shape, ev: Term, ty: Type, level: Level) -> R<Rc<Term>> {
        match shape {
            Shape::Unary => Ok(Rc::new(ev)),
            Shape::Binary => self.project(ev, ty, level, "respects2"),
        }
    }

    /// `R(x, x)`: `Reflexive<C>(R)`'s field, or an obligation of its own, as
    /// `rel_cong` leaves an unchanged argument.
    fn reflexivity(&mut self, x: &Rc<Term>) -> R<Rc<Term>> {
        if self.reflexive.is_none() {
            let rel = self.relation_alias(&Rc::clone(&self.relation))?;
            let (ty, level) = self.statement(&format!("relation_props::Reflexive<{}>({rel})", self.carrier_name))?;
            self.reflexive = Some(match self.resolve(&ty, &level) {
                Some(dict) => Some(self.project(dict, ty, level, "rel_refl")?),
                None => None,
            });
        }
        if let Some(Some(refl)) = &self.reflexive {
            return Ok(apply(Rc::clone(refl), [Rc::clone(x)]));
        }
        let rel = self.relation_alias(&Rc::clone(&self.relation))?;
        let xa = self.alias(Rc::clone(x), (*self.carrier).clone(), self.level.clone());
        let (ty, level) = self.statement(&format!("{rel}({xa}, {xa})"))?;
        Ok(Rc::new(self.obligation(ty, level, "fixed")?))
    }

    /// `R(y, x)` from `p : R(x, y)`.
    fn symmetric(&mut self, p: &Rc<Term>, x: &Rc<Term>, y: &Rc<Term>) -> R<Rc<Term>> {
        let r = Rc::clone(&self.relation);
        let sym = self.class_field("Symmetric", &[r], "rel_sym", "symmetry")?;
        Ok(apply(sym, [Rc::clone(x), Rc::clone(y), Rc::clone(p)]))
    }

    /// The step that chains `first(x, y)` and `second(y, z)` into
    /// `goal(x, z)`: `Transitive`'s when all three are one relation, else
    /// `Trans`'s, the classes `calc` chains with.
    fn chain(&mut self, first: &Rc<Term>, second: &Rc<Term>, goal: &Rc<Term>) -> R<Rc<Term>> {
        if first == goal && second == goal {
            self.class_field("Transitive", &[Rc::clone(goal)], "rel_trans", "transitivity")
        } else {
            let relations = [Rc::clone(first), Rc::clone(second), Rc::clone(goal)];
            self.class_field("Trans", &relations, "rel_chain", "transitivity")
        }
    }

    /// `class<C>(relations…)`'s `field`, resolved or an obligation, once.
    fn class_field(&mut self, class: &'static str, relations: &[Rc<Term>], field: &str, label: &str) -> R<Rc<Term>> {
        if let Some((_, _, t)) = self.fields.iter().find(|(c, rs, _)| *c == class && rs.as_slice() == relations) {
            return Ok(Rc::clone(t));
        }
        let mut names = Vec::new();
        for r in relations {
            names.push(self.relation_alias(r)?);
        }
        let (ty, level) =
            self.statement(&format!("relation_props::{class}<{}>({})", self.carrier_name, names.join(", ")))?;
        let dict = match self.resolve(&ty, &level) {
            Some(dict) => dict,
            None => self.obligation(ty.clone(), level.clone(), label)?,
        };
        let projected = self.project(dict, ty, level, field)?;
        self.fields.push((class, relations.to_vec(), Rc::clone(&projected)));
        Ok(projected)
    }

    fn resolve(&self, ty: &Type, level: &Level) -> Option<Term> {
        self.e.resolve_goal(
            &self.cx,
            ty,
            level,
            &self.e.display_type(self.original, ty),
            None,
            self.span,
            &mut Vec::new(),
        )
    }

    fn obligation(&mut self, ty: Type, level: Level, label: &str) -> R<Term> {
        self.goals += 1;
        self.e.relation_obligation(self.original, "rewrite", label, self.goals - 1, ty, level, self.span)
    }

    /// `dict.field`, elaborated as written.
    fn project(&mut self, dict: Term, ty: Type, level: Level, field: &str) -> R<Rc<Term>> {
        let name = self.alias(Rc::new(dict), ty, level);
        let source = format!("fn generated() -> Type {{ {name}.{field} }}");
        let mut file = parse_file(&source).map_err(|e| ElabError::Elab { msg: e.msg, span: self.span })?;
        let Some(Item::Decl(d)) = file.items.pop() else { unreachable!("one declaration") };
        let (term, _, _) = self.e.generated_scope(|e| e.elab_infer(&self.cx, &d.body.result))?;
        Ok(Rc::new(term))
    }

    // ---------------------------------------------------------------------
    // Spelling evidence statements

    /// A type written as text in `cx`: an evidence statement over the
    /// carrier and aliases.
    fn statement(&self, text: &str) -> R<(Type, Level)> {
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
        if let Some((_, name)) = self.relations.iter().find(|(t, _)| t == r) {
            return Ok(name.clone());
        }
        let c = &self.carrier_name;
        let (ty, level) = self.statement(&format!("{c} → {c} → Type"))?;
        if !self.checks(r, &ty, &level) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`rewrite`:{} is not a relation on `{}` alone; a relation rewrite needs \
                     a non-dependent `C → C → Type`",
                    self.shown(r),
                    self.e.display_type(self.original, &self.carrier),
                ),
                span: self.span,
            });
        }
        let name = self.alias(Rc::clone(r), ty, level);
        self.relations.push((Rc::clone(r), name.clone()));
        Ok(name)
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
                && !self.cx.aliases.iter().any(|a| a.name == name)
                && !self.cx.tyvars.iter().any(|a| a.name == name)
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
        self.e.spell_term_clean(self.original, t).map_or_else(String::new, |s| format!(" `{s}`"))
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
