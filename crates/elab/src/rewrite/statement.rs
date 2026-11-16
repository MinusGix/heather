//! A simplifier's step along a law between statements, `P ↔ Q`
//! (`docs/tactics/simp-design.md` §12, `issues/simp-iff-laws.md`).
//!
//! The term walk (`relation.rs`) rewrites terms inside a goal, across term
//! operations that carry congruence evidence. A statement's contexts are
//! type formers, and each has one congruence for `↔` that `logic` proves
//! once: `iff_and_congr`, `iff_or_congr`, `iff_imp_congr`, `iff_not_congr`,
//! `iff_iff_congr`, and `iff_forall_congr` and `iff_exists_congr` below a
//! quantifier. So this walk is over
//! the statement: the goal itself, the operands of `∧`, `∨`, `↔`, `¬` and a
//! non-dependent `→`, and the body of a `∀` or an `∃`, one binder down.
//!
//! Each position is matched against the law's left side on its own, so two
//! positions may be two instances (nothing is abstracted, as a `J` motive
//! or a relation's shared node would need). A position that is an instance
//! is not walked into: the driver's next step sees what replaced it.
//!
//! A law that is an equation or a relation step reaches the same positions:
//! where it fires at an operand (`Leaf`, the driver's own step there), its
//! two directions are that operand's `↔`, and the congruences carry it out
//! (`Statements::within`). The lowering of `∧` and `∨` puts an operand
//! below a binder, where the equation form's motive does not look.
//!
//! The result is a proof of `goal ↔ next`, written as calls of the
//! congruences over aliases for the parts, and its two directions as
//! functions. Nothing is trusted: the declaration gate checks the whole.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Item, Span, parse_file};

use super::{Miss, Premise, Rewrites, instantiate, same_key};
use crate::inductive::Inductives;
use crate::{Alias, Cx, ElabError, Elaborator, R, TyVar};

/// Statement rewriting's part of the elaborator.
pub(super) struct Statements<'e>(pub(super) &'e Elaborator);

impl std::ops::Deref for Statements<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

/// A law `(x₁ … xₖ) → P ↔ Q` read at a context: its binders' types,
/// outermost first, and `P`, scoped below them.
struct Law {
    k: u32,
    telescope: Vec<(Type, Level)>,
    left: Type,
    /// The context `left` is scoped in: the law's, then its binders.
    below: Cx,
}

/// A statement that changed: what it became, and the proof of
/// `Iff<it, to>` with its type and level.
struct Changed {
    to: Type,
    iff: Term,
    iff_ty: Type,
    iff_level: Level,
}

/// One step: the goal after it, the two directions of `goal ↔ next` as
/// functions with their types, and the first instance's two sides.
pub(super) struct StatementStep {
    pub(super) next: Type,
    /// `goal → next`.
    pub(super) forward: (Term, Type),
    /// `next → goal`.
    pub(super) backward: (Term, Type),
    /// As a route prints them, spelled where the instance was found.
    pub(super) sides: Option<(String, String)>,
}

/// A step some other form took at one operand: what the operand became and
/// the two directions between them, as functions.
pub(super) struct Leaf {
    pub(super) to: Type,
    pub(super) forward: Term,
    pub(super) backward: Term,
    pub(super) sides: Option<(String, String)>,
}

/// The step at an operand, in its context, that many binders below the
/// goal's: `Err` is why the law is blocked there.
pub(super) type LeafStep<'f> = &'f dyn Fn(&Cx, u32, &Type, &Level) -> R<Result<Option<Leaf>, String>>;

/// What a walk rewrites its positions by.
enum By<'f, 'p> {
    /// A law between statements, read at the walk's context.
    Law { law: Law, proof: Term, proof_ty: Type, premise: Option<Premise<'p>> },
    /// Another form's step, at the operands of the goal.
    Leaf(LeafStep<'f>),
}

pub(super) enum StatementOutcome {
    Fired(Box<StatementStep>),
    Blocked(String),
    Miss,
}

#[derive(Clone, Copy)]
enum Connective {
    And,
    Or,
    Iff,
}

impl Connective {
    fn congruence(self) -> &'static str {
        match self {
            Connective::And => "iff_and_congr",
            Connective::Or => "iff_or_congr",
            Connective::Iff => "iff_iff_congr",
        }
    }
}

impl Statements<'_> {
    /// Is `ty`, below any binders, a statement `P ↔ Q` as written?
    pub(super) fn is_law(&self, cx: &Cx, ty: &Type, span: Span) -> bool {
        matches!(self.law(cx, ty, span), Ok(Some(_)))
    }

    /// The two sides of `ty` when it is `Iff<P, Q>`, each with its level.
    pub(super) fn iff_sides(&self, cx: &Cx, ty: &Type) -> Option<[(Type, Level); 2]> {
        let inline = self.inline(cx, ty)?;
        if !self.display_tag_of(&inline).is_some_and(|ind| matches!(ind.name.as_str(), "Iff" | "logic::Iff")) {
            return None;
        }
        // `record Iff<P, Q> { mp: P → Q, mpr: Q → P }` lowers to its tag,
        // then its fields: `Σ(tag). Σ(P → Q). Σ(Q → P). Unit`.
        let Type::Sigma { fst: tag, fst_level, snd: fields, .. } = &inline else { return None };
        let Type::Sigma { fst: mp, .. } = &**fields else { return None };
        let Type::Pi { dom_level, cod_level, dom, cod } = &**mp else { return None };
        let mut below = cx.clone();
        below.push("_".into(), (**tag).clone(), fst_level.clone());
        let left = crate::strengthen_ty(&below.gamma, dom, 1)?;
        below.push("_".into(), (**dom).clone(), dom_level.clone());
        let right = crate::strengthen_ty(&below.gamma, cod, 2)?;
        Some([(left, dom_level.clone()), (right, cod_level.clone())])
    }

    /// `ty` as the type former its declaration lowers to, when it names one.
    fn inline(&self, cx: &Cx, ty: &Type) -> Option<Type> {
        let former = |t: &Type| matches!(t, Type::Sigma { .. } | Type::Sum { .. } | Type::Wf { .. });
        if former(ty) {
            return Some(ty.clone());
        }
        if !matches!(ty, Type::El { .. }) {
            return None;
        }
        if let Some(inline) = self.unspell_here(ty).filter(former) {
            return Some(inline);
        }
        // Never by unfolding: a relation defined as a `↔` (`Same(a, b)`)
        // is that relation where it is written.
        let _ = cx;
        None
    }

    /// `ty` as `Exists<A>(λ x. B(x))`: the binder's type and level, and the
    /// body as a code, one binder down. `record Exists<A>(P: A → Type)
    /// { witness: A, proof: P(witness) }` lowers to its tag, then its
    /// fields, `Σ(tag). Σ(A). Σ(El(P(witness))). Unit`, with the predicate
    /// applied and not contracted.
    fn existential(&self, cx: &Cx, ty: &Type) -> Option<(Rc<Type>, Level, Rc<Term>)> {
        let inline = self.inline(cx, ty)?;
        if !self.display_tag_of(&inline).is_some_and(|ind| matches!(ind.name.as_str(), "Exists" | "logic::Exists")) {
            return None;
        }
        let Type::Sigma { fst: tag, fst_level: tag_level, snd: fields, .. } = &inline else { return None };
        let Type::Sigma { fst: witness, fst_level: dom_level, snd: rest, .. } = &**fields else { return None };
        let Type::Sigma { fst: proof, .. } = &**rest else { return None };
        let Type::El { tm, .. } = &**proof else { return None };
        let (predicate, at) = crate::spelling::app_of(tm)?;
        if !matches!(&**at, Term::Var(x) if x.0 == 0) {
            return None;
        }
        let mut below = cx.clone();
        below.push("_".into(), (**tag).clone(), tag_level.clone());
        let dom = crate::strengthen_ty(&below.gamma, witness, 1)?;
        below.push("_".into(), (**witness).clone(), dom_level.clone());
        let Term::Lam { body, .. } = crate::strengthen_tm(&below.gamma, predicate, 2)? else { return None };
        Some((Rc::new(dom), dom_level.clone(), body))
    }

    /// `ty` as `A ∧ B`, `A ∨ B` or `A ↔ B`, with its operands.
    fn connective(&self, cx: &Cx, ty: &Type) -> Option<(Connective, [(Type, Level); 2])> {
        if let Some(sides) = self.iff_sides(cx, ty) {
            return Some((Connective::Iff, sides));
        }
        let inline = self.inline(cx, ty)?;
        let ind = self.display_tag_of(&inline)?;
        let which = match ind.name.as_str() {
            "And" | "logic::And" => Connective::And,
            "Or" | "logic::Or" => Connective::Or,
            _ => return None,
        };
        let targs = Inductives(self.0).display_targs(cx, &inline, &ind)?;
        let [a, b] = <[(Type, Level); 2]>::try_from(targs).ok()?;
        Some((which, [a, b]))
    }

    fn law(&self, cx: &Cx, ty: &Type, span: Span) -> R<Option<Law>> {
        let mut pcx = cx.clone();
        let mut k = 0u32;
        let mut telescope = Vec::new();
        let mut cur = ty.clone();
        loop {
            if let Some([(left, _), _]) = self.iff_sides(&pcx, &cur) {
                return Ok(Some(Law { k, telescope, left, below: pcx }));
            }
            // A relation's application is a relation step, whatever the
            // relation unfolds to.
            if matches!(cur, Type::Id { .. }) || crate::relational_context::proof::Relation::of_type(self.0, &pcx, &cur, span).is_some() {
                return Ok(None);
            }
            match self.whnf(&pcx, &cur, span)? {
                Type::Pi { dom_level, dom, cod, .. } if k < super::MAX_OPEN => {
                    telescope.push(((*dom).clone(), dom_level.clone()));
                    pcx.push(format!("_{k}"), (*dom).clone(), dom_level);
                    k += 1;
                    cur = (*cod).clone();
                }
                _ => return Ok(None),
            }
        }
    }

    /// One law `proof : proof_ty` at `goal`: every position that is an
    /// instance of its left side rewritten to the right side.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn step(
        &self,
        cx: &Cx,
        name: &str,
        proof: &Term,
        proof_ty: &Type,
        goal: &Type,
        lvl: &Level,
        premise: Option<Premise<'_>>,
        span: Span,
    ) -> R<StatementOutcome> {
        let Some(law) = self.law(cx, proof_ty, span)? else { return Ok(StatementOutcome::Miss) };
        if law.k > 0 && matches!(&law.left, Type::El { tm, .. } if matches!(&**tm, Term::Var(x) if x.0 < law.k)) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`simp_only`: the left side of {name} is one of its own arguments, so it \
                     would match every statement; apply the law to that argument"
                ),
                span,
            });
        }
        let by = By::Law { law, proof: proof.clone(), proof_ty: proof_ty.clone(), premise };
        self.walked(Walk { e: self.0, cx: cx.clone(), by, span, depth: 0, entered: false, serial: 0, first: None, blocked: None }, goal, lvl)
    }

    /// `goal` with `leaf`'s step taken at each operand it fires at: below
    /// `∧`, `∨`, `↔`, `¬`, `→` and `∀`, never at the goal itself, which is
    /// the caller's own step.
    pub(super) fn within(&self, cx: &Cx, goal: &Type, lvl: &Level, leaf: LeafStep<'_>, span: Span) -> R<StatementOutcome> {
        self.walked(Walk { e: self.0, cx: cx.clone(), by: By::Leaf(leaf), span, depth: 0, entered: false, serial: 0, first: None, blocked: None }, goal, lvl)
    }

    fn walked(&self, mut walk: Walk<'_, '_, '_>, goal: &Type, lvl: &Level) -> R<StatementOutcome> {
        let Some(changed) = walk.statement(goal, lvl)? else {
            return Ok(match walk.blocked {
                Some(why) => StatementOutcome::Blocked(why),
                None => StatementOutcome::Miss,
            });
        };
        if changed.to == *goal {
            return Ok(StatementOutcome::Miss);
        }
        let h = walk.alias(changed.iff, changed.iff_ty, changed.iff_level);
        let (mp, mp_ty, _) = walk.expr(&format!("{h}.mp"))?;
        let (mpr, mpr_ty, _) = walk.expr(&format!("{h}.mpr"))?;
        Ok(StatementOutcome::Fired(Box::new(StatementStep {
            next: changed.to,
            forward: (mp, mp_ty),
            backward: (mpr, mpr_ty),
            sides: walk.first,
        })))
    }
}

struct Walk<'a, 'f, 'p> {
    e: &'a Elaborator,
    /// The context of the statement being walked, with every part a
    /// congruence call mentions as an alias or a type variable.
    cx: Cx,
    by: By<'f, 'p>,
    span: Span,
    /// Binders below the goal's own context.
    depth: u32,
    /// The walk is past the goal itself.
    entered: bool,
    serial: usize,
    /// The first instance's two sides, spelled where it was found.
    first: Option<(String, String)>,
    blocked: Option<String>,
}

impl Walk<'_, '_, '_> {
    fn statements(&self) -> Statements<'_> {
        Statements(self.e)
    }

    /// `ty` rewritten, or `None` where no position in it is an instance.
    fn statement(&mut self, ty: &Type, lvl: &Level) -> R<Option<Changed>> {
        let here = match &self.by {
            By::Law { .. } => self.instance(ty, lvl)?,
            // The goal itself is the caller's.
            By::Leaf(_) if !self.entered => None,
            By::Leaf(leaf) => match leaf(&self.cx, self.depth, ty, lvl)? {
                Ok(Some(leaf)) => self.packaged(ty, lvl, leaf)?,
                Ok(None) => None,
                Err(why) => {
                    self.blocked.get_or_insert(why);
                    None
                }
            },
        };
        self.entered = true;
        if let Some(changed) = here {
            return Ok(Some(changed));
        }
        if let Some((which, [(a, al), (b, bl)])) = self.statements().connective(&self.cx, ty) {
            let left = self.statement(&a, &al)?;
            let right = self.statement(&b, &bl)?;
            if left.is_none() && right.is_none() {
                return Ok(None);
            }
            let (pa, pb) = (self.operand(&a, &al, left), self.operand(&b, &bl, right));
            return self.congruence(ty, lvl, &format!("{}({pa}, {pb})", which.congruence()));
        }
        if let Type::Pi { dom_level, cod_level, dom, cod } = ty {
            let mut below = self.cx.clone();
            below.push(self.binder(), (**dom).clone(), dom_level.clone());
            if let Some(conclusion) = crate::strengthen_ty(&below.gamma, cod, 1) {
                let premise = self.statement(dom, dom_level)?;
                let concluded = self.statement(&conclusion, cod_level)?;
                if premise.is_none() && concluded.is_none() {
                    return Ok(None);
                }
                let (pa, pb) = (self.operand(dom, dom_level, premise), self.operand(&conclusion, cod_level, concluded));
                return self.congruence(ty, lvl, &format!("iff_imp_congr({pa}, {pb})"));
            }
            return self.quantifier(ty, lvl, below, dom_level, cod_level, dom, cod, false);
        }
        if let Some((dom, dom_level, body)) = self.statements().existential(&self.cx, ty) {
            // The predicate's body is a code at `Ty l`: a statement at `l`.
            let mut below = self.cx.clone();
            below.push(self.binder(), (*dom).clone(), dom_level.clone());
            let oracle = self.e.semantic_oracle();
            let Ok((Type::Ty(body_level), _)) =
                heather_kernel::typing::infer_term(oracle.world(), 0, Layer::Prog, &below.gamma, &body, self.e.policy.fuel)
            else {
                return Ok(None);
            };
            let body_ty = Type::El { level: body_level.clone(), tm: body };
            return self.quantifier(ty, lvl, below, &dom_level, &body_level, &dom, &body_ty, true);
        }
        // `¬P`: a call of `Not` as written, and not a definition that
        // unfolds to one.
        if matches!(ty, Type::El { tm, .. } if crate::spelling::app_spine(tm).1.len() == 1)
            && let Type::Pi { dom_level, dom, .. } = self.e.whnf(&self.cx, ty, self.span)?
            && self.is_negation(ty, &dom, &dom_level)
        {
            let Some(inner) = self.statement(&dom, &dom_level)? else { return Ok(None) };
            let pa = self.operand(&dom, &dom_level, Some(inner));
            return self.congruence(ty, lvl, &format!("iff_not_congr({pa})"));
        }
        Ok(None)
    }

    /// `(x: A) → B(x)`, or `Exists(λ x. B(x))` when `exists`, with `B`
    /// rewritten one binder down.
    #[allow(clippy::too_many_arguments)]
    fn quantifier(
        &mut self,
        ty: &Type,
        lvl: &Level,
        below: Cx,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Rc<Type>,
        cod: &Type,
        exists: bool,
    ) -> R<Option<Changed>> {
        // A law is read again one binder down; a leaf is told the depth.
        let deeper = match &self.by {
            By::Law { proof, proof_ty, premise, .. } => {
                let (proof, proof_ty) = (proof.shift_local(1), proof_ty.shift_local(1));
                let Some(law) = self.statements().law(&below, &proof_ty, self.span)? else { return Ok(None) };
                By::Law { law, proof, proof_ty, premise: *premise }
            }
            By::Leaf(leaf) => By::Leaf(*leaf),
        };
        let outer_cx = std::mem::replace(&mut self.cx, below);
        let outer_by = std::mem::replace(&mut self.by, deeper);
        self.depth += 1;
        let body = self.statement(cod, cod_level);
        self.depth -= 1;
        self.cx = outer_cx;
        self.by = outer_by;
        let Some(body) = body? else { return Ok(None) };
        // `λ x. body : (x: A) → B(x) ↔ B'(x)`.
        let pointwise = Term::Lam {
            dom_level: dom_level.clone(),
            cod_level: body.iff_level.clone(),
            dom: Rc::clone(dom),
            body: Rc::new(body.iff),
        };
        let pointwise_ty = Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: body.iff_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::new(body.iff_ty),
        };
        let level = Level::max(dom_level.clone(), body.iff_level);
        // The two predicates, `λ x. ⌜B(x)⌝` and `λ x. ⌜B'(x)⌝`.
        let (Some(before), Some(after)) = (crate::code::code_of(cod), crate::code::code_of(&body.to)) else { return Ok(None) };
        let predicate = |w: &mut Self, code: Term| {
            let p = Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: Level::succ(cod_level.clone()),
                dom: Rc::clone(dom),
                body: Rc::new(code),
            };
            let (p_ty, p_level) = w.infer(&p)?;
            Some(w.alias(p, p_ty, p_level))
        };
        let (Some(p), Some(q)) = (predicate(self, before), predicate(self, after)) else { return Ok(None) };
        let h = self.alias(pointwise, pointwise_ty, level);
        if exists {
            // What the goal becomes is the former at the new predicate, as
            // the elaborator writes it.
            let source = format!("fn generated(x: Exists({q})) -> Type {{ Type }}");
            let Ok(mut file) = parse_file(&source) else { return Ok(None) };
            let Some(Item::Decl(d)) = file.items.pop() else { return Ok(None) };
            let Ok((to, _)) = self.e.generated_scope(|e| e.elab_ty(&self.cx, &d.params[0].ty)) else { return Ok(None) };
            return Ok(self.congruence(ty, lvl, &format!("iff_exists_congr({p}, {q}, {h})"))?.map(|c| Changed { to, ..c }));
        }
        // The congruence states its right side as `(x: A) → Q(x)` at the
        // predicate `Q`, a β-redex in the body: what the goal becomes is
        // the body as rewritten.
        let to = Type::Pi { dom_level: dom_level.clone(), cod_level: cod_level.clone(), dom: Rc::clone(dom), cod: Rc::new(body.to) };
        Ok(self.congruence(ty, lvl, &format!("iff_forall_congr({p}, {q}, {h})"))?.map(|c| Changed { to, ..c }))
    }

    /// What a congruence call takes for an operand: the alias of its proof,
    /// or reflexivity where it did not change.
    fn operand(&mut self, ty: &Type, level: &Level, changed: Option<Changed>) -> String {
        match changed {
            Some(c) => self.alias(c.iff, c.iff_ty, c.iff_level),
            None => {
                let t = self.tyvar(ty, level);
                format!("iff_refl<{t}>()")
            }
        }
    }

    /// The congruence `text` proves `ty ↔ to`, for the `to` it states.
    fn congruence(&mut self, ty: &Type, lvl: &Level, text: &str) -> R<Option<Changed>> {
        let (iff, iff_ty, iff_level) = self.expr(text).map_err(|e| ElabError::Elab {
            msg: format!(
                "`simp_only`: a law between statements rewrites inside a connective by \
                 `logic`'s congruences for `↔`, and `{text}` did not elaborate: {}",
                e.message()
            ),
            span: self.span,
        })?;
        let Some([(from, _), (to, _)]) = self.statements().iff_sides(&self.cx, &iff_ty) else {
            return Ok(None);
        };
        if from != *ty && !self.e.conv_types(&self.cx, &from, ty, lvl) {
            return Ok(None);
        }
        Ok(Some(Changed { to, iff, iff_ty, iff_level }))
    }

    /// `ty` as an instance of the law's left side.
    fn instance(&mut self, ty: &Type, lvl: &Level) -> R<Option<Changed>> {
        let By::Law { law, proof, proof_ty, premise } = &self.by else { return Ok(None) };
        let k = law.k;
        let mut binds = vec![None; k as usize];
        if !self.matches(law, ty, lvl, &mut binds) {
            return Ok(None);
        }
        let not_a_law = |ty: &Type| ElabError::Elab {
            msg: format!("internal: `simp_only`: `{}` stopped being a law", self.e.display_type(&self.cx, ty)),
            span: self.span,
        };
        let rw = Rewrites(self.e);
        let (iff, iff_ty) = match rw.instantiated(&self.cx, proof.clone(), proof_ty, k, &binds, *premise, self.span, &not_a_law) {
            Ok(found) => found,
            Err(Miss::NoInstance) => return Ok(None),
            Err(Miss::Unbound { premise: Some((p, _)), .. }) => {
                let why = format!(
                    "its side condition `{}` is not a hypothesis here, and nothing discharged it",
                    self.e.display_type(&self.cx, &p)
                );
                self.blocked.get_or_insert(why);
                return Ok(None);
            }
            Err(Miss::Unbound { index, .. }) => {
                let why = format!("matching its left side does not determine its argument {index}; apply the law to it");
                self.blocked.get_or_insert(why);
                return Ok(None);
            }
            Err(Miss::Hard(e)) => return Err(e),
        };
        let Some([(from, from_level), (to, to_level)]) = self.statements().iff_sides(&self.cx, &iff_ty) else {
            return Ok(None);
        };
        if from != *ty && !self.e.conv_types(&self.cx, &from, ty, lvl) {
            return Ok(None);
        }
        if from_level != to_level {
            self.blocked.get_or_insert("its two sides are statements at different universe levels".to_string());
            return Ok(None);
        }
        let Some((_, iff_level)) = self.infer(&iff) else { return Ok(None) };
        // The right side as its declaration's reference, where the law's
        // own type had it lowered: what a code of it is read from.
        let to = crate::gendefs::GeneratedDefs(self.e).respell_ty_deep(&self.cx, &to, 0).unwrap_or(to);
        let sides = (self.e.display_type(&self.cx, &from), self.e.display_type(&self.cx, &to));
        self.first.get_or_insert(sides);
        Ok(Some(Changed { to, iff, iff_ty, iff_level }))
    }

    /// Does the law's left side match `ty`? Its arguments go to `binds`.
    fn matches(&self, law: &Law, ty: &Type, lvl: &Level, binds: &mut [Option<Rc<Term>>]) -> bool {
        let k = law.k;
        let left = &law.left;
        if k == 0 {
            if left == ty {
                return true;
            }
            return match (crate::code::code_of(left), crate::code::code_of(ty)) {
                (Some(l), Some(t)) => same_key(&l, &t, 0) && self.e.conv_types(&self.cx, left, ty, lvl),
                _ => false,
            };
        }
        let rw = Rewrites(self.e);
        let mut deferred = Vec::new();
        if !self.matches_at(law, left, ty, binds, &mut deferred) {
            return false;
        }
        if !rw.bind_dictionaries(&self.cx, k, binds, &law.telescope, self.span) {
            return false;
        }
        deferred.into_iter().all(|(p, t)| match instantiate(&self.cx.gamma, &p, k, binds) {
            Some(p) => p == *t || rw.terms_convert(&self.cx, &p, &t),
            None => false,
        })
    }

    /// Structural matching of a statement pattern: an equation by its two
    /// sides, a statement variable by the whole statement, anything else by
    /// its code's application spine.
    fn matches_at(&self, law: &Law, pat: &Type, ty: &Type, binds: &mut [Option<Rc<Term>>], deferred: &mut Vec<(Term, Rc<Term>)>) -> bool {
        let k = law.k;
        let rw = Rewrites(self.e);
        if let (Type::Id { lhs: pl, rhs: pr, .. }, Type::Id { lhs, rhs, .. }) = (pat, ty) {
            return rw.match_spine(&self.cx, pl, lhs, k, binds, deferred) && rw.match_spine(&self.cx, pr, rhs, k, binds, deferred);
        }
        let variable = matches!(pat, Type::El { tm, .. } if matches!(&**tm, Term::Var(x) if x.0 < k));
        // A connective in the pattern (`P ∧ True ↔ P`) is matched operand
        // by operand: its type arguments are in a lowering, not on a spine.
        if !variable && let Some((which, [(pa, _), (pb, _)])) = self.statements().connective(&law.below, pat) {
            let Some((found, [(a, _), (b, _)])) = self.statements().connective(&self.cx, ty) else { return false };
            return which as u8 == found as u8 && self.matches_at(law, &pa, &a, binds, deferred) && self.matches_at(law, &pb, &b, binds, deferred);
        }
        if let (Type::Pi { dom: pd, dom_level, cod: pc, .. }, Type::Pi { dom, cod, .. }) = (pat, ty) {
            let mut below = law.below.clone();
            below.push("_".into(), (**pd).clone(), dom_level.clone());
            let mut here = self.cx.clone();
            here.push("_".into(), (**dom).clone(), dom_level.clone());
            let (Some(pc), Some(cod)) = (crate::strengthen_ty(&below.gamma, pc, 1), crate::strengthen_ty(&here.gamma, cod, 1)) else {
                return false;
            };
            return self.matches_at(law, pd, dom, binds, deferred) && self.matches_at(law, &pc, &cod, binds, deferred);
        }
        let (Some(p), Some(t)) = (crate::code::code_of(pat), crate::code::code_of(ty)) else { return false };
        if !variable && !same_key(&p, &t, k) {
            return false;
        }
        rw.match_spine(&self.cx, &p, &Rc::new(t), k, binds, deferred)
    }

    /// A leaf's two directions as the `↔` between the operand and what it
    /// became.
    fn packaged(&mut self, ty: &Type, lvl: &Level, leaf: Leaf) -> R<Option<Changed>> {
        let (Some((forward_ty, forward_level)), Some((backward_ty, backward_level))) = (self.infer(&leaf.forward), self.infer(&leaf.backward))
        else {
            return Ok(None);
        };
        let from = self.tyvar(ty, lvl);
        let to = self.tyvar(&leaf.to, lvl);
        let forward = self.alias(leaf.forward, forward_ty, forward_level);
        let backward = self.alias(leaf.backward, backward_ty, backward_level);
        let (iff, iff_ty, iff_level) = self.expr(&format!("iff_of<{from}, {to}>({forward}, {backward})"))?;
        if let Some(sides) = leaf.sides {
            self.first.get_or_insert(sides);
        }
        Ok(Some(Changed { to: leaf.to, iff, iff_ty, iff_level }))
    }

    /// Is `ty`, which unfolds to `dom → False`, the call `Not(dom)` itself?
    fn is_negation(&mut self, ty: &Type, dom: &Type, dom_level: &Level) -> bool {
        let t = self.tyvar(dom, dom_level);
        let source = format!("fn generated(x: Not({t})) -> Type {{ Type }}");
        let Ok(mut file) = parse_file(&source) else { return false };
        let Some(Item::Decl(d)) = file.items.pop() else { return false };
        let Ok((written, _)) = self.e.generated_scope(|e| e.elab_ty(&self.cx, &d.params[0].ty)) else { return false };
        match (crate::code::code_of(&written), crate::code::code_of(ty)) {
            (Some(w), Some(t)) => same_key(&w, &t, 0),
            _ => false,
        }
    }

    /// The kernel's type of `t` here.
    fn infer(&self, t: &Term) -> Option<(Type, Level)> {
        let oracle = self.e.semantic_oracle();
        heather_kernel::typing::infer_term(oracle.world(), 0, Layer::Prog, &self.cx.gamma, t, self.e.policy.fuel).ok()
    }

    /// An expression written as text in `cx`, inferred.
    fn expr(&self, text: &str) -> R<(Term, Type, Level)> {
        let source = format!("fn generated() -> Type {{ {text} }}");
        let mut file = parse_file(&source).map_err(|e| ElabError::Elab { msg: e.msg, span: self.span })?;
        let Some(Item::Decl(d)) = file.items.pop() else { unreachable!("one declaration") };
        self.e.generated_scope(|e| e.elab_infer(&self.cx, &d.body.result))
    }

    fn tyvar(&mut self, ty: &Type, level: &Level) -> String {
        let name = self.fresh();
        self.cx.tyvars.push(TyVar { name: name.clone(), ty: ty.clone(), level: level.clone(), depth: self.cx.names.len() });
        name
    }

    fn alias(&mut self, term: Term, ty: Type, level: Level) -> String {
        let name = self.fresh();
        self.cx.aliases.push(Rc::new(Alias {
            name: name.clone(),
            depth: self.cx.names.len(),
            term: Rc::new(term),
            ty,
            level,
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        name
    }

    /// A name for the binder of a `∀` the walk goes below: what a route
    /// calls it.
    fn binder(&self) -> String {
        let free = |name: &str| !self.cx.names.contains(name);
        std::iter::once("x".to_string()).chain((1..).map(|i| format!("x{i}"))).find(|name| free(name)).expect("an unused name")
    }

    fn fresh(&mut self) -> String {
        loop {
            let name = format!("__statement_{}", self.serial);
            self.serial += 1;
            if !self.cx.names.contains(&name)
                && !self.cx.aliases.iter_inner().any(|a| a.name == name)
                && !self.cx.tyvars.iter_inner().any(|a| a.name == name)
            {
                return name;
            }
        }
    }
}
