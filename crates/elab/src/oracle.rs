//! Typed access to the kernel's semantic operations.
//!
//! The elaborator uses several global worlds, but reduction and conversion
//! must always receive one world together with one fuel policy. Diagnostic
//! decoding shares that input while deliberately having a different failure
//! contract: it declines instead of turning exhaustion into an error.

use std::sync::Arc as Rc;

use heather_kernel::conv::{self, ConvError};
use heather_kernel::eval;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{self, Defs, OutOfFuel};
use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, Term, Type};
use heather_kernel::value::{Head, VTy, Val, ValueArena};

use crate::readback::Readback;

/// Steps the small-step reducer may spend on the *spelling* of a head the
/// value machine has already found stuck. See [`SemanticOracle::whnf_type`]:
/// past this budget the input itself is the answer.
const STUCK_SPELLING_STEPS: u64 = 64;

/// A kernel world used for semantic elaboration decisions.
#[derive(Clone)]
pub(crate) struct SemanticOracle {
    world: GlobalCtx,
    fuel: u64,
}

impl SemanticOracle {
    /// Use an already-complete global world, such as the goal arena's real Ψ.
    pub(crate) fn in_world(world: GlobalCtx, fuel: u64) -> Self {
        Self { world, fuel }
    }

    /// Extend a cached base world with dynamic meta binders.
    pub(crate) fn with_dynamic(base: &GlobalCtx, dynamic: &[GlobalBinding], fuel: u64) -> Self {
        if dynamic.is_empty() {
            return Self::in_world(base.clone(), fuel);
        }
        Self::in_world(base.extended(dynamic.iter().cloned()), fuel)
    }

    pub(crate) fn world(&self) -> &GlobalCtx {
        &self.world
    }

    /// The δ-transparent weak head normal form of a type, as the elaborator's
    /// head-shape probes want it: "is this a Π", "is this a universe", "which
    /// former is this".
    ///
    /// The answer is *decided* in the value domain; the small-step reducer
    /// only spells what the value cannot. `reduce::whnf_type_delta` rewrites terms, so on a
    /// type whose head is a computing `fn … → Type` over a computed argument
    /// (`El^0(Le(x, dot(row, atoms)))`: `Le` at `Int` unfolds to a `match`
    /// on the dot product) it evaluates the whole computation by substitution
    /// — copying the argument lists at every step — to learn that the head is
    /// stuck (issues/elaborator-whnf-probes-on-computing-types.md). The value
    /// machine evaluates the same type with environments and is not
    /// pathological there (it is what conversion already runs on these
    /// types), so it is asked first, whenever the head could compute at all:
    ///
    /// - a **former** at the head: the reducer would reach the same former,
    ///   but by substitution, copying every continuation and branch bundle at
    ///   each step on the way (a straight stretch's encoded `match`,
    ///   issues/elab-whnf-copies-straight-continuations.md). Its top layer is
    ///   read off the value instead ([`Readback`]): each child is a closure
    ///   the machine has not evaluated, read back as its syntax under its
    ///   environment — exactly the reduct's child, since weak head reduction
    ///   never enters one. A child the readback does not know falls back to
    ///   the reducer, as before;
    /// - a **neutral** at the head: the probe's answer is "no former", and
    ///   every reduct is as good a witness of it as any other. The reducer is
    ///   given a small fixed step budget so a cheaply reached stuck spelling
    ///   stays exactly what it was, and past that budget the input itself is
    ///   returned — convertible to every reduct, and the spelling every
    ///   diagnostic and unifier consumer read before the probe anyway;
    /// - **out of fuel** in the value domain: out of fuel. The reducer shares
    ///   nothing, so it takes at least the steps the machine ran out of, and
    ///   each of its steps copies the term: asked again, it spent tens of
    ///   CPU-minutes reaching the same verdict on a closed length fact over a
    ///   generated program's code
    ///   (issues/closed-length-facts-evaluate-encodings.md).
    ///
    /// Adequacy of the machine against ch. 06 reduction (the kernel's
    /// differential tests) is what makes the first bullet's "same former"
    /// and the second's "no former" one claim; the first bullet's "same
    /// spelling" is checked against the reducer in debug builds
    /// ([`crate::readback::verify`]).
    pub(crate) fn whnf_type(&self, gamma: &LocalCtx, ty: &Type) -> Result<Type, OutOfFuel> {
        // The elaborator's own head-shape probes are a phase of elaboration
        // and not of the gate (`docs/instrumentation-design.md` §5): nothing
        // inside a `stats::time_kernel` bracket reaches here, so this column
        // is drawn from the elaborate side of the split and `kernel_ns` keeps
        // its meaning.
        let _phase = crate::stats::guard(crate::stats::Timer::ElabWhnf);
        let defs = Defs::transparent(&self.world);
        if type_head_may_compute(ty) {
            let arena = ValueArena::new();
            let probe = eval::whnf_value_ty(&arena, &Rc::new(ty.clone()), gamma, defs, self.fuel);
            let stuck = match probe.as_deref() {
                Ok(VTy::Neutral(_)) => true,
                // A `Vec`/`Fin` at a non-canonical length is a former the
                // input already shows; the reducer could only respell the
                // length. (Reached through an `El`, the decode is the point.)
                Ok(VTy::Vec { .. } | VTy::Fin { .. }) => {
                    matches!(ty, Type::Vec { .. } | Type::Fin { .. })
                }
                // A former with no sub-structure *is* its own readback, and it
                // is the shape of a decidable proposition that computed:
                // `Le(3, dot(row, atoms))` to `Unit`. The reducer would redo
                // the computation by substitution to spell four bytes.
                Ok(VTy::Nat) => return Ok(Type::Nat),
                Ok(VTy::Ty(l)) => return Ok(Type::Ty(l.clone())),
                Ok(VTy::Unit { level }) => return Ok(Type::Unit { level: level.clone() }),
                Ok(VTy::Empty { level }) => return Ok(Type::Empty { level: level.clone() }),
                Ok(VTy::SEmpty { level }) => return Ok(Type::SEmpty { level: level.clone() }),
                Err(OutOfFuel) => return Err(OutOfFuel),
                // A former with sub-structure: read its top layer off the
                // value (`readback.rs`), its children the syntax the machine
                // has not evaluated — the reducer's spelling, without
                // redoing the computation by substitution to reach it.
                Ok(former) => match Readback::new(gamma).head(former) {
                    Some(read) => {
                        #[cfg(debug_assertions)]
                        crate::readback::verify(ty, gamma, defs, self.fuel, &read);
                        return Ok(read);
                    }
                    None => false,
                },
            };
            if stuck {
                let budget = self.fuel.min(STUCK_SPELLING_STEPS);
                return Ok(reduce::whnf_type_delta(ty, gamma, defs, budget)
                    .unwrap_or_else(|OutOfFuel| ty.clone()));
            }
        }
        reduce::whnf_type_delta(ty, gamma, defs, self.fuel)
    }

    /// [`Self::whnf_type`] for terms, with the same division of labour: the
    /// value machine decides whether a canonical form is at the head, the
    /// reducer spells it. The motive-exposure path hands an `El`'s encoding
    /// here after the type probe, so a stuck encoding has to be as cheap as
    /// the stuck type was.
    pub(crate) fn whnf_term(&self, gamma: &LocalCtx, term: &Term) -> Result<Term, OutOfFuel> {
        let _phase = crate::stats::guard(crate::stats::Timer::ElabWhnf);
        let defs = Defs::transparent(&self.world);
        if term_head_may_compute(term) {
            let arena = ValueArena::new();
            let probe = eval::whnf_value(&arena, &Rc::new(term.clone()), gamma, defs, self.fuel);
            let stuck = match probe.as_deref() {
                Ok(Val::Neutral(_)) => true,
                Ok(Val::Zero) => return Ok(Term::Zero),
                Ok(Val::Triv { level }) => return Ok(Term::Triv { level: level.clone() }),
                Ok(Val::TmNat) => return Ok(Term::TmNat),
                Ok(Val::TmTy(l)) => return Ok(Term::TmTy(l.clone())),
                Ok(Val::TmUnit { level }) => return Ok(Term::TmUnit { level: level.clone() }),
                Ok(Val::TmEmpty { level }) => return Ok(Term::TmEmpty { level: level.clone() }),
                Ok(Val::TmSEmpty { level }) => return Ok(Term::TmSEmpty { level: level.clone() }),
                Err(OutOfFuel) => return Err(OutOfFuel),
                // A constructor with fields: read its top layer off the
                // value, as `whnf_type` reads a former's. A reduct through a
                // family's transports (`J` along a stored-children equation,
                // docs/iwf-infinitary-design.md §7) is a constructor whose
                // fields the reducer would reach only by copying those
                // transports' motives at every step
                // (issues/elab-whnf-family-transport-cost.md).
                Ok(canonical) => match Readback::new(gamma).term_head(canonical) {
                    Some(read) => {
                        #[cfg(debug_assertions)]
                        crate::readback::verify_term(term, gamma, defs, self.fuel, &read);
                        return Ok(read);
                    }
                    None => false,
                },
            };
            if stuck {
                let budget = self.fuel.min(STUCK_SPELLING_STEPS);
                return Ok(reduce::whnf_term_delta(term, gamma, defs, budget)
                    .unwrap_or_else(|OutOfFuel| term.clone()));
            }
        }
        reduce::whnf_term_delta(term, gamma, defs, self.fuel)
    }

    /// The global `term`'s weak head is stuck eliminating: its whnf is a
    /// neutral headed by a global, with at least one elimination in its
    /// spine that is not an application (a projection, a `match`, a
    /// recursor). A bare call of a global that does not unfold is a value,
    /// not a stuck reduction, so it does not count
    /// (`issues/stuck-on-opaque-theorem-diagnostic.md`).
    ///
    /// Read off the value and never spelled: [`Self::whnf_term`] spells a
    /// stuck reduct back as a term, and the sides of a certificate's refused
    /// pin spelled that way outgrew the test process's memory rail, where
    /// their value graph shares.
    pub(crate) fn eliminated_global(&self, gamma: &LocalCtx, term: &Term) -> Option<GlobalVar> {
        let arena = ValueArena::new();
        let defs = Defs::transparent(&self.world);
        let v = eval::whnf_value(&arena, &Rc::new(term.clone()), gamma, defs, self.fuel).ok()?;
        let Val::Neutral(n) = &*v else { return None };
        let Head::Global { var, .. } = &n.head else { return None };
        n.spine.iter_rev().any(|e| !e.is_application()).then_some(*var)
    }

    /// [`Self::whnf_term`] under the stuck-spelling budget, for a *speculative*
    /// probe: one that reads the reduct's head to decide whether reduction
    /// bought anything and abandons it otherwise
    /// (docs/omega-measure-reduction-design.md §2). Nothing here may pay the
    /// oracle's full fuel for an answer it may discard.
    pub(crate) fn whnf_term_bounded(
        &self,
        gamma: &LocalCtx,
        term: &Term,
    ) -> Result<Term, OutOfFuel> {
        Self {
            world: self.world.clone(),
            fuel: self.fuel.min(STUCK_SPELLING_STEPS),
        }
        .whnf_term(gamma, term)
    }

    /// The number a natural-number term computes to within `steps` of
    /// δ-transparent evaluation ([`eval::nat_value`]); `None` for a stuck
    /// term, a value past `u64`, or a budget spent.
    pub(crate) fn nat_value(&self, gamma: &LocalCtx, term: &Rc<Term>, steps: u64) -> Option<u64> {
        let _phase = crate::stats::guard(crate::stats::Timer::ElabWhnf);
        let defs = Defs::transparent(&self.world);
        eval::nat_value(term, gamma, defs, self.fuel.min(steps)).ok().flatten()
    }

    /// This oracle with its fuel capped at `steps`, for a speculative
    /// question whose "no" is as good as a spent budget.
    pub(crate) fn bounded(&self, steps: u64) -> Self {
        Self {
            world: self.world.clone(),
            fuel: self.fuel.min(steps),
        }
    }

    /// Normalize without δ. Some structural encodings deliberately preserve
    /// global neutrals while reducing only their local computation.
    pub(crate) fn whnf_term_opaque(
        &self,
        gamma: &LocalCtx,
        term: &Term,
    ) -> Result<Term, OutOfFuel> {
        let _phase = crate::stats::guard(crate::stats::Timer::ElabWhnf);
        reduce::whnf_term(term, gamma, self.fuel)
    }

    /// The elaborator's one reduct walk (issues/one-unfold-to-primitive.md):
    /// `term`'s successive transparent head reducts, `term` itself not
    /// included, ending at its weak head normal form, at `walk`'s budget, or
    /// at the oracle's fuel, whichever comes first. The site reads each
    /// reduct for the head it wants and stops there; the budget is the one
    /// thing that differs, and every one is named in [`Unfold`].
    pub(crate) fn unfold<'a>(&'a self, gamma: &'a LocalCtx, term: &Term, walk: Unfold) -> TermReducts<'a> {
        TermReducts {
            oracle: self,
            gamma,
            current: term.clone(),
            remaining: self.fuel.min(walk.steps()),
        }
    }

    /// [`Self::unfold`] read for the first reduct `read` answers: the walk
    /// most sites are.
    pub(crate) fn unfold_to<T>(
        &self,
        gamma: &LocalCtx,
        term: &Term,
        walk: Unfold,
        read: impl FnMut(Term) -> Option<T>,
    ) -> Option<T> {
        self.unfold(gamma, term, walk).find_map(read)
    }

    pub(crate) fn convert_type(
        &self,
        gamma: &LocalCtx,
        layer: Layer,
        lhs: &Type,
        rhs: &Type,
        level: &Level,
    ) -> Result<(), ConvError> {
        conv::conv_type(&self.world, gamma, layer, lhs, rhs, level, self.fuel)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn convert_term(
        &self,
        gamma: &LocalCtx,
        layer: Layer,
        lhs: &Term,
        rhs: &Term,
        ty: &Type,
        level: &Level,
    ) -> Result<(), ConvError> {
        conv::conv_term(&self.world, gamma, layer, lhs, rhs, ty, level, self.fuel)
    }

    /// A best-effort reader over this world, with its own step budget.
    pub(crate) fn diagnostics(&self, steps: usize) -> DiagnosticOracle<'_> {
        DiagnosticOracle {
            world: &self.world,
            steps,
        }
    }
}

/// Could δ-transparent reduction of this type do more than a decode step?
/// Only `El`, `Vec` and `Fin` step at all (a `U^δ` is opaque at every layer),
/// and each computes exactly when the term it is stuck on does.
fn type_head_may_compute(ty: &Type) -> bool {
    match ty {
        Type::El { tm, .. } => term_head_may_compute(tm),
        Type::Vec { len, .. } | Type::Fin { len } => term_head_may_compute(len),
        _ => false,
    }
}

/// Could δ-transparent reduction of this term do work at its head? Walk the
/// eliminator spine to its head: a local variable is stuck for good, a global
/// may unfold, and a canonical form under an eliminator is a redex. A bare
/// canonical form is already normal. Deliberately cheap and conservative —
/// a `true` only costs the value-domain probe.
fn term_head_may_compute(t: &Term) -> bool {
    let mut cur = t;
    loop {
        cur = match cur {
            Term::Var(_) => return false,
            Term::GlobalTm { .. } => return true,
            Term::ElimNat { scrut, .. }
            | Term::ElimEmpty { scrut, .. }
            | Term::Case { scrut, .. }
            | Term::ElimW { scrut, .. }
            | Term::ElimWf { scrut, .. }
            | Term::ElimSEmpty { scrut, .. }
            | Term::ElimSquash { scrut, .. }
            | Term::LetBoxTy { scrut, .. }
            | Term::LetBoxTm { scrut, .. }
            | Term::ElimCodeTy { scrut, .. }
            | Term::ElimCodeTm { scrut, .. } => scrut,
            Term::J { proof, .. } => proof,
            Term::Fst { pair, .. }
            | Term::Snd { pair, .. }
            | Term::FstAt { pair, .. }
            | Term::SndAt { pair, .. } => pair,
            Term::App { fun, .. }
            | Term::AppAt { fun, .. }
            | Term::UApp { fun, .. }
            | Term::CtxApp { fun, .. }
            | Term::TyApp { fun, .. } => fun,
            _ => {
                return if std::ptr::eq(cur, t) {
                    !reduce::is_whnf_term(t)
                } else {
                    true
                };
            }
        };
    }
}

/// Every reduct walk the elaborator takes, by what it looks for, with its
/// budget: the most head reducts it reads before it gives up
/// (docs/elaborator-principles-survey.md §5). Each budget was set by its
/// first customer, and a step is a δ step on a definition of any size or a
/// single β step alike, so the numbers say how far each search was willing
/// to go, not how much work it does. They are kept here, in one table, to be
/// retired one at a time once a walk can stop at the head it wants by itself
/// ([[unifier-lazy-delta]], issues/one-unfold-to-primitive.md step 2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Unfold {
    /// A defined proposition reaching a goal `omega` reads (a relation, a
    /// connective, a guard), and the goal side it is unfolded beside
    /// (crates/elab/src/omega_cert.rs).
    Proposition,
    /// A goal headed by a definition no evidence rule is about, reaching one
    /// some rule is about: `PowOk(x, -1)` unfolds to `x.Apart(0)` in a
    /// handful (docs/inverse-power-notation-design.md §4).
    RuleGoal,
    /// A definition unfolded looking for the edge image it names
    /// (`ring`'s `Reifier::wrapped_image`).
    RingWrapper,
    /// A committed term compared with one that has holes
    /// (the tactic host's `same_tm`).
    HoleComparison,
    /// A scrutinee that is, or becomes, a comparison: `lowb(x) =
    /// x.unsigned_lt_bit(10)` (goal_combinators' `comparison_of`).
    Comparison,
    /// A term reaching the match it is stuck on, or its co-occurrences
    /// (goal_combinators' `stuck_scrutinee`, `co_occurrences`; each also
    /// spends the caller's own budget).
    StuckScrutinee,
    /// A call reaching the match its definition makes on a constructor
    /// argument (goal_combinators' `matched_at_constructor`).
    MatchedArm,
    /// An instance's bit operand reaching an injection or a call the source
    /// names (`Elaborator::instance_bit`).
    InstanceBit,
    /// An argument's type read for implicits after a solution did not fit
    /// its slot: a δ step and the β steps that apply the unfolded body,
    /// twice over, and no whnf at large
    /// (issues/index-inference-through-unfolding.md).
    IndexRead,
    /// A word before `bv_omega` takes it as a leaf: enough for a definition
    /// that calls another, not enough to evaluate one.
    WordShape,
    /// One head step, which the relational walker re-enters after
    /// (relational_context/proof.rs).
    OneStep,
    /// A literal's embedding reaching a global's call or a value
    /// (`Elaborator::reduced_embedding`).
    LiteralEmbedding,
    /// A type code reaching the encoding of an inductive family it decodes
    /// to (iwf_family.rs, indexed.rs).
    FamilyEncoding,
}

impl Unfold {
    /// The walk's budget, in head reducts.
    pub(crate) fn steps(self) -> u64 {
        match self {
            Unfold::OneStep => 1,
            Unfold::RingWrapper => 4,
            Unfold::Comparison | Unfold::IndexRead => 8,
            Unfold::HoleComparison | Unfold::MatchedArm | Unfold::WordShape => 16,
            Unfold::InstanceBit | Unfold::LiteralEmbedding => 32,
            Unfold::Proposition | Unfold::RuleGoal | Unfold::StuckScrutinee => 64,
            Unfold::FamilyEncoding => 1024,
        }
    }
}

pub(crate) struct TermReducts<'a> {
    oracle: &'a SemanticOracle,
    gamma: &'a LocalCtx,
    current: Term,
    remaining: u64,
}

impl Iterator for TermReducts<'_> {
    type Item = Term;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let next = reduce::step_term_delta(
            &self.current,
            self.gamma,
            Defs::transparent(&self.oracle.world),
        )
        .ok()??;
        self.current = next.clone();
        Some(next)
    }
}

/// Best-effort semantic reading for diagnostics.
///
/// Unlike [`SemanticOracle`], every failure—including exhaustion—is `None`.
/// Nothing returned here may decide whether source elaborates.
pub(crate) struct DiagnosticOracle<'a> {
    world: &'a GlobalCtx,
    steps: usize,
}

impl DiagnosticOracle<'_> {
    /// Decode an `El`-headed type until a visible type constructor appears.
    pub(crate) fn decode_type(&self, gamma: &LocalCtx, ty: &Type) -> Option<Type> {
        if !matches!(ty, Type::El { .. }) {
            return None;
        }
        let defs = Defs::transparent(self.world);
        let mut head = ty.clone();
        for _ in 0..self.steps {
            head = reduce::step_type_delta(&head, gamma, defs).ok()??;
            if !matches!(head, Type::El { .. }) {
                return Some(head);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc as Rc;

    use heather_kernel::term::{GlobalVar, LocalSubst, LocalVar};

    use super::*;

    fn transparent_nat() -> GlobalBinding {
        GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Ty(Level::Zero)),
            level: Level::constant(1),
            body: Some(Rc::new(Term::TmNat)),
        }
    }

    #[test]
    fn dynamic_binders_are_part_of_the_oracle_world() {
        let base = GlobalCtx::default();
        let oracle = SemanticOracle::with_dynamic(&base, &[transparent_nat()], 32);
        let reference = Term::GlobalTm {
            var: GlobalVar(0),
            subst: LocalSubst::id(&LocalCtx::nil()),
        };
        assert_eq!(
            oracle.whnf_term(&LocalCtx::nil(), &reference).unwrap(),
            Term::TmNat
        );
    }

    #[test]
    fn diagnostic_exhaustion_declines_without_changing_semantic_reduction() {
        let oracle = SemanticOracle::in_world(GlobalCtx::default(), 32);
        let ty = Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::TmNat),
        };

        assert_eq!(oracle.whnf_type(&LocalCtx::nil(), &ty).unwrap(), Type::Nat);
        assert_eq!(
            oracle.diagnostics(0).decode_type(&LocalCtx::nil(), &ty),
            None
        );
        assert_eq!(
            oracle.diagnostics(1).decode_type(&LocalCtx::nil(), &ty),
            Some(Type::Nat)
        );
    }

    /// A world with one computing family at `GlobalVar(0)`:
    /// `P : Π(Nat). Ty 0 := λ n. elim_Nat(n; Nat; Unit)` — a `fn … → Type`
    /// whose head is a `match`, the shape of `Le` at `Int` and at `Nat`.
    fn computing_world() -> GlobalCtx {
        let body = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::constant(1),
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::ElimNat {
                level: Level::constant(1),
                motive: Rc::new(Type::Ty(Level::Zero)),
                base: Rc::new(Term::TmNat),
                step: Rc::new(Term::TmUnit { level: Level::Zero }),
                scrut: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        GlobalCtx::new(vec![GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::constant(1),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Ty(Level::Zero)),
            }),
            level: Level::constant(1),
            body: Some(Rc::new(body)),
        }])
    }

    /// `Γ = x : Nat`.
    fn one_nat() -> LocalCtx {
        LocalCtx::nil().extended(Rc::new(Type::Nat), Level::Zero)
    }

    /// `El^0 (P arg)` in `Γ = x : Nat`.
    fn p_of(arg: Term) -> Type {
        Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::App {
                fun: Rc::new(Term::GlobalTm {
                    var: GlobalVar(0),
                    subst: LocalSubst::id(&one_nat()),
                }),
                dom_level: Level::Zero,
                cod_level: Level::constant(1),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Ty(Level::Zero)),
                arg: Rc::new(arg),
            }),
        }
    }

    /// `elim_Nat(⌜n⌝; x; λ _ ih. ih)`: `n` ι-steps away from the local `x`.
    fn count_down_to_x(n: u64) -> Term {
        Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Var(LocalVar(0))),
            step: Rc::new(Term::Var(LocalVar(0))),
            scrut: Rc::new(Term::NatLit(n.into())),
        }
    }

    const FUEL: u64 = 1 << 20;

    fn reducer_type(ty: &Type) -> Type {
        reduce::whnf_type_delta(ty, &one_nat(), Defs::transparent(&computing_world()), FUEL)
            .unwrap()
    }

    #[test]
    fn a_stuck_head_keeps_the_reducers_spelling_when_it_is_cheap() {
        let oracle = SemanticOracle::in_world(computing_world(), FUEL);
        let ty = p_of(Term::Var(LocalVar(0)));
        let got = oracle.whnf_type(&one_nat(), &ty).unwrap();
        let reducer = reducer_type(&ty);
        assert_ne!(reducer, ty, "the probe must have something to spell");
        assert_eq!(got, reducer);
    }

    #[test]
    fn a_stuck_head_past_the_spelling_budget_is_the_input_itself() {
        let oracle = SemanticOracle::in_world(computing_world(), FUEL);
        let ty = p_of(count_down_to_x(4 * STUCK_SPELLING_STEPS));
        let reducer = reducer_type(&ty);
        assert_ne!(reducer, ty);
        assert!(!matches!(reducer, Type::Pi { .. } | Type::Unit { .. } | Type::Nat));
        assert_eq!(oracle.whnf_type(&one_nat(), &ty).unwrap(), ty);
    }

    #[test]
    fn a_closed_former_is_read_back_from_the_value() {
        let oracle = SemanticOracle::in_world(computing_world(), FUEL);
        for (arg, want) in [
            (Term::Zero, Type::Nat),
            (Term::Succ(Rc::new(Term::Zero)), Type::Unit { level: Level::Zero }),
            // The literal steps through `Succ` only in the reducer; the
            // value machine runs it as a program. Same former either way.
            (Term::NatLit(1000u64.into()), Type::Unit { level: Level::Zero }),
        ] {
            let ty = p_of(arg);
            assert_eq!(oracle.whnf_type(&one_nat(), &ty).unwrap(), want);
            assert_eq!(reducer_type(&ty), want);
        }
    }

    #[test]
    fn a_former_with_sub_structure_takes_the_reducers_spelling() {
        let mut bindings = computing_world().bindings.to_vec();
        bindings.push(GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Ty(Level::Zero)),
            level: Level::constant(1),
            body: Some(Rc::new(Term::TmPi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Term::TmNat),
                cod: Rc::new(Term::TmNat),
            })),
        });
        let world = GlobalCtx::new(bindings);
        let oracle = SemanticOracle::in_world(world.clone(), FUEL);
        let ty = Type::El {
            level: Level::Zero,
            // Innermost binding: the code pushed last.
            tm: Rc::new(Term::GlobalTm {
                var: GlobalVar(0),
                subst: LocalSubst::id(&one_nat()),
            }),
        };
        let got = oracle.whnf_type(&one_nat(), &ty).unwrap();
        assert!(matches!(got, Type::Pi { .. }));
        let reducer =
            reduce::whnf_type_delta(&ty, &one_nat(), Defs::transparent(&world), FUEL).unwrap();
        assert_eq!(got, reducer);
    }

    #[test]
    fn terms_follow_the_same_division_of_labour() {
        let oracle = SemanticOracle::in_world(computing_world(), FUEL);
        // Past the budget: the input.
        let far = count_down_to_x(4 * STUCK_SPELLING_STEPS);
        assert_eq!(oracle.whnf_term(&one_nat(), &far).unwrap(), far);
        // A closed canonical value: read back from the value.
        let closed = Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Zero),
            step: Rc::new(Term::Var(LocalVar(0))),
            scrut: Rc::new(Term::NatLit(1000u64.into())),
        };
        assert_eq!(oracle.whnf_term(&one_nat(), &closed).unwrap(), Term::Zero);
        // Cheaply stuck: the reducer's spelling.
        let near = count_down_to_x(3);
        let reducer =
            reduce::whnf_term_delta(&near, &one_nat(), Defs::transparent(&computing_world()), FUEL)
                .unwrap();
        assert_eq!(reducer, Term::Var(LocalVar(0)));
        assert_eq!(oracle.whnf_term(&one_nat(), &near).unwrap(), reducer);
    }

    /// Out of fuel in the value domain is the answer: the reducer, which
    /// shares nothing, never finishes on less fuel than the machine ran out
    /// of, and asking it anyway once spent tens of CPU-minutes copying a
    /// generated program's code to say the same thing
    /// (issues/closed-length-facts-evaluate-encodings.md).
    #[test]
    fn out_of_fuel_in_the_value_domain_is_the_verdict() {
        // `P(elim_Nat(⌜40⌝; 1; λ _ ih. ih))`: forty ι-steps to `P(1)`, `Unit`.
        let arg = Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Succ(Rc::new(Term::Zero))),
            step: Rc::new(Term::Var(LocalVar(0))),
            scrut: Rc::new(Term::NatLit(40u64.into())),
        };
        let ty = p_of(arg);
        let world = computing_world();
        let (mut short, mut enough) = (0, 0);
        for fuel in 0..64 {
            let arena = ValueArena::new();
            let machine =
                eval::whnf_value_ty(&arena, &Rc::new(ty.clone()), &one_nat(), Defs::transparent(&world), fuel);
            let reducer = reduce::whnf_type_delta(&ty, &one_nat(), Defs::transparent(&world), fuel);
            let got = SemanticOracle::in_world(world.clone(), fuel).whnf_type(&one_nat(), &ty);
            if machine.is_err() {
                short += 1;
                assert!(reducer.is_err(), "fuel {fuel}: the reducer finished where the machine ran out");
                assert!(got.is_err(), "fuel {fuel}");
            } else {
                enough += 1;
                assert_eq!(got.unwrap(), Type::Unit { level: Level::Zero }, "fuel {fuel}");
            }
        }
        assert!(short > 0 && enough > 0, "both sides of the machine's threshold are exercised");
    }
}
