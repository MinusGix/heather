//! Typed access to the kernel's semantic operations.
//!
//! The elaborator uses several global worlds, but reduction and conversion
//! must always receive one world together with one fuel policy. Diagnostic
//! decoding shares that input while deliberately having a different failure
//! contract: it declines instead of turning exhaustion into an error.

use heather_kernel::conv::{self, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{self, Defs, OutOfFuel};
use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};

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
        let mut bindings = base.bindings.to_vec();
        bindings.extend(dynamic.iter().cloned());
        Self::in_world(GlobalCtx::new(bindings), fuel)
    }

    pub(crate) fn world(&self) -> &GlobalCtx {
        &self.world
    }

    pub(crate) fn whnf_type(&self, gamma: &LocalCtx, ty: &Type) -> Result<Type, OutOfFuel> {
        reduce::whnf_type_delta(ty, gamma, Defs::transparent(&self.world), self.fuel)
    }

    pub(crate) fn whnf_term(&self, gamma: &LocalCtx, term: &Term) -> Result<Term, OutOfFuel> {
        reduce::whnf_term_delta(term, gamma, Defs::transparent(&self.world), self.fuel)
    }

    /// Normalize without δ. Some structural encodings deliberately preserve
    /// global neutrals while reducing only their local computation.
    pub(crate) fn whnf_term_opaque(
        &self,
        gamma: &LocalCtx,
        term: &Term,
    ) -> Result<Term, OutOfFuel> {
        reduce::whnf_term(term, gamma, self.fuel)
    }

    /// Successive transparent reducts, bounded by both oracle fuel and `limit`.
    pub(crate) fn term_reducts<'a>(
        &'a self,
        gamma: &'a LocalCtx,
        term: &Term,
        limit: u64,
    ) -> TermReducts<'a> {
        TermReducts {
            oracle: self,
            gamma,
            current: term.clone(),
            remaining: self.fuel.min(limit),
        }
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
        )?;
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
            head = reduce::step_type_delta(&head, gamma, defs)?;
            if !matches!(head, Type::El { .. }) {
                return Some(head);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use heather_kernel::term::{GlobalVar, LocalSubst};

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
}
