//! Committed meta-program definitions and their elaboration-slot index.
//!
//! A `meta fn` is checked at the meta layer but cannot live in Ψ. Its
//! definition therefore stays elaborator-side, optionally indexed by the slot
//! named in its `for` clause. These two views are one registry invariant: a
//! claimed slot always resolves to the definition that claimed it.

use std::collections::HashMap;
use std::rc::Rc;

use heather_kernel::term::{Term, Type};

use crate::names::qkey;
use crate::slots::Slot;

/// One registered `meta fn`: its closed layer-m term and statement type,
/// plus the Π order declared by a template signature.
///
/// The hook types an evaluated payload by kernel inference rather than by
/// peeling `stmt`; the statement remains the checked fact about `term`.
#[derive(Clone)]
pub(crate) struct MetaDef {
    pub(crate) term: Rc<Term>,
    #[allow(dead_code)]
    pub(crate) stmt: Rc<Type>,
    /// `|Ψ|` when this definition was registered. Unlike a Ψ-resident body,
    /// an elaborator-held definition is not automatically rescoped as Ψ grows,
    /// so [`Self::at`] shifts it by the growth at each use site.
    pub(crate) psi_len: u32,
    /// Positions into the slot's ingredient list, in template binder order:
    /// the one place a legally permuted signature's application order lives.
    pub(crate) order: Vec<usize>,
}

impl MetaDef {
    /// This definition's term and statement, rescoped to a Ψ of length `now`.
    pub(crate) fn at(&self, now: usize) -> (Rc<Term>, Rc<Type>) {
        let growth = now as u32 - self.psi_len;
        if growth == 0 {
            return (Rc::clone(&self.term), Rc::clone(&self.stmt));
        }
        (
            Rc::new(self.term.shift_global(growth)),
            Rc::new(self.stmt.shift_global(growth)),
        )
    }
}

#[derive(Clone, Default)]
pub(crate) struct MetaPrograms {
    definitions: HashMap<String, MetaDef>,
    /// `(module, written definition name)`, retained separately so collision
    /// diagnostics can identify the declaring module without parsing a key.
    slots: HashMap<Slot, (String, String)>,
}

impl MetaPrograms {
    pub(crate) fn definition(&self, module: &str, name: &str) -> Option<&MetaDef> {
        self.definitions.get(&qkey(module, name))
    }

    /// The existing owner of `slot`, for registration-time diagnostics.
    pub(crate) fn slot_owner(&self, slot: Slot) -> Option<(&str, &str)> {
        self.slots
            .get(&slot)
            .map(|(module, name)| (module.as_str(), name.as_str()))
    }

    /// The definition dispatched by `slot`, together with its written name.
    pub(crate) fn for_slot(&self, slot: Slot) -> Option<(&str, &MetaDef)> {
        let (module, name) = self.slots.get(&slot)?;
        let definition = self
            .definition(module, name)
            .expect("a claimed meta-program slot has its definition");
        Some((name, definition))
    }

    /// Install a validated definition and its optional slot claim as one
    /// infallible commit. Callers must finish name and signature validation
    /// before reaching this boundary.
    pub(crate) fn commit(
        &mut self,
        module: String,
        name: String,
        slot: Option<Slot>,
        definition: MetaDef,
    ) {
        let key = qkey(&module, &name);
        if let Some(slot) = slot {
            assert!(
                !self.slots.contains_key(&slot),
                "validated meta-program slot is vacant"
            );
        }
        assert!(
            !self.definitions.contains_key(&key),
            "validated meta-program name is vacant"
        );

        self.definitions.insert(key, definition);
        if let Some(slot) = slot {
            self.slots.insert(slot, (module, name));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn definition() -> MetaDef {
        MetaDef {
            term: Rc::new(Term::Zero),
            stmt: Rc::new(Type::Nat),
            psi_len: 0,
            order: vec![1, 0],
        }
    }

    #[test]
    fn ordinary_meta_programs_are_definitions_without_dispatch() {
        let mut programs = MetaPrograms::default();
        programs.commit("m".into(), "walk".into(), None, definition());

        assert!(programs.definition("m", "walk").is_some());
        assert!(programs.for_slot(Slot::VecMap).is_none());
    }

    #[test]
    fn a_commit_installs_the_definition_and_slot_views_together() {
        let mut programs = MetaPrograms::default();
        programs.commit(
            "templates".into(),
            "map_code".into(),
            Some(Slot::VecMap),
            definition(),
        );

        assert_eq!(
            programs.slot_owner(Slot::VecMap),
            Some(("templates", "map_code"))
        );
        let (name, registered) = programs.for_slot(Slot::VecMap).expect("slot lookup");
        assert_eq!(name, "map_code");
        assert_eq!(registered.order, vec![1, 0]);
        assert!(std::ptr::eq(
            registered,
            programs
                .definition("templates", "map_code")
                .expect("definition lookup")
        ));
    }
}
