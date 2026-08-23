//! Registry of committed nominal type declarations.
//!
//! A declaration has several operational faces: its qualified surface name,
//! nominal tag, constructor names, optional fording skeleton, record-field
//! fast path, and generated Ψ definitions. They are one invariant and live
//! here rather than as parallel fields on `Elaborator`.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::gendefs::GenDefs;
use crate::inductive::Inductive;
use crate::names::qkey;

#[derive(Clone, Default)]
pub(crate) struct Types {
    inductives: HashMap<String, Rc<Inductive>>,
    by_tag: HashMap<u32, Rc<Inductive>>,
    forded_by_skeleton: HashMap<u32, Rc<Inductive>>,
    constructors: HashMap<String, (Rc<Inductive>, usize)>,
    record_fields: HashSet<String>,
    next_tag: u32,
    gdefs: GenDefs,
}

impl Types {
    pub(crate) fn next_tag(&self) -> u32 {
        self.next_tag
    }

    pub(crate) fn inductive(&self, key: &str) -> Option<&Rc<Inductive>> {
        self.inductives.get(key)
    }

    pub(crate) fn by_tag(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.by_tag.get(&tag)
    }

    pub(crate) fn forded_by_skeleton(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.forded_by_skeleton.get(&tag)
    }

    pub(crate) fn constructor(&self, key: &str) -> Option<&(Rc<Inductive>, usize)> {
        self.constructors.get(key)
    }

    pub(crate) fn has_record_field(&self, name: &str) -> bool {
        self.record_fields.contains(name)
    }

    pub(crate) fn gdefs(&self) -> &GenDefs {
        &self.gdefs
    }

    pub(crate) fn gdefs_mut(&mut self) -> &mut GenDefs {
        &mut self.gdefs
    }

    /// Install every nominal index for one fully checked declaration.
    ///
    /// Tags are reserved only by this operation, so failed elaboration cannot
    /// consume one. A forded declaration installs its skeleton immediately
    /// before the family, matching the tags used while constructing both.
    pub(crate) fn commit(&mut self, module: &str, ind: Rc<Inductive>) {
        if let Some(skeleton) = &ind.skel {
            debug_assert_eq!(skeleton.tag, self.next_tag);
            debug_assert!(!self.by_tag.contains_key(&skeleton.tag));
            self.by_tag.insert(skeleton.tag, Rc::clone(skeleton));
            self.inductives
                .insert(qkey(module, &skeleton.name), Rc::clone(skeleton));
            self.forded_by_skeleton
                .insert(skeleton.tag, Rc::clone(&ind));
            self.next_tag += 1;
        }

        debug_assert_eq!(ind.tag, self.next_tag);
        debug_assert!(!self.by_tag.contains_key(&ind.tag));
        for (index, ctor) in ind.ctors.iter().enumerate() {
            self.constructors
                .insert(qkey(module, &ctor.name), (Rc::clone(&ind), index));
        }
        if ind.is_record {
            for (name, _) in &ind.ctors[0].fields {
                if let Some(name) = name {
                    self.record_fields.insert(name.clone());
                }
            }
        }
        self.by_tag.insert(ind.tag, Rc::clone(&ind));
        self.inductives.insert(qkey(module, &ind.name), ind);
        self.next_tag += 1;
    }
}

#[cfg(test)]
mod tests {
    use crate::Elaborator;
    use crate::names::qkey;

    #[test]
    fn a_failed_inductive_neither_consumes_a_tag_nor_enters_an_index() {
        let mut el = Elaborator::new();
        assert!(!el.check_source("inductive Bad { Mk, Mk }").is_empty());
        assert_eq!(el.types.next_tag(), 0);
        assert!(el.types.inductive(&qkey("main", "Bad")).is_none());

        assert!(el.check_source("inductive Good { MkGood }").is_empty());
        let good = el
            .types
            .inductive(&qkey("main", "Good"))
            .expect("committed");
        assert_eq!(good.tag, 0);
        assert_eq!(el.types.next_tag(), 1);
    }
}
