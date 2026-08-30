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
struct TypeLayer {
    inductives: HashMap<String, Rc<Inductive>>,
    by_tag: HashMap<u32, Rc<Inductive>>,
    forded_by_skeleton: HashMap<u32, Rc<Inductive>>,
    constructors: HashMap<String, (Rc<Inductive>, usize)>,
    record_fields: HashSet<String>,
}

/// Append-only nominal indexes split into immutable image layers and one
/// suffix delta. The indexes for a declaration remain one `TypeLayer`, so a
/// commit cannot expose only one face of a nominal type.
#[derive(Clone, Default)]
pub(crate) struct Types {
    sealed: Rc<Vec<Rc<TypeLayer>>>,
    current: Rc<TypeLayer>,
    next_tag: u32,
    gdefs: GenDefs,
}

impl Types {
    pub(crate) fn semantic_snapshot(&self) -> Self {
        let mut types = self.clone();
        types.seal_current();
        types.gdefs = types.gdefs.semantic_snapshot();
        types
    }

    fn seal_current(&mut self) {
        let empty = self.current.inductives.is_empty()
            && self.current.by_tag.is_empty()
            && self.current.forded_by_skeleton.is_empty()
            && self.current.constructors.is_empty()
            && self.current.record_fields.is_empty();
        if empty {
            return;
        }
        Rc::make_mut(&mut self.sealed).push(Rc::clone(&self.current));
        self.current = Rc::new(TypeLayer::default());
    }

    fn layers(&self) -> impl Iterator<Item = &TypeLayer> {
        std::iter::once(self.current.as_ref()).chain(self.sealed.iter().rev().map(Rc::as_ref))
    }

    pub(crate) fn next_tag(&self) -> u32 {
        self.next_tag
    }

    pub(crate) fn inductive(&self, key: &str) -> Option<&Rc<Inductive>> {
        self.layers().find_map(|layer| layer.inductives.get(key))
    }

    pub(crate) fn by_tag(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.layers().find_map(|layer| layer.by_tag.get(&tag))
    }

    pub(crate) fn forded_by_skeleton(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.layers()
            .find_map(|layer| layer.forded_by_skeleton.get(&tag))
    }

    pub(crate) fn constructor(&self, key: &str) -> Option<&(Rc<Inductive>, usize)> {
        self.layers().find_map(|layer| layer.constructors.get(key))
    }

    pub(crate) fn has_record_field(&self, name: &str) -> bool {
        self.layers().any(|layer| layer.record_fields.contains(name))
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
            debug_assert!(self.by_tag(skeleton.tag).is_none());
        }
        let ind_tag = self.next_tag + u32::from(ind.skel.is_some());
        debug_assert_eq!(ind.tag, ind_tag);
        debug_assert!(self.by_tag(ind.tag).is_none());

        let layer = Rc::make_mut(&mut self.current);
        if let Some(skeleton) = &ind.skel {
            layer.by_tag.insert(skeleton.tag, Rc::clone(skeleton));
            layer.inductives
                .insert(qkey(module, &skeleton.name), Rc::clone(skeleton));
            layer.forded_by_skeleton
                .insert(skeleton.tag, Rc::clone(&ind));
            self.next_tag += 1;
        }

        for (index, ctor) in ind.ctors.iter().enumerate() {
            layer.constructors
                .insert(qkey(module, &ctor.name), (Rc::clone(&ind), index));
        }
        if ind.is_record {
            for (name, _) in &ind.ctors[0].fields {
                if let Some(name) = name {
                    layer.record_fields.insert(name.clone());
                }
            }
        }
        layer.by_tag.insert(ind.tag, Rc::clone(&ind));
        layer.inductives.insert(qkey(module, &ind.name), ind);
        self.next_tag += 1;
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

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

    #[test]
    fn semantic_image_shares_nominal_and_generated_prefixes() {
        let mut base = Elaborator::new();
        base.elab_source("inductive A { MkA }").unwrap();
        let image = base.semantic_image();
        let mut left = image.elaborator();
        let right = image.elaborator();

        assert!(Rc::ptr_eq(&left.types.sealed, &right.types.sealed));
        assert!(left.types.gdefs.shares_sealed_with(&right.types.gdefs));
        left.elab_source("inductive B { MkB }").unwrap();

        assert!(Rc::ptr_eq(&left.types.sealed, &right.types.sealed));
        assert!(left.types.gdefs.shares_sealed_with(&right.types.gdefs));
        assert!(left.types.inductive(&qkey("main", "B")).is_some());
        assert!(right.types.inductive(&qkey("main", "B")).is_none());
        assert_eq!(left.types.next_tag(), right.types.next_tag() + 1);
    }
}
