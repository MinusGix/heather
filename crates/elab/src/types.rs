//! Registry of committed nominal type declarations.
//!
//! A declaration has several operational faces: its qualified surface name,
//! nominal tag, constructor names, optional fording skeleton, record-field
//! fast path, and generated Ψ definitions. They are one invariant and live
//! here rather than as parallel fields on `Elaborator`.

use std::collections::{HashMap, HashSet};
use std::sync::Arc as Rc;

use crate::gendefs::GenDefs;
use crate::inductive::Inductive;
use crate::layered::{Layer, Layered, index_hash};
use crate::names::qkey;

/// The syntax-owned prelude class's tag, reserved: [`declaration_tag`] never
/// derives it. A tag is one literal (`inductive::tag_type`), so a reserved
/// value costs nothing over any other.
pub(crate) const COLLECTION_LITERAL_TAG: u32 = 1 << 16;

/// A nominal declaration's tag, derived from its qualified name alone
/// (`docs/module-dag-design.md` §3,
/// `issues/nominal-tags-from-declaration-identity.md`).
///
/// It used to be the count of inductives committed before it, so what a
/// module elaborated to depended on how many inductives its process had
/// loaded before it, not only on what it imports: two modules built apart
/// would hand out the same tags, and an added inductive upstream moved every
/// later tag. A tag from the name is the same in every world that holds the
/// declaration. Two declarations whose names hash alike are refused where
/// the second is committed or replayed, never probed onward: a probe would
/// make the tag depend on what was committed first again. The `IWf` route's
/// shape declaration is named `D#shape`, so it has a tag of its own.
///
/// FNV-1a over `module::name`, folded to 32 bits. Not a security boundary:
/// a collision costs an error, never a confusion, because it is refused.
pub(crate) fn declaration_tag(module: &str, name: &str) -> u32 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in module.bytes().chain(*b"::").chain(name.bytes()) {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    let tag = (h ^ (h >> 32)) as u32;
    // The reserved tag is skipped by a fixed rule, so the result is still a
    // function of the name.
    if tag == COLLECTION_LITERAL_TAG { tag ^ 1 } else { tag }
}

#[derive(Clone, Default)]
struct TypeLayer {
    inductives: HashMap<String, Rc<Inductive>>,
    by_tag: HashMap<u32, Rc<Inductive>>,
    iwf_by_shape: HashMap<u32, Rc<Inductive>>,
    constructors: HashMap<String, (Rc<Inductive>, usize)>,
    /// A mutual group's members (docs/mutual-inductive-design.md §2): each
    /// member's qualified name to its family and its position there.
    members: HashMap<String, (Rc<Inductive>, usize)>,
    record_fields: HashSet<String>,
}

/// [`TypeLayer`]'s tables, as the layer index numbers them.
const INDUCTIVES: usize = 0;
const BY_TAG: usize = 1;
const IWF_BY_SHAPE: usize = 2;
const CONSTRUCTORS: usize = 3;
const MEMBERS: usize = 4;
const RECORD_FIELDS: usize = 5;

impl Layer for TypeLayer {
    const TABLES: usize = 6;

    fn keys(&self, table: usize, out: &mut dyn FnMut(u64)) {
        match table {
            INDUCTIVES => self.inductives.keys().for_each(|k| out(index_hash(k.as_str()))),
            BY_TAG => self.by_tag.keys().for_each(|k| out(index_hash(k))),
            IWF_BY_SHAPE => self.iwf_by_shape.keys().for_each(|k| out(index_hash(k))),
            CONSTRUCTORS => self.constructors.keys().for_each(|k| out(index_hash(k.as_str()))),
            MEMBERS => self.members.keys().for_each(|k| out(index_hash(k.as_str()))),
            RECORD_FIELDS => self.record_fields.iter().for_each(|k| out(index_hash(k.as_str()))),
            _ => unreachable!("TypeLayer has {} tables", Self::TABLES),
        }
    }
}

/// Append-only nominal indexes split into immutable image layers and one
/// suffix delta. The indexes for a declaration remain one `TypeLayer`, so a
/// commit cannot expose only one face of a nominal type.
#[derive(Clone, Default)]
pub(crate) struct Types {
    tables: Layered<TypeLayer>,
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
        let current = self.tables.current();
        let empty = current.inductives.is_empty()
            && current.by_tag.is_empty()
            && current.iwf_by_shape.is_empty()
            && current.constructors.is_empty()
            && current.members.is_empty()
            && current.record_fields.is_empty();
        if empty {
            return;
        }
        self.tables.seal_current();
    }

    pub(crate) fn inductive(&self, key: &str) -> Option<&Rc<Inductive>> {
        self.tables.find(INDUCTIVES, key, |layer| layer.inductives.get(key))
    }

    pub(crate) fn by_tag(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.tables.find(BY_TAG, &tag, |layer| layer.by_tag.get(&tag))
    }

    pub(crate) fn iwf_by_shape(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.tables.find(IWF_BY_SHAPE, &tag, |layer| layer.iwf_by_shape.get(&tag))
    }

    pub(crate) fn constructor(&self, key: &str) -> Option<&(Rc<Inductive>, usize)> {
        self.tables.find(CONSTRUCTORS, key, |layer| layer.constructors.get(key))
    }

    /// A mutual group's member: its family and its position among the
    /// family's members.
    pub(crate) fn member(&self, key: &str) -> Option<&(Rc<Inductive>, usize)> {
        self.tables.find(MEMBERS, key, |layer| layer.members.get(key))
    }

    pub(crate) fn has_record_field(&self, name: &str) -> bool {
        self.tables
            .find(RECORD_FIELDS, name, |layer| layer.record_fields.contains(name).then_some(()))
            .is_some()
    }

    pub(crate) fn gdefs(&self) -> &GenDefs {
        &self.gdefs
    }

    pub(crate) fn gdefs_mut(&mut self) -> &mut GenDefs {
        &mut self.gdefs
    }

    /// The declaration already holding `tag`, if any: what a new
    /// declaration whose name hashes to it collides with.
    pub(crate) fn tag_holder(&self, tag: u32) -> Option<&Rc<Inductive>> {
        self.by_tag(tag)
    }

    /// Install every nominal index for one fully checked declaration.
    ///
    /// The caller has refused a tag collision ([`Self::tag_holder`]); an
    /// `IWf`-route declaration installs its shape declaration beside the
    /// family.
    pub(crate) fn commit(&mut self, module: &str, ind: Rc<Inductive>) {
        if let Some(skeleton) = &ind.skel {
            debug_assert!(self.by_tag(skeleton.tag).is_none());
        }
        debug_assert!(self.by_tag(ind.tag).is_none());

        let layer = self.tables.current_mut();
        if let Some(skeleton) = &ind.skel {
            layer.by_tag.insert(skeleton.tag, Rc::clone(skeleton));
            layer.inductives
                .insert(qkey(module, &skeleton.name), Rc::clone(skeleton));
            layer.iwf_by_shape
                .insert(skeleton.tag, Rc::clone(&ind));
        }

        for (index, ctor) in ind.ctors.iter().enumerate() {
            layer.constructors
                .insert(qkey(module, &ctor.name), (Rc::clone(&ind), index));
        }
        for (index, member) in ind.members.iter().enumerate() {
            layer.members
                .insert(qkey(module, &member.name), (Rc::clone(&ind), index));
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
    }
}

#[cfg(test)]
mod tests {
    use crate::Elaborator;
    use crate::names::qkey;

    #[test]
    fn a_failed_inductive_neither_holds_a_tag_nor_enters_an_index() {
        let mut el = Elaborator::new();
        assert!(!el.check_source("inductive Bad { Mk, Mk }").is_empty());
        assert!(el.types.tag_holder(super::declaration_tag("main", "Bad")).is_none());
        assert!(el.types.inductive(&qkey("main", "Bad")).is_none());

        assert!(el.check_source("inductive Good { MkGood }").is_empty());
        let good = el
            .types
            .inductive(&qkey("main", "Good"))
            .expect("committed");
        assert_eq!(good.tag, super::declaration_tag("main", "Good"));
    }

    /// A declaration's tag is a function of its qualified name, not of what
    /// was committed before it (`docs/module-dag-design.md` §3).
    #[test]
    fn a_tag_does_not_depend_on_the_declarations_before_it() {
        let mut alone = Elaborator::new();
        alone.elab_source("inductive Second { MkSecond }").unwrap();
        let mut after = Elaborator::new();
        after.elab_source("inductive First { MkFirst }\ninductive Second { MkSecond }").unwrap();
        let tag = |el: &Elaborator| el.types.inductive(&qkey("main", "Second")).expect("committed").tag;
        assert_eq!(tag(&alone), tag(&after));
    }

    /// Two names that hash alike are refused at the second declaration, with
    /// both named, never given the next free tag: that would make a tag depend
    /// on which came first again. `T69021` and `T104011` collide in `main`.
    #[test]
    fn a_tag_collision_is_refused_naming_both() {
        assert_eq!(super::declaration_tag("main", "T69021"), super::declaration_tag("main", "T104011"));
        let mut el = Elaborator::new();
        let errs = el.check_source("inductive T69021 { A }\ninductive T104011 { B }");
        let text = errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n");
        assert!(text.contains("collides") && text.contains("main::T69021") && text.contains("main::T104011"), "{text}");
        assert!(el.types.inductive(&qkey("main", "T104011")).is_none());
    }

    #[test]
    fn the_syntax_protocol_tag_is_reserved() {
        let el = Elaborator::with_prelude().expect("prelude");
        assert_eq!(
            el.types
                .inductive(&qkey(crate::PRELUDE_MODULE, "CollectionLiteral"))
                .expect("protocol class")
                .tag,
            crate::types::COLLECTION_LITERAL_TAG,
        );
    }

    #[test]
    fn semantic_image_shares_nominal_and_generated_prefixes() {
        let mut base = Elaborator::new();
        base.elab_source("inductive A { MkA }").unwrap();
        let image = base.semantic_image();
        let mut left = image.elaborator();
        let right = image.elaborator();

        assert!(left.types.tables.shares_sealed_with(&right.types.tables));
        assert!(left.types.gdefs.shares_sealed_with(&right.types.gdefs));
        left.elab_source("inductive B { MkB }").unwrap();

        assert!(left.types.tables.shares_sealed_with(&right.types.tables));
        assert!(left.types.gdefs.shares_sealed_with(&right.types.gdefs));
        assert!(left.types.inductive(&qkey("main", "B")).is_some());
        assert!(right.types.inductive(&qkey("main", "B")).is_none());
    }
}
