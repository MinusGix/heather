//! Explicit assumptions and the declarations through which they flow.
//!
//! This is elaborator metadata, not kernel syntax.  The kernel correctly sees
//! both a theorem and an axiom as an opaque global; the surface distinction
//! and the dependency graph are recorded before theorem proofs are discarded.

use std::sync::Mutex;
use std::collections::{BTreeMap, HashMap};
use heather_kernel::rc::Rc;
use heather_kernel::term::Term;

use crate::layered::{Layer, Layered, index_hash};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssumptionKind {
    User,
    Primitive,
}

impl AssumptionKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::User => "user",
            Self::Primitive => "primitive",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomUse {
    pub axiom: String,
    pub kind: AssumptionKind,
    /// Deterministic shortest path, target first and axiom last.
    pub path: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomReport {
    pub target: String,
    pub is_axiom: bool,
    pub direct: Vec<String>,
    pub axioms: Vec<AxiomUse>,
}

#[derive(Clone)]
struct Entry {
    is_axiom: bool,
    direct: Vec<String>,
    axioms: BTreeMap<String, AxiomUse>,
}

#[derive(Clone, Default)]
struct ProvenanceLayer {
    entries: BTreeMap<String, Rc<Entry>>,
}

impl Layer for ProvenanceLayer {
    const TABLES: usize = 1;

    fn keys(&self, _: usize, out: &mut dyn FnMut(u64)) {
        self.entries.keys().for_each(|k| out(index_hash(k.as_str())));
    }
}

/// Append-only provenance split into immutable image layers and one suffix
/// delta. Capturing an image seals the current delta; its first declaration
/// therefore never clones the imported dependency graph.
#[derive(Clone, Default)]
pub(crate) struct Provenance {
    tables: Layered<ProvenanceLayer>,
    /// What the body of a global with no record of its own reaches, by its
    /// Ψ position ([`Self::reached_through`]). A cache: each entry holds the
    /// body it was read from, and answers only for that body.
    through: Through,
}

/// [`Provenance::reached_through`]'s cache. A clone starts empty: an entry
/// is recomputed from the body it describes, so nothing is lost but the
/// reading, and a sealed image shared between threads carries no table.
#[derive(Default)]
struct Through(Mutex<HashMap<u32, (Rc<Term>, Rc<Vec<String>>)>>);

impl Clone for Through {
    fn clone(&self) -> Self {
        Self::default()
    }
}

impl Provenance {
    pub(crate) fn semantic_snapshot(&self) -> Self {
        let mut provenance = self.clone();
        provenance.seal_current();
        provenance
    }

    fn seal_current(&mut self) {
        if self.tables.current().entries.is_empty() {
            return;
        }
        self.tables.seal_current();
    }

    fn entry(&self, key: &str) -> Option<&Entry> {
        self.tables.find(0, key, |layer| layer.entries.get(key)).map(Rc::as_ref)
    }

    pub(crate) fn commit(&mut self, key: String, is_axiom: bool, mut direct: Vec<String>) {
        direct.sort();
        direct.dedup();
        let mut axioms = BTreeMap::new();
        if is_axiom {
            axioms.insert(
                key.clone(),
                AxiomUse {
                    axiom: key.clone(),
                    kind: AssumptionKind::User,
                    path: vec![key.clone()],
                },
            );
        }
        for dependency in &direct {
            let Some(entry) = self.entry(dependency) else {
                continue;
            };
            for inherited in entry.axioms.values() {
                let mut candidate = Vec::with_capacity(inherited.path.len() + 1);
                candidate.push(key.clone());
                candidate.extend(inherited.path.iter().cloned());
                let replacement = AxiomUse {
                    axiom: inherited.axiom.clone(),
                    kind: inherited.kind,
                    path: candidate,
                };
                match axioms.get(&inherited.axiom) {
                    Some(old)
                        if (old.path.len(), &old.path)
                            <= (replacement.path.len(), &replacement.path) => {}
                    _ => {
                        axioms.insert(inherited.axiom.clone(), replacement);
                    }
                }
            }
        }
        self.tables.current_mut().entries.insert(
            key,
            Rc::new(Entry {
                is_axiom,
                direct,
                axioms,
            }),
        );
    }

    /// Whether `key` has a record: only a recorded name is an edge a later
    /// declaration's assumptions flow through.
    pub(crate) fn is_recorded(&self, key: &str) -> bool {
        self.entry(key).is_some()
    }

    /// The recorded names the unrecorded global at Ψ position `abs` reaches
    /// through `body`, computed by `read` the first time this body is asked
    /// about.
    pub(crate) fn reached_through(
        &self,
        abs: u32,
        body: &Rc<Term>,
        read: impl FnOnce() -> Vec<String>,
    ) -> Rc<Vec<String>> {
        let cached = |table: &HashMap<u32, (Rc<Term>, Rc<Vec<String>>)>| {
            table.get(&abs).filter(|(of, _)| Rc::ptr_eq(of, body)).map(|(_, names)| Rc::clone(names))
        };
        // Not held across `read`, which asks about the globals below this one.
        if let Some(names) = cached(&self.through.0.lock().unwrap_or_else(|e| e.into_inner())) {
            return names;
        }
        let names = Rc::new(read());
        self.through.0.lock().unwrap_or_else(|e| e.into_inner()).insert(abs, (Rc::clone(body), Rc::clone(&names)));
        names
    }

    pub(crate) fn is_axiom(&self, key: &str) -> bool {
        self.entry(key).is_some_and(|entry| entry.is_axiom)
    }

    pub(crate) fn report(&self, key: &str) -> Option<AxiomReport> {
        let entry = self.entry(key)?;
        Some(AxiomReport {
            target: key.to_string(),
            is_axiom: entry.is_axiom,
            direct: entry.direct.clone(),
            axioms: entry.axioms.values().cloned().collect(),
        })
    }

    pub(crate) fn tainted(&self) -> Vec<AxiomReport> {
        let mut entries = BTreeMap::new();
        for layer in self.tables.layers_oldest_first() {
            for (key, entry) in &layer.entries {
                entries.insert(key.as_str(), entry.as_ref());
            }
        }
        entries
            .into_iter()
            .filter(|(_, entry)| !entry.is_axiom && !entry.axioms.is_empty())
            .filter_map(|(key, _)| self.report(key))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_snapshot_shares_prefix_and_starts_an_empty_suffix() {
        let mut base = Provenance::default();
        base.commit("m::axiom".into(), true, Vec::new());
        for i in 0..128 {
            base.commit(
                format!("m::d{i}"),
                false,
                vec!["m::axiom".into()],
            );
        }

        let image = base.semantic_snapshot();
        assert_eq!(image.tables.sealed_len(), 1);
        assert!(image.tables.current().entries.is_empty());

        let mut suffix = image.clone();
        assert!(image.tables.shares_sealed_with(&suffix.tables));
        suffix.commit(
            "next::result".into(),
            false,
            vec!["m::d127".into()],
        );

        assert!(image.tables.shares_sealed_with(&suffix.tables));
        assert!(image.report("next::result").is_none());
        let report = suffix.report("next::result").expect("suffix entry");
        assert_eq!(report.direct, ["m::d127"]);
        assert_eq!(report.axioms[0].path.first().map(String::as_str), Some("next::result"));
        assert_eq!(report.axioms[0].path.last().map(String::as_str), Some("m::axiom"));
    }
}
