//! Explicit assumptions and the declarations through which they flow.
//!
//! This is elaborator metadata, not kernel syntax.  The kernel correctly sees
//! both a theorem and an axiom as an opaque global; the surface distinction
//! and the dependency graph are recorded before theorem proofs are discarded.

use std::collections::BTreeMap;

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
pub(crate) struct Provenance {
    entries: BTreeMap<String, Entry>,
}

impl Provenance {
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
            let Some(entry) = self.entries.get(dependency) else { continue };
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
                        if (old.path.len(), &old.path) <= (replacement.path.len(), &replacement.path) => {}
                    _ => {
                        axioms.insert(inherited.axiom.clone(), replacement);
                    }
                }
            }
        }
        self.entries.insert(key, Entry { is_axiom, direct, axioms });
    }

    pub(crate) fn report(&self, key: &str) -> Option<AxiomReport> {
        let entry = self.entries.get(key)?;
        Some(AxiomReport {
            target: key.to_string(),
            is_axiom: entry.is_axiom,
            direct: entry.direct.clone(),
            axioms: entry.axioms.values().cloned().collect(),
        })
    }

    pub(crate) fn tainted(&self) -> Vec<AxiomReport> {
        self.entries
            .iter()
            .filter(|(_, entry)| !entry.is_axiom && !entry.axioms.is_empty())
            .filter_map(|(key, _)| self.report(key))
            .collect()
    }
}
