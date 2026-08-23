//! Committed representation registries.
//!
//! A `datarepr` has several lookup faces that must land together: its spec
//! identity, its written name, an optional monomorph name, its designed access
//! paths, and its obligation rows. An `impl` similarly couples its lookup
//! entry, provenance, access paths, and obligations. This module owns those
//! views; declaration entry points snapshot it while provisional access paths
//! are live, then either commit the linked lookup/reporting views or restore
//! the whole registry on failure.

use std::collections::HashMap;

use crate::access::AccessTable;
use crate::datarepr::{DatareprInfo, DatareprKey, ImplEntry, Obligation};

#[derive(Clone, Default)]
pub(crate) struct Representations {
    by_spec: HashMap<DatareprKey, DatareprInfo>,
    by_name: HashMap<String, DatareprInfo>,
    monomorphs: HashMap<(u32, String), String>,
    impls: HashMap<(String, String), ImplEntry>,
    obligations: Vec<Obligation>,
    access: AccessTable,
}

impl Representations {
    pub(crate) fn for_spec(&self, key: &DatareprKey) -> Option<&DatareprInfo> {
        self.by_spec.get(key)
    }

    pub(crate) fn named(&self, name: &str) -> Option<&DatareprInfo> {
        self.by_name.get(name)
    }

    pub(crate) fn has_name(&self, name: &str) -> bool {
        self.by_name.contains_key(name)
    }

    pub(crate) fn commit_repr(
        &mut self,
        key: DatareprKey,
        name: String,
        info: DatareprInfo,
        monomorph: Option<(u32, String)>,
        obligations: Vec<Obligation>,
    ) {
        debug_assert!(!self.by_spec.contains_key(&key));
        debug_assert!(!self.by_name.contains_key(&name));
        if let Some(monomorph) = monomorph {
            self.monomorphs.insert(monomorph, name.clone());
        }
        self.obligations.extend(obligations);
        self.by_spec.insert(key, info.clone());
        self.by_name.insert(name, info);
    }

    pub(crate) fn monomorph(&self, tag: u32, args: &str) -> Option<&str> {
        self.monomorphs
            .get(&(tag, args.to_string()))
            .map(String::as_str)
    }

    pub(crate) fn has_impl(&self, repr: &str, op: &str) -> bool {
        self.impls.contains_key(&(repr.to_string(), op.to_string()))
    }

    pub(crate) fn commit_impl(
        &mut self,
        repr: String,
        op: String,
        entry: ImplEntry,
        obligations: Vec<Obligation>,
    ) {
        debug_assert!(!self.impls.contains_key(&(repr.clone(), op.clone())));
        self.obligations.extend(obligations);
        self.impls.insert((repr, op), entry);
    }

    pub(crate) fn impl_entry(&self, repr: &str, op: &str) -> Option<&ImplEntry> {
        self.impls.get(&(repr.to_string(), op.to_string()))
    }

    pub(crate) fn obligations(&self) -> &[Obligation] {
        &self.obligations
    }

    pub(crate) fn access(&self) -> &AccessTable {
        &self.access
    }

    pub(crate) fn access_mut(&mut self) -> &mut AccessTable {
        &mut self.access
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::datarepr::Provenance;

    fn obligation(owner: &str) -> Obligation {
        Obligation {
            owner: owner.to_string(),
            path: format!("{owner}::law"),
            field: "law".to_string(),
            state: "supplied",
            provenance: None,
            statement: "True".to_string(),
        }
    }

    #[test]
    fn commits_install_every_linked_lookup_view() {
        let mut representations = Representations::default();
        let key = (Some(7), "Tok".to_string());
        let info = DatareprInfo {
            global: "ListTok".to_string(),
            written: "List<Tok>".to_string(),
            carrier: "PackedList".to_string(),
            record: "Repr_ListTok".to_string(),
            ctors: Rc::new(Vec::new()),
        };

        representations.commit_repr(
            key.clone(),
            "ListTok".to_string(),
            info,
            Some((7, "Tok".to_string())),
            vec![obligation("datarepr ListTok")],
        );

        assert_eq!(representations.for_spec(&key).unwrap().global, "ListTok");
        assert_eq!(
            representations.named("ListTok").unwrap().written,
            "List<Tok>"
        );
        assert_eq!(representations.monomorph(7, "Tok"), Some("ListTok"));
        assert_eq!(representations.obligations().len(), 1);

        representations.commit_impl(
            "ListTok".to_string(),
            "append".to_string(),
            ImplEntry {
                global: "ListTok_append_impl".to_string(),
                provenance: Provenance::Derived,
            },
            vec![obligation("impl append for ListTok")],
        );

        let implementation = representations.impl_entry("ListTok", "append").unwrap();
        assert_eq!(implementation.global, "ListTok_append_impl");
        assert_eq!(implementation.provenance, Provenance::Derived);
        assert_eq!(representations.obligations().len(), 2);
    }
}
