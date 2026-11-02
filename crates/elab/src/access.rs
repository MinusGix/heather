//! The designed access spellings of a repr and its `Impl`s
//! (`docs/repr-access-spellings-design.md`).
//!
//! A `datarepr` and an `impl` mint names — `Repr_N`, `N_spec_rec`,
//! `Impl_R_f` — because their artifacts are emitted as surface source and
//! re-parsed, and generated text can only declare names the surface can
//! write (`docs/datarepr-design.md` §1.4 as-landed note 1). Those names are
//! not the surface. The surface is `<owner>::<member>` at the name the author
//! wrote: `BinNat::abs`, `Impl(add, BinNat)::refines`.
//!
//! This module is the table that connects the two, in three directions:
//!
//! - **alias** (designed → minted), consulted by [`Elaborator::key_of`] as a
//!   *fallback* — only for a name that does not resolve on its own, so nothing
//!   that resolved before can be reinterpreted;
//! - **refusal** (minted → a sentence), consulted by
//!   [`Elaborator::resolve_name`] in user source only, so a minted name is an
//!   error naming the designed form rather than a working second spelling;
//! - **display** (minted → designed), applied to the statements the obligations
//!   listing and a `?` print, so that what is printed is what can be written.
//!
//! Generated source is exempt from the refusal by *mode*, not by inspection of
//! the text: [`Elaborator::generated_mode`] raises it for the duration of one
//! emission. That is the same boundary `issues/unnameable-generated-names.md`
//! will need at the lexer once minted names carry its marker.

use crate::Elaborator;
use std::collections::HashMap;

#[derive(Clone)]
/// Why a minted name is not spellable, as the second half of its diagnostic.
enum Restriction {
    /// It has a designed spelling: this one.
    Designed(String),
    /// It has none, and should not: a step in *how* a clause was proved, or a
    /// value consumers reach through the registry rather than by name
    /// (design §3.3). The string says what it is an internal *of*.
    Internal(String),
}

#[derive(Clone, Default)]
pub(crate) struct AccessTable {
    /// Designed path → the declaration it names.
    alias: HashMap<String, String>,
    /// Minted name → why it is refused.
    restricted: HashMap<String, Restriction>,
    /// Minted → designed, longest minted first so that a replacement never
    /// eats a prefix of a longer one.
    display: Vec<(String, String)>,
    /// Owner → its designed members, for the miss diagnostic. An owner with
    /// members is a closed list, so "no such member" can print the list.
    owners: HashMap<String, Vec<String>>,
}

impl Elaborator {
    /// Record a designed access path and the declaration it resolves to. The
    /// minted name becomes unspellable in user source at the same moment.
    pub(crate) fn designate_access(&mut self, designed: &str, minted: &str) {
        let access = self.representations.access_mut();
        access
            .alias
            .insert(designed.to_string(), minted.to_string());
        access.restricted.insert(
            minted.to_string(),
            Restriction::Designed(designed.to_string()),
        );
        access
            .display
            .push((minted.to_string(), designed.to_string()));
        access.display.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
        if let Some((owner, member)) = designed.rsplit_once("::") {
            access
                .owners
                .entry(owner.to_string())
                .or_default()
                .push(member.to_string());
        }
        self.record_module_event(|| crate::module_delta::DeltaEvent::Access {
            designed: designed.to_string(),
            minted: minted.to_string(),
        });
    }

    /// Record a generated name with no designed spelling (design §3.3).
    pub(crate) fn internal_access(&mut self, minted: &str, of: &str) {
        self.representations
            .access_mut()
            .restricted
            .insert(minted.to_string(), Restriction::Internal(of.to_string()));
        self.record_module_event(|| crate::module_delta::DeltaEvent::InternalAccess {
            minted: minted.to_string(),
            owner: of.to_string(),
        });
    }

    /// The declaration a designed path names, if this is one.
    pub(crate) fn access_alias<'a>(&'a self, name: &str) -> Option<&'a str> {
        self.representations
            .access()
            .alias
            .get(name)
            .map(String::as_str)
    }

    /// The refusal for a name written in user source, if it is one. `None` in
    /// generated mode, where the minted names are what the text says.
    pub(crate) fn access_refusal(&self, name: &str) -> Option<String> {
        if self.in_generated() {
            return None;
        }
        let access = self.representations.access();
        match access.restricted.get(name)? {
            Restriction::Designed(d) => Some(format!(
                "`{name}` is a generated name and is not part of the surface — write \
                 `{d}` (docs/repr-access-spellings-design.md §2)"
            )),
            Restriction::Internal(of) => Some(format!(
                "`{name}` is an internal of {of} and has no surface spelling: a route's \
                 intermediate is not an access point \
                 (docs/repr-access-spellings-design.md §3.3)"
            )),
        }
    }

    /// `Impl(add, BinNat)::refines` naming no declared `impl`. Separated from
    /// the generic qualifier complaint because the qualifier is not a name at
    /// all — it is an applied owner, and what is missing is the declaration.
    pub(crate) fn unknown_access_path(&self, name: &str) -> Option<String> {
        let (owner, member) = name.rsplit_once("::")?;
        let access = self.representations.access();
        if access.alias.contains_key(name) {
            return None;
        }
        // An owner that *has* designed members and was asked for one it does
        // not have: the list is closed and short, so print it rather than
        // complain about the qualifier (which is a repr's name, and is not a
        // module and not a type).
        if let Some(members) = access.owners.get(owner) {
            let list = members
                .iter()
                .map(|m| format!("`{m}`"))
                .collect::<Vec<_>>()
                .join(", ");
            return Some(format!(
                "`{owner}` has no member `{member}`: its access points are {list} \
                 (docs/repr-access-spellings-design.md §3.1)"
            ));
        }
        if !owner.ends_with(')') {
            return None;
        }
        let (head, args) = owner.split_once('(')?;
        let args: Vec<&str> = args.trim_end_matches(')').split(", ").collect();
        if head == "Impl"
            && let [op, repr] = args.as_slice()
        {
            return Some(format!(
                "no `impl {op} for {repr}` is declared, so `{name}` names nothing \
                 (`{member}` is a member of an `Impl`'s namespace)"
            ));
        }
        Some(format!(
            "`{owner}` is not an owner with members, so `{name}` names nothing"
        ))
    }

    /// A statement, path or type as it should be *printed*: every minted name
    /// replaced by its designed spelling (design §7). The stored strings are
    /// the source text the generated declarations are checked against and are
    /// deliberately left alone — display is the only place the two disagree.
    pub(crate) fn display_paths(&self, s: &str) -> String {
        let mut out = s.to_string();
        for (minted, designed) in &self.representations.access().display {
            if out.contains(minted.as_str()) {
                out = out.replace(minted.as_str(), designed);
            }
        }
        out
    }

    /// Run `f` with generated mode raised. A guard rather than two statements
    /// because every caller has error paths.
    pub(crate) fn generated_mode<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let depth = self.scope.generated_depth.get() + 1;
        self.scoped(|s| s.generated_depth.get_mut(), depth, f)
    }

    /// The `&self` form of [`Self::generated_mode`], for generated
    /// expressions elaborated from a checking position that holds no
    /// exclusive borrow (the Omega certificate route).
    pub(crate) fn generated_scope<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
        let depth = self.scope.generated_depth.get() + 1;
        self.scoped_cell(|s| &s.generated_depth, depth, || f(self))
    }

    /// Whether generated source is being elaborated right now. Diagnostics
    /// against generated spans have no user file to point into.
    pub(crate) fn in_generated(&self) -> bool {
        self.scope.generated_depth.get() > 0
    }

    /// Every access path of a `datarepr` (design §3.1), registered at the
    /// declaration and *before* its emission is elaborated — a `?` reports
    /// statements, and those are printed through [`Self::display_paths`].
    pub(crate) fn register_repr_access(&mut self, name: &str, ctors: &[String]) {
        let rec = crate::datarepr::record_name(name);
        let mut members: Vec<String> =
            vec!["abs".into(), "inv".into(), "fold".into(), "fold_law".into()];
        for c in ctors {
            members.push(format!("mk_{c}"));
            members.push(format!("{c}_abs"));
            members.push(format!("{c}_inv"));
        }
        for m in members {
            self.designate_access(&format!("{name}::{m}"), &format!("{rec}::{m}"));
        }
        // The spec recursor is the one member that is not a field of the
        // record: the anchor law's statement names it, so it has to be
        // writable (design §3.1).
        self.designate_access(
            &format!("{name}::spec_rec"),
            &crate::datarepr::spec_rec_name(name),
        );
    }

    /// The via-abs default's four artifacts (design §3.1), registered only when
    /// `fold` was actually defaulted — which is the only case in which they
    /// exist. Conditional membership is deliberate and visible: at a repr that
    /// wrote its own `fold`, `N::emb` is "no such member", with the member list
    /// printed, rather than a name that resolves at one repr and not another
    /// for reasons the writer cannot see.
    pub(crate) fn register_fold_default_access(&mut self, name: &str) {
        for suffix in ["emb", "emb_inv", "emb_abs", "fold_via_abs"] {
            self.designate_access(&format!("{name}::{suffix}"), &format!("{name}_{suffix}"));
        }
    }

    /// Every access path of an `impl` (design §3.1). `refines_inv` exists only
    /// at a repr-typed result; registering it unconditionally would promise a
    /// member that is not there, so it is passed in.
    pub(crate) fn register_impl_access(&mut self, op: &str, repr: &str, res_is_spec: bool) {
        let rec = crate::datarepr::impl_record_name(repr, op);
        let mut members = vec!["body".to_string(), "refines".to_string()];
        if res_is_spec {
            members.push("refines_inv".to_string());
        }
        for m in &members {
            self.designate_access(&format!("Impl({op}, {repr})::{m}"), &format!("{rec}::{m}"));
        }
        let of = format!("`impl {op} for {repr}`");
        self.internal_access(&format!("{rec}::via_derived_obligation"), &of);
        self.internal_access(&format!("{repr}_{op}_impl"), &of);
    }
}
