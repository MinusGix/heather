//! Checked names and registered values (docs/registered-values-design.md).
//!
//! Three surface forms let a tactic's tables live beside the lemmas they
//! name, where every name is checked, instead of as strings in the tactic:
//!
//! - `name_of(p)` is the string a name lookup at a `by` resolves back to the
//!   global `p` denotes here. It is refused where `p` names nothing, so a
//!   renamed lemma is an error at the table, not a silent skip at a `by`.
//! - `register def x: T = e;` is the value definition `x`, also entered in
//!   the registry under its type `T`, a record or other inductive with no
//!   parameters.
//! - `registered(T)` is the list of every value registered at `T` in the
//!   current world, in canonical (global-name) order. As a parameter default
//!   (`rows: List<T> := registered(T)`) it is read where the call is, so a
//!   tactic's `by` sees the rows of the modules its client imports.

use heather_syntax::ast::{Block, Expr, ExprKind, Stmt, Ty, TyKind};

use crate::{err, Cx, Elaborator, R};
use crate::name_lookup::NameLookup;

/// The names `Lookup` answers without a declaration (host.rs).
const BUILTIN_NAMES: &[&str] = &["Nat", "Succ", "True", "False"];

/// Registered definitions' part of the elaborator.
pub(crate) struct Registered<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Registered<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Elaborator {
    /// `register def x: T = e;`: elaborate the `def`, then register it at
    /// its type's key.
    pub(crate) fn elab_registered_def(&mut self, d: &heather_syntax::Decl) -> R<()> {
        if !d.value {
            return err(
                "`register` marks a `def`: a registered value is a table a reader collects \
                 with `registered(T)` (docs/registered-values-design.md)",
                d.span,
            );
        }
        if !d.tyvars.is_empty() || !d.params.is_empty() {
            return err(
                "a registered `def` takes no type parameters: `registered(T)` collects values \
                 of one closed type",
                d.span,
            );
        }
        // The written type names the registry: `registered(T)` reads the
        // values registered at the same `T`.
        let TyKind::Named { name: written, args } = &d.result.kind else {
            return err(
                "a registered `def` writes its type, a record or inductive by name \
                 (`register def x: T = …;`), which is what `registered(T)` names",
                d.result.span,
            );
        };
        let ty_key = NameLookup(self).key_of_kinds(written, &[crate::names::NameKind::Inductive]);
        let (Some(ty_key), Some(ind)) = (ty_key, self.lookup_inductive(written).cloned()) else {
            return err(
                format!("`{written}` is not a record or inductive here: a registered value's type is one"),
                d.result.span,
            );
        };
        if !args.is_empty() || !ind.params.is_empty() || !ind.valparams.is_empty() {
            return err(
                format!(
                    "`{written}` has parameters: a registered value's type is a record or \
                     inductive with none, so `registered({written})` names it exactly"
                ),
                d.result.span,
            );
        }
        self.elab_decl(d)?;
        let Some(key) = self.key_of(&d.name) else {
            return err(format!("`{}` is not a declared global", d.name), d.span);
        };
        if self.traits.is_registered(&key) {
            return err(format!("`{}` is already registered", d.name), d.span);
        }
        self.semantic_commit_registered(ty_key, key);
        Ok(())
    }
}

impl Registered<'_> {
    /// `name_of(p)` and `registered(T)`, rewritten to the expressions they
    /// stand for: a string literal, and a list literal of the registered
    /// globals at their written type. `None` for anything else, and where a
    /// local or a global of the form's own name hides it.
    pub(crate) fn registry_rewrite(&self, cx: &Cx, e: &Expr) -> R<Option<Expr>> {
        let ExprKind::App { head, args, named, explicit: false, goal_oriented: false } = &e.kind else {
            return Ok(None);
        };
        let ExprKind::Var(form) = &head.kind else { return Ok(None) };
        if form != "name_of" && form != "registered" {
            return Ok(None);
        }
        if self.shadowed(cx, form) {
            return Ok(None);
        }
        let ([arg], true) = (args.as_slice(), named.is_empty()) else {
            return err(format!("`{form}` takes one name: `{form}(…)`"), e.span);
        };
        let ExprKind::Var(written) = &arg.kind else {
            return err(format!("`{form}` takes a name, not an expression"), arg.span);
        };
        let span = e.span;
        if form == "name_of" {
            let name = self.checked_name(cx, written).ok_or_else(|| crate::ElabError::Elab {
                msg: format!("`name_of({written})`: `{written}` names no global here"),
                span: arg.span,
            })?;
            return Ok(Some(Expr { kind: ExprKind::Str(name), span }));
        }
        let Some(key) = NameLookup(self).key_of_kinds(written, &[crate::names::NameKind::Inductive]) else {
            return err(
                format!("`registered({written})`: `{written}` names no record or inductive type here"),
                arg.span,
            );
        };
        let items: Vec<Expr> = self
            .traits
            .registered(&key)
            .iter()
            // The world can hold modules this one does not import (a gate
            // folder's prefix): only its import closure's entries are read.
            .filter(|global| {
                crate::names::split_qual(global).is_some_and(|(module, _)| self.names.reaches(module))
            })
            .map(|global| Expr { kind: ExprKind::Var(global.clone()), span })
            .collect();
        // `{ let registered: List<T> = [x, …]; registered }`: the list at its
        // element type, which the literal alone does not fix when it is empty.
        let list_ty = Ty {
            kind: TyKind::Named {
                name: "List".into(),
                args: vec![Ty { kind: TyKind::Named { name: written.clone(), args: Vec::new() }, span: arg.span }],
            },
            span,
        };
        let local = "registered".to_string();
        Ok(Some(Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts: vec![Stmt::Let {
                    name: local.clone(),
                    ty: Some(list_ty),
                    expr: Expr { kind: ExprKind::CollectionLit(items), span },
                    span,
                    opaque: false,
                }],
                result: Box::new(Expr { kind: ExprKind::Var(local), span }),
                ons: Vec::new(),
                span,
            })),
            span,
        }))
    }

    /// The spelling `Lookup` resolves back to what `written` denotes here:
    /// a builtin's own name, an inductive's or a global's qualified key.
    /// `None` where `written` names nothing a `by` could look up.
    fn checked_name(&self, cx: &Cx, written: &str) -> Option<String> {
        if cx.names.iter_inner().any(|n| n == written) || cx.aliases.iter_inner().any(|a| a.name == *written) {
            return None;
        }
        if BUILTIN_NAMES.contains(&written) && self.lookup_global(written).is_none() {
            return Some(written.to_string());
        }
        if let Some(key) = NameLookup(self).key_of_kinds(written, &[crate::names::NameKind::Inductive]) {
            return Some(key);
        }
        let key = self.key_of(written)?;
        self.global_abs(&key)?;
        Some(key)
    }
}
