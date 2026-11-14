//! A module pass's part of the elaborator: entering a module and elaborating its items in order.

use std::collections::HashMap;

use heather_syntax::{Decl, Item, Span, parse_file};

use crate::{
    COMMON_MODULE, Elaborator, GroupKind, ItemPlan, PRELUDE_MODULE, R, err, item_timing_name, lint,
    measure_groups, mutual_family, mutual_rec, slice_names, slice_source, stats,
};
use crate::datarepr::DataReprMut;
use crate::declarations::DeclarationsMut;
use crate::diagnostics::ElabError;
use crate::host::HostMut;
use crate::module_delta::{Deltas, DeltasMut};
use crate::name_lookup::NameLookup;
use crate::names::{ImportSpec, NameKind, Scope, qkey};
use crate::resolve::ResolutionMut;
use crate::traits::ClassesMut;

/// A module pass's part of the elaborator: entering a module and elaborating its items in order.
pub(crate) struct ModulePassMut<'e>(pub(crate) &'e mut Elaborator);

impl std::ops::Deref for ModulePassMut<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl std::ops::DerefMut for ModulePassMut<'_> {
    fn deref_mut(&mut self) -> &mut Elaborator {
        self.0
    }
}

impl ModulePassMut<'_> {
    /// [`Elaborator::elab_source`] into a named module. The elaborator does no file
    /// IO: an `import m;` here requires that `m` has *already* been elaborated
    /// into this same accumulator, which is exactly what the CLI's topological
    /// walk guarantees (docs/modules-design.md §3.2).
    /// What one container's item loop needs before it starts: the mutual
    /// groups of `docs/mutual-recursion-design.md` §1, and the declaration
    /// names §8's forward-reference message reads.
    fn begin_container(&mut self, file: &heather_syntax::File) -> ItemPlan {
        let mut groups = measure_groups(&file.items);
        let mut kinds = vec![GroupKind::Measure; groups.len()];
        // Mutual `inductive` groups (docs/mutual-inductive-design.md §1).
        for g in mutual_family::inductive_groups(&file.items) {
            groups.push(g);
            kinds.push(GroupKind::Inductive);
        }
        // Mutual structural recursion over a mutual family (§6 there): a
        // member is one of this container's groups', or an imported one.
        let local_members: Vec<&str> = groups
            .iter()
            .zip(&kinds)
            .filter(|(_, k)| **k == GroupKind::Inductive)
            .flat_map(|(g, _)| g.iter())
            .filter_map(|&i| match &file.items[i] {
                Item::Inductive(d) => Some(d.name.as_str()),
                _ => None,
            })
            .collect();
        let is_member = |n: &str| local_members.contains(&n) || self.lookup_member(n).is_some();
        let structural = mutual_rec::structural_groups(&file.items, &is_member);
        for g in structural {
            groups.push(g);
            kinds.push(GroupKind::Structural);
        }
        let mut in_group: HashMap<usize, usize> = HashMap::new();
        for (g, members) in groups.iter().enumerate() {
            for &idx in members {
                in_group.insert(idx, g);
            }
        }
        *self.pass.container_decls.borrow_mut() = file
            .items
            .iter()
            .enumerate()
            .filter_map(|(i, it)| match it {
                Item::Decl(d) => {
                    Some((d.name.clone(), d.decreases.is_some(), i))
                }
                Item::Prefixed(p) => Some((p.decl.name.clone(), false, i)),
                _ => None,
            })
            .collect();
        self.pass.container_at.set(0);
        ItemPlan { groups, kinds, in_group }
    }

    /// One item, with a mutual group elaborated at its *first* member and the
    /// rest of the group a no-op (§1).
    fn elab_item_at(
        &mut self,
        file: &heather_syntax::File,
        idx: usize,
        item: &Item,
        plan: &ItemPlan,
    ) -> R<()> {
        self.pass.container_at.set(idx);
        match item {
            Item::Decl(d) => match plan.in_group.get(&idx) {
                Some(&g) if plan.groups[g][0] == idx => {
                    let members: Vec<&Decl> = plan.groups[g]
                        .iter()
                        .map(|&k| match &file.items[k] {
                            Item::Decl(d) => d,
                            _ => unreachable!("a group holds declarations"),
                        })
                        .collect();
                    match plan.kinds[g] {
                        GroupKind::Structural => {
                            self.session_transaction(|me| me.elab_structural_group(&members))
                        }
                        _ => self.session_transaction(|me| DeclarationsMut(me).elab_measure_group(&members)),
                    }
                }
                Some(_) => Ok(()),
                None => self.elab_decl(d),
            },
            // The declaration forms that are not a `fn`: each lowers to a
            // family of generated definitions. `gendefs` already times
            // *pushing* one; this brackets the lowering that builds them, so
            // an `inductive`'s or an `instance`'s own work has a column
            // instead of landing in `other`
            // (`docs/instrumentation-design.md` §5).
            Item::Inductive(i) => match plan.in_group.get(&idx) {
                Some(&g) if plan.groups[g][0] == idx => {
                    let members: Vec<&heather_syntax::InductiveDecl> = plan.groups[g]
                        .iter()
                        .map(|&k| match &file.items[k] {
                            Item::Inductive(d) => d,
                            _ => unreachable!("an inductive group holds inductives"),
                        })
                        .collect();
                    stats::timed(stats::Timer::Lower, || {
                        self.session_transaction(|me| me.elab_mutual_inductives(&members))
                    })
                }
                Some(_) => Ok(()),
                None => stats::timed(stats::Timer::Lower, || self.elab_inductive(i)),
            },
            Item::Class(c) => stats::timed(stats::Timer::Lower, || ClassesMut(self).elab_class(c)),
            Item::Instance(i) => stats::timed(stats::Timer::Lower, || ClassesMut(self).elab_instance(i)),
            Item::Designation(d) => stats::timed(stats::Timer::Lower, || ClassesMut(self).elab_designation(d)),
            Item::Datarepr(d) => stats::timed(stats::Timer::Lower, || DataReprMut(self).elab_datarepr(d)),
            Item::Impl(i) => stats::timed(stats::Timer::Lower, || DataReprMut(self).elab_impl(i)),
            Item::Generate(g) => HostMut(self).elab_generate(g),
            Item::Prefixed(p) => HostMut(self).elab_prefixed(p),
            Item::PrefixedRecord(p) => HostMut(self).elab_prefixed_record(p),
            Item::Import(_) => Ok(()),
        }
    }

    /// Run `f` with the kernel gate inline, restoring the configured width
    /// afterwards. The pool is quiescent at both ends: the fallback is entered
    /// only after a join, and the inline pass queues nothing.
    pub(crate) fn serially<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let width = self.pass.kernel_pool.workers();
        self.pass.kernel_pool.set_workers(1);
        // The discarded pass's verdicts become answerable exactly here, for
        // exactly this pass (§5.2).
        self.pass.kernel_replay.arm();
        let out = f(self);
        self.pass.kernel_replay.finish();
        self.pass.kernel_pool.set_workers(width);
        out
    }

    /// One pass over a module's items at whatever width the pool is set to.
    /// `deferred_failed` is set when a *queued* proof was rejected or its
    /// worker panicked — the one outcome a parallel pass can reach that the
    /// serial gate could not, and therefore the one that costs a replay.
    pub(crate) fn elab_module_pass(
        &mut self,
        module: &str,
        src: &str,
        deferred_failed: &mut bool,
    ) -> R<()> {
        // Parse time is its own column: it is not elaboration, and a frontend
        // regression in one is not a regression in the other
        // (`docs/instrumentation-design.md` §5).
        let file = stats::timed(stats::Timer::Parse, || parse_file(src))?;
        let lint_source = lint::Source::new(src, self.policy.lint_profile);
        self.enter_module(module, &file)?;
        DeltasMut(self).slice_enter(module);
        let plan = self.begin_container(&file);
        for (idx, item) in file.items.iter().enumerate() {
            let name = item_timing_name(item);
            let _item = stats::scope(stats::ScopeKind::Item, module, &name);
            // The miss sampler's item column
            // (issues/conv-miss-sampler-item-attribution.md): every
            // conversion miss the kernel records until the item ends is
            // charged to this declaration. A no-op without `value-metrics`.
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.policy.value_metrics {
                metrics.set_current_item(Some(Arc::from(name.as_str())));
            }
            let slice_source = slice_source(&file, src, idx, &plan);
            let slice_start = lint::item_span(item).start;
            let slice_mark = Deltas(self).slice_begin();
            // Every sealed proof the item opens, here or in its kernel
            // checks, is charged to its slice (`issues/theorem-witness-unfolding.md`).
            let unsealing = heather_kernel::unseal::Recording::start();
            // `--only` names items that elaborate from source however exact
            // the prefix is (`docs/check-only-design.md`); a group is named
            // through any member.
            let forced = DeltasMut(self).slice_forced(&slice_names(&file, idx, &plan));
            // A replayed slice carries the item's warnings, source lints
            // included: nothing is re-run over it.
            if !forced && DeltasMut(self).try_replay_slice(idx, &slice_source, slice_start) {
                if let Some(mark) = slice_mark {
                    DeltasMut(self).slice_end(mark, slice_source, slice_start, true, unsealing.finish());
                }
                continue;
            }
            let warn_mark = self.pass.warnings.borrow().len();
            let omega_mark = self.pass.omega_reports.borrow().len();
            let r = self.elab_item_at(&file, idx, item, &plan);
            // Canonical derived instances are minted **between** items, where
            // Ψ may grow (docs/traits-layer2-design.md §8). A failed item
            // mints nothing: its derivations are as speculative as the rest of
            // it.
            if r.is_err() {
                self.pass.pending_derived.borrow_mut().clear();
                self.pass.warnings.borrow_mut().truncate(warn_mark);
                self.pass.omega_reports.borrow_mut().truncate(omega_mark);
            } else {
                ResolutionMut(self).mint_pending();
                stats::timed(stats::Timer::Lint, || NameLookup(self).run_source_lints(item, &lint_source));
                if let Some(mark) = slice_mark {
                    DeltasMut(self).slice_elaborated();
                    DeltasMut(self).slice_end(mark, slice_source, slice_start, false, unsealing.finish());
                }
            }
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.policy.value_metrics {
                metrics.set_current_item(None);
            }
            if r.is_err() {
                self.pass.container_decls.borrow_mut().clear();
                if let Some(g) = self.policy.gate.as_ref() {
                    g.abandon(&self.psi);
                }
                // Nothing may outlive the module with proofs in flight, the
                // failure path included (`docs/parallel-kernel-gate-design.md`
                // §5). The item's own error is the one reported — unless a
                // queued proof also failed, in which case this whole pass is
                // discarded and replayed serially, and the error the caller
                // sees is the replay's.
                if self.join_kernel_gate().is_some() {
                    *deferred_failed = true;
                }
            }
            r?;
            // The early abort (§5.1): a queued proof has already failed, so
            // the rest of this pass is work the replay will do again. Stop
            // here and let the join report it.
            if self.pass.kernel_pool.poll_failed() {
                break;
            }
        }
        self.pass.container_decls.borrow_mut().clear();
        // The join, before this returns and therefore before any caller can
        // publish an image, record a verdict, or write an executable.
        match self.join_kernel_gate() {
            Some(e) => {
                *deferred_failed = true;
                Err(e)
            }
            None => Ok(()),
        }
    }

    /// Set the scope for a module about to be elaborated: its own name plus
    /// its written imports, each checked for existence and for the one
    /// import-time error the regime has (two lists claiming one name).
    fn enter_module(&mut self, module: &str, file: &heather_syntax::File) -> R<()> {
        // Re-entering a module is *not* an error here, and it is **additive**:
        // a caller that feeds one accumulator two chunks of the same module
        // (every test that calls `check_source` twice, and every REPL-shaped
        // use) is doing what one file would do, so the second chunk keeps the
        // first's imports and may add to them. Duplicate declarations already
        // error one layer down; two distinct *files* claiming one module name
        // is a loader concern, where the paths are known.
        let mut scope = self
            .names
            .module_scope(module)
            .cloned()
            .unwrap_or_else(|| Scope::new(module));
        let mut written: Vec<(&str, bool)> = Vec::new();
        for item in &file.items {
            let Item::Import(imp) = item else { continue };
            if imp.module == module {
                return err(
                    format!("a module cannot import itself (`{module}`)"),
                    imp.span,
                );
            }
            if imp.module != PRELUDE_MODULE && !self.names.has_module(&imp.module) {
                return err(
                    format!(
                        "unknown module `{}`: it is not in this run's import closure",
                        imp.module
                    ),
                    imp.module_span,
                );
            }
            // Twice *in this file* is the error; an import repeated across
            // two chunks of one module is the same import.
            if written.contains(&(imp.module.as_str(), imp.reexport)) {
                return err(format!("`{}` is imported twice", imp.module), imp.span);
            }
            written.push((&imp.module, imp.reexport));
            let mut exported = Vec::new();
            for (n, nspan) in &imp.listed {
                if imp.reexport && let Some(why) = self.access_refusal(n) {
                    return err(why, *nspan);
                }
                if !self.names.declares(&imp.module, n) {
                    return err(format!("`{}` declares no `{n}`", imp.module), *nspan);
                }
                if let Some(other) = scope
                    .imports
                    .iter()
                    .find(|i| i.module != imp.module && i.listed.iter().any(|l| l == n)
                        && self.names.origin(&i.module, n) != self.names.origin(&imp.module, n))
                    .map(|i| i.module.clone())
                {
                    // Both were asked for by name; there is nothing left to
                    // prefer, so this is the error the regime promises rather
                    // than a silent precedence.
                    return err(
                        format!(
                            "`{n}` is listed by two imports (`{other}` and `{}`): a listed \
                             name is a standing choice, so only one import may claim it",
                            imp.module
                        ),
                        *nspan,
                    );
                }
                if imp.reexport {
                    exported.push(n.clone());
                    // Selecting a type also exposes its constructors. Methods and
                    // instances remain explicit selections (including qualified names).
                    if let Some(origin) = self.names.origin(&imp.module, n)
                        && let Some(ind) = self.types.inductive(&qkey(origin, n))
                    {
                        for ctor in &ind.ctors {
                            if self.names.declares(&imp.module, &ctor.name)
                                && !exported.contains(&ctor.name) {
                                exported.push(ctor.name.clone());
                            }
                        }
                    }
                }
            }
            for name in &exported {
                let origin = self.names.origin(&imp.module, name);
                if self.names.declares(module, name) && self.names.origin(module, name) != origin {
                    return err(format!("reexport `{name}` conflicts with a declaration in `{module}`"), imp.span);
                }
                for previous in &scope.imports {
                    if previous.exported.contains(name) && self.names.origin(&previous.module, name) != origin {
                        return err(format!("reexport `{name}` conflicts between `{}` and `{}`", previous.module, imp.module), imp.span);
                    }
                }
            }
            let listed: Vec<String> = imp.listed.iter().map(|(n, _)| n.clone()).collect();
            match scope.imports.iter_mut().find(|i| i.module == imp.module) {
                Some(existing) => { existing.listed.extend(listed); existing.exported.extend(exported); },
                None => scope.imports.push(ImportSpec {
                    module: imp.module.clone(),
                    listed,
                    exported,
                }),
            }
        }
        // The common prelude, implicitly, when it is already in this world:
        // the modules it exports from are elaborated before it and so never
        // import it, and every later module's closure holds it, as the
        // loader and the image keys add it (issues/std-prelude-facade.md).
        if module != COMMON_MODULE
            && self.names.has_module(COMMON_MODULE)
            && scope.imports.iter().all(|i| i.module != COMMON_MODULE)
        {
            scope.imports.push(ImportSpec {
                module: COMMON_MODULE.to_string(),
                listed: Vec::new(),
                exported: Vec::new(),
            });
        }
        self.names.enter_scope(scope);
        // The interface boundary is per module: the definitions this module
        // declares are transparent in it, every other module's are withheld.
        if !self.interfaces.is_empty() {
            self.refresh_delta_psi();
        }
        Ok(())
    }

    /// [`NameLookup::check_declarable`] then [`Elaborator::add_name`], for the sites that
    /// register in one step.
    pub(crate) fn declare_name(&mut self, name: &str, kind: NameKind, span: Span) -> R<()> {
        NameLookup(self).check_declarable(name, span)?;
        self.add_name(name, kind);
        Ok(())
    }

    pub(crate) fn check_module_source_inner(&mut self, module: &str, src: &str) -> Vec<ElabError> {
        let mut deferred_failed = false;
        if self.gate_is_inline() {
            return self.check_module_pass(module, src, &mut deferred_failed);
        }
        self.pass.kernel_replay.clear();
        let mark = self.module_pass_checkpoint();
        let parallel = self.check_module_pass(module, src, &mut deferred_failed);
        if !deferred_failed {
            return parallel;
        }
        // §5.1: the recovery contract — report every bad declaration, keep
        // checking the good ones — is a *serial* statement about declaration
        // order, and a deferred rejection arrives out of that order and after
        // its declaration has already been committed to Ψ. So the pass is
        // discarded whole, down to the last registration and warning, and the
        // module is re-checked serially. The caller sees the serial answer.
        self.restore_module_pass(mark);
        self.serially(|me| me.check_module_pass(module, src, &mut false))
    }

    fn check_module_pass(
        &mut self,
        module: &str,
        src: &str,
        deferred_failed: &mut bool,
    ) -> Vec<ElabError> {
        let file = match stats::timed(stats::Timer::Parse, || parse_file(src)) {
            Ok(f) => f,
            Err(e) => return vec![e.into()],
        };
        let lint_source = lint::Source::new(src, self.policy.lint_profile);
        if let Err(e) = self.enter_module(module, &file) {
            return vec![e];
        }
        DeltasMut(self).slice_enter(module);
        let plan = self.begin_container(&file);
        let mut errs = Vec::new();
        for (idx, item) in file.items.iter().enumerate() {
            let warn_mark = self.pass.warnings.borrow().len();
            let name = item_timing_name(item);
            // The declaration scope, the same bracket as `elab_module_source`
            // — `heather check` is the primary command and had none
            // (`docs/instrumentation-design.md` §5) — carrying the miss
            // sampler's item column with it
            // (issues/conv-miss-sampler-item-attribution.md). A no-op without
            // `value-metrics`, and free without `--timings`.
            let item_scope = stats::scope(stats::ScopeKind::Item, module, &name);
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.policy.value_metrics {
                metrics.set_current_item(Some(Arc::from(name.as_str())));
            }
            // A slice of the previous delta stands in for the item when its
            // text and the prefix so far match
            // (`docs/declaration-slice-replay-design.md` §4).
            let slice_source = slice_source(&file, src, idx, &plan);
            let slice_start = lint::item_span(item).start;
            let slice_mark = Deltas(self).slice_begin();
            // Every sealed proof the item opens, here or in its kernel
            // checks, is charged to its slice (`issues/theorem-witness-unfolding.md`).
            let unsealing = heather_kernel::unseal::Recording::start();
            // `--only` names items that elaborate from source however exact
            // the prefix is (`docs/check-only-design.md`); a group is named
            // through any member.
            let forced = DeltasMut(self).slice_forced(&slice_names(&file, idx, &plan));
            // A replayed slice carries the item's warnings, source lints
            // included: nothing is re-run over it.
            if !forced && DeltasMut(self).try_replay_slice(idx, &slice_source, slice_start) {
                if let Some(mark) = slice_mark {
                    DeltasMut(self).slice_end(mark, slice_source, slice_start, true, unsealing.finish());
                }
                #[cfg(feature = "value-metrics")]
                if let Some(metrics) = &self.policy.value_metrics {
                    metrics.set_current_item(None);
                }
                continue;
            }
            let r = self.elab_item_at(&file, idx, item, &plan);
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.policy.value_metrics {
                metrics.set_current_item(None);
            }
            drop(item_scope);
            if r.is_err() {
                self.pass.pending_derived.borrow_mut().clear();
                // §4: a failed item's warnings are as speculative as the rest
                // of it — it registers nothing, and it says nothing.
                self.pass.warnings.borrow_mut().truncate(warn_mark);
                DeltasMut(self).slice_failed(slice_mark, slice_source, slice_start);
            } else {
                ResolutionMut(self).mint_pending();
                stats::timed(stats::Timer::Lint, || NameLookup(self).run_source_lints(item, &lint_source));
                if let Some(mark) = slice_mark {
                    DeltasMut(self).slice_elaborated();
                    DeltasMut(self).slice_end(mark, slice_source, slice_start, false, unsealing.finish());
                }
            }
            if let Err(e) = r {
                errs.push(e);
                // The refused declaration's gate question is dead, and the
                // next declaration lands at the same Ψ length.
                if let Some(g) = self.policy.gate.as_ref() {
                    g.abandon(&self.psi);
                }
            }
            // The early abort (§5.1): this pass is already doomed to be
            // replayed serially, so stop elaborating declarations for it.
            if self.pass.kernel_pool.poll_failed() {
                break;
            }
        }
        self.pass.container_decls.borrow_mut().clear();
        // The join (`docs/parallel-kernel-gate-design.md` §5). This is the
        // path `check_module_delta` runs inside, so the semantic image, the
        // declaration cache and `heather check`'s verdict all sit behind it.
        if let Some(e) = self.join_kernel_gate() {
            *deferred_failed = true;
            errs.push(e);
        }
        errs
    }
}
