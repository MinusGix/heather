//! Name lookup's part of the elaborator: resolving a written name and reading the world's globals.

use heather_kernel::typing;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};

use heather_syntax::{Expr, ExprKind, Item, Span};

use crate::{Elaborator, R, err, lint, names, recursion, with_self_shadow_note};
use crate::application::ParamMeta;
use crate::context::Cx;
use crate::diagnostics::{ElabError, LintFix, Warning};
use crate::gendefs::GeneratedDefs;
use crate::lint::Lint;
use crate::names::{NameKind, NameRes, qkey, split_qual};
use crate::recursion::SelfRef;

/// Name lookup's part of the elaborator: resolving a written name and reading the world's globals.
pub(crate) struct NameLookup<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for NameLookup<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl NameLookup<'_> {
    /// [`Self::resolve_name`] without the surface refusal: what the *tables*
    /// say. The alias's target is looked up through this — a designed path
    /// resolves to a declaration whose own name is not spellable, which is the
    /// whole point of the alias (design §5).
    pub(crate) fn resolve_declared(&self, name: &str) -> NameRes {
        self.resolve_declared_kinds(name, names::ANY_KIND)
    }

    fn resolve_declared_kinds(&self, name: &str, kinds: &[NameKind]) -> NameRes {
        let scopes = self.scope.resolution_scopes.borrow();
        // Omega's generated certificate may explicitly name its library
        // dependencies. This overlay applies to this qualified lookup only:
        // it neither opens bare names nor changes the caller's saved imports.
        if (self.scope.omega_depth.get() > 0 || self.scope.ring_depth.get() > 0)
            && let Some((module, base)) = split_qual(name)
            && matches!(module, "omega" | "nat" | "int" | "logic" | "list" | "ring" | "linarith")
            && self.names.declares(module, base)
        {
            return NameRes::Found(module.to_string());
        }
        // An evidence rule the search proposes is cited by its key on the
        // caller's behalf, as a certificate names its dependencies above. Its
        // module need only be in the import closure: a rule reaches a file
        // through the module that imports it (`field_division`'s sign rules
        // are `ordered_sign`'s), as an instance does, and the caller never
        // wrote its name.
        if self.scope.rule_citation.borrow().as_deref() == Some(name)
            && let Some((module, base)) = split_qual(name)
            && self.names.declares(module, base)
            && self.names.reaches(module)
        {
            return NameRes::Found(module.to_string());
        }
        // A registered value is cited by its key on the caller's behalf by
        // `registered(T)` (docs/registered-values-design.md), as an evidence
        // rule is above: its module need only be in the import closure.
        if let Some((module, base)) = split_qual(name)
            && self.traits.is_registered(name)
            && self.names.declares(module, base)
            && self.names.reaches(module)
        {
            return NameRes::Found(module.to_string());
        }
        self.names
            .resolve_kinds(scopes.last().map(Rc::as_ref), name, kinds, |m, ty, ctor| {
                self.types
                    .inductive(&qkey(m, ty))
                    .is_some_and(|i| i.ctors.iter().any(|c| c.name == ctor))
            })
    }

    /// The base half of a written name — `nat::Nat::sub` and `sub` both name `sub`.
    fn base_name(name: &str) -> &str {
        split_qual(name).map(|(_, b)| b).unwrap_or(name)
    }

    /// [`recursion::elab_self_call`], with a refusal *of the call* — one at
    /// the call itself or one naming the callee, not an error inside an
    /// argument that happens to surface here — noted with the global the
    /// written name hides ([`Self::self_shadow_note`]).
    pub(crate) fn self_call_noted(&self, cx: &Cx, written: &str, args: &[Expr], explicit: bool, span: Span) -> R<(Term, Type, Level)> {
        recursion::elab_self_call(self.0, cx, args, explicit, span).map_err(|e| {
            let ElabError::Elab { msg, span: at } = &e else { return e };
            let selfref = cx.selfref.as_ref().expect("a self-call has a self-reference");
            if *at != span && !msg.contains(&format!("`{}`", selfref.name)) {
                return e;
            }
            let note = self.self_shadow_note(selfref, written);
            with_self_shadow_note(e, note.as_deref())
        })
    }

    /// Inside a member `T::name`, the bare `name` is the member's own
    /// self-reference, checked before any global, so a top-level `name` is
    /// hidden there. When `written` is that bare spelling and a declaration
    /// of the name does resolve outside the member, the note naming it and
    /// the qualified spelling that reaches it
    /// (issues/self-reference-hides-same-named-global.md). `None` for a
    /// non-member, the qualified spelling, or a name nothing else declares.
    pub(crate) fn self_shadow_note(&self, selfref: &SelfRef, written: &str) -> Option<String> {
        if selfref.name == selfref.written_name || written != selfref.name {
            return None;
        }
        let key = self.key_of(self.instance_alias(written))?;
        if key == selfref.written_name || key.ends_with(&format!("::{}", selfref.written_name)) {
            return None;
        }
        // The module-qualified spelling, offered only when it reaches the
        // same declaration from here.
        let reach = split_qual(&key)
            .map(|(module, _)| qkey(module, written))
            .filter(|spelling| self.key_of(spelling).as_deref() == Some(key.as_str()));
        let member = &selfref.written_name;
        let hides = format!(
            "note: inside the member `{member}`, the bare name `{written}` is `{member}` itself \
             (its self-reference), which hides the declaration `{key}`"
        );
        Some(match reach {
            Some(spelling) => format!("{hides}; write `{spelling}` to reach it"),
            None => hides,
        })
    }

    /// [`Self::key_of`] with the candidate set restricted by declaration kind.
    /// See [`Self::lookup_inductive`] for the one restricted caller and why
    /// the restriction is licensed there and nowhere else.
    pub(crate) fn key_of_kinds(&self, name: &str, kinds: &[NameKind]) -> Option<String> {
        if self.access_refusal(name).is_some() {
            return None;
        }
        // A registered instance's global, by its key: generated, unwritable
        // (`#`), and reachable wherever its instance is, which is the whole
        // run's closure (docs/module-dag-design.md §2) and not only the
        // modules this one names. A child instance fills an inherited field
        // from a parent registered in a module it never imported
        // (`algebra`'s `CommMonoidRel<Nat>(RelId, add)` under `semiring`'s
        // `CommSemiring<Nat>`).
        if name.contains('#') && split_qual(name).is_some() && self.names.global(name).is_some() {
            return Some(name.to_string());
        }
        if let Some(k) = self.key_of_declared_kinds(name, kinds) {
            return Some(k);
        }
        // The alias, strictly as a fallback. Its target is resolved through
        // `key_of_declared` and not `key_of`, because the target's own name is
        // the one the surface refuses — that is what the alias is for.
        if let Some(target) = self.access_alias(name) {
            return self.key_of_declared_kinds(target, kinds);
        }
        // A designed path under its module's name, `m::f::rec`: `m`'s own
        // `f::rec`, as `m::f` is `m`'s `f`.
        let (module, path) = name.split_once("::")?;
        let target = self.access_alias(path)?;
        self.key_of_declared_kinds(&format!("{module}::{target}"), kinds)
    }

    fn key_of_declared_kinds(&self, name: &str, kinds: &[NameKind]) -> Option<String> {
        match self.resolve_declared_kinds(name, kinds) {
            NameRes::Found(m) => {
                // A *member* declares the qualified string itself
                // (issues/type-owned-members-receiver-slice.md), so its key
                // keeps both halves: `List::nth` in module `list` is
                // `list::List::nth`. The two other qualified readings —
                // `nat::Nat::sub` (module path) and `Option::None` (constructor by
                // type) — declare the base name, and this is what tells them
                // apart without a second resolution judgment.
                if split_qual(name).is_some() && self.names.declares(&m, name) {
                    return Some(qkey(&m, name));
                }
                Some(qkey(&m, Self::base_name(name)))
            }
            _ => None,
        }
    }

    /// Inside a member of `T` (`fn T::f`), a bare name may name `T`'s other
    /// members: `cong_cons` for `List::cong_cons` inside `List::append_assoc`
    /// (docs/sections-design.md §6). The member joins the candidate set with
    /// the same rank as every other reading, so when the bare name also
    /// resolves on its own the two are ambiguous (`Err`, the message): a
    /// precedence either way would let a library's growth reinterpret checked
    /// text (docs/modules-design.md §8). Only a declared member counts, never
    /// the constructor reading of `T::C`. It is consulted only where a written
    /// expression enters elaboration ([`Self::owner_rewrite`]), so the
    /// elaborator's own lookups of library names, and receiver dispatch's
    /// ambient readings, are untouched.
    fn owner_member(&self, name: &str) -> Result<Option<String>, String> {
        let Some(owner) = self.scope.member_owner.as_deref() else { return Ok(None) };
        if name.contains("::") || self.scope.instance_scope.iter().any(|(base, _)| base == name) {
            return Ok(None);
        }
        let full = format!("{owner}::{name}");
        let NameRes::Found(m) = self.resolve_declared(&full) else { return Ok(None) };
        if !self.names.declares(&m, &full) {
            return Ok(None);
        }
        match self.resolve_declared(name) {
            NameRes::NotFound | NameRes::NoSuchQualifier(_) | NameRes::Restricted(_) => Ok(Some(full)),
            NameRes::Found(other) => Err(format!(
                "`{name}` is ambiguous here: inside a member of `{owner}` it can name \
                 `{owner}::{name}` (`{m}`) or `{name}` (`{other}`). Write `{owner}::{name}` \
                 for the member, or qualify the other (`{other}::{name}`) \
                 (docs/sections-design.md §6)"
            )),
            NameRes::Ambiguous(origins) => Err(format!(
                "`{name}` is ambiguous here: inside a member of `{owner}` it can name \
                 `{owner}::{name}` (`{m}`), and it is also declared in {}. Qualify it \
                 (docs/sections-design.md §6)",
                origins.iter().map(|o| format!("`{o}`")).collect::<Vec<_>>().join(" and ")
            )),
        }
    }

    /// A bare written name, or the bare head of a written call, that names a
    /// sibling member ([`Self::owner_member`]) is rewritten to its qualified
    /// spelling before the expression is elaborated, so every route after it
    /// (implicit masks, receivers, deferral) sees the declaration's own name.
    /// Locals, aliases and the declaration's own name shadow it, as they
    /// shadow every global.
    pub(crate) fn owner_rewrite(&self, cx: &Cx, e: &Expr) -> R<Option<Expr>> {
        if self.scope.member_owner.is_none() {
            return Ok(None);
        }
        let (name, span) = match &e.kind {
            ExprKind::Var(n) => (n, e.span),
            ExprKind::App { head, .. } => match &head.kind {
                ExprKind::Var(n) => (n, head.span),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return Ok(None);
        }
        let full = match self.owner_member(name) {
            Ok(Some(full)) => full,
            Ok(None) => return Ok(None),
            Err(msg) => return err(msg, span),
        };
        let mut out = e.clone();
        match &mut out.kind {
            ExprKind::Var(n) => *n = full,
            ExprKind::App { head, .. } => head.kind = ExprKind::Var(full),
            _ => unreachable!(),
        }
        Ok(Some(out))
    }

    /// Inside an `instance` block, an unqualified name that is an *earlier*
    /// member of this block names that member's global
    /// (docs/traits-layer1-design.md §4.2). A name rewrite and nothing more:
    /// the members' own parameters are unaffected, so in a *generic* instance
    /// a cross-member call still passes the `requires` binders — layer 1 has
    /// no resolution to fill them with.
    ///
    /// Consulted only from [`Self::lookup_global`], so locals, aliases,
    /// constructors and the self-reference all shadow it exactly as they
    /// shadow any global.
    pub(crate) fn instance_alias<'a>(&'a self, name: &'a str) -> &'a str {
        if self.scope.instance_scope.is_empty() {
            return name;
        }
        match self
            .scope.instance_scope
            .iter()
            .rev()
            .find(|(base, _)| base == name)
        {
            Some((_, full)) => full,
            None => name,
        }
    }

    /// Is `name` declared in the module being elaborated, as one of `kinds`?
    /// The duplicate-declaration test: a *module* never declares one name
    /// twice, while two modules may.
    pub(crate) fn own_declares(&self, name: &str, kinds: &[NameKind]) -> bool {
        self.names.declares_own(self.names.module(), name, kinds)
    }

    /// The one collision the regime turns into an error at the *declaration*:
    /// a local name that an import listed by name. (An unlisted collision is
    /// fine — locals win.) Checked before anything is registered, since a
    /// failed declaration must register nothing.
    pub(crate) fn check_declarable(&self, name: &str, span: Span) -> R<()> {
        if let Some(m) = self
            .names
            .scope()
            .imports
            .iter()
            .find(|i| i.listed.iter().any(|l| l == name))
            .map(|i| i.module.clone())
        {
            return err(
                format!(
                    "`{name}` is declared here and also listed by `import {m}::{{{name}}};` \
                     — a listed name is the file asking for that one, so the two cannot \
                     both stand: drop it from the import list and qualify (`{m}::{name}`)"
                ),
                span,
            );
        }
        Ok(())
    }

    pub(crate) fn emit_lint_with_fix(
        &self,
        lint: Lint,
        msg: impl Into<String>,
        span: Span,
        fix: Option<LintFix>,
    ) {
        // §4.1: a span into *generated* text does not index into any file a
        // reader has, and a `datarepr`'s emission is elaborated inside an
        // ordinary `check` of the declaration that owns it. Rendering such a
        // span against the user's source would point a caret at an unrelated
        // line. Generated code is the generator's problem, so it is dropped
        // here rather than filtered by whoever renders.
        if self.in_generated() {
            return;
        }
        let mut warnings = self.pass.warnings.borrow_mut();
        if warnings.iter().any(|w| w.lint == lint && w.span == span) {
            return;
        }
        warnings.push(Warning {
            lint,
            msg: msg.into(),
            span,
            fix,
        });
    }

    pub(crate) fn run_source_lints(&self, item: &Item, source: &lint::Source<'_>) {
        for warning in self
            .pass.warnings
            .borrow_mut()
            .iter_mut()
            .filter(|w| w.lint == Lint::RedundantMatchMotive)
        {
            if let Some(fix) = &mut warning.fix
                && let Some(span) = source.complete_motive_fix(item, fix.span)
            {
                fix.span = span;
                fix.replacement = " ".into();
            }
        }
        for finding in lint::check_item(item, source) {
            // A dead arm's body is deliberately never checked. Its dedicated
            // semantic warning already says so; piling lexical unused-binder
            // findings onto names in that body would pretend we had analyzed
            // code that cannot run.
            if finding.lint == Lint::UnusedPatternBinder
                && self.pass.warnings.borrow().iter().any(|w| {
                    w.lint == Lint::UnreachableMatchArm
                        && w.span.start <= finding.span.start
                        && finding.span.end <= w.span.end
                })
            {
                continue;
            }
            if !self.in_generated() {
                self.pass.warnings.borrow_mut().push(Warning {
                    lint: finding.lint,
                    msg: finding.msg,
                    span: finding.span,
                    fix: finding.fix,
                });
            }
        }
    }

    /// A declared global's elaborated statement and body, by written name —
    /// what an analyzer's input is read out of (the fn to transcribe is an
    /// ordinary declaration, already checked and in Ψ).
    /// The binding at `abs`'s own world: the Ψ prefix its prefix-scoped
    /// statement and body resolve against.
    fn prefix_world(&self, abs: usize) -> GlobalCtx {
        self.psi.prefix(abs)
    }

    /// `ty`, a statement scoped at binding `abs`, with its checked spellings
    /// in component form, for a `box` (`typing::spell_checked_in_code_ty`).
    fn code_form_ty(&self, abs: usize, ctx: &LocalCtx, ty: Rc<Type>, level: &Level) -> Option<Rc<Type>> {
        if heather_kernel::subst::holds_checked_spelling_ty(&ty) {
            let world = self.prefix_world(abs);
            typing::spell_checked_in_code_ty(&world, 0, Layer::Code, ctx, ty, level, self.policy.fuel).ok()
        } else {
            Some(ty)
        }
    }

    pub(crate) fn global_body(&self, name: &str) -> Option<(Rc<Type>, Rc<Term>)> {
        self.global_body_at(self.lookup_global(name)?.abs as usize)
    }

    /// [`Self::global_body`] by Ψ coordinate.
    pub(crate) fn global_body_at(&self, abs: usize) -> Option<(Rc<Type>, Rc<Term>)> {
        match self.psi.bindings.get(abs)? {
            GlobalBinding::Tm {
                ty,
                body: Some(body),
                ..
            } => Some((Rc::clone(ty), Rc::clone(body))),
            _ => None,
        }
    }

    /// The **pull reflection API**, first cut
    /// (issues/fn-reflection-for-analyzers.md,
    /// docs/fn-signature-reflection-design.md §1): a declared fn's *type as
    /// code* — a `Term::BoxTy` of type `CodeTy(·, 0)`, ready for the
    /// type-code recursor. Nothing is stored per declaration; the type is
    /// read out of Ψ on request, which is what makes this pull and not push.
    ///
    /// THIS IMPLEMENTATION IS FINAL, and that is a correction to what the
    /// signature-reflection round expected here
    /// (docs/opaque-globals-analysis-design.md §2): the opaque-globals round
    /// settled unfolding-for-analysis *at the reflection boundary*, so the
    /// Ψ-read below (a committed statement is read as stored, as
    /// `Defs::body` reads a constant's body) already *is* `u^δ`
    /// unfolding-on-request.
    /// No kernel machinery replaces it and no ch. 07 obligation attaches,
    /// because the kernel never learns reflection happened.
    ///
    /// By name, this entry is the tests' (`wf.rs`); certgen resolves the name
    /// once and calls [`Self::fn_type_code_at`].
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fn_type_code(&self, name: &str) -> Option<Term> {
        self.fn_type_code_at(self.lookup_global(name)?.abs as usize)
    }

    /// [`Self::fn_type_code`] by Ψ coordinate, which is how certgen reaches it
    /// once it has resolved the declaration's name.
    pub(crate) fn fn_type_code_at(&self, abs: usize) -> Option<Term> {
        let GlobalBinding::Tm { ctx, ty, level, .. } = self.psi.bindings.get(abs)? else {
            return None;
        };
        // A box payload holds no checked spelling (`docs/intro-by-type-design.md`
        // §2.3), and a statement elaborated outside a quote may: translate it
        // in the binding's own world before rescoping.
        let ty = self.code_form_ty(abs, ctx, Rc::clone(ty), level)?;
        // A committed statement names committed definitions only: it is
        // read as stored.
        let ty = (*ty).clone();
        // Unfolding-for-analysis, per the doctrine above, now with a second
        // case: a statement spells registered lowerings as `El (D#tycode^δ)`
        // (`docs/annotation-component-respell-design.md` §2.1), and at layer
        // m a boxed global reference is *syntax* — the analyzer cannot δ
        // through it, so the signature checker would decline every fn whose
        // result is a coded declaration. The reflection boundary is where
        // that unfolds: hand the analyzer the inline lowering the reference
        // decodes to, i.e. exactly the type it analyzed before the respell
        // existed.
        let len = self.psi.bindings.len() as u32;
        let ty = match GeneratedDefs(self).unspell_ty_deep(len, &ty) {
            Some(t) => t,
            None => ty,
        };
        Some(Term::BoxTy(Rc::new(ty)))
    }

    /// Does `name`, read where the current context is, resolve back to the
    /// binding at absolute Ψ index `abs`? What a renderer whose output is
    /// re-parsed has to ask before it uses a base name
    /// (issues/omega-renders-member-by-base-name.md).
    pub(crate) fn base_name_resolves_to(&self, name: &str, abs: usize) -> bool {
        self.lookup_global(name).is_some_and(|i| i.abs as usize == abs)
    }

    /// The canonical qualified spelling of a global. Generated modules use
    /// this rather than [`Self::global_name_at`]'s deliberately presentation-
    /// oriented base name when they refer across a module boundary.
    pub(crate) fn global_qualified_name_at(&self, abs: usize) -> Option<String> {
        Some(self.names.global_name_at(abs as u32)?.to_string())
    }

    /// The **declared** name of the global at `abs`: its qualified key minus
    /// the module, so `nat::Nat::add` gives `Nat::add` and `ir_v1::dbl` gives
    /// `dbl`. The split is [`names::split_qual`]'s, at the first `::`, since
    /// module names are single-segment. What certgen derives its generated
    /// items' stems from (docs/certgen-global-identity-design.md §2).
    pub(crate) fn global_declared_name_at(&self, abs: usize) -> Option<String> {
        let key = self.names.global_name_at(abs as u32)?;
        Some(names::split_qual(key).map_or(key, |(_, d)| d).to_string())
    }

    /// The parameter table of the binding at absolute Ψ index `abs`, empty for
    /// a binding that has none. The by-index companion of [`Self::params_of`].
    pub(crate) fn params_at(&self, abs: usize) -> Rc<Vec<ParamMeta>> {
        self.names
            .params_at(abs as u32)
            .unwrap_or_else(|| Rc::new(Vec::new()))
    }
}
