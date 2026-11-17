//! The two readings of a hypothesis in a case split's arm
//! (docs/language/matching/arm-readings-design.md).
//!
//! A `match` that refines a hypothesis `w: P(e)` binds a copy `w: P(C(x̄))`
//! under the same name in each arm, and the binder it was copied from is
//! still in scope. A use of the name is the refined copy unless the type it
//! is used at is the written one, and then it is the outer binder: the
//! place decides, not the shape of the arm's source. The equation of a
//! `match h:` reads `C(x̄) = C(x̄)` the same way, and is `refl` there.

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Expr, ExprKind, Span};
use crate::diagnostics::ElabError;
use crate::{Cx, Elaborator};

/// What a name an arm binds can also be read as.
pub(crate) enum ReadingKind {
    /// A refined hypothesis: the position of the binder it was copied from.
    Written(usize),
    /// The equation of a `match h:`: `refl` where both sides are the
    /// constructor.
    Equation,
    /// A hypothesis at this position that the match would have refined and
    /// could not: the motive that abstracts the test from its type is
    /// ill-formed, so it has its type as written only (design §3.5).
    Kept(usize),
}

/// One name with a second reading: the first binder called `name` at or
/// after position `after` (the context's length where the match stood).
pub(crate) struct Reading {
    pub(crate) name: String,
    pub(crate) after: usize,
    /// Which binder of that name, counted from `after`: a match that
    /// refines two hypotheses of one name binds two copies.
    pub(crate) nth: usize,
    pub(crate) kind: ReadingKind,
    /// How many uses of the name elaborated to the refined copy. A
    /// hypothesis no arm used refined is not generalized
    /// (design §3.4): the match is lowered again without it.
    pub(crate) uses: std::cell::Cell<u32>,
}

pub(crate) struct Readings<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Readings<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Readings<'_> {
    /// The record for the binder at `position`, if a match bound it as a
    /// copy or as its equation.
    fn at<'a>(cx: &'a Cx, position: usize) -> Option<&'a Reading> {
        let name = cx.names.iter().nth(position)?;
        cx.readings.iter_inner().map(|r| &**r).find(|r| {
            if let ReadingKind::Kept(q) = r.kind {
                return q == position;
            }
            r.name == name
                && cx.names.iter().enumerate().skip(r.after).filter(|(_, n)| *n == name).nth(r.nth).map(|(i, _)| i)
                    == Some(position)
        })
    }

    /// The outer binder the copy at `position` refines, if it is one: its
    /// reading as written (for a goal report, design §7 "Display").
    pub(crate) fn written_position(cx: &Cx, position: usize) -> Option<usize> {
        match Self::at(cx, position) {
            Some(Reading { kind: ReadingKind::Written(from), .. }) => Some(*from),
            _ => None,
        }
    }

    /// The other readings of a use of a name that elaborated to `term`,
    /// innermost first: each a variable and its type, scoped in `cx`.
    pub(crate) fn written(&self, cx: &Cx, term: &Term) -> Vec<(Term, Type)> {
        let mut out = Vec::new();
        let Term::Var(LocalVar(index)) = term else { return out };
        let len = cx.names.len();
        let Some(mut position) = len.checked_sub(1 + *index as usize) else { return out };
        while let Some(Reading { kind: ReadingKind::Written(from), .. }) = Self::at(cx, position) {
            let Some(entry) = cx.gamma.entries.get(*from) else { break };
            out.push((
                Term::Var(LocalVar((len - 1 - *from) as u32)),
                entry.ty.shift_local((len - *from) as u32),
            ));
            position = *from;
        }
        out
    }

    /// The refined reading of a `match h:`'s equation `e = C(x̄)`:
    /// `refl` at `C(x̄) = C(x̄)`.
    pub(crate) fn equation(&self, cx: &Cx, term: &Term) -> Option<(Term, Type)> {
        let Term::Var(LocalVar(index)) = term else { return None };
        let len = cx.names.len();
        let position = len.checked_sub(1 + *index as usize)?;
        let Some(Reading { kind: ReadingKind::Equation, .. }) = Self::at(cx, position) else { return None };
        let entry = cx.gamma.entries.get(position)?;
        let Type::Id { level, ty, rhs, .. } = entry.ty.shift_local((len - position) as u32) else { return None };
        Some((
            Term::Refl { level: level.clone(), ty: Rc::clone(&ty), tm: Rc::clone(&rhs) },
            Type::Id { level, ty, lhs: Rc::clone(&rhs), rhs },
        ))
    }

    /// A use of a name, elaborated to `term` at type `got`, where `expected`
    /// is wanted: another reading of it that fits, if `got` does not.
    pub(crate) fn reread(&self, cx: &Cx, term: &Term, got: &Type, expected: &Type, lvl: &Level) -> Option<(Term, Type)> {
        if cx.readings.is_empty() || got == expected || !matches!(term, Term::Var(_)) {
            return None;
        }
        let mut candidates = self.written(cx, term);
        candidates.extend(self.equation(cx, term));
        if candidates.is_empty() || self.0.conv_types(cx, got, expected, lvl) {
            return None;
        }
        let found = candidates.into_iter().find(|(_, ty)| self.0.conv_types(cx, ty, expected, lvl));
        if found.is_some() {
            Self::note_replaced(cx, term);
        }
        found
    }

    /// The readings a match registers for its arms: each refined position
    /// (not one the recursion varies, which is another value in the arm),
    /// and the equation's name.
    pub(crate) fn register(cx: &mut Cx, refined: &[usize], unrefined: &[usize], shadowed: &[&str], eqbind: Option<&str>) -> Vec<Rc<Reading>> {
        let after = cx.names.len();
        let mut registered = Vec::new();
        for &q in refined {
            if unrefined.contains(&q) {
                continue;
            }
            let Some(name) = cx.names.iter().nth(q).map(str::to_string) else { continue };
            if shadowed.contains(&name.as_str()) {
                continue;
            }
            let nth = registered.iter().filter(|r: &&Rc<Reading>| r.name == name).count();
            let reading = Rc::new(Reading { name, after, nth, kind: ReadingKind::Written(q), uses: Default::default() });
            registered.push(Rc::clone(&reading));
            cx.readings.push(reading);
        }
        if let Some(h) = eqbind {
            if !shadowed.contains(&h) {
                cx.readings.push(Rc::new(Reading { name: h.to_string(), after, nth: 0, kind: ReadingKind::Equation, uses: Default::default() }));
            }
        }
        registered
    }

    /// A use of a name elaborated to the binder at `position`.
    pub(crate) fn note_use(cx: &Cx, position: usize) {
        if cx.readings.is_empty() {
            return;
        }
        if let Some(reading @ Reading { kind: ReadingKind::Written(_), .. }) = Self::at(cx, position) {
            reading.uses.set(reading.uses.get() + 1);
        }
    }

    /// A use of `name` at `span` resolved to the binder at `position`:
    /// remembered if the name has another reading, for [`Self::refusal_note`].
    pub(crate) fn note_use_at(&self, cx: &Cx, name: &str, position: usize, span: Span) {
        Self::note_use(cx, position);
        if cx.readings.is_empty() || Self::at(cx, position).is_none() {
            return;
        }
        let kept = match Self::at(cx, position) {
            Some(Reading { kind: ReadingKind::Kept(_), .. }) => {
                let ty = cx.gamma.entries.get(position).and_then(|entry| self.0.display_type_clean(&cx.prefix(position), &entry.ty));
                Some(format!(
                    "; the match around this could not read `{name}` at its case, because taking the match's test out of \
                     its type leaves something ill-typed, so `{name}` has its type as written here{}",
                    ty.map(|t| format!(", `{t}`")).unwrap_or_default(),
                ))
            }
            _ => None,
        };
        let mut uses = self.0.attempt.reading_uses.borrow_mut();
        if !uses.iter().any(|(at, _, _)| *at == span) {
            uses.push((span, name.to_string(), kept));
        }
    }

    /// What a refused use at `span`, of type `got`, adds to its message
    /// when the name used has another reading in this arm: that reading,
    /// which was tried and does not fit either (design §3.5). Empty when
    /// the span is no such use, or the other reading does not spell.
    pub(crate) fn refusal_note(&self, cx: &Cx, span: Span, got: &Type) -> String {
        let Some(name) = self.0.attempt.reading_uses.borrow().iter().find(|(at, _, _)| *at == span).map(|(_, n, _)| n.clone()) else {
            return String::new();
        };
        if let Some(note) = self.kept_note(span) {
            return note;
        }
        let Some(position) = Self::binder(cx, &name) else { return String::new() };
        let len = cx.names.len();
        let term = Term::Var(LocalVar((len - 1 - position) as u32));
        let mut others = self.written(cx, &term);
        let equation = self.equation(cx, &term);
        if let Some(entry) = cx.gamma.entries.get(position) {
            others.push((term.clone(), entry.ty.shift_local((len - position) as u32)));
        }
        let shown = self.0.display_type_clean(cx, got);
        let mut spelled: Vec<String> = Vec::new();
        for (_, ty) in others.iter().chain(equation.iter()) {
            if let Some(s) = self.0.display_type_clean(cx, ty)
                && Some(&s) != shown.as_ref()
                && !spelled.contains(&s)
            {
                spelled.push(s);
            }
        }
        if spelled.is_empty() {
            return String::new();
        }
        let what = if equation.is_some() { "at its case, by `refl`" } else { "with the match's test as written" };
        format!(
            "; in this arm `{name}` is also {} ({what}), which is not what is expected here either",
            spelled.iter().map(|s| format!("`{s}`")).collect::<Vec<_>>().join(" and "),
        )
    }

    /// Records that the match at `cx` could not refine the hypotheses at
    /// `kept`.
    pub(crate) fn register_kept(cx: &mut Cx, kept: &[usize]) {
        let after = cx.names.len();
        for &q in kept {
            let Some(name) = cx.names.iter().nth(q).map(str::to_string) else { continue };
            cx.readings.push(Rc::new(Reading { name, after, nth: 0, kind: ReadingKind::Kept(q), uses: Default::default() }));
        }
    }

    /// Why the name used at `span` has only its type as written, if a
    /// match around it tried to refine it and could not.
    fn kept_note(&self, span: Span) -> Option<String> {
        self.0.attempt.reading_uses.borrow().iter().find(|(at, _, _)| *at == span).and_then(|(_, _, kept)| kept.clone())
    }

    /// An arm's refusal at a use of a hypothesis the match could not
    /// refine, saying so (design §3.5).
    pub(crate) fn explain(&self, error: ElabError) -> ElabError {
        match error {
            ElabError::Elab { msg, span } if !msg.contains("could not read `") => match self.kept_note(span) {
                Some(note) => ElabError::Elab { msg: format!("{msg}{note}"), span },
                None => ElabError::Elab { msg, span },
            },
            other => other,
        }
    }

    /// A use that elaborated to `term` was given another reading.
    pub(crate) fn note_replaced(cx: &Cx, term: &Term) {
        let Term::Var(LocalVar(index)) = term else { return };
        let Some(position) = cx.names.len().checked_sub(1 + *index as usize) else { return };
        if let Some(reading @ Reading { kind: ReadingKind::Written(_), .. }) = Self::at(cx, position) {
            reading.uses.set(reading.uses.get().saturating_sub(1));
        }
    }

    /// The binder a name refers to, unless a `let` shadows it.
    fn binder(cx: &Cx, name: &str) -> Option<usize> {
        let position = cx.names.lookup(name)?;
        (!cx.aliases.iter_inner().any(|a| a.name == *name && a.depth > position)).then_some(position)
    }

    /// A call that hands a match's equation to facts about its scrutinee,
    /// `k(h)` or `k(h, w)` with `k` a refined hypothesis and each argument
    /// the equation or a refined hypothesis, is taken as written if it
    /// checks as written
    /// (design §3.4): the context to elaborate it in, with the refined
    /// copies out of reach of their names. `expected` is the call's type
    /// where the position states one.
    pub(crate) fn as_written(&self, cx: &Cx, e: &Expr, expected: Option<(&Type, &Level)>) -> Option<Cx> {
        if cx.readings.is_empty() {
            return None;
        }
        let ExprKind::App { head, args, named, .. } = &e.kind else { return None };
        let ExprKind::Var(head_name) = &head.kind else { return None };
        if !named.is_empty() || args.is_empty() || !cx.readings.iter_inner().any(|r| &r.name == head_name) {
            return None;
        }
        let len = cx.names.len();
        let mut hidden: Vec<usize> = Vec::new();
        let mut origin = |mut position: usize| {
            while let Some(Reading { kind: ReadingKind::Written(from), .. }) = Self::at(cx, position) {
                hidden.push(position);
                position = *from;
            }
            position
        };
        let head_position = Self::binder(cx, head_name)?;
        let Some(Reading { kind: ReadingKind::Written(_), .. }) = Self::at(cx, head_position) else { return None };
        let head_origin = origin(head_position);
        let type_at = |position: usize| cx.gamma.entries.get(position).map(|entry| entry.ty.shift_local((len - position) as u32));
        // The call hands the match's equation on: without it there is no
        // written fact for the others to be beside.
        let mut equation = false;
        let mut ty = type_at(head_origin)?;
        let mut level = cx.gamma.entries.get(head_origin)?.level.clone();
        for arg in args {
            let ExprKind::Var(name) = &arg.kind else { return None };
            let position = Self::binder(cx, name)?;
            let at = match &Self::at(cx, position)?.kind {
                ReadingKind::Written(_) => origin(position),
                ReadingKind::Equation => {
                    equation = true;
                    position
                }
                ReadingKind::Kept(_) => return None,
            };
            let Type::Pi { dom_level, cod_level, dom, cod } = self.0.whnf(cx, &ty, e.span).ok()? else { return None };
            if !self.0.conv_types(cx, &type_at(at)?, &dom, &dom_level) {
                return None;
            }
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Var(LocalVar((len - 1 - at) as u32)))));
            level = cod_level;
        }
        if hidden.is_empty() || !equation {
            return None;
        }
        if let Some((expected, expected_level)) = expected
            && !(level.equiv(expected_level) && self.0.conv_types(cx, &ty, expected, expected_level))
        {
            return None;
        }
        let mut written = cx.clone();
        written.names = cx.names.renamed_at(&hidden, |name| format!("#written:{name}"));
        Some(written)
    }
}
