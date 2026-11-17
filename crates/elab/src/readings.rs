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
use heather_kernel::term::{LocalVar, Term, Type};
use crate::{Cx, Elaborator};

/// What a name an arm binds can also be read as.
pub(crate) enum ReadingKind {
    /// A refined hypothesis: the position of the binder it was copied from.
    Written(usize),
    /// The equation of a `match h:`: `refl` where both sides are the
    /// constructor.
    Equation,
}

/// One name with a second reading: the first binder called `name` at or
/// after position `after` (the context's length where the match stood).
pub(crate) struct Reading {
    pub(crate) name: String,
    pub(crate) after: usize,
    pub(crate) kind: ReadingKind,
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
            r.name == name
                && cx.names.iter().enumerate().skip(r.after).find(|(_, n)| *n == name).map(|(i, _)| i)
                    == Some(position)
        })
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
        candidates.into_iter().find(|(_, ty)| self.0.conv_types(cx, ty, expected, lvl))
    }

    /// The readings a match registers for its arms: each refined position
    /// (not one the recursion varies, which is another value in the arm),
    /// and the equation's name.
    pub(crate) fn register(cx: &mut Cx, refined: &[usize], unrefined: &[usize], shadowed: &[&str], eqbind: Option<&str>) {
        let after = cx.names.len();
        for &q in refined {
            if unrefined.contains(&q) {
                continue;
            }
            let Some(name) = cx.names.iter().nth(q).map(str::to_string) else { continue };
            if shadowed.contains(&name.as_str()) {
                continue;
            }
            cx.readings.push(Rc::new(Reading { name, after, kind: ReadingKind::Written(q) }));
        }
        if let Some(h) = eqbind {
            if !shadowed.contains(&h) {
                cx.readings.push(Rc::new(Reading { name: h.to_string(), after, kind: ReadingKind::Equation }));
            }
        }
    }
}
