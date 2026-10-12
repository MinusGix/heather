//! Named and positional argument normalization before spine elaboration.

use heather_syntax::{Expr, ExprKind, NamedArg, Span};

use super::ParamMeta;
use crate::inductive::Inductive;
use crate::{ElabError, R, err};

/// A defaulted parameter a call left out (docs/named-arguments-design.md §9):
/// the marker's arguments are the declaring global's key and the parameter's
/// index in its table, and checking it runs the default against the
/// parameter's instantiated domain. Like the parser's markers, this head
/// cannot collide with a source name.
pub(crate) const PARAM_DEFAULT: &str = "\0param-default";

/// The marker standing for `default`'s parameter in a call that left it out.
fn default_marker(default: &super::ParamDefault, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(Expr { kind: ExprKind::Var(PARAM_DEFAULT.into()), span }),
            args: vec![
                Expr { kind: ExprKind::Str(default.owner.clone()), span },
                Expr { kind: ExprKind::Num((default.index as u64).into()), span },
            ],
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

/// Named arguments at a **callable** head (docs/named-arguments-design.md
/// §8.3): permute the written `x := e` arguments into declaration order
/// and hand the result to the ordinary spine walkers, which never learn
/// that any name was written.
///
/// Returns the argument vector for the parameters this call fills and the
/// **adjusted mask** — a named implicit's or solver parameter's `true`
/// flips to `false`, so its slot consumes the written argument instead of
/// minting a meta or a resolution obligation. That flip is the whole of
/// the elaboration change: the flipped slot then travels
/// `apply_implicit`'s ordinary explicit-argument path, which already
/// zonks the domain against the solutions learned so far, defers a
/// checking-only argument at a metaful domain, and drives `unify_arg_ty`
/// otherwise.
///
/// A **defaulted** parameter the call left out is filled here too, by
/// [`PARAM_DEFAULT`]'s marker with its mask bit flipped, so the default is
/// a named argument the caller did not have to write: checked at the
/// parameter's domain in declaration order, and deferred until that domain
/// is known, by the same path (docs/named-arguments-design.md §9.6).
///
/// `None` — and *nothing cloned* — when no named argument was written and
/// the call leaves no default to fill, which is this round's invariant: such
/// a call reaches the walkers with exactly the vector and mask it did before.
#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve_named(
    callee: &str,
    value_head: bool,
    params: &[ParamMeta],
    param_offset: usize,
    mask: &[bool],
    args: &[Expr],
    named: &[NamedArg],
    span: Span,
) -> R<Option<(Vec<Expr>, Vec<bool>)>> {
    let n = mask.len();
    let defaulted = |mi: usize| {
        mask[mi] && params.get(mi + param_offset).is_some_and(|p| p.default.is_some())
    };
    if named.is_empty() && !(0..n).any(defaulted) {
        return Ok(None);
    }
    let mut slots: Vec<Option<Expr>> = vec![None; n];
    let mut written: Vec<Option<Span>> = vec![None; n];
    let mut newmask = mask.to_vec();
    // The positional prefix fills the explicit parameters in declaration
    // order, exactly as it does today.
    let mut rest = args.iter();
    for mi in 0..n {
        if mask[mi] {
            continue;
        }
        let Some(a) = rest.next() else { break };
        slots[mi] = Some(a.clone());
        written[mi] = Some(a.span);
    }
    // Over-application spills onto the call's *result*, whose `Type::Pi`
    // has no names at all (§4.3), so the two do not compose. Checked
    // *after* the names below, so that a callee with no parameter table at
    // all — where "more than it has parameters" is vacuously true — still
    // gets §7's message about names rather than one about arity.
    let over_applied = rest.next().is_some();
    for na in named {
        let Some(pi) = params.iter().position(|p| p.name == na.name) else {
            return Err(no_such_param(
                callee,
                value_head,
                params,
                param_offset,
                mask,
                na,
            ));
        };
        let p = &params[pi];
        if p.is_type {
            return err(
                format!(
                    "`{}` is a type parameter of `{callee}`, and a type argument is a \
                     *type* rather than an expression — write `{callee}<…>` \
                     (docs/named-arguments-design.md §5.3)",
                    na.name
                ),
                na.name_span,
            );
        }
        if pi < param_offset {
            return err(
                format!(
                    "`{}` is already given by `{callee}<…>`: the written type arguments \
                     fill the leading parameters",
                    na.name
                ),
                na.name_span,
            );
        }
        let mi = pi - param_offset;
        if mi >= n {
            return err(
                format!("`{}` is not a parameter this call fills", na.name),
                na.name_span,
            );
        }
        if written[mi].is_some() {
            let msg = if p.is_self {
                format!(
                    "`{}` is `{callee}`'s receiver parameter, so a method call `e.{callee}(…)` \
                     already fills it — `{} := …` fills it a second time. Give it by name \
                     only in the plain-call spelling `{callee}(…)`",
                    na.name, na.name
                )
            } else {
                format!(
                    "`{}` is given twice: once already, and again as `{} := …`",
                    na.name, na.name
                )
            };
            return err(msg, na.name_span);
        }
        slots[mi] = Some(na.expr.clone());
        written[mi] = Some(na.name_span);
        // The third state of the mask: given by name, so the slot is
        // filled by the written argument rather than inferred or searched.
        newmask[mi] = false;
    }
    if over_applied && named.is_empty() {
        // Only a default made this call reach here: its positional
        // arguments outnumber the parameters that take one by position.
        let first = (0..n).find(|&mi| defaulted(mi)).expect("a default to fill");
        let name = &params[first + param_offset].name;
        return err(
            format!(
                "`{callee}` takes {} argument(s) by position, found {}: `{name}` has a \
                 default, so it has no positional slot — give it by name (`{name} := …`)",
                mask.iter().filter(|&&m| !m).count(),
                args.len(),
            ),
            span,
        );
    }
    // Every defaulted parameter the call left out is filled from its
    // default: the third state of the mask again, with the caller's
    // argument supplied by the declaration.
    for mi in 0..n {
        if slots[mi].is_none() && newmask[mi] && defaulted(mi) {
            let default = params[mi + param_offset].default.as_deref().expect("defaulted");
            slots[mi] = Some(default_marker(default, span));
            newmask[mi] = false;
        }
    }
    if over_applied {
        return err(
            format!(
                "`{callee}` is applied to more arguments than it has parameters, and a \
                 named argument cannot name one past the end: the extra arguments apply \
                 to the *result* of the call, whose type binds no parameter names"
            ),
            named[0].span,
        );
    }
    // No gaps (§4.3): an explicit parameter the named arguments jumped
    // over has nothing to put in its spine position.
    let mut out = Vec::with_capacity(n);
    for (mi, slot) in slots.into_iter().enumerate() {
        match slot {
            Some(e) => out.push(e),
            None if newmask[mi] => {}
            None => {
                let what = params.get(mi + param_offset).map_or_else(
                    || format!("parameter {}", mi + 1),
                    |p| format!("`{}`", p.name),
                );
                let why = if named.is_empty() {
                    "A call that leaves a parameter to its default has to fill every \
                     parameter before it — partial application and parameter defaults do \
                     not compose"
                } else {
                    "A call that names an argument has to fill every parameter before it — \
                     partial application and named arguments do not compose"
                };
                return err(
                    format!("`{callee}` is applied to too few arguments: {what} has none. {why}"),
                    span,
                );
            }
        }
    }
    Ok(Some((out, newmask)))
}

/// The refusal for a named argument whose name no parameter has
/// (docs/named-arguments-design.md §7): two messages, because a callee
/// with no parameter *names* is a different situation from a typo.
fn no_such_param(
    callee: &str,
    value_head: bool,
    params: &[ParamMeta],
    param_offset: usize,
    mask: &[bool],
    na: &NamedArg,
) -> ElabError {
    // `#i` is what `skel_params` gives a binder that was never named. It
    // is unspellable — no identifier starts with `#` — so it can never be
    // *matched* by accident; this message is the only way to reach one.
    let nameable: Vec<&str> = params
        .iter()
        .skip(param_offset)
        .take(mask.len())
        .filter(|p| !p.is_type && !p.name.starts_with('#'))
        .map(|p| p.name.as_str())
        .collect();
    let msg = if nameable.is_empty() && value_head {
        format!(
            "`{callee}` is a value whose type binds no parameter names, so its arguments \
             are positional (issues/implicit-binders-in-function-types.md). Write the \
             argument positionally, or annotate the binder — `(x: T) -> …`"
        )
    } else if nameable.is_empty() {
        format!("`{callee}` has no named parameters to fill: write the arguments positionally")
    } else {
        format!(
            "`{callee}` has no parameter named `{}` (it has: {})",
            na.name,
            nameable.join(", ")
        )
    };
    ElabError::Elab {
        msg,
        span: na.name_span,
    }
}

/// The refusal for a named argument at a head that has no parameter table
/// at all — a builtin arm, an expression in head position, a self-call
/// (docs/named-arguments-design.md §8.2). Called *centrally*, so a form
/// that never learned about names cannot silently drop one.
pub(crate) fn refuse_named(what: &str, why: &str, named: &[NamedArg]) -> R<()> {
    match named.first() {
        None => Ok(()),
        Some(na) => err(
            format!("{what} takes positional arguments only: {why}"),
            na.name_span,
        ),
    }
}

/// Named arguments at a **constructor** (docs/named-arguments-design.md
/// §6): permute by field name into field order. Shares
/// [`permute_by_name_refs`] with the record literal, so
/// `Monoid(unit := 0)` and `Monoid { unit: 0 }` cannot drift into
/// disagreeing about what is unknown, duplicated or missing.
///
/// `None`, cloning nothing, when no name was written — which is what
/// leaves a partially applied constructor (`Cons(1)`, η-expanded against
/// an expected Π) on exactly the path it was on before. Naming an
/// argument *does* require saturating, for §4.3's reason.
pub(crate) fn resolve_constructor_arguments<'a>(
    ind: &Inductive,
    i: usize,
    args: &[&'a Expr],
    named: &[&'a NamedArg],
    span: Span,
) -> R<Option<Vec<&'a Expr>>> {
    if named.is_empty() {
        return Ok(None);
    }
    let cname = ind.ctors[i].name.clone();
    let decl: Vec<&str> = ind.ctors[i]
        .fields
        .iter()
        .map(|(n, _)| n.as_deref().unwrap_or("_"))
        .collect();
    let written: Vec<(&str, &Expr, Span)> = named
        .iter()
        .map(|na| (na.name.as_str(), &na.expr, na.name_span))
        .collect();
    permute_by_name_refs(&cname, "field", &decl, args, &written, span).map(Some)
}

/// Permute a by-name argument list into declaration order: the one
/// function behind the record literal `D { f: e }` (§6 of
/// docs/surface-records.md) and the named-argument constructor call
/// `C(f := e)` (§6 of docs/named-arguments-design.md).
///
/// One function rather than two, because these two spellings say the same
/// thing and their diagnostics must not be able to disagree about what is
/// unknown, what is duplicated and what is missing.
///
/// `positional` is the prefix given without names (always empty for a
/// literal); `written` is `(name, value, span-of-the-name)`.
pub(crate) fn permute_by_name_refs<'a>(
    owner: &str,
    noun: &str,
    decl: &[&str],
    positional: &[&'a Expr],
    written: &[(&str, &'a Expr, Span)],
    span: Span,
) -> R<Vec<&'a Expr>> {
    let mut slots: Vec<Option<&Expr>> = vec![None; decl.len()];
    if positional.len() > decl.len() {
        return err(
            format!(
                "`{owner}` takes {} {noun}(s), found {}",
                decl.len(),
                positional.len() + written.len()
            ),
            span,
        );
    }
    for (i, a) in positional.iter().enumerate() {
        slots[i] = Some(*a);
    }
    for (name, value, nsp) in written {
        let Some(i) = decl.iter().position(|d| d == name) else {
            // An unnamed field is spelled `_` in `decl` and is therefore
            // unmatchable, which is right: a positional-only constructor
            // gains nothing here and must not pretend to.
            return err(
                format!(
                    "`{owner}` has no {noun} `{name}` (it has: {})",
                    decl.join(", ")
                ),
                *nsp,
            );
        };
        if slots[i].is_some() {
            return err(format!("{noun} `{name}` is given twice"), *nsp);
        }
        slots[i] = Some(value);
    }
    let missing: Vec<&str> = decl
        .iter()
        .zip(&slots)
        .filter(|(_, s)| s.is_none())
        .map(|(d, _)| *d)
        .collect();
    if !missing.is_empty() {
        return err(
            format!("`{owner}` is missing {noun}(s): {}", missing.join(", ")),
            span,
        );
    }
    Ok(slots
        .into_iter()
        .map(|s| s.expect("checked above"))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use heather_syntax::ExprKind;

    const SPAN: Span = Span { start: 0, end: 1 };

    fn expression(value: u64) -> Expr {
        Expr {
            kind: ExprKind::Num(value.into()),
            span: SPAN,
        }
    }

    fn parameter(name: &str, implicit: bool) -> ParamMeta {
        ParamMeta {
            name: name.into(),
            implicit,
            is_type: false,
            is_self: false,
            skel: None,
            solver: None,
            default: None,
        }
    }

    #[test]
    fn an_unnamed_call_is_a_zero_allocation_decline() {
        let params = [parameter("x", false)];
        assert!(
            resolve_named(
                "f",
                false,
                &params,
                0,
                &[false],
                &[expression(0)],
                &[],
                SPAN
            )
            .expect("unnamed call")
            .is_none()
        );
    }

    #[test]
    fn named_arguments_fill_implicit_slots_in_declaration_order() {
        let params = [
            parameter("x", false),
            parameter("evidence", true),
            parameter("y", false),
        ];
        let named = [
            NamedArg {
                name: "evidence".into(),
                name_span: SPAN,
                expr: expression(1),
                span: SPAN,
            },
            NamedArg {
                name: "y".into(),
                name_span: SPAN,
                expr: expression(2),
                span: SPAN,
            },
        ];
        let (arguments, mask) = resolve_named(
            "f",
            false,
            &params,
            0,
            &[false, true, false],
            &[expression(0)],
            &named,
            SPAN,
        )
        .expect("named call")
        .expect("normalization");
        assert!(matches!(&arguments[0].kind, ExprKind::Num(__n) if __n.as_u64() == Some(0)));
        assert!(matches!(&arguments[1].kind, ExprKind::Num(__n) if __n.as_u64() == Some(1)));
        assert!(matches!(&arguments[2].kind, ExprKind::Num(__n) if __n.as_u64() == Some(2)));
        assert_eq!(mask, [false, false, false]);
    }

    #[test]
    fn record_and_constructor_fields_share_one_permutation() {
        let first = expression(1);
        let second = expression(2);
        let written = [("right", &second, SPAN), ("left", &first, SPAN)];
        let ordered = permute_by_name_refs("Pair", "field", &["left", "right"], &[], &written, SPAN)
            .expect("field permutation");
        assert!(std::ptr::eq(ordered[0], &first));
        assert!(std::ptr::eq(ordered[1], &second));
        assert!(matches!(&ordered[0].kind, ExprKind::Num(__n) if __n.as_u64() == Some(1)));
        assert!(matches!(&ordered[1].kind, ExprKind::Num(__n) if __n.as_u64() == Some(2)));
    }
}
