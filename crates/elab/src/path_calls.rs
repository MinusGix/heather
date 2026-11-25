//! A call that lends places `&mut` (docs/language/sequencing-surface-design.md
//! §24, docs/language/ownership-design.md §10.3).
//!
//! The parser expands `let r = f(&mut a, x, &mut b.g);` into the call,
//! marked `\0pathcall` with each lent place marked `\0mutarg`, and the
//! assignments that rebind the places from the callee's `Mutated` nest. What
//! is left here is to elaborate the call with the markers dropped, after
//! holding each marked argument to the callee's parameter at that place: a
//! live-path (`&mut`) parameter exactly where an argument is lent. The test
//! reads the modes the declaration recorded ([`crate::application::ParamMeta`]),
//! and the call's type is held to one `Mutated` per lent place, which is the
//! whole check where the callee has no recorded table (its own recursion, a
//! local function).
//!
//! Bookkeeping, not a discipline: nothing here asks who else reaches a place
//! (vision principle 7; the judgment over reflected code is a library's).

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, ParamMode, Span};

use crate::application::{subject_index_in, Callables, ParamMeta};
use crate::dispatch::Members;
use crate::statements::StatementElab;
use crate::{err, Cx, Elaborator, R};

pub(crate) struct PathCalls<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for PathCalls<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

/// The input of `marker(e)`.
fn unmark<'e>(e: &'e Expr, marker: &str) -> Option<&'e Expr> {
    match &e.kind {
        ExprKind::App { head, args, .. } if args.len() == 1 && matches!(&head.kind, ExprKind::Var(n) if n == marker) => {
            Some(&args[0])
        }
        _ => None,
    }
}

impl PathCalls<'_> {
    /// `\0pathcall(call)` read as the call, or a `\0mutarg` the parser left
    /// where no statement takes it, refused. `None` for anything else.
    pub(crate) fn read(&self, cx: &Cx, e: &Expr) -> Option<R<(Term, Type, Level)>> {
        if unmark(e, heather_syntax::MUTARG).is_some() {
            return Some(err(
                "a `&mut` argument is lent by a call that is a statement, a `let`'s value or a block's \
                 end, `let r = f(&mut a);`, where the place can be rebound after it: not inside another \
                 expression (docs/language/sequencing-surface-design.md §24)",
                e.span,
            ));
        }
        let call = unmark(e, heather_syntax::PATHCALL)?;
        Some(self.path_call(cx, call, false, e.span))
    }

    /// Does `call` lend a place at its top, `f(…, \0mutarg(a), …)`?
    pub(crate) fn lends(call: &Expr) -> bool {
        let args = match &call.kind {
            ExprKind::App { args, .. } => args,
            ExprKind::Dot { args: Some(args), .. } => args,
            _ => return false,
        };
        args.iter().any(|a| unmark(a, heather_syntax::MUTARG).is_some())
    }

    /// A call that lends places, elaborated with the markers dropped once
    /// each lent argument is held to the callee's modes. `candidate` is a
    /// method call on a mutable place, which the statement that binds it
    /// rebinds when the callee's receiver is a live path
    /// (`statements::elaborate_mut_call`): its receiver may then be `&mut`,
    /// and the call's type has one more `Mutated`, the receiver's,
    /// outermost.
    pub(crate) fn path_call(&self, cx: &Cx, call: &Expr, candidate: bool, span: Span) -> R<(Term, Type, Level)> {
        let (args, named, explicit) = match &call.kind {
            ExprKind::App { args, named, explicit, .. } => (args, named, *explicit),
            ExprKind::Dot { args: Some(args), named, .. } => (args, named, false),
            _ => return err("a `&mut` argument is lent to a call", span),
        };
        let lent: Vec<bool> = args.iter().map(|a| unmark(a, heather_syntax::MUTARG).is_some()).collect();
        let stripped_args: Vec<Expr> =
            args.iter().map(|a| unmark(a, heather_syntax::MUTARG).cloned().unwrap_or_else(|| a.clone())).collect();
        let mut stripped = call.clone();
        match &mut stripped.kind {
            ExprKind::App { args, .. } => *args = stripped_args,
            ExprKind::Dot { args: Some(args), .. } => *args = stripped_args,
            _ => unreachable!(),
        }
        if !explicit {
            let named: Vec<&str> = named.iter().map(|n| n.name.as_str()).collect();
            self.check_modes(cx, call, &lent, &named, candidate, span)?;
        }
        let (term, ty, level) = self.0.infer_mut_call(cx, &stripped)?;
        // One `Mutated` per lent place, the answer innermost, and the
        // receiver's outermost when it comes back.
        let threaded = candidate && Members(self).threads_receiver(cx, &stripped) == Some(true);
        let count = lent.iter().filter(|l| **l).count() + usize::from(threaded);
        let mut at = (Rc::new(term.clone()), ty.clone());
        for k in 0..count {
            let record = self
                .0
                .record_for_destructuring(cx, &at.1, span)
                .filter(|r| r.name == heather_syntax::MUTATED_RECORD);
            let Some(record) = record else {
                return err(
                    format!(
                        "this call lends {count} place{} `&mut`, so its value is one `Mutated` record per \
                         place, and {}: the callee's parameters there are not `&mut`",
                        if count == 1 { "" } else { "s" },
                        if k == 0 { "it is none".to_string() } else { format!("it has {k}") },
                    ),
                    span,
                );
            };
            let (t, ty, _) = self.0.project_destructured_field(cx, &record, &at.1, Rc::clone(&at.0), 1, span)?;
            at = (Rc::new(t), ty);
        }
        Ok((term, ty, level))
    }

    /// The callee's recorded modes against the lent arguments: a `&mut`
    /// parameter where, and only where, an argument is lent. A callee with
    /// no table (a local, its own recursion) is left to the type check.
    fn check_modes(&self, cx: &Cx, call: &Expr, lent: &[bool], named: &[&str], candidate: bool, span: Span) -> R<()> {
        let (callee, method) = match &call.kind {
            ExprKind::App { head, .. } => match &head.kind {
                ExprKind::Var(f) if !cx.names.iter_inner().any(|n| n == f) => (f.clone(), false),
                _ => return Ok(()),
            },
            ExprKind::Dot { recv, name, .. } => (Members(self).member_head(cx, recv, name, false, call.span)?, true),
            _ => return Ok(()),
        };
        let table = Callables(self).params_of(&callee);
        if table.is_empty() {
            return Ok(());
        }
        let shown = callee.rsplit("::").next().unwrap_or(&callee);
        let explicit: Vec<&ParamMeta> = table.iter().filter(|p| !p.implicit && !named.contains(&p.name.as_str())).collect();
        let explicit: Vec<&ParamMeta> = if method {
            let subject = subject_index_in(&table);
            if !candidate && explicit.get(subject).is_some_and(|p| p.mode == ParamMode::Path) {
                return err(
                    format!(
                        "`{shown}`'s receiver is a `&mut` parameter, so it comes back to its place, and this \
                         receiver is not one that can be rebound: call `{shown}` on a `let mut` local, a `mut` \
                         or `&mut` parameter or a field path of one, or lend every place in the plain call, \
                         `{callee}(&mut …, …)`"
                    ),
                    span,
                );
            }
            explicit.iter().enumerate().filter(|(i, _)| *i != subject).map(|(_, p)| *p).collect()
        } else {
            explicit
        };
        for (i, p) in explicit.iter().enumerate() {
            let is_lent = lent.get(i).copied();
            match (p.mode == ParamMode::Path, is_lent) {
                (true, Some(false)) => {
                    return err(
                        format!(
                            "`{shown}` takes `{}` as `&mut`, so its argument is a place it lends back: \
                             write `&mut` before it, or call `{shown}` with no `&mut` at all for its \
                             `Mutated` record",
                            p.name
                        ),
                        span,
                    );
                }
                (false, Some(true)) => {
                    return err(
                        format!(
                            "`{shown}`'s parameter `{}` is not `&mut`, so nothing comes back to the place \
                             lent it: pass the value, without `&mut`",
                            p.name
                        ),
                        span,
                    );
                }
                _ => {}
            }
        }
        Ok(())
    }
}
