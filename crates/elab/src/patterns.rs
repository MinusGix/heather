//! Deep patterns and the `_` arm — the pattern-matrix preprocessing
//! (`docs/nested-match-patterns-design.md`).
//!
//! This module is the mechanization of that document and is meant to be read
//! against it; the section numbers in the comments are its.
//!
//! The doctrine, in one line: **nothing here builds a kernel term.** The pass
//! rewrites surface arms into surface arms, and every lowering below it —
//! `elab_match_nat`, `elab_match_fin`, `elab_match_data`, `elab_match_wf`,
//! `elab_match_indexed`, `elab_match_iwf` — is called with exactly the arm
//! shape it accepted before this existed (§1). The one thing that is not pure
//! surface is the *sharing* device of §5, which elaborates one body early and
//! parks it in an [`Alias`]; that too is machinery the elaborator already had.
//!
//! The pass is **idempotent** and its fast path is "no arm is `_` and no
//! binder is a constructor pattern", which is every `match` written before
//! this round (§9).

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::{
    ANON_CTOR_LEFT, ANON_CTOR_ONLY, ANON_CTOR_RIGHT, Arm, Block, Expr, ExprKind, MatchForm, Pat,
    Span, Stmt,
};

use crate::inductive::{FieldKind, decoded};
use crate::{Alias, Cx, Elaborator, R, err};
use crate::indexed::IndexedFamilies;
use crate::iwf_family::IwfFamily;

/// One row of the matrix: a pattern per column, the body it selects, and the
/// pattern variables the columns it has already been specialized *past* bound
/// (§3.2 — those become `let` aliases at the leaf).
#[derive(Clone)]
struct Row {
    pats: Vec<Pat>,
    /// Index into the arm list, which is also the identity of the body: two
    /// leaves carrying the same `body` are two copies of one arm (§5).
    body: usize,
    /// `(user name, column variable)`, innermost last.
    binds: Vec<(String, String)>,
    span: Span,
}

fn is_anonymous_ctor(name: &str) -> bool {
    matches!(name, ANON_CTOR_ONLY | ANON_CTOR_LEFT | ANON_CTOR_RIGHT)
}

fn anonymous_ctor_name<'a>(ind: &'a crate::inductive::Inductive, written: &str) -> Option<&'a str> {
    let index = match written {
        ANON_CTOR_ONLY if ind.ctors.len() == 1 => 0,
        ANON_CTOR_LEFT if ind.ctors.len() == 2 => 0,
        ANON_CTOR_RIGHT if ind.ctors.len() == 2 => 1,
        _ => return None,
    };
    Some(ind.ctors[index].name.as_str())
}

/// The type evidence attached to one pattern-matrix column. A stored field
/// type may depend on the fields before it, so the context travels with the
/// type rather than being reconstructed from a surface name later.
#[derive(Clone)]
struct PatCol {
    cx: Cx,
    ty: Type,
    lvl: Level,
}

/// The mutable state of one compilation: the fresh-name counter and the leaf
/// census that §5 needs.
struct Compile {
    next: usize,
    /// The form the *written* match was spelled as, carried so that a
    /// generated inner level names it rather than saying `match` at a block
    /// whose text says `split` (issues/diagnostics-name-the-written-form.md).
    /// A generated level has no spelling of its own — it stands for a pattern
    /// column — so the one it inherits is the only honest answer available.
    form: MatchForm,
    /// Whether the arms being compiled are a generated level's (§7.1 of
    /// `docs/diagnostic-warnings-design.md`): ours, not the writer's, so an
    /// unreachable one is not their problem to hear about.
    generated: bool,
    /// How many leaves each arm's body reached.
    uses: Vec<usize>,
    /// Whether each arm ever bound a pattern variable at a leaf. A row that
    /// binds nothing means the same term wherever it lands, which is §5.1's
    /// condition 1.
    binding: Vec<bool>,
}

impl Compile {
    fn fresh(&mut self) -> String {
        let n = self.next;
        self.next += 1;
        format!("#p{n}")
    }
}

/// What to say about an arm that reached no leaf, given the arms *before* it —
/// which are the only ones that can have shadowed it, first match being the
/// rule (§3.3).
///
/// The two shapes are the two the redundancy issue lists, and they want
/// different advice: a `_` that covers nothing is a spelling the writer can
/// simply drop, while a shadowed constructor arm usually means one of the
/// earlier patterns is wider than its author thought.
fn unreachable_msg(a: &Arm, before: &[Arm], form: MatchForm) -> String {
    let kw = form.keyword();
    if a.default {
        return format!(
            "this `_` arm can never be reached: the arms above it already cover every \
             constructor, so it stands for nothing. Deleting it does not change what \
             this `{kw}` means"
        );
    }
    let shadowed_by_same = before.iter().any(|b| b.ctor == a.ctor);
    format!(
        "this `{}` arm can never be reached: {} already matches every value it does, and \
         first match wins (docs/nested-match-patterns-design.md §3.3), so its body is \
         never run — and never checked",
        a.ctor,
        if shadowed_by_same {
            format!("an earlier `{}` arm", a.ctor)
        } else {
            format!("an earlier arm of this `{kw}`")
        }
    )
}

/// The placeholder a leaf carries until §5 decides between sharing and
/// copying. Unspellable, so it can only ever refer to what this module put
/// there.
fn slot(body: usize) -> String {
    format!("#arm{body}")
}

/// Pattern elaboration's part of the elaborator.
pub(crate) struct Patterns<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Patterns<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Patterns<'_> {
    /// §9. Rewrite a `match`'s arms so that every binder is a plain name and
    /// no arm is `_`. Returns `None` when there was nothing to do — the common
    /// case, and the one that must stay free.
    ///
    /// The returned [`Cx`] differs from the argument only in `aliases`: it is
    /// `Γ`-identical, so a caller may use it for the arms and the original for
    /// anything scoped before the match without either being wrong.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_arms(
        &self,
        cx: &Cx,
        form: MatchForm,
        // Whether the pattern compiler built the node these arms came from.
        // Read only to decide whether an unreachable arm is worth reporting
        // (`docs/diagnostic-warnings-design.md` §7.1).
        generated: bool,
        arms: &[Arm],
        scrut_t: &Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        result: &Type,
        independent: bool,
        mlvl: &Level,
        span: Span,
    ) -> R<Option<(Cx, Vec<Arm>)>> {
        let had_anonymous = arms.iter().any(|a| is_anonymous_ctor(&a.ctor));
        let arms = self.resolve_anonymous_arms(cx, arms, scrut_ty, span)?;
        let arms = arms.as_slice();
        let has_named = arms.iter().any(|a| a.binders.iter().any(Pat::has_named));
        // The fast path, and the reason the pass may be called from three
        // entry points without anyone costing it (§9). A bare identifier is
        // classified against its own column type, not the global constructor
        // table: two visible constructors of one name must not turn it into a
        // binder (issues/deep-pattern-ctor-needs-column-type.md).
        let has_deep = arms.iter().any(|a| {
            let cols = self.pattern_fields_at(cx, scrut_ty, scrut_lvl, &a.ctor, span);
            a.binders
                .iter()
                .enumerate()
                .any(|(j, p)| self.pat_is_deep_at(p, cols.as_ref().and_then(|cs| cs.get(j))))
        });
        if !had_anonymous && !has_named && !arms.iter().any(|a| a.default) && !has_deep {
            return Ok(None);
        }
        self.check_default_arms(arms, span)?;
        let arms = if has_named {
            self.normalize_named_arms(cx, arms, scrut_ty, span)?
        } else {
            arms.to_vec()
        };
        // §3.5: a sub-pattern identifier that names a constructor *of its
        // column type* is that constructor. Done before anything else, so
        // `is_deep` below sees the reclassified shape.
        let arms: Vec<Arm> = arms
            .iter()
            .map(|a| Arm {
                binders: {
                    let cols = self.pattern_fields_at(cx, scrut_ty, scrut_lvl, &a.ctor, span);
                    a.binders
                        .iter()
                        .enumerate()
                        .map(|(j, p)| self.reclassify_at(p, cols.as_ref().and_then(|cs| cs.get(j))))
                        .collect()
                },
                ..a.clone()
            })
            .collect();
        let deep = arms.iter().any(|a| a.binders.iter().any(|p| p.is_deep()));
        if deep {
            self.check_deep_allowed(cx, form, &arms, scrut_t, scrut_ty, span)?;
        }
        let (rows, ctors) = self.matrix(cx, &arms, scrut_ty, span)?;
        // The generated column names must shadow *nothing*: a leaf deep in the
        // tree refers to a column bound several levels above it, and this pass
        // runs again on every level it emits (§9), so a per-call counter
        // starting at zero would have the inner run rebind the outer run's
        // names. Start past everything in scope and everything the arms
        // already mention, which is exactly the set a generated name could
        // collide with.
        let mut next = 0;
        let mut bump = |n: &str| {
            if let Some(k) = n.strip_prefix("#p").and_then(|d| d.parse::<usize>().ok()) {
                next = next.max(k + 1);
            }
        };
        cx.names.iter().for_each(|n| bump(n));
        cx.aliases.iter().for_each(|a| bump(&a.name));
        for a in &arms {
            pat_names(&a.binders, &mut bump);
        }
        let mut st = Compile {
            form,
            generated,
            next,
            uses: vec![0; arms.len()],
            binding: vec![false; arms.len()],
        };
        let out = self.emit_top(&mut st, &arms, rows, ctors, span)?;
        self.settle(cx, &arms, out, &st, result, independent, mlvl)
            .map(Some)
    }

    // -- validation (§4, §6, §7) --------------------------------------------

    /// §4: at most one `_`, and it is last. First-match semantics (§3.3) would
    /// otherwise make every following arm dead, silently.
    fn check_default_arms(&self, arms: &[Arm], _span: Span) -> R<()> {
        let mut seen: Option<&Arm> = None;
        for a in arms {
            if let Some(prev) = seen {
                return err(
                    format!(
                        "a `_` arm must be the last arm: `{}` after it can never be \
                         reached, because `_` already stands for every constructor \
                         with no arm of its own",
                        if a.default { "_" } else { a.ctor.as_str() }
                    ),
                    prev.span,
                );
            }
            if a.default {
                seen = Some(a);
            }
        }
        Ok(())
    }

    /// §6 and §7 — the two places a deep pattern is refused, both because some
    /// *other* machinery reads the binder this feature would move.
    fn check_deep_allowed(
        &self,
        cx: &Cx,
        form: MatchForm,
        arms: &[Arm],
        scrut_t: &Term,
        scrut_ty: &Type,
        span: Span,
    ) -> R<()> {
        // §6: the termination guard matches a self-call's argument against
        // this level's binder, and a deep pattern moves it one level down.
        // The trigger is a self-call *in an arm*, not merely a match on a
        // parameter: the guard is only ever read by `elab_self_call`, so a
        // declaration that does not call itself here has nothing to lose. The
        // scan is a sound over-approximation — a mention of the name that is
        // not a call still refuses, and there is no such mention that
        // elaborates (a bare self-reference is already an error). A case
        // split inside the recursion (`recursion::guard_param`) hands its
        // arms the enclosing guard, so its patterns may be deep.
        if let Some(dec) = crate::recursion::guard_param(cx, scrut_t, arms)
            && let Some(s) = cx.selfref.as_ref()
            && arms
                .iter()
                .any(|a| {
                    crate::inductive::expr_mentions(&a.body, &s.name)
                        || (s.written_name != s.name
                            && crate::inductive::expr_mentions(&a.body, &s.written_name))
                })
        {
            return err(
                format!(
                    "a deep pattern is not available in this `{}`: it descends on \
                     `{}`, a parameter of `{}`, so its arm binders are what the \
                     termination guard matches a recursive call's argument against. \
                     Match the field in a nested `match` inside the arm instead \
                     (docs/nested-match-patterns-design.md \u{a7}6)",
                    form.keyword(),
                    s.params[dec].0,
                    s.name
                ),
                span,
            );
        }
        // §7: an index field's binder is not a value binder — it is aliased to
        // a component of the index pattern, and the guard's `rebind` reads it.
        let fam = IwfFamily(self)
            .iwf_of_at(cx, scrut_ty)
            .map(|(i, _)| i)
            .or_else(|| IndexedFamilies(self).indexed_of_at(cx, scrut_ty).map(|(i, _)| i));
        let Some(ind) = fam else { return Ok(()) };
        for a in arms {
            let Some(i) = crate::inductive::arm_ctor_index(&ind, &a.ctor) else {
                continue;
            };
            for (k, p) in a.binders.iter().enumerate() {
                if p.is_deep() && matches!(ind.ctors[i].kind.get(k), Some(FieldKind::IndexVar)) {
                    return err(
                        format!(
                            "a deep pattern is not available at field {k} of `{}`: `{}` \
                             is an indexed family, and that binder is the arm's *index* \
                             pattern variable rather than a value — it is determined by \
                             the scrutinee's index, so there is nothing here to case on \
                             (docs/nested-match-patterns-design.md \u{a7}7)",
                            a.ctor, ind.name
                        ),
                        p.span(),
                    );
                }
            }
        }
        Ok(())
    }

    // -- the matrix (§3.3) ---------------------------------------------------

    /// The initial rows, plus the constructor set when one is needed.
    ///
    /// The set is needed exactly when a `_` arm is present (§4): that is the
    /// one question the pattern compiler cannot defer to the level below,
    /// because the level below is what it would have to *build*.
    #[allow(clippy::type_complexity)]
    fn matrix(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrut_ty: &Type,
        span: Span,
    ) -> R<(Vec<(usize, Row)>, Option<Vec<(String, usize)>>)> {
        let mut rows = Vec::new();
        for (i, a) in arms.iter().enumerate() {
            if a.default {
                continue;
            }
            rows.push((
                i,
                Row {
                    pats: a.binders.clone(),
                    body: i,
                    binds: vec![],
                    span: a.span,
                },
            ));
        }
        if !arms.iter().any(|a| a.default) {
            return Ok((rows, None));
        }
        let Some(ctors) = self.ctors_at(cx, scrut_ty, span) else {
            return err(
                "a `_` arm needs the scrutinee's type to have a known set of \
                 constructors, and this one does not — there is nothing to expand it \
                 to. Write the arms out",
                span,
            );
        };
        Ok((rows, Some(ctors)))
    }

    /// The top level: group the rows by their arm's constructor, and emit one
    /// arm per constructor (§3.3). The `_` row, if there is one, joins *every*
    /// group as an all-wildcard row and supplies the constructors that have no
    /// group at all — which is §4's expansion, done in the same step.
    fn emit_top(
        &self,
        st: &mut Compile,
        arms: &[Arm],
        rows: Vec<(usize, Row)>,
        ctors: Option<Vec<(String, usize)>>,
        span: Span,
    ) -> R<Vec<Arm>> {
        let dflt = arms.iter().position(|a| a.default);
        // Constructor order: the declaration's when we have it (so the `_`
        // expansion is deterministic), the source's otherwise.
        let mut order: Vec<String> = Vec::new();
        if let Some(cs) = &ctors {
            order.extend(cs.iter().map(|(n, _)| n.clone()));
        } else {
            for (i, _) in &rows {
                if !order.contains(&arms[*i].ctor) {
                    order.push(arms[*i].ctor.clone());
                }
            }
        }
        let mut out = Vec::new();
        for name in order {
            let group: Vec<&Row> = rows
                .iter()
                .filter(|(i, _)| arms[*i].ctor == name)
                .map(|(_, r)| r)
                .collect();
            // The arity: the declared one when known, else what the arms
            // agree on. A disagreement is the ordinary arity error, raised by
            // the lowering below once the true arity is in hand — except that
            // the columns have to line up *here*, so a disagreement inside a
            // group is caught here too.
            let arity = match &ctors {
                Some(cs) => cs.iter().find(|(n, _)| *n == name).map(|(_, k)| *k),
                None => None,
            };
            let arity = match arity {
                Some(k) => k,
                None => group.first().map(|r| r.pats.len()).unwrap_or(0),
            };
            for r in &group {
                if r.pats.len() != arity && ctors.is_some() {
                    return err(
                        format!("`{name}` binds {arity} field(s), found {}", r.pats.len()),
                        r.span,
                    );
                }
            }
            let mut sub: Vec<Row> = group.iter().map(|r| (*r).clone()).collect();
            if let Some(d) = dflt {
                sub.push(Row {
                    pats: (0..arity).map(|_| wild(span)).collect(),
                    body: d,
                    binds: vec![],
                    span: arms[d].span,
                });
            }
            if sub.is_empty() {
                // No arm and no `_`: the missing-arm error belongs to the
                // lowering, which knows the family's name.
                continue;
            }
            // Preserve the pre-feature output exactly when there is nothing to
            // compile: one row, all binders plain. This is what keeps a
            // `match` that only gained a `_` arm byte-identical to the one
            // that spells its arms out.
            // First match (§3.3): if the *first* row's patterns are all
            // variables it wins at every leaf below this constructor, so the
            // rows behind it are unreachable here and there is nothing to
            // compile. This is also what keeps a `match` that only gained a
            // `_` arm emitting byte-identically to one that spells its arms
            // out.
            let flat = !sub[0].pats.iter().any(|p| p.is_deep());
            let (binders, body) = if flat {
                let r = &sub[0];
                st.uses[r.body] += 1;
                if r.pats.iter().any(|p| p.name() != "_") {
                    st.binding[r.body] = true;
                }
                (r.pats.clone(), placeholder(r.body, arms[r.body].body.span))
            } else {
                let cols: Vec<String> = (0..arity).map(|_| st.fresh()).collect();
                let body = self.compile(st, arms, &cols, sub, span)?;
                let binders = cols
                    .iter()
                    .map(|c| Pat::Var {
                        name: c.clone(),
                        span,
                    })
                    .collect();
                (binders, body)
            };
            // The arm's span is its *first* source row's, so an arity or
            // duplicate diagnostic still lands where the user wrote it.
            let aspan = group.first().map(|r| r.span).unwrap_or(span);
            out.push(Arm {
                ctor: name,
                default: false,
                binders,
                body,
                span: aspan,
            });
        }
        Ok(out)
    }

    /// The matrix recursion (§3.3): pick the leftmost column some row does not
    /// have a variable at, `match` on it, and recurse. A column with no
    /// constructor pattern anywhere is never split, which is what makes the
    /// emitted nesting the one the pattern reads like.
    fn compile(
        &self,
        st: &mut Compile,
        arms: &[Arm],
        cols: &[String],
        rows: Vec<Row>,
        span: Span,
    ) -> R<Expr> {
        let col = cols
            .iter()
            .enumerate()
            .position(|(j, _)| rows.iter().any(|r| r.pats[j].is_deep()));
        let Some(j) = col else {
            // A leaf: first match wins (§3.3).
            let r = &rows[0];
            return Ok(self.leaf(st, arms, cols, r));
        };
        // Group by the constructor at column `j`, in source order; every
        // variable row joins every group *and* forms the `_` branch.
        let mut order: Vec<String> = Vec::new();
        for r in &rows {
            if let Pat::Ctor { name, .. } = &r.pats[j] {
                if !order.contains(name) {
                    order.push(name.clone());
                }
            }
        }
        let mut out: Vec<Arm> = Vec::new();
        for name in &order {
            let arity = rows
                .iter()
                .find_map(|r| match &r.pats[j] {
                    Pat::Ctor { name: n, args, .. } if n == name => Some(args.len()),
                    _ => None,
                })
                .expect("the name came from a row");
            let sub_cols: Vec<String> = (0..arity).map(|_| st.fresh()).collect();
            let mut cols2 = cols.to_vec();
            cols2.splice(j..j + 1, sub_cols.iter().cloned());
            let mut sub: Vec<Row> = Vec::new();
            for r in &rows {
                match &r.pats[j] {
                    Pat::Ctor { name: n, args, .. } if n == name => {
                        if args.len() != arity {
                            return err(
                                format!(
                                    "`{name}` binds {arity} field(s) in an earlier \
                                     pattern of this `{}`, found {}",
                                    st.form.keyword(),
                                    args.len()
                                ),
                                r.pats[j].span(),
                            );
                        }
                        let mut r2 = r.clone();
                        r2.pats.splice(j..j + 1, args.iter().cloned());
                        sub.push(r2);
                    }
                    Pat::Ctor { .. } => {}
                    Pat::Var { name: v, .. } => {
                        let mut r2 = r.clone();
                        if v != "_" {
                            r2.binds.push((v.clone(), cols[j].clone()));
                        }
                        r2.pats.splice(j..j + 1, (0..arity).map(|_| wild(r.span)));
                        sub.push(r2);
                    }
                    Pat::Named { .. } => unreachable!("named patterns are normalized first"),
                }
            }
            let body = self.compile(st, arms, &cols2, sub, span)?;
            out.push(Arm {
                ctor: name.clone(),
                default: false,
                binders: sub_cols
                    .iter()
                    .map(|c| Pat::Var {
                        name: c.clone(),
                        span,
                    })
                    .collect(),
                body,
                span,
            });
        }
        // The `_` branch carries the variable rows only — they are the rows
        // that match a constructor with no group, and they do not bind that
        // constructor's fields, which is exactly right: they never named them.
        let fallthrough: Vec<Row> = rows
            .iter()
            .filter(|r| !r.pats[j].is_deep())
            .map(|r| {
                let mut r2 = r.clone();
                if let Pat::Var { name: v, .. } = &r.pats[j]
                    && v != "_"
                {
                    r2.binds.push((v.clone(), cols[j].clone()));
                }
                r2.pats.remove(j);
                r2
            })
            .collect();
        if !fallthrough.is_empty() {
            let mut cols2 = cols.to_vec();
            cols2.remove(j);
            let body = self.compile(st, arms, &cols2, fallthrough, span)?;
            out.push(Arm {
                ctor: "_".to_string(),
                default: true,
                binders: vec![],
                body,
                span,
            });
        }
        Ok(Expr {
            kind: ExprKind::Match {
                form: st.form,
                // §7.1: our level, our arms.
                generated: true,
                scrut: Box::new(Expr {
                    kind: ExprKind::Var(cols[j].clone()),
                    span,
                }),
                eqbind: None,
                motive: None,
                arms: out,
            },
            // The whole match's span: a missing-arm error inside a *generated*
            // level has nowhere better to point (§3.4).
            span,
        })
    }

    /// A leaf: the row's body, wrapped in the `let` aliases that bind its
    /// pattern variables to the columns they came from (§3.2). An alias is
    /// inlined at each use, so this costs nothing in the emitted term.
    fn leaf(&self, st: &mut Compile, arms: &[Arm], cols: &[String], r: &Row) -> Expr {
        let span = arms[r.body].body.span;
        st.uses[r.body] += 1;
        let mut stmts: Vec<Stmt> = Vec::new();
        for (name, col) in &r.binds {
            stmts.push(let_alias(name, col, span));
        }
        for (j, p) in r.pats.iter().enumerate() {
            if p.name() != "_" {
                stmts.push(let_alias(p.name(), &cols[j], span));
            }
        }
        if stmts.is_empty() {
            return placeholder(r.body, span);
        }
        st.binding[r.body] = true;
        Expr {
            kind: ExprKind::Block(Box::new(Block {
                stmts,
                result: Box::new(placeholder(r.body, span)),
                ons: vec![],
                span,
            })),
            span,
        }
    }

    // -- §5: sharing, or copying -------------------------------------------

    /// Replace every placeholder with the arm body it stands for, sharing the
    /// ones that landed in more than one leaf when §5.1 allows.
    #[allow(clippy::too_many_arguments)]
    fn settle(
        &self,
        cx: &Cx,
        arms: &[Arm],
        out: Vec<Arm>,
        st: &Compile,
        result: &Type,
        independent: bool,
        mlvl: &Level,
    ) -> R<(Cx, Vec<Arm>)> {
        let mut cx2 = cx.clone();
        let mut bodies: Vec<Option<Expr>> = vec![None; arms.len()];
        for (i, a) in arms.iter().enumerate() {
            match st.uses[i] {
                // No leaf: nothing this arm matches is left by the arms above
                // it, so its body is never elaborated and never runs. That
                // silence was deliberate and is the redundancy half of
                // issues/match-arm-redundancy-warning.md; with a warning
                // channel it can finally be *said*
                // (docs/diagnostic-warnings-design.md §7). The census is the
                // one §5 already computes for sharing — reachability is not a
                // new analysis, it is this number being zero.
                0 => {
                    if !st.generated {
                        self.emit_lint(
                            crate::Lint::UnreachableMatchArm,
                            unreachable_msg(a, &arms[..i], st.form),
                            a.span,
                        );
                    }
                }
                1 => bodies[i] = Some(a.body.clone()),
                n => {
                    if independent && !st.binding[i] {
                        // §5.2: elaborate once, park it in an alias, and let
                        // alias resolution do the per-arm weakening.
                        let t = self.elab_check(&cx2, &a.body, result, mlvl)?;
                        cx2.aliases.push(Rc::new(Alias {
                            skel: None,
                            name: slot(i),
                            depth: cx2.names.len(),
                            term: Rc::new(t),
                            ty: result.clone(),
                            level: mlvl.clone(),
                            spliced: None,
                            shifted: Default::default(),
                        }));
                        // The placeholder already *is* a reference to it.
                        continue;
                    }
                    if crate::count_holes_expr(&a.body) > 0 {
                        return err(
                            format!(
                                "this arm's body is used by {n} of the compiled arms, and \
                                 it contains a `?goal`, which cannot be elaborated more \
                                 than once. {} Write the arms out, or move the goal \
                                 outside the `match` \
                                 (docs/nested-match-patterns-design.md \u{a7}10.3)",
                                if independent {
                                    "It is copied because it binds pattern variables, \
                                     which mean different things in different arms."
                                } else {
                                    "It is copied because the motive mentions the \
                                     scrutinee, so the arms have different types."
                                }
                            ),
                            a.body.span,
                        );
                    }
                    bodies[i] = Some(a.body.clone());
                }
            }
        }
        let out = out.into_iter().map(|a| fill_arm(a, &bodies)).collect();
        Ok((cx2, out))
    }

    // -- helpers -------------------------------------------------------------

    /// §3.5. The parser cannot know whether a bare identifier is a nullary
    /// constructor. The column type can: it names exactly one declaration,
    /// even when the written constructor name is ambiguous in the surrounding
    /// module scope.
    fn reclassify_at(&self, p: &Pat, col: Option<&PatCol>) -> Pat {
        match p {
            Pat::Var { name, span }
                if col.is_some_and(|c| {
                    self.pattern_fields_at(&c.cx, &c.ty, &c.lvl, name, *span)
                        .is_some()
                }) =>
            {
                Pat::Ctor {
                    name: name.clone(),
                    args: vec![],
                    span: *span,
                }
            }
            Pat::Var { .. } => p.clone(),
            Pat::Ctor { name, args, span } => {
                let resolved = col
                    .and_then(|c| self.inductive_at(&c.cx, &c.ty, *span))
                    .and_then(|ind| anonymous_ctor_name(&ind, name).map(str::to_owned))
                    .unwrap_or_else(|| name.clone());
                Pat::Ctor {
                    name: resolved.clone(),
                    args: {
                        let cols = col.and_then(|c| {
                            self.pattern_fields_at(&c.cx, &c.ty, &c.lvl, &resolved, *span)
                        });
                        args.iter()
                            .enumerate()
                            .map(|(j, a)| {
                                self.reclassify_at(a, cols.as_ref().and_then(|cs| cs.get(j)))
                            })
                            .collect()
                    },
                    span: *span,
                }
            }
            Pat::Named { field, pat, span } => Pat::Named {
                field: field.clone(),
                pat: Box::new(self.reclassify_at(pat, col)),
                span: *span,
            },
        }
    }

    fn pat_is_deep_at(&self, p: &Pat, col: Option<&PatCol>) -> bool {
        match p {
            Pat::Ctor { .. } => true,
            Pat::Var { name, span } => col.is_some_and(|c| {
                self.pattern_fields_at(&c.cx, &c.ty, &c.lvl, name, *span)
                    .is_some()
            }),
            Pat::Named { pat, .. } => self.pat_is_deep_at(pat, col),
        }
    }

    /// The actual types of constructor fields at one instantiated scrutinee
    /// type. Payloads are read from the lowering's Sigma spine, so a field
    /// declared as `A` at `Outer<Inner>` is seen here as `Inner`, not as the
    /// stored surface variable. Plain recursive children have the scrutinee's
    /// own type. This is the same information the arm lowerings project when
    /// the generated inner match is elaborated.
    fn pattern_fields_at(
        &self,
        cx: &Cx,
        ty: &Type,
        lvl: &Level,
        ctor_name: &str,
        span: Span,
    ) -> Option<Vec<PatCol>> {
        if let Type::Fin { len } = &*decoded(ty) {
            let len_w = self.whnf_tm(cx, len, span).ok()?;
            let pred = match crate::inductive::nat_head(&len_w) {
                crate::inductive::NatHead::Zero => return None,
                crate::inductive::NatHead::Succ(k) => k,
                crate::inductive::NatHead::Neutral => return None,
            };
            return match ctor_name {
                "FZ" => Some(vec![]),
                "FS" => Some(vec![PatCol {
                    cx: cx.clone(),
                    ty: Type::Fin { len: pred },
                    lvl: Level::Zero,
                }]),
                _ => None,
            };
        }
        let head = self.whnf(cx, ty, span).ok()?;
        if matches!(head, Type::Nat) {
            return match ctor_name {
                "Zero" => Some(vec![]),
                "Succ" => Some(vec![PatCol {
                    cx: cx.clone(),
                    ty: Type::Nat,
                    lvl: Level::Zero,
                }]),
                _ => None,
            };
        }
        let ind = self.inductive_at(cx, ty, span)?;
        let ctor_name = anonymous_ctor_name(&ind, ctor_name).unwrap_or(ctor_name);
        let i = crate::inductive::arm_ctor_index(&ind, ctor_name)?;
        let ctor = &ind.ctors[i];
        let spine = self.spine(ty, lvl, ind.ctors.len(), span).ok()?;
        let mut pcx = cx.clone();
        let mut cur = (*spine.ctors[i].0).clone();
        let mut payloads = Vec::new();
        let mut first = true;
        loop {
            let Type::Sigma {
                fst_level,
                snd,
                fst,
                ..
            } = self.whnf(&pcx, &cur, span).ok()?
            else {
                break;
            };
            if !first {
                payloads.push(PatCol {
                    cx: pcx.clone(),
                    ty: (*fst).clone(),
                    lvl: fst_level.clone(),
                });
            }
            first = false;
            let next = snd.apply_local(
                &crate::embed(&pcx.gamma, 1).extended(Rc::new(Term::Var(LocalVar(0)))),
            );
            pcx.push(
                format!("#pat{}", pcx.names.len()),
                (*fst).clone(),
                fst_level,
            );
            cur = next;
        }
        if payloads.len() != ctor.payload().count() {
            return None;
        }
        let mut payloads = payloads.into_iter();
        let by = (pcx.names.len() - cx.names.len()) as u32;
        let unknown = || PatCol {
            cx: pcx.clone(),
            ty: Type::Ty(Level::Zero),
            lvl: Level::succ(Level::Zero),
        };
        let fields = ctor
            .kind
            .iter()
            .map(|kind| match kind {
                FieldKind::Payload => payloads.next(),
                FieldKind::Plain => Some(PatCol {
                    cx: pcx.clone(),
                    ty: ty.shift_local(by),
                    lvl: lvl.clone(),
                }),
                // A container is a primitive Vec and an IndexVar is supplied
                // by the family eliminator. Neither has declared constructors
                // for a deep surface pattern to select here; retain an
                // explicitly constructor-less column so sibling payloads do
                // not lose their type evidence.
                FieldKind::Container { .. } | FieldKind::IndexVar | FieldKind::FnChild => {
                    Some(unknown())
                }
            })
            .collect::<Option<Vec<_>>>()?;
        Some(fields)
    }

    fn resolve_anonymous_arms(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrut_ty: &Type,
        span: Span,
    ) -> R<Vec<Arm>> {
        if !arms.iter().any(|a| is_anonymous_ctor(&a.ctor)) {
            return Ok(arms.to_vec());
        }
        let Some(ind) = self.inductive_at(cx, scrut_ty, span) else {
            return err(
                "anonymous constructor patterns need an inductive or record scrutinee",
                span,
            );
        };
        arms.iter()
            .map(|arm| {
                if !is_anonymous_ctor(&arm.ctor) {
                    return Ok(arm.clone());
                }
                let Some(name) = anonymous_ctor_name(&ind, &arm.ctor) else {
                    let want = if arm.ctor == ANON_CTOR_ONLY { 1 } else { 2 };
                    return err(
                        format!(
                            "this anonymous constructor pattern needs a type with {want} constructor(s), but `{}` has {}",
                            ind.name,
                            ind.ctors.len()
                        ),
                        arm.span,
                    );
                };
                Ok(Arm { ctor: name.to_owned(), ..arm.clone() })
            })
            .collect()
    }

    /// Restore declaration order for every `field := pattern` list before
    /// the positional pattern matrix sees it. Omitted named fields become
    /// `_`; the old positional path is returned unchanged apart from nested
    /// named patterns.
    fn normalize_named_arms(
        &self,
        cx: &Cx,
        arms: &[Arm],
        scrut_ty: &Type,
        span: Span,
    ) -> R<Vec<Arm>> {
        let ind = self.inductive_at(cx, scrut_ty, span);
        let mut out = Vec::with_capacity(arms.len());
        for arm in arms {
            if arm.default {
                out.push(arm.clone());
                continue;
            }
            let Some(ind) = ind.as_ref() else {
                if arm.binders.iter().any(Pat::has_named) {
                    return err(
                        format!(
                            "`{}` has positional-only pattern fields; write its binders by position",
                            arm.ctor
                        ),
                        arm.span,
                    );
                }
                out.push(arm.clone());
                continue;
            };
            let Some(i) = crate::inductive::arm_ctor_index(ind, &arm.ctor) else {
                // Preserve the ordinary unknown-constructor diagnostic.
                out.push(arm.clone());
                continue;
            };
            let binders = self.normalize_pat_args(&arm.ctor, &arm.binders, &ind.ctors[i].fields)?;
            out.push(Arm {
                binders,
                ..arm.clone()
            });
        }
        Ok(out)
    }

    fn normalize_pat(&self, p: &Pat) -> R<Pat> {
        match p {
            Pat::Var { .. } => Ok(p.clone()),
            Pat::Named { .. } => unreachable!("a named pattern is normalized with its siblings"),
            Pat::Ctor { name, args, span } => {
                let fields = self
                    .ctor_of(name)
                    .map(|(ind, i)| ind.ctors[i].fields.clone());
                let args = match fields {
                    Some(fields) => self.normalize_pat_args(name, args, &fields)?,
                    None if args.iter().any(Pat::has_named) => {
                        return err(
                            format!(
                                "`{name}` has positional-only pattern fields; write its binders by position"
                            ),
                            *span,
                        );
                    }
                    None => args
                        .iter()
                        .map(|a| self.normalize_pat(a))
                        .collect::<R<_>>()?,
                };
                Ok(Pat::Ctor {
                    name: name.clone(),
                    args,
                    span: *span,
                })
            }
        }
    }

    fn normalize_pat_args(
        &self,
        ctor: &str,
        args: &[Pat],
        fields: &[(Option<String>, heather_syntax::Ty)],
    ) -> R<Vec<Pat>> {
        let named = args.iter().any(|p| matches!(p, Pat::Named { .. }));
        if !named {
            return args.iter().map(|p| self.normalize_pat(p)).collect();
        }
        if args.iter().any(|p| !matches!(p, Pat::Named { .. })) {
            return err(
                format!(
                    "a `{ctor}` pattern cannot mix positional binders with `field := pattern`; use one form"
                ),
                args.iter()
                    .find(|p| !matches!(p, Pat::Named { .. }))
                    .unwrap()
                    .span(),
            );
        }
        if fields.iter().all(|(n, _)| n.is_none()) {
            return err(
                format!(
                    "`{ctor}` has positional-only pattern fields; write its binders by position"
                ),
                args[0].span(),
            );
        }
        let mut out: Vec<Pat> = fields.iter().map(|_| wild(args[0].span())).collect();
        let mut used = vec![false; fields.len()];
        for arg in args {
            let Pat::Named { field, pat, span } = arg else {
                unreachable!()
            };
            let Some(i) = fields.iter().position(|(n, _)| n.as_deref() == Some(field)) else {
                return err(format!("`{ctor}` has no field `{field}`"), *span);
            };
            if used[i] {
                return err(
                    format!("field `{field}` appears twice in this `{ctor}` pattern"),
                    *span,
                );
            }
            used[i] = true;
            out[i] = self.normalize_pat(pat)?;
        }
        Ok(out)
    }

    fn inductive_at(
        &self,
        cx: &Cx,
        ty: &Type,
        span: Span,
    ) -> Option<Rc<crate::inductive::Inductive>> {
        if let Some((ind, _)) = IwfFamily(self).iwf_of_at(cx, ty) {
            return Some(ind);
        }
        let head = self.whnf(cx, ty, span).ok()?;
        if !matches!(head, Type::Empty { .. })
            && let Some((ind, _)) = IndexedFamilies(self).indexed_of_at(cx, ty)
        {
            return Some(ind);
        }
        self.tag_of(&head)
    }

    /// §4: the scrutinee type's constructors and their arities, in declaration
    /// order. Mirrors [`Routes::elab_match`](crate::matching::Routes::elab_match)'s dispatch, and deliberately
    /// so: a `_` must expand to exactly the arms that dispatch will demand.
    fn ctors_at(&self, cx: &Cx, scrut_ty: &Type, span: Span) -> Option<Vec<(String, usize)>> {
        let named = |ind: &crate::inductive::Inductive| {
            ind.ctors
                .iter()
                .map(|c| (c.name.clone(), c.fields.len()))
                .collect::<Vec<_>>()
        };
        if let Some((ind, fam)) = IwfFamily(self).iwf_of_at(cx, scrut_ty) {
            // A mutual group's member: its own constructors, the only ones a
            // `match` on it has arms for (docs/mutual-inductive-design.md §4).
            if let Some(m) = (!ind.members.is_empty())
                .then(|| IwfFamily(self).iwf_member_at(cx, &ind, &fam.idx, span))
                .flatten()
            {
                return Some(
                    ind.members[m]
                        .ctors
                        .iter()
                        .map(|&k| (ind.ctors[k].name.clone(), ind.ctors[k].fields.len()))
                        .collect(),
                );
            }
            return Some(named(&ind));
        }
        let head = self.whnf(cx, scrut_ty, span).ok()?;
        if !matches!(head, Type::Empty { .. })
            && let Some((ind, _)) = IndexedFamilies(self).indexed_of_at(cx, scrut_ty)
        {
            return Some(named(&ind));
        }
        if let Some(ind) = self.tag_of(&head) {
            return Some(named(&ind));
        }
        if let Type::Fin { len } = &*decoded(scrut_ty) {
            let len_w = self.whnf_tm(cx, len, span).ok()?;
            return match crate::inductive::nat_head(&len_w) {
                crate::inductive::NatHead::Zero => Some(vec![]),
                crate::inductive::NatHead::Succ(_) => {
                    Some(vec![("FZ".into(), 0), ("FS".into(), 1)])
                }
                crate::inductive::NatHead::Neutral => None,
            };
        }
        match head {
            Type::Empty { .. } => Some(vec![]),
            Type::Nat => Some(vec![("Zero".into(), 0), ("Succ".into(), 1)]),
            _ => None,
        }
    }
}

/// Every binder name written anywhere in a pattern list.
fn pat_names(ps: &[Pat], f: &mut impl FnMut(&str)) {
    for p in ps {
        match p {
            Pat::Var { name, .. } => f(name),
            Pat::Ctor { args, .. } => pat_names(args, f),
            Pat::Named { pat, .. } => pat_names(std::slice::from_ref(pat), f),
        }
    }
}

fn wild(span: Span) -> Pat {
    Pat::Var {
        name: "_".to_string(),
        span,
    }
}

fn placeholder(body: usize, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Var(slot(body)),
        span,
    }
}

fn let_alias(name: &str, col: &str, span: Span) -> Stmt {
    Stmt::Let {
        name: name.to_string(),
        ty: None,
        expr: Expr {
            kind: ExprKind::Var(col.to_string()),
            span,
        },
        span,
        opaque: false,
    }
}

/// Substitute the settled bodies for their placeholders. Only the node shapes
/// this module generates are walked — a placeholder cannot occur anywhere
/// else, since its name is unspellable.
fn fill_arm(a: Arm, bodies: &[Option<Expr>]) -> Arm {
    Arm {
        body: fill(a.body, bodies),
        ..a
    }
}

fn fill(e: Expr, bodies: &[Option<Expr>]) -> Expr {
    match e.kind {
        ExprKind::Var(ref n) => {
            let Some(i) = n.strip_prefix("#arm").and_then(|d| d.parse::<usize>().ok()) else {
                return e;
            };
            match bodies.get(i).and_then(|b| b.clone()) {
                // `None` is the shared case: the alias is in scope and the
                // placeholder is already the reference to it.
                None => e,
                Some(b) => b,
            }
        }
        ExprKind::Block(b) => {
            let Block {
                stmts,
                result,
                ons,
                span,
            } = *b;
            Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(fill(*result, bodies)),
                    ons,
                    span,
                })),
                span: e.span,
            }
        }
        ExprKind::Match {
            form,
            generated,
            scrut,
            eqbind,
            motive,
            arms,
        } => Expr {
            kind: ExprKind::Match {
                form,
                generated,
                scrut,
                eqbind,
                motive,
                arms: arms.into_iter().map(|a| fill_arm(a, bodies)).collect(),
            },
            span: e.span,
        },
        _ => e,
    }
}
