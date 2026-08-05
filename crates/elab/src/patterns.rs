//! Deep patterns and the `_` arm — the pattern-matrix preprocessing
//! (`docs/nested-match-patterns-design.md`).
//!
//! This module is the mechanization of that document and is meant to be read
//! against it; the section numbers in the comments are its.
//!
//! The doctrine, in one line: **nothing here builds a kernel term.** The pass
//! rewrites surface arms into surface arms, and every lowering below it —
//! `elab_match_nat`, `elab_match_fin`, `elab_match_data`, `elab_match_wf`,
//! `elab_match_indexed`, `elab_match_forded` — is called with exactly the arm
//! shape it accepted before this existed (§1). The one thing that is not pure
//! surface is the *sharing* device of §5, which elaborates one body early and
//! parks it in an [`Alias`]; that too is machinery the elaborator already had.
//!
//! The pass is **idempotent** and its fast path is "no arm is `_` and no
//! binder is a constructor pattern", which is every `match` written before
//! this round (§9).

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Arm, Block, Expr, ExprKind, Pat, Span, Stmt};

use crate::inductive::{decoded, FieldKind};
use crate::{err, Alias, Cx, Elaborator, R};

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

/// The mutable state of one compilation: the fresh-name counter and the leaf
/// census that §5 needs.
struct Compile {
    next: usize,
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

/// The placeholder a leaf carries until §5 decides between sharing and
/// copying. Unspellable, so it can only ever refer to what this module put
/// there.
fn slot(body: usize) -> String {
    format!("#arm{body}")
}

impl Elaborator {
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
        arms: &[Arm],
        scrut_t: &Term,
        scrut_ty: &Type,
        result: &Type,
        independent: bool,
        mlvl: &Level,
        span: Span,
    ) -> R<Option<(Cx, Vec<Arm>)>> {
        // The fast path, and the reason the pass may be called from three
        // entry points without anyone costing it (§9).
        if !arms.iter().any(|a| a.default || a.binders.iter().any(|p| self.pat_is_deep(p))) {
            return Ok(None);
        }
        self.check_default_arms(arms, span)?;
        // §3.5: a sub-pattern identifier that names a constructor *is* that
        // constructor, exactly as in expression position. Done before
        // anything else, so `is_deep` below sees the reclassified shape.
        let arms: Vec<Arm> = arms
            .iter()
            .map(|a| Arm {
                binders: a.binders.iter().map(|p| self.reclassify(p)).collect(),
                ..a.clone()
            })
            .collect();
        let deep = arms.iter().any(|a| a.binders.iter().any(|p| p.is_deep()));
        if deep {
            self.check_deep_allowed(cx, &arms, scrut_t, scrut_ty, span)?;
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
            next,
            uses: vec![0; arms.len()],
            binding: vec![false; arms.len()],
        };
        let out = self.emit_top(&mut st, &arms, rows, ctors, span)?;
        self.settle(cx, &arms, out, &st, result, independent, mlvl).map(Some)
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
        // elaborates (a bare self-reference is already an error).
        if let Some(dec) = self.descends_on_param(cx, scrut_t)
            && let Some(s) = cx.selfref.as_ref()
            && arms.iter().any(|a| crate::inductive::expr_mentions(&a.body, &s.name))
        {
            return err(
                format!(
                    "a deep pattern is not available in this `match`: it descends on \
                     `{}`, a parameter of `{}`, so its arm binders are what the \
                     termination guard matches a recursive call's argument against. \
                     Match the field in a nested `match` inside the arm instead \
                     (docs/nested-match-patterns-design.md \u{a7}6)",
                    s.params[dec].0, s.name
                ),
                span,
            );
        }
        // §7: an index field's binder is not a value binder — it is aliased to
        // a component of the index pattern, and the guard's `rebind` reads it.
        let fam = self
            .forded_of_at(cx, scrut_ty)
            .map(|(i, _)| i)
            .or_else(|| self.indexed_of_at(cx, scrut_ty).map(|(i, _)| i));
        let Some(ind) = fam else { return Ok(()) };
        for a in arms {
            let Some(i) = crate::inductive::arm_ctor_index(&ind, &a.ctor) else { continue };
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
                    .map(|c| Pat::Var { name: c.clone(), span })
                    .collect();
                (binders, body)
            };
            // The arm's span is its *first* source row's, so an arity or
            // duplicate diagnostic still lands where the user wrote it.
            let aspan = group.first().map(|r| r.span).unwrap_or(span);
            out.push(Arm { ctor: name, default: false, binders, body, span: aspan });
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
                                     pattern of this `match`, found {}",
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
                }
            }
            let body = self.compile(st, arms, &cols2, sub, span)?;
            out.push(Arm {
                ctor: name.clone(),
                default: false,
                binders: sub_cols
                    .iter()
                    .map(|c| Pat::Var { name: c.clone(), span })
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
                0 => {}
                1 => bodies[i] = Some(a.body.clone()),
                n => {
                    if independent && !st.binding[i] {
                        // §5.2: elaborate once, park it in an alias, and let
                        // alias resolution do the per-arm weakening.
                        let t = self.elab_check(&cx2, &a.body, result, mlvl)?;
                        cx2.aliases.push(Rc::new(Alias {
                            name: slot(i),
                            depth: cx2.names.len(),
                            term: Rc::new(t),
                            ty: result.clone(),
                            level: mlvl.clone(),
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
    /// constructor, so this decides it, by the same rule expression position
    /// uses. `Zero`/`Succ`/`FZ`/`FS` are named explicitly: they are the
    /// kernel's, not any declaration's, so `ctor_of` has never heard of them.
    fn reclassify(&self, p: &Pat) -> Pat {
        match p {
            Pat::Var { name, span } if self.is_ctor_name(name) => {
                Pat::Ctor { name: name.clone(), args: vec![], span: *span }
            }
            Pat::Var { .. } => p.clone(),
            Pat::Ctor { name, args, span } => Pat::Ctor {
                name: name.clone(),
                args: args.iter().map(|a| self.reclassify(a)).collect(),
                span: *span,
            },
        }
    }

    fn is_ctor_name(&self, name: &str) -> bool {
        matches!(name, "Zero" | "Succ" | "FZ" | "FS") || self.ctor_of(name).is_some()
    }

    fn pat_is_deep(&self, p: &Pat) -> bool {
        match p {
            Pat::Ctor { .. } => true,
            Pat::Var { name, .. } => self.is_ctor_name(name),
        }
    }

    /// §4: the scrutinee type's constructors and their arities, in declaration
    /// order. Mirrors [`Elaborator::elab_match`]'s dispatch, and deliberately
    /// so: a `_` must expand to exactly the arms that dispatch will demand.
    fn ctors_at(&self, cx: &Cx, scrut_ty: &Type, span: Span) -> Option<Vec<(String, usize)>> {
        let named = |ind: &crate::inductive::Inductive| {
            ind.ctors.iter().map(|c| (c.name.clone(), c.fields.len())).collect::<Vec<_>>()
        };
        if let Some((ind, _)) = self.forded_of_at(cx, scrut_ty) {
            return Some(named(&ind));
        }
        let head = self.whnf(cx, scrut_ty, span).ok()?;
        if !matches!(head, Type::Empty { .. })
            && let Some((ind, _)) = self.indexed_of_at(cx, scrut_ty)
        {
            return Some(named(&ind));
        }
        if let Some(ind) = self.tag_of(&head) {
            return Some(named(&ind));
        }
        if let Type::Fin { len } = &*decoded(scrut_ty) {
            return match &*self.whnf_tm(cx, len, span).ok()? {
                Term::Zero => Some(vec![]),
                Term::Succ(_) => Some(vec![("FZ".into(), 0), ("FS".into(), 1)]),
                _ => None,
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
        }
    }
}

fn wild(span: Span) -> Pat {
    Pat::Var { name: "_".to_string(), span }
}

fn placeholder(body: usize, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(slot(body)), span }
}

fn let_alias(name: &str, col: &str, span: Span) -> Stmt {
    Stmt::Let {
        name: name.to_string(),
        ty: None,
        expr: Expr { kind: ExprKind::Var(col.to_string()), span },
        span,
    }
}

/// Substitute the settled bodies for their placeholders. Only the node shapes
/// this module generates are walked — a placeholder cannot occur anywhere
/// else, since its name is unspellable.
fn fill_arm(a: Arm, bodies: &[Option<Expr>]) -> Arm {
    Arm { body: fill(a.body, bodies), ..a }
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
            let Block { stmts, result, ons, span } = *b;
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
        ExprKind::Match { scrut, eqbind, motive, arms } => Expr {
            kind: ExprKind::Match {
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
