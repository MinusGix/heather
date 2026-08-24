//! Operator-symbol resolution and rewriting.
//!
//! This owns the three-rung ladder (local symbol binder, carrier designation,
//! compatibility fallback), its carrier probes, and the rewrite into an
//! ordinary named application. Designation storage remains in the trait
//! registry.

use heather_kernel::term::Type;
use heather_syntax::{Expr, ExprKind, OpFixity, Span};

use super::Carrier;
use crate::{
    err, expression_left_leaf_is_numeral, traits, Cx, Elaborator, OperatorFallbackUse, R,
};

impl Elaborator {
    // -- operator symbols ---------------------------------------------------

    /// The fixed name an operator symbol falls back to — the third rung of
    /// [`Self::resolve_op_name`] and the whole of what `+` meant before this
    /// round (docs/operators-onto-classes-design.md §4).
    ///
    /// This table *is* the parser desugaring it replaced, moved from
    /// `Parser::infix_op`'s first column to the resolver's last stop. That is
    /// the growth invariant, and it is structural rather than audited: a file
    /// with no designation for a symbol runs exactly this.
    fn op_fallback(sym: &str, fixity: OpFixity) -> Option<&'static str> {
        if fixity != OpFixity::Infix {
            return None;
        }
        match sym {
            "+" => Some("add"),
            "*" => Some("mul"),
            "<=" => Some("Le"),
            // `Lt`, not `lt`: the row was written when nothing defined either
            // and the lowercase spelling was a guess. `std/nat` declares `Lt`
            // beside `Le`, and a relation is capitalized here for the same
            // reason `Le` is (issues/nat-order-kit.md, 2026-08-16).
            "<" => Some("Lt"),
            _ => None,
        }
    }

    /// §5.2's uniqueness rule, over the **symbol** namespace
    /// (docs/operators-onto-classes-design.md §5.1–§5.2, as
    /// issues/binder-symbol-as-notation.md amends them): a declaration installs
    /// each spelling once, by any mix of constraint symbol slots and `as`.
    ///
    /// Only the symbol half needs a new check. `as` mints no identifier — the
    /// binder keeps the name it would have had, which is the whole design — so
    /// the identifier half is the parameter-list checks that were already
    /// there, unchanged.
    pub(crate) fn check_symbol_free(installed: &[(String, String)], sym: &str, span: Span) -> R<()> {
        let Some((_, prev)) = installed.iter().find(|(s, _)| s == sym) else { return Ok(()) };
        // A constraint slot's binder is `#op∙@0_0` and unspellable, so it is
        // named by what wrote it rather than by the generated name.
        let by = match traits::op_index_symbol(prev) {
            Some(_) => format!("a constraint that named it (`<…: C({sym})>`)"),
            None => format!("`{prev} as {sym}`"),
        };
        err(
            format!(
                "`{sym}` is already this declaration's body spelling, installed by {by}: \
                 each spelling binds exactly one referent, so one declaration installs a \
                 symbol once — by a constraint's symbol slot or by `as`, not both \
                 (docs/operators-onto-classes-design.md §5.1). Pick a second symbol, or \
                 drop one of the two spellings"
            ),
            span,
        )
    }

    // The clause a diagnostic uses to say which of rung 2's two sources the
    // carrier came from (docs/bare-symbol-checking-carrier-design.md §6).
    const FROM_OPERAND: &'static str = "the carrier of its left operand";
    const FROM_EXPECTED: &'static str = "the carrier this position expects";

    /// The name an operator symbol means here — the three-rung ladder of
    /// docs/operators-onto-classes-design.md §4, as
    /// docs/bare-symbol-checking-carrier-design.md widens rung 2.
    ///
    /// `args` is the symbol's operand list, empty for a bare symbol between
    /// delimiters (`Monoid(+)`, `mconcat(++, xss)`). Rung 2 takes its carrier
    /// from the operand when there is one and from `expected` — the first
    /// domain of the type this **checking** position asks for — when there is
    /// not. Unapplied is not the same as carrier-less: in an *inference*
    /// position (`expected` is `None`) there is genuinely nothing to probe,
    /// and only rungs 1 and 3 can fire.
    fn resolve_op_name(
        &self,
        cx: &Cx,
        sym: &str,
        fixity: OpFixity,
        args: &[Expr],
        expected: Option<&Type>,
        span: Span,
    ) -> R<String> {
        // 1. A constraint binder that named the symbol. Innermost first, and
        //    before any type is looked at: inside `<A: Monoid(+)>` the `+` is
        //    the bound index and nothing else, at every carrier.
        if fixity == OpFixity::Infix
            && let Some((_, n)) = cx.op_locals.iter().rev().find(|(s, _)| s == sym)
        {
            return Ok(n.clone());
        }
        // 2. The designation at the carrier — the operand's, or the one this
        //    position expects. Probed only when the symbol has designations at
        //    all, so a file that declares none pays one failed lookup in a
        //    usually-empty map and no inference.
        //
        //    The two sources are exclusive, and this is the one place that
        //    says so: only a **bare** symbol reads the expected type. An
        //    applied one has an operand, which is the more specific evidence —
        //    the value the operation will be applied to, where the expected
        //    type is only what the surrounding position will accept — and
        //    admitting a second source there would put something new in the
        //    path of every operator expression that elaborates today
        //    (docs/bare-symbol-checking-carrier-design.md §4.2).
        let mut uncovered_carrier = None;
        if self.traits.has_designation_for(fixity, sym) {
            let flexible_left = args.first().is_some_and(expression_left_leaf_is_numeral);
            let expected_for_numeral = if flexible_left {
                expected
                    .and_then(|t| self.carrier_of_ty(cx, t, span))
                    .filter(|h| self.designated(sym, fixity, &h.key).is_some())
                    .map(|h| (h, Self::FROM_EXPECTED))
            } else {
                None
            };
            let sibling_for_numeral = if flexible_left {
                args.iter()
                    .skip(1)
                    .filter(|arg| !expression_left_leaf_is_numeral(arg))
                    .find_map(|arg| {
                        self.op_carrier_head(cx, std::slice::from_ref(arg), span)
                            .filter(|h| self.designated(sym, fixity, &h.key).is_some())
                    })
                    .map(|h| (h, "the carrier of its first non-numeral operand"))
            } else {
                None
            };
            let probed = if let Some(from_expected) = expected_for_numeral {
                Some(from_expected)
            } else if let Some(from_sibling) = sibling_for_numeral {
                Some(from_sibling)
            } else if args.is_empty() {
                expected
                    .and_then(|t| self.expected_carrier_head(cx, t, span))
                    .map(|h| (h, Self::FROM_EXPECTED))
            } else {
                self.op_carrier_head(cx, args, span).map(|h| (h, Self::FROM_OPERAND))
            };
            if let Some((head, from)) = probed {
                // The carrier the probe found is a *declaration*, and the
                // table is keyed on declarations
                // (issues/designation-key-collides-across-modules.md): a file
                // that sees two `List`s asks about the one its operand
                // actually has, and the other module's `++` is not consulted.
                if let Some(op) = self.designated(sym, fixity, &head.key) {
                    return Ok(op);
                }
                uncovered_carrier = Some((head, from));
            }
        }
        // 3. The symbol's fallback name, resolved as it always was. `&&`,
        //    `||` and `++` have no entry — they postdate the parser's fixed table, so
        //    there is no old desugaring for the growth invariant to preserve
        //    (issues/bool-operator-designations.md) — and refuse like a
        //    fallback whose name is missing, not like a symbol outside the
        //    grammar.
        let fb = Self::op_fallback(sym, fixity);
        if let Some(fb) = fb
            && (self.lookup_global(fb).is_some()
                || self.ctor_of(fb).is_some()
                || cx.names.iter().any(|n| n == fb)
                || cx.aliases.iter().any(|a| a.name == fb))
        {
            if let Some((head, from)) = &uncovered_carrier {
                let note = format!(
                    "`{sym}` has no designation at `{}` ({from}), so it used its \
                     fallback name `{fb}`",
                    head.written
                );
                let mut notes = self.attempt.op_fallback_notes.borrow_mut();
                if !notes.contains(&note) {
                    notes.push(note);
                }
                let mut uses = self.attempt.op_fallback_uses.borrow_mut();
                if !uses.iter().any(|u| u.span == span) {
                    uses.push(OperatorFallbackUse {
                        symbol: sym.into(),
                        fallback: fb.into(),
                        carrier: head.written.clone(),
                        from,
                        span,
                    });
                }
            }
            return Ok(fb.to_string());
        }
        // Reporting "unbound name `add`" would name something the writer
        // never typed. Say what *was* typed, and what would have to be
        // true for it to mean something.
        let known = self
            .traits
            .designations_for(fixity, sym)
            .into_iter()
            // The *written* carrier, not the key: this line tells a reader
            // where the symbol does mean something, and `list::List` is the
            // registry's name for it, not theirs
            // (issues/diagnostics-name-the-written-form.md).
            .map(|(carrier, op)| format!("`{carrier}` (`{op}`)"))
            .collect::<Vec<_>>();
        // The carrier rung 2 tried, where it got one from either source. Naming
        // it is the difference between "covers this carrier" — which names no
        // carrier at all — and a sentence the reader can check against the
        // table (docs/bare-symbol-checking-carrier-design.md §6).
        let designation_form = if fixity == OpFixity::Prefix {
            format!("designation prefix {sym} at …")
        } else {
            format!("designation {sym} at …")
        };
        let tried = match &uncovered_carrier {
            Some((head, from)) => {
                format!("nothing designates `{sym}` at `{}` — {from} —", head.written)
            }
            None => format!("no `{designation_form}` covers this carrier,"),
        };
        let binder_clause = if fixity == OpFixity::Infix {
            format!("no constraint binder named it (`<A: Monoid({sym})>`), ")
        } else {
            String::new()
        };
        err(
            format!(
                "`{sym}` has no meaning here: {binder_clause}{tried} and {}. {}",
                match fb {
                    Some(fb) => format!("its fallback name `{fb}` is not in scope"),
                    None => format!("`{sym}` has no fallback name"),
                },
                if known.is_empty() {
                    format!("`{sym}` designates nothing anywhere in this program")
                } else {
                    format!("`{sym}` designates something at {}", known.join(", "))
                }
            ),
            span,
        )
    }

    /// The head of the carrier an operator application is at — rung 2's probe
    /// (docs/operators-onto-classes-design.md §4.1).
    ///
    /// Two rules, both load-bearing. It **descends the left spine** through
    /// operator applications to the leftmost non-operator leaf and infers that
    /// one: `a + b + c` is `(a + b) + c`, so naively inferring `args[0]` would
    /// re-infer the whole prefix at every rung and cost 2^d on a chain of
    /// length d, where the descent costs d. And it is a **proposal, never a
    /// decision**: a leaf that does not infer, or a head with no entry, falls
    /// through to the fallback rung, so a mis-probe costs a rung and never a
    /// wrong term. The speculative inference's goals are rolled back for the
    /// same reason.
    fn op_carrier_head(&self, cx: &Cx, args: &[Expr], span: Span) -> Option<Carrier> {
        let mut leaf = args.first()?;
        loop {
            let ExprKind::App { head, args, .. } = &leaf.kind else { break };
            if !matches!(head.kind, ExprKind::OpSymbol { .. }) {
                break;
            }
            match args.first() {
                Some(a) => leaf = a,
                None => break,
            }
        }
        if self.is_checking_only(cx, leaf) {
            return None;
        }
        let mark = self.attempt.goal_arena.mark();
        let inferred = self.elab_infer(cx, leaf);
        self.attempt.goal_arena.rollback(mark);
        let (_, ty, _) = inferred.ok()?;
        self.carrier_of_ty(cx, &ty, span)
    }

    /// The head of the carrier a **checking position** is asking for — rung
    /// 2's second source (docs/bare-symbol-checking-carrier-design.md §3, §4).
    ///
    /// The expected type's **first domain**, which is where the left operand
    /// would have sat: at `A -> A -> A` with `A := List<B>` it is `List`. That
    /// is the same fact `op_carrier_head` gets by inferring an operand,
    /// arriving from the other side — and it costs no inference at all, since
    /// there is no operand to infer.
    ///
    /// A proposal like its applied twin, and declining is cheap: an expected
    /// type that is no `Π`, or a domain with no nominal head — a variable, a
    /// meta, `Type` — answers `None` through `type_namespace`, so a domain
    /// that still mentions an implicit needs no separate meta test, and the
    /// ladder simply goes on to the fallback rung.
    fn expected_carrier_head(&self, cx: &Cx, expected: &Type, span: Span) -> Option<Carrier> {
        let Type::Pi { dom, .. } = self.whnf(cx, expected, span).ok()? else { return None };
        self.carrier_of_ty(cx, &dom, span)
    }

    /// An operator symbol, bare or applied, rewritten to the ordinary
    /// application it means. `None` for every expression that is not one,
    /// which is every expression written before this round.
    ///
    /// A *rewrite* and not an elaboration arm on purpose: everything
    /// downstream — checking position, implicit insertion, spilling, the
    /// call diagnostics — is the path a written name already takes, and a
    /// symbol earns none of it separately. That is also what makes rung 2's
    /// checking-position source free of a second lesson: the name it produces
    /// is *checked* against `expected`, so a generic `append` gets its element
    /// type from the same domain the carrier came from
    /// (docs/operators-onto-classes-design.md §12.2).
    ///
    /// `expected` is the checking position's type where there is one, and
    /// `None` at the two inference sites.
    pub(crate) fn op_rewrite(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<Option<Expr>> {
        let (sym, args, explicit, goal_oriented) = match &e.kind {
            ExprKind::OpSymbol { symbol, fixity } => ((symbol, fixity), None, false, false),
            ExprKind::App { head, args, named, explicit, goal_oriented } => match &head.kind {
                // An operator application carries the named arguments it was
                // written with — `a.op(x := 1)` reaches here after `.`
                // resolution — so the rewrite preserves them rather than
                // rewriting them away.
                ExprKind::OpSymbol { symbol, fixity } => {
                    ((symbol, fixity), Some((args, named)), *explicit, *goal_oriented)
                }
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        let name = self.resolve_op_name(
            cx,
            sym.0,
            *sym.1,
            args.map_or(&[][..], |(a, _)| a),
            expected,
            e.span,
        )?;
        let head = Expr { kind: ExprKind::Var(name), span: e.span };
        Ok(Some(match args {
            None => head,
            Some((args, named)) => Expr {
                kind: ExprKind::App {
                    head: Box::new(head),
                    args: args.clone(),
                    named: named.clone(),
                    explicit,
                    goal_oriented,
                },
                span: e.span,
            },
        }))
    }

    /// A **bare** operator symbol whose meaning only a carrier can settle —
    /// the gate on [`Self::is_checking_only`]'s new arm
    /// (docs/bare-symbol-checking-carrier-design.md §4.3).
    ///
    /// Two conjuncts, both load-bearing.
    ///
    /// Rung 1 first, so a symbol this declaration's own binder named is never
    /// deferred: `sum_all`'s `mconcat(+, xs)` resolves without looking at a
    /// type and elaborates through exactly the code it did before.
    ///
    /// And the symbol must be designated *somewhere*, which is the growth
    /// invariant's guard and the very guard rung 2 already carries. Without it
    /// a file that declares no designation for a symbol would stop inferring
    /// it by the fallback — and the fallback's own type is sometimes what
    /// teaches the call its carrier — so a program written before this round
    /// could start refusing. With it, such a file runs byte-identical code.
    pub(crate) fn symbol_needs_a_carrier(&self, cx: &Cx, sym: &str, fixity: OpFixity) -> bool {
        (fixity != OpFixity::Infix || !cx.op_locals.iter().any(|(s, _)| s == sym))
            && self.traits.has_designation_for(fixity, sym)
    }

}
