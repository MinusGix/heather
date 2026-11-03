//! Character and string literals (docs/string-char-design.md §3).
//!
//! Both follow the numeral's ladder exactly: a literal at its *own* spec type
//! elaborates to that type's introduction form, and at any other expected
//! carrier it resolves a one-field class and applies its embedding, the way
//! `elab_overloaded_num_check` resolves `Numeral`. Like `Numeral`, the classes
//! are visible exactly when their type is: a literal at a carrier with no
//! instance is a resolution failure, and a literal in a program that has not
//! imported `std/char` is told to import it.
//!
//! Neither literal builds a kernel term of its own. A character is the
//! *surface* `char::ofNat(code, bool::decide_yes(refl))` and a string is the
//! *surface* `string::String([…])`, re-elaborated through the ordinary paths:
//! the proof route is then the one `decide` already owns, and the list body is
//! the collection-literal lowering `List` already owns, so there is no second
//! way to build either.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, Term, Type};
use heather_syntax::{Expr, ExprKind, ScaledLit, Span};

use crate::oracle::Unfold;
use crate::{application, Cx, ElabError, Elaborator, R};

/// The surface name of the `Char` record, its introduction form, and the
/// reflection lemma a literal's scalar proof goes through. Written as keys
/// (`module::name`), the way `elab_decide` names `bool::decide_yes`: a key is
/// a writable name, and naming the declaration rather than the bare word is
/// what keeps a local binder from capturing a generated call.
const CHAR_TYPE: &str = "char::Char";
const CHAR_INTRO: &str = "char::ofNat";
const STRING_TYPE: &str = "string::String";
const DECIDE_YES: &str = "bool::decide_yes";
const DECIMAL_TYPE: &str = "rat::Decimal";
const DECIMAL_INTRO: &str = "rat::Decimal::lit";
const DECIMAL_RAT: &str = "rat::Decimal::rat";
const HEX_TYPE: &str = "rat::HexFloat";
const HEX_INTRO: &str = "rat::HexFloat::lit";
const HEX_RAT: &str = "rat::HexFloat::rat";
// The literal classes, read by identity (`Elaborator::syntax_class`): a
// literal at a carrier needs the class's module in its closure, not its name
// in scope.
pub(crate) const NUMERAL: &str = "algebra::Numeral";
const CHAR_LITERAL: &str = "char::CharLiteral";
const STRING_LITERAL: &str = "string::StringLiteral";
const HEX_LITERAL: &str = "rat::HexLiteral";
const DECIMAL_LITERAL: &str = "rat::DecimalLiteral";

/// `Numeral` of `algebra::Numeral`: the spelling a diagnostic shows.
fn key_name(key: &str) -> &str {
    key.rsplit("::").next().unwrap_or(key)
}

/// The spec type, its introduction form and its reading at `Rat`, for a
/// decimal or a hex float literal.
fn scaled_names(lit: &ScaledLit) -> (&'static str, &'static str, &'static str) {
    if lit.hex { (HEX_TYPE, HEX_INTRO, HEX_RAT) } else { (DECIMAL_TYPE, DECIMAL_INTRO, DECIMAL_RAT) }
}

/// The module half of a resolved key: `char` for `char::ofNat`.
fn key_module(key: &str) -> &str {
    key.split_once("::").map_or(key, |(module, _)| module)
}

fn var(name: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Var(name.to_string()),
        span,
    }
}

fn call(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args,
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

impl Elaborator {
    /// Is the expected type the declaration `name` names here? `None` for a
    /// name with no reading in this scope, which is what makes the direct
    /// route optional: without `std/char` imported there is no `Char` to
    /// build, and the literal falls through to the class rung.
    fn expected_is(&self, cx: &Cx, expected: &Type, name: &str, span: Span) -> bool {
        let Some(key) = self.closure_key(name) else {
            return false;
        };
        self.carrier_of_ty(cx, expected, span)
            .is_some_and(|carrier| carrier.key == key)
    }

    /// The key of a literal's spec name (`char::Char`, `char::ofNat`), read
    /// in this module's scope or, failing that, in the declaring module's own
    /// when that module is in the closure: a character literal at a byte
    /// (`CharLiteral<BitVec(8)>`, from `byte`) builds its `Char` first, and
    /// `char` is then in the closure without being named here
    /// (issues/literal-classes-need-importing.md).
    fn closure_key(&self, name: &str) -> Option<String> {
        self.key_of(name).or_else(|| {
            let module = key_module(name);
            self.names.has_module(module).then(|| self.read_in_module(module, |s| s.key_of(name)))?
        })
    }

    /// Run `read` with names resolved as `module` reads them: the module
    /// declaring a literal's spec type. A literal's generated call is that
    /// module's term, not the client's: `char::ofNat`'s witness names
    /// `bool::decide_yes` and a string's characters are `char` literals, so
    /// resolving them in the client's scope demanded imports the client never
    /// wrote, and the refusal then named the type's own module
    /// (issues/literal-needs-module-names-wrong-module.md). The client's
    /// scope already decided that the type is in reach; the call it expands
    /// to sees what the type's module sees, as a parameter default does.
    fn read_in_module<T>(&self, module: &str, read: impl FnOnce(&Self) -> T) -> T {
        let Some(scope) = self.names.module_scope(module) else {
            return read(self);
        };
        let scope = Rc::new(scope.clone());
        let _scope = self.use_scope(&scope);
        read(self)
    }

    /// `char::ofNat(code, bool::decide_yes(refl))`, and the module it reads
    /// in (see [`Self::read_in_module`]). The proof is exactly the
    /// term the `decide` goal combinator writes; the kernel judges the `refl`
    /// by running the `Decide<char::scalar(n)>` instance at the code, and it
    /// can only go the `Inl` way because the lexer already refused every
    /// non-scalar payload.
    fn char_intro(&self, c: char, span: Span) -> Option<(Expr, String)> {
        let intro = self.closure_key(CHAR_INTRO)?;
        let module = key_module(&intro).to_string();
        let yes = self.read_in_module(&module, |s| s.key_of(DECIDE_YES))?;
        let code = Expr {
            kind: ExprKind::Num(u64::from(u32::from(c)).into()),
            span,
        };
        let proof = call(var(&yes, span), vec![Expr { kind: ExprKind::Refl, span }], span);
        Some((call(var(&intro, span), vec![code, proof], span), module))
    }

    /// `string::String([…])` — the record over the *collection literal* of the
    /// characters. Reusing `[…]` is the point: the `List<Char>` body is built
    /// by the protocol `list` already registers, so a string literal adds no
    /// list-building route of its own. Read in `string`'s scope, which is
    /// what lets the characters build without `char` imported here.
    fn string_intro(&self, text: &str, span: Span) -> Option<(Expr, String)> {
        let ctor = self.key_of(STRING_TYPE)?;
        let module = key_module(&ctor).to_string();
        let chars = text
            .chars()
            .map(|c| Expr {
                kind: ExprKind::Char(c),
                span,
            })
            .collect();
        let body = Expr {
            kind: ExprKind::CollectionLit(chars),
            span,
        };
        Some((call(var(&ctor, span), vec![body], span), module))
    }

    /// The class rung, shared by both literals and shaped on
    /// `elab_overloaded_num_check`'s `Numeral` arm: resolve the one-parameter
    /// class at the expected carrier and apply its single field to the
    /// literal, which the field's domain then checks at the literal's own spec
    /// type. `None` when the class is not visible here.
    fn literal_class(
        &self,
        cx: &Cx,
        class_key: &str,
        field_name: &str,
        literal: &Expr,
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> Option<R<Term>> {
        let (ind, named) = self.literal_class_record(class_key)?;
        let class_name = key_name(class_key);
        let field = ind.field_index(field_name)?;
        (|| {
            let targs = [(expected.clone(), expected_level.clone())];
            let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &[], span)?;
            let carrier = self
                .type_namespace(cx, expected, span)
                .unwrap_or_else(|| "the expected type".to_string());
            let display = format!("{class_name}<{carrier}>");
            let mut trace = Vec::new();
            let Some(dict) =
                self.resolve_goal(cx, &goal, &goal_level, &display, None, span, &mut trace)
            else {
                if !named {
                    return Ok(None);
                }
                return Err(ElabError::Resolution {
                    goal: display,
                    span,
                    trace,
                });
            };
            let (embed, embed_ty, embed_level) =
                self.project_field(cx, &ind, &goal, Rc::new(dict), field, span)?;
            let since = self.attempt.trivial_uses.borrow().len();
            let (out, _, _) = application::apply_explicit(
                self,
                cx,
                Some(field_name),
                Rc::new(Vec::new()),
                0,
                embed,
                embed_ty,
                embed_level,
                std::slice::from_ref(literal),
            )?;
            self.settle_deferred_units(since)?;
            Ok(Some(self.reduced_embedding(cx, out)))
        })()
        .transpose()
    }

    /// A literal's embedding at a carrier whose instance is known, read as
    /// the carrier's own construction rather than a dictionary projection:
    /// `ofNat(8, 10)` for `'\n'` or `10` at a byte, so the frontend, `split_all`
    /// and instance search all see the spelling the carrier's library uses
    /// (docs/native-programs-read-like-programs-design.md §3, S3). The
    /// projection unfolds only as far as the field's body: the first reduct
    /// headed by another definition (`BitVec::ofNat`), with each argument
    /// that computes to a natural literal computed (`c.toNat()` of a closed
    /// character), or the value the field returns when it is a constructor.
    /// A dictionary that is a local (`<A: Numeral>`) does not unfold, and the
    /// term stays as it was.
    /// Decide, here, every `trivial` recorded since `since` that left its
    /// verdict to the gate ([`crate::expr::UnitCheckingElab`]). A literal's
    /// embedding is reduced before it is emitted ([`Self::reduced_embedding`]),
    /// and a reduct can drop an argument its field ignores — `HexLiteral`'s
    /// `ofHex` takes the `trivial` that the carrier holds the value and never
    /// reads it — so the gate would never see the `⟨⟩` it was left to judge
    /// (`issues/closed-verdict-evaluated-twice.md`).
    pub(crate) fn settle_deferred_units(&self, since: usize) -> R<()> {
        let uses = self.attempt.trivial_uses.borrow();
        let Some(pending) = uses.get(since..).filter(|p| !p.is_empty()) else {
            return Ok(());
        };
        let oracle = self.semantic_oracle();
        for u in pending {
            match oracle.whnf_type(&u.cx.gamma, &u.expected) {
                Ok(Type::Unit { .. }) => {}
                Ok(_) => {
                    return Err(ElabError::Elab {
                        msg: format!(
                            "`trivial` proves `True`, but `{}` is expected here",
                            self.display_type(&u.cx, &u.expected)
                        ),
                        span: u.span,
                    });
                }
                Err(_) => {
                    return Err(ElabError::Elab {
                        msg: "out of fuel reducing a type".into(),
                        span: u.span,
                    });
                }
            }
        }
        Ok(())
    }

    pub(crate) fn reduced_embedding(&self, cx: &Cx, out: Term) -> Term {
        let oracle = self.goal_oracle();
        let mut last = None;
        for reduct in oracle.unfold(&cx.gamma, &out, Unfold::LiteralEmbedding) {
            let (head, _) = crate::spelling::app_spine(&reduct);
            if matches!(head, Term::GlobalTm { .. }) {
                return self.literal_arguments(cx, &reduct);
            }
            last = Some(reduct);
        }
        match last {
            Some(value) if crate::spelling::app_of(&value).is_none() => value,
            _ => out,
        }
    }

    fn literal_arguments(&self, cx: &Cx, term: &Term) -> Term {
        let natural = |t: &Term| {
            let mut t = t;
            while let Term::Succ(inner) = t {
                t = inner;
            }
            matches!(t, Term::Zero | Term::NatLit(_))
        };
        let mut output = term.clone();
        if let Term::App { fun, arg, .. } | Term::AppAt { fun, arg } = &mut output {
            *fun = Rc::new(self.literal_arguments(cx, fun));
            if !natural(arg)
                && let Ok(computed) = self.goal_oracle().bounded(256).whnf_term(&cx.gamma, arg)
                && natural(&computed)
            {
                *arg = Rc::new(computed);
            }
        }
        output
    }

    /// A character literal in checking position.
    pub(crate) fn elab_char_check(
        &self,
        cx: &Cx,
        c: char,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
    ) -> R<Term> {
        if self.expected_is(cx, expected, CHAR_TYPE, e.span) {
            let at = (
                match cx.gamma.base {
                    CtxBase::Nil => None,
                    CtxBase::Var(v) => Some(v.0),
                },
                cx.gamma.entries.len(),
                self.lowering_scope(),
            );
            if let Some((.., term)) = self.attempt.char_literals.borrow().iter().find(|(k, a, ty, _)| *k == c && *a == at && ty == expected) {
                return Ok(term.clone());
            }
            let (intro, module) = self
                .char_intro(c, e.span)
                .ok_or_else(|| self.literal_needs_module(CHAR_TYPE, e.span))?;
            let term = self.read_in_module(&module, |s| s.elab_check(cx, &intro, expected, lvl))?;
            self.attempt.char_literals.borrow_mut().push((c, at, expected.clone(), term.clone()));
            return Ok(term);
        }
        if let Some(result) =
            self.literal_class(cx, CHAR_LITERAL, "ofChar", e, expected, lvl, e.span)
        {
            return result;
        }
        let (term, ty, _) = self.elab_char_infer(cx, c, e)?;
        self.note_check_mismatch(cx, &ty, expected, &Level::Zero, e.span);
        Ok(term)
    }

    /// A character literal in inference position: `Char`, the only type it
    /// names by itself.
    pub(crate) fn elab_char_infer(&self, cx: &Cx, c: char, e: &Expr) -> R<(Term, Type, Level)> {
        let (intro, module) = self
            .char_intro(c, e.span)
            .ok_or_else(|| self.literal_needs_module(CHAR_TYPE, e.span))?;
        self.read_in_module(&module, |s| s.elab_infer(cx, &intro))
    }

    /// A string literal in checking position.
    pub(crate) fn elab_string_check(
        &self,
        cx: &Cx,
        text: &str,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
    ) -> R<Term> {
        if self.expected_is(cx, expected, STRING_TYPE, e.span) {
            let (intro, module) = self
                .string_intro(text, e.span)
                .ok_or_else(|| self.literal_needs_module(STRING_TYPE, e.span))?;
            return self.read_in_module(&module, |s| s.elab_check(cx, &intro, expected, lvl));
        }
        if let Some(result) =
            self.literal_class(cx, STRING_LITERAL, "ofString", e, expected, lvl, e.span)
        {
            return result;
        }
        let (term, ty, _) = self.elab_string_infer(cx, text, e)?;
        self.note_check_mismatch(cx, &ty, expected, &Level::Zero, e.span);
        Ok(term)
    }

    /// A string literal in inference position: `String`.
    pub(crate) fn elab_string_infer(
        &self,
        cx: &Cx,
        text: &str,
        e: &Expr,
    ) -> R<(Term, Type, Level)> {
        let (intro, module) = self
            .string_intro(text, e.span)
            .ok_or_else(|| self.literal_needs_module(STRING_TYPE, e.span))?;
        self.read_in_module(&module, |s| s.elab_infer(cx, &intro))
    }

    /// `rat::Decimal::lit(mant, up, down)` (or `HexFloat`'s), the exponent
    /// split into its two signs so the parts are numerals.
    fn scaled_intro(&self, lit: &ScaledLit, span: Span) -> Option<Expr> {
        let intro = self.key_of(scaled_names(lit).1)?;
        let num = |n: heather_syntax::Numeral| Expr { kind: ExprKind::Num(n), span };
        let up = u64::try_from(lit.exp.max(0)).unwrap_or(0);
        let down = lit.exp.min(0).unsigned_abs();
        Some(call(var(&intro, span), vec![num(lit.mant.clone()), num(up.into()), num(down.into())], span))
    }

    /// A decimal or hex float literal in checking position. At its spec type
    /// it is the record of its parts; at another carrier it resolves
    /// `DecimalLiteral` (whose `exact` field, run here, draws the
    /// inexact-literal warning when it says `False`) or `HexLiteral` (whose
    /// `ofHex` takes the proof `trivial` that the carrier holds the value, so
    /// an unrepresentable hex float is refused); with neither, it is a `Rat`.
    pub(crate) fn elab_scaled_check(
        &self,
        cx: &Cx,
        lit: &ScaledLit,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
    ) -> R<Term> {
        let (type_key, _, _) = scaled_names(lit);
        // Every rung goes through the spec type: the class's field takes a
        // `Decimal`, and the reading at `Rat` is `Decimal::rat`.
        if self.key_of(type_key).is_none() {
            return Err(self.literal_needs_module(type_key, e.span));
        }
        if self.expected_is(cx, expected, type_key, e.span) {
            let intro = self
                .scaled_intro(lit, e.span)
                .ok_or_else(|| self.literal_needs_module(type_key, e.span))?;
            return self.elab_check(cx, &intro, expected, lvl);
        }
        let rung = if lit.hex {
            let proof = var("trivial", e.span);
            self.literal_class_fields(cx, HEX_LITERAL, "ofHex", None, &[e.clone(), proof], expected, lvl, e.span)
        } else {
            self.literal_class_fields(cx, DECIMAL_LITERAL, "ofDecimal", Some("exact"), std::slice::from_ref(e), expected, lvl, e.span)
        };
        if let Some(result) = rung {
            // The only way `trivial` fails at `HexLiteral`'s `Ok` is a value
            // the carrier does not hold; say that, not the obligation.
            let result = match result {
                Err(err) if lit.hex && !matches!(err, ElabError::Resolution { .. }) => Err(ElabError::Elab {
                    msg: format!(
                        "this hex float is not exactly a value of `{}`, and a hex float must be exact: write it with fewer digits, or as a decimal to round it",
                        self.display_type(cx, expected)
                    ),
                    span: e.span,
                }),
                other => other,
            };
            let (term, exact) = result?;
            if let Some(exact) = exact
                && self.literal_bit_false(cx, &exact, e.span)
            {
                let carrier = self.display_type(cx, expected);
                self.emit_lint(
                    crate::Lint::InexactLiteral,
                    format!("this literal is not exactly a value of `{carrier}`: it stands for the nearest one"),
                    e.span,
                );
            }
            return Ok(term);
        }
        let (term, ty, _) = self.elab_scaled_infer(cx, lit, e)?;
        self.note_check_mismatch(cx, &ty, expected, &Level::Zero, e.span);
        Ok(term)
    }

    /// Does a literal's `exact` bit compute to `False`? Asked of the kernel's
    /// conversion, the judgement a `refl` would get at the gate: the bit is
    /// a closed run of the carrier's rounding, which the evaluator answers
    /// where the elaborator's own weak-head reduction would spell every step.
    fn literal_bit_false(&self, cx: &Cx, bit: &Term, span: Span) -> bool {
        let Some(key) = self.key_of("rat::Decimal::inexact") else {
            return false;
        };
        let Ok((no, ty, level)) = self.elab_infer(cx, &call(var(&key, span), Vec::new(), span)) else {
            return false;
        };
        self.goal_oracle()
            .convert_term(&cx.gamma, heather_kernel::layer::Layer::Prog, bit, &no, &ty, &level)
            .is_ok()
    }

    /// A decimal or hex float literal in inference position: the `Rat` it
    /// denotes.
    pub(crate) fn elab_scaled_infer(&self, cx: &Cx, lit: &ScaledLit, e: &Expr) -> R<(Term, Type, Level)> {
        let (type_key, _, rat_key) = scaled_names(lit);
        let intro = self
            .scaled_intro(lit, e.span)
            .ok_or_else(|| self.literal_needs_module(type_key, e.span))?;
        let reading = self.key_of(rat_key).ok_or_else(|| self.literal_needs_module(type_key, e.span))?;
        self.elab_infer(cx, &call(var(&reading, e.span), vec![intro], e.span))
    }

    /// [`Self::literal_class`] for a class whose embedding takes `args`
    /// (the literal and anything after it), also applying the field `check`,
    /// when named, to the literal alone. `None` when the class is not
    /// visible here.
    #[allow(clippy::too_many_arguments)]
    fn literal_class_fields(
        &self,
        cx: &Cx,
        class_key: &str,
        field_name: &str,
        check: Option<&str>,
        args: &[Expr],
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> Option<R<(Term, Option<Term>)>> {
        let (ind, named) = self.literal_class_record(class_key)?;
        let class_name = key_name(class_key);
        let field = ind.field_index(field_name)?;
        let check = match check {
            Some(name) => Some((name, ind.field_index(name)?)),
            None => None,
        };
        (|| {
            let targs = [(expected.clone(), expected_level.clone())];
            let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &[], span)?;
            let carrier = self
                .type_namespace(cx, expected, span)
                .unwrap_or_else(|| "the expected type".to_string());
            let display = format!("{class_name}<{carrier}>");
            let mut trace = Vec::new();
            let Some(dict) =
                self.resolve_goal(cx, &goal, &goal_level, &display, None, span, &mut trace)
            else {
                if !named {
                    return Ok(None);
                }
                return Err(ElabError::Resolution {
                    goal: display,
                    span,
                    trace,
                });
            };
            let dict = Rc::new(dict);
            let since = self.attempt.trivial_uses.borrow().len();
            let apply = |name: &str, index, args: &[Expr]| -> R<Term> {
                let (embed, embed_ty, embed_level) = self.project_field(cx, &ind, &goal, Rc::clone(&dict), index, span)?;
                let (out, _, _) = application::apply_explicit(
                    self,
                    cx,
                    Some(name),
                    Rc::new(Vec::new()),
                    0,
                    embed,
                    embed_ty,
                    embed_level,
                    args,
                )?;
                Ok(out)
            };
            let out = apply(field_name, field, args)?;
            self.settle_deferred_units(since)?;
            let checked = match check {
                Some((name, index)) => Some(apply(name, index, &args[..1])?),
                None => None,
            };
            Ok(Some((self.reduced_embedding(cx, out), checked)))
        })()
        .transpose()
    }

    fn literal_needs_module(&self, type_key: &str, span: Span) -> ElabError {
        let module = type_key.split("::").next().unwrap_or(type_key);
        ElabError::Elab {
            msg: format!(
                "a literal at `{type_key}` needs the type in scope: add `import {module};`"
            ),
            span,
        }
    }
}

/// One constructor value of a collection literal's spine, opened: the node
/// with its label's element projections contracted, its children still to
/// build, and the ones built so far.
struct SpineFrame {
    node: Term,
    pending: Vec<Rc<Term>>,
    built: Vec<Rc<Term>>,
}

impl Elaborator {
    /// A collection literal's value with its **constructor spine built out**:
    /// `Cons(1, Cons(2, Nil))`, not the weak head the protocol's conversion
    /// leaves, `Cons(fst(v), fold(snd(v)))` over the literal's vector `v`.
    ///
    /// The weak head is a correct term and the kernel builds the rest when
    /// it needs it, but every reader that *shows* a term met the vector and
    /// the unreduced fold: a refusal at a goal holding `[1, 2]` or `"hi"`
    /// printed the kernel encoding
    /// (issues/decide-refusal-spells-string-literal-encoding.md), and the
    /// display path may not reduce to recover it. So the literal reduces here,
    /// once, where reducing is the elaborator's business. Nothing names the
    /// container: any `Wf` constructor value is opened, each child is
    /// reduced to its weak head, and a projection out of the literal's own
    /// vector is read off the vector — which is how an element comes back as
    /// the term it elaborated to rather than its unfolding. A child that does
    /// not reduce to a constructor stays as it was, and `budget` (a few nodes
    /// per element) bounds the walk for a container whose literal is not a
    /// spine, so the result is always the same value, at worst less built.
    ///
    /// Iterative, since a spine is as deep as the literal is long.
    pub(crate) fn collection_literal_spine(&self, cx: &Cx, value: Term, len: usize) -> Term {
        let mut budget = 4 * (len + 1);
        let mut stack: Vec<SpineFrame> = Vec::new();
        let mut next = Rc::new(value);
        loop {
            let mut done = match spine_frame(&next) {
                Some(frame) if budget > 0 => {
                    budget -= 1;
                    stack.push(frame);
                    None
                }
                _ => Some(next),
            };
            loop {
                let Some(top) = stack.last_mut() else {
                    let done = done.expect("a value or an open frame");
                    return Rc::unwrap_or_clone(done);
                };
                if let Some(value) = done.take() {
                    top.built.push(value);
                }
                if let Some(child) = top.pending.pop() {
                    next = self.spine_child(cx, child, budget);
                    break;
                }
                let frame = stack.pop().expect("the frame just read");
                done = Some(Rc::new(rebuilt(frame)));
            }
        }
    }

    /// A child of a literal's constructor value, reduced to its weak head
    /// when that is another constructor value; otherwise as it was.
    fn spine_child(&self, cx: &Cx, child: Rc<Term>, budget: usize) -> Rc<Term> {
        if budget == 0 {
            return child;
        }
        // The fold's step hands the child the vector's tail as `snd(v)`:
        // read it off `v` first, so each step's projections stay one deep.
        let mut applied = (*child).clone();
        if let Term::App { arg, .. } | Term::AppAt { arg, .. } = &mut applied
            && let Some(tail) = projected(arg)
        {
            *arg = tail;
        }
        match self.expr_elab().whnf_term(cx, &applied) {
            Ok(reduct) if matches!(reduct, Term::Supf { .. }) => Rc::new(reduct),
            _ => child,
        }
    }
}

/// Open a `Wf` constructor value: its label with element projections read
/// off the literal's vector, and the entries of its children tuple.
fn spine_frame(t: &Term) -> Option<SpineFrame> {
    let Term::Supf { level, shape, arity, label, children } = t else {
        return None;
    };
    let mut pending = Vec::new();
    let mut cur = children;
    while let Some((fst, snd)) = crate::spelling::pair_of(cur) {
        pending.push(Rc::clone(fst));
        cur = snd;
    }
    let count = pending.len();
    // Popped from the back: the first child is built first.
    pending.reverse();
    Some(SpineFrame {
        node: Term::Supf {
            level: level.clone(),
            shape: Rc::clone(shape),
            arity: Rc::clone(arity),
            label: contracted(label),
            children: Rc::clone(children),
        },
        pending,
        built: Vec::with_capacity(count),
    })
}

/// The frame's node with its children replaced by the built ones, in order.
fn rebuilt(frame: SpineFrame) -> Term {
    let SpineFrame { mut node, built, .. } = frame;
    if let Term::Supf { children, .. } = &mut node {
        *children = with_items(children, &built);
    }
    node
}

/// `tuple` with its first `items.len()` entries replaced.
fn with_items(tuple: &Rc<Term>, items: &[Rc<Term>]) -> Rc<Term> {
    let Some((item, rest)) = items.split_first() else {
        return Rc::clone(tuple);
    };
    let mut out = (**tuple).clone();
    if let Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } = &mut out {
        *snd = with_items(snd, rest);
        *fst = Rc::clone(item);
    }
    Rc::new(out)
}

/// A label with every projection out of a literal pair read off the pair,
/// through the injections and pairs a constructor label is built of.
fn contracted(t: &Rc<Term>) -> Rc<Term> {
    if let Some(field) = projected(t) {
        return field;
    }
    let mut out = (**t).clone();
    match &mut out {
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
            let (f, s) = (contracted(fst), contracted(snd));
            if Rc::ptr_eq(&f, fst) && Rc::ptr_eq(&s, snd) {
                return Rc::clone(t);
            }
            (*fst, *snd) = (f, s);
        }
        Term::Inl { val, .. } | Term::Inr { val, .. } | Term::InlAt { val, .. } | Term::InrAt { val, .. } => {
            let v = contracted(val);
            if Rc::ptr_eq(&v, val) {
                return Rc::clone(t);
            }
            *val = v;
        }
        _ => return Rc::clone(t),
    }
    Rc::new(out)
}

/// `fst`/`snd` of a pair — or of a projection that itself reads off one —
/// as the component it selects; `None` when the chain bottoms out at
/// anything but a pair.
fn projected(t: &Term) -> Option<Rc<Term>> {
    let (first, inner) = crate::spelling::proj_of(t)?;
    let inner = projected(inner).unwrap_or_else(|| Rc::clone(inner));
    let (fst, snd) = crate::spelling::pair_of(&inner)?;
    Some(Rc::clone(if first { fst } else { snd }))
}
