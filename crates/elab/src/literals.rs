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
//! *surface* `char::ofNat(code, logic::decide_yes(refl))` and a string is the
//! *surface* `string::String([…])`, re-elaborated through the ordinary paths:
//! the proof route is then the one `decide` already owns, and the list body is
//! the collection-literal lowering `List` already owns, so there is no second
//! way to build either.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, Span};

use crate::{application, Cx, ElabError, Elaborator, R};

/// The surface name of the `Char` record, its introduction form, and the
/// reflection lemma a literal's scalar proof goes through. Written as keys
/// (`module::name`), the way `elab_decide` names `logic::decide_yes`: a key is
/// a writable name, and naming the declaration rather than the bare word is
/// what keeps a local binder from capturing a generated call.
const CHAR_TYPE: &str = "char::Char";
const CHAR_INTRO: &str = "char::ofNat";
const STRING_TYPE: &str = "string::String";
const DECIDE_YES: &str = "logic::decide_yes";

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
        let Some(key) = self.key_of(name) else {
            return false;
        };
        self.carrier_of_ty(cx, expected, span)
            .is_some_and(|carrier| carrier.key == key)
    }

    /// `char::ofNat(code, logic::decide_yes(refl))`. The proof is exactly the
    /// term the `decide` goal combinator writes; the kernel judges the `refl`
    /// by running `char::scalar_dec` at the code, and it can only go the `Inl`
    /// way because the lexer already refused every non-scalar payload.
    fn char_intro(&self, c: char, span: Span) -> Option<Expr> {
        let intro = self.key_of(CHAR_INTRO)?;
        let yes = self.key_of(DECIDE_YES)?;
        let code = Expr {
            kind: ExprKind::Num(u64::from(u32::from(c))),
            span,
        };
        let proof = call(var(&yes, span), vec![Expr { kind: ExprKind::Refl, span }], span);
        Some(call(var(&intro, span), vec![code, proof], span))
    }

    /// `string::String([…])` — the record over the *collection literal* of the
    /// characters. Reusing `[…]` is the point: the `List<Char>` body is built
    /// by the protocol `list` already registers, so a string literal adds no
    /// list-building route of its own.
    fn string_intro(&self, text: &str, span: Span) -> Option<Expr> {
        let ctor = self.key_of(STRING_TYPE)?;
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
        Some(call(var(&ctor, span), vec![body], span))
    }

    /// The class rung, shared by both literals and shaped on
    /// `elab_overloaded_num_check`'s `Numeral` arm: resolve the one-parameter
    /// class at the expected carrier and apply its single field to the
    /// literal, which the field's domain then checks at the literal's own spec
    /// type. `None` when the class is not visible here.
    fn literal_class(
        &self,
        cx: &Cx,
        class_name: &str,
        field_name: &str,
        literal: &Expr,
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> Option<R<Term>> {
        let class = self.lookup_class(class_name)?;
        if class.params.len() != 1 || !class.valparams.is_empty() {
            return None;
        }
        let ind = self.lookup_inductive(&class.name).cloned()?;
        let field = ind.field_index(field_name)?;
        Some((|| {
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
                return Err(ElabError::Resolution {
                    goal: display,
                    span,
                    trace,
                });
            };
            let (embed, embed_ty, embed_level) =
                self.project_field(cx, &ind, &goal, Rc::new(dict), field, span)?;
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
            Ok(out)
        })())
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
            let intro = self
                .char_intro(c, e.span)
                .ok_or_else(|| self.literal_needs_module(CHAR_TYPE, e.span))?;
            return self.elab_check(cx, &intro, expected, lvl);
        }
        if let Some(result) =
            self.literal_class(cx, "CharLiteral", "ofChar", e, expected, lvl, e.span)
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
        let intro = self
            .char_intro(c, e.span)
            .ok_or_else(|| self.literal_needs_module(CHAR_TYPE, e.span))?;
        self.elab_infer(cx, &intro)
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
            let intro = self
                .string_intro(text, e.span)
                .ok_or_else(|| self.literal_needs_module(STRING_TYPE, e.span))?;
            return self.elab_check(cx, &intro, expected, lvl);
        }
        if let Some(result) =
            self.literal_class(cx, "StringLiteral", "ofString", e, expected, lvl, e.span)
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
        let intro = self
            .string_intro(text, e.span)
            .ok_or_else(|| self.literal_needs_module(STRING_TYPE, e.span))?;
        self.elab_infer(cx, &intro)
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
