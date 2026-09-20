//! Printing a kernel type back as **surface** syntax. Diagnostics use the
//! bounded presentation path; generated annotations additionally require
//! complete source spelling and a caller-owned type comparison.
//!
//! `docs/surface-type-display-design.md`. [[goal-display-decodes]] gave the
//! display sites a *reader* — δ-step an `El` until a non-`El` head appears —
//! which covers every type whose wrapper is removable. This module is the
//! other direction: a `fn … -> Type` relation at open arguments is stuck as
//! `El(app(app(Le; n); m))` irreducibly, and an equation between two calls was
//! never `El`-headed at all, so both print as raw kernel encoding with every
//! `App` node's domain and codomain annotations in the middle of the message.
//! Spelling the term as the surface that would elaborate to it is what those
//! two shapes want (`issues/le-diagnostics-print-raw-el.md`).
//!
//! Three invariants, each against a way this could go wrong:
//!
//! - **The diagnostic path never reduces.** No δ, no β, no whnf, no fuel. The one registry
//!   consultation is [`Elaborator::unspell_here`], which is a lookup rather
//!   than a reduction. So this code cannot affect what is checked — a stronger
//!   guarantee than the reader's, which at least spends steps.
//! - **Every node either spells or falls back to that node's `{:?}`.** There
//!   is no whole-type cliff: an unspellable argument prints raw inside a call
//!   that prints as a call. A raw node is truncated ([`RAW_NODE_CHARS`]) so
//!   one bad subterm cannot reintroduce the several-hundred-column message.
//! - **Too many fallbacks abandons the attempt.** Above [`SPELL_FALLBACKS`]
//!   the top-level call declines and the caller prints the plain bounded
//!   `Debug`. A half-spelled monster is worse than the honest raw form,
//!   because it *looks* like surface syntax while being neither.

use std::cell::{Cell, RefCell};
use std::sync::Arc as Rc;

use heather_kernel::term::{CtxBase, GlobalVar, LocalSubst, LocalVar, SubstTail, Term, Type};

use crate::diagnostics::DISPLAY_DECODE_STEPS;
use crate::inductive::nat_value;
use crate::{Cx, Elaborator, dress_true, show_level};

/// Nodes the walk may visit. Generous next to `fmt.rs`'s 512, because a
/// spelled node is a handful of characters where a raw one is a record.
const SPELL_NODES: u32 = 320;
/// Nesting the walk may descend. A surface type deeper than this is not
/// readable spelled either.
const SPELL_DEPTH: u32 = 16;
/// Raw nodes tolerated before the whole attempt is abandoned (§2).
const SPELL_FALLBACKS: u32 = 4;
/// Characters of a raw node kept before eliding.
const RAW_NODE_CHARS: usize = 96;

impl Elaborator {
    /// A type as a human should read it: best-effort decoded head, surface
    /// spelling, then the bounded kernel form.
    pub(crate) fn display_type(&self, cx: &Cx, ty: &Type) -> String {
        let decoded = self.display_decode(cx, ty);
        let target = decoded.as_ref().unwrap_or(ty);
        match self.spell_type(cx, target) {
            Some(spelled) => spelled,
            None => dress_true(&format!("{target:?}")),
        }
    }

    /// [`Self::display_type`] for a message that makes a claim about a type.
    /// It declines unless the complete result has a surface spelling.
    pub(crate) fn display_type_clean(&self, cx: &Cx, ty: &Type) -> Option<String> {
        let decoded = self.display_decode(cx, ty);
        self.spell_type_clean(cx, decoded.as_ref().unwrap_or(ty))
    }

    fn display_decode(&self, cx: &Cx, ty: &Type) -> Option<Type> {
        self.semantic_oracle()
            .diagnostics(DISPLAY_DECODE_STEPS)
            .decode_type(&cx.gamma, ty)
    }

    /// Spell `ty` as surface, or decline. Declining means "the caller should
    /// print the raw bounded form", not "there was an error".
    pub(crate) fn spell_type(&self, cx: &Cx, ty: &Type) -> Option<String> {
        self.spell_within(cx, ty, SPELL_FALLBACKS)
    }

    /// [`Self::spell_type`] admitting **no** raw node: `Some` only when every
    /// node of `ty` spelled. A message that *makes a claim about* a type — as
    /// opposed to displaying one it was asked to display — needs this, because
    /// a claim the reader cannot check is worse than no claim
    /// (`issues/check-fallback-discards-expected-type.md`).
    pub(crate) fn spell_type_clean(&self, cx: &Cx, ty: &Type) -> Option<String> {
        self.spell_within(cx, ty, 0)
    }

    /// Complete source spelling for generated annotations. The caller must
    /// re-elaborate and compare it before using it as a type.
    pub(crate) fn spell_type_source(&self, cx: &Cx, ty: &Type) -> Option<String> {
        let mut sp = self.speller(cx);
        sp.qualified = true;
        sp.annotations = true;
        let out = sp.ty(ty, 0);
        (sp.fallbacks.get() == 0).then_some(out)
    }

    /// Spell a **term** as surface, or decline — [`Self::spell_type_clean`]'s
    /// counterpart at the other syntactic class, and admitting no raw node for
    /// the same reason.
    ///
    /// The walk has always spelled terms (an `El`'s payload, an equation's two
    /// sides, a call's arguments): what did not exist was an *entry point* at
    /// a term, so a diagnostic holding one had no choice but `{:?}`
    /// (issues/lgg-diagnostic-dumps-kernel-terms.md). The budgets, the
    /// per-node fallback and the abandon rule are the same ones, because it is
    /// the same walk. Only the clean flavour is offered: a diagnostic holding
    /// a bare term is *making a claim* about it, and half a spelling of a
    /// lowered inductive is the `inl[0,0](Σ[0,0](Unit 0). …)` wall wearing
    /// surface syntax. A tolerant flavour can be added when something wants to
    /// *display* a term it was asked to display.
    ///
    /// `t` must be scoped in `cx` — a subterm read out from under binders is
    /// **not**, and its variables would be spelled with the wrong names. A
    /// caller holding one strengthens it first ([`crate::strengthen_tm`]) and
    /// declines when it does not strengthen.
    pub(crate) fn spell_term_clean(&self, cx: &Cx, t: &Term) -> Option<String> {
        let sp = self.speller(cx);
        let out = sp.tm(t, 0);
        (sp.fallbacks.get() == 0).then_some(out)
    }

    /// [`Self::spell_term_clean`], but spelling a global **qualified** wherever
    /// its base name does not resolve back to it here. For a caller that
    /// re-*parses* what it renders — `omega`'s certificate route — the base
    /// name is not a presentation choice but a silent hole: `xs.len()` came
    /// back as `len(…)`, unbound outside `list`
    /// (issues/omega-renders-member-by-base-name.md).
    pub(crate) fn spell_term_source(&self, cx: &Cx, t: &Term) -> Option<String> {
        let mut sp = self.speller(cx);
        sp.qualified = true;
        let out = sp.tm(t, 0);
        (sp.fallbacks.get() == 0).then_some(out)
    }

    fn spell_within(&self, cx: &Cx, ty: &Type, fallbacks: u32) -> Option<String> {
        let sp = self.speller(cx);
        let out = sp.ty(ty, 0);
        (sp.fallbacks.get() <= fallbacks).then_some(out)
    }

    fn speller<'a>(&'a self, cx: &'a Cx) -> Speller<'a> {
        Speller {
            el: self,
            cx,
            names: RefCell::new(cx.names.clone()),
            nodes: Cell::new(SPELL_NODES),
            fallbacks: Cell::new(0),
            qualified: false,
            annotations: false,
        }
    }
}

struct Speller<'a> {
    el: &'a Elaborator,
    cx: &'a Cx,
    /// `cx.names` extended with one entry per binder the walk has descended
    /// under, so a `Var` under a printed `Π` resolves to the name just chosen
    /// for it.
    names: RefCell<Vec<String>>,
    nodes: Cell<u32>,
    fallbacks: Cell<u32>,
    /// Spell globals so the result can be **re-parsed** rather than only read.
    qualified: bool,
    annotations: bool,
}

impl Speller<'_> {
    // -- budget -------------------------------------------------------------

    /// Charge one node. `false` means the budget is spent and the caller must
    /// fall back.
    fn charge(&self, d: u32) -> bool {
        if d >= SPELL_DEPTH || self.nodes.get() == 0 {
            return false;
        }
        self.nodes.set(self.nodes.get() - 1);
        true
    }

    fn raw_ty(&self, ty: &Type) -> String {
        self.fallbacks.set(self.fallbacks.get() + 1);
        elide(&format!("{ty:?}"))
    }

    fn raw_tm(&self, t: &Term) -> String {
        self.fallbacks.set(self.fallbacks.get() + 1);
        elide(&format!("{t:?}"))
    }

    // -- binders ------------------------------------------------------------

    /// Binders the walk has descended under since `cx`.
    ///
    /// **Not `d`.** `d` is the *budget* depth ([`Self::charge`]) and counts
    /// every descent, binder or not — `Squash`'s payload, a `Π`'s domain and a
    /// spelled type argument all take `d + 1`. `names` is `cx.names` plus one
    /// entry per binder [`Self::under`] pushed, and `cx.names` is parallel to
    /// `cx.gamma.entries`, so this difference is what a context *length* has
    /// to be extended by to scope a type the walk is currently looking at
    /// (issues/pi-codomain-record-mismatch-panics-kernel.md).
    fn binders(&self) -> u32 {
        (self.names.borrow().len() - self.cx.names.len()) as u32
    }

    /// A name for a binder the kernel does not name: the first of a short
    /// preference list not already in scope, else `x{n}`.
    fn fresh(&self) -> String {
        let names = self.names.borrow();
        for cand in ["x", "y", "z", "a", "b", "c"] {
            if !names.iter().any(|n| n == cand) {
                return cand.to_string();
            }
        }
        format!("x{}", names.len())
    }

    /// Does `body`, scoped in `Γ` plus `d` display binders plus its own, use
    /// its own binder? This is [`crate::strengthen_ty`] at `d = 1` — drop the
    /// binder to a marker, shift back, and see whether the original is
    /// restored — which needs no new traversal of `Term`/`Type` to drift out of
    /// sync with the syntax. Spelled out here rather than called because the
    /// walk knows the *length* of the context `body` is scoped in but does not
    /// hold the context itself, and `drop_binders` reads only that length and
    /// the base.
    ///
    /// The base is why this is not a one-liner: under a context variable the
    /// tail must be `Wk`, since a variable cannot address a context-variable
    /// base. An `Empty` tail there is a kernel invariant violation, and the
    /// kernel says so by panicking (`crates/kernel/src/subst.rs`).
    fn dependent(&self, body: &Type, d: u32) -> bool {
        let m = self.cx.gamma.entries.len() as u32 + d;
        let tail = match self.cx.gamma.base {
            CtxBase::Nil => SubstTail::Empty {
                len: m,
                base: CtxBase::Nil,
            },
            CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
        };
        let terms = (0..m)
            .map(|k| Rc::new(Term::Var(LocalVar(m - 1 - k))))
            .chain(std::iter::once(Rc::new(Term::Zero)))
            .collect();
        let dropped = body.apply_local(&LocalSubst { tail, terms });
        dropped.shift_local(1) != *body
    }

    /// Spell `body` under one binder named `name`.
    fn under(&self, name: &str, body: &Type, d: u32) -> String {
        self.names.borrow_mut().push(name.to_string());
        let s = self.ty(body, d + 1);
        self.names.borrow_mut().pop();
        s
    }

    fn source_instance(&self, ind: &crate::inductive::Inductive, args: &[Rc<Term>], d: u32) -> Option<String> {
        if args.len() != ind.params.len() + ind.valparams.len() { return None; }
        let (types, values) = args.split_at(ind.params.len());
        let types = types.iter().map(|t| {
            // Decoding a canonical code only reads its own constructors;
            // the ambient universe is irrelevant to this source spelling.
            let code = Type::El { level: crate::Level::Zero, tm: Rc::clone(t) };
            self.ty(&code, d + 1)
        }).collect::<Vec<_>>();
        let values = values.iter().map(|t| self.tm(t, d + 1)).collect::<Vec<_>>();
        let head = if types.is_empty() { ind.name.clone() }
            else { format!("{}<{}>", ind.name, types.join(", ")) };
        Some(if values.is_empty() { head } else { format!("{head}({})", values.join(", ")) })
    }

    // -- types --------------------------------------------------------------

    fn ty(&self, ty: &Type, d: u32) -> String {
        if !self.charge(d) {
            return self.raw_ty(ty);
        }
        if self.annotations && let std::borrow::Cow::Owned(decoded) = crate::inductive::decoded(ty) {
            return self.ty(&decoded, d + 1);
        }
        if self.annotations && let Type::El { tm, .. } = ty
            && let Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(tm)
            && let Some(ind) = self.el.types.by_tag(tag)
            && let Some(source) = self.source_instance(&ind, &args, d)
        { return source; }
        // A reference to a registered lowering is spelled through the
        // registry's inline copy, which is what `tag_of` recognizes.
        if let Some(inline) = self.el.unspell_here(ty) {
            return self.ty(&inline, d);
        }
        // An inductive instance is its declaration's name, wherever its
        // lowering is what we are looking at.
        if matches!(ty, Type::Wf { .. } | Type::Sum { .. } | Type::Sigma { .. })
            && let Some(ind) = self.el.display_tag_of(ty)
        {
            if self.annotations && !ind.valparams.is_empty() {
                // Unlike a diagnostic, a generated annotation cannot omit
                // value arguments. Reuse the checked instance matcher.
                if self.names.borrow().len() != self.cx.names.len() {
                    return self.raw_ty(ty);
                }
                let Some(args) = self.el.instance_args(self.cx, &ind, ty) else {
                    return self.raw_ty(ty);
                };
                return self.source_instance(&ind, &args, d).unwrap_or_else(|| self.raw_ty(ty));
            }
            return if ind.params.is_empty() {
                ind.name.clone()
            } else if let Some(args) =
                self.el.display_targs(self.cx, ty, &ind, self.binders())
            {
                let shown = args
                    .iter()
                    .map(|(arg, _)| self.ty(arg, d + 1))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{shown}>", ind.name)
            } else {
                format!("{}<…>", ind.name)
            };
        }
        match ty {
            Type::Nat => "Nat".to_string(),
            Type::Unit { .. } => "True".to_string(),
            Type::Empty { .. } => "False".to_string(),
            Type::Ty(l) => format!("Type<{}>", show_level(l)),
            Type::El { tm, .. } => self.tm(tm, d),
            Type::Id { lhs, rhs, .. } => {
                format!("{} = {}", self.tm(lhs, d), self.tm(rhs, d))
            }
            // No surface form exists for strict equality; the glyph is
            // display-only and deliberately not `=`.
            Type::SEq { lhs, rhs, .. } => {
                format!("{} ≡ {}", self.tm(lhs, d), self.tm(rhs, d))
            }
            Type::Squash { ty, .. } => format!("∥{}∥", self.ty(ty, d + 1)),
            Type::Vec { elem, len, .. } => {
                format!("[{}; {}]", self.ty(elem, d + 1), self.tm(len, d))
            }
            Type::Fin { len } => format!("Fin({})", self.tm(len, d)),
            Type::Pi { dom, cod, .. } => {
                let dom_s = self.ty(dom, d + 1);
                if self.dependent(cod, d) {
                    let name = self.fresh();
                    let cod_s = self.under(&name, cod, d);
                    format!("({name}: {dom_s}) -> {cod_s}")
                } else {
                    // The binder is unused, so any name resolves nothing; push
                    // one anyway to keep the index arithmetic honest.
                    let cod_s = self.under("_", cod, d);
                    format!("{dom_s} -> {cod_s}")
                }
            }
            Type::GlobalTy { var, subst } => self
                .global(*var, subst)
                .map(|(n, _)| n)
                .unwrap_or_else(|| self.raw_ty(ty)),
            _ => self.raw_ty(ty),
        }
    }

    // -- terms --------------------------------------------------------------

    fn tm(&self, t: &Term, d: u32) -> String {
        if !self.charge(d) {
            return self.raw_tm(t);
        }
        if self.annotations
            && let Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(t)
            && let Some(ind) = self.el.types.by_tag(tag)
            && let Some(source) = self.source_instance(&ind, &args, d)
        { return source; }
        // `3`, not `S(S(S(0)))`.
        if let Some(k) = nat_value(t) {
            return k.to_string();
        }
        match t {
            Term::Var(LocalVar(i)) => self.var(*i).unwrap_or_else(|| self.raw_tm(t)),
            Term::Succ(p) => format!("Succ({})", self.tm(p, d + 1)),
            Term::Refl { .. } => "refl".to_string(),
            Term::Triv { .. } => "trivial".to_string(),
            Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                format!("({}, {})", self.tm(fst, d + 1), self.tm(snd, d + 1))
            }
            Term::Lam { dom, body, .. } => {
                let dom_s = self.ty(dom, d + 1);
                let name = self.fresh();
                self.names.borrow_mut().push(name.clone());
                let body_s = self.tm(body, d + 1);
                self.names.borrow_mut().pop();
                format!("λ ({name}: {dom_s}) => {body_s}")
            }
            // A code and the type it encodes are written identically, so a
            // code former delegates rather than repeating the table.
            Term::TmNat => "Nat".to_string(),
            Term::TmUnit { .. } => "True".to_string(),
            Term::TmEmpty { .. } => "False".to_string(),
            Term::TmTy(level) => format!("Type<{}>", show_level(level)),
            Term::TmId { ty, lhs, rhs, .. } => {
                let _ = ty;
                format!("{} = {}", self.tm(lhs, d + 1), self.tm(rhs, d + 1))
            }
            Term::TmVec { elem, len, .. } => {
                format!("[{}; {}]", self.tm(elem, d + 1), self.tm(len, d + 1))
            }
            Term::TmFin { len } => format!("Fin({})", self.tm(len, d + 1)),
            Term::TmSquash { ty, .. } => format!("∥{}∥", self.tm(ty, d + 1)),
            Term::Squash { tm, .. } => format!("squash({})", self.tm(tm, d + 1)),
            Term::Supf { .. }
            | Term::Inl { .. }
            | Term::Inr { .. }
            | Term::InlAt { .. }
            | Term::InrAt { .. } => self.ctor_value(t, d).unwrap_or_else(|| self.raw_tm(t)),
            Term::App { .. } => self.call(t, d),
            Term::GlobalTm { var, subst } => self
                .global(*var, subst)
                .map(|(n, _)| n)
                .unwrap_or_else(|| self.raw_tm(t)),
            _ => self.raw_tm(t),
        }
    }

    /// A lowered constructor value as `C(f₁, …)` — the shape a `match` arm's
    /// motive is instantiated at, so it is what a goal statement inside an arm
    /// shows. This is the *canonical* half of
    /// [`Elaborator::read_ctor`](crate::Elaborator::read_ctor): an injection
    /// path over a `Pair`, whose payload fields sit in the label's Σ spine and
    /// whose plain children sit in the tuple. Deliberately not a call to that
    /// method — it takes a constructor spine, can elaborate projections, and
    /// can fail, none of which a display path may do. Anything that does not
    /// line up exactly declines, so the worst case is the raw form.
    fn ctor_value(&self, t: &Term, d: u32) -> Option<String> {
        let (label, children, ind) = match t {
            Term::Supf {
                shape,
                label,
                children,
                ..
            } => (&**label, Some(&**children), self.el.display_tag_of(shape)?),
            // Tier 0: the value *is* the injection, and either summand type
            // carries the nominal tag — behind a spine-code reference for a
            // flat declaration, which the display lookup sees through.
            Term::Inl { lhs, .. } => (t, None, self.el.display_tag_of(lhs)?),
            Term::Inr { rhs, .. } => (t, None, self.el.display_tag_of(rhs)?),
            // The checked spellings carry the **whole sum**, not a summand,
            // and `tag_of` already walks a `Sum` to its leftmost constructor
            // — so the same lookup serves, one node higher
            // (`docs/intro-by-type-design.md` §4.2). An annotation that is
            // not structurally a sum (an un-reduced `El(case(…))`) declines,
            // and the display falls back to `raw_tm` as it does for every
            // other shape it cannot read; a whnf here would need a span the
            // display path does not carry.
            Term::InlAt { ty, .. } | Term::InrAt { ty, .. } => {
                (t, None, self.el.display_tag_of(ty)?)
            }
            _ => return None,
        };
        // Walk the injection path: `Inr` steps past a constructor, `Inl`
        // selects one.
        let n = ind.ctors.len();
        let mut i = 0usize;
        let mut cur = label;
        loop {
            match crate::spelling::inj_of(cur) {
                Some((false, val)) if i + 1 < n => {
                    i += 1;
                    cur = val;
                }
                Some((true, val)) => {
                    cur = val;
                    break;
                }
                _ => break,
            }
        }
        let ctor = ind.ctors.get(i)?;
        // A container field is neither payload nor a plain child, and reading
        // it back means reading a vector: out of scope for a display.
        if ctor.container().is_some() {
            return None;
        }
        // A `match` arm's motive is instantiated at the *neutral* summand
        // value, not at a canonical constructor
        // (issues/absurd-on-branch-scrutinee.md), so the payload is a variable
        // and its fields are projections of it. The constructor is still
        // identified by the injection path, which is the readable part: name
        // it, and admit the fields were not recovered — the same convention a
        // parameterized inductive's arguments get.
        let Some((_, snd)) = crate::spelling::pair_of(cur) else {
            return Some(if ctor.fields.is_empty() {
                ctor.name.clone()
            } else {
                format!("{}(…)", ctor.name)
            });
        };
        let mut payload: Vec<&Rc<Term>> = Vec::new();
        let mut p = snd;
        for _ in 0..ctor.payload().count() {
            let Some((fst, snd)) = crate::spelling::pair_of(p) else {
                return None;
            };
            payload.push(fst);
            p = snd;
        }
        let mut kids: Vec<&Rc<Term>> = Vec::new();
        if let Some(children) = children {
            let mut c = children;
            for _ in 0..ctor.arity() {
                let Some((fst, snd)) = crate::spelling::pair_of(c) else {
                    return None;
                };
                kids.push(fst);
                c = snd;
            }
        } else if ctor.arity() > 0 {
            return None;
        }
        // Re-interleave into declaration order, which is the order the surface
        // writes the constructor's arguments in.
        let (mut a, mut b) = (0usize, 0usize);
        let mut shown = Vec::with_capacity(ctor.fields.len());
        for k in 0..ctor.fields.len() {
            let v = if ctor.kind[k].is_child() {
                b += 1;
                kids.get(b - 1)?
            } else {
                a += 1;
                payload.get(a - 1)?
            };
            shown.push(self.tm(v, d + 1));
        }
        Some(if shown.is_empty() {
            ctor.name.clone()
        } else {
            format!("{}({})", ctor.name, shown.join(", "))
        })
    }

    /// An `App` spine as a call. The head's *implicit* parameters are dropped,
    /// so `len<A>(xs)`'s two-argument spine prints as `len(xs)` — what the
    /// caller wrote.
    fn call(&self, t: &Term, d: u32) -> String {
        let mut args: Vec<&Rc<Term>> = Vec::new();
        let mut head = t;
        while let Term::App { fun, arg, .. } = head {
            args.push(arg);
            head = fun;
        }
        args.reverse();

        // Record projections have a nominal generated-definition key. The
        // spine is the declaration's telescope and then the receiver
        // (`docs/per-instantiation-type-codes-design.md` §13), so the
        // receiver is the last argument and the arguments before it are the
        // instantiation — dropped, exactly as a call's implicits are. Do not
        // unfold definitions or guess how an applied function-valued field
        // hides implicit arguments.
        if let Term::GlobalTm { var, subst } = head
            && subst.terms.is_empty()
            && let Some(crate::gendefs::GenDef::RecProj(tag, field)) = self.el.gen_def_of(*var)
            && let Some(record) = self.el.types.by_tag(tag)
            && record.is_record
            && args.len() == record.params.len() + record.valparams.len() + 1
            && let Some(receiver) = args.last()
            && let Some((Some(name), _)) = record.ctors[0].fields.get(field)
        {
            let shown = self.tm(receiver, d + 1);
            return if matches!(receiver.as_ref(), Term::Var(_) | Term::App { .. }) {
                format!("{shown}.{name}")
            } else {
                format!("({shown}).{name}")
            };
        }

        let (name, implicit) = match head {
            Term::GlobalTm { var, subst } => match self.global(*var, subst) {
                Some((n, imp)) => (n, imp),
                None => return self.raw_tm(t),
            },
            Term::Var(LocalVar(i)) => match self.var(*i) {
                Some(n) => (n, Vec::new()),
                None => return self.raw_tm(t),
            },
            _ => return self.raw_tm(t),
        };
        let shown: Vec<String> = args
            .iter()
            .enumerate()
            .filter(|(i, _)| !implicit.get(*i).copied().unwrap_or(false))
            .map(|(_, a)| self.tm(a, d + 1))
            .collect();
        if shown.is_empty() {
            name
        } else {
            format!("{name}({})", shown.join(", "))
        }
    }

    // -- names --------------------------------------------------------------

    /// The binder name for a de Bruijn index, or `None` when the index is out
    /// of the scope this display knows about.
    fn var(&self, i: u32) -> Option<String> {
        let names = self.names.borrow();
        let pos = names.len().checked_sub(1 + i as usize)?;
        names.get(pos).cloned()
    }

    /// A global's written name and its parameters' implicitness. Declines for
    /// a substituted global (a top-level declaration has a nil context, so its
    /// substitution carries no terms — anything else is not a plain reference)
    /// and for a binding `globals` does not name, which is every generated
    /// definition.
    fn global(&self, var: GlobalVar, subst: &LocalSubst) -> Option<(String, Vec<bool>)> {
        if !subst.terms.is_empty() {
            return None;
        }
        let abs = self.el.global_abs_of(var)?;
        let mut name = self.el.global_name_at(abs)?;
        // A member's base name is the presentation choice, and re-parsing it
        // elsewhere resolves to nothing (or, worse, to something else). Fall
        // back to the qualified spelling exactly where the base one does not
        // come back here.
        if self.qualified && !self.el.base_name_resolves_to(&name, abs) {
            name = self.el.global_qualified_name_at(abs)?;
        }
        let implicit = self.el.params_at(abs).iter().map(|p| p.implicit).collect();
        Some((name, implicit))
    }
}

/// Truncate a raw node's rendering. `fmt.rs` already bounds it by nodes; this
/// bounds it by columns, which is the axis a diagnostic is read on.
fn elide(s: &str) -> String {
    let s = crate::dress_true(s);
    match s.char_indices().nth(RAW_NODE_CHARS) {
        None => s,
        Some((at, _)) => format!("{}…", &s[..at]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use heather_kernel::level::Level;

    /// The negative control the design asks for, and the reason it lives here:
    /// the surface language makes an unspellable type hard to *write*, since
    /// every type a declaration can state is either a former this module knows
    /// or an application of something named. So the refusal is exercised on a
    /// hand-built type — `sEmpty` has no surface form and never will.
    #[test]
    fn a_type_with_no_surface_form_is_refused_rather_than_guessed() {
        let el = Elaborator::with_prelude().expect("prelude");
        let cx = Cx::empty();
        let raw = Type::SEmpty { level: Level::Zero };
        // One refusal is under the cap, so the node itself falls back while the
        // attempt stands.
        assert_eq!(el.spell_type(&cx, &raw).as_deref(), Some("sEmpty 0"));
        // Wrapped in something that *does* spell, the fallback is local: the
        // arrow is still readable.
        let pi = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(raw.clone()),
            cod: Rc::new(Type::Nat),
        };
        assert_eq!(el.spell_type(&cx, &pi).as_deref(), Some("sEmpty 0 -> Nat"));
    }

    /// Above the fallback budget the whole attempt is abandoned: a half-spelled
    /// type *looks* like surface syntax while being neither, so the caller gets
    /// the honest raw form instead.
    #[test]
    fn more_refusals_than_the_budget_abandons_the_spelling() {
        let el = Elaborator::with_prelude().expect("prelude");
        let cx = Cx::empty();
        let mut ty = Type::SEmpty { level: Level::Zero };
        for _ in 0..SPELL_FALLBACKS {
            ty = Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::SEmpty { level: Level::Zero }),
                cod: Rc::new(ty),
            };
        }
        assert_eq!(el.spell_type(&cx, &ty), None);
    }
}
