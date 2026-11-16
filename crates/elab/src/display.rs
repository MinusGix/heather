//! Printing a kernel type back as **surface** syntax. Diagnostics use the
//! bounded presentation path; generated annotations additionally require
//! complete source spelling and a caller-owned type comparison.
//!
//! `docs/elaborator/surface-type-display-design.md`. [[goal-display-decodes]] gave the
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
//! - **The diagnostic path never reduces.** No δ, no whnf, no fuel. The
//!   registry consultations are [`Elaborator::unspell_here`] and the type
//!   names the program wrote ([`TypeName`]), lookups rather than
//!   reductions. So this code cannot affect what is checked — a stronger
//!   guarantee than the reader's, which at least spends steps. The one
//!   contraction is a β-redex's, at a node that would otherwise print raw: a
//!   redex has no surface form, and a let-bound or instantiated λ at a head
//!   leaves one in the types a mismatch note holds
//!   (`issues/elab-accepts-mismatch-under-redex-head.md`). It is syntactic
//!   substitution, charged to the same node budget, and only in the reading
//!   flavours: the source flavours, whose output is re-parsed, still decline.
//! - **Every node either spells or falls back to that node's `{:?}`.** There
//!   is no whole-type cliff: an unspellable argument prints raw inside a call
//!   that prints as a call. A raw node is truncated ([`RAW_NODE_CHARS`]) so
//!   one bad subterm cannot reintroduce the several-hundred-column message.
//! - **Too many fallbacks abandons the attempt.** Above [`SPELL_FALLBACKS`]
//!   the top-level call declines and the caller prints the plain bounded
//!   `Debug`. A half-spelled monster is worse than the honest raw form,
//!   because it *looks* like surface syntax while being neither.

use std::cell::{Cell, RefCell};
use heather_kernel::rc::Rc;

use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{CtxBase, GlobalBinding, GlobalVar, LocalSubst, LocalVar, SubstTail, Term, Type};

use crate::diagnostics::DISPLAY_DECODE_STEPS;
use crate::gendefs::GenDef;
use crate::unification::Sol;
use crate::{Cx, Elaborator, ParamMeta, dress_true, show_level};
use heather_syntax::{OpFixity, OperatorForm};
use crate::iwf_family::IwfFamily;
use crate::gendefs::GeneratedDefs;
use crate::inductive::Inductives;
use crate::app_unify::AppUnify;
use crate::name_lookup::NameLookup;

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
    /// Substitute known scratch solutions and give the remaining slots stable
    /// display-only names. The markers are outside Ψ and are consumed by the
    /// bounded speller; they are never sent to reduction or type checking.
    pub(crate) fn display_deferred_argument(
        &self, cx: &Cx, head: &Term, params: &[ParamMeta],
        domains: &[(usize, Type)], slot_param: &[usize], sols: &[Sol],
    ) -> String {
        let selected = match head {
            Term::GlobalTm { var, .. } => self.global_abs_of(*var)
                .and_then(|abs| NameLookup(self).global_qualified_name_at(abs)),
            _ => self.spell_term_clean(cx, head),
        }.unwrap_or_else(|| "…".to_string());
        let first = self.placeholder_base();
        let placeholders: Vec<_> = slot_param.iter().enumerate().map(|(slot, &p)| {
            let name = params.get(p).map(|p| p.name.as_str()).unwrap_or("_");
            (GlobalVar::index(first + slot as u32), format!("?{name}"))
        }).collect();
        let entries = sols.iter().enumerate().rev().map(|(slot, sol)| {
            GlobalEntry::Tm(sol.solved().cloned().unwrap_or_else(|| Rc::new(Term::GlobalTm {
                var: placeholders[slot].0,
                subst: LocalSubst::id(&cx.gamma),
            })))
        }).collect();
        let sigma = GlobalSubst { entries };
        let shown = domains.iter().map(|(p, dom)| {
            let dom = dom.apply_global(&sigma);
            let mut sp = self.speller(cx);
            sp.rough = Some(&placeholders);
            let ty = sp.ty(&dom, 0);
            let name = params.get(*p).map(|p| p.name.as_str()).unwrap_or("_");
            format!("`{name}: {ty}`")
        }).collect::<Vec<_>>().join(", ");
        format!("\nselected callee: `{selected}`; rough parameter types: {shown}")
    }

    /// The first Ψ index past every binding the elaborator knows, where
    /// display-only placeholder globals start.
    pub(crate) fn placeholder_base(&self) -> u32 {
        self.psi.bindings.len() as u32 + self.global_padding() + self.scope.meta_pushed.borrow().len() as u32
    }

    /// What a numeral elaborates to at each carrier a closed `Numeral`
    /// instance embeds it into, over the literal as local `0`, scoped where
    /// the display reads (docs/language/carrier-directed-numerals-design.md): the
    /// body of the instance's `ofNat` field, which is what
    /// [`Literals::reduced_embedding`](crate::literals::Literals::reduced_embedding) leaves of a literal at that carrier —
    /// `Rat::ofInt(OfNat(n))` at `Rat`, and at `Int`, whose field is the
    /// constructor `OfNat`, that constructor's value. Read off the
    /// definitions; nothing is reduced. A parameterized instance (`BitVec(n)`)
    /// and a field that is no λ after its definitions contribute nothing,
    /// and `Nat`'s identity embedding is the display's own numeral.
    pub(crate) fn numeral_templates(&self) -> Vec<Term> {
        // A committed body names committed definitions only: it is read as
        // stored.
        let definition = |abs: usize| -> Option<Term> {
            let Some(GlobalBinding::Tm { body: Some(body), .. }) = self.psi.bindings.get(abs) else {
                return None;
            };
            Some((**body).clone())
        };
        let class = crate::literals::NUMERAL;
        let mut out = Vec::new();
        for (head, index) in self.traits.instances_of_class(class) {
            let Some(info) = self.traits.instance(&crate::traits::instance_key(class, &head, &index)) else {
                continue;
            };
            if info.parameterized {
                continue;
            }
            let Some(abs) = self.names.global(&info.global).map(|g| g.abs as usize) else {
                continue;
            };
            // A name stands for its definition; the dictionary is the
            // class record's value, the tag then `(ofNat, ⟨⟩)`.
            let unfolded = |t: Term| match t {
                Term::GlobalTm { var, ref subst } if subst.terms.is_empty() => {
                    self.global_abs_of(var).and_then(definition)
                }
                t => Some(t),
            };
            let entry = |t: Term, first: bool| match unfolded(t)? {
                Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                    Some((*if first { fst } else { snd }).clone())
                }
                _ => None,
            };
            let Some(field) = definition(abs)
                .and_then(|dict| entry(dict, false))
                .and_then(|rest| entry(rest, true))
                .and_then(|field| unfolded(field).and_then(unfolded))
            else {
                continue;
            };
            let Term::Lam { body, .. } = field else { continue };
            // `Nat`'s identity embedding is the display's own numeral.
            if !matches!(*body, Term::Var(_)) {
                out.push((*body).clone());
            }
        }
        out
    }

    /// A type mentioning placeholder globals (from [`Self::placeholder_base`]
    /// on), each spelled by its name. Raw nodes are elided.
    pub(crate) fn display_rough_type(&self, cx: &Cx, ty: &Type, placeholders: &[(GlobalVar, String)]) -> String {
        let mut sp = self.speller(cx);
        sp.rough = Some(placeholders);
        sp.ty(ty, 0)
    }

    /// [`Self::display_rough_type`] for a term.
    pub(crate) fn display_rough_term(&self, cx: &Cx, t: &Term, placeholders: &[(GlobalVar, String)]) -> String {
        let mut sp = self.speller(cx);
        sp.rough = Some(placeholders);
        sp.tm(t, 0)
    }

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
            crossed: RefCell::new(Vec::new()),
            nodes: Cell::new(SPELL_NODES),
            fallbacks: Cell::new(0),
            qualified: false,
            annotations: false,
            rough: None,
            numerals: std::cell::OnceCell::new(),
        }
    }
}

/// The type of the closed top-level term `name`, spelled as source with
/// every name qualified ([`Elaborator::spell_type_source`]), after the
/// display's decoding: what a tool generating code over the term's value
/// needs to annotate it (`heather eval`). `None` for a name that is not a
/// plain top-level term, or a type with a node the speller cannot write.
/// A generated annotation is elaborated again, so a wrong spelling is a
/// refusal there and not a misreading.
pub fn global_type_source(el: &Elaborator, name: &str) -> Option<String> {
    let (_, ty, _) = crate::host::Host(el).raw_global(name)?;
    let cx = Cx::empty();
    let decoded = el.display_decode(&cx, &ty);
    el.spell_type_source(&cx, decoded.as_ref().unwrap_or(&ty))
}

/// A type name the program wrote, and the instance it names: what the
/// display respells by that name (issues/type-name-display-respelling.md).
///
/// A `def` at a universe is expanded where it is read
/// (docs/library/fixed-width-integers-design.md §2), so nothing after elaboration can
/// tell `u8` from `BitVec(8)`. The expansion is a pure function of the
/// definition, so it is read once, off the definition's body, when the name
/// is first written, and the display looks an instance up here. Only bodies
/// whose meaning the display can match without reducing anything are kept:
/// a declaration's type constructor applied to closed arguments (`def Byte:
/// Type = BitVec(8)`), or the constructor itself over the family's one
/// argument (`def u: Nat → Type = BitVec`). Anything else is not recorded,
/// and its expansion keeps the honest spelling.
#[derive(Clone)]
pub(crate) struct TypeName {
    /// The name as written: `Byte`, or the family part of `u8`, `u`.
    written: String,
    /// The definition it resolved to, module-qualified. A display uses the
    /// name only where it still resolves there.
    def: String,
    /// The declaration the name expands to an instance of.
    tag: u32,
    shape: TypeNameShape,
}

#[derive(Clone)]
enum TypeNameShape {
    /// This instance only: the declaration's value arguments, closed.
    Exact(Vec<Rc<Term>>),
    /// A width family, `u(n)` for every `n`: spelled `u8` at a numeral.
    Family,
}

impl Elaborator {
    /// Note that the program wrote `written`, a type name resolving to the
    /// `def` `def` (module-qualified), so the display may respell its
    /// expansion by it. Written again, it becomes the most recent, which is
    /// the one the display prefers.
    pub(crate) fn record_type_name(&self, written: &str, def: &str) {
        let mut names = self.memos.type_names.borrow_mut();
        if let Some(at) = names.iter().position(|n| n.written == written && n.def == def) {
            let name = names.remove(at);
            names.push(name);
            return;
        }
        if let Some((tag, shape)) = self.type_name_shape(def) {
            names.push(TypeName { written: written.to_string(), def: def.to_string(), tag, shape });
        }
    }

    /// What the `def` `def` names, read off its body without reducing it:
    /// `D#tycode_fn` applied to closed value arguments, `D#tycode`, or
    /// `λ n. D#tycode_fn(n)` for a declaration with one value parameter and no
    /// type parameters — or any of those through another `def` that is one
    /// (`def Word: Type = u(16)`, `def Short: Type = Word`).
    fn type_name_shape(&self, def: &str) -> Option<(u32, TypeNameShape)> {
        self.type_name_shape_at(self.lookup_global(def)?.abs, 4)
    }

    fn type_name_shape_at(&self, abs: u32, depth: u32) -> Option<(u32, TypeNameShape)> {
        let (_, body) = NameLookup(self).global_body_at(abs as usize)?;
        let closed = |t: &Rc<Term>| t.shift_local(1) == **t && !crate::gendefs::names_global(t);
        let (family, inner) = match &*body {
            Term::Lam { body, .. } => (true, body),
            _ => (false, &body),
        };
        let mut args = Vec::new();
        let mut head = &**inner;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(Rc::clone(arg));
            head = fun;
        }
        args.reverse();
        let Term::GlobalTm { var, .. } = head else { return None };
        // The body is scoped in the Ψ prefix before its own binding.
        let at = var.position(abs as usize)? as u32;
        let is_bound = matches!(args.as_slice(), [a] if matches!(**a, Term::Var(LocalVar(0))));
        let (tag, takes_args) = match self.types.gdefs().key_for_abs(&at).copied() {
            Some(GenDef::TyCodeFn(tag)) => (tag, true),
            Some(GenDef::TyCode(tag)) => (tag, false),
            Some(_) => return None,
            // Another `def`, by what it names.
            None if depth > 0 => {
                let (tag, shape) = self.type_name_shape_at(at, depth - 1)?;
                return match (shape, family, args.as_slice()) {
                    (TypeNameShape::Family, false, [v]) if closed(v) => Some((tag, TypeNameShape::Exact(args))),
                    (TypeNameShape::Family, true, _) if is_bound => Some((tag, TypeNameShape::Family)),
                    (shape, false, []) => Some((tag, shape)),
                    _ => None,
                };
            }
            None => return None,
        };
        let ind = self.types.by_tag(tag)?;
        if !ind.params.is_empty() || ind.index.is_some() || ind.codata {
            return None;
        }
        if family {
            let one = takes_args && ind.valparams.len() == 1 && is_bound;
            return one.then_some((tag, TypeNameShape::Family));
        }
        if args.len() != ind.valparams.len() || (!takes_args && !args.is_empty()) || !args.iter().all(closed) {
            return None;
        }
        Some((tag, TypeNameShape::Exact(args)))
    }
}

struct Speller<'a> {
    el: &'a Elaborator,
    cx: &'a Cx,
    /// `cx.names` extended with one entry per binder the walk has descended
    /// under, so a `Var` under a printed `Π` resolves to the name just chosen
    /// for it.
    names: RefCell<crate::spine::Binders>,
    /// The types of the binders [`Self::binders`] counts, outermost first,
    /// each scoped in `cx` plus the ones before it, so [`Self::here`] can
    /// rebuild the context the walk is standing in.
    crossed: RefCell<Vec<(Type, crate::Level)>>,
    nodes: Cell<u32>,
    fallbacks: Cell<u32>,
    /// Spell globals so the result can be **re-parsed** rather than only read.
    qualified: bool,
    annotations: bool,
    /// Presentation-only scratch placeholders; this mode elides raw nodes.
    rough: Option<&'a [(GlobalVar, String)]>,
    /// [`Elaborator::numeral_templates`], read the first time the walk meets
    /// a term that could be a numeral.
    numerals: std::cell::OnceCell<Vec<Term>>,
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
        if self.rough.is_some() { return "…".to_string(); }
        self.fallbacks.set(self.fallbacks.get() + 1);
        elide(&format!("{ty:?}"))
    }

    fn raw_tm(&self, t: &Term) -> String {
        if let Some(name) = self.alias(t) {
            return name;
        }
        if self.rough.is_some() { return "…".to_string(); }
        self.fallbacks.set(self.fallbacks.get() + 1);
        elide(&format!("{t:?}"))
    }

    /// A spelling that admits, with `…`, what it did not recover. A reader
    /// can take that; a caller that re-*parses* the result cannot, so there it
    /// counts as a fallback and the source flavour declines — before this,
    /// `omega` met the `…` of an arm's `Cons(…)` as an unexpected character.
    fn elided(&self, shown: String) -> String {
        if self.qualified {
            self.fallbacks.set(self.fallbacks.get() + 1);
        }
        shown
    }

    /// The written name of an alias in scope that `t` *is*, before `t` falls
    /// back to its raw form. A `match` arm binds its constructor's fields as
    /// aliases for projections out of the arm's payload or children
    /// (`fst(snd(#rest))`), and a projection out of a neutral tuple has no
    /// spelling of its own — but the arm binder's name is one, and the one
    /// the programmer wrote (issues/tier1-arm-binder-has-no-spelling.md). Only
    /// a fallback: a term that spells never becomes a `let`'s name, so no
    /// display that worked changes. An alias counts only while its name still
    /// means it — not re-bound by a later binder or alias — so re-parsing the
    /// spelling here comes back to `t`.
    fn alias(&self, t: &Term) -> Option<String> {
        let names = self.names.borrow();
        // Innermost first, so the aliases bound after `a` are the ones
        // already passed.
        let mut later_aliases: Vec<&str> = Vec::new();
        self.cx.aliases.iter_inner().find_map(|a| {
            let shadowed_by_alias = later_aliases.contains(&a.name.as_str());
            later_aliases.push(&a.name);
            // A context can carry an alias bound deeper than its own names
            // (one cut back to a prefix); that alias is not in scope here.
            let later = names.len().checked_sub(a.depth)?;
            // The term first: it is the test that almost always fails.
            if !shifted_projection(&a.term, later as u32, t) && !self.reduced_child(a, later as u32, t) {
                return None;
            }
            let shadowed = shadowed_by_alias || names.iter_inner().take(later).any(|n| n == a.name);
            let written = a.name.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_');
            (written && !shadowed).then(|| a.name.clone())
        })
    }

    /// Is `t` the arm child alias `a` reads, once read? A recursive child's
    /// alias is the match's `nth(cs; i)`, which the goal a motive hands an
    /// arm has already computed to the projection out of the children
    /// (`fst(cs)` for `rest`), as [`crate::spelling::tuple_fields`] reads it.
    /// `later` is how far below the alias's depth the walk is.
    fn reduced_child(&self, a: &crate::context::Alias, later: u32, t: &Term) -> bool {
        if crate::spelling::proj_of(t).is_none() || !matches!(crate::spelling::app_spine(&a.term).0, Term::ElimNat { .. }) {
            return false;
        }
        // Reduced where the context is, then moved to where the walk is.
        let Some(to_cx) = self.cx.names.len().checked_sub(a.depth) else {
            return false;
        };
        let Some(below_cx) = (later as usize).checked_sub(to_cx) else {
            return false;
        };
        let term = a.term.shift_local(to_cx as u32);
        let Ok(reduced) = self.el.goal_oracle().whnf_term_bounded(&self.cx.gamma, &term) else {
            return false;
        };
        crate::spelling::proj_of(&reduced).is_some() && shifted_projection(&reduced, below_cx as u32, t)
    }

    /// The name the program wrote for the instance of declaration `tag` at
    /// value arguments `values` (scoped where the walk is), if it wrote one
    /// that still means it here: [`TypeName`]. The most recently written
    /// wins, which inside a declaration is the one that declaration wrote.
    /// For a reader only: a source flavour's spelling is re-elaborated, and
    /// what it emits stays the declaration's own name.
    fn named(&self, tag: u32, values: &[Rc<Term>], d: u32) -> Option<String> {
        if self.qualified || self.annotations {
            return None;
        }
        let candidates: Vec<TypeName> = self.el.memos.type_names.borrow().iter().rev()
            .filter(|n| n.tag == tag)
            .cloned()
            .collect();
        candidates.into_iter().find_map(|n| {
            let hidden = self.names.borrow().contains(&n.written)
                || self.cx.aliases.iter_inner().any(|a| a.name == n.written);
            if hidden || Inductives(self.el).global_value(&n.written).as_deref() != Some(n.def.as_str()) {
                return None;
            }
            match (&n.shape, values) {
                (TypeNameShape::Exact(args), _) => {
                    (args.len() == values.len() && args.iter().zip(values).all(|(a, v)| a == v))
                        .then(|| n.written.clone())
                }
                (TypeNameShape::Family, [v]) => {
                    // `u8`, unless `u8` is a name of its own, which would be
                    // read instead of the family (§2.2).
                    if let Some(k) = crate::inductive::nat_numeral(v) {
                        let short = format!("{}{k}", n.written);
                        if matches!(crate::inductive::split_width(&short), Some((f, _)) if f == n.written)
                            && Inductives(self.el).global_value(&short).is_none()
                        {
                            return Some(short);
                        }
                    }
                    Some(format!("{}({})", n.written, self.tm(v, d + 1)))
                }
                (TypeNameShape::Family, _) => None,
            }
        })
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

    /// The context the walk is standing in: `cx` extended by the binders it
    /// has crossed, under the names chosen for them. A reader that has to
    /// work *at* the walk's position — [`Inductives::display_targs`]
    /// re-lowers a declaration at arguments that may mention those binders —
    /// takes this rather than strengthening back out to `cx`
    /// (issues/type-arguments-under-a-binder-print-elided.md).
    fn here(&self) -> std::borrow::Cow<'_, Cx> {
        let crossed = self.crossed.borrow();
        if crossed.is_empty() {
            return std::borrow::Cow::Borrowed(self.cx);
        }
        let names = self.names.borrow();
        let mut cx = self.cx.clone();
        let base = self.cx.names.len();
        for (k, (ty, level)) in crossed.iter().enumerate() {
            let name = names.get(base + k).unwrap_or("_").to_string();
            cx.push(name, ty.clone(), level.clone());
        }
        std::borrow::Cow::Owned(cx)
    }

    /// Enter a binder of type `ty` named `name`; [`Self::leave`] undoes it.
    fn enter(&self, name: &str, ty: &Type, level: &crate::Level) {
        self.names.borrow_mut().push(name, None);
        self.crossed.borrow_mut().push((ty.clone(), level.clone()));
    }

    fn leave(&self) {
        self.names.borrow_mut().pop();
        self.crossed.borrow_mut().pop();
    }

    /// A name for a binder the kernel does not name: the first of a short
    /// preference list not already in scope, else `x{n}`.
    fn fresh(&self) -> String {
        let names = self.names.borrow();
        let used = |candidate: &str| names.contains(candidate)
            || self.cx.aliases.iter_inner().any(|a| a.name == candidate);
        for cand in ["x", "y", "z", "a", "b", "c"] {
            if !used(cand) {
                return cand.to_string();
            }
        }
        let mut next = names.len();
        loop {
            let candidate = format!("x{next}");
            if !used(&candidate) { return candidate; }
            next += 1;
        }
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
            CtxBase::Nil => SubstTail::Empty,
            CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
        };
        let terms = (0..m)
            .map(|k| Rc::new(Term::Var(LocalVar(m - 1 - k))))
            .chain(std::iter::once(Rc::new(Term::Zero)))
            .collect();
        let dropped = body.apply_local(&LocalSubst { tail, terms });
        dropped.shift_local(1) != *body
    }

    /// Spell `body` under one binder of type `dom` named `name`.
    fn under(&self, name: &str, dom: &Type, level: &crate::Level, body: &Type, d: u32) -> String {
        self.enter(name, dom, level);
        let s = self.ty(body, d + 1);
        self.leave();
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
        if (self.annotations || self.rough.is_some()) && let std::borrow::Cow::Owned(decoded) = crate::inductive::decoded(ty) {
            return self.ty(&decoded, d + 1);
        }
        if self.annotations && let Type::El { tm, .. } = ty
            && let Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(tm)
            && let Some(ind) = self.el.types.by_tag(tag)
            && let Some(source) = self.source_instance(&ind, &args, d)
        { return source; }
        // A codata instance as a code (a type argument, `PreservesRelation<
        // CoTree<R>(E), …>`) is spelled as the instance it decodes to.
        if let Type::El { tm, .. } = ty
            && matches!(**tm, Term::TmM { .. })
            && let std::borrow::Cow::Owned(decoded) = crate::inductive::decoded(ty)
        {
            return self.ty(&decoded, d + 1);
        }
        // A reference to a registered lowering is spelled through the
        // registry's inline copy, which is what `tag_of` recognizes.
        if let Some(inline) = self.el.unspell_here(ty) {
            return self.ty(&inline, d);
        }
        // A codata instance, `M(…)(⟨⟩)`: its declaration's name, with the type
        // arguments read off the shape it carries (a tier-1 spine), and value
        // arguments elided (docs/inductives/codata-elaborator-design.md §2).
        if let Type::M { sig, index } = ty
            && let Some(ind) = self.el.tag_of(ty).filter(|i| i.codata)
        {
            // An indexed one shows its index, the components of the tuple
            // (docs/inductives/codata-indexed-design.md §2).
            let idx = if ind.co_index.is_empty() {
                String::new()
            } else {
                let mut parts = Vec::new();
                let mut cur = Rc::clone(index);
                for _ in 1..ind.co_index.len() {
                    match crate::spelling::pair_of(&cur) {
                        Some((fst, snd)) => {
                            parts.push(self.tm(fst, d + 1));
                            cur = Rc::clone(snd);
                        }
                        None => break,
                    }
                }
                parts.push(self.tm(&cur, d + 1));
                format!("({})", parts.join(", "))
            };
            if ind.params.is_empty() && ind.valparams.is_empty() {
                return format!("{}{idx}", ind.name);
            }
            if self.annotations {
                return self.raw_ty(ty);
            }
            let shape = sig.shape_at(index);
            // A named signature carries its arguments: `El(D#mshape ā j)`
            // (docs/inductives/codata-named-signature-design.md §2), type arguments as
            // codes and value arguments as written.
            if let Type::El { tm, .. } = &shape
                && let Some((crate::gendefs::GenDef::MShape(_), args)) = self.el.gen_app_of(tm)
                && args.len() == ind.params.len() + ind.valparams.len() + 1
            {
                let np = ind.params.len();
                let targs = if np == 0 {
                    String::new()
                } else {
                    let shown = args[..np]
                        .iter()
                        .map(|a| self.ty(&Type::El { level: heather_kernel::level::Level::Zero, tm: Rc::clone(a) }, d + 1))
                        .collect::<Vec<_>>();
                    format!("<{}>", shown.join(", "))
                };
                let mut vals: Vec<String> = args[np..args.len() - 1].iter().map(|a| self.tm(a, d + 1)).collect();
                if !idx.is_empty() {
                    vals.push(idx[1..idx.len() - 1].to_string());
                }
                let vargs = if vals.is_empty() { String::new() } else { format!("({})", vals.join(", ")) };
                return format!("{}{targs}{vargs}", ind.name);
            }
            let targs = if ind.params.is_empty() {
                String::new()
            } else if let Some(args) = Inductives(self.el).display_targs(&self.here(), &shape, &ind) {
                let shown = args.iter().map(|(arg, _)| self.ty(arg, d + 1)).collect::<Vec<_>>().join(", ");
                format!("<{shown}>")
            } else {
                "<…>".to_string()
            };
            let vargs = if ind.valparams.is_empty() { "" } else { "(…)" };
            let shown = format!("{}{targs}{vargs}{idx}", ind.name);
            return if targs == "<…>" || !vargs.is_empty() { self.elided(shown) } else { shown };
        }
        // An `IWf`-route family at an index (docs/kernel/iwf-former-design.md §8):
        // `D<ā>(e)`, or for a mutual group's family the member the index
        // selects, `Tm(e)` (docs/inductives/mutual-inductive-design.md §2).
        if let Type::IWf { sig, index } = ty
            && let Some((ind, _)) = IwfFamily(self.el).iwf_of(ty)
        {
            return self.iwf_instance(&ind, &sig.shape, index, d);
        }
        // …and its `W` encoding, for a family with a function field
        // (docs/kernel/iwf-infinitary-design.md §5).
        if matches!(ty, Type::Sigma { .. })
            && let Some((ind, fam)) = IwfFamily(self.el).iwf_of(ty)
        {
            return self.iwf_instance(&ind, fam.shape().0, &fam.idx, d);
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
                let Some(args) = GeneratedDefs(self.el).instance_args(self.cx, &ind, ty) else {
                    return self.raw_ty(ty);
                };
                return self.source_instance(&ind, &args, d).unwrap_or_else(|| self.raw_ty(ty));
            }
            // A value parameter is often the whole difference between two
            // instances — `BitVec(8)` against `BitVec(16)` — so a diagnostic
            // that drops it reads as a contradiction
            // (issues/width-specific-method-on-other-width.md). The checked
            // instance matcher recovers it; a type that does not match keeps
            // the bare name below, as before.
            //
            // The source flavour (omega's and ring's atoms, which are
            // re-elaborated) needs it more: a bare `BitVec` there is not a
            // display slip but an atom list that does not elaborate — a
            // lambda's binder, `λ (x: BitVec(8)) => …`
            // (issues/omega-atom-lambda-binder-type-spelled-bare.md). It
            // spells the type arguments too, and declines (counts a
            // fallback) where it cannot recover either.
            if !ind.valparams.is_empty() && self.qualified {
                return match GeneratedDefs(self.el).display_args(self.cx, &ind, ty, self.binders()) {
                    Some(args) => self.source_instance(&ind, &args, d).unwrap_or_else(|| self.raw_ty(ty)),
                    None => self.elided(ind.name.clone()),
                };
            }
            if !ind.valparams.is_empty()
                && let Some(values) = GeneratedDefs(self.el).display_vargs(self.cx, &ind, ty, self.binders())
            {
                if ind.params.is_empty() && let Some(name) = self.named(ind.tag, &values, d) {
                    return name;
                }
                let values = values
                    .iter()
                    .map(|t| self.tm(t, d + 1))
                    .collect::<Vec<_>>()
                    .join(", ");
                let head = if ind.params.is_empty() {
                    ind.name.clone()
                } else {
                    self.elided(format!("{}<…>", ind.name))
                };
                return format!("{head}({values})");
            }
            return if ind.params.is_empty() {
                let named = if ind.valparams.is_empty() { self.named(ind.tag, &[], d) } else { None };
                named.unwrap_or_else(|| ind.name.clone())
            } else if let Some(args) =
                Inductives(self.el).display_targs(&self.here(), ty, &ind)
            {
                let shown = args
                    .iter()
                    .map(|(arg, _)| self.ty(arg, d + 1))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{shown}>", ind.name)
            } else {
                self.elided(format!("{}<…>", ind.name))
            };
        }
        match ty {
            Type::Nat => "Nat".to_string(),
            Type::Unit { .. } => "True".to_string(),
            Type::Empty { .. } => "False".to_string(),
            Type::Ty(l) => format!("Type<{}>", show_level(l)),
            Type::El { tm, .. } => self.nullary_call(tm).unwrap_or_else(|| self.tm(tm, d)),
            Type::Id { lhs, rhs, .. } => {
                let side = |t: &Term| self.operand_at(t, d, Form::comparand);
                format!("{} = {}", side(lhs), side(rhs))
            }
            // No surface form exists for strict equality; the glyph is
            // display-only and deliberately not `=`.
            Type::SEq { lhs, rhs, .. } => {
                let side = |t: &Term| self.operand_at(t, d, Form::comparand);
                format!("{} ≡ {}", side(lhs), side(rhs))
            }
            Type::Squash { ty, .. } => format!("∥{}∥", self.ty(ty, d + 1)),
            Type::Vec { elem, len, .. } => {
                format!("[{}; {}]", self.ty(elem, d + 1), self.tm(len, d))
            }
            Type::Fin { len } => format!("Fin({})", self.tm(len, d)),
            Type::Pi { dom, dom_level, cod, .. } => {
                // `->` associates to the right: a function domain is
                // parenthesized, or `(A -> B) -> C` would read as `A -> B -> C`.
                let dom_s = match &**dom {
                    Type::Pi { .. } => format!("({})", self.ty(dom, d + 1)),
                    _ => self.ty(dom, d + 1),
                };
                if self.dependent(cod, d) {
                    let name = self.fresh();
                    let cod_s = self.under(&name, dom, dom_level, cod, d);
                    format!("({name}: {dom_s}) -> {cod_s}")
                } else {
                    // The binder is unused, so any name resolves nothing; push
                    // one anyway to keep the index arithmetic honest.
                    let cod_s = self.under("_", dom, dom_level, cod, d);
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
        if let Some(placeholders) = self.rough
            && let Term::GlobalTm { var, .. } = t
            && let Some((_, name)) = placeholders.iter().find(|(v, _)| v == var)
        { return name.clone(); }
        if self.annotations
            && let Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(t)
            && let Some(ind) = self.el.types.by_tag(tag)
            && let Some(source) = self.source_instance(&ind, &args, d)
        { return source; }
        // A code of an instance the program named: `List<u8>`'s argument.
        if let Some((GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(t)
            && let Some(name) = self.named(tag, &args, d)
        { return name; }
        if let Term::GlobalTm { var, .. } = t
            && let Some(GenDef::TyCode(tag)) = self.el.gen_def_of(*var)
            && let Some(name) = self.named(tag, &[], d)
        { return name; }
        // A type constructor applied to only some of its type arguments, as
        // a kinded carrier is — `Bind<Pair2<Bool, ·>>` — shows the arguments
        // it fixes and a hole for each it leaves; the call spelling below
        // drops type arguments, which leaves the bare name `Pair2`
        // (issues/applied-meta-approximation-diagnostics.md). For a reader
        // only: `·` re-parses as a section.
        if !self.qualified
            && !self.annotations
            && let Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(t)
            && let Some(ind) = self.el.types.by_tag(tag)
            && args.len() < ind.params.len()
        {
            let mut shown: Vec<String> = args
                .iter()
                .map(|a| self.ty(&Type::El { level: crate::Level::Zero, tm: Rc::clone(a) }, d + 1))
                .collect();
            shown.extend((args.len()..ind.params.len()).map(|_| "·".to_string()));
            return format!("{}<{}>", ind.name, shown.join(", "));
        }
        // A fully applied type constructor as a code (a predicate's body,
        // `λ x => P(x) ∨ Q(x)`): the type it decodes to.
        if !self.annotations
            && let Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) = self.el.gen_app_of(t)
            && let Some(ind) = self.el.types.by_tag(tag)
            && args.len() == ind.params.len() + ind.valparams.len()
        {
            let decoded = Type::El { level: crate::Level::Zero, tm: Rc::new(t.clone()) };
            if self.el.unspell_here(&decoded).is_some() {
                return self.ty(&decoded, d + 1);
            }
        }
        // `3`, not `S(S(S(0)))`.
        if let Some(k) = crate::inductive::nat_numeral(t) {
            return k.to_string();
        }
        // `2` at `Int`, not `OfNat(2)`; `0` at `Rat`, not `ofInt(OfNat(0))`.
        if let Some(k) = self.carrier_numeral(t) {
            return k;
        }
        // `'h'`, not `ofNat(104, decide_yes(refl))`.
        if let Some(c) = self.char_literal(t) {
            let mut out = String::from("'");
            escape_into(c, '\'', &mut out);
            out.push('\'');
            return out;
        }
        // A `match` on an enumeration, and the convoy `match h:` and
        // `if h:` lower to, as the reader wrote it: a lowered `decreases`
        // body's test, read back in a goal or an unfolding equation, is not
        // `app@(case[0,0,0](M Π…`.
        // A case on an injection, as its contractum: the instance of a
        // motive at an arm is the goal with the arm's constructor where the
        // scrutinee stood, and the arm proves what that reduces to.
        if !self.qualified
            && !self.annotations
            && let Some(r) = crate::spelling::iota_case(t)
        {
            return self.tm(&crate::spelling::contract_projections(&Rc::new(r)), d + 1);
        }
        if self.rough.is_none() && !self.qualified {
            if let Some(shown) = self.convoy(t, d) {
                return shown;
            }
            if let Term::Case { .. } = t
                && let Some(shown) = self.enum_match(t, None, d)
            {
                return shown;
            }
        }
        match t {
            // A codata instance's code, `λ a b => Eutt<R>(E, a, b)`'s body:
            // the instance it decodes to.
            Term::TmM { .. } => self.ty(&Type::El { level: heather_kernel::level::Level::Zero, tm: Rc::new(t.clone()) }, d + 1),
            Term::Var(LocalVar(i)) => self.var(*i).unwrap_or_else(|| self.raw_tm(t)),
            Term::Succ(p) => format!("Succ({})", self.tm(p, d + 1)),
            Term::Refl { .. } => "refl".to_string(),
            Term::Triv { .. } => "trivial".to_string(),
            Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => self
                .ctor_value(t, d)
                .unwrap_or_else(|| format!("({}, {})", self.tm(fst, d + 1), self.tm(snd, d + 1))),
            Term::Lam { dom, dom_level, body, .. } => {
                let dom_s = self.ty(dom, d + 1);
                let name = self.fresh();
                self.enter(name.as_str(), dom, dom_level);
                let body_s = self.tm(body, d + 1);
                self.leave();
                format!("λ ({name}: {dom_s}) => {body_s}")
            }
            // A code and the type it encodes are written identically, so a
            // code former delegates rather than repeating the table.
            Term::TmNat => "Nat".to_string(),
            // A function type as a code: the unfolding of a type function,
            // `Nat → List<Nat> → Nat`'s codomain
            // (issues/type-function-argument-mismatch-only-kernel-refuses.md).
            Term::TmPi { .. } => {
                let decoded = crate::inductive::decoded(&Type::El { level: crate::Level::Zero, tm: Rc::new(t.clone()) }).into_owned();
                if matches!(decoded, Type::Pi { .. }) { self.ty(&decoded, d + 1) } else { self.raw_tm(t) }
            }
            Term::TmUnit { .. } => "True".to_string(),
            Term::TmEmpty { .. } => "False".to_string(),
            Term::TmTy(level) => format!("Type<{}>", show_level(level)),
            Term::TmId { ty, lhs, rhs, .. } => {
                let _ = ty;
                let side = |t: &Term| self.operand(t, d, Form::comparand);
                format!("{} = {}", side(lhs), side(rhs))
            }
            Term::TmVec { elem, len, .. } => {
                format!("[{}; {}]", self.tm(elem, d + 1), self.tm(len, d + 1))
            }
            Term::TmFin { len } => format!("Fin({})", self.tm(len, d + 1)),
            Term::TmSquash { ty, .. } => format!("∥{}∥", self.tm(ty, d + 1)),
            Term::Squash { tm, .. } => format!("squash({})", self.tm(tm, d + 1)),
            Term::Supf { .. }
            | Term::Supi { .. }
            | Term::Inl { .. }
            | Term::Inr { .. }
            | Term::InlAt { .. }
            | Term::InrAt { .. } => self.ctor_value(t, d).unwrap_or_else(|| self.raw_tm(t)),
            Term::App { .. } | Term::AppAt { .. } => self.call(t, d),
            Term::Fst { .. } | Term::FstAt { .. } => self
                .alias(t)
                .or_else(|| self.field_read(t, d))
                .or_else(|| self.value_field_read(t, d))
                .or_else(|| self.projection_reduct(t, d))
                .unwrap_or_else(|| self.raw_tm(t)),
            // A match the walk cannot name the constructors of, shown to a
            // reader by what it matches on.
            Term::Case { scrut, .. } if self.rough.is_some() => format!("match {} {{ … }}", self.tm(scrut, d + 1)),
            Term::GlobalTm { var, subst } => self
                .global(*var, subst)
                .map(|(n, _)| n)
                .or_else(|| self.goal_slot(*var))
                .unwrap_or_else(|| self.raw_tm(t)),
            _ => self.raw_tm(t),
        }
    }

    /// A defaulted parameter's argument, as a reader sees it: spelled when
    /// it spells, `…` when it does not. What fills a defaulted proof is
    /// usually a search's certificate (`omega`'s, inline in the term), whose
    /// raw form would spend the whole fallback budget and turn the statement
    /// around it into the kernel wall. The spelling for re-parsing keeps the
    /// ordinary rule, since `…` does not re-parse.
    fn defaulted_argument(&self, a: &Term, d: u32) -> String {
        if self.qualified || self.rough.is_some() {
            return self.tm(a, d);
        }
        let (nodes, fallbacks) = (self.nodes.get(), self.fallbacks.get());
        let spelled = self.tm(a, d);
        if self.fallbacks.get() == fallbacks {
            return spelled;
        }
        self.nodes.set(nodes);
        self.fallbacks.set(fallbacks);
        "…".to_string()
    }

    /// A reference to a slot of the declaration's goal world, spelled for a
    /// reader by what fills it: a lifted `bv_omega` proof as `bv_omega`, the
    /// search the source wrote, and a goal as `?name`. A statement that
    /// mentions a search (`f(x, inside := bv_omega)`) otherwise shows the
    /// slot's kernel reference `u3^{·; x1; x0}`
    /// (issues/goal-hole-beside-a-search-in-the-statement.md). Not when the
    /// spelling is re-parsed: there `bv_omega` would search again and `?g`
    /// would raise a goal, so the slot declines like any unspellable node.
    fn goal_slot(&self, var: GlobalVar) -> Option<String> {
        if self.qualified {
            return None;
        }
        let abs = self.el.global_abs_of(var)?;
        let slot = abs.checked_sub(self.el.psi().bindings.len())?;
        self.el.attempt.goal_arena.slot_spelling(slot)
    }

    /// `match h: e { … }`: a case analysis whose motive is `Π(e = z). M`,
    /// applied to `refl` — what `match h:` and `if h:` lower to
    /// (docs/language/matching/dependent-match-compiler-design.md §4). Each arm is a `λ` over
    /// the equation, which takes the name `h` (or a fresh one) in the arm.
    fn convoy(&self, t: &Term, d: u32) -> Option<String> {
        let (case, arg) = crate::spelling::app_of(t)?;
        let Term::Refl { .. } = &**arg else { return None };
        let Term::Case { motive, scrut, .. } = &**case else { return None };
        let Type::Pi { dom, .. } = &**motive else { return None };
        let Type::Id { lhs, rhs, .. } = &**dom else { return None };
        // Under the motive's binder: `e` weakened past it, and `z` itself.
        if !matches!(&**rhs, Term::Var(LocalVar(0))) || **lhs != scrut.shift_local(1) {
            return None;
        }
        let name = self.fresh_from(&["h", "e", "same"]);
        self.enum_match(case, Some(&name), d)
    }

    /// `match e { C₀ => a₀, … }` for a case analysis over an enumeration,
    /// a tier-0 inductive whose constructors carry nothing: `Bool`, read as
    /// `if e { … } else { … }`, or a chain of cases, one per constructor
    /// but the last, each on the one before's right summand. With `eq`,
    /// each arm is a `λ` over the convoy's equation, bound under that name.
    /// `None` for anything else, which falls back to the raw spelling.
    fn enum_match(&self, t: &Term, eq: Option<&str>, d: u32) -> Option<String> {
        let Term::Case { lhs, scrut, .. } = t else { return None };
        let ind = self.el.display_tag_of(lhs)?;
        let n = ind.ctors.len();
        if n < 2 || ind.ctors.iter().any(|c| c.fields.len() != 0) {
            return None;
        }
        // A convoy over more than two constructors would chain its
        // equation through the inner cases' motives; not read here.
        if eq.is_some() && n != 2 {
            return None;
        }
        let mut arms: Vec<String> = Vec::with_capacity(n);
        let mut entered = 0;
        let mut cur = t;
        let shown = (|| {
            for k in 0..n - 1 {
                let Term::Case { lhs, rhs, lhs_level, rhs_level, case_l, case_r, scrut: s, .. } = cur else {
                    return None;
                };
                if k > 0 && !matches!(&**s, Term::Var(LocalVar(0))) {
                    return None;
                }
                arms.push(self.enum_arm(lhs, lhs_level, case_l, eq, d)?);
                if k + 2 == n {
                    arms.push(self.enum_arm(rhs, rhs_level, case_r, eq, d)?);
                } else {
                    // The rest of the constructors, under the right
                    // summand's binder, which nothing in an arm reads.
                    let name = self.fresh();
                    self.enter(&name, rhs, rhs_level);
                    entered += 1;
                    cur = case_r;
                }
            }
            Some(())
        })();
        for _ in 0..entered {
            self.leave();
        }
        shown?;
        let scrut_s = self.tm(scrut, d + 1);
        let head = match eq {
            Some(h) => format!("{h}: {scrut_s}"),
            None => scrut_s,
        };
        if self.standard(&ind, "bool", "Bool") {
            // `inductive Bool { False, True }`: the right arm is `True`'s.
            return Some(format!("if {head} {{ {} }} else {{ {} }}", arms[1], arms[0]));
        }
        let shown: Vec<String> =
            ind.ctors.iter().zip(&arms).map(|(c, a)| format!("{} => {a}", c.name)).collect();
        Some(format!("match {head} {{ {} }}", shown.join(", ")))
    }

    /// One arm of [`Self::enum_match`]: `body` under the summand's binder
    /// (the constructor's empty payload, which it does not read), and under
    /// the equation's `λ` when there is one.
    fn enum_arm(&self, summand: &Type, level: &crate::Level, body: &Term, eq: Option<&str>, d: u32) -> Option<String> {
        let payload = self.fresh();
        self.enter(&payload, summand, level);
        let shown = match (eq, body) {
            (None, body) => Some(self.tm(body, d + 1)),
            (Some(h), Term::Lam { dom, dom_level, body, .. }) => {
                self.enter(h, dom, dom_level);
                let s = self.tm(body, d + 1);
                self.leave();
                Some(s)
            }
            (Some(_), _) => None,
        };
        self.leave();
        shown
    }

    /// [`Self::fresh`] with the caller's own preferences first.
    fn fresh_from(&self, preferred: &[&str]) -> String {
        {
            let names = self.names.borrow();
            let used = |candidate: &str| names.contains(candidate)
                || self.cx.aliases.iter_inner().any(|a| a.name == candidate);
            if let Some(c) = preferred.iter().find(|c| !used(c)) {
                return c.to_string();
            }
        }
        self.fresh()
    }

    /// A nullary `fn` in a type position, spelled as its call, `Inner()`:
    /// the bare name is not a type there, and does not re-read as one
    /// (issues/type-function-argument-mismatch-only-kernel-refuses.md). A
    /// `def` is used by its bare name, so it keeps the ordinary spelling, as
    /// does anything that is not a declared `fn`.
    fn nullary_call(&self, t: &Term) -> Option<String> {
        let Term::GlobalTm { var, subst } = t else { return None };
        if self.rough.is_some() || self.el.gen_def_of(*var).is_some() {
            return None;
        }
        let (name, _) = self.global(*var, subst)?;
        let abs = self.el.global_abs_of(*var)?;
        if !NameLookup(self.el).params_at(abs).is_empty() {
            return None;
        }
        let key = self.el.names.global_name_at(abs as u32)?;
        let (module, base) = crate::names::split_qual(key)?;
        let decl = self.el.names.surface_decl_in(module, base)?;
        (matches!(decl.kind, heather_syntax::DeclKind::Fn) && !decl.value && decl.params.is_empty())
            .then(|| format!("{name}()"))
    }

    /// `D<ā>(e)` for an `IWf`-route family, the type arguments read off the
    /// shape (the family's shape declaration is an ordinary unindexed one),
    /// and a mutual group's family as the member its index selects.
    fn iwf_instance(
        &self,
        ind: &crate::inductive::Inductive,
        shape: &Type,
        index: &Term,
        d: u32,
    ) -> String {
        let targs = if ind.params.is_empty() {
            String::new()
        } else {
            match ind.skel.as_ref().and_then(|skel| {
                Inductives(self.el).display_targs(&self.here(), shape, skel)
            }) {
                Some(args) => {
                    let shown = args.iter().map(|(arg, _)| self.ty(arg, d + 1)).collect::<Vec<_>>();
                    format!("<{}>", shown.join(", "))
                }
                None => self.elided("<…>".to_string()),
            }
        };
        if ind.members.is_empty() {
            return format!("{}{targs}({})", ind.name, self.tm(index, d + 1));
        }
        let Some(crate::inductive::IdxTy::Decl(mi)) = &ind.index_ty else {
            return self.raw_tm(index);
        };
        let (k, payload) = self.inj_path(index, mi.ctors.len());
        let Some(member) = ind.members.get(k) else {
            return self.raw_tm(index);
        };
        if member.index.is_none() {
            return format!("{}{targs}", member.name);
        }
        match crate::spelling::tuple_fields(self.el, self.cx, payload, 1, 1, self.binders()) {
            Some(fields) => format!("{}{targs}({})", member.name, self.tm(&fields[0], d + 1)),
            None => self.elided(format!("{}{targs}(…)", member.name)),
        }
    }

    /// Walk a tier-0 value's injection path over `n` constructors
    /// ([`crate::spelling::inj_path`]): the constructor's number and its
    /// payload tuple.
    fn inj_path<'t>(&self, label: &'t Term, n: usize) -> (usize, &'t Term) {
        let path = crate::spelling::inj_path(label, n);
        (path.ctor, path.at)
    }

    /// A lowered constructor value as `C(f₁, …)` — the shape a `match` arm's
    /// motive is instantiated at, so it is what a goal statement inside an arm
    /// shows. This is the *canonical* half of
    /// [`Elaborator::read_ctor`](Inductives::read_ctor): an injection
    /// path over a `Pair`, whose payload fields sit in the label's Σ spine and
    /// whose plain children sit in the tuple. Deliberately not a call to that
    /// method — it takes a constructor spine, can elaborate projections, and
    /// can fail, none of which a display path may do. Anything that does not
    /// line up exactly declines, so the worst case is the raw form.
    fn ctor_value(&self, t: &Term, d: u32) -> Option<String> {
        let (ind, i, fields) = self.ctor_fields(t)?;
        let ctor = &ind.ctors[i];
        let Some(fields) = fields else {
            return Some(self.elided(format!("{}(…)", ctor.name)));
        };
        if let Some(literal) = self.literal_value(t, &ind, &fields, d) {
            return Some(literal);
        }
        let shown: Vec<String> = fields.iter().map(|v| self.tm(v, d + 1)).collect();
        let head = format!("{}{}", ctor.name, self.ctor_targs(t, &ind, i, d));
        Some(if shown.is_empty() {
            head
        } else {
            format!("{head}({})", shown.join(", "))
        })
    }

    /// The `<…>` a re-parsed constructor value needs: its declaration's type
    /// arguments, written only in the source flavour and only when one of
    /// them is mentioned by none of the constructor's fields, so elaborating
    /// the arguments could not infer it. `Nil` alone came back as
    /// `List::len(Nil)` in `omega`'s certificate and did not elaborate
    /// (issues/omega-certificate-drops-type-arguments.md); `Cons(x, xs)`
    /// infers and keeps its spelling. Empty when the arguments do not
    /// recover from the value's type, which leaves the spelling as it was.
    fn ctor_targs(&self, t: &Term, ind: &crate::inductive::Inductive, i: usize, d: u32) -> String {
        if !self.qualified || ind.params.is_empty() {
            return String::new();
        }
        let ctor = &ind.ctors[i];
        let undetermined = ind.params.iter().any(|p| {
            !ctor.fields.iter().any(|(_, ty)| crate::inductive::occurs(ty, p).is_some())
        });
        if !undetermined {
            return String::new();
        }
        let ty: &Type = match t {
            Term::Supf { shape, .. } => shape,
            Term::InlAt { ty: Some(ty), .. } | Term::InrAt { ty: Some(ty), .. } => ty,
            Term::PairAt { ty: Some(ty), .. } => ty,
            _ => return String::new(),
        };
        // Under a binder the walk has entered, `self.cx` does not scope the
        // arguments, and the complete spelling below needs it to.
        if self.binders() != 0 {
            return String::new();
        }
        let Some(args) = Inductives(self.el).display_targs(self.cx, ty, ind) else {
            return String::new();
        };
        // The generated-annotation flavour: an argument at a type with value
        // parameters must keep them (`Nil<BitVec(8)>`, not `Nil<BitVec>`),
        // and an argument that does not spell completely leaves the bare name.
        let mut shown = Vec::with_capacity(args.len());
        for (arg, _) in &args {
            if !self.charge(d + 1) {
                return String::new();
            }
            let Some(one) = self.el.spell_type_source(self.cx, arg) else {
                return String::new();
            };
            shown.push(one);
        }
        format!("<{}>", shown.join(", "))
    }

    /// A lowered constructor value read back: its declaration, the
    /// constructor's number, and its fields in declaration order — `None`
    /// for the fields when the payload tuple does not read. The reading half
    /// of [`Self::ctor_value`], which [`Self::literal_value`] also walks a
    /// list's spine with.
    fn ctor_fields(&self, t: &Term) -> Option<(Rc<crate::inductive::Inductive>, usize, Option<Vec<Rc<Term>>>)> {
        let (label, children, ind) = match t {
            Term::Supf {
                shape,
                label,
                children,
                ..
            } => (&**label, Some(&**children), self.el.display_tag_of(shape)?),
            // An `IWf`-route family's value: the label is the shape
            // declaration's injection, whose constructors are the family's
            // in order, and the children are the `DVec` tuple.
            Term::Supi { sig, label, children } => {
                let skel = self.el.tag_of(&sig.shape)?;
                let fam = Rc::clone(self.el.types.iwf_by_shape(skel.tag)?);
                (&**label, Some(&**children), fam)
            }
            // Tier 0: the value *is* the injection, and either summand type
            // carries the nominal tag — behind a spine-code reference for a
            // flat declaration, which the display lookup sees through.
            Term::Inl { lhs, .. } => (t, None, self.el.display_tag_of(lhs)?),
            Term::Inr { rhs, .. } => (t, None, self.el.display_tag_of(rhs)?),
            // The checked spellings carry the **whole sum**, not a summand,
            // and `tag_of` already walks a `Sum` to its leftmost constructor
            // — so the same lookup serves, one node higher
            // (`docs/elaborator/intro-by-type-design.md` §4.2). An annotation that is
            // not structurally a sum (an un-reduced `El(case(…))`) declines,
            // and the display falls back to `raw_tm` as it does for every
            // other shape it cannot read; a whnf here would need a span the
            // display path does not carry. Only the outermost injection of a
            // chain carries one, which is the one this reads.
            Term::InlAt { ty, .. } | Term::InrAt { ty, .. } => {
                (t, None, self.el.display_tag_of(ty.as_deref()?)?)
            }
            // A record value is its one constructor's payload tuple itself —
            // no injection, the tag at entry 0 — and the checked pair carries
            // the record's type. Only a record: a payload tuple inside another
            // inductive's value is not one.
            Term::PairAt { ty: Some(ty), .. } => match self.el.display_tag_of(ty) {
                Some(ind) if ind.is_record => (t, None, ind),
                _ => return None,
            },
            _ => return None,
        };
        // Walk the injection path: `Inr` steps past a constructor, `Inl`
        // selects one.
        let (i, cur) = self.inj_path(label, ind.ctors.len());
        let fields = self.ctor_tuple(&ind, i, cur, children)?;
        Some((ind, i, fields))
    }

    /// [`Self::ctor_fields`]'s tuples, read for constructor `i`.
    fn ctor_tuple(&self, ind: &crate::inductive::Inductive, i: usize, cur: &Term, children: Option<&Term>) -> Option<Option<Vec<Rc<Term>>>> {
        let ctor = ind.ctors.get(i)?;
        // A container field is neither payload nor a plain child, and reading
        // it back means reading a vector: out of scope for a display.
        if ctor.container().is_some() {
            return None;
        }
        let Some(payload) = crate::spelling::tuple_fields(
            self.el, self.cx, cur, 1, ctor.payload().count(), self.binders(),
        ) else {
            return Some(None);
        };
        let kids = match children {
            Some(children) => crate::spelling::tuple_fields(
                self.el, self.cx, children, 0, ctor.arity(), self.binders(),
            )?,
            None if ctor.arity() == 0 => Vec::new(),
            None => return None,
        };
        // Re-interleave into declaration order, which is the order the surface
        // writes the constructor's arguments in.
        let (mut a, mut b) = (0usize, 0usize);
        let mut fields = Vec::with_capacity(ctor.fields.len());
        for k in 0..ctor.fields.len() {
            let v = if ctor.kind[k].is_child() {
                b += 1;
                kids.get(b - 1)?
            } else {
                a += 1;
                payload.get(a - 1)?
            };
            fields.push(Rc::clone(v));
        }
        Some(Some(fields))
    }

    /// A value of one of the library's literal types spelled as the literal
    /// that elaborates to it: `"hi"` for a `string::String` over character
    /// literals, and `[1, 2]` for a standard `list::List` spine. Keyed on the
    /// declarations' identities, as the literals themselves are
    /// (issues/canonical-list-literal-identity.md), so a look-alike
    /// declaration spells as its constructors, and a list whose tail is not
    /// a constructor (`Cons(1, xs)`) stays a call. A list is a bracket only
    /// when the spelling is for reading: `[…]` checks and never infers, so a
    /// re-parsed `[1, 2] = xs` would not come back, and the source flavour
    /// keeps `Cons`. A list longer than the walk's budget ends in `…`.
    fn literal_value(&self, t: &Term, ind: &crate::inductive::Inductive, fields: &[Rc<Term>], d: u32) -> Option<String> {
        if self.standard(ind, "string", "String") {
            let [chars] = fields else { return None };
            let mut out = String::from("\"");
            for item in self.list_items(chars)? {
                if !self.charge(d) {
                    return None;
                }
                escape_into(self.char_literal(&item)?, '"', &mut out);
            }
            out.push('"');
            return Some(out);
        }
        if self.qualified || !self.standard(ind, "list", "List") {
            return None;
        }
        let mut shown = Vec::new();
        for item in self.list_items(t)? {
            if self.nodes.get() == 0 {
                shown.push(self.elided("…".to_string()));
                break;
            }
            shown.push(self.tm(&item, d + 1));
        }
        Some(format!("[{}]", shown.join(", ")))
    }

    /// Is `ind` the declaration `module::name`?
    fn standard(&self, ind: &crate::inductive::Inductive, module: &str, name: &str) -> bool {
        self.el.types.inductive(&crate::names::qkey(module, name)).is_some_and(|it| it.tag == ind.tag)
    }

    /// The elements of a standard list value spelled out to its `Nil`, or
    /// `None` when a cell is anything else.
    fn list_items(&self, t: &Term) -> Option<Vec<Rc<Term>>> {
        let mut items = Vec::new();
        let mut cur = Rc::new(t.clone());
        loop {
            let (ind, i, fields) = self.ctor_fields(&cur)?;
            if !self.standard(&ind, "list", "List") {
                return None;
            }
            match (ind.ctors.get(i)?.name.as_str(), fields?.as_slice()) {
                ("Nil", []) => return Some(items),
                ("Cons", [head, tail]) => {
                    items.push(Rc::clone(head));
                    cur = Rc::clone(tail);
                }
                _ => return None,
            }
        }
    }

    /// The numeral `t` is at a carrier other than `Nat`: exactly when `t` is
    /// what that numeral elaborates to there, the carrier's `Numeral`
    /// embedding at it (docs/language/carrier-directed-numerals-design.md), read
    /// backwards — `OfNat(2)` at `Int`, `ofInt(OfNat(0))` at `Rat`
    /// (issues/diagnostic-numeral-literal-spelling.md). Read off the
    /// instance's own field, never by reducing `t`: a term that only
    /// computes to one (`NegSucc(2)`, `OfNat(1 + 1)`) keeps its spelling,
    /// and so does a carrier no instance embeds numerals into. A negative
    /// numeral needs nothing here: `-3` is the negation of `3`, which the
    /// operator display already writes as the prefix form it is.
    ///
    /// For a reader only, as [`Self::op_form`] is.
    fn carrier_numeral(&self, t: &Term) -> Option<String> {
        if self.qualified || self.annotations {
            return None;
        }
        let (head, _) = crate::spelling::app_spine(t);
        if matches!(head, Term::Var(_) | Term::Zero | Term::Succ(_) | Term::NatLit(_) | Term::Lam { .. }) {
            return None;
        }
        let templates = self.numerals.get_or_init(|| self.el.numeral_templates());
        templates.iter().find_map(|body| {
            let (template_head, _) = crate::spelling::app_spine(body);
            let same_head = match (template_head, head) {
                (Term::GlobalTm { var: a, .. }, Term::GlobalTm { var: b, .. }) => a == b,
                (a, b) => std::mem::discriminant(a) == std::mem::discriminant(b),
            };
            if !same_head {
                return None;
            }
            // The body at a hole no term contains, in `t`'s scope: the
            // literal's position is then where the two first differ, and
            // the whole term must be the body at that literal. (Far out of
            // any scope, yet with room to be weakened under a binder.)
            let scope = self.names.borrow().len() as u32;
            let hole = Term::Var(LocalVar(u32::MAX / 2));
            let (_, literal) = crate::lgg::first_difference(&body.inst_top(scope, &hole), t)?.at?;
            let k = crate::inductive::nat_numeral(&literal)?;
            (body.inst_top(scope, &literal) == *t).then(|| k.to_string())
        })
    }

    /// The character a `char::ofNat(code, bool::decide_yes(…))` call
    /// builds — exactly the term a character literal elaborates to
    /// (`literals.rs`). The proof must be that one: a `Char` carries its
    /// `scalar` proof relevantly, so an `ofNat` at some other proof is not
    /// the literal and spells as the call it is.
    fn char_literal(&self, t: &Term) -> Option<char> {
        let args = self.call_of(t, "char::ofNat")?;
        let [code, proof] = args.as_slice() else { return None };
        self.call_of(proof, "bool::decide_yes")?;
        let code = crate::inductive::nat_numeral(code)?.as_u64()?;
        char::from_u32(u32::try_from(code).ok()?)
    }

    /// `t`'s arguments when it is a call of the declaration `key`.
    fn call_of<'t>(&self, t: &'t Term, key: &str) -> Option<Vec<&'t Rc<Term>>> {
        let (head, args) = crate::spelling::app_spine(t);
        let Term::GlobalTm { var, subst } = head else { return None };
        let abs = self.el.global_abs_of(*var)?;
        (subst.terms.is_empty() && NameLookup(self.el).global_qualified_name_at(abs)? == key).then_some(args)
    }

    /// `r.name` for a field read a record's declaration left inline. A closed
    /// record whose spine is not dependent registers no projection
    /// definitions (`register_rec_projs` in `gendefs.rs`: they would be all
    /// cost), so `s.words` elaborates to the walk itself, `fst(snd(snd(s)))`
    /// — entry 0 of the spine is the tag, field `j` is entry `j + 1`
    /// ([`Elaborator::project_field`]). Without this the speller met that
    /// walk as raw nodes, and `omega` could not name `s.words` as an atom
    /// (issues/omega-record-projection-atoms.md).
    ///
    /// The receiver's type decides it: read off the receiver's spine
    /// ([`AppUnify::spine_type`]) when its head is a variable, a global or
    /// another field read — the receivers a written `.name` leaves — and only
    /// at the context's own scope, since a binder the walk descended under has
    /// no type in `cx.gamma`. Re-elaborating the spelling walks the same
    /// spine, so it comes back to `t`.
    fn field_read(&self, t: &Term, d: u32) -> Option<String> {
        // Under binders the walk crossed, the receiver is typed where the
        // walk stands: a field read in a `match` arm, `s.hash` in an `if h:`
        // branch of a lowered `decreases` body. For a reader only: a source
        // spelling under a binder keeps declining, as it always has.
        if self.binders() != 0 && self.qualified {
            return None;
        }
        let (pair, name) = self.el.field_read_parts(&self.here(), t)?;
        let shown = self.tm(pair, d + 1);
        Some(if (matches!(&**pair, Term::Var(_) | Term::App { .. } | Term::AppAt { .. })
            || crate::spelling::proj_of(pair).is_some())
            && self.form(pair).bare_receiver()
        {
            format!("{shown}.{name}")
        } else {
            format!("({shown}).{name}")
        })
    }

    /// A field read off a constructed record value
    /// (issues/decreases-measure-record-field-unspelled.md): a `decreases`
    /// measure `s.m` at the self-call `f(CdState(s.m - 1, …))` is
    /// `fst(snd(pair(…)))`, whose receiver is no variable [`Self::field_read`]
    /// can type, and whose weak head unfolds the field's value (`s.m - 1`)
    /// on into `sub`'s eliminator. For reading it is the read as written,
    /// `CdState(s.m - 1, …).m`; for a source spelling it is the field's value
    /// itself — the component projected by syntax, which re-elaborates to a
    /// term the read converts to by Σ-β alone. A component that does not
    /// spell leaves the attempt to the routes after this one.
    fn value_field_read(&self, t: &Term, d: u32) -> Option<String> {
        let field = crate::spelling::project_value(t)?;
        if self.qualified {
            let before = self.fallbacks.get();
            let shown = self.tm(field, d + 1);
            if self.fallbacks.get() == before {
                return Some(shown);
            }
            self.fallbacks.set(before);
            return None;
        }
        let mut receiver = t;
        while let Some((_, pair)) = crate::spelling::proj_of(receiver) {
            receiver = pair;
        }
        let (ind, _, Some(fields)) = self.ctor_fields(receiver)? else {
            return None;
        };
        if !ind.is_record {
            return None;
        }
        let k = fields.iter().position(|v| Rc::ptr_eq(v, field) || **v == **field)?;
        let (Some(name), _) = ind.ctors[0].fields.get(k)? else {
            return None;
        };
        Some(format!("{}.{name}", self.ctor_value(receiver, d + 1)?))
    }

    /// A projection nothing above names, spelled as its bounded weak head —
    /// for a *source* spelling only. A field read off a constructor value, or
    /// off a `match` on one, has no written form the walk can recover
    /// (`WcState(0, 0, 0, False).inside` after a `let` inlined it, `(match
    /// True { … }).words` in a motive's instance), but its reduct is a value
    /// or a neutral that spells. A source caller re-elaborates what it gets
    /// and checks it by conversion, which redoes the reduction; a diagnostic
    /// shows the term it holds, so it does not ask. A projection out of a
    /// neutral is its own weak head and still falls back.
    fn projection_reduct(&self, t: &Term, d: u32) -> Option<String> {
        if !self.qualified || self.binders() != 0 {
            return None;
        }
        let reduct = self.el.goal_oracle().whnf_term_bounded(&self.cx.gamma, t).ok()?;
        (reduct != *t).then(|| self.tm(&reduct, d + 1))
    }

    /// An `App` spine as a call. The head's *implicit* parameters are dropped,
    /// so `len<A>(xs)`'s two-argument spine prints as `len(xs)` — what the
    /// caller wrote.
    /// The recogniser behind a call's spelling, shared with the tactic
    /// host's `View` (`host.rs`): `t`'s application spine as a head and its
    /// arguments, or `None` when the head is neither a named global nor a
    /// local. A record projection's head is the field and its one argument
    /// the receiver, the instantiation before it dropped.
    pub(crate) fn call_parts<'t>(&self, t: &'t Term) -> Option<(CallHead, Vec<&'t Rc<Term>>)> {
        let mut args: Vec<&Rc<Term>> = Vec::new();
        let mut head = t;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(arg);
            head = fun;
        }
        args.reverse();

        // Record projections have a nominal generated-definition key. The
        // spine is the declaration's telescope and then the receiver
        // (`docs/inductives/per-instantiation-type-codes-design.md` §13), so the
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
            return Some((CallHead::Field(name.clone()), vec![receiver]));
        }

        match head {
            Term::GlobalTm { var, subst } => {
                let (name, shown) = self.global(*var, subst)?;
                Some((CallHead::Global(name, shown), args))
            }
            Term::Var(LocalVar(i)) => Some((CallHead::Local(*i), args)),
            _ => None,
        }
    }

    /// A function-valued record field applied, `nb.number(a)`
    /// (issues/omega-applied-field-atom.md): the field read spelled as
    /// [`Self::field_read`] or a projection call spells it, then its
    /// arguments. Only when each argument meets an explicit arrow of the
    /// field's declared type, so the spelling re-elaborates to the same
    /// spine; an implicit binder, or a type the declaration names through an
    /// alias, declines (the call then spells as before).
    fn applied_field(&self, t: &Term, d: u32) -> Option<String> {
        let (inner, _) = crate::spelling::app_spine(t);
        let projection = match inner {
            Term::GlobalTm { var, subst } => {
                subst.terms.is_empty()
                    && matches!(self.el.gen_def_of(*var), Some(crate::gendefs::GenDef::RecProj(..)))
            }
            _ => crate::spelling::proj_of(inner).is_some(),
        };
        if !projection {
            return None;
        }
        let mut args: Vec<&Rc<Term>> = Vec::new();
        let mut head = t;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(arg);
            head = fun;
            let Some((receiver, record, idx)) = self.field_head(head) else {
                continue;
            };
            let mut ty = &record.ctors[0].fields.get(idx)?.1;
            for _ in 0..args.len() {
                let heather_syntax::TyKind::Fn { implicit: false, cod, .. } = &ty.kind else {
                    return None;
                };
                ty = cod;
            }
            let (Some(name), _) = record.ctors[0].fields.get(idx)? else {
                return None;
            };
            let recv = self.tm(receiver, d + 1);
            // A receiver written with type arguments (`sin<A>`) is no
            // postfix operand, so only a bare one goes unparenthesised.
            let bare = (matches!(&**receiver, Term::Var(_) | Term::App { .. } | Term::AppAt { .. })
                || crate::spelling::proj_of(receiver).is_some())
                && self.form(receiver).bare_receiver()
                && !recv.contains('<');
            let shown = if bare { format!("{recv}.{name}") } else { format!("({recv}).{name}") };
            let shown_args = args.iter().rev().map(|a| self.tm(a, d + 1)).collect::<Vec<_>>();
            return Some(format!("{shown}({})", shown_args.join(", ")));
        }
        None
    }

    /// The record and field number a field read `head` names: an inline
    /// projection walk [`Elaborator::field_read_record`] types, or a
    /// projection definition applied to its instantiation and receiver.
    fn field_head<'t>(&self, head: &'t Term) -> Option<(&'t Rc<Term>, Rc<crate::inductive::Inductive>, usize)> {
        if crate::spelling::proj_of(head).is_some() {
            if self.binders() != 0 {
                return None;
            }
            return self.el.field_read_record(self.cx, head);
        }
        let (inner, args) = crate::spelling::app_spine(head);
        if let Term::GlobalTm { var, subst } = inner
            && subst.terms.is_empty()
            && let Some(crate::gendefs::GenDef::RecProj(tag, field)) = self.el.gen_def_of(*var)
            && let Some(record) = self.el.types.by_tag(tag)
            && record.is_record
            && args.len() == record.params.len() + record.valparams.len() + 1
        {
            return Some((args.last()?, Rc::clone(record), field));
        }
        None
    }

    fn call(&self, t: &Term, d: u32) -> String {
        if let Some(op) = self.op_form(t) {
            return self.operator(&op, d);
        }
        if let Some(shown) = self.applied_field(t, d) {
            return shown;
        }
        let (head, args) = match self.call_parts(t) {
            Some(parts) => parts,
            // A β-redex has no surface spelling, and its contractum is the
            // same type to every reader: a let-bound or instantiated λ at the
            // head (`post(u)` with `post := λ u => P(u.memory)`) spells as
            // what it stands for (issues/elab-accepts-mismatch-under-redex-head.md).
            // Only for a reader: a source flavour's caller re-parses what it
            // gets (omega's and ring's atoms, generated annotations), and a
            // declined redex is part of what those routes decide on.
            None => {
                return match crate::spelling::beta_head(t).filter(|_| !self.qualified && !self.annotations) {
                    Some(r) => self.tm(&r, d + 1),
                    None => self.raw_tm(t),
                };
            }
        };
        let (name, implicit) = match head {
            CallHead::Field(name) => {
                let receiver = args[0];
                let shown = self.tm(receiver, d + 1);
                // An arm's binder is a projection of the scrutinee and reads
                // as its name, so it is as bare as a variable.
                return if (matches!(receiver.as_ref(), Term::Var(_) | Term::App { .. } | Term::AppAt { .. })
                    && self.form(receiver).bare_receiver())
                    || self.alias(receiver).is_some()
                {
                    format!("{shown}.{name}")
                } else {
                    format!("({shown}).{name}")
                };
            }
            CallHead::Global(n, imp) => (n, imp),
            CallHead::Local(i) => match self.var(i) {
                Some(n) => (n, Vec::new()),
                None => return self.raw_tm(t),
            },
        };
        // Named arguments follow every positional one, as the parser requires.
        // Type parameters are written `<…>`, all of them once any one is.
        let mut shown: Vec<String> = Vec::new();
        let mut named: Vec<String> = Vec::new();
        let mut types: Vec<String> = Vec::new();
        let written_types = implicit.iter().any(|s| matches!(s, Shown::Type(true)));
        for (i, a) in args.iter().enumerate() {
            match implicit.get(i) {
                Some(Shown::Hidden) => {}
                Some(Shown::Type(_)) => {
                    if written_types {
                        types.push(self.tm(a, d + 1));
                    }
                }
                Some(Shown::Named(name)) => named.push(format!("{name} := {}", self.defaulted_argument(a, d + 1))),
                Some(Shown::Explicit) | None => shown.push(self.tm(a, d + 1)),
            }
        }
        shown.extend(named);
        let name = if types.is_empty() { name } else { format!("{name}<{}>", types.join(", ")) };
        if shown.is_empty() {
            name
        } else {
            format!("{name}({})", shown.join(", "))
        }
    }

    // -- operators ----------------------------------------------------------

    /// The operator `t` is written with, when it is a resolved operation the
    /// program could have written as one here
    /// (issues/diagnostic-operator-resugaring.md). Elaboration resolves `a +
    /// b` to `Nat::add(a, b)`, and the display reads that back only where the
    /// inverse is exact: the designation table, read backwards at the
    /// operand's carrier, names exactly one symbol of the call's arity, and
    /// no constraint binder for that symbol is in scope to take it instead
    /// (rung 1 of the resolver, `dispatch/operator.rs`). Anything else — an
    /// undesignated operation, a partial or over-application, a call with a
    /// named argument the notation cannot carry, two symbols for one
    /// operation — keeps its named call.
    ///
    /// The carrier is the operand's type as the callee declares it, not the
    /// global's name: `RelId(a, b)` is `a ≈ b` at `Nat`, where `≈`
    /// designates it, and a named call at a carrier where nothing does.
    ///
    /// For a reader only. The source flavours' output is re-parsed and fed to
    /// decisions (`omega`'s atoms, generated annotations), and what they emit
    /// stays what it was: nothing elaboration keys on reads this spelling.
    fn op_form<'t>(&self, t: &'t Term) -> Option<OpForm<'t>> {
        if self.qualified || self.annotations {
            return None;
        }
        let (head, args) = self.call_parts(t)?;
        match head {
            CallHead::Global(_, shown) => {
                if shown.len() != args.len() {
                    return None;
                }
                let mut operands = Vec::new();
                let mut first = None;
                for (i, (s, a)) in shown.iter().zip(&args).enumerate() {
                    match s {
                        Shown::Explicit => {
                            first.get_or_insert(i);
                            operands.push(*a);
                        }
                        Shown::Hidden | Shown::Type(false) => {}
                        Shown::Named(_) | Shown::Type(true) => return None,
                    }
                }
                let (spine_head, _) = crate::spelling::app_spine(t);
                let Term::GlobalTm { var, .. } = spine_head else { return None };
                let abs = self.el.global_abs_of(*var)?;
                let op = NameLookup(self.el).global_qualified_name_at(abs)?;
                let carrier = self.operand_carrier(abs, first?, &args)?;
                let mut found = self.el.traits.symbols_designating(&op, &carrier).into_iter().filter(|(fixity, sym)| {
                    let arity = if *fixity == OpFixity::Infix { 2 } else { 1 };
                    arity == operands.len() && heather_syntax::operator_form(sym, *fixity).is_some()
                });
                let (fixity, symbol) = found.next()?;
                if found.next().is_some() {
                    return None;
                }
                // Rung 1: inside `<A: Monoid(+)>` the written `+` is the bound
                // index at every carrier, so it cannot spell this.
                if fixity == OpFixity::Infix && self.cx.op_locals.iter_inner().any(|(s, _)| *s == symbol) {
                    return None;
                }
                let form = heather_syntax::operator_form(&symbol, fixity)?;
                Some(OpForm { symbol, fixity, form, operands })
            }
            // A constraint binder's operation, `#op<=@0_2(a, b)`: the symbol
            // that names it, while that symbol still resolves to it here.
            CallHead::Local(i) => {
                let name = self.var(i)?;
                let symbol = crate::traits::op_index_symbol(&name)?.to_string();
                let innermost = self.cx.op_locals.iter_inner().find(|(s, _)| *s == symbol)?;
                if innermost.1 != name || args.len() != 2 {
                    return None;
                }
                let form = heather_syntax::operator_form(&symbol, OpFixity::Infix)?;
                Some(OpForm { symbol, fixity: OpFixity::Infix, form, operands: args })
            }
            CallHead::Field(_) => None,
        }
    }

    /// The key of the carrier the callee at `abs` declares its explicit
    /// parameter `first` at — what the resolver would have read off the
    /// operand. A type parameter there is the type argument the call passed.
    /// Read off the declared telescope and the call's own arguments, never
    /// by reducing.
    fn operand_carrier(&self, abs: usize, first: usize, args: &[&Rc<Term>]) -> Option<String> {
        let Some(heather_kernel::term::GlobalBinding::Tm { ty, .. }) = self.el.psi.bindings.get(abs) else {
            return None;
        };
        let mut ty: &Type = ty;
        while let Type::UPi { body, .. } = ty {
            ty = body;
        }
        for _ in 0..first {
            let Type::Pi { cod, .. } = ty else { return None };
            ty = cod;
        }
        let Type::Pi { dom, .. } = ty else { return None };
        if let Type::El { tm, .. } = &**dom
            && let Term::Var(LocalVar(k)) = **tm
        {
            let p = first.checked_sub(k as usize + 1)?;
            let code = Type::El { level: crate::Level::Zero, tm: Rc::clone(args.get(p)?) };
            return self.carrier_key(&code);
        }
        // The binding is committed, so its type names committed definitions
        // only and the registry lookups below read it as stored.
        self.carrier_key(dom)
    }

    /// The designation key of a type's carrier, structurally: `Nat`, or the
    /// declaration an instance or a code names.
    fn carrier_key(&self, ty: &Type) -> Option<String> {
        if matches!(ty, Type::Nat) {
            return Some("Nat".to_string());
        }
        if let Type::El { tm, .. } = ty {
            if matches!(**tm, Term::TmNat) {
                return Some("Nat".to_string());
            }
            let tag = match self.el.gen_app_of(tm) {
                Some((GenDef::TyCodeFn(tag) | GenDef::TyCode(tag), _)) => Some(tag),
                _ => match &**tm {
                    Term::GlobalTm { var, .. } => match self.el.gen_def_of(*var) {
                        Some(GenDef::TyCode(tag)) => Some(tag),
                        _ => None,
                    },
                    _ => None,
                },
            };
            if let Some(ind) = tag.and_then(|tag| self.el.types.by_tag(tag)) {
                return Some(crate::names::qkey(&ind.scope.module, &ind.name));
            }
        }
        let inline = self.el.unspell_here(ty);
        let ind = self.el.tag_of(inline.as_ref().unwrap_or(ty))?;
        Some(crate::names::qkey(&ind.scope.module, &ind.name))
    }

    /// `op` spelled with its symbol, each operand parenthesized exactly where
    /// the parser would otherwise read it differently.
    fn operator(&self, op: &OpForm, d: u32) -> String {
        let sym = &op.symbol;
        match (op.form, op.operands.as_slice()) {
            (OperatorForm::Infix(l, r), [a, b]) => format!(
                "{} {sym} {}",
                self.operand(a, d, |f| f.left_of(l)),
                self.operand(b, d, |f| f.right_of(r)),
            ),
            (OperatorForm::Comparison, [a, b]) => {
                format!("{} {sym} {}", self.operand(a, d, Form::comparand), self.operand(b, d, Form::comparand))
            }
            (OperatorForm::Power, [a, b]) => format!(
                "{} ^ {}",
                self.operand(a, d, |f| f.at_most(Form::Postfix)),
                self.operand(b, d, |f| f.at_most(Form::Prefix)),
            ),
            (OperatorForm::Prefix, [a]) => format!("{sym}{}", self.operand(a, d, |f| f.at_most(Form::Prefix))),
            (OperatorForm::Postfix, [a]) => format!("{}{sym}", self.operand(a, d, |f| f.at_most(Form::Postfix))),
            // `op_form` matched arity to fixity; nothing else reaches here.
            _ => self.raw_tm(op.operands[0]),
        }
    }

    /// An operand one level down, in parentheses unless `fits` its form.
    fn operand(&self, t: &Term, d: u32, fits: impl Fn(Form) -> bool) -> String {
        self.operand_at(t, d + 1, fits)
    }

    fn operand_at(&self, t: &Term, d: u32, fits: impl Fn(Form) -> bool) -> String {
        let shown = self.tm(t, d);
        let mut form = self.form(t);
        // A spelling the walk did not build as an operator but that reads as
        // one, a negative literal: `(-1) ^ n`.
        if form == Form::Atom && shown.starts_with('-') {
            form = Form::Prefix;
        }
        if fits(form) { shown } else { format!("({shown})") }
    }

    /// Where `t`'s spelling sits in the grammar. Classifies without spelling,
    /// along the routes [`Self::tm`] takes to a non-atomic form.
    fn form(&self, t: &Term) -> Form {
        let mut t = std::borrow::Cow::Borrowed(t);
        // A β-redex spells as its contractum (`call`); a few steps suffice
        // for any the display holds, and an exhausted count says "loosest",
        // which only adds parentheses.
        for _ in 0..8 {
            if let Some(op) = self.op_form(&t) {
                return match op.form {
                    OperatorForm::Infix(l, r) => Form::Infix(l, r),
                    OperatorForm::Comparison => Form::Comparison,
                    OperatorForm::Power => Form::Power,
                    OperatorForm::Prefix => Form::Prefix,
                    OperatorForm::Postfix => Form::Postfix,
                };
            }
            match &*t {
                Term::Lam { .. } => return Form::Binder,
                Term::TmId { .. } => return Form::Comparison,
                Term::App { .. } | Term::AppAt { .. }
                    if !self.qualified && !self.annotations && self.call_parts(&t).is_none() =>
                {
                    match crate::spelling::beta_head(&t) {
                        Some(r) => t = std::borrow::Cow::Owned(r),
                        None => return Form::Atom,
                    }
                }
                _ => return Form::Atom,
            }
        }
        Form::Binder
    }

    // -- names --------------------------------------------------------------

    /// The binder name for a de Bruijn index, or `None` when the index is out
    /// of the scope this display knows about.
    fn var(&self, i: u32) -> Option<String> {
        let names = self.names.borrow();
        names.nth_inner(i as usize).map(str::to_string)
    }

    /// A global's written name and how each of its parameters is shown.
    /// Declines for a substituted global (a top-level declaration has a nil
    /// context, so its substitution carries no terms — anything else is not a
    /// plain reference) and for a binding `globals` does not name, which is
    /// every generated definition.
    fn global(&self, var: GlobalVar, subst: &LocalSubst) -> Option<(String, Vec<Shown>)> {
        if !subst.terms.is_empty() {
            return None;
        }
        let abs = self.el.global_abs_of(var)?;
        let mut name = self.el.global_name_at(abs)?;
        // A member's base name is the presentation choice, and re-parsing it
        // elsewhere resolves to nothing (or, worse, to something else). Fall
        // back to the qualified spelling exactly where the base one does not
        // come back here.
        if self.qualified && !NameLookup(self.el).base_name_resolves_to(&name, abs) {
            name = NameLookup(self.el).global_qualified_name_at(abs)?;
            // Nor the qualified one, from a module this one does not import:
            // a spelling that does not re-parse here declines like any
            // other unspellable node, and `omega` abstracts it.
            if !NameLookup(self.el).base_name_resolves_to(&name, abs) {
                return None;
            }
        }
        // A generated name (`sum#step`, `f#True`) is minted with a `#` no
        // source can write: spelled for re-parsing, it is its designed path
        // (`sum::step`) where that path still names it, and otherwise
        // declines like any other unspellable node, so `omega` abstracts it.
        if self.qualified && name.contains('#') {
            // Designed paths are not module-qualified.
            let declared = NameLookup(self.el).global_declared_name_at(abs)?;
            let designed = self.el.display_paths(&declared);
            let back = self.el.access_alias(&designed) == Some(declared.as_str());
            if designed.contains('#') || !back {
                return None;
            }
            name = designed;
        }
        let params = NameLookup(self.el).params_at(abs);
        // Spelling for re-parsing keeps an implicit that nothing written
        // determines: `BitVec::ofNat(5)` alone cannot say its width, so it is
        // spelled `BitVec::ofNat(5, n := 64)`
        // (`issues/omega-respells-atoms-without-implicits.md`). A resolved
        // (`requires`) parameter is left to resolution, as it was written.
        let determined = if self.qualified { self.el.implicits_determined(abs, params.len()) } else { Vec::new() };
        let shown = params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                if !p.implicit {
                    Shown::Explicit
                } else if p.is_type {
                    Shown::Type(self.qualified && !determined.get(i).copied().unwrap_or(true))
                } else if p.default.is_some() {
                    // A defaulted parameter's value is whatever the call
                    // gave, the default or an override, and nothing else
                    // determines it, so it is spelled by name in both modes
                    // (docs/language/named-arguments-design.md §9.6).
                    Shown::Named(p.name.clone())
                } else if !self.qualified
                    || p.solver.is_some()
                    || determined.get(i).copied().unwrap_or(true)
                    // A class index a symbol slot introduced (`MonoidRel::range`'s
                    // `≈`) has a generated name no call can write: a call fills
                    // it from the symbol's designation, as the source did.
                    || crate::traits::op_index_symbol(&p.name).is_some()
                {
                    Shown::Hidden
                } else {
                    Shown::Named(p.name.clone())
                }
            })
            .collect();
        Some((name, shown))
    }
}

/// A call's head, as [`Speller::call_parts`] recognises it.
pub(crate) enum CallHead {
    /// A record field read; the one argument is the receiver.
    Field(String),
    /// A named global, and how each of its parameters is shown.
    Global(String, Vec<Shown>),
    /// A local, by de Bruijn index.
    Local(u32),
}

/// How a call spells one of its head's parameters.
pub(crate) enum Shown {
    Explicit,
    /// An implicit the call's written arguments determine.
    Hidden,
    /// An implicit they do not, written as a named argument.
    Named(String),
    /// A leading type parameter; `true` when the call does not determine it.
    Type(bool),
}

/// A call [`Speller::op_form`] spells as an operator.
struct OpForm<'t> {
    symbol: String,
    fixity: OpFixity,
    form: OperatorForm,
    operands: Vec<&'t Rc<Term>>,
}

/// How a spelled term sits in the expression grammar, for deciding whether
/// it needs parentheses as an operand: the parser's own levels
/// ([`heather_syntax::OperatorForm`]), plus an atom and a binder form.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Form {
    /// A call, a name, a literal, anything delimited.
    Atom,
    Postfix,
    Power,
    Prefix,
    /// An infix rung, as its left and right binding powers.
    Infix(u8, u8),
    /// `a = b`, `a <= b`: non-associative, below every infix rung.
    Comparison,
    /// `λ x => …`, which runs as far right as it can.
    Binder,
}

impl Form {
    /// Tightness among the forms an operand position takes whole.
    fn rank(self) -> u8 {
        match self {
            Form::Atom => 0,
            Form::Postfix => 1,
            Form::Power => 2,
            Form::Prefix => 3,
            Form::Infix(..) => 4,
            Form::Comparison => 5,
            Form::Binder => 6,
        }
    }

    /// No looser than `bound` (an operand position that takes `bound`'s
    /// level whole).
    fn at_most(self, bound: Form) -> bool {
        self.rank() <= bound.rank()
    }

    /// The left operand of an infix rung that folds at left power `l`: an
    /// infix child stays together when its right operand stops before the
    /// parent's symbol.
    fn left_of(self, l: u8) -> bool {
        match self {
            Form::Infix(_, cr) => l < cr,
            f => f.at_most(Form::Prefix),
        }
    }

    /// The right operand of an infix rung parsed at right power `r`: an infix
    /// child stays together when its own symbol folds at that power.
    fn right_of(self, r: u8) -> bool {
        match self {
            Form::Infix(cl, _) => cl >= r,
            f => f.at_most(Form::Prefix),
        }
    }

    /// A side of `=` or of a comparison: anything below the comparison level.
    fn comparand(self) -> bool {
        self.at_most(Form::Infix(0, 0))
    }

    /// A receiver `r.f` takes without parentheses.
    fn bare_receiver(self) -> bool {
        self.at_most(Form::Postfix)
    }
}

impl Elaborator {
    /// `t`'s call shape as the tactic host's `View` presents it: the head a
    /// diagnostic would print and the arguments it would write, implicit and
    /// type arguments dropped as the diagnostic drops them.
    pub(crate) fn view_call(&self, cx: &Cx, t: &Term) -> Option<(CallHead, Vec<Rc<Term>>)> {
        let sp = self.speller(cx);
        let (head, args) = sp.call_parts(t)?;
        let written = |i: usize| match &head {
            CallHead::Global(_, shown) => matches!(shown.get(i), Some(Shown::Explicit) | None),
            CallHead::Field(_) | CallHead::Local(_) => true,
        };
        let args = args.iter().enumerate().filter(|(i, _)| written(*i)).map(|(_, a)| Rc::clone(a)).collect();
        Some((head, args))
    }

    /// A lowered constructor value as the tactic host's `View` presents it:
    /// its declaration, the constructor's number, and its fields in
    /// declaration order. The display's own reader ([`Speller::ctor_fields`]),
    /// so what a diagnostic spells as `C(…)` is what a view presents.
    pub(crate) fn view_ctor(&self, cx: &Cx, t: &Term) -> Option<(Rc<crate::inductive::Inductive>, usize, Vec<Rc<Term>>)> {
        let (ind, i, fields) = self.speller(cx).ctor_fields(t)?;
        Some((ind, i, fields?))
    }

    /// A field read a record's declaration left inline, `fst(snd(…(r)))`,
    /// as the record value `r` and the field's name: the recogniser behind
    /// the speller's `r.name` (`Speller::field_read`), shared with the tactic
    /// host's `View`. The record is read off the receiver's spine type, so
    /// only a receiver whose head is a variable, a global or another field
    /// read is recognised, and only at `cx`'s own scope.
    pub(crate) fn field_read_parts<'t>(&self, cx: &Cx, t: &'t Term) -> Option<(&'t Rc<Term>, String)> {
        let (pair, record, idx) = self.field_read_record(cx, t)?;
        let (Some(name), _) = record.ctors[0].fields.get(idx)? else {
            return None;
        };
        Some((pair, name.clone()))
    }

    /// [`Self::field_read_parts`]'s receiver, record and field number.
    pub(crate) fn field_read_record<'t>(
        &self,
        cx: &Cx,
        t: &'t Term,
    ) -> Option<(&'t Rc<Term>, Rc<crate::inductive::Inductive>, usize)> {
        let (true, mut pair) = crate::spelling::proj_of(t)? else {
            return None;
        };
        let mut entry = 0usize;
        while let Some((false, inner)) = crate::spelling::proj_of(pair) {
            entry += 1;
            pair = inner;
        }
        let idx = entry.checked_sub(1)?;
        let (head, _) = crate::spelling::app_spine(pair);
        if !matches!(head, Term::Var(_) | Term::GlobalTm { .. }) && crate::spelling::proj_of(head).is_none() {
            return None;
        }
        let span = heather_syntax::Span { start: 0, end: 0 };
        let ty = AppUnify(self).spine_type(cx, pair, span)?;
        let record = self.record_of_at(cx, &ty, span)?;
        record.ctors[0].fields.get(idx)?;
        Some((pair, record, idx))
    }

    /// For each of the first `count` parameters of the global at `abs`,
    /// whether a later **explicit** parameter's domain mentions it, so that
    /// elaborating the written arguments infers it. An explicit parameter
    /// answers `true`; so does every parameter when the type is not a plain
    /// Π telescope, the conservative side (the call then spells as before).
    fn implicits_determined(&self, abs: usize, count: usize) -> Vec<bool> {
        let params = NameLookup(self).params_at(abs);
        let Some(heather_kernel::term::GlobalBinding::Tm { ty, .. }) = self.psi.bindings.get(abs) else {
            return vec![true; count];
        };
        let mut ty: &Type = ty;
        if let Type::UPi { body, .. } = ty {
            ty = body;
        }
        let mut doms: Vec<&Type> = Vec::new();
        while doms.len() < count {
            let Type::Pi { dom, cod, .. } = ty else { return vec![true; count] };
            doms.push(dom);
            ty = cod;
        }
        (0..count)
            .map(|i| {
                !params.get(i).is_some_and(|p| p.implicit)
                    || (i + 1..count).any(|j| {
                        !params.get(j).is_some_and(|p| p.implicit)
                            && crate::unification::mentions_binder(doms[j], j as u32, (j - 1 - i) as u32)
                    })
            })
            .collect()
    }
}

/// `c` as it is written between `quote`s: the lexer's named escapes, a
/// control character as `\u{…}`, and everything else as itself.
fn escape_into(c: char, quote: char, out: &mut String) {
    match c {
        '\n' => out.push_str("\\n"),
        '\t' => out.push_str("\\t"),
        '\r' => out.push_str("\\r"),
        '\0' => out.push_str("\\0"),
        '\\' => out.push_str("\\\\"),
        c if c == quote => {
            out.push('\\');
            out.push(c);
        }
        c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", u32::from(c))),
        c => out.push(c),
    }
}

/// `spelling::same_projection(&alias.shift_local(by), t)` without the shift
/// unless the paths agree: a weakening keeps a projection a projection and a
/// node of one kind that kind, and moves a variable by `by`. The shift copies
/// the alias, and a walk asks every alias in scope at every projection it
/// spells (omega's certificate reads its atoms this way).
fn shifted_projection(alias: &Term, by: u32, t: &Term) -> bool {
    match (crate::spelling::proj_of(alias), crate::spelling::proj_of(t)) {
        (Some((af, ap)), Some((tf, tp))) => af == tf && shifted_projection(ap, by, tp),
        (Some(_), None) | (None, Some(_)) => false,
        (None, None) => match (alias, t) {
            (Term::Var(i), Term::Var(j)) => i.0.checked_add(by) == Some(j.0),
            _ if std::mem::discriminant(alias) != std::mem::discriminant(t) => false,
            _ => alias.shift_local(by) == *t,
        },
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

    /// The alias test without its copy answers what the copy did, on paths
    /// that agree, that part where the shift moves the base, and that differ
    /// in a field, in length or in the base's kind.
    #[test]
    fn a_shifted_projection_agrees_with_shifting_the_alias() {
        let var = |i| Rc::new(Term::Var(LocalVar(i)));
        let fst = |p: Rc<Term>| Rc::new(Term::FstAt { pair: p });
        let snd = |p: Rc<Term>| Rc::new(Term::SndAt { pair: p });
        let aliases = [var(0), fst(var(1)), snd(fst(var(0))), fst(Rc::new(Term::Zero)), snd(Rc::new(Term::Succ(var(2))))];
        let subjects = [
            var(0), var(3), fst(var(1)), fst(var(4)), snd(var(4)), fst(fst(var(4))), snd(fst(var(3))),
            snd(fst(var(2))), fst(Rc::new(Term::Zero)), snd(Rc::new(Term::Succ(var(5)))), snd(Rc::new(Term::Succ(var(2)))),
        ];
        for alias in &aliases {
            for t in &subjects {
                for by in [0, 1, 3] {
                    assert_eq!(
                        shifted_projection(alias, by, t),
                        crate::spelling::same_projection(&alias.shift_local(by), t),
                        "{alias:?} shifted by {by} against {t:?}",
                    );
                }
            }
        }
        assert!(shifted_projection(&snd(fst(var(0))), 3, &snd(fst(var(3)))));
    }

    #[test]
    fn rough_parameter_types_elide_kernel_only_nodes_and_exhausted_budgets() {
        let el = Elaborator::with_prelude().expect("prelude");
        let cx = Cx::empty();
        let mut ty = Type::SEmpty { level: Level::Zero };
        let note = el.display_deferred_argument(
            &cx, &Term::Zero, &[], &[(0, ty.clone())], &[], &[],
        );
        assert!(note.contains("`_: …`"), "{note}");
        for _ in 0..64 {
            ty = Type::Pi {
                dom_level: Level::Zero, cod_level: Level::Zero,
                dom: Rc::new(Type::Nat), cod: Rc::new(ty),
            };
        }
        let note = el.display_deferred_argument(&cx, &Term::Zero, &[], &[(0, ty)], &[], &[]);
        assert!(note.contains("Nat ->") && note.contains('…'), "{note}");
        assert!(!note.contains("sEmpty") && !note.contains("Pi("), "{note}");
        assert!(note.len() < 512, "rough type must stay bounded: {note}");
    }

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
