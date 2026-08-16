//! `datarepr` — runtime representations of spec inductives, linked by
//! certified refinement (`docs/datarepr-design.md`, `issues/datarepr-separation.md`).
//!
//! Nothing here reaches the kernel on its own, and nothing here is trusted.
//! A `datarepr` builds *surface source* — a spec-recursor specialization, the
//! per-inductive `Repr_N` record (§1.1), one ordinary declaration per clause
//! under `Repr_N`'s namespace, and the assembled record value — and hands each
//! item to the ordinary declaration gate. Every obligation in §1.1 is
//! therefore checked by the kernel exactly as a hand-written one would be;
//! `repr::naive()` is a *generator of source*, not a privileged instance.
//!
//! Emitting text rather than AST is the choice certgen made for its
//! per-signature records, and for the same reason: these artifacts are
//! dependent record types whose field list is computed from a constructor
//! list, and their AST spelling is an order of magnitude more code than their
//! surface spelling. The cost is that generated names must be *nameable* —
//! see the note in `elab_datarepr`.

use std::collections::HashMap;
use std::rc::Rc;

use heather_syntax::{parse_file, DatareprBody, DatareprDecl, DatareprField, Expr, ExprKind, Item, Span, Ty, TyKind};

use crate::{err, Elaborator, R};

/// A registered repr. Keyed per design §4: the spec inductive's elaborated
/// declaration identity (its nominal tag — the thing that changes when the
/// declaration is edited) plus the elaborated arguments of the instantiation.
/// Nominal keying would let a stale basis survive a refactor, which is the
/// failure mode §4 exists to avoid.
#[derive(Clone)]
pub(crate) struct DatareprInfo {
    /// The global that *is* the repr — `ListTok`, a `Repr_ListTok`.
    pub global: String,
    /// The spec type as written, for diagnostics and for restating an
    /// operation's signature with `S ↦ R`.
    pub written: String,
    /// The carrier, spelled.
    pub carrier: String,
    /// The generated record, whose namespace holds `abs` and `inv`.
    pub record: String,
    /// The spec constructors at this instantiation — the shape the transfer
    /// generator reads its algebra off.
    pub ctors: Rc<Vec<CtorView>>,
}

/// `(spec declaration identity, instantiation arguments)`. The tag is `None`
/// for `Nat`, which is a kernel type with no declaration to key on.
pub(crate) type DatareprKey = (Option<u32>, String);

// -- the spec inductive, as everything downstream needs to SPELL it ----------

/// One constructor field at the instantiation.
pub(crate) struct FieldView {
    /// The binder the generated source uses for this field.
    pub binder: String,
    /// A recursive position — the spec type itself. This is the only place
    /// `S ↦ R` applies (v1 rule, §1.2: *all* occurrences, no per-position
    /// mixing), and the only place `abs` is inserted by the adaptation.
    pub rec: bool,
    /// The field's type at the instantiation, spelled at the SPEC side.
    pub spell: String,
}

pub(crate) struct CtorView {
    pub name: String,
    pub fields: Vec<FieldView>,
}

/// The spec side of a `datarepr`, resolved and spelled.
struct SpecView {
    /// How the spec type is written: `List<Tok>`, `Nat`.
    spell: String,
    ctors: Vec<CtorView>,
    key: DatareprKey,
    /// A parameterized instantiation, i.e. one this declaration is the
    /// *minting site* for (§1.4 item 2).
    monomorph: Option<(u32, String)>,
}

impl SpecView {
    /// The indices of this constructor's recursive fields, in order.
    fn rec_of(c: &CtorView) -> Vec<usize> {
        c.fields.iter().enumerate().filter(|(_, f)| f.rec).map(|(i, _)| i).collect()
    }
}

// -- inline clause expressions, and the obligations they discharge -----------

/// The clause expressions the generated source carries as **placeholders**
/// (design §4.2, FINDING B).
///
/// A clause used to be turned back into text by [`spell_expr`], which declines
/// on everything larger than a name, a call or a projection — so an inline λ,
/// `match` or `let`-block was unwritable even though all of them check in
/// exactly the 0-ary shape the emission uses. The answer is not a wider
/// printer (~25 `ExprKind` variants to keep in sync forever, to reproduce text
/// that is immediately re-parsed) but to put the user's own `Expr` back after
/// parsing: the skeleton is generated with a placeholder name, and
/// [`Elaborator::elab_generated`] replaces it before `elab_decl` ever sees the
/// declaration.
///
/// A placeholder only ever occupies the **whole body** of a generated
/// declaration, which is what keeps the substitution a body-root replacement
/// rather than a general AST walk.
#[derive(Default)]
pub(crate) struct Splices {
    by_key: HashMap<String, Spliced>,
    n: usize,
}

struct Spliced {
    /// The clause's name, for the diagnostic.
    clause: String,
    /// Its span **in the user's file** — where a failure is reported, rather
    /// than at the owner declaration as before (§2.3).
    span: Span,
    expr: Expr,
}

impl Splices {
    /// Reserve a placeholder for one clause and return the text the generator
    /// writes in the body position.
    fn add(&mut self, clause: &str, span: Span, expr: &Expr) -> String {
        let key = format!("clause_splice_{}", self.n);
        self.n += 1;
        self.by_key.insert(
            key.clone(),
            Spliced { clause: clause.to_string(), span, expr: expr.clone() },
        );
        key
    }
}

/// A `?` clause: the **reporting hole** of design §1.2. It is not deferral —
/// it makes the declaration fail, at the `?`'s own span, printing the statement
/// that clause owes. The author reads the statement out of the error and writes
/// the proof where the `?` was.
pub(crate) struct Hole {
    owner: String,
    path: String,
    field: String,
    /// `?later` — a label, which only appears in the message.
    label: Option<String>,
    span: Span,
}

/// The `?` diagnostic (§2.3): the owner, the `::` path and the statement.
fn hole_error<T>(obs: &[Obligation], h: &Hole) -> R<T> {
    let stmt = obs
        .iter()
        .find(|o| o.field == h.field)
        .map(|o| o.statement.clone())
        // Unreachable: a `?` is only accepted at a field the generator states.
        .unwrap_or_else(|| "<the generator did not state this field>".to_string());
    let label = match &h.label {
        Some(l) => format!(" (labelled `{l}`)"),
        None => String::new(),
    };
    err(
        format!(
            "`{}` of `{}` is not proved{label}: a `?` clause reports its obligation and \
             fails — write the proof here \
             (docs/obligation-records-design.md §1.2)\n  `{}` owes:\n    {}",
            h.field, h.owner, h.path, stmt
        ),
        h.span,
    )
}

/// Only theorem fields are obligations (§1.1): the data fields are what the
/// statements are *computed from*, so a `?` there leaves the schema with
/// nothing to synthesize.
fn hole_on_data_field(clause: &str) -> String {
    format!(
        "`?` at clause `{clause}`, which is not an obligation: only the theorem clauses \
         may be `?`, because the data clauses are what their statements are computed \
         from (docs/obligation-records-design.md §1.1)"
    )
}

/// One obligation-bearing field of a generated declaration, recorded as the
/// generator spells it (design §1.1, §6).
///
/// Two consumers: a `?` at that clause, which fails printing `statement`, and
/// `heather obligations`, which lists them. Both want the statement as the
/// **source text** the schema is built in — decoding a kernel term back into
/// something a human can read is `issues/goal-display-decodes`, and building
/// the schema as source is how this design does not need it (§1.3, §6).
#[derive(Clone, Debug)]
pub struct Obligation {
    /// `impl add for BinNat`, `datarepr BinC`.
    pub owner: String,
    /// The printed path (§3): `Impl(add, BinNat)::refines`, `BinC::Succ_inv`.
    /// `::` because an obligation is a member of its owner's namespace;
    /// print-only in v1, so nothing parses it.
    pub path: String,
    pub field: String,
    /// `supplied` — the author wrote a proof — or `defaulted` (omitted, and
    /// therefore `refl`). Never `open`: under inline-first a listed file is a
    /// checked file (§6).
    pub state: &'static str,
    pub provenance: Option<Provenance>,
    pub statement: String,
}

/// How an artifact came to be. Recorded on the registry entry and printed by
/// the tooling; **never consulted by a certificate** — the registry has one
/// entry per key and the certificate is the same names whatever produced them
/// (design §9's last bullet, and the Q2 verdict's "distinguish provenance on
/// inspection").
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Provenance {
    /// Every clause is a plain name: the form generators emit.
    Named,
    /// At least one clause is an inline expression (§4.2).
    Inline,
    /// `:= derive()` — the transfer generator wrote all of it (§4.3).
    Derived,
    /// `refines := via_derived(p)` — the derived certificate, composed (§4.3).
    ViaDerived,
}

impl Provenance {
    pub fn as_str(self) -> &'static str {
        match self {
            Provenance::Named => "named",
            Provenance::Inline => "inline",
            Provenance::Derived => "derived",
            Provenance::ViaDerived => "via",
        }
    }
}

/// A registered `Impl`: the global holding the assembled record value, and how
/// it got there.
#[derive(Clone)]
pub(crate) struct ImplEntry {
    pub global: String,
    pub provenance: Provenance,
}

/// A surface type spelled back into source. Unlike `traits::render_ty` — a
/// *diagnostic* renderer with `_` fallbacks — this declines rather than
/// spelling something it cannot spell faithfully: the result is fed back to
/// the parser, so a lossy rendering would be a silently wrong artifact.
pub(crate) fn spell_ty(t: &Ty) -> Option<String> {
    Some(match &t.kind {
        TyKind::Nat => "Nat".into(),
        TyKind::Univ { level: 0 } => "Type".into(),
        TyKind::Univ { level } => format!("Type<{level}>"),
        TyKind::Named { name, args } if args.is_empty() => name.clone(),
        TyKind::Named { name, args } => {
            let a: Option<Vec<String>> = args.iter().map(spell_ty).collect();
            format!("{name}<{}>", a?.join(", "))
        }
        TyKind::Fn { binder: None, implicit: false, dom, cod } => {
            format!("({} -> {})", spell_ty(dom)?, spell_ty(cod)?)
        }
        TyKind::Fn { binder: Some(b), implicit: false, dom, cod } => {
            format!("(({b}: {}) -> {})", spell_ty(dom)?, spell_ty(cod)?)
        }
        _ => return None,
    })
}

impl Elaborator {
    /// Resolve the spec type into the constructor list the record's shape is
    /// computed from.
    fn spec_view(&self, spec: &Ty, span: Span) -> R<SpecView> {
        let Some(spell) = spell_ty(spec) else {
            return err(
                "the spec type of a `datarepr` is a declared inductive or `Nat`".to_string(),
                span,
            );
        };
        // `Nat` is a kernel type and has no declaration (`lib/std/nat.hthr`'s
        // header), so its constructor list is written here rather than read
        // off one. It is spelled exactly as a declaration would be, which is
        // why nothing downstream needs to know the difference.
        if matches!(spec.kind, TyKind::Nat) {
            return Ok(SpecView {
                spell,
                ctors: vec![
                    CtorView { name: "Zero".into(), fields: Vec::new() },
                    CtorView {
                        name: "Succ".into(),
                        fields: vec![FieldView {
                            binder: "a0".into(),
                            rec: true,
                            spell: "Nat".into(),
                        }],
                    },
                ],
                key: (None, String::new()),
                monomorph: None,
            });
        }
        let TyKind::Named { name, args } = &spec.kind else {
            return err(
                format!("`{spell}` is not a declared inductive, so it has no constructors to \
                         represent"),
                span,
            );
        };
        let Some(ind) = self.lookup_inductive(name).cloned() else {
            return err(format!("`{name}` is not a declared inductive"), span);
        };
        if ind.index.is_some() || !ind.valparams.is_empty() {
            return err(
                format!(
                    "`{spell}` is an indexed or value-parameterized declaration: v1 reprs are \
                     over plain inductives (docs/datarepr-design.md §5.1)"
                ),
                span,
            );
        }
        if ind.params.len() != args.len() {
            return err(
                format!(
                    "`{name}` takes {} type argument(s), not {}",
                    ind.params.len(),
                    args.len()
                ),
                span,
            );
        }
        // Type parameters are monomorphized (`InductiveDecl`'s doc), so
        // instantiating a stored field type is a substitution on the spelling.
        let mut subst: HashMap<&str, String> = HashMap::new();
        for (p, a) in ind.params.iter().zip(args.iter()) {
            let Some(s) = spell_ty(a) else {
                return err(format!("`{spell}`'s type argument cannot be spelled"), span);
            };
            subst.insert(p.as_str(), s);
        }
        let mut ctors = Vec::new();
        for c in &ind.ctors {
            let mut fields = Vec::new();
            for (i, (_, fty)) in c.fields.iter().enumerate() {
                let fty = subst_ty(fty, &subst);
                let Some(s) = spell_ty(&fty) else {
                    return err(
                        format!(
                            "`{}`'s field {i} has a type this round cannot spell: a v1 repr's \
                             non-recursive fields are left at their spec types \
                             (docs/datarepr-design.md §1.1)",
                            c.name
                        ),
                        span,
                    );
                };
                fields.push(FieldView { binder: format!("a{i}"), rec: s == spell, spell: s });
            }
            ctors.push(CtorView { name: c.name.clone(), fields });
        }
        let argkey = args.iter().filter_map(spell_ty).collect::<Vec<_>>().join(",");
        Ok(SpecView {
            key: (Some(ind.tag), argkey.clone()),
            monomorph: (!args.is_empty()).then_some((ind.tag, argkey)),
            spell,
            ctors,
        })
    }

    /// `datarepr N for S { … }` / `datarepr N for S := repr::naive();`
    /// (design §1.4).
    ///
    /// The generated names are **nameable** (`Repr_N`, `Repr_N::abs`, …)
    /// rather than carrying the `#` sigil `issues/unnameable-generated-names.md`
    /// points at. Forced, not chosen: the artifacts are emitted as source and
    /// re-parsed, and `#` never begins a surface identifier, so an unnameable
    /// name cannot be *written* in the text that declares it. The namespace
    /// hangs off `Repr_N` and not off `N` as §1.4 sketches, because a member
    /// declaration's qualifier has to name a type in scope and `N` names the
    /// assembled value.
    pub(crate) fn elab_datarepr(&mut self, d: &DatareprDecl) -> R<()> {
        let mut spec = self.spec_view(&d.spec, d.spec.span)?;
        if let Some(prev) = self.datareprs.get(&spec.key) {
            return err(
                format!(
                    "`{}` already has a repr, `{}`: v1 is one repr per spec type \
                     (docs/datarepr-design.md §5.3 defers multi-repr)",
                    prev.written, prev.global
                ),
                d.span,
            );
        }
        if self.datarepr_by_name.contains_key(&d.name) {
            return err(format!("duplicate repr name `{}`", d.name), d.span);
        }
        // The designed access spellings (`docs/repr-access-spellings-design.md`
        // §5), registered before anything is generated: a `?` in a clause
        // reports statements, and those are printed through the same table.
        let ctors: Vec<String> = spec.ctors.iter().map(|c| c.name.clone()).collect();
        self.register_repr_access(&d.name, &ctors);
        let mut sp = Splices::default();
        let mut holes = Vec::new();
        let clauses = self.clauses_of(d, &spec, &mut sp, &mut holes)?;
        if clauses.fold.is_none() {
            self.register_fold_default_access(&d.name);
        }
        let owner = format!("datarepr {}", d.name);
        let mut obs = Vec::new();
        let src = generate(&d.name, &spec, &clauses, &owner, &mut obs);
        // A statement is printed, by the listing and by a `?`, and what is
        // printed has to be what can be written: the minted names the
        // generated declarations are checked against become the designed
        // paths at exactly this boundary (design §7).
        for o in &mut obs {
            o.statement = self.display_paths(&o.statement);
        }
        // A `?` reports and fails (§1.2): the statements exist by now, and
        // nothing has been declared, so the file is refused with the obligation
        // printed and no artifact left behind.
        if let Some(h) = holes.first() {
            return hole_error(&obs, h);
        }
        self.elab_generated(&src, &owner, d.span, &sp)?;
        self.obligations.extend(obs);
        let info = DatareprInfo {
            global: d.name.clone(),
            written: spec.spell.clone(),
            carrier: clauses.carrier.clone(),
            record: record_name(&d.name),
            ctors: Rc::new(std::mem::take(&mut spec.ctors)),
        };
        self.datareprs.insert(
            spec.key.clone(),
            info.clone(),
        );
        self.datarepr_by_name.insert(d.name.clone(), info);
        // The minting site (§1.4 item 2): a parameterized instantiation has no
        // name today, and this declaration is where it gets one. The consumer
        // is certgen's rim, which needs a name to build `embed_T`'s — not a
        // new type: `List<Tok>` is perfectly spellable as a *type*, it just
        // cannot name a function.
        if let Some(mono) = spec.monomorph {
            self.monomorphs.insert(mono, d.name.clone());
        }
        Ok(())
    }

    /// The clause table: every field of the generated record, as the source
    /// expression that fills it. Either read off the written clauses or minted
    /// by `repr::naive()`.
    fn clauses_of(
        &self,
        d: &DatareprDecl,
        spec: &SpecView,
        sp: &mut Splices,
        holes: &mut Vec<Hole>,
    ) -> R<Clauses> {
        match &d.body {
            DatareprBody::Mint(e) => {
                if !is_naive_call(e) {
                    return err(
                        format!(
                            "`{}` is not a repr generator this round knows: v1 has \
                             `repr::naive()` only, and the auto-pick meta-program \
                             (`repr::inductive_repr()`) is v2+ \
                             (docs/datarepr-design.md §5.1 item 2, §5.2)",
                            spell_expr(e).unwrap_or_else(|| "this expression".into())
                        ),
                        e.span,
                    );
                }
                Ok(naive_clauses(&d.name, spec))
            }
            DatareprBody::Fields(fs) => self.written_clauses(d, spec, fs, sp, holes),
        }
    }

    fn written_clauses(
        &self,
        d: &DatareprDecl,
        spec: &SpecView,
        fs: &[DatareprField],
        sp: &mut Splices,
        holes: &mut Vec<Hole>,
    ) -> R<Clauses> {
        // `mk C` and a plain clause `C` are different clauses; the `mk` ones
        // key under a prefix containing a space, which no clause name has.
        let mut by_name: HashMap<String, (String, Span)> = HashMap::new();
        let mut prov: HashMap<String, Provenance> = HashMap::new();
        for f in fs {
            if f.is_mk && !spec.ctors.iter().any(|c| c.name == f.name) {
                return err(
                    format!(
                        "`mk {}` is not a constructor of `{}`: the clause list is checked \
                         against the spec declaration",
                        f.name, spec.spell
                    ),
                    f.span,
                );
            }
            let key =
                if f.is_mk { format!("mk {}", f.name) } else { f.name.clone() };
            if by_name.contains_key(&key) {
                return err(format!("duplicate clause `{key}`"), f.span);
            }
            // `R` is the carrier, and the generated source uses it as a *type*
            // in a dozen positions, so it is the one clause that still has to
            // survive as text. Everything else is spliced (§4.2).
            if key == "R" {
                let Some(text) = spell_expr(&f.expr) else {
                    return err(
                        "clause `R` is the repr's carrier and stands in *type* position \
                         throughout the generated source, so it has to be spellable: \
                         write it as a type name or an applied type name"
                            .to_string(),
                        f.span,
                    );
                };
                by_name.insert(key, (text, f.span));
                continue;
            }
            if let ExprKind::Hole(label) = &f.expr.kind {
                if !is_repr_obligation(spec, &key) {
                    return err(hole_on_data_field(&key), f.expr.span);
                }
                holes.push(Hole {
                    owner: format!("datarepr {}", d.name),
                    path: format!("{}::{key}", d.name),
                    field: key.clone(),
                    label: label.clone(),
                    span: f.expr.span,
                });
            }
            prov.insert(
                key.clone(),
                if matches!(f.expr.kind, ExprKind::Var(_)) {
                    Provenance::Named
                } else {
                    Provenance::Inline
                },
            );
            let placeholder = sp.add(&key, f.span, &f.expr);
            by_name.insert(key, (placeholder, f.span));
        }
        let mut missing = Vec::new();
        let take = |k: &str, by: &mut HashMap<String, (String, Span)>| {
            by.remove(k).map(|(t, _)| t)
        };
        let req = |k: &str, by: &mut HashMap<String, (String, Span)>, missing: &mut Vec<String>| {
            take(k, by).unwrap_or_else(|| {
                missing.push(k.to_string());
                String::new()
            })
        };
        let carrier = req("R", &mut by_name, &mut missing);
        let abs = req("abs", &mut by_name, &mut missing);
        // `inv` and `fold` have defaults (`issues/repr-fold-via-abs-default.md`):
        // an omitted `inv` is `True` — the same `Zero = Zero` the naive repr
        // spells, §1.4 note 6 — and an omitted `fold` is the fold *through*
        // `abs`, synthesized in `generate`. Omission means "take the default"
        // and nothing else; a `?` still reports and fails (design
        // docs/obligation-records-design.md §1.2).
        let inv = take("inv", &mut by_name)
            .unwrap_or_else(|| format!("\u{3bb} (r: {carrier}) => (Zero = Zero)"));
        let fold = take("fold", &mut by_name);
        let mut mks = Vec::new();
        for c in &spec.ctors {
            mks.push(req(&format!("mk {}", c.name), &mut by_name, &mut missing));
        }
        if !missing.is_empty() {
            return err(
                format!(
                    "`datarepr {}` is missing {}: a repr's correctness basis is \
                     `R`, `abs` and one `mk` per constructor \
                     (docs/datarepr-design.md §1.1); `inv` and `fold` default \
                     when omitted",
                    d.name,
                    missing.join(", ")
                ),
                d.span,
            );
        }
        // Laws may be omitted, in which case they are `refl` — the definitional
        // case, which is every law of the naive repr (§1.4).
        let mut laws = Vec::new();
        for c in &spec.ctors {
            let a = take(&format!("{}_abs", c.name), &mut by_name);
            let i = take(&format!("{}_inv", c.name), &mut by_name);
            laws.push((a, i));
        }
        let fold_law = take("fold_law", &mut by_name);
        if let Some((k, (_, span))) = by_name.iter().next() {
            return err(
                format!(
                    "`{k}` is not a clause of a repr of `{}`: the clauses are `R`, `abs`, \
                     `inv`, `fold`, `fold_law`, one `mk C` per constructor and the \
                     per-constructor laws `C_abs`/`C_inv`",
                    spec.spell
                ),
                *span,
            );
        }
        Ok(Clauses { carrier, abs, inv, mks, laws, fold, fold_law, prov })
    }

    /// Parse and elaborate generated source in the *current* module and scope.
    /// A failure here is a failure of the `datarepr` declaration, reported
    /// against it — the generated text is an implementation detail, so it is
    /// named in the message rather than shown.
    fn elab_generated(
        &mut self,
        src: &str,
        what: &str,
        span: Span,
        sp: &Splices,
    ) -> R<()> {
        // Generated mode: inside it the minted names *are* the surface, which
        // is what the emission spells (`docs/repr-access-spellings-design.md`
        // §6). A mode and not a property of the text, so that a generator that
        // one day writes designed paths needs no change here.
        self.generated_mode(|me| me.elab_generated_at(src, what, span, sp))
    }

    fn elab_generated_at(
        &mut self,
        src: &str,
        what: &str,
        span: Span,
        sp: &Splices,
    ) -> R<()> {
        let mut file = match parse_file(src) {
            Ok(f) => f,
            Err(e) => {
                return err(
                    format!("`datarepr {what}` generated source that does not parse: {}", e.msg),
                    span,
                )
            }
        };
        // The splice (§4.2): a generated body that is exactly a placeholder
        // becomes the user's own expression, spans and all. Done here rather
        // than in the generator because the generator writes *text*, and this
        // is the one point at which that text has become an AST and has not
        // yet been elaborated.
        let mut wrote: Vec<Option<(&str, Span)>> = Vec::with_capacity(file.items.len());
        for item in &mut file.items {
            let mut from = None;
            if let Item::Decl(d) = item
                && d.body.stmts.is_empty()
                && let ExprKind::Var(name) = &d.body.result.kind
                && let Some(s) = sp.by_key.get(name.as_str())
            {
                from = Some((s.clause.as_str(), s.span));
                d.body.result = Box::new(s.expr.clone());
            }
            wrote.push(from);
        }
        for (item, from) in file.items.iter().zip(wrote) {
            let (r, isp) = match item {
                Item::Decl(d) => (self.elab_decl(d), d.span),
                Item::Inductive(i) => (self.elab_inductive(i), i.span),
                Item::Impl(i) => (self.elab_impl(i), i.span),
                _ => unreachable!("the generator emits declarations, records and impls only"),
            };
            if let Err(e) = r {
                self.pending_derived.borrow_mut().clear();
                // The generated declaration is quoted. It is the *obligation*
                // the writer owes — a repr's law, restated at their carrier —
                // so without it the diagnostic names a field and shows
                // nothing, and the field's statement is exactly what is not
                // obvious.
                //
                // A spliced clause reports at the CLAUSE's own span, which is
                // in the user's file and is where they wrote the proof; an
                // unspliced one still reports at the owner declaration, which
                // is the only span it has (§4.2's recorded limitation: a
                // spliced subtree's spans index the user's file, so pointing at
                // a failing sub-term wants span provenance and is deferred).
                let (at, lead) = match from {
                    Some((clause, cs)) => (cs, format!("`{what}`, clause `{clause}`")),
                    None => (span, format!("`{what}`")),
                };
                return err(
                    format!(
                        "{lead}: {}\n  in the generated declaration:\n    {}",
                        e.message(),
                        src[isp.start..isp.end].replace('\n', "\n    ")
                    ),
                    at,
                );
            }
            self.mint_pending();
        }
        Ok(())
    }

    /// The name a `datarepr` minted for a parameterized instantiation, if any
    /// (§1.4 item 2). The consumer is certgen's rim.
    pub fn monomorph_name(&self, name: &str, args: &[Ty]) -> Option<&str> {
        let ind = self.lookup_inductive(name)?;
        let argkey = args.iter().filter_map(spell_ty).collect::<Vec<_>>().join(",");
        self.monomorphs.get(&(ind.tag, argkey)).map(|s| s.as_str())
    }
}

/// The filled-in field list of the generated record, as source expressions.
/// A law's `None` is the omitted-because-definitional case, filled with
/// `refl` under the binders the statement quantifies over.
struct Clauses {
    carrier: String,
    abs: String,
    inv: String,
    mks: Vec<String>,
    /// Per constructor, `(C_abs, C_inv)`.
    laws: Vec<(Option<String>, Option<String>)>,
    /// `None` is the omitted-because-defaultable case: the fold *through*
    /// `abs`, synthesized by [`generate`] together with the embedding and the
    /// two lemmas its anchor law needs.
    fold: Option<String>,
    fold_law: Option<String>,
    /// How each written clause was written, by field name — for the
    /// obligations listing (§6). A field absent here was omitted, and is
    /// therefore `defaulted`.
    prov: HashMap<String, Provenance>,
}

/// `repr::naive()` (§5.1 item 2): carrier = the spec type, `abs = id`,
/// `inv = True`, images = the constructors, fold = the recursor, every law
/// `refl`. Always mintable for any inductive, because nothing in it depends
/// on anything but the constructor list.
fn naive_clauses(name: &str, spec: &SpecView) -> Clauses {
    let s = &spec.spell;
    let mks = spec
        .ctors
        .iter()
        .map(|c| {
            let body = if c.fields.is_empty() {
                c.name.clone()
            } else {
                let args: Vec<&str> = c.fields.iter().map(|f| f.binder.as_str()).collect();
                format!("{}({})", c.name, args.join(", "))
            };
            lams(&c.fields.iter().map(|f| (f.binder.clone(), f.spell.clone())).collect::<Vec<_>>(), &body)
        })
        .collect();
    Clauses {
        carrier: s.clone(),
        abs: format!("\u{3bb} (r: {s}) => r"),
        // `True` spelled as the one proposition available without a library:
        // `Nat` is a kernel type, so `Zero = Zero` is in scope wherever a
        // `datarepr` is (`lib/std/nat.hthr`'s header), and `refl` inhabits it.
        inv: format!("\u{3bb} (r: {s}) => (Zero = Zero)"),
        mks,
        laws: spec.ctors.iter().map(|_| (None, None)).collect(),
        // The naive fold is the spec recursor itself, not the via-abs default:
        // at `abs = id` the default's embedding would be a round-trip through
        // the constructor images where the recursor is already at hand, and
        // every emission this generator has ever produced stays byte-identical.
        fold: Some({
            let mut bs = vec![("B".to_string(), "Type".to_string())];
            for (j, c) in spec.ctors.iter().enumerate() {
                bs.push((format!("s{j}"), step_ty(c, s, "B")));
            }
            bs.push(("r".to_string(), s.clone()));
            let args: Vec<String> = (0..spec.ctors.len()).map(|j| format!("s{j}")).collect();
            lams(&bs, &format!("{}(B, {}, r)", spec_rec_name(name), args.join(", ")))
        }),
        fold_law: None,
        prov: HashMap::new(),
    }
}

/// The clauses of a repr that are obligations rather than data (§1.1): the
/// per-constructor commutation and closure laws, and the fold anchor.
fn is_repr_obligation(spec: &SpecView, clause: &str) -> bool {
    clause == "fold_law"
        || spec
            .ctors
            .iter()
            .any(|c| clause == format!("{}_abs", c.name) || clause == format!("{}_inv", c.name))
}

fn is_naive_call(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::App { head, args, .. } => args.is_empty() && is_naive_call(head),
        ExprKind::Var(n) => n == "repr::naive",
        _ => false,
    }
}

/// An expression back into source. Deliberately **not** `traits::render_expr`:
/// that is a diagnostic renderer whose fallback is `_`, which here would parse
/// back as a *hole* and could be silently inferred into something the user
/// never wrote. Every shape this does not spell is a decline instead.
///
/// Its job narrowed when clauses started splicing (§4.2): the only clause it
/// still spells is `R`, the carrier, which stands in **type** position
/// throughout the generated source and so cannot be an arbitrary expression.
/// Everything else here is diagnostics — naming an expression the elaborator
/// is refusing.
pub(crate) fn spell_expr(e: &Expr) -> Option<String> {
    Some(match &e.kind {
        ExprKind::Var(n) => n.clone(),
        ExprKind::Num(n) => n.to_string(),
        ExprKind::App { head, args, .. } => {
            let a: Option<Vec<String>> = args.iter().map(spell_expr).collect();
            let a = a?;
            if a.is_empty() {
                format!("{}()", spell_expr(head)?)
            } else {
                format!("{}({})", spell_expr(head)?, a.join(", "))
            }
        }
        ExprKind::TyApp { head, args } => {
            let a: Option<Vec<String>> = args.iter().map(spell_ty).collect();
            format!("{}<{}>", spell_expr(head)?, a?.join(", "))
        }
        ExprKind::Dot { recv, name, .. } => format!("{}.{name}", spell_expr(recv)?),
        _ => return None,
    })
}

// -- spelling the generated source ------------------------------------------

pub(crate) fn spec_rec_name(name: &str) -> String {
    format!("{name}_spec_rec")
}

pub(crate) fn record_name(name: &str) -> String {
    format!("Repr_{name}")
}

/// The `Impl` record's name — the namespace holding `body`, `refines` and (at a
/// repr-typed result) `refines_inv`. Spelled in one place because two clients
/// need it to agree: `elab_impl`, which declares it, and the transfer
/// generator, which resolves a callee's certificate through it. Reaching
/// through the *namespace* rather than projecting the assembled value is not a
/// style choice — projecting a theorem-valued field off a record value is
/// `issues/theorem-field-projection-oom.md`.
pub(crate) fn impl_record_name(repr: &str, op: &str) -> String {
    format!("Impl_{repr}_{op}")
}

/// `λ (x: T) => λ (y: U) => body`, or `body` when there are no binders.
pub(crate) fn lams(bs: &[(String, String)], body: &str) -> String {
    let mut s = String::new();
    for (n, t) in bs {
        s.push_str(&format!("\u{3bb} ({n}: {t}) => "));
    }
    s.push_str(body);
    s
}

/// `(x: T) -> (y: U) -> cod`.
pub(crate) fn pis(bs: &[(String, String)], cod: &str) -> String {
    let mut s = String::new();
    for (n, t) in bs {
        s.push_str(&format!("({n}: {t}) -> "));
    }
    s.push_str(cod);
    s
}

/// `x: T, y: U` — a declaration's parameter list, the shape the transfer
/// generator's lemmas are declared with (`pis` is the same binders as a type).
pub(crate) fn params_src(bs: &[(String, String)]) -> String {
    bs.iter().map(|(n, t)| format!("{n}: {t}")).collect::<Vec<_>>().join(", ")
}

/// `f(a)(b)` — curried application, the shape every function-typed *field* of
/// the record has (§1.1 writes them curried).
pub(crate) fn appc(head: &str, args: &[String]) -> String {
    let mut s = head.to_string();
    for a in args {
        s.push_str(&format!("({a})"));
    }
    s
}

/// One `fold` step's type at carrier `at`: the constructor's fields, then one
/// `B` per recursive field. The spec step is this at the spec type, the repr
/// step this at the carrier — the two sides the adaptation runs between.
fn step_ty(c: &CtorView, at: &str, b: &str) -> String {
    let mut bs = Vec::new();
    for f in &c.fields {
        bs.push((f.binder.clone(), if f.rec { at.to_string() } else { f.spell.clone() }));
    }
    for (k, _) in SpecView::rec_of(c).iter().enumerate() {
        bs.push((format!("b{k}"), b.to_string()));
    }
    pis(&bs, b)
}

/// The spec step adapted repr-ward (§1.1, as corrected 2026-08-15): `abs` at
/// the child position. The adaptation runs one way only — there is no `S -> R`
/// — so the law takes the SPEC step and this is what the fold is applied to.
fn adapt(c: &CtorView, carrier: &str, s: &str, abs: &str) -> String {
    let mut bs = Vec::new();
    for f in &c.fields {
        bs.push((f.binder.clone(), if f.rec { carrier.to_string() } else { f.spell.clone() }));
    }
    let recs = SpecView::rec_of(c);
    for (k, _) in recs.iter().enumerate() {
        bs.push((format!("b{k}"), "B".to_string()));
    }
    let mut args: Vec<String> = c
        .fields
        .iter()
        .map(|f| if f.rec { appc(abs, &[f.binder.clone()]) } else { f.binder.clone() })
        .collect();
    for (k, _) in recs.iter().enumerate() {
        args.push(format!("b{k}"));
    }
    lams(&bs, &appc(s, &args))
}

/// The whole artifact, in dependency order: the spec recursor specialization,
/// the record, one declaration per clause under the record's namespace, and
/// the assembled value.
fn generate(
    name: &str,
    spec: &SpecView,
    cl: &Clauses,
    owner: &str,
    obs: &mut Vec<Obligation>,
) -> String {
    let s = &spec.spell;
    let c = &cl.carrier;
    let rec = record_name(name);
    let sr = spec_rec_name(name);
    let abs = format!("{rec}::abs()");
    let inv = format!("{rec}::inv()");
    let nctor = spec.ctors.len();
    let steps: Vec<String> = (0..nctor).map(|j| format!("s{j}")).collect();
    let mut out = String::new();

    // 1. The spec recursor at this instantiation. `S`'s eliminator is `match`,
    //    which is a *form* and not a global, so the anchor law needs a name to
    //    state itself against and this is it (§1.4 item 2's "recursor
    //    specialization").
    {
        let mut ps = vec![("B".to_string(), "Type".to_string())];
        for (j, ct) in spec.ctors.iter().enumerate() {
            ps.push((format!("s{j}"), step_ty(ct, s, "B")));
        }
        ps.push(("x".to_string(), s.clone()));
        let params: Vec<String> =
            ps.iter().map(|(n, t)| format!("{n}: {t}")).collect();
        let mut arms = String::new();
        for (j, ct) in spec.ctors.iter().enumerate() {
            let pat = if ct.fields.is_empty() {
                ct.name.clone()
            } else {
                let bs: Vec<&str> = ct.fields.iter().map(|f| f.binder.as_str()).collect();
                format!("{}({})", ct.name, bs.join(", "))
            };
            let mut args: Vec<String> =
                ct.fields.iter().map(|f| f.binder.clone()).collect();
            for i in SpecView::rec_of(ct) {
                args.push(format!(
                    "{sr}(B, {}, {})",
                    steps.join(", "),
                    ct.fields[i].binder
                ));
            }
            arms.push_str(&format!("        {pat} => {},\n", appc(&format!("s{j}"), &args)));
        }
        out.push_str(&format!(
            "fn {sr}({}) -> B {{\n    match x {{\n{arms}    }}\n}}\n\n",
            params.join(", ")
        ));
    }

    // 2. The record (§1.1). Its shape is the constructor list's, which is why
    //    it is generated per inductive rather than being one polymorphic class.
    {
        let mut fs: Vec<String> = vec![
            "    R: Type".into(),
            format!("    abs: (r: R) -> {s}"),
            "    inv: (r: R) -> Type".into(),
        ];
        for ct in &spec.ctors {
            fs.push(format!("    mk_{}: {}", ct.name, mk_ty(ct, "R")));
        }
        for ct in &spec.ctors {
            fs.push(format!("    {}_abs: {}", ct.name, abs_law_ty(ct, "R", "abs", "inv", &mk_field(ct))));
            fs.push(format!("    {}_inv: {}", ct.name, inv_law_ty(ct, "R", "inv", &mk_field(ct))));
        }
        let mut fb = vec![("B".to_string(), "Type".to_string())];
        for (j, ct) in spec.ctors.iter().enumerate() {
            fb.push((format!("s{j}"), step_ty(ct, "R", "B")));
        }
        fb.push(("r".to_string(), "R".to_string()));
        fs.push(format!("    fold: {}", pis(&fb, "B")));
        fs.push(format!("    fold_law: {}", fold_law_ty(spec, "R", "abs", "inv", "fold", &sr)));
        out.push_str(&format!("record {rec} {{\n{}\n}}\n\n", fs.join(",\n")));
    }

    // 3. The namespace: one ordinary declaration per clause, at exactly the
    //    field's type. Each is 0-ary and the clause is its whole body, so a
    //    written clause is checked against its obligation and nothing else —
    //    and a failure names the field.
    out.push_str(&format!("fn {rec}::abs() -> (r: {c}) -> {s} {{ {} }}\n", cl.abs));
    out.push_str(&format!("fn {rec}::inv() -> (r: {c}) -> Type {{ {} }}\n", cl.inv));
    for (ct, mk) in spec.ctors.iter().zip(cl.mks.iter()) {
        out.push_str(&format!(
            "fn {rec}::mk_{}() -> {} {{ {mk} }}\n",
            ct.name,
            mk_ty(ct, c)
        ));
    }
    let mkg = |ct: &CtorView| format!("{rec}::mk_{}()", ct.name);
    // Each law is recorded as it is stated (§1.1's statement schema): a `?` at
    // this clause prints the statement, and so does the obligations listing.
    //
    // The two *data* clauses that have a default — `inv` and `fold` — are
    // listed alongside the laws, with the type they are checked against as
    // their statement. They are still not obligations in §1.1's sense (a `?`
    // at either is refused, because the statements are computed *from* them);
    // what the row answers is the question the defaults created, "did this
    // repr take the default here?" (`issues/repr-fold-via-abs-default.md`).
    let mut note = |field: String, statement: &str, written: bool| {
        obs.push(Obligation {
            owner: owner.to_string(),
            path: format!("{name}::{field}"),
            state: if written { "supplied" } else { "defaulted" },
            provenance: if written { cl.prov.get(&field).copied() } else { None },
            field,
            statement: statement.to_string(),
        });
    };
    note("inv".to_string(), &format!("(r: {c}) -> Type"), cl.prov.contains_key("inv"));
    for (ct, (la, li)) in spec.ctors.iter().zip(cl.laws.iter()) {
        let ty = abs_law_ty(ct, c, &abs, &inv, &mkg(ct));
        note(format!("{}_abs", ct.name), &ty, la.is_some());
        out.push_str(&format!(
            "theorem {rec}::{}_abs(): {ty} {{ {} }}\n",
            ct.name,
            la.clone().unwrap_or_else(|| refl_under(ct, c, &inv))
        ));
        let ty = inv_law_ty(ct, c, &inv, &mkg(ct));
        note(format!("{}_inv", ct.name), &ty, li.is_some());
        out.push_str(&format!(
            "theorem {rec}::{}_inv(): {ty} {{ {} }}\n",
            ct.name,
            li.clone().unwrap_or_else(|| refl_under(ct, c, &inv))
        ));
    }
    // The via-abs default (`issues/repr-fold-via-abs-default.md`): the fold the
    // repr did not write is `spec_rec ∘ abs`, and the three declarations it
    // rests on go here — after the image laws, which two of them consume, and
    // before `fold` itself, which the first one is spelled inside.
    let fold_body = match &cl.fold {
        Some(f) => f.clone(),
        None => {
            out.push_str(&emb_decls(name, spec, c, &rec, &sr, &abs, &inv));
            via_abs_fold(name, spec, c, &sr, &abs)
        }
    };
    let mut fb = vec![("B".to_string(), "Type".to_string())];
    for (j, ct) in spec.ctors.iter().enumerate() {
        fb.push((format!("s{j}"), step_ty(ct, c, "B")));
    }
    fb.push(("r".to_string(), c.clone()));
    let fold_ty = pis(&fb, "B");
    note("fold".to_string(), &fold_ty, cl.prov.contains_key("fold"));
    out.push_str(&format!("fn {rec}::fold() -> {fold_ty} {{ {fold_body} }}\n"));
    {
        let ty = fold_law_ty(spec, c, &abs, &inv, &format!("{rec}::fold()"), &sr);
        note("fold_law".to_string(), &ty, cl.fold_law.is_some());
        let body = cl.fold_law.clone().unwrap_or_else(|| {
            let mut bs = vec![("B".to_string(), "Type".to_string())];
            for (j, ct) in spec.ctors.iter().enumerate() {
                bs.push((format!("s{j}"), step_ty(ct, s, "B")));
            }
            bs.push(("r".to_string(), c.clone()));
            bs.push(("h".to_string(), appc(&inv, &["r".to_string()])));
            // A written fold's law is `refl` when it is definitional (the naive
            // repr). The *defaulted* fold's is not — it is the induction
            // `via_abs_law` states, which is why that lemma exists at all.
            match &cl.fold {
                Some(_) => lams(&bs, "refl"),
                None => {
                    out.push_str(&via_abs_law(name, spec, &sr, &abs));
                    let mut args = vec!["B".to_string()];
                    args.extend((0..spec.ctors.len()).map(|j| format!("s{j}")));
                    args.push(appc(&abs, &["r".to_string()]));
                    lams(&bs, &format!("{}({})", via_abs_law_name(name), args.join(", ")))
                }
            }
        });
        out.push_str(&format!("theorem {rec}::fold_law(): {ty} {{ {body} }}\n"));
    }

    // 4. The assembled value — the `class`/`instance` pattern's last step
    //    (§1.4): a namespace of ordinary declarations, then one record value.
    {
        let mut fields = vec![
            format!("R: {c}"),
            format!("abs: {rec}::abs()"),
            format!("inv: {rec}::inv()"),
        ];
        for ct in &spec.ctors {
            fields.push(format!("mk_{}: {rec}::mk_{}()", ct.name, ct.name));
        }
        for ct in &spec.ctors {
            fields.push(format!("{}_abs: {rec}::{}_abs()", ct.name, ct.name));
            fields.push(format!("{}_inv: {rec}::{}_inv()", ct.name, ct.name));
        }
        fields.push(format!("fold: {rec}::fold()"));
        fields.push(format!("fold_law: {rec}::fold_law()"));
        out.push_str(&format!(
            "\nfn {name}() -> {rec} {{ {rec} {{ {} }} }}\n",
            fields.join(", ")
        ));
    }
    out
}

/// `mk_C`'s type at carrier `at`: the constructor's signature with `S ↦ R`.
fn mk_ty(c: &CtorView, at: &str) -> String {
    let bs: Vec<(String, String)> = c
        .fields
        .iter()
        .map(|f| (f.binder.clone(), if f.rec { at.to_string() } else { f.spell.clone() }))
        .collect();
    pis(&bs, at)
}

fn mk_field(c: &CtorView) -> String {
    format!("mk_{}", c.name)
}

/// The binder list every per-constructor law quantifies over: the image's
/// arguments, then `inv` at each repr-typed one (§1.1 — every law quantifies
/// over `inv`-satisfying inputs).
fn law_binders(c: &CtorView, at: &str, inv: &str) -> Vec<(String, String)> {
    let mut bs: Vec<(String, String)> = c
        .fields
        .iter()
        .map(|f| (f.binder.clone(), if f.rec { at.to_string() } else { f.spell.clone() }))
        .collect();
    for (k, i) in SpecView::rec_of(c).iter().enumerate() {
        bs.push((format!("h{k}"), appc(inv, &[c.fields[*i].binder.clone()])));
    }
    bs
}

/// `abs(mk_C(x⃗)) = C(y⃗)` under the law binders, with `abs` at the recursive
/// arguments on the spec side.
fn abs_law_ty(c: &CtorView, at: &str, abs: &str, inv: &str, mk: &str) -> String {
    let bs = law_binders(c, at, inv);
    let args: Vec<String> = c.fields.iter().map(|f| f.binder.clone()).collect();
    let lhs = appc(abs, &[appc(mk, &args)]);
    let spec_args: Vec<String> = c
        .fields
        .iter()
        .map(|f| if f.rec { appc(abs, &[f.binder.clone()]) } else { f.binder.clone() })
        .collect();
    let rhs = if spec_args.is_empty() {
        c.name.clone()
    } else {
        format!("{}({})", c.name, spec_args.join(", "))
    };
    pis(&bs, &format!("{lhs} = {rhs}"))
}

/// `inv(mk_C(x⃗))` under the law binders — the closure half.
fn inv_law_ty(c: &CtorView, at: &str, inv: &str, mk: &str) -> String {
    let bs = law_binders(c, at, inv);
    let args: Vec<String> = c.fields.iter().map(|f| f.binder.clone()).collect();
    pis(&bs, &appc(inv, &[appc(mk, &args)]))
}

/// A law whose content is definitional: `refl` under the statement's binders.
fn refl_under(c: &CtorView, at: &str, inv: &str) -> String {
    lams(&law_binders(c, at, inv), "refl")
}

/// The fold anchor's statement (§1.1, corrected form): the law takes the SPEC
/// step, adapts it repr-ward with `abs` at the child position, and equates the
/// fold with the spec recursor at `abs(r)`.
fn fold_law_ty(spec: &SpecView, at: &str, abs: &str, inv: &str, fold: &str, sr: &str) -> String {
    let s = &spec.spell;
    let mut bs = vec![("B".to_string(), "Type".to_string())];
    for (j, ct) in spec.ctors.iter().enumerate() {
        bs.push((format!("s{j}"), step_ty(ct, s, "B")));
    }
    bs.push(("r".to_string(), at.to_string()));
    bs.push(("h".to_string(), appc(inv, &["r".to_string()])));
    let mut fargs = vec!["B".to_string()];
    for (j, ct) in spec.ctors.iter().enumerate() {
        fargs.push(adapt(ct, at, &format!("s{j}"), abs));
    }
    fargs.push("r".to_string());
    let lhs = appc(fold, &fargs);
    let steps: Vec<String> = (0..spec.ctors.len()).map(|j| format!("s{j}")).collect();
    let rhs = format!("{sr}(B, {}, {})", steps.join(", "), appc(abs, &["r".to_string()]));
    pis(&bs, &format!("{lhs} = {rhs}"))
}

// -- the via-abs fold default (issues/repr-fold-via-abs-default.md) ---------
//
// `fold` is the one clause whose canonical definition is available to every
// repr: fold *through* `abs`, which is what `Bin` writes by hand
// (`nat_rec_(B, s0, λ m b => s1(bin_of_nat(m))(b), bin_abs(r))`). Reading that
// shape schematically, it needs one thing the record does not state — a map
// `S -> R` to put the spec recursor's child back at the carrier, since the
// repr-side step wants it there. That map is not new machinery: it is the spec
// recursor over the constructor **images**, and `bin_of_nat` is exactly it.
//
// The consequence, and the round's finding: the anchor law of the defaulted
// fold is **not** `refl`. `abs ∘ emb = id` is a theorem, not a conversion, so
// the default owes three declarations — the embedding, `inv` of it, and the
// round-trip — plus one induction relating the two recursor calls. All four are
// generated from the repr's own image laws, which is the sharper statement of
// what the default means: at a repr whose images are certified, the fold anchor
// is derivable rather than an independent obligation.

/// The embedding `S -> R`: the spec recursor with the constructor images as
/// its algebra.
fn emb_name(name: &str) -> String {
    format!("{name}_emb")
}

fn emb_inv_name(name: &str) -> String {
    format!("{name}_emb_inv")
}

fn emb_abs_name(name: &str) -> String {
    format!("{name}_emb_abs")
}

fn via_abs_law_name(name: &str) -> String {
    format!("{name}_fold_via_abs")
}

/// `C(a0, a1)`, or `C` — a constructor pattern and a constructor application
/// are the same text.
fn ctor_at(c: &CtorView, args: &[String]) -> String {
    if args.is_empty() {
        c.name.clone()
    } else {
        format!("{}({})", c.name, args.join(", "))
    }
}

fn ctor_pat(c: &CtorView) -> String {
    ctor_at(c, &c.fields.iter().map(|f| f.binder.clone()).collect::<Vec<_>>())
}

/// A chain of one-position rewrites, `trans`-composed. Each link is an explicit
/// `j` whose motive abstracts exactly the position it rewrites, so its `refl`
/// proves the link's left endpoint — the same rule reprgen's certificate chains
/// follow (design §3.1 correction 2: the motive is spelled, never inferred).
/// `None` when there is nothing to rewrite, and the caller supplies `refl`.
fn rewrite_chain(
    args: &[String],
    edits: &[(usize, String, String)],
    render: &dyn Fn(&[String]) -> String,
) -> Option<String> {
    let mut cur = args.to_vec();
    let mut links: Vec<String> = Vec::new();
    for (i, to, p) in edits {
        let lhs = render(&cur);
        let mut mot = cur.clone();
        mot[*i] = "y".to_string();
        links.push(format!("j({p}, \u{3bb} y q => {lhs} = {}, refl)", render(&mot)));
        cur[*i] = to.clone();
    }
    let mut it = links.into_iter().rev();
    let mut acc = it.next()?;
    for l in it {
        acc = format!("trans({l}, {acc})");
    }
    Some(acc)
}

/// The image of a constructor's arguments on each side: the field itself, or
/// the recursive result / the embedded child at a recursive position.
fn image_args(c: &CtorView, at_rec: &dyn Fn(usize, &str) -> String) -> Vec<String> {
    let mut k = 0;
    let mut args = Vec::new();
    for f in &c.fields {
        if f.rec {
            args.push(at_rec(k, &f.binder));
            k += 1;
        } else {
            args.push(f.binder.clone());
        }
    }
    args
}

/// The three declarations the via-abs fold rests on: the embedding, its
/// `inv`-closure and the round-trip `abs ∘ emb = id`. Both lemmas are the same
/// induction shape — one image law per arm, applied to the inductive
/// hypotheses — which is why they are generated together.
fn emb_decls(
    name: &str,
    spec: &SpecView,
    c: &str,
    rec: &str,
    sr: &str,
    abs: &str,
    inv: &str,
) -> String {
    let s = &spec.spell;
    let emb = emb_name(name);
    let emb_inv = emb_inv_name(name);
    let emb_abs = emb_abs_name(name);
    let mut out = String::new();

    // The embedding itself.
    let mut steps = Vec::new();
    for ct in &spec.ctors {
        let mut bs: Vec<(String, String)> =
            ct.fields.iter().map(|f| (f.binder.clone(), f.spell.clone())).collect();
        for (k, _) in SpecView::rec_of(ct).iter().enumerate() {
            bs.push((format!("b{k}"), c.to_string()));
        }
        let args = image_args(ct, &|k, _| format!("b{k}"));
        steps.push(lams(&bs, &appc(&format!("{rec}::mk_{}()", ct.name), &args)));
    }
    out.push_str(&format!(
        "fn {emb}(x: {s}) -> {c} {{ {sr}({c}, {}, x) }}\n",
        steps.join(", ")
    ));

    // `inv` of it: the closure law of each image, applied to the inductive
    // hypotheses. At `inv = True` every arm is inhabited and says nothing; at a
    // canonical-form `inv` this is what the round-trip below is paid with.
    let mut arms = String::new();
    for ct in &spec.ctors {
        let args = image_args(ct, &|_, b| appc(&emb, &[b.to_string()]));
        let mut proof_args = args.clone();
        for i in SpecView::rec_of(ct) {
            proof_args.push(format!("{emb_inv}({})", ct.fields[i].binder));
        }
        arms.push_str(&format!(
            "        {} => {},\n",
            ctor_pat(ct),
            appc(&format!("{rec}::{}_inv()", ct.name), &proof_args)
        ));
    }
    out.push_str(&format!(
        "theorem {emb_inv}(x: {s}): {} {{\n    match x {{\n{arms}    }}\n}}\n",
        appc(inv, &[format!("{emb}(x)")])
    ));

    // The round-trip. One commutation law per arm opens it — that is where the
    // `inv` lemma above is spent — and a `j` chain closes the recursive
    // positions with the inductive hypothesis.
    let mut arms = String::new();
    for ct in &spec.ctors {
        let args = image_args(ct, &|_, b| appc(&emb, &[b.to_string()]));
        let mut law_args = args.clone();
        for i in SpecView::rec_of(ct) {
            law_args.push(format!("{emb_inv}({})", ct.fields[i].binder));
        }
        let opened = appc(&format!("{rec}::{}_abs()", ct.name), &law_args);
        // The law lands at `C(…, abs(emb(a_i)), …)`; each recursive position is
        // then rewritten to `a_i` itself.
        let state = image_args(ct, &|_, b| appc(abs, &[appc(&emb, &[b.to_string()])]));
        let edits: Vec<(usize, String, String)> = SpecView::rec_of(ct)
            .iter()
            .map(|i| {
                let b = &ct.fields[*i].binder;
                (*i, b.clone(), format!("{emb_abs}({b})"))
            })
            .collect();
        let proof = match rewrite_chain(&state, &edits, &|a| ctor_at(ct, a)) {
            Some(chain) => format!("trans({opened}, {chain})"),
            None => opened,
        };
        arms.push_str(&format!("        {} => {proof},\n", ctor_pat(ct)));
    }
    out.push_str(&format!(
        "theorem {emb_abs}(x: {s}): {} = x {{\n    match x {{\n{arms}    }}\n}}\n",
        appc(abs, &[format!("{emb}(x)")])
    ));
    out
}

/// The default `fold`: the spec recursor at `abs(r)`, with each repr-side step
/// handed the embedded child. This is `Bin`'s hand-written `bin_fold`, read
/// schematically.
fn via_abs_fold(name: &str, spec: &SpecView, c: &str, sr: &str, abs: &str) -> String {
    let emb = emb_name(name);
    let mut bs = vec![("B".to_string(), "Type".to_string())];
    for (j, ct) in spec.ctors.iter().enumerate() {
        bs.push((format!("s{j}"), step_ty(ct, c, "B")));
    }
    bs.push(("r".to_string(), c.to_string()));
    let mut args = vec!["B".to_string()];
    args.extend(spec_steps(spec, &|_, b| appc(&emb, &[b.to_string()])));
    args.push(appc(abs, &["r".to_string()]));
    lams(&bs, &format!("{sr}({})", args.join(", ")))
}

/// The spec-side algebra the default fold hands to the recursor: one step per
/// constructor, binding the constructor's fields at their **spec** types and
/// applying the repr-side step `s_j` to `at_rec` of each recursive one.
fn spec_steps(spec: &SpecView, at_rec: &dyn Fn(usize, &str) -> String) -> Vec<String> {
    let mut out = Vec::new();
    for (j, ct) in spec.ctors.iter().enumerate() {
        let mut bs: Vec<(String, String)> =
            ct.fields.iter().map(|f| (f.binder.clone(), f.spell.clone())).collect();
        let recs = SpecView::rec_of(ct);
        for (k, _) in recs.iter().enumerate() {
            bs.push((format!("b{k}"), "B".to_string()));
        }
        let mut args = image_args(ct, at_rec);
        for (k, _) in recs.iter().enumerate() {
            args.push(format!("b{k}"));
        }
        out.push(lams(&bs, &appc(&format!("s{j}"), &args)));
    }
    out
}

/// The anchor law of the defaulted fold, generalized off the carrier.
///
/// Unfolding the default fold turns `fold_law`'s left-hand side into the spec
/// recursor at `abs(r)` over an algebra that reaches its child through
/// `abs ∘ emb`; the right-hand side is the same recursor over the plain
/// algebra. So the law is a statement about the recursor alone, at an arbitrary
/// spec value — an induction whose arms rewrite each `abs(emb(a))` to `a` with
/// the round-trip and each recursive call with the inductive hypothesis.
fn via_abs_law(name: &str, spec: &SpecView, sr: &str, abs: &str) -> String {
    let s = &spec.spell;
    let emb = emb_name(name);
    let emb_abs = emb_abs_name(name);
    let lem = via_abs_law_name(name);
    let mut ps = vec![("B".to_string(), "Type".to_string())];
    for (j, ct) in spec.ctors.iter().enumerate() {
        ps.push((format!("s{j}"), step_ty(ct, s, "B")));
    }
    ps.push(("x".to_string(), s.clone()));
    let plain: Vec<String> = (0..spec.ctors.len()).map(|j| format!("s{j}")).collect();
    let through = spec_steps(spec, &|_, b| appc(abs, &[appc(&emb, &[b.to_string()])]));
    let at = |steps: &[String], x: &str| {
        let mut a = vec!["B".to_string()];
        a.extend(steps.iter().cloned());
        a.push(x.to_string());
        format!("{sr}({})", a.join(", "))
    };
    let ih = |x: &str| {
        let mut a = vec!["B".to_string()];
        a.extend(plain.iter().cloned());
        a.push(x.to_string());
        format!("{lem}({})", a.join(", "))
    };
    let mut arms = String::new();
    for (j, ct) in spec.ctors.iter().enumerate() {
        let recs = SpecView::rec_of(ct);
        // The arm's two sides, reduced: the step applied to the fields — with
        // `abs(emb(·))` at the recursive ones on the left — and then to the
        // recursive calls.
        let mut state = image_args(ct, &|_, b| appc(abs, &[appc(&emb, &[b.to_string()])]));
        for i in &recs {
            state.push(at(&through, &ct.fields[*i].binder));
        }
        let nf = ct.fields.len();
        let mut edits: Vec<(usize, String, String)> = recs
            .iter()
            .map(|i| {
                let b = &ct.fields[*i].binder;
                (*i, b.clone(), format!("{emb_abs}({b})"))
            })
            .collect();
        for (k, i) in recs.iter().enumerate() {
            let b = &ct.fields[*i].binder;
            edits.push((nf + k, at(&plain, b), ih(b)));
        }
        let step = format!("s{j}");
        let proof = rewrite_chain(&state, &edits, &|a| appc(&step, a))
            .unwrap_or_else(|| "refl".to_string());
        arms.push_str(&format!("        {} => {proof},\n", ctor_pat(ct)));
    }
    format!(
        "theorem {lem}({}): {} = {} {{\n    match x {{\n{arms}    }}\n}}\n",
        params_src(&ps),
        at(&through, "x"),
        at(&plain, "x")
    )
}

// -- substituting an inductive's type parameters ----------------------------

/// Instantiating a stored field type at the declaration's arguments. Type
/// parameters are monomorphized, so this is a rename on the surface type — the
/// same move `traits::rename_ty` makes for a parent class's fields, over the
/// larger map a `datarepr`'s arguments need (a parameter goes to a *type*, not
/// to another name).
pub(crate) fn subst_ty(t: &Ty, m: &HashMap<&str, String>) -> Ty {
    let kind = match &t.kind {
        TyKind::Named { name, args } if args.is_empty() => match m.get(name.as_str()) {
            // The substituted type is re-parsed from its spelling rather than
            // cloned: the argument is a `Ty` from the declaration site and its
            // spans belong to that file.
            Some(s) => TyKind::Named { name: s.clone(), args: Vec::new() },
            None => TyKind::Named { name: name.clone(), args: Vec::new() },
        },
        TyKind::Named { name, args } => TyKind::Named {
            name: name.clone(),
            args: args.iter().map(|a| subst_ty(a, m)).collect(),
        },
        TyKind::Fn { binder, implicit, dom, cod } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(subst_ty(dom, m)),
            cod: Box::new(subst_ty(cod, m)),
        },
        k => k.clone(),
    };
    Ty { kind, span: t.span }
}

// -- the cost basis: `impl f for Rp` ----------------------------------------

/// §1.2's statement schema at one `(operation, repr)` pair, as spelled source.
///
/// One computation, two consumers, per `docs/obligation-records-design.md` §2.1
/// (FINDING A): `elab_impl` declares the obligations from it and the transfer
/// generator's phase 3 states the derived ones from it, and before the
/// extraction each had its own copy of the same paragraph. Everything is a
/// `String` because the statements have to be *written back out* — a `?` prints
/// one, the obligations listing prints one, and the generated declaration is
/// checked against one — and a kernel term would have to be decoded to do any
/// of that (§1.3, §6).
pub(crate) struct ImplSchema {
    pub op: String,
    /// `Impl_<repr>_<op>`: the namespace the obligations are declared in.
    pub record: String,
    /// The signature with `S ↦ R` at every occurrence (v1 rule), in
    /// declaration order.
    pub binders: Vec<(String, String)>,
    /// The parameters that landed at the carrier, in declaration order.
    pub at_repr: Vec<String>,
    /// One `inv` hypothesis per repr-typed parameter, `(h0, inv(x))` — every
    /// law quantifies over `inv`-satisfying inputs (§1.1).
    pub hyps: Vec<(String, String)>,
    /// The spec-side arguments: `abs(x)` at a repr-typed parameter, the binder
    /// itself elsewhere.
    pub spec_args: Vec<String>,
    /// The result spelled repr-ward — the carrier at a repr-typed result.
    pub result: String,
    /// The result is the spec type: the two-conclusion case (§1.2).
    pub res_is_spec: bool,
    /// `Repr_N::abs()`, `Repr_N::inv()`.
    pub abs: String,
    pub inv: String,
}

impl ImplSchema {
    /// The binder names, in order.
    pub fn args(&self) -> Vec<String> {
        self.binders.iter().map(|(n, _)| n.clone()).collect()
    }

    /// `head(x1)(x2)` — an implementation applied to the signature's binders.
    pub fn call(&self, head: &str) -> String {
        appc(head, &self.args())
    }

    /// `f(⟦x̄⟧)` — the spec side of every conclusion.
    pub fn spec_call(&self) -> String {
        format!("{}({})", self.op, self.spec_args.join(", "))
    }

    /// Everything the conclusions quantify over: the signature, then the `inv`
    /// hypotheses.
    pub fn law_binders(&self) -> Vec<(String, String)> {
        let mut law = self.binders.clone();
        law.extend(self.hyps.iter().cloned());
        law
    }

    pub fn body_ty(&self) -> String {
        pis(&self.binders, &self.result)
    }

    /// §1.2's first conclusion, with `call` standing for the implementation:
    /// `abs(call) = f(⟦x̄⟧)` at a repr-typed result, `call = f(⟦x̄⟧)` otherwise.
    pub fn refines_concl(&self, call: &str) -> String {
        if self.res_is_spec {
            format!("{} = {}", appc(&self.abs, &[call.to_string()]), self.spec_call())
        } else {
            format!("{call} = {}", self.spec_call())
        }
    }

    /// §1.2's second conclusion, which exists only at a repr-typed result: an
    /// implementation that *builds* a repr owes `inv` of what it built.
    pub fn inv_concl(&self, call: &str) -> String {
        appc(&self.inv, &[call.to_string()])
    }

    pub fn refines_ty(&self, call: &str) -> String {
        pis(&self.law_binders(), &self.refines_concl(call))
    }

    pub fn inv_ty(&self, call: &str) -> String {
        pis(&self.law_binders(), &self.inv_concl(call))
    }

    /// The obligation's printed path (design §3): `::` because an obligation is
    /// a member of its owner's namespace. Print-only in v1 — nothing parses it.
    pub fn path(&self, repr: &str, field: &str) -> String {
        format!("Impl({}, {repr})::{field}", self.op)
    }
}

impl Elaborator {
    /// Build §1.2's schema at `(op, repr)`. Both callers have already checked
    /// that the repr and the declaration are in scope and that the operation is
    /// monomorphic — with their own messages, which differ deliberately — so
    /// what is left here is the spelling.
    pub(crate) fn impl_schema(&self, op: &str, repr: &str) -> Result<ImplSchema, String> {
        let rp = self
            .datarepr_by_name
            .get(repr)
            .ok_or_else(|| format!("`{repr}` is not a `datarepr` in scope"))?;
        let f = self
            .decls
            .get(op)
            .ok_or_else(|| format!("`{op}` is not a declared function here"))?;
        let s = &rp.written;
        let c = &rp.carrier;
        let abs = format!("{}::abs()", rp.record);
        let inv = format!("{}::inv()", rp.record);
        let mut binders: Vec<(String, String)> = Vec::new();
        let mut at_repr: Vec<String> = Vec::new();
        let mut spec_args: Vec<String> = Vec::new();
        for p in &f.params {
            let Some(t) = spell_ty(&p.ty) else {
                return Err(format!(
                    "`{op}`'s parameter `{}` has a type this round cannot spell",
                    p.name
                ));
            };
            if t == *s {
                binders.push((p.name.clone(), c.clone()));
                at_repr.push(p.name.clone());
                spec_args.push(appc(&abs, &[p.name.clone()]));
            } else {
                binders.push((p.name.clone(), t));
                spec_args.push(p.name.clone());
            }
        }
        let Some(res) = spell_ty(&f.result) else {
            return Err(format!("`{op}`'s result type cannot be spelled"));
        };
        let res_is_spec = res == *s;
        let hyps = at_repr
            .iter()
            .enumerate()
            .map(|(k, x)| (format!("h{k}"), appc(&inv, &[x.clone()])))
            .collect();
        Ok(ImplSchema {
            op: op.to_string(),
            record: impl_record_name(repr, op),
            binders,
            at_repr,
            hyps,
            spec_args,
            result: if res_is_spec { c.clone() } else { res },
            res_is_spec,
            abs,
            inv,
        })
    }
}

impl Elaborator {
    /// `impl f for Rp { body := …, refines := … }` (design §1.2).
    ///
    /// The registry is **open by construction**: the operation is an index, so
    /// each `Impl` is its own generated record and there is no closed field
    /// list anywhere to amend when a new operation gets an implementation.
    /// Keyed per §4 on (repr name, operation) — see the as-landed note there
    /// about the operation half being its resolved name rather than its
    /// `.code`.
    pub(crate) fn elab_impl(&mut self, d: &heather_syntax::ImplDecl) -> R<()> {
        let Some(rp) = self.datarepr_by_name.get(&d.repr).cloned() else {
            return err(
                format!("`{}` is not a `datarepr` in scope", d.repr),
                d.span,
            );
        };
        let Some(f) = self.decls.get(&d.op).cloned() else {
            return err(
                format!(
                    "`{}` is not a declared function here: an `Impl` restates its \
                     signature, so the declaration has to be in scope",
                    d.op
                ),
                d.span,
            );
        };
        if !f.tyvars.is_empty() {
            return err(
                format!(
                    "`{}` is polymorphic: an `Impl` at a v1 repr is over a monomorphic \
                     operation (docs/datarepr-design.md §5.1)",
                    d.op
                ),
                d.span,
            );
        }
        if self.impls.contains_key(&(d.repr.clone(), d.op.clone())) {
            return err(
                format!("`{}` already has an implementation at `{}`", d.op, d.repr),
                d.span,
            );
        }
        let fields = match &d.body {
            DatareprBody::Mint(e) => return self.elab_impl_derive(d, e),
            DatareprBody::Fields(fs) => fs,
        };
        // The signature with `S ↦ R` at every occurrence (v1 rule: *all*
        // occurrences, per-position mixing deferred), and §1.2's conclusions —
        // one computation, shared with the transfer generator (§2.1).
        let s = &rp.written;
        let sch = match self.impl_schema(&d.op, &d.repr) {
            Ok(sch) => sch,
            Err(msg) => return err(msg, d.span),
        };
        let res_is_spec = sch.res_is_spec;
        // As in `elab_datarepr`: the paths exist as soon as the schema does,
        // which is before the first thing that prints a statement.
        self.register_impl_access(&d.op, &d.repr, res_is_spec);
        let body_ty = sch.body_ty();
        let rec = sch.record.clone();
        let bodyg = format!("{rec}::body()");
        // At `Y = S` there are two conclusions, and they are two fields rather
        // than a conjunction because there is no conjunction to be had without
        // a library.
        let refines_ty = sch.refines_ty(&sch.call(&bodyg));
        let inv_ty = sch.inv_ty(&sch.call(&bodyg));

        let owner = format!("impl {} for {}", d.op, d.repr);
        let mut sp = Splices::default();
        let mut holes: Vec<Hole> = Vec::new();
        let mut prov: HashMap<String, Provenance> = HashMap::new();
        let mut by: HashMap<String, (String, Span)> = HashMap::new();
        // `refines := via_derived(p)` (§4.3): recognised here rather than
        // spliced, because it is the one clause whose *statement* is not the
        // field's — the user proves the weak abs-image equation and the
        // certificate is composed from it.
        let mut via: Option<(&Expr, Span)> = None;
        for cl in fields {
            if cl.is_mk {
                return err("an `Impl` has no `mk` clauses".to_string(), cl.span);
            }
            if by.contains_key(&cl.name) || (cl.name == "refines" && via.is_some()) {
                return err(format!("duplicate clause `{}`", cl.name), cl.span);
            }
            if cl.name == "refines"
                && let Some(arg) = route_call(&cl.expr, "via_derived")
            {
                let [arg] = arg else {
                    return err(
                        "`via_derived` takes one argument: the proof that this \
                         implementation and the derived one have the same image under \
                         `abs` (docs/obligation-records-design.md §4.3)"
                            .to_string(),
                        cl.expr.span,
                    );
                };
                via = Some((arg, cl.span));
                prov.insert(cl.name.clone(), Provenance::ViaDerived);
                continue;
            }
            if let ExprKind::Hole(label) = &cl.expr.kind {
                if cl.name != "refines" && cl.name != "refines_inv" {
                    return err(hole_on_data_field(&cl.name), cl.expr.span);
                }
                holes.push(Hole {
                    owner: owner.clone(),
                    path: sch.path(&d.repr, &cl.name),
                    field: cl.name.clone(),
                    label: label.clone(),
                    span: cl.expr.span,
                });
            }
            prov.insert(
                cl.name.clone(),
                if matches!(cl.expr.kind, ExprKind::Var(_)) {
                    Provenance::Named
                } else {
                    Provenance::Inline
                },
            );
            by.insert(cl.name.clone(), (sp.add(&cl.name, cl.span, &cl.expr), cl.span));
        }
        let Some((body, _)) = by.remove("body") else {
            return err(format!("`impl {} for {}` needs a `body`", d.op, d.repr), d.span);
        };
        let refines = by.remove("refines").map(|(t, _)| t);
        if refines.is_none() && via.is_none() {
            return err(
                format!("`impl {} for {}` needs a `refines` (design §1.2)", d.op, d.repr),
                d.span,
            );
        }
        let refines_inv = by.remove("refines_inv").map(|(t, _)| t);
        if res_is_spec && refines_inv.is_none() {
            // The via-derived route names *why* it cannot fill this one: an
            // abs-image equation says nothing about `inv` of what was built,
            // which is exactly what a non-injective `abs` costs (§4.3).
            let why = if via.is_some() {
                format!(
                    "`impl {} for {}` returns `{s}`, so it also needs a `refines_inv`, and \
                     `via_derived` cannot fill it: `inv(body(x̄))` does not follow from an \
                     abs-image equation — that is what a non-injective `abs` costs \
                     (docs/obligation-records-design.md §4.3). Write it, or prove carrier \
                     equality instead",
                    d.op, d.repr
                )
            } else {
                format!(
                    "`impl {} for {}` returns `{s}`, so it also needs a `refines_inv`: \
                     an implementation that *builds* a repr owes `inv` of what it built \
                     (design §1.2)",
                    d.op, d.repr
                )
            };
            return err(why, d.span);
        }
        if let Some((k, (_, span))) = by.iter().next() {
            return err(
                format!("`{k}` is not a clause of an `Impl`: the clauses are `body`, \
                         `refines` and (at a repr-typed result) `refines_inv`"),
                *span,
            );
        }

        let mut src = String::new();
        let mut fields = vec![format!("    body: {body_ty}")];
        // Stated against the record's own `body` field, so the record type is
        // self-contained and reads as the obligation it is.
        let selfcall = sch.call("body");
        fields.push(format!("    refines: {}", sch.refines_ty(&selfcall)));
        if res_is_spec {
            fields.push(format!("    refines_inv: {}", sch.inv_ty(&selfcall)));
        }
        // The obligations, recorded as they are stated (§1.1): a `?` prints one
        // and the listing prints them all.
        // A route that wrote the whole declaration (`derive()`) owns every
        // field's provenance; otherwise it is per clause.
        let route = self.impl_provenance;
        let mut obs =
            vec![obligation_row(&owner, &sch, &d.repr, "refines", &refines_ty, &prov, route)];
        if res_is_spec {
            obs.push(obligation_row(&owner, &sch, &d.repr, "refines_inv", &inv_ty, &prov, route));
        }
        for o in &mut obs {
            o.statement = self.display_paths(&o.statement);
        }
        if let Some(h) = holes.first() {
            return hole_error(&obs, h);
        }
        src.push_str(&format!("record {rec} {{\n{}\n}}\n\n", fields.join(",\n")));
        src.push_str(&format!("fn {rec}::body() -> {body_ty} {{ {body} }}\n"));
        let provenance = match &via {
            Some(_) => Provenance::ViaDerived,
            None if prov.values().any(|p| *p == Provenance::Inline) => Provenance::Inline,
            None => Provenance::Named,
        };
        match (&refines, &via) {
            (Some(refines), _) => {
                src.push_str(&format!(
                    "theorem {rec}::refines(): {refines_ty} {{ {refines} }}\n"
                ));
            }
            // §4.3: derive, state the weak abs-image equation, and compose.
            (None, Some((arg, span))) => {
                let em = match self.reprgen(&d.op, &d.repr) {
                    Ok(em) => em,
                    Err(why) => {
                        return err(
                            format!(
                                "`refines := via_derived(…)` at `impl {} for {}` needs the \
                                 derived `Impl` to compose with, and generating one \
                                 declines: {why}",
                                d.op, d.repr
                            ),
                            *span,
                        )
                    }
                };
                // The derived artifacts WITHOUT the transfer's own `impl`
                // block: at one key there is only ever one `Impl` and this
                // declaration is it (design FINDING E), so the route consumes
                // reprgen's certificate, not its registration.
                let mut pre = em.text[..em.impl_at].to_string();
                pre.push('\n');
                pre.push_str(&src);
                src = pre;
                let derived_call = appc(&em.body, &sch.args());
                let obl = pis(
                    &sch.law_binders(),
                    &if res_is_spec {
                        format!(
                            "{} = {}",
                            appc(&sch.abs, &[sch.call(&bodyg)]),
                            appc(&sch.abs, &[derived_call.clone()])
                        )
                    } else {
                        format!("{} = {derived_call}", sch.call(&bodyg))
                    },
                );
                let obg = format!("{rec}::via_derived_obligation()");
                src.push_str(&format!("theorem {obg}: {obl} {{ {} }}\n", sp.add("refines", *span, arg)));
                // The derived certificate quantifies over ONE `inv`
                // hypothesis, at the parameter the transfer recursed on; the
                // schema's hypotheses are one per repr-typed parameter, so the
                // right one is found by name and not by position.
                let k = sch.at_repr.iter().position(|x| *x == em.rec_param).unwrap_or(0);
                let mut dargs = sch.args();
                dargs.push(sch.hyps[k].0.clone());
                let law = sch.law_binders();
                src.push_str(&format!(
                    "theorem {rec}::refines(): {refines_ty} {{ {} }}\n",
                    lams(
                        &law,
                        &format!(
                            "trans({}, {}({}))",
                            appc(&obg, &law.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>()),
                            em.refines,
                            dargs.join(", ")
                        )
                    )
                ));
            }
            (None, None) => unreachable!("checked above"),
        }
        let mut lit = vec![
            format!("body: {rec}::body()"),
            format!("refines: {rec}::refines()"),
        ];
        if let Some(ri) = &refines_inv {
            src.push_str(&format!("theorem {rec}::refines_inv(): {inv_ty} {{ {ri} }}\n"));
            lit.push(format!("refines_inv: {rec}::refines_inv()"));
        }
        let global = format!("{}_{}_impl", d.repr, d.op);
        src.push_str(&format!("\nfn {global}() -> {rec} {{ {rec} {{ {} }} }}\n", lit.join(", ")));
        self.elab_generated(&src, &owner, d.span, &sp)?;
        self.register_impl(&d.repr, &d.op, global, provenance);
        self.obligations.extend(obs);
        Ok(())
    }

    /// `impl f for Rp := derive();` (§4.3) — the pinning form, and the first
    /// transfer requested from surface source.
    ///
    /// The transfer generator is already a pure function from the registries to
    /// text, so this is a *caller*: elaborate the emission — whose own `impl`
    /// block is what registers the result — or fail at the declaration with the
    /// decline reason **verbatim**, which is what lets a tool tell "the fragment
    /// does not cover this" from "you have not proved it yet" (§6).
    fn elab_impl_derive(&mut self, d: &heather_syntax::ImplDecl, e: &Expr) -> R<()> {
        if route_call(e, "derive").map(|a| a.is_empty()) != Some(true) {
            return err(
                format!(
                    "`{}` is not a route this round knows: an `impl` body is `derive()` \
                     (docs/obligation-records-design.md §4.3), and everything else is \
                     written as clauses",
                    spell_expr(e).unwrap_or_else(|| "this expression".into())
                ),
                e.span,
            );
        }
        let em = match self.reprgen(&d.op, &d.repr) {
            Ok(em) => em,
            Err(why) => {
                return err(
                    format!("`impl {} for {} := derive()` declines: {why}", d.op, d.repr),
                    d.span,
                )
            }
        };
        let owner = format!("impl {} for {}", d.op, d.repr);
        // The emission's `impl` block lands through the ordinary path below,
        // which is what records the registry entry; this says who wrote it.
        self.impl_provenance = Some(Provenance::Derived);
        let r = self.elab_generated(&em.text, &owner, d.span, &Splices::default());
        self.impl_provenance = None;
        r
    }

    fn register_impl(&mut self, repr: &str, op: &str, global: String, prov: Provenance) {
        let provenance = self.impl_provenance.unwrap_or(prov);
        self.impls.insert(
            (repr.to_string(), op.to_string()),
            ImplEntry { global, provenance },
        );
    }

    /// The `Impl` registered for `op` at repr `rp`, if any — the
    /// "find the `Impl` for `f` at `Rp`" query of §1.4 item 3. The consumers
    /// are the transfer generator and the compiler walk; nothing in the
    /// surface path reads it.
    pub fn impl_global(&self, repr: &str, op: &str) -> Option<&str> {
        self.impls.get(&(repr.to_string(), op.to_string())).map(|e| e.global.as_str())
    }

    /// How that `Impl` came to be (§4.4). For humans and tools only — the Q2
    /// verdict's "distinguish provenance on inspection"; no certificate and no
    /// resolution consults it.
    pub fn impl_provenance_of(&self, repr: &str, op: &str) -> Option<Provenance> {
        self.impls.get(&(repr.to_string(), op.to_string())).map(|e| e.provenance)
    }

    /// Every obligation of every obligation-bearing declaration elaborated so
    /// far, in declaration order — `heather obligations` (§6).
    pub fn obligations(&self) -> &[Obligation] {
        &self.obligations
    }
}

/// One row of the ledger for an `impl`'s field.
fn obligation_row(
    owner: &str,
    sch: &ImplSchema,
    repr: &str,
    field: &str,
    statement: &str,
    prov: &HashMap<String, Provenance>,
    route: Option<Provenance>,
) -> Obligation {
    Obligation {
        owner: owner.to_string(),
        path: sch.path(repr, field),
        field: field.to_string(),
        state: "supplied",
        provenance: route.or_else(|| prov.get(field).copied()),
        statement: statement.to_string(),
    }
}

/// `derive()` / `via_derived(p)` in clause position: an ordinary application of
/// an ordinary name, which is the point (§4.3 — the two routes are written as
/// the metafunctions they are meant to become, and the elaborator's two special
/// powers over them, expected-type synthesis and the derive-if-absent effect,
/// are the only things keeping them special).
fn route_call<'a>(e: &'a Expr, name: &str) -> Option<&'a [Expr]> {
    match &e.kind {
        ExprKind::App { head, args, .. } => match &head.kind {
            ExprKind::Var(n) if n == name => Some(args),
            _ => None,
        },
        _ => None,
    }
}
