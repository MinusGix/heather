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
        let clauses = self.clauses_of(d, &spec)?;
        let src = generate(&d.name, &spec, &clauses);
        self.elab_generated(&src, &format!("datarepr {}", d.name), d.span)?;
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
    fn clauses_of(&self, d: &DatareprDecl, spec: &SpecView) -> R<Clauses> {
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
            DatareprBody::Fields(fs) => self.written_clauses(d, spec, fs),
        }
    }

    fn written_clauses(
        &self,
        d: &DatareprDecl,
        spec: &SpecView,
        fs: &[DatareprField],
    ) -> R<Clauses> {
        // `mk C` and a plain clause `C` are different clauses; the `mk` ones
        // key under a prefix containing a space, which no clause name has.
        let mut by_name: HashMap<String, (String, Span)> = HashMap::new();
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
            let Some(text) = spell_expr(&f.expr) else {
                return err(
                    format!(
                        "clause `{key}` is not a shape this round can spell into the \
                         generated repr: write it as a name, a call or a projection, \
                         binding anything larger to a `fn` first"
                    ),
                    f.span,
                );
            };
            by_name.insert(key, (text, f.span));
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
        let inv = req("inv", &mut by_name, &mut missing);
        let fold = req("fold", &mut by_name, &mut missing);
        let mut mks = Vec::new();
        for c in &spec.ctors {
            mks.push(req(&format!("mk {}", c.name), &mut by_name, &mut missing));
        }
        if !missing.is_empty() {
            return err(
                format!(
                    "`datarepr {}` is missing {}: a repr's correctness basis is \
                     `R`, `abs`, `inv`, `fold` and one `mk` per constructor \
                     (docs/datarepr-design.md §1.1)",
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
        Ok(Clauses { carrier, abs, inv, mks, laws, fold, fold_law })
    }

    /// Parse and elaborate generated source in the *current* module and scope.
    /// A failure here is a failure of the `datarepr` declaration, reported
    /// against it — the generated text is an implementation detail, so it is
    /// named in the message rather than shown.
    fn elab_generated(&mut self, src: &str, what: &str, span: Span) -> R<()> {
        let file = match parse_file(src) {
            Ok(f) => f,
            Err(e) => {
                return err(
                    format!("`datarepr {what}` generated source that does not parse: {}", e.msg),
                    span,
                )
            }
        };
        for item in &file.items {
            let (r, isp) = match item {
                Item::Decl(d) => (self.elab_decl(d), d.span),
                Item::Inductive(i) => (self.elab_inductive(i), i.span),
                _ => unreachable!("the generator emits declarations and records only"),
            };
            if let Err(e) = r {
                self.pending_derived.borrow_mut().clear();
                // The generated declaration is quoted. It is the *obligation*
                // the writer owes — a repr's law, restated at their carrier —
                // so without it the diagnostic names a field and shows
                // nothing, and the field's statement is exactly what is not
                // obvious.
                return err(
                    format!(
                        "`{what}`: {}\n  in the generated declaration:\n    {}",
                        e.message(),
                        src[isp.start..isp.end].replace('\n', "\n    ")
                    ),
                    span,
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
    fold: String,
    fold_law: Option<String>,
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
        fold: {
            let mut bs = vec![("B".to_string(), "Type".to_string())];
            for (j, c) in spec.ctors.iter().enumerate() {
                bs.push((format!("s{j}"), step_ty(c, s, "B")));
            }
            bs.push(("r".to_string(), s.clone()));
            let args: Vec<String> = (0..spec.ctors.len()).map(|j| format!("s{j}")).collect();
            lams(&bs, &format!("{}(B, {}, r)", spec_rec_name(name), args.join(", ")))
        },
        fold_law: None,
    }
}

fn is_naive_call(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::App { head, args, .. } => args.is_empty() && is_naive_call(head),
        ExprKind::Var(n) => n == "repr::naive",
        _ => false,
    }
}

/// A clause expression, back into source. Deliberately **not**
/// `traits::render_expr`: that is a diagnostic renderer whose fallback is
/// `_`, which here would parse back as a *hole* and could be silently
/// inferred into something the user never wrote. Every shape this does not
/// spell is a decline instead.
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
fn generate(name: &str, spec: &SpecView, cl: &Clauses) -> String {
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
    for (ct, (la, li)) in spec.ctors.iter().zip(cl.laws.iter()) {
        let ty = abs_law_ty(ct, c, &abs, &inv, &mkg(ct));
        out.push_str(&format!(
            "theorem {rec}::{}_abs(): {ty} {{ {} }}\n",
            ct.name,
            la.clone().unwrap_or_else(|| refl_under(ct, c, &inv))
        ));
        let ty = inv_law_ty(ct, c, &inv, &mkg(ct));
        out.push_str(&format!(
            "theorem {rec}::{}_inv(): {ty} {{ {} }}\n",
            ct.name,
            li.clone().unwrap_or_else(|| refl_under(ct, c, &inv))
        ));
    }
    let mut fb = vec![("B".to_string(), "Type".to_string())];
    for (j, ct) in spec.ctors.iter().enumerate() {
        fb.push((format!("s{j}"), step_ty(ct, c, "B")));
    }
    fb.push(("r".to_string(), c.clone()));
    out.push_str(&format!("fn {rec}::fold() -> {} {{ {} }}\n", pis(&fb, "B"), cl.fold));
    {
        let ty = fold_law_ty(spec, c, &abs, &inv, &format!("{rec}::fold()"), &sr);
        let body = cl.fold_law.clone().unwrap_or_else(|| {
            let mut bs = vec![("B".to_string(), "Type".to_string())];
            for (j, ct) in spec.ctors.iter().enumerate() {
                bs.push((format!("s{j}"), step_ty(ct, s, "B")));
            }
            bs.push(("r".to_string(), c.clone()));
            bs.push(("h".to_string(), appc(&inv, &["r".to_string()])));
            lams(&bs, "refl")
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
        // The signature with `S ↦ R` at every occurrence (v1 rule: *all*
        // occurrences, per-position mixing deferred).
        let s = &rp.written;
        let c = &rp.carrier;
        let abs = format!("{}::abs()", rp.record);
        let inv = format!("{}::inv()", rp.record);
        let mut binders: Vec<(String, String)> = Vec::new();
        let mut at_repr: Vec<String> = Vec::new();
        let mut spec_args: Vec<String> = Vec::new();
        for p in &f.params {
            let Some(t) = spell_ty(&p.ty) else {
                return err(
                    format!("`{}`'s parameter `{}` has a type this round cannot spell", d.op, p.name),
                    d.span,
                );
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
            return err(format!("`{}`'s result type cannot be spelled", d.op), d.span);
        };
        let res_is_spec = res == *s;
        let mut hyps: Vec<(String, String)> = Vec::new();
        for (k, x) in at_repr.iter().enumerate() {
            hyps.push((format!("h{k}"), appc(&inv, &[x.clone()])));
        }
        let body_ty =
            pis(&binders, if res_is_spec { c } else { &res });
        let rec = format!("Impl_{}_{}", d.repr, d.op);
        let bodyg = format!("{rec}::body()");
        let call = appc(&bodyg, &binders.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>());
        let fcall = format!("{}({})", d.op, spec_args.join(", "));
        let mut law = binders.clone();
        law.extend(hyps.clone());
        // §1.2's conclusion, by result type. At `Y = S` there are two of them,
        // and they are two fields rather than a conjunction because there is
        // no conjunction to be had without a library.
        let refines_ty = pis(
            &law,
            &if res_is_spec {
                format!("{} = {fcall}", appc(&abs, &[call.clone()]))
            } else {
                format!("{call} = {fcall}")
            },
        );
        let inv_ty = pis(&law, &appc(&inv, &[call.clone()]));

        let mut by: HashMap<String, (String, Span)> = HashMap::new();
        for cl in &d.fields {
            if cl.is_mk {
                return err("an `Impl` has no `mk` clauses".to_string(), cl.span);
            }
            let Some(text) = spell_expr(&cl.expr) else {
                return err(
                    format!("clause `{}` is not a shape this round can spell", cl.name),
                    cl.span,
                );
            };
            if by.insert(cl.name.clone(), (text, cl.span)).is_some() {
                return err(format!("duplicate clause `{}`", cl.name), cl.span);
            }
        }
        let Some((body, _)) = by.remove("body") else {
            return err(format!("`impl {} for {}` needs a `body`", d.op, d.repr), d.span);
        };
        let Some((refines, _)) = by.remove("refines") else {
            return err(
                format!("`impl {} for {}` needs a `refines` (design §1.2)", d.op, d.repr),
                d.span,
            );
        };
        let refines_inv = by.remove("refines_inv").map(|(t, _)| t);
        if res_is_spec && refines_inv.is_none() {
            return err(
                format!(
                    "`impl {} for {}` returns `{s}`, so it also needs a `refines_inv`: \
                     an implementation that *builds* a repr owes `inv` of what it built \
                     (design §1.2)",
                    d.op, d.repr
                ),
                d.span,
            );
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
        let selfcall = appc("body", &binders.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>());
        fields.push(format!(
            "    refines: {}",
            pis(
                &law,
                &if res_is_spec {
                    format!("{} = {fcall}", appc(&abs, &[selfcall.clone()]))
                } else {
                    format!("{selfcall} = {fcall}")
                }
            )
        ));
        if res_is_spec {
            fields.push(format!("    refines_inv: {}", pis(&law, &appc(&inv, &[selfcall]))));
        }
        src.push_str(&format!("record {rec} {{\n{}\n}}\n\n", fields.join(",\n")));
        src.push_str(&format!("fn {rec}::body() -> {body_ty} {{ {body} }}\n"));
        src.push_str(&format!("theorem {rec}::refines(): {refines_ty} {{ {refines} }}\n"));
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
        self.elab_generated(&src, &format!("impl {} for {}", d.op, d.repr), d.span)?;
        self.impls.insert((d.repr.clone(), d.op.clone()), global);
        Ok(())
    }

    /// The `Impl` registered for `op` at repr `rp`, if any — the
    /// "find the `Impl` for `f` at `Rp`" query of §1.4 item 3. The consumers
    /// are the transfer generator and the compiler walk; nothing in the
    /// surface path reads it.
    pub fn impl_global(&self, repr: &str, op: &str) -> Option<&str> {
        self.impls.get(&(repr.to_string(), op.to_string())).map(|s| s.as_str())
    }
}
