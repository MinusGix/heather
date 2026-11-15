//! Mutual inductive families (`docs/inductives/mutual-inductive-design.md`): a group of
//! `inductive` declarations that mention one another, lowered to **one**
//! `IWf`-route family indexed by the sum of the members' indices.
//!
//! Nothing here builds a kernel term. A group is two generated surface
//! declarations, elaborated by the ordinary routes (§2):
//!
//! ```text
//! inductive D_1#members { D_1#member(n: I_1), …, D_k#member }        (tier 0)
//! inductive D_1#mutual<p̄> : (j: D_1#members) -> Type { every constructor,
//!     each member occurrence E<p̄>(e) rewritten to D_1#mutual<p̄>(E#member(e)) }
//! ```
//!
//! and each member is a **view** of the family at its index constructor,
//! resolved where a type is named ([`MutualFamily::lower_member`]). What this
//! module owns is the surface: forming the group (§1), the member-level
//! refusals, each in the member's terms rather than the generated family's,
//! and the rewrite. The doctrine is the tiers': the rewrite is untrusted, the
//! kernel re-checks every term the routes emit, and a refusal names what the
//! user wrote.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::ast::{CtorDecl, FieldDecl, InductiveDecl, Item};
use heather_syntax::{Expr, ExprKind, Span, Ty, TyKind};

use crate::inductive::{IdxTy, Inductive, Member, expr_mentions, named_head, occurs};
use crate::names::NameKind;
use crate::{Cx, Elaborator, R, err};
use crate::iwf_family::IwfFamily;
use crate::inductive::Inductives;
use crate::name_lookup::NameLookup;
use crate::inductive::InductivesMut;

/// The generated family's name (§2).
pub(crate) fn family_name(first: &str) -> String {
    format!("{first}#mutual")
}

/// The generated index type's name: one constructor per member (§2).
pub(crate) fn members_name(first: &str) -> String {
    format!("{first}#members")
}

/// Member `name`'s index constructor (§2).
pub(crate) fn member_ctor_name(name: &str) -> String {
    format!("{name}#member")
}

/// The groups of §1: within each maximal run of consecutive `inductive`
/// items, the strongly connected components of size > 1 under "a field or a
/// result annotation names", as item indices in declaration order. A
/// singleton is not a group and is elaborated as it always was.
///
/// Syntactic, like `measure_groups`: a mis-grouping costs a refusal, never a
/// wrong lowering, since a group is only ever elaborated through the routes.
pub(crate) fn inductive_groups(items: &[Item]) -> Vec<Vec<usize>> {
    let mut groups = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let start = i;
        while i < items.len() && matches!(&items[i], Item::Inductive(_)) {
            i += 1;
        }
        if i == start {
            i += 1;
            continue;
        }
        let run: Vec<&InductiveDecl> = items[start..i]
            .iter()
            .map(|it| match it {
                Item::Inductive(d) => d,
                _ => unreachable!("the run holds inductives only"),
            })
            .collect();
        for comp in strongly_connected(&run) {
            if comp.len() > 1 {
                groups.push(comp.into_iter().map(|b| start + b).collect());
            }
        }
    }
    groups
}

/// The components of a run, each in declaration order, components ordered by
/// their first member.
fn strongly_connected(run: &[&InductiveDecl]) -> Vec<Vec<usize>> {
    let n = run.len();
    // `reach[a][b]`: `a` names `b`, transitively. Runs are a handful of
    // declarations, so the closure is cheaper than a Tarjan.
    let mut reach = vec![vec![false; n]; n];
    for (a, d) in run.iter().enumerate() {
        for (b, e) in run.iter().enumerate() {
            reach[a][b] = mentions(d, &e.name);
        }
    }
    for k in 0..n {
        for a in 0..n {
            for b in 0..n {
                if reach[a][k] && reach[k][b] {
                    reach[a][b] = true;
                }
            }
        }
    }
    let mut taken = vec![false; n];
    let mut comps = Vec::new();
    for a in 0..n {
        if taken[a] {
            continue;
        }
        let comp: Vec<usize> = (a..n)
            .filter(|&b| b == a || (reach[a][b] && reach[b][a]))
            .collect();
        for &b in &comp {
            taken[b] = true;
        }
        comps.push(comp);
    }
    comps
}

/// Does `d` name `other` in a field type or a result annotation?
fn mentions(d: &InductiveDecl, other: &str) -> bool {
    d.ctors.iter().any(|c| {
        c.fields.iter().any(|f| occurs(&f.ty, other).is_some())
            || c.result.as_ref().is_some_and(|r| expr_mentions(r, other))
    })
}

/// One member's surface, validated: its index binder and the binder's type,
/// for an indexed member.
struct MemberHead<'a> {
    decl: &'a InductiveDecl,
    index: Option<(String, Ty)>,
}

/// How a field mentions the group, once validated.
enum Occurrence<'a> {
    /// No member is named.
    None,
    /// The field's whole type is member `k`, at the index `e` for an indexed
    /// member.
    Child { member: usize, index: Option<&'a Expr> },
    /// The field is `(y: A) -> E(e)`, `A` free of the group: a function
    /// child, lowered on the family's `W` form
    /// (docs/kernel/iwf-infinitary-design.md §1), `e` read under `y`.
    FnChild { member: usize, index: Option<&'a Expr> },
}

/// Mutual inductive families' part of the elaborator.
pub(crate) struct MutualFamily<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for MutualFamily<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Elaborator {
    /// A mutual group (§1–§2): validate it in the members' terms, generate the
    /// member index type and the family, elaborate both by the ordinary
    /// routes, and declare the members.
    pub(crate) fn elab_mutual_inductives(&mut self, decls: &[&InductiveDecl]) -> R<()> {
        let heads = MutualFamily(self).validate_group(decls)?;
        let first = &decls[0].name;
        let members_decl = members_decl(first, &heads);
        self.elab_inductive(&members_decl)?;
        let (family, members) = family_decl(first, &heads)?;
        InductivesMut(self).elab_inductive_members(&family, members)?;
        for d in decls {
            self.add_name(&d.name, NameKind::Inductive);
        }
        Ok(())
    }
}

impl MutualFamily<'_> {
    /// §1's requirements, each refused in the members' own terms before
    /// anything is generated — the generated family's refusals would name
    /// it, and nobody wrote it.
    fn validate_group<'a>(&self, decls: &[&'a InductiveDecl]) -> R<Vec<MemberHead<'a>>> {
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        let first = decls[0];
        let group = names.join("`, `");
        let mut heads = Vec::with_capacity(decls.len());
        for d in decls {
            if NameLookup(self).own_declares(&d.name, &[NameKind::Inductive, NameKind::Global]) {
                return err(format!("duplicate name `{}`", d.name), d.span);
            }
            NameLookup(self).check_declarable(&d.name, d.span)?;
            if d.name == "Nat" {
                return err("`Nat` is built in", d.span);
            }
            if d.is_codata {
                return err(
                    format!(
                        "`{}` is `codata` and is mutually recursive with `{group}`: a \
                         mutual group is of `inductive` declarations \
                         (docs/inductives/mutual-inductive-design.md §1)",
                        d.name
                    ),
                    d.span,
                );
            }
            if d.is_record {
                return err(
                    format!(
                        "`{}` is a `record` but is mutually recursive with `{group}`: a \
                         recursive declaration is an `inductive` (docs/language/surface-records.md §2)",
                        d.name
                    ),
                    d.span,
                );
            }
            if d.params != first.params {
                return err(
                    format!(
                        "the members of a mutual group declare the same type parameters, \
                         in the same order: `{}` has <{}> and `{}` has <{}> \
                         (docs/inductives/mutual-inductive-design.md §1)",
                        first.name,
                        first.params.join(", "),
                        d.name,
                        d.params.join(", ")
                    ),
                    d.span,
                );
            }
            if let Some(p) = d.valparams.first() {
                return err(
                    format!(
                        "`{}` has a value parameter and is a member of the mutual group \
                         `{group}`: a group is one indexed family, which takes none \
                         (docs/language/surface-value-parameters.md §6); state it as an index",
                        d.name
                    ),
                    p.span,
                );
            }
            let index = match &d.index {
                None => None,
                Some(ty) => {
                    let TyKind::Fn {
                        binder: Some(n),
                        implicit: false,
                        dom,
                        cod,
                    } = &ty.kind
                    else {
                        return err(
                            "an indexed member's head is `: (n: I) -> Type`, one index \
                             (docs/inductives/mutual-inductive-design.md §1)",
                            ty.span,
                        );
                    };
                    if !matches!(cod.kind, TyKind::Univ { level: 0 }) {
                        return err(
                            "an index telescope ends in bare `Type`; the family's level is \
                             computed from the fields (docs/inductives/inductive-indexed-lowering.md §2)",
                            cod.span,
                        );
                    }
                    // The single-family rules for what can be an index type.
                    Inductives(self).index_type(dom, &d.name, &[])?;
                    Some((n.clone(), (**dom).clone()))
                }
            };
            heads.push(MemberHead { decl: d, index });
        }
        // Constructors: one namespace across the group, each result at its
        // own member, each member occurrence a whole field at the shared
        // parameters.
        let mut seen: Vec<(&str, &str)> = Vec::new();
        for h in &heads {
            let d = h.decl;
            for c in &d.ctors {
                if let Some((_, owner)) = seen.iter().find(|(n, _)| *n == c.name) {
                    return err(
                        if *owner == d.name {
                            format!("duplicate constructor `{}`", c.name)
                        } else {
                            format!(
                                "`{}` is a constructor of both `{owner}` and `{}`: the \
                                 members of a mutual group share one constructor namespace",
                                c.name, d.name
                            )
                        },
                        c.span,
                    );
                }
                seen.push((&c.name, &d.name));
                self.validate_result(h, c, &names)?;
                for f in &c.fields {
                    occurrence(&heads, d, c, f)?;
                }
            }
        }
        Ok(heads)
    }

    /// An indexed member's constructor states its result at its own member,
    /// `D<p̄>(e)`; an unindexed member's states none.
    fn validate_result(&self, h: &MemberHead, c: &CtorDecl, names: &[&str]) -> R<()> {
        let d = h.decl;
        let Some(r) = &c.result else {
            if h.index.is_some() {
                return err(
                    format!(
                        "`{}` needs a result annotation: every constructor of an indexed \
                         member states its index (`{} : {}<…>(…)`)",
                        c.name, c.name, d.name
                    ),
                    c.span,
                );
            }
            return Ok(());
        };
        if h.index.is_none() {
            return err(
                format!(
                    "`{}` has a result annotation, but `{}` is not indexed: only an \
                     indexed member's constructors state their index",
                    c.name, d.name
                ),
                r.span,
            );
        }
        let head = match &r.kind {
            ExprKind::App { head, args, .. } if args.len() == 1 => named_head(head),
            _ => None,
        };
        match head {
            Some((n, targs)) if n == d.name => {
                if !uniform(targs, &d.params) {
                    return err(
                        format!(
                            "`{}`'s result is `{}` at arguments other than its own \
                             parameters; parameters are monomorphized, so the result is \
                             uniform",
                            c.name, d.name
                        ),
                        r.span,
                    );
                }
                Ok(())
            }
            Some((n, _)) if names.contains(&n) => err(
                format!(
                    "`{}` is a constructor of `{}`, so its result is `{}(…)`, not `{n}(…)`: \
                     each member's constructors build that member",
                    c.name, d.name, d.name
                ),
                r.span,
            ),
            _ => err(
                format!(
                    "`{}`'s result annotation is `{}<…>(e)`, the member applied to one \
                     index",
                    c.name, d.name
                ),
                r.span,
            ),
        }
    }

    /// `⟦D_t<ā>(m)⟧`: the group's family at member `k`'s index constructor
    /// (§2). `idx` is the written index, present exactly for an indexed
    /// member; the caller has matched that already.
    pub(crate) fn lower_member(
        &self,
        cx: &Cx,
        fam: &Inductive,
        k: usize,
        targs: &[Ty],
        idx: Option<&Expr>,
        span: Span,
    ) -> R<(Type, Level)> {
        let member = &fam.members[k];
        if targs.len() != fam.params.len() {
            return err(
                format!(
                    "`{}` takes {} type argument(s), found {}",
                    member.name,
                    fam.params.len(),
                    targs.len()
                ),
                span,
            );
        }
        match (&member.index, idx) {
            (Some(_), None) => {
                return err(
                    format!(
                        "`{}` is indexed: write `{}(e)`, the member at an index",
                        member.name, member.name
                    ),
                    span,
                );
            }
            (None, Some(_)) => {
                return err(format!("`{}` is not indexed", member.name), span);
            }
            _ => {}
        }
        let mut lowered = Vec::with_capacity(targs.len());
        for a in targs {
            lowered.push(self.elab_ty(cx, a)?);
        }
        let idx_t = self.member_index(cx, fam, k, idx, span)?;
        IwfFamily(self).lower_iwf_instance(cx, fam, &lowered, &[], idx_t, span)
    }

    /// The member a type is, when it is a mutual group's family at one of
    /// its index constructors: `⟦Tm<ā>⟧` read back to the family and `Tm`'s
    /// position. The index is read structurally, by its injection path over
    /// the member index type (the spelling [`Self::member_index`] builds);
    /// a neutral index is no member.
    pub(crate) fn member_of_family_ty(&self, ty: &Type) -> Option<(Rc<Inductive>, usize)> {
        let (fam, iwf) = IwfFamily(self).iwf_of(ty)?;
        if fam.members.is_empty() {
            return None;
        }
        let path = crate::spelling::inj_path(&iwf.idx, fam.members.len());
        if !path.reached || path.ctor >= fam.members.len() {
            return None;
        }
        Some((fam, path.ctor))
    }

    /// The family's index at member `k`: `D_t#member(e)`, built by the member
    /// index type's own constructor lowering, which checks `e` at the
    /// member's index type.
    pub(crate) fn member_index(
        &self,
        cx: &Cx,
        fam: &Inductive,
        k: usize,
        idx: Option<&Expr>,
        span: Span,
    ) -> R<Term> {
        let Some(IdxTy::Decl(iind)) = &fam.index_ty else {
            return err("internal: a mutual family is indexed by its members", span);
        };
        let (ity, ilvl) = self.lower_instance(cx, iind, &[], &[], span)?;
        let args: Vec<&Expr> = idx.into_iter().collect();
        self.build_ctor(cx, iind, k, &args, &ity, &ilvl, span)
    }

    /// The member a family constructor belongs to, by name, for a
    /// diagnostic.
    pub(crate) fn member_name_of(fam: &Inductive, ctor: usize) -> &str {
        fam.member_of_ctor(ctor)
            .map_or(fam.name.as_str(), |m| fam.members[m].name.as_str())
    }
}

/// Are the written type arguments the declaration's own parameters, bare and
/// in order?
fn uniform(targs: &[Ty], params: &[String]) -> bool {
    targs.len() == params.len()
        && targs.iter().zip(params).all(|(a, p)| {
            matches!(&a.kind, TyKind::Named { name, args } if name == p && args.is_empty())
        })
}

/// How field `f` of constructor `c` of member `d` mentions the group, or the
/// refusal if it does in a way the family cannot carry.
fn occurrence<'a>(
    heads: &[MemberHead],
    d: &InductiveDecl,
    c: &CtorDecl,
    f: &'a FieldDecl,
) -> R<Occurrence<'a>> {
    if let Some((member, index)) = whole_occurrence(heads, d, c, &f.ty)? {
        return Ok(Occurrence::Child { member, index });
    }
    // `(y: A) -> E(e)`: the codomain is a whole occurrence, the domain names
    // no member (a mention there is not strictly positive, refused below).
    if let TyKind::Fn { dom, cod, implicit: false, .. } = &f.ty.kind
        && heads.iter().all(|h| occurs(dom, &h.decl.name).is_none())
        && let Some((member, index)) = whole_occurrence(heads, d, c, cod)?
    {
        return Ok(Occurrence::FnChild { member, index });
    }
    if let Some(h) = heads.iter().find(|h| occurs(&f.ty, &h.decl.name).is_some()) {
        let why = match &f.ty.kind {
            TyKind::Fn { .. } => {
                "a member occurs in a function field only as its codomain, `(y: A) -> E(e)` \
                 with `A` free of the group (docs/kernel/iwf-infinitary-design.md §1)"
            }
            TyKind::Vec { .. } => {
                "a container field of a member is not lowered on the family's route; \
                 write the children as fields"
            }
            _ => "a member occurs in a field only as the field's whole type",
        };
        return err(
            format!(
                "field of `{}` mentions the mutual member `{}` inside another type: {why} \
                 (docs/inductives/mutual-inductive-design.md §1)",
                c.name, h.decl.name
            ),
            f.ty.span,
        );
    }
    Ok(Occurrence::None)
}

/// `ty` as a whole member occurrence, `E<p̄>` or `E<p̄>(e)`: the member and
/// its index, after the checks that it is one the family can carry.
fn whole_occurrence<'a>(
    heads: &[MemberHead],
    d: &InductiveDecl,
    c: &CtorDecl,
    ty: &'a Ty,
) -> R<Option<(usize, Option<&'a Expr>)>> {
    let member_of = |n: &str| heads.iter().position(|h| h.decl.name == n);
    // The whole field: `E<p̄>` or `E<p̄>(e)`.
    let whole: Option<(usize, &[Ty], Option<&'a [Expr]>)> = match &ty.kind {
        TyKind::Named { name, args } => member_of(name).map(|k| (k, args.as_slice(), None)),
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, args, .. } => named_head(head)
                .and_then(|(n, targs)| member_of(n).map(|k| (k, targs, Some(args.as_slice())))),
            _ => None,
        },
        _ => None,
    };
    if let Some((k, targs, vals)) = whole {
        let e = heads[k].decl;
        if !uniform(targs, &d.params) {
            return err(
                format!(
                    "field of `{}` uses `{}` at arguments other than the group's \
                     parameters; parameters are monomorphized, so a recursive occurrence \
                     must be uniform",
                    c.name, e.name
                ),
                ty.span,
            );
        }
        let index = match (vals, &heads[k].index) {
            (None, None) => None,
            (Some([i]), Some(_)) => Some(i),
            (None, Some(_)) => {
                return err(
                    format!(
                        "field of `{}` names `{}` without its index: `{}` is indexed, so \
                         a child is `{}(e)`",
                        c.name, e.name, e.name, e.name
                    ),
                    ty.span,
                );
            }
            (Some(_), Some(_)) => {
                return err(
                    format!("a child of `{}` states one index: `{}(i)`", c.name, e.name),
                    ty.span,
                );
            }
            (Some(_), None) => {
                return err(
                    format!(
                        "field of `{}` applies `{}` to an index, but `{}` is not indexed",
                        c.name, e.name, e.name
                    ),
                    ty.span,
                );
            }
        };
        if let Some(i) = index
            && let Some(h) = heads.iter().find(|h| expr_mentions(i, &h.decl.name))
        {
            return err(
                format!(
                    "the index of a child of `{}` mentions `{}`: an index is a value \
                     of the member's index type",
                    c.name, h.decl.name
                ),
                i.span,
            );
        }
        return Ok(Some((k, index)));
    }
    Ok(None)
}

/// `inductive D_1#members { D_t#member(n: I_t) | D_t#member, … }` (§2).
fn members_decl(first: &str, heads: &[MemberHead]) -> InductiveDecl {
    let span = heads[0].decl.span;
    InductiveDecl {
        name: members_name(first),
        params: Vec::new(),
        valparams: Vec::new(),
        varies: None,
        ctors: heads
            .iter()
            .map(|h| CtorDecl {
                name: member_ctor_name(&h.decl.name),
                fields: h
                    .index
                    .iter()
                    .map(|(n, ty)| FieldDecl {
                        name: Some(n.clone()),
                        ty: ty.clone(),
                        default: None,
                        span: ty.span,
                    })
                    .collect(),
                result: None,
                span: h.decl.span,
            })
            .collect(),
        is_record: false,
        is_codata: false,
        index: None,
        span,
    }
}

/// `inductive D_1#mutual<p̄> : (j: D_1#members) -> Type { … }` (§2), and the
/// members it is the union of.
fn family_decl(first: &str, heads: &[MemberHead]) -> R<(InductiveDecl, Vec<Member>)> {
    let span = heads[0].decl.span;
    let params = heads[0].decl.params.clone();
    let fam = family_name(first);
    let at = |k: usize, idx: Option<&Expr>, span: Span| -> Expr {
        let tag = var(&member_ctor_name(&heads[k].decl.name), span);
        let index = match idx {
            None => tag,
            Some(e) => app(tag, vec![e.clone()], span),
        };
        let head = var(&fam, span);
        let head = if params.is_empty() {
            head
        } else {
            Expr {
                kind: ExprKind::TyApp {
                    head: Box::new(head),
                    args: params
                        .iter()
                        .map(|p| Ty {
                            kind: TyKind::Named { name: p.clone(), args: Vec::new() },
                            span,
                        })
                        .collect(),
                },
                span,
            }
        };
        app(head, vec![index], span)
    };
    let mut ctors = Vec::new();
    let mut members = Vec::new();
    for (k, h) in heads.iter().enumerate() {
        let d = h.decl;
        let mut mine = Vec::new();
        for c in &d.ctors {
            mine.push(ctors.len());
            let mut fields = Vec::with_capacity(c.fields.len());
            for f in &c.fields {
                let ty = match occurrence(heads, d, c, f)? {
                    Occurrence::None => f.ty.clone(),
                    Occurrence::Child { member, index } => Ty {
                        kind: TyKind::OfExpr(Box::new(at(member, index, f.ty.span))),
                        span: f.ty.span,
                    },
                    Occurrence::FnChild { member, index } => {
                        let TyKind::Fn { binder, implicit, dom, cod } = &f.ty.kind else {
                            unreachable!("classified by `occurrence`");
                        };
                        Ty {
                            kind: TyKind::Fn {
                                binder: binder.clone(),
                                implicit: *implicit,
                                dom: dom.clone(),
                                cod: Box::new(Ty {
                                    kind: TyKind::OfExpr(Box::new(at(member, index, cod.span))),
                                    span: cod.span,
                                }),
                            },
                            span: f.ty.span,
                        }
                    }
                };
                fields.push(FieldDecl { ty, ..f.clone() });
            }
            // The written result's index, under the member's tag.
            let result = match &c.result {
                None => at(k, None, c.span),
                Some(r) => {
                    let ExprKind::App { args, .. } = &r.kind else {
                        unreachable!("validated by `validate_result`");
                    };
                    at(k, Some(&args[0]), r.span)
                }
            };
            ctors.push(CtorDecl {
                name: c.name.clone(),
                fields,
                result: Some(result),
                span: c.span,
            });
        }
        members.push(Member {
            name: d.name.clone(),
            index: h.index.as_ref().map(|(n, _)| n.clone()),
            ctors: mine,
        });
    }
    let index = Ty {
        kind: TyKind::Fn {
            binder: Some("#j".into()),
            implicit: false,
            dom: Box::new(Ty {
                kind: TyKind::Named { name: members_name(first), args: Vec::new() },
                span,
            }),
            cod: Box::new(Ty { kind: TyKind::Univ { level: 0 }, span }),
        },
        span,
    };
    let decl = InductiveDecl {
        name: fam,
        params,
        valparams: Vec::new(),
        varies: None,
        ctors,
        is_record: false,
        is_codata: false,
        index: Some(index),
        span,
    };
    Ok((decl, members))
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

fn app(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
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
