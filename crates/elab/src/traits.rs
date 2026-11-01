//! Classes and instances, layer 1 (`docs/traits-layer1-design.md`).
//!
//! Nothing here reaches the kernel on its own. A `class` builds the
//! `InductiveDecl` that the equivalent `record` would have built and hands it
//! to `elab_inductive`; an `instance` builds `ast::Decl`s — one per block
//! member, one for the assembled value, one per synthesized canonical parent,
//! one per override-agreement certificate — and hands each to `elab_decl`.
//! Every artifact therefore passes the ordinary declaration gate, and the
//! trusted base is untouched (design §intro).
//!
//! The two tables this round adds are consumed by `extends` and by the
//! instance assembler only. Layer 2's resolver is the consumer they exist for.

use std::collections::{HashMap, HashSet};
use std::sync::Arc as Rc;

use heather_syntax::{
    Block, ClassDecl, ClassRef, CtorDecl, Decl, DeclKind, DesignationDecl, Expr, ExprKind,
    FieldDecl, InductiveDecl, InstanceBody, InstanceDecl, InstanceField, LamBinder, OpFixity,
    Param, RecordLitField, Span, Stmt, Ty, TyKind,
};

use heather_kernel::term::Term;

use crate::application::ParamMeta;
use crate::names::qkey;
use crate::resolve::DerivedInst;
use crate::{ElabError, Elaborator, R, err};

/// A declared class: the record it is, plus what `extends` and the instance
/// assembler need to know about it.
#[derive(Clone)]
pub(crate) struct ClassInfo {
    /// Unqualified name, as written.
    pub name: String,
    /// Type-parameter names, in order — every name written in the angle
    /// brackets, kinded or not.
    pub params: Vec<String>,
    /// Parallel to [`Self::params`]: a **constructor** parameter's kind
    /// (`class Bind<M: Type → Type>`, issues/higher-kinded-classes.md), `None`
    /// for an ordinary type parameter. A kinded parameter is a term, so the
    /// class's record takes it as a leading value parameter, before
    /// [`Self::valparams`]; [`Elaborator::kinded_class_ty`] moves a written
    /// head's argument there.
    pub kinds: Vec<Option<Ty>>,
    /// `class Monoid<A>(op: A -> A -> A)` — the declared **value indices**
    /// (docs/operation-indexed-classes-design.md §3), types written in terms
    /// of `params`. Empty for an unindexed class. Their names are what a
    /// constraint binder binds the index under (§4).
    pub valparams: Vec<Param>,
    /// The record's field list. Untagged parents contribute their flattened
    /// fields; a tagged parent contributes one dictionary-valued field.
    pub fields: Vec<FieldDecl>,
    /// Every ancestor, transitively, with equal fibers at equal paths deduped.
    /// Distinct tagged fibers are retained. Each `ClassRef`'s arguments are
    /// written in terms of *this* class's parameters; `path` says which
    /// dictionary-valued fields reach it from this class.
    pub ancestors: Vec<ClassRef>,
    /// Which class contributed each field, parallel to `fields`. `None` for
    /// the class's own fields. Used to phrase the collision diagnostic and to
    /// decide which ancestor an inherited field is filled from.
    pub owner: Vec<Option<String>>,
}

impl ClassInfo {
    /// Does the class take a type constructor (`class Bind<M: Type → Type>`)?
    /// Its record then has value parameters even with no written index, so a
    /// literal of it is spelled without type arguments and takes them from
    /// the expected type, as an indexed class's does.
    pub(crate) fn is_kinded(&self) -> bool {
        self.kinds.iter().any(Option::is_some)
    }
}

/// A registered instance: one canonical value per (class, resolved carrier)
/// (design §4.1, `docs/instance-resolved-key-design.md`).
#[derive(Clone)]
pub(crate) struct InstanceInfo {
    /// The global that *is* the instance, **module-qualified** —
    /// `main::Rat::Monoid`, `int::Le::Decide`. Qualified because it is emitted
    /// as a `Var` at a *use* site, in a module that may see two `Le::Decide`s
    /// (`docs/instance-resolved-key-design.md` §4): the unqualified string was
    /// a name that resolved by luck of visibility, and the registry has to
    /// name the very declaration it registered.
    pub global: String,
    /// The instance head as written, for diagnostics (`Monoid<Rat>`).
    pub written: String,
    /// The **index spelling** this instance is keyed at
    /// (docs/operation-indexed-classes-design.md §3.1) — the resolved global
    /// key of each index argument, joined. Empty at an unindexed class. It is
    /// part of the registry key and it is what a value-slot refusal lists.
    pub index: String,
    /// `true` when the instance takes parameters (generic instance or
    /// `requires` binders), in which case it cannot be projected from by name
    /// alone — fill-by-reference is refused against it with a clear message.
    pub parameterized: bool,
}

/// A registered **designation**: what one operator symbol means at one
/// carrier head (docs/operators-onto-classes-design.md §3).
#[derive(Clone)]
pub(crate) struct DesignationInfo {
    /// The designated operation, as a bare global name. Emitted bare at each
    /// use site and instantiated there by ordinary implicit inference — which
    /// is why the declaration refuses anything but a name (§3.2).
    pub op: String,
    /// The declaration as written, for the duplicate diagnostic.
    pub written: String,
    /// The carrier head **as the writer spelled it** — `List`, not
    /// `list::List`. The key is the resolved declaration ([`DesigKey`]), which
    /// is exactly why the written form is kept beside it: a diagnostic that
    /// lists the table quotes something a reader can type
    /// (`issues/diagnostics-name-the-written-form.md`), and once the key
    /// stopped being a spelling there was nowhere else to read it off.
    pub carrier: String,
}

/// The key a designation is registered under: **(fixity, symbol,
/// carrier-head key)**, the third component a *resolved* declaration reference and not a surface
/// spelling — `docs/instance-resolved-key-design.md` §3's rule applied one
/// table over (issues/designation-key-collides-across-modules.md).
///
/// `("++", "list::List")` and `("++", "seq::List")` are two designations that
/// coexist; keying the head on the written `List` made the second a duplicate
/// of the first.
///
/// Fixity keeps a future infix `-` distinct from prefix negation. The symbol
/// component is not a spelling in the relevant sense: it is one of
/// the grammar's fixed operator tokens, the same token in every module, and no
/// declaration can introduce another `+`.
pub(crate) type DesigKey = (OpFixity, String, String);

/// `head_key` is the carrier head **resolved** — [`Elaborator::carrier_key`]
/// at a declaration, [`Elaborator::carrier_of_ty`] at a lowered operand —
/// never a written head's raw string.
pub(crate) fn designation_key(fixity: OpFixity, sym: &str, head_key: &str) -> DesigKey {
    (fixity, sym.to_string(), head_key.to_string())
}

#[cfg(test)]
mod designation_key_tests {
    use super::*;

    #[test]
    fn prefix_and_infix_slots_do_not_collide() {
        assert_ne!(
            designation_key(OpFixity::Prefix, "-", "int::Int"),
            designation_key(OpFixity::Infix, "-", "int::Int")
        );
    }
}

/// The key an instance is registered under: **(class key, carrier-head key,
/// index spelling)**, every component a *resolved* declaration reference and
/// no component a surface spelling
/// (`docs/instance-resolved-key-design.md` §3).
///
/// The first component is the class's qualified key, the second the carrier
/// head's — `("bool::Decide", "int::Int::Le", "")` and `("bool::Decide",
/// "nat::Nat::Le", "")` are two instances that coexist, where keying the head on
/// the written name `Le` collided them
/// (issues/instance-key-collides-across-modules.md).
///
/// The third is the **index spelling**
/// (docs/operation-indexed-classes-design.md §3.1): each index argument's own
/// resolved global key, joined. Two instances at one key are the
/// duplicate-declaration error they always were, two at different indices
/// coexist as equals. Empty at an unindexed class, so every key that predates
/// value indices carries one resolved component instead of two.
pub(crate) type InstKey = (String, String, String);

/// `head_key` is the carrier head **resolved** — [`Elaborator::carrier_key`],
/// never `head_name`'s raw string.
pub(crate) fn instance_key(class_key: &str, head_key: &str, index: &str) -> InstKey {
    (
        class_key.to_string(),
        head_key.to_string(),
        index.to_string(),
    )
}

/// Committed class, instance, designation, and derived-dictionary state.
///
/// These tables answer one question together: which structure does a carrier
/// expose? Their fields stay private so declaration code cannot update a
/// lookup view without going through the matching registration operation.
#[derive(Clone, Default)]
pub(crate) struct Traits {
    class_members: HashSet<String>,
    /// The unqualified names of the classes with a kinded parameter
    /// (`class Bind<M: Type → Type>`): the cheap prefilter that keeps
    /// [`Elaborator::kinded_class_ty`] off every other named type.
    kinded: HashSet<String>,
    classes: HashMap<String, Rc<ClassInfo>>,
    instances: HashMap<InstKey, InstanceInfo>,
    designations: HashMap<DesigKey, DesignationInfo>,
    derived: Vec<DerivedInst>,
    /// Evidence rules by the qualified key of their conclusion's relation
    /// (`nat::Nat::Lt`), each list in canonical (global-name) order
    /// (docs/positivity-evidence-design.md §6 A).
    evidence: HashMap<String, Vec<EvidenceRule>>,
}

/// One `evidence theorem`: what `:= infer` may apply at a proposition goal.
///
/// Keyed by the conclusion's relation, read off the checked statement's head
/// global, so two rules about one relation coexist where the class registry's
/// (class, carrier head) key would collide them. `heads` is the head global
/// of each of the relation's arguments, `None` where the rule binds it to a
/// variable: a prefilter only, the kernel-checked trial decides.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EvidenceRule {
    pub(crate) global: String,
    pub(crate) relation: String,
    pub(crate) heads: Vec<Option<String>>,
}

impl Traits {
    pub(crate) fn commit_class(&mut self, key: String, info: ClassInfo) {
        debug_assert!(!self.classes.contains_key(&key));
        for name in info.fields.iter().filter_map(|field| field.name.as_ref()) {
            self.class_members.insert(name.clone());
        }
        if info.kinds.iter().any(Option::is_some) {
            self.kinded.insert(info.name.clone());
        }
        self.classes.insert(key, Rc::new(info));
    }

    /// Could `name` (qualified or not) name a class with a kinded parameter?
    /// A prefilter on the last path segment: `false` is certain, `true` is
    /// then resolved.
    pub(crate) fn maybe_kinded(&self, name: &str) -> bool {
        !self.kinded.is_empty()
            && self.kinded.contains(name.rsplit("::").next().unwrap_or(name))
    }

    pub(crate) fn class(&self, key: &str) -> Option<&Rc<ClassInfo>> {
        self.classes.get(key)
    }

    pub(crate) fn has_class(&self, key: &str) -> bool {
        self.classes.contains_key(key)
    }

    pub(crate) fn has_member(&self, name: &str) -> bool {
        self.class_members.contains(name)
    }

    pub(crate) fn classes_declaring(&self, name: &str) -> Vec<(String, Rc<ClassInfo>)> {
        let mut out: Vec<_> =
            self.classes
                .iter()
                .filter(|(_, info)| {
                    info.fields.iter().zip(&info.owner).any(|(field, owner)| {
                        field.name.as_deref() == Some(name) && owner.is_none()
                    })
                })
                .map(|(key, info)| (key.clone(), Rc::clone(info)))
                .collect();
        out.sort_by(|left, right| left.0.cmp(&right.0));
        out
    }

    pub(crate) fn instance(&self, key: &InstKey) -> Option<&InstanceInfo> {
        self.instances.get(key)
    }

    pub(crate) fn has_instance(&self, key: &InstKey) -> bool {
        self.instances.contains_key(key)
    }

    /// A generic class index overlaps every concrete index at the same class
    /// and carrier. Resolution tries candidates by canonical name rather than
    /// specificity, so admit neither declaration order: coexistence would make
    /// the selected dictionary an artifact of sorting.
    pub(crate) fn generic_index_overlap(
        &self,
        class_key: &str,
        head_key: &str,
        index: &str,
    ) -> Option<&InstanceInfo> {
        let parts: Vec<_> = index.split(", ").collect();
        self.instances
            .iter()
            .find(|((class, head, other_index), _)| {
                let other: Vec<_> = other_index.split(", ").collect();
                class == class_key
                    && head == head_key
                    && parts.len() == other.len()
                    && parts.iter().zip(other).all(|(a, b)| {
                        a == &b || a.starts_with("#binder") || b.starts_with("#binder")
                    })
            })
            .map(|(_, info)| info)
    }

    pub(crate) fn commit_instance(&mut self, key: InstKey, info: InstanceInfo) {
        debug_assert!(!self.instances.contains_key(&key));
        self.instances.insert(key, info);
    }

    /// The candidates of a class in the order resolution tries them
    /// (`docs/traits-layer2-design.md` §3.1): sorted by canonical name, except
    /// that the instances keyed at `prefer` — the head of the goal's carrier,
    /// when the caller could read it off the solver parameter's written type —
    /// come first, in that same order. A head-keyed instance is the specific
    /// one; a candidate at another head can still fit by unfolding the goal,
    /// and building it costs that unfolding whether or not it wins
    /// (docs/reflection-through-decide-instances-design.md §3).
    pub(crate) fn candidates(
        &self,
        class_key: &str,
        prefer: Option<&str>,
    ) -> Vec<(String, bool, String)> {
        let mut out: Vec<_> = self
            .instances
            .iter()
            .filter(|((class, _, _), _)| class == class_key)
            .map(|((_, head, _), info)| {
                (
                    prefer.is_none_or(|p| p != head),
                    info.global.clone(),
                    info.parameterized,
                    info.index.clone(),
                )
            })
            .collect();
        out.sort();
        out.into_iter().map(|(_, g, p, i)| (g, p, i)).collect()
    }

    /// Every instance of a class: its head key and its index spelling, in
    /// key order. The cast edges are read this way
    /// (`Elaborator::cast_edges`, docs/casting-design.md §14).
    pub(crate) fn instances_of_class(&self, class_key: &str) -> Vec<(String, String)> {
        let mut out: Vec<_> = self
            .instances
            .keys()
            .filter(|(class, _, _)| class == class_key)
            .map(|(_, head, index)| (head.clone(), index.clone()))
            .collect();
        out.sort();
        out
    }

    pub(crate) fn instances_answering(
        &self,
        class_key: &str,
        head_key: Option<&str>,
    ) -> Vec<String> {
        let mut out: Vec<_> = self
            .instances
            .iter()
            .filter(|((class, head, _), _)| {
                class == class_key && head_key.is_none_or(|key| head == key)
            })
            .map(|(_, info)| info.written.clone())
            .collect();
        out.sort();
        out
    }

    pub(crate) fn designation(&self, key: &DesigKey) -> Option<&DesignationInfo> {
        self.designations.get(key)
    }

    pub(crate) fn commit_evidence(&mut self, rule: EvidenceRule) {
        let rules = self.evidence.entry(rule.relation.clone()).or_default();
        debug_assert!(!rules.iter().any(|r| r.global == rule.global));
        let at = rules.partition_point(|r| r.global < rule.global);
        rules.insert(at, rule);
    }

    pub(crate) fn has_evidence(&self, global: &str) -> bool {
        self.evidence.values().flatten().any(|r| r.global == global)
    }

    /// The rules about `relation`, in canonical order.
    pub(crate) fn evidence_rules(&self, relation: &str) -> &[EvidenceRule] {
        self.evidence.get(relation).map_or(&[], Vec::as_slice)
    }

    pub(crate) fn commit_designation(&mut self, key: DesigKey, info: DesignationInfo) {
        debug_assert!(!self.designations.contains_key(&key));
        self.designations.insert(key, info);
    }

    pub(crate) fn designated(
        &self,
        fixity: OpFixity,
        symbol: &str,
        carrier_key: &str,
    ) -> Option<&str> {
        self.designations
            .get(&designation_key(fixity, symbol, carrier_key))
            .map(|info| info.op.as_str())
    }

    pub(crate) fn has_designation_for(&self, fixity: OpFixity, symbol: &str) -> bool {
        self.designations
            .keys()
            .any(|(registered_fixity, registered, _)| {
                *registered_fixity == fixity && registered == symbol
            })
    }

    pub(crate) fn designations_at(&self, carrier_key: &str) -> Vec<(String, String)> {
        let mut out: Vec<_> = self
            .designations
            .iter()
            .filter(|((fixity, _, carrier), _)| {
                *fixity == OpFixity::Infix && carrier == carrier_key
            })
            .map(|((_, symbol, _), info)| (symbol.clone(), info.op.clone()))
            .collect();
        out.sort();
        out
    }

    pub(crate) fn designations_for(&self, fixity: OpFixity, symbol: &str) -> Vec<(String, String)> {
        let mut out: Vec<_> = self
            .designations
            .iter()
            .filter(|((registered_fixity, registered, _), _)| {
                *registered_fixity == fixity && registered == symbol
            })
            .map(|(_, info)| (info.carrier.clone(), info.op.clone()))
            .collect();
        out.sort();
        out
    }

    pub(crate) fn derived(&self) -> &[DerivedInst] {
        &self.derived
    }

    pub(crate) fn commit_derived(&mut self, derived: DerivedInst) {
        self.derived.push(derived);
    }
}

/// The index spelling as a *name* fragment: a key may contain `::` (a
/// resolved global's qualifier) and a declaration name must not, since one
/// `::` is a member qualifier and two are refused.
fn name_suffix(index: &str) -> String {
    index.replace("::", "#").replace(", ", "#")
}

/// The head name of a surface type — the carrier's constructor, which is what
/// the canonical name is built from and what has to name a type in scope.
fn head_name(t: &Ty) -> Option<&str> {
    match &t.kind {
        TyKind::Nat => Some("Nat"),
        TyKind::Named { name, .. } => Some(name),
        // An **applied type former** — `Le(n, m)`, `Not(P)` — whose head is the
        // former's own name (widened 2026-08-17, docs/decide-class-design.md §2).
        // A proposition stated by recursion into `Type` is the carrier a
        // decidability class is *for*, and it arrives here as an ordinary
        // application rather than as a `Named` type, because `Le` is a `fn`.
        //
        // Deliberately NOT `TyKind::Eq`: an equation's head would have to be one
        // reserved key for every equality at every type, so `Decide<n = m>` at
        // `Nat` and at `Bool` would collide as duplicates. Keying that needs the
        // endpoints' type in the key, which is the (class, carrier-syntax) key
        // §7.1 defers to layer 2 — the one case of this round that genuinely
        // wants it (issues/decidable-equation-carrier.md).
        //
        // The spine is walked rather than unwrapped once, so a former written
        // with **type** arguments — `Rep<A>(n)`, whose expression is an `App`
        // around a `TyApp` — reaches the same `Var` as `Le(n, m)` does
        // (issues/type-former-carrier-with-type-arguments.md). The type
        // arguments are no more part of the head than the value arguments are:
        // the registry has never keyed on a carrier's arguments, only on the
        // name at the end of its spine.
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, .. } | ExprKind::TyApp { head, .. } => spine_head(head),
            _ => None,
        },
        _ => None,
    }
}

/// The `Var` at the end of an application spine, through both application
/// forms. Reached only from [`head_name`]'s *applied* case, so a bare name in
/// type position is still not a carrier: the "at least one application" shape
/// is what the widening admitted and this keeps it.
fn spine_head(e: &Expr) -> Option<&str> {
    match &e.kind {
        ExprKind::App { head, .. } | ExprKind::TyApp { head, .. } => spine_head(head),
        ExprKind::Var(name) => Some(name),
        _ => None,
    }
}

/// A surface type as written, for diagnostics and for the instance's display
/// name. Not a canonical encoding — nothing keys on it.
pub(crate) fn render_ty(t: &Ty) -> String {
    match &t.kind {
        TyKind::Nat => "Nat".into(),
        TyKind::Univ { level } => format!("Type<{level}>"),
        TyKind::Named { name, args } if args.is_empty() => name.clone(),
        TyKind::Named { name, args } => {
            format!(
                "{name}<{}>",
                args.iter().map(render_ty).collect::<Vec<_>>().join(", ")
            )
        }
        TyKind::Fn { dom, cod, .. } => format!("{} -> {}", render_ty(dom), render_ty(cod)),
        // A goal may be an ordinary proposition (`p: n = n := infer`), and
        // "`_`" for it would make the whole diagnostic unreadable.
        TyKind::Eq(a, b) => format!("{} = {}", render_expr(a), render_expr(b)),
        TyKind::Vec { elem, .. } => format!("[{}; _]", render_ty(elem)),
        TyKind::Fin(_) => "Fin(_)".into(),
        // `Monoid<A>(op)` — a class at its index, which arrives applied
        // (docs/operation-indexed-classes-design.md §3). Rendering it as `_`
        // would empty out every diagnostic the indexed classes produce.
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, args, .. } => {
                let h = match &head.kind {
                    ExprKind::TyApp { head, args } => format!(
                        "{}<{}>",
                        render_expr(head),
                        args.iter().map(render_ty).collect::<Vec<_>>().join(", ")
                    ),
                    _ => render_expr(head),
                };
                format!(
                    "{h}({})",
                    args.iter().map(render_expr).collect::<Vec<_>>().join(", ")
                )
            }
            _ => render_expr(e),
        },
        _ => "_".into(),
    }
}

/// The written form of the few expression shapes that appear inside a *type*
/// worth displaying — an equation's endpoints. Anything larger renders as
/// `_`: this is a diagnostic's display, and nothing keys on it.
pub(crate) fn render_expr(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Var(n) => n.clone(),
        ExprKind::OpSymbol { symbol, .. } => symbol.clone(),
        ExprKind::Num(n) => n.to_string(),
        ExprKind::Eq(lhs, rhs) => format!("{} = {}", render_expr(lhs), render_expr(rhs)),
        // Prefer the direct surface notation only while its source shape is
        // still present. In particular, do not inspect an elaborated `Pi`
        // ending in `False`: an arbitrary function into `False` is not
        // necessarily an inequality.
        ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            ..
        } if matches!(&head.kind, ExprKind::Var(name) if name == "Not")
            && named.is_empty()
            && matches!(
                args.as_slice(),
                [Expr {
                    kind: ExprKind::Eq(..),
                    ..
                }]
            ) =>
        {
            let ExprKind::Eq(lhs, rhs) = &args[0].kind else {
                unreachable!()
            };
            format!("{} ≠ {}", render_expr(lhs), render_expr(rhs))
        }
        // An operator application renders as what was **written**
        // (`a + b`, never `add(a, b)`) — the standing ask of
        // `issues/diagnostics-name-the-written-form.md`, arriving free now
        // that the symbol survives into the AST.
        ExprKind::App { head, args, .. }
            if matches!(
                head.kind,
                ExprKind::OpSymbol {
                    fixity: OpFixity::Infix,
                    ..
                }
            ) && args.len() == 2 =>
        {
            format!(
                "{} {} {}",
                render_expr(&args[0]),
                render_expr(head),
                render_expr(&args[1])
            )
        }
        ExprKind::App { head, args, .. }
            if matches!(
                head.kind,
                ExprKind::OpSymbol {
                    fixity: OpFixity::Prefix,
                    ..
                }
            ) && args.len() == 1 =>
        {
            format!("{}{}", render_expr(head), render_expr(&args[0]))
        }
        ExprKind::App { head, args, .. }
            if matches!(
                head.kind,
                ExprKind::OpSymbol {
                    fixity: OpFixity::Postfix,
                    ..
                }
            ) && args.len() == 1 =>
        {
            format!("{}{}", render_expr(&args[0]), render_expr(head))
        }
        // A named argument renders as it was **written**, `x := e`, for the
        // same reason an operator application renders as `a + b`
        // (issues/diagnostics-name-the-written-form.md).
        ExprKind::App {
            head, args, named, ..
        } => format!(
            "{}({}){}",
            render_expr(head),
            args.iter()
                .map(render_expr)
                .chain(
                    named
                        .iter()
                        .filter(|a| !a.name.starts_with("#decreasing:"))
                        .map(|a| format!("{} := {}", a.name, render_expr(&a.expr)))
                )
                .collect::<Vec<_>>()
                .join(", "),
            named.iter().find_map(|a| a.name.strip_prefix("#decreasing:"))
                .map(|n| format!(" decreasing {n}")).unwrap_or_default()
        ),
        ExprKind::Dot { recv, name, .. } => format!("{}.{name}", render_expr(recv)),
        _ => "_".into(),
    }
}

/// Whether two inherited class references name the same law-bearing fiber.
///
/// `extends` arguments are restricted to the child's own parameters, so every
/// type argument is a bare named parameter and every index is a bare variable.
/// Compare those names structurally rather than using the diagnostic renderer:
/// class name alone is insufficient because `Monoid<A>(add)` and
/// `Monoid<A>(mul)` are distinct fibers.
fn same_parent_fiber(a: &ClassRef, b: &ClassRef) -> bool {
    same_parent_carrier(a, b)
        && a.index.len() == b.index.len()
        && a.index.iter().zip(&b.index).all(|(x, y)| {
            matches!((&x.kind, &y.kind), (ExprKind::Var(xn), ExprKind::Var(yn)) if xn == yn)
        })
}

fn same_parent_carrier(a: &ClassRef, b: &ClassRef) -> bool {
    a.name == b.name
        && a.args.len() == b.args.len()
        && a.args.iter().zip(&b.args).all(|(x, y)| {
            matches!(
                (&x.kind, &y.kind),
                (
                    TyKind::Named { name: xn, args: xa },
                    TyKind::Named { name: yn, args: ya }
                ) if xa.is_empty() && ya.is_empty() && xn == yn
            )
        })
}

#[cfg(test)]
mod inequality_render_tests {
    use super::*;

    fn expr(kind: ExprKind) -> Expr {
        Expr {
            kind,
            span: Span { start: 0, end: 0 },
        }
    }

    #[test]
    fn only_the_surface_not_equality_shape_renders_as_inequality() {
        let equation = expr(ExprKind::Eq(
            Box::new(expr(ExprKind::Var("x".into()))),
            Box::new(expr(ExprKind::Num(0u64.into()))),
        ));
        let call = |name: &str| {
            expr(ExprKind::App {
                head: Box::new(expr(ExprKind::Var(name.into()))),
                args: vec![equation.clone()],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            })
        };

        assert_eq!(render_expr(&call("Not")), "x ≠ 0");
        assert_eq!(render_expr(&call("reject")), "reject(x = 0)");
    }
}

pub(crate) fn class_ref_written(r: &ClassRef) -> String {
    let head = format!(
        "{}<{}>",
        r.name,
        r.args.iter().map(render_ty).collect::<Vec<_>>().join(", ")
    );
    if r.index.is_empty() {
        return head;
    }
    format!(
        "{head}({})",
        r.index
            .iter()
            .map(render_expr)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// A class head's argument written in a type slot, read as the expression a
/// kinded parameter takes: `Option` is the name, `Result<Nat>` the generic
/// application, and an expression in type position is itself. `None` for a
/// structural type former, which no type constructor is spelled as.
fn ty_as_expr(t: &Ty) -> Option<Expr> {
    match &t.kind {
        TyKind::Named { name, args } if args.is_empty() => Some(var(name, t.span)),
        TyKind::Named { name, args } => Some(span_expr(
            ExprKind::TyApp { head: Box::new(var(name, t.span)), args: args.clone() },
            t.span,
        )),
        TyKind::OfExpr(e) => Some((**e).clone()),
        _ => None,
    }
}

fn span_expr(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn var(name: &str, span: Span) -> Expr {
    span_expr(ExprKind::Var(name.to_string()), span)
}

/// What [`Elaborator::expand_constraints`] produces: the rewritten parameter
/// telescope, plus the two per-declaration facts the desugaring is the only
/// thing that knows.
pub(crate) struct Expanded {
    pub params: Vec<Param>,
    /// Index names a *repeated* constraint left bound to nothing
    /// (docs/operation-indexed-classes-design.md §5.2), with the refusal each
    /// one owes.
    pub ambiguous: Vec<(String, String)>,
    /// Operator symbols a `C(+)` slot installed, as (symbol, binder name)
    /// (docs/operators-onto-classes-design.md §5).
    pub symbols: Vec<(String, String)>,
}

/// The generated name of an index binder a SYMBOL slot introduced
/// (docs/operators-onto-classes-design.md §5.1).
///
/// The **symbol is in the name**, because a call site fills this slot from the
/// designation table and the only thing that reaches it about the callee's
/// parameters is their names. Same device as `#index{i}_{k}` and
/// `#constraint{ix}`: `#` never begins an identifier, so nothing in a body can
/// reach it and the name is free to carry data. `@` separates because no
/// operator symbol contains one.
pub(crate) fn op_index_binder(sym: &str, i: usize, k: usize) -> String {
    format!("#op{sym}@{i}_{k}")
}

/// The symbol an index binder's generated name carries, if it was made by
/// [`op_index_binder`].
pub(crate) fn op_index_symbol(name: &str) -> Option<&str> {
    let rest = name.strip_prefix("#op")?;
    let (sym, _) = rest.rsplit_once('@')?;
    (!sym.is_empty()).then_some(sym)
}

// -- renaming a parent's type parameters ------------------------------------
//
// `extends` arguments are restricted to the child's own type parameters
// (design §3), so instantiating a parent's stored field declarations is a
// rename. The two walks below are mechanical and total: a missed variant would
// silently leave a parent's parameter name free, which the record's own
// lowering would then report as an unknown type — loud, but at the wrong
// place, so nothing here takes a wildcard shortcut.

type Ren = HashMap<String, String>;

/// Where a class holds an ancestor, for a diagnostic: untagged, or at the
/// path of tags that reaches it.
fn where_reached(path: &[String]) -> String {
    if path.is_empty() {
        "untagged".to_string()
    } else {
        format!("at `{}`", path.join("."))
    }
}

/// The [`Ren`] key under which a parent's body symbol maps to the child's
/// index argument. A NUL prefix keeps it apart from every identifier.
fn symbol_key(symbol: &str) -> String {
    format!("\0{symbol}")
}

/// A class's own body symbols read as its own index names — what the
/// phantom-index check counts occurrences through.
fn own_symbols(info: &ClassInfo) -> Ren {
    info.valparams
        .iter()
        .filter_map(|p| p.symbol.as_ref().map(|s| (symbol_key(s), p.name.clone())))
        .collect()
}

fn ren(m: &Ren, n: &str) -> String {
    m.get(n).cloned().unwrap_or_else(|| n.to_string())
}

fn rename_ty(m: &Ren, t: &Ty) -> Ty {
    let kind = match &t.kind {
        TyKind::Nat => TyKind::Nat,
        TyKind::Univ { level } => TyKind::Univ { level: *level },
        TyKind::Ctx => TyKind::Ctx,
        TyKind::Eq(a, b) => TyKind::Eq(Box::new(rename_expr(m, a)), Box::new(rename_expr(m, b))),
        TyKind::OfExpr(e) => TyKind::OfExpr(Box::new(rename_expr(m, e))),
        TyKind::TypeOf(e) => TyKind::TypeOf(Box::new(rename_expr(m, e))),
        TyKind::Named { name, args } => TyKind::Named {
            name: ren(m, name),
            args: args.iter().map(|a| rename_ty(m, a)).collect(),
        },
        TyKind::Vec { elem, len } => TyKind::Vec {
            elem: Box::new(rename_ty(m, elem)),
            len: Box::new(rename_expr(m, len)),
        },
        TyKind::Fin(e) => TyKind::Fin(Box::new(rename_expr(m, e))),
        TyKind::Squash(inner) => TyKind::Squash(Box::new(rename_ty(m, inner))),
        TyKind::Fn {
            binder,
            implicit,
            dom,
            cod,
        } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(rename_ty(m, dom)),
            cod: Box::new(rename_ty(m, cod)),
        },
        TyKind::TyCode { ctx } => TyKind::TyCode { ctx: ctx.clone() },
        TyKind::Code { ctx, ty } => TyKind::Code {
            ctx: ctx.clone(),
            ty: Box::new(rename_ty(m, ty)),
        },
        TyKind::Splice { name } => TyKind::Splice { name: name.clone() },
    };
    Ty { kind, span: t.span }
}

fn rename_expr(m: &Ren, e: &Expr) -> Expr {
    use ExprKind::*;
    let kind = match &e.kind {
        Var(n) => Var(ren(m, n)),
        // A symbol a parent's head bound (`op as ∙`) is that parent's index,
        // so instantiating the parent spells it as the child's argument: the
        // child installs its own symbols, not the parent's
        // (`symbol_key`). Any other symbol names nothing in the telescope
        // and is kept.
        OpSymbol { symbol, fixity } => match m.get(&symbol_key(symbol)) {
            Some(n) => Var(n.clone()),
            None => OpSymbol {
                symbol: symbol.clone(),
                fixity: *fixity,
            },
        },
        Univ { level } => Univ { level: *level },
        Num(n) => Num(n.clone()),
        Scaled(lit) => Scaled(lit.clone()),
        Char(c) => Char(*c),
        Str(text) => Str(text.clone()),
        ArgSlot(index) => ArgSlot(*index),
        Refl => Refl,
        AutoRefl => AutoRefl,
        Hole(n) => Hole(n.clone()),
        App {
            head,
            args,
            named,
            explicit,
            goal_oriented,
        } => App {
            head: Box::new(rename_expr(m, head)),
            args: args.iter().map(|a| rename_expr(m, a)).collect(),
            // A named argument's *name* is the callee's parameter name, which
            // no instantiation renames — only its value is a subterm.
            named: named
                .iter()
                .map(|na| heather_syntax::NamedArg {
                    name: na.name.clone(),
                    name_span: na.name_span,
                    expr: rename_expr(m, &na.expr),
                    span: na.span,
                })
                .collect(),
            explicit: *explicit,
            goal_oriented: *goal_oriented,
        },
        TyApp { head, args } => TyApp {
            head: Box::new(rename_expr(m, head)),
            args: args.iter().map(|a| rename_ty(m, a)).collect(),
        },
        Lam { binders, body } => Lam {
            binders: binders
                .iter()
                .map(|b| LamBinder {
                    name: b.name.clone(),
                    ty: b.ty.as_ref().map(|t| rename_ty(m, t)),
                    implicit: b.implicit,
                    span: b.span,
                })
                .collect(),
            body: Box::new(rename_expr(m, body)),
        },
        CollectionLit(es) => CollectionLit(es.iter().map(|x| rename_expr(m, x)).collect()),
        Eq(a, b) => Eq(Box::new(rename_expr(m, a)), Box::new(rename_expr(m, b))),
        TyLit(t) => TyLit(Box::new(rename_ty(m, t))),
        Match {
            form,
            generated,
            scrut,
            eqbind,
            motive,
            arms,
        } => Match {
            form: *form,
            generated: *generated,
            scrut: Box::new(rename_expr(m, scrut)),
            eqbind: eqbind.clone(),
            motive: motive.as_ref().map(|x| Box::new(rename_expr(m, x))),
            arms: arms
                .iter()
                .map(|a| heather_syntax::Arm {
                    ctor: a.ctor.clone(),
                    default: a.default,
                    binders: a.binders.clone(),
                    body: rename_expr(m, &a.body),
                    span: a.span,
                })
                .collect(),
        },
        // A `match code` cannot appear in a class member's body — the renamer
        // walks program-layer declarations and `match code` is layer-m only —
        // but a walk that silently dropped a form would rename the wrong
        // thing, so it recurses like every other binder-carrying node.
        MatchCode {
            scrut,
            motive,
            arms,
        } => MatchCode {
            scrut: Box::new(rename_expr(m, scrut)),
            motive: Box::new(rename_ty(m, motive)),
            arms: arms
                .iter()
                .map(|a| heather_syntax::Arm {
                    ctor: a.ctor.clone(),
                    default: a.default,
                    binders: a.binders.clone(),
                    body: rename_expr(m, &a.body),
                    span: a.span,
                })
                .collect(),
        },
        Dot {
            recv,
            name,
            tyargs,
            args,
            named,
        } => Dot {
            recv: Box::new(rename_expr(m, recv)),
            name: name.clone(),
            tyargs: tyargs.iter().map(|t| rename_ty(m, t)).collect(),
            args: args
                .as_ref()
                .map(|v| v.iter().map(|a| rename_expr(m, a)).collect()),
            named: named
                .iter()
                .map(|na| heather_syntax::NamedArg {
                    name: na.name.clone(),
                    name_span: na.name_span,
                    expr: rename_expr(m, &na.expr),
                    span: na.span,
                })
                .collect(),
        },
        Index { recv, idx } => Index {
            recv: Box::new(rename_expr(m, recv)),
            idx: Box::new(rename_expr(m, idx)),
        },
        RecordUpdate { base, fields } => RecordUpdate {
            base: Box::new(rename_expr(m, base)),
            fields: fields
                .iter()
                .map(|f| RecordLitField { name: f.name.clone(), expr: rename_expr(m, &f.expr), span: f.span })
                .collect(),
        },
        RecordLit {
            name,
            tyargs,
            fields,
        } => RecordLit {
            name: ren(m, name),
            tyargs: tyargs.iter().map(|t| rename_ty(m, t)).collect(),
            fields: fields
                .iter()
                .map(|f| RecordLitField {
                    name: f.name.clone(),
                    expr: rename_expr(m, &f.expr),
                    span: f.span,
                })
                .collect(),
        },
        Block(b) => Block(Box::new(rename_block(m, b))),
        Quote(x) => Quote(Box::new(rename_expr(m, x))),
        Splice(x) => Splice(Box::new(rename_expr(m, x))),
        J {
            proof,
            motive,
            case,
        } => J {
            proof: Box::new(rename_expr(m, proof)),
            motive: Box::new(rename_expr(m, motive)),
            case: Box::new(rename_expr(m, case)),
        },
    };
    Expr { kind, span: e.span }
}

fn rename_block(m: &Ren, b: &Block) -> Block {
    Block {
        stmts: b
            .stmts
            .iter()
            .map(|s| match s {
                Stmt::Let {
                    name,
                    ty,
                    expr,
                    span,
                    opaque,
                } => Stmt::Let {
                    name: name.clone(),
                    ty: ty.as_ref().map(|t| rename_ty(m, t)),
                    expr: rename_expr(m, expr),
                    span: *span,
                    opaque: *opaque,
                },
                Stmt::LetRecord { fields, expr, span } => Stmt::LetRecord {
                    fields: fields.clone(),
                    expr: rename_expr(m, expr),
                    span: *span,
                },
                Stmt::LetCode { name, expr, span } => Stmt::LetCode {
                    name: name.clone(),
                    expr: rename_expr(m, expr),
                    span: *span,
                },
            })
            .collect(),
        result: Box::new(rename_expr(m, &b.result)),
        ons: b
            .ons
            .iter()
            .map(|o| heather_syntax::OnStmt {
                target: match &o.target {
                    heather_syntax::OnTarget::Name(n) => heather_syntax::OnTarget::Name(n.clone()),
                    heather_syntax::OnTarget::Stmt(t) => {
                        heather_syntax::OnTarget::Stmt(rename_ty(m, t))
                    }
                    heather_syntax::OnTarget::Ctor {
                        ctor,
                        binders,
                        default,
                    } => heather_syntax::OnTarget::Ctor {
                        ctor: ctor.clone(),
                        binders: binders.clone(),
                        default: *default,
                    },
                },
                expr: rename_expr(m, &o.expr),
                span: o.span,
            })
            .collect(),
        span: b.span,
    }
}

/// A class's declared index type, at the constraint's arguments: the class's
/// type parameters replaced by the types the constraint applies it to. A
/// substitution rather than [`rename_ty`]'s rename, because a constraint may
/// name a *composite* carrier (`requires m: Monoid<List<A>>(append)`).
fn subst_ty(m: &HashMap<String, Ty>, t: &Ty) -> Ty {
    if let TyKind::Named { name, args } = &t.kind
        && args.is_empty()
        && let Some(a) = m.get(name)
    {
        return a.clone();
    }
    let ren: Ren = Ren::new();
    let kind = match &t.kind {
        TyKind::Named { name, args } => TyKind::Named {
            name: name.clone(),
            args: args.iter().map(|a| subst_ty(m, a)).collect(),
        },
        TyKind::Fn {
            binder,
            implicit,
            dom,
            cod,
        } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(subst_ty(m, dom)),
            cod: Box::new(subst_ty(m, cod)),
        },
        TyKind::Vec { elem, len } => TyKind::Vec {
            elem: Box::new(subst_ty(m, elem)),
            len: len.clone(),
        },
        // Every other shape's payload is a term, and a class's index type is a
        // type expression: `rename_ty`'s walk with an empty map is the identity
        // and keeps this total without a wildcard clone.
        _ => return rename_ty(&ren, t),
    };
    Ty { kind, span: t.span }
}

/// Does this written type mention `name` as a bare variable? Used only to spot
/// the dependency cycle a linked index can close.
fn ty_mentions(t: &Ty, name: &str) -> bool {
    ty_var_count(t, name) > 0
        || match &t.kind {
            TyKind::Eq(a, b) => expr_mentions(a, name) || expr_mentions(b, name),
            TyKind::OfExpr(e) => expr_mentions(e, name),
            TyKind::Fn { dom, cod, .. } => ty_mentions(dom, name) || ty_mentions(cod, name),
            TyKind::Named { args, .. } => args.iter().any(|a| ty_mentions(a, name)),
            _ => false,
        }
}

fn expr_mentions(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Var(n) => n == name,
        ExprKind::App {
            head, args, named, ..
        } => {
            expr_mentions(head, name)
                || args.iter().any(|a| expr_mentions(a, name))
                || named.iter().any(|a| expr_mentions(&a.expr, name))
        }
        ExprKind::TyApp { head, args } => {
            expr_mentions(head, name) || args.iter().any(|a| ty_mentions(a, name))
        }
        ExprKind::Dot {
            recv, tyargs, args, named, ..
        } => {
            expr_mentions(recv, name)
                || tyargs.iter().any(|a| ty_mentions(a, name))
                || args.iter().flatten().any(|a| expr_mentions(a, name))
                || named.iter().any(|a| expr_mentions(&a.expr, name))
        }
        ExprKind::Eq(a, b) => expr_mentions(a, name) || expr_mentions(b, name),
        _ => false,
    }
}

/// The size of a written type: type constructors and variable occurrences,
/// counted the same way on both sides of the decrease check (§6). Only the
/// *comparison* is meaningful, so a coarse walk is the honest one — anything
/// finer would be a claim about which shapes shrink.
fn ty_size(t: &Ty) -> usize {
    match &t.kind {
        TyKind::Named { args, .. } => 1 + args.iter().map(ty_size).sum::<usize>(),
        TyKind::Vec { elem, .. } => 1 + ty_size(elem),
        TyKind::Fn { dom, cod, .. } => 1 + ty_size(dom) + ty_size(cod),
        // An equality carrier is measured through both endpoints. Value
        // binders in `instance(n, m: Nat) Decide<n = m>` must be recoverable
        // from the head, and required subgoals must obey the same Paterson
        // measure as every other carrier.
        TyKind::Eq(a, b) => 1 + expr_size(a) + expr_size(b),
        // An applied type former (`Not(P)`, `Le(n, m)`) is a carrier as of the
        // 2026-08-17 widening, so the measure has to see into it. Falling
        // through to `1` was harmless only while such a carrier could not be
        // declared: a head of size 1 admits no strictly smaller subgoal, so
        // every instance at one refused, whatever it required.
        TyKind::OfExpr(e) => expr_size(e),
        _ => 1,
    }
}

/// [`ty_size`] through an application's expression spine. An argument that is
/// itself a type (a `TyApp`'s) re-enters [`ty_size`], so `Not(P)` and `And<P, Q>`
/// are measured on one scale and a mixed carrier cannot game the comparison.
fn expr_size(e: &Expr) -> usize {
    match &e.kind {
        ExprKind::App {
            head, args, named, ..
        } => {
            expr_size(head)
                + args.iter().map(expr_size).sum::<usize>()
                + named.iter().map(|a| expr_size(&a.expr)).sum::<usize>()
        }
        ExprKind::TyApp { head, args } => expr_size(head) + args.iter().map(ty_size).sum::<usize>(),
        _ => 1,
    }
}

/// How often `v` occurs as a bare name in `t` — the second half of Paterson's
/// condition, which is what refuses `C<A> requires C<Pair<A, A>>` even where
/// the sizes happen to agree.
fn ty_var_count(t: &Ty, v: &str) -> usize {
    match &t.kind {
        TyKind::Named { name, args } => {
            (name == v && args.is_empty()) as usize
                + args.iter().map(|a| ty_var_count(a, v)).sum::<usize>()
        }
        TyKind::Vec { elem, .. } => ty_var_count(elem, v),
        TyKind::Fn { dom, cod, .. } => ty_var_count(dom, v) + ty_var_count(cod, v),
        TyKind::Eq(a, b) => expr_var_count(a, v) + expr_var_count(b, v),
        // The occurrence half of the same widening: a parameter of an applied
        // former (`Not(P)`'s `P`) is a bare occurrence exactly as `And<P, Q>`'s
        // is, and Paterson's second condition has to count it.
        TyKind::OfExpr(e) => expr_var_count(e, v),
        _ => 0,
    }
}

/// [`ty_var_count`] through an application's expression spine.
fn expr_var_count(e: &Expr, v: &str) -> usize {
    match &e.kind {
        // The head is walked rather than skipped. A former's own name is never
        // one of the carrier's variables, so in practice this adds zero; if it
        // ever did not, a higher count on the *subgoal* side is the direction
        // that refuses, which is the safe way to be wrong.
        ExprKind::App {
            head, args, named, ..
        } => {
            expr_var_count(head, v)
                + args.iter().map(|a| expr_var_count(a, v)).sum::<usize>()
                + named
                    .iter()
                    .map(|a| expr_var_count(&a.expr, v))
                    .sum::<usize>()
        }
        ExprKind::TyApp { head, args } => {
            expr_var_count(head, v) + args.iter().map(|a| ty_var_count(a, v)).sum::<usize>()
        }
        ExprKind::Var(name) => (name == v) as usize,
        ExprKind::Eq(a, b) => expr_var_count(a, v) + expr_var_count(b, v),
        _ => 0,
    }
}

/// How often `v` occurs in the instance head's **class arguments** — the part
/// of the head a binder may be recovered from. The index is measured separately
/// by [`index_var_count`] and is not a substitute: see [`Elaborator::check_valparams`].
fn head_var_count(c: &ClassRef, v: &str) -> usize {
    c.args.iter().map(|a| ty_var_count(a, v)).sum()
}

/// How often `v` occurs in the instance head's **index arguments**. Only ever
/// asked in order to refuse: an index joins the registry *key* as a spelling.
fn index_var_count(c: &ClassRef, v: &str) -> usize {
    c.index.iter().map(|e| expr_var_count(e, v)).sum()
}

/// The instance's telescope after its type parameters
/// (docs/value-generic-instances-design.md §3): the **value binders** first,
/// then the solver parameters.
///
/// Value binders lead because a `requires` type may mention one —
/// `instance(n: Nat) C<F(n)> requires D<G(n)>` — while the converse cannot
/// happen: a solver parameter's type is a class type, and no binder's type is
/// written in terms of a dictionary.
fn instance_params(d: &InstanceDecl) -> Vec<Param> {
    d.valparams
        .iter()
        .cloned()
        .chain(d.requires.iter().cloned())
        .collect()
}

/// A block whose result is `e` and which binds nothing — every synthesized
/// declaration's body.
fn body_of(e: Expr) -> Block {
    let span = e.span;
    Block {
        stmts: Vec::new(),
        result: Box::new(e),
        ons: Vec::new(),
        span,
    }
}

impl Elaborator {
    // -- classes ------------------------------------------------------------

    /// `class C<p⃗> extends … { f⃗ }` — the record, then the registry entry
    /// (design §2, §3).
    pub(crate) fn elab_class(&mut self, d: &ClassDecl) -> R<()> {
        for (i, p) in d.params.iter().enumerate() {
            if d.params[..i].contains(p) {
                return err(format!("duplicate type parameter `{p}`"), d.span);
            }
        }
        // Untagged parents flatten as before. A tagged parent is instead one
        // dictionary-valued field, which lets one class occur at distinct
        // operation fibers without collapsing either structure.
        let mut fields: Vec<FieldDecl> = Vec::new();
        let mut owner: Vec<Option<String>> = Vec::new();
        let mut ancestors: Vec<ClassRef> = Vec::new();
        // `direct` runs parallel to `ancestors`: whether the entry is one of
        // this class's own written parents rather than something one of them
        // brought along.
        let mut direct: Vec<bool> = Vec::new();
        let add_ancestor = |ancestors: &mut Vec<ClassRef>,
                            direct: &mut Vec<bool>,
                            candidate: ClassRef,
                            is_direct: bool|
         -> R<()> {
            // One fiber reached by two paths. The same path is the ordinary
            // diamond and collapses. Through different paths — a setoid
            // inherited untagged and again inside a tagged monoid, or inside
            // two tags — the class keeps one canonical copy: the untagged one
            // if there is one, else the first reached. Every instance owes the
            // other copies agreement with it (`shared_ancestor_agreements`),
            // so two dictionaries for one fiber never register side by side.
            // Writing one parent twice is still refused: that is an authoring
            // slip, not a composition.
            if let Some(i) = ancestors
                .iter()
                .position(|x| same_parent_fiber(x, &candidate))
            {
                let previous = &ancestors[i];
                if previous.path == candidate.path {
                    return Ok(());
                }
                if is_direct && direct[i] {
                    return err(
                        format!(
                            "`{}` inherits the same `{}` fiber through two different parent \
                             paths (`{}` and `{}`), so its canonical parent would be \
                             ambiguous",
                            d.name,
                            candidate.name,
                            previous.path.join("."),
                            candidate.path.join(".")
                        ),
                        candidate.span,
                    );
                }
                // Only a fiber with no data may be held twice. Copies of a
                // proof-only dictionary differ in proofs, which no statement
                // mentions; copies of a unit or an inverse are different
                // terms in generic code, so a theorem stated through one copy
                // would not apply through the other.
                if let Some(info) = self.lookup_class(&candidate.name)
                    && !self.proof_only(&info)
                {
                    return err(
                        format!(
                            "`{}` would hold the `{}` fiber `{}` twice, {} and {}: that \
                             class carries data, and two copies of it are not convertible \
                             in generic code. Inherit it once, and take any further law it \
                             needs as a law class of its own",
                            d.name,
                            candidate.name,
                            class_ref_written(&candidate),
                            where_reached(&previous.path),
                            where_reached(&candidate.path)
                        ),
                        candidate.span,
                    );
                }
                if candidate.path.is_empty() {
                    ancestors[i] = candidate;
                    direct[i] = is_direct;
                }
                return Ok(());
            }
            let Some(previous) = ancestors.iter().find(|x| x.name == candidate.name) else {
                ancestors.push(candidate);
                direct.push(is_direct);
                return Ok(());
            };
            if (!previous.path.is_empty() || !candidate.path.is_empty())
                && previous.path != candidate.path
            {
                // A registry key can distinguish two written indices, but if
                // a differing index never occurs in the record's field types,
                // the kernel quite correctly sees the dictionary types as
                // convertible. Such a class cannot support two canonical
                // structures at one carrier.
                if same_parent_carrier(previous, &candidate)
                    && let Some(info) = self.lookup_class(&candidate.name)
                {
                    for (i, (left, right)) in
                        previous.index.iter().zip(&candidate.index).enumerate()
                    {
                        let same = matches!(
                            (&left.kind, &right.kind),
                            (ExprKind::Var(x), ExprKind::Var(y)) if x == y
                        );
                        let Some(param) = info.valparams.get(i) else {
                            continue;
                        };
                        let spelled = own_symbols(&info);
                        if !same
                            && info.fields.iter().all(|field| {
                                ty_var_count(&rename_ty(&spelled, &field.ty), &param.name) == 0
                            })
                        {
                            return err(
                                format!(
                                    "`{}` cannot inherit `{}` at two values of `{}`: that \
                                     index does not occur in the parent dictionary's field \
                                     types, so the kernel sees the two fibers as convertible",
                                    d.name, candidate.name, param.name
                                ),
                                candidate.span,
                            );
                        }
                    }
                }
                ancestors.push(candidate);
                direct.push(is_direct);
                return Ok(());
            }
            err(
                format!(
                    "`{}` inherits the class `{}` at two distinct fibers (`{}` and `{}`): \
                     unqualified flattening cannot identify them; give the parent \
                     dictionaries distinct `as` names",
                    d.name,
                    candidate.name,
                    class_ref_written(previous),
                    class_ref_written(&candidate)
                ),
                candidate.span,
            )
        };
        for parent in &d.extends {
            let (pinfo, rename) = self.parent_view(d, parent)?;
            // The parent's own ancestors come with it, renamed the same way.
            for a in &pinfo.ancestors {
                let mut path = parent.path.clone();
                path.extend(a.path.iter().cloned());
                let a = ClassRef {
                    name: a.name.clone(),
                    args: a.args.iter().map(|t| rename_ty(&rename, t)).collect(),
                    index: a.index.iter().map(|e| rename_expr(&rename, e)).collect(),
                    path,
                    span: parent.span,
                };
                add_ancestor(&mut ancestors, &mut direct, a, false)?;
            }
            add_ancestor(
                &mut ancestors,
                &mut direct,
                ClassRef {
                    name: parent.name.clone(),
                    args: parent.args.clone(),
                    index: parent.index.clone(),
                    path: parent.path.clone(),
                    span: parent.span,
                },
                true,
            )?;
            if let Some(tag) = parent.path.first() {
                if fields.iter().any(|f| f.name.as_deref() == Some(tag)) {
                    return err(
                        format!("`{}` already has a field or parent named `{tag}`", d.name),
                        parent.span,
                    );
                }
                fields.push(FieldDecl {
                    name: Some(tag.clone()),
                    ty: heather_syntax::class_ty(
                        parent.name.clone(),
                        parent.args.clone(),
                        parent.index.clone(),
                        parent.span,
                    ),
                    default: None,
                    span: parent.span,
                });
                owner.push(None);
                continue;
            }
            for (f, o) in pinfo.fields.iter().zip(pinfo.owner.iter()) {
                let from = o.clone().unwrap_or_else(|| pinfo.name.clone());
                let name = f.name.clone().unwrap_or_default();
                if let Some(prev) = fields.iter().position(|g| g.name == f.name) {
                    // A shared ancestor reached twice contributes once. Two
                    // *unrelated* classes contributing one name is a genuine
                    // collision and is refused.
                    let prev_from = owner[prev].clone().unwrap_or_default();
                    if prev_from != from {
                        return err(
                            format!(
                                "field `{name}` is inherited from both `{prev_from}` and \
                                 `{from}`, which are unrelated: flattening collapses a \
                                 shared ancestor reached by two paths, it does not merge \
                                 two different fields"
                            ),
                            parent.span,
                        );
                    }
                    continue;
                }
                fields.push(FieldDecl {
                    name: f.name.clone(),
                    ty: rename_ty(&rename, &f.ty),
                    default: None,
                    span: parent.span,
                });
                owner.push(Some(from));
            }
        }
        for f in &d.fields {
            if let Some(prev) = fields.iter().position(|g| g.name == f.name) {
                let from = owner[prev].clone().unwrap_or_default();
                return err(
                    format!(
                        "`{}` already has a field `{}` inherited from `{from}`: a class \
                         does not redeclare an inherited field — an instance overrides it \
                         (and owes agreement)",
                        d.name,
                        f.name.clone().unwrap_or_default()
                    ),
                    f.span,
                );
            }
            fields.push(f.clone());
            owner.push(None);
        }
        // The record. One constructor named after the class, exactly as
        // `record` desugars (docs/surface-records.md §2.1).
        let ctor = CtorDecl {
            name: d.name.clone(),
            fields: fields.clone(),
            result: None,
            span: d.span,
        };
        // A kinded parameter is a type constructor, a term: the record takes
        // it as a leading value parameter (`record Bind(M: Type → Type)`, the
        // shape that already computes as a dictionary), and keeps the
        // ordinary ones as its type parameters.
        let kinds = if d.kinds.len() == d.params.len() {
            d.kinds.clone()
        } else {
            vec![None; d.params.len()]
        };
        let mut rec_params = Vec::new();
        let mut rec_valparams = Vec::new();
        for (p, k) in d.params.iter().zip(&kinds) {
            match k {
                None => rec_params.push(p.clone()),
                Some(kind) => rec_valparams.push(Param {
                    name: p.clone(),
                    ty: kind.clone(),
                    implicit: false,
                    is_self: false,
                    solver: None,
                    default: None,
                    origin: heather_syntax::ParamOrigin::Written,
                    symbol: None,
                    span: kind.span,
                }),
            }
        }
        rec_valparams.extend(d.valparams.iter().cloned());
        let ind = InductiveDecl {
            name: d.name.clone(),
            params: rec_params,
            valparams: rec_valparams,
            ctors: vec![ctor],
            is_record: true,
            is_codata: false,
            index: None,
            span: d.span,
        };
        self.elab_inductive(&ind)?;
        let info = ClassInfo {
            name: d.name.clone(),
            params: d.params.clone(),
            kinds,
            valparams: d.valparams.clone(),
            fields,
            ancestors,
            owner,
        };
        let key = qkey(self.names.module(), &d.name);
        self.semantic_commit_class(key, info);
        Ok(())
    }

    /// A carrier head as the registry keys it: the **declaration** the head
    /// names, qualified (`docs/instance-resolved-key-design.md` §3).
    ///
    /// The fallback is the bare name, and it is reached by exactly the three
    /// names [`Elaborator::names_a_type`] claims with no declaration behind
    /// them — `Nat`, `Type`, `True`. Those are the language's own and cannot be
    /// declared twice, so a bare key for them is a *constant*, not a spelling
    /// that might mean two things.
    pub(crate) fn carrier_key(&self, head: &str) -> String {
        self.key_of(head).unwrap_or_else(|| head.to_string())
    }

    /// The registry head key of a solver parameter's carrier at a call
    /// site, read off the parameter's **written** type — `Decide<P>` with
    /// `P` a type parameter the call has already solved, or `Decide<Le(n, m)>`
    /// spelled out — so that resolution can try the instances keyed there
    /// first (`docs/reflection-through-decide-instances-design.md` §3).
    /// `None` whenever the head is not one identifier: the order then stays
    /// the plain canonical one, and nothing is decided here either way.
    ///
    /// A solved type parameter is applied to the callee as a *term* (the
    /// carrier's code) before any solver parameter is reached, so it is read
    /// off `applied`'s spine — the type arguments lead it — and its own spine
    /// head is a global the current Ψ names. A written applied former
    /// resolves the way an instance head does at declaration.
    pub(crate) fn solver_carrier_head(
        &self,
        written: &Ty,
        params: &[ParamMeta],
        applied: &Term,
    ) -> Option<String> {
        let TyKind::Named { args, .. } = &written.kind else {
            return None;
        };
        let [carrier] = args.as_slice() else {
            return None;
        };
        if let TyKind::Named { name, args } = &carrier.kind
            && args.is_empty()
            && let Some(position) = params
                .iter()
                .filter(|p| p.is_type)
                .position(|p| p.name == *name)
        {
            let mut type_args = Vec::new();
            let mut head = applied;
            while let Some((fun, arg)) = crate::spelling::app_of(head) {
                type_args.push(&**arg);
                head = fun;
            }
            type_args.reverse();
            let mut head = *type_args.get(position)?;
            while let Some((fun, _)) = crate::spelling::app_of(head) {
                head = fun;
            }
            let Term::GlobalTm { var, .. } = head else {
                return None;
            };
            let abs = self.global_abs_of(*var)?;
            return self.names.global_name_at(abs as u32).map(str::to_string);
        }
        // A class over a type constructor (issues/higher-kinded-classes.md):
        // the carrier is a value parameter `{M: Type → Type}`, solved by now
        // to the constructor — `D#tycode_fn^δ` for a declaration with a code
        // function, whose key is the declaration's own. A λ constructor has
        // no head to prefer.
        if let TyKind::Named { name, args } = &carrier.kind
            && args.is_empty()
            && let Some(position) = params.iter().position(|p| !p.is_type && p.name == *name)
        {
            let mut spine = Vec::new();
            let mut head = applied;
            while let Some((fun, arg)) = crate::spelling::app_of(head) {
                spine.push(&**arg);
                head = fun;
            }
            spine.reverse();
            let mut head = *spine.get(position)?;
            while let Some((fun, _)) = crate::spelling::app_of(head) {
                head = fun;
            }
            let Term::GlobalTm { var, .. } = head else {
                return None;
            };
            let abs = self.global_abs_of(*var)?;
            let crate::gendefs::GenDef::TyCodeFn(tag) =
                *self.types.gdefs().key_for_abs(&(abs as u32))?
            else {
                return None;
            };
            let owner = self.types.by_tag(tag)?;
            return Some(qkey(&owner.scope.module, &owner.name));
        }
        head_name(carrier).map(|h| self.carrier_key(h))
    }

    /// A solver parameter's written class goal with its constructor
    /// parameter replaced by the constructor the call solved it to —
    /// `Bind<M>` shown as `Bind<List>` — for a class over a type constructor
    /// (issues/higher-kinded-classes.md). `key` is
    /// [`Self::solver_carrier_head`]'s answer; `None` for every other goal.
    pub(crate) fn kinded_goal_display(
        &self,
        written: &Ty,
        params: &[ParamMeta],
        key: &str,
    ) -> Option<String> {
        let reference = self.class_ref_of_ty(written)?;
        let class = self.lookup_class(&reference.name)?;
        if !class.is_kinded() {
            return None;
        }
        let shown = key.rsplit("::").next().unwrap_or(key).to_string();
        let mut changed = false;
        let args: Vec<Ty> = reference
            .args
            .iter()
            .zip(&class.kinds)
            .map(|(a, k)| match (&a.kind, k) {
                (TyKind::Named { name, args }, Some(_))
                    if args.is_empty() && params.iter().any(|p| !p.is_type && p.name == *name) =>
                {
                    changed = true;
                    Ty { kind: TyKind::Named { name: shown.clone(), args: Vec::new() }, span: a.span }
                }
                _ => a.clone(),
            })
            .collect();
        changed.then(|| {
            render_ty(&heather_syntax::class_ty(reference.name, args, reference.index, written.span))
        })
    }

    /// The **index spelling** of an instance head
    /// (docs/operation-indexed-classes-design.md §3.1): each index argument's
    /// resolved global key, joined. A direct generic binder instead contributes
    /// its alpha-stable binder position. Both are *keys* computed from the
    /// declaration alone. An arbitrary λ is refused here, and the alternative
    /// is stated: a structure built from an unnamed operation is what scope is
    /// for.
    fn index_spelling(
        &self,
        cref: &ClassRef,
        class: &ClassInfo,
        decl: &InstanceDecl,
    ) -> R<String> {
        let mut parts = Vec::with_capacity(cref.index.len());
        for (p, a) in class.valparams.iter().zip(cref.index.iter()) {
            let head = match &a.kind {
                ExprKind::Var(n) => Some(n),
                ExprKind::TyApp { head, .. } => match &head.kind {
                    ExprKind::Var(n) => Some(n),
                    _ => None,
                },
                _ => None,
            };
            let Some(n) = head else {
                // A symbol in an instance head would make the registry key
                // depend on the designation table's state at declaration
                // time, which the key exists not to depend on.
                if let ExprKind::OpSymbol { symbol: s, .. } = &a.kind {
                    return err(
                        format!(
                            "an instance names its index by the **operation**, not by a \
                             symbol: write the operation `{s}` designates here. A \
                             designation says what a symbol means at a carrier \
                             (`designation {s} at … := …`); the registry key is the \
                             operation, so the two stay separable \
                             (docs/operators-onto-classes-design.md §3.3)"
                        ),
                        a.span,
                    );
                }
                return err(
                    format!(
                        "the index `{}` of this instance is not spellable: `{}` must be a \
                         global reference (possibly at this instance's own type \
                         parameters), because the registry key is computed from the \
                         declaration alone (docs/operation-indexed-classes-design.md \
                         §3.1). A structure built from an unnamed operation is a `let`-bound \
                         value, found by scope rather than registered",
                        p.name,
                        render_expr(a)
                    ),
                    a.span,
                );
            };
            // A value-generic index is determined by unifying the candidate
            // head with the goal, just like a binder in the carrier. Give it
            // a declaration-stable, unwritable key component: binder spelling
            // must not make alpha-equivalent instances distinct.
            let generic = decl
                .tyvars
                .iter()
                .map(|p| &p.name)
                .chain(decl.valparams.iter().map(|p| &p.name))
                .position(|name| name == n);
            parts.push(match generic {
                Some(i) => format!("#binder{i}"),
                None => self.key_of(n).unwrap_or_else(|| n.clone()),
            });
        }
        Ok(parts.join(", "))
    }

    /// A parent class reference, resolved, with the renaming that instantiates
    /// it at the child's arguments. Layer 1 restricts the arguments to the
    /// child's own type parameters, so instantiation is a rename (design §3).
    fn parent_view(&self, d: &ClassDecl, parent: &ClassRef) -> R<(Rc<ClassInfo>, Ren)> {
        let info = match self.lookup_class(&parent.name) {
            Some(i) => i,
            None => return Err(self.not_a_class(&parent.name, "extends", parent.span)),
        };
        if info.params.len() != parent.args.len() {
            return err(
                format!(
                    "`{}` takes {} type argument(s), {} given",
                    parent.name,
                    info.params.len(),
                    parent.args.len()
                ),
                parent.span,
            );
        }
        let mut rename = Ren::new();
        for (p, a) in info.params.iter().zip(parent.args.iter()) {
            let arg = match &a.kind {
                TyKind::Named { name, args } if args.is_empty() && d.params.contains(name) => {
                    name.clone()
                }
                _ => {
                    return err(
                        format!(
                            "an `extends` argument must be one of `{}`'s own type parameters \
                             (`{}`), and `{}` is not: instantiating a parent at a composite \
                             type is refused at layer 1 rather than half-supported \
                             (docs/traits-layer1-design.md §3)",
                            d.name,
                            d.params.join(", "),
                            render_ty(a)
                        ),
                        a.span,
                    );
                }
            };
            rename.insert(p.clone(), arg);
        }
        // The parent's **index**, at the child's own spelling
        // (docs/operation-indexed-classes-design.md §3): a single-op chain
        // passes its index up unchanged, so an `extends` index argument is
        // restricted exactly as an `extends` type argument is — to one of the
        // child's own value parameters — which keeps instantiating the parent
        // a rename rather than a substitution.
        if info.valparams.len() != parent.index.len() {
            return err(
                format!(
                    "`{}` takes {} index argument(s), {} given: write `extends {}<…>({})`",
                    parent.name,
                    info.valparams.len(),
                    parent.index.len(),
                    parent.name,
                    info.valparams
                        .iter()
                        .map(|p| p.name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                parent.span,
            );
        }
        for (p, a) in info.valparams.iter().zip(parent.index.iter()) {
            let ExprKind::Var(n) = &a.kind else {
                return err(
                    format!(
                        "an `extends` index must be one of `{}`'s own value parameters \
                         (`{}`), and `{}` is not: a chain passes its index up unchanged, \
                         and a parent at a *computed* index is the diamond \
                         (docs/operation-indexed-classes-design.md §8), not this form",
                        d.name,
                        d.valparams
                            .iter()
                            .map(|p| p.name.as_str())
                            .collect::<Vec<_>>()
                            .join(", "),
                        render_expr(a)
                    ),
                    a.span,
                );
            };
            if !d.valparams.iter().any(|q| q.name == *n) {
                return err(
                    format!(
                        "`{n}` is not a value parameter of `{}`: an `extends` index must be \
                         one of the child's own (`{}`)",
                        d.name,
                        d.valparams
                            .iter()
                            .map(|p| p.name.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    a.span,
                );
            }
            rename.insert(p.name.clone(), n.clone());
            if let Some(sym) = &p.symbol {
                rename.insert(symbol_key(sym), n.clone());
            }
        }
        Ok((info, rename))
    }

    /// The diagnostic for a name in class position that is not a class. A
    /// *declared* type gets told what it is: `instance R<Z>` on a `record R`
    /// is the mistake this catches, and "unbound name" would be a lie.
    fn not_a_class(&self, name: &str, what: &str, span: Span) -> ElabError {
        if self.lookup_inductive(name).is_some() {
            return ElabError::Elab {
                msg: format!(
                    "`{name}` is not a class, so it has no instances and cannot be \
                     extended: `{what}` takes a `class`, and a plain `record` value is \
                     written as an ordinary `fn`"
                ),
                span,
            };
        }
        self.name_miss(name, format!("`{name}` is not a class in scope"), span)
    }

    /// Does every field of the class state a proposition rather than hold
    /// data? A field whose type ends in a named type (the carrier, `Nat`, a
    /// list), a universe, or an applied type former or class (a dictionary)
    /// is data; one ending in an equation, a squash, or an applied relation
    /// or predicate is a proof. Conservative: a proposition spelled as a
    /// named type counts as data, which only refuses a sharing.
    fn proof_only(&self, info: &ClassInfo) -> bool {
        fn result(t: &Ty) -> &Ty {
            match &t.kind {
                TyKind::Fn { cod, .. } => result(cod),
                _ => t,
            }
        }
        info.fields.iter().all(|f| match &result(&f.ty).kind {
            TyKind::Eq(..) | TyKind::Squash(_) => true,
            TyKind::OfExpr(e) => match &e.kind {
                ExprKind::App { head, .. } => match crate::inductive::named_head(head) {
                    Some((name, _)) => {
                        self.lookup_class(name).is_none() && self.lookup_inductive(name).is_none()
                    }
                    None => true,
                },
                _ => true,
            },
            _ => false,
        })
    }

    pub(crate) fn lookup_class(&self, name: &str) -> Option<Rc<ClassInfo>> {
        self.traits.class(&self.key_of(name)?).cloned()
    }

    /// A written head of a class over a type constructor, re-spelled as the
    /// record it lowers to (issues/higher-kinded-classes.md, piece 3):
    ///
    /// ```text
    /// Bind<Option>            ⇝  Bind(Option)
    /// StateM<S, M>(op)        ⇝  StateM<S>(M, op)      (M kinded, S not)
    /// ```
    ///
    /// A kinded parameter is a term, so the class's record takes it as a
    /// leading value parameter ([`Self::elab_class`]); the angle-bracket
    /// spelling stays the class's interface, which every reader of a
    /// [`ClassRef`] (registry keys, canonical names, `requires`) keeps
    /// seeing. The argument becomes an expression: a bare generic name is
    /// then checked at the kind, which is the η-expansion
    /// `check_generic_former_value` does, and a parameter `M` is a local.
    /// `None` for every type that is not such a head, so nothing else moves.
    pub(crate) fn kinded_class_ty(&self, ty: &Ty) -> Option<Ty> {
        let (name, args, index): (&str, &[Ty], &[Expr]) = match &ty.kind {
            TyKind::Named { name, args } => (name, args, &[]),
            TyKind::OfExpr(e) => match &e.kind {
                ExprKind::App {
                    head,
                    args: index,
                    named,
                    explicit: false,
                    goal_oriented: false,
                } if named.is_empty() => match &head.kind {
                    ExprKind::TyApp { head: h, args } => match &h.kind {
                        ExprKind::Var(n) => (n, args, index),
                        _ => return None,
                    },
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        };
        if args.is_empty() || !self.traits.maybe_kinded(name) {
            return None;
        }
        let info = self.lookup_class(name)?;
        if info.kinds.len() != args.len() || info.kinds.iter().all(Option::is_none) {
            return None;
        }
        let span = ty.span;
        let mut targs = Vec::new();
        let mut vargs = Vec::new();
        for (a, k) in args.iter().zip(&info.kinds) {
            match k {
                None => targs.push(a.clone()),
                Some(_) => vargs.push(ty_as_expr(a)?),
            }
        }
        vargs.extend(index.iter().cloned());
        let head = var(name, span);
        let head = if targs.is_empty() {
            head
        } else {
            span_expr(ExprKind::TyApp { head: Box::new(head), args: targs }, span)
        };
        Some(Ty {
            kind: TyKind::OfExpr(Box::new(span_expr(
                ExprKind::App {
                    head: Box::new(head),
                    args: vargs,
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            ))),
            span,
        })
    }

    /// A parameter's type read as a **class reference**: the class's name, its
    /// type arguments, and its written index arguments. Both spellings — the
    /// unindexed `Named` one and the applied `OfExpr` one
    /// [`heather_syntax::class_ty`] builds — read back through here, so no
    /// consumer has to know which it is holding.
    pub(crate) fn class_ref_of_ty(&self, t: &Ty) -> Option<ClassRef> {
        match &t.kind {
            TyKind::Named { name, args } if self.lookup_class(name).is_some() => Some(ClassRef {
                name: name.clone(),
                args: args.clone(),
                index: Vec::new(),
                path: Vec::new(),
                span: t.span,
            }),
            TyKind::OfExpr(e) => {
                let ExprKind::App { head, args, .. } = &e.kind else {
                    return None;
                };
                let (name, targs) = crate::inductive::named_head(head)?;
                self.lookup_class(name)?;
                Some(ClassRef {
                    name: name.to_string(),
                    args: targs.to_vec(),
                    index: args.clone(),
                    path: Vec::new(),
                    span: t.span,
                })
            }
            _ => None,
        }
    }

    /// Inline constraints that **share a symbol at one carrier** become one
    /// constraint at a synthesized class extending them all
    /// (issues/constraints-sharing-indices.md).
    ///
    /// `<A: OrderedField(≈, <, <=, +, *) + CommRingOfInt(≈, +, *)>` names one
    /// `≈`, one `+` and one `*`, and both classes reach `CommRing` over them.
    /// Two dictionaries would hold two `CommRing`s, and a lemma mixing laws
    /// from both sides would be stated over two different units; linking the
    /// second constraint's index to the first's binders shares the
    /// operations but not the ancestor. One dictionary of the class
    /// `CommRingOfInt+OrderedField`, whose `extends` flattens the shared
    /// ancestor once, is what the writer meant: both classes are reached from
    /// it by upcast, through one `CommRing`. A concrete carrier assembles it
    /// from its two instances at resolution ([`Elaborator::join_parents`]),
    /// which is sound there because the carrier's canonical instances already
    /// share their ancestors by reference.
    ///
    /// The class is synthesized in this module the first time a declaration
    /// asks for it and found by name after that. Its parents are sorted by
    /// name, so the constraint's written order does not make a second class.
    /// Only anonymous constraints whose every index slot is a symbol merge;
    /// anything else is left to [`Self::expand_constraints`] unchanged.
    pub(crate) fn merge_linked_constraints(&mut self, decl: &Decl) -> R<Option<Decl>> {
        // Each candidate: (position, its class reference, the class, the
        // carrier as written).
        let mut cands: Vec<(usize, ClassRef, Rc<ClassInfo>, Vec<String>)> = Vec::new();
        for (i, p) in decl.params.iter().enumerate() {
            if p.solver.is_none() || !p.name.starts_with("#constraint") {
                continue;
            }
            let Some(r) = self.class_ref_of_ty(&p.ty) else { continue };
            let Some(class) = self.lookup_class(&r.name) else { continue };
            if class.valparams.is_empty()
                || class.is_kinded()
                || r.index.len() != class.valparams.len()
                || !r.index.iter().all(|a| matches!(a.kind, ExprKind::OpSymbol { .. }))
            {
                continue;
            }
            let carrier = r.args.iter().map(render_ty).collect();
            cands.push((i, r, class, carrier));
        }
        if cands.len() < 2 {
            return Ok(None);
        }
        let symbols_of = |r: &ClassRef| -> Vec<String> {
            r.index
                .iter()
                .filter_map(|a| match &a.kind {
                    ExprKind::OpSymbol { symbol, .. } => Some(symbol.clone()),
                    _ => None,
                })
                .collect()
        };
        // Connected components under "same carrier, a symbol in common".
        let n = cands.len();
        let mut comp: Vec<usize> = (0..n).collect();
        fn root(comp: &mut [usize], mut i: usize) -> usize {
            while comp[i] != i {
                comp[i] = comp[comp[i]];
                i = comp[i];
            }
            i
        }
        for a in 0..n {
            for b in a + 1..n {
                if cands[a].3 != cands[b].3 {
                    continue;
                }
                let sa = symbols_of(&cands[a].1);
                if symbols_of(&cands[b].1).iter().any(|s| sa.contains(s)) {
                    let (ra, rb) = (root(&mut comp, a), root(&mut comp, b));
                    comp[rb] = ra;
                }
            }
        }
        let roots: Vec<usize> = (0..n).map(|i| root(&mut comp, i)).collect();
        let mut groups: Vec<Vec<usize>> = Vec::new();
        for i in 0..n {
            match groups.iter_mut().find(|g| roots[g[0]] == roots[i]) {
                Some(g) => g.push(i),
                None => groups.push(vec![i]),
            }
        }
        groups.retain(|g| g.len() >= 2);
        if groups.is_empty() {
            return Ok(None);
        }
        let mut params = decl.params.clone();
        let mut drop: Vec<usize> = Vec::new();
        for g in groups {
            let mut members: Vec<&(usize, ClassRef, Rc<ClassInfo>, Vec<String>)> =
                g.iter().map(|&k| &cands[k]).collect();
            // A class written twice is §5.2's business, not a merge.
            if members
                .iter()
                .enumerate()
                .any(|(i, m)| members[..i].iter().any(|q| q.2.name == m.2.name))
            {
                continue;
            }
            members.sort_by(|a, b| a.2.name.cmp(&b.2.name));
            let first = members[0];
            let span = decl.params[first.0].span;
            // The merged class's parameters are its first parent's, and every
            // other parent's are renamed onto them positionally; the carriers
            // agree, so the arities do.
            let cparams = first.2.params.clone();
            if members.iter().any(|m| m.2.params.len() != cparams.len()) {
                continue;
            }
            // One value parameter per distinct symbol, in first-occurrence
            // order over the sorted parents, under its first parent's name.
            let mut syms: Vec<String> = Vec::new();
            let mut sym_exprs: Vec<Expr> = Vec::new();
            let mut valparams: Vec<Param> = Vec::new();
            let mut extends: Vec<ClassRef> = Vec::new();
            for m in &members {
                let sub: HashMap<String, Ty> = m
                    .2
                    .params
                    .iter()
                    .cloned()
                    .zip(cparams.iter().map(|p| Ty {
                        kind: TyKind::Named { name: p.clone(), args: vec![] },
                        span,
                    }))
                    .collect();
                let mut index: Vec<Expr> = Vec::new();
                for (v, a) in m.2.valparams.iter().zip(m.1.index.iter()) {
                    let ExprKind::OpSymbol { symbol, .. } = &a.kind else { unreachable!() };
                    let k = match syms.iter().position(|s| s == symbol) {
                        Some(k) => k,
                        None => {
                            let mut name = v.name.clone();
                            if valparams.iter().any(|q: &Param| q.name == name)
                                || cparams.contains(&name)
                            {
                                name = format!("{name}_{}", valparams.len());
                            }
                            syms.push(symbol.clone());
                            sym_exprs.push(a.clone());
                            valparams.push(Param {
                                name,
                                ty: subst_ty(&sub, &v.ty),
                                symbol: None,
                                default: None,
                                solver: None,
                                ..v.clone()
                            });
                            syms.len() - 1
                        }
                    };
                    index.push(var(&valparams[k].name, span));
                }
                // By key, so the join can find the parent from a module that
                // does not import it by its bare name.
                let pkey = self.key_of(&m.1.name).unwrap_or_else(|| m.1.name.clone());
                extends.push(ClassRef {
                    name: pkey,
                    args: cparams
                        .iter()
                        .map(|p| Ty { kind: TyKind::Named { name: p.clone(), args: vec![] }, span })
                        .collect(),
                    index,
                    path: Vec::new(),
                    span,
                });
            }
            let name = members.iter().map(|m| m.2.name.as_str()).collect::<Vec<_>>().join("+");
            match self.lookup_class(&name) {
                // Found by name: the same parents, linked the same way, or a
                // different linking that this declaration cannot share.
                Some(have) => {
                    let same = have.valparams.len() == valparams.len()
                        && extends.iter().all(|e| {
                            have.ancestors.iter().any(|a| {
                                a.path.is_empty()
                                    && a.name == e.name
                                    && a.index.iter().map(render_expr).eq(e.index.iter().map(render_expr))
                            })
                        });
                    if !same {
                        return err(
                            format!(
                                "these constraints share symbols at one carrier, so they are one \
                                 dictionary of `{name}`; that class is already in scope with \
                                 its parents' indices linked differently. Write the shared \
                                 symbols in the same slots (issues/constraints-sharing-indices.md)"
                            ),
                            span,
                        );
                    }
                }
                None => self.elab_class(&ClassDecl {
                    name: name.clone(),
                    params: cparams.clone(),
                    kinds: vec![None; cparams.len()],
                    valparams,
                    extends,
                    fields: Vec::new(),
                    span,
                })?,
            }
            let p = &mut params[first.0];
            p.ty = heather_syntax::class_ty(name, first.1.args.clone(), sym_exprs, p.ty.span);
            // The merged binder stands where the earliest member was written.
            let earliest = members.iter().map(|m| m.0).min().expect("a group has members");
            if earliest != first.0 {
                params.swap(earliest, first.0);
            }
            drop.extend(members.iter().map(|m| m.0).filter(|&i| i != earliest));
        }
        if drop.is_empty() {
            return Ok(None);
        }
        let params = params
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !drop.contains(i))
            .map(|(_, p)| p)
            .collect();
        Ok(Some(Decl { params, ..decl.clone() }))
    }

    /// The constraint binders' desugaring
    /// (docs/operation-indexed-classes-design.md §4, §4.1).
    ///
    /// At an **indexed** class a solver parameter with an EMPTY index slot
    /// grows the index binders in front of it, under the class's own declared
    /// parameter names — so the body writes `op` as an ordinary variable and
    /// the operation rides exactly the machinery the carrier type rides. A
    /// LINKED slot (`<A: Monoid(op)>`) binds nothing and instead floats the
    /// dictionary binder past the parameters it names, which is the whole of
    /// the forward-reference license: only a constraint's index slot, only into
    /// its own declaration's parameter list, written order still authoritative
    /// for every positional call site and every diagnostic.
    ///
    /// A no-op for every declaration with no indexed-class constraint, which is
    /// every declaration written before this grammar existed.
    #[allow(clippy::type_complexity)]
    pub(crate) fn expand_constraints(&self, decl: &Decl) -> R<Option<Expanded>> {
        let mut refs: Vec<Option<ClassRef>> = Vec::with_capacity(decl.params.len());
        let mut indexed = false;
        for p in &decl.params {
            let r = p
                .solver
                .is_some()
                .then(|| self.class_ref_of_ty(&p.ty))
                .flatten();
            indexed |= r
                .as_ref()
                .and_then(|r| self.lookup_class(&r.name))
                .is_some_and(|c| !c.valparams.is_empty());
            refs.push(r);
        }
        if !indexed {
            return Ok(None);
        }
        // Which classes appear more than once among the constraints: §5.2's
        // uniqueness rule, decided before any binder is named.
        let mut repeated: Vec<String> = Vec::new();
        for (i, r) in refs.iter().enumerate() {
            let Some(r) = r else { continue };
            if refs[..i].iter().flatten().any(|q| q.name == r.name) {
                repeated.push(r.name.clone());
            }
        }
        // §5.2: the bare declared index name binds only when its class appears
        // once in the constraint list. Where it does not, the name is bound by
        // nothing and a bare use is refused *naming both constraints* — which
        // is a better answer than "unbound name" for a name the reader has
        // every reason to expect.
        let mut ambiguous: Vec<(String, String)> = Vec::new();
        // The symbols a SYMBOL slot installs, in written order — later
        // entries shadow earlier ones, which is `Cx::op_locals`'s rule.
        let mut symbols: Vec<(String, String)> = Vec::new();
        for c in &repeated {
            let Some(class) = self.lookup_class(c) else {
                continue;
            };
            let at = refs
                .iter()
                .flatten()
                .filter(|r| r.name == *c)
                .map(class_ref_written)
                .collect::<Vec<_>>()
                .join("` and `");
            for v in &class.valparams {
                ambiguous.push((
                    v.name.clone(),
                    format!(
                        "`{}` is the index of `{c}`, and `{c}` constrains this \
                         declaration twice (`{at}`): the bare name binds only where the \
                         class appears once. Link each index to a parameter \
                         (`<A: {c}({}1) + {c}({}2)>`) and write the one you mean",
                        v.name, v.name, v.name
                    ),
                ));
            }
        }
        let mut out: Vec<Param> = Vec::new();
        // Where each written parameter ended up, so the float below can be
        // stated over positions rather than over names.
        for (i, p) in decl.params.iter().enumerate() {
            let Some(r) = &refs[i] else {
                out.push(p.clone());
                continue;
            };
            let Some(class) = self.lookup_class(&r.name) else {
                out.push(p.clone());
                continue;
            };
            if class.valparams.is_empty() {
                out.push(p.clone());
                continue;
            }
            if !r.index.is_empty() {
                if r.index.len() != class.valparams.len() {
                    return err(
                        format!(
                            "`{}` takes {} index argument(s), {} given",
                            r.name,
                            class.valparams.len(),
                            r.index.len()
                        ),
                        p.span,
                    );
                }
                // SYMBOL (docs/operators-onto-classes-design.md §5): a slot
                // written as an operator binds the index like an EMPTY slot
                // does — an ordinary implicit, filled by unification — and
                // additionally *installs* the symbol as that binder's local
                // meaning for the whole declaration. A mixed list
                // (`Semiring<A>(+, mul)`) is per-slot, because there is
                // nothing to gain from refusing it.
                if !r
                    .index
                    .iter()
                    .any(|a| matches!(a.kind, ExprKind::OpSymbol { .. }))
                {
                    out.push(p.clone());
                    continue;
                }
                let sub: HashMap<String, Ty> = class
                    .params
                    .iter()
                    .cloned()
                    .zip(r.args.iter().cloned())
                    .collect();
                let mut index: Vec<Expr> = Vec::new();
                for (k, (v, a)) in class.valparams.iter().zip(r.index.iter()).enumerate() {
                    let ExprKind::OpSymbol { symbol: sym, .. } = &a.kind else {
                        index.push(a.clone());
                        continue;
                    };
                    // The generated name **carries its symbol**, because the
                    // call site has to recover "this slot was designated by
                    // `+`" from the callee's parameter list and nothing else
                    // travels there (§5.1). `#` never begins an identifier, so
                    // the name is unspellable and free to be a record.
                    let name = op_index_binder(sym, i, k);
                    symbols.push((sym.clone(), name.clone()));
                    // §5.1: each referent binds exactly one spelling, and a
                    // SYMBOL slot's is the symbol. The declared name is left
                    // bound to nothing, and a bare use of it says which
                    // spelling does work — the same device §5.2 uses, and
                    // consulted at the same one place.
                    ambiguous.push((
                        v.name.clone(),
                        format!(
                            "`{}` is the index of `{}`, and `<…: {}({sym})>` binds it under \
                             the SYMBOL: write `x {sym} y`, which is the same binder. Each \
                             of the index slot's three referents binds one spelling — the \
                             empty slot binds `{}`, a linked slot binds your parameter's \
                             name, and a symbol binds the symbol \
                             (docs/operators-onto-classes-design.md §5.1)",
                            v.name, r.name, r.name, v.name
                        ),
                    ));
                    out.push(Param {
                        name: name.clone(),
                        ty: subst_ty(&sub, &v.ty),
                        implicit: true,
                        is_self: false,
                        solver: None,
                        default: None,
                        origin: heather_syntax::ParamOrigin::Written,
                        // The generated index binder is not a declaring
                        // occurrence the user wrote, and a class's own `as`
                        // is strictly local to its body — it is not an
                        // advertisement to its users' binders
                        // (issues/class-default-operators.md owns that).
                        symbol: None,
                        span: p.span,
                    });
                    index.push(var(&name, p.span));
                }
                let mut p = p.clone();
                p.ty = heather_syntax::class_ty(r.name.clone(), r.args.clone(), index, p.ty.span);
                out.push(p);
                continue;
            }
            // EMPTY: the index binders, then the instance binder over them.
            let sub: HashMap<String, Ty> = class
                .params
                .iter()
                .cloned()
                .zip(r.args.iter().cloned())
                .collect();
            let mut index: Vec<Expr> = Vec::new();
            for (k, v) in class.valparams.iter().enumerate() {
                let bare = !repeated.contains(&r.name);
                let name = if bare {
                    v.name.clone()
                } else {
                    format!("#index{i}_{k}")
                };
                if bare
                    && (decl.params.iter().any(|q| q.name == name)
                        || decl.tyvars.iter().any(|q| q.name == name))
                {
                    return err(
                        format!(
                            "`{name}` is already bound here, and `<{}: {}>` binds the index \
                             under `{}`'s own parameter name: link the index instead \
                             (`{}({name})`), which says the two are the same thing rather \
                             than shadowing one with the other",
                            render_ty(&r.args[0]),
                            r.name,
                            r.name,
                            r.name
                        ),
                        p.span,
                    );
                }
                out.push(Param {
                    name: name.clone(),
                    ty: subst_ty(&sub, &v.ty),
                    implicit: true,
                    is_self: false,
                    solver: None,
                    default: None,
                    origin: heather_syntax::ParamOrigin::Written,
                    symbol: None,
                    span: p.span,
                });
                index.push(var(&name, p.span));
            }
            let mut p = p.clone();
            p.ty = heather_syntax::class_ty(r.name.clone(), r.args.clone(), index, p.ty.span);
            out.push(p);
        }
        self.float_linked(decl, &mut out)?;
        Ok(Some(Expanded {
            params: out,
            ambiguous,
            symbols,
        }))
    }

    /// The linked slot's float (§4.1): a constraint binder moves to just after
    /// the last parameter its index names, and nothing else moves. A parameter
    /// that mentions a constraint the constraint would have to follow is the
    /// dependency cycle, refused by name.
    fn float_linked(&self, decl: &Decl, params: &mut Vec<Param>) -> R<()> {
        let pos = |name: &str| params.iter().position(|q| q.name == name);
        let mut keys: Vec<(usize, usize)> = (0..params.len()).map(|i| (i * 2, i)).collect();
        let mut moved: Vec<(usize, usize)> = Vec::new();
        for (i, p) in params.iter().enumerate() {
            if p.solver.is_none() {
                continue;
            }
            let Some(r) = self.class_ref_of_ty(&p.ty) else {
                continue;
            };
            let mut want = i * 2;
            for a in &r.index {
                let ExprKind::Var(n) = &a.kind else { continue };
                // A *global* index needs no float: `requires m: Mon<U>(ul)`
                // names a declaration, not a parameter, and the slot is
                // already ground where the binder stands.
                if pos(n).is_none()
                    && (self.lookup_global(n).is_some() || self.ctor_of(n).is_some())
                {
                    continue;
                }
                let Some(j) = pos(n) else {
                    return err(
                        format!(
                            "`{n}` is not a parameter of `{}`: a constraint's index slot links \
                             the index to an explicit parameter of this same declaration \
                             (`<A: {}({n})>(…, {n}: …)`), and that is the only forward \
                             reference the language has",
                            decl.name, r.name
                        ),
                        a.span,
                    );
                };
                want = want.max(j * 2 + 1);
            }
            if want > i * 2 {
                moved.push((i, want));
                keys[i].0 = want;
            }
        }
        if moved.is_empty() {
            return Ok(());
        }
        // A cycle: an earlier parameter's type names the very dictionary that
        // now has to follow it. Only a `requires` binder is nameable, so this
        // is the one shape that can close the loop.
        for (i, want) in &moved {
            let name = &params[*i].name;
            if name.starts_with('#') {
                continue;
            }
            for (j, q) in params.iter().enumerate() {
                if j * 2 <= *want && j != *i && ty_mentions(&q.ty, name) {
                    return err(
                        format!(
                            "`{name}` and `{}` depend on each other: `{name}`'s index names \
                             `{}`, whose type names `{name}` — a constraint's index may look \
                             forward, and a cycle is refused rather than ordered by guess",
                            q.name, q.name
                        ),
                        params[*i].span,
                    );
                }
            }
        }
        keys.sort();
        let src = std::mem::take(params);
        let mut src: Vec<Option<Param>> = src.into_iter().map(Some).collect();
        for (_, i) in keys {
            params.push(src[i].take().expect("each index taken once"));
        }
        Ok(())
    }

    /// The colon in a type-parameter list carries two nouns — a **universe**
    /// (`<A: Type<n>>`, where `A` lives) and a **class** (`<A: Monoid>`, what
    /// `A` carries) — told apart by the head word alone
    /// (issues/requires-placement-syntax.md §R2-A). A word that is neither is
    /// the one place that reading can go wrong, so it is reported here, naming
    /// both readings, rather than falling out of the desugared type as
    /// "unknown type `Nat`" — a complaint about `Nat<A>`, which the user never
    /// wrote.
    ///
    /// Constraint parameters are recognized by their unspellable `#`-prefixed
    /// binder name, which is the parser's mark that this `Param` came from the
    /// inline form and not from a `requires` binder (whose type is checked by
    /// the ordinary class-reference path, with the user's own name to blame).
    pub(crate) fn check_constraint_param(&self, p: &Param) -> R<()> {
        if !p.name.starts_with("#constraint") {
            return Ok(());
        }
        // The applied spelling (`<A: Monoid(op)>`) is already a class reference
        // by construction — nothing else parses into it — so only the bare one
        // can name a non-class.
        let TyKind::Named { name, .. } = &p.ty.kind else {
            return Ok(());
        };
        if self.lookup_class(name).is_some() {
            return Ok(());
        }
        err(
            format!(
                "`{name}` is not a class, so it cannot constrain a type parameter. \
                 After the colon in `<A: …>` there are two readings and this is \
                 neither: a UNIVERSE — `Type`, `Type<n>` — saying where `A` lives, or \
                 the name of a `class`, saying what `A` carries"
            ),
            p.span,
        )
    }

    // -- designations -------------------------------------------------------

    /// `designation + at Nat := add`
    /// (docs/operators-onto-classes-design.md §3).
    ///
    /// A table entry and nothing else: no global is minted, no value is
    /// assembled, nothing reaches Ψ. What it buys is that the symbol `+` has a
    /// meaning at that carrier, which is the half of an operator that the
    /// parser could never supply.
    pub(crate) fn elab_designation(&mut self, d: &DesignationDecl) -> R<()> {
        let Some(head) = head_name(&d.carrier) else {
            return err(
                format!(
                    "the carrier `{}` has no head type name, so `{}` has nothing to be \
                     designated at: a designation is keyed on the carrier's *head*, \
                     exactly as an instance's canonical name is",
                    render_ty(&d.carrier),
                    d.symbol
                ),
                d.carrier.span,
            );
        };
        let head = head.to_string();
        // A type parameter of this very declaration is not a carrier: it names
        // no head, so keying on it would key on a binder.
        if !self.names_a_carrier(&head) || d.tyvars.contains(&head) {
            return err(
                format!(
                    "`{head}` is not a type or a type former in scope, so a designation \
                     of `{}` at it attaches to nothing",
                    d.symbol
                ),
                d.carrier.span,
            );
        }
        // The right-hand side is a **bare global name** (§3.2): a designated
        // operation is emitted bare at each use site and instantiated there by
        // ordinary implicit inference, which is how `mconcat(append, xss)`
        // already reaches the generic instance. A written type application
        // would pin the wrong site's arguments, so it is refused here rather
        // than half-supported.
        let ExprKind::Var(op) = &d.op.kind else {
            return err(
                format!(
                    "the operation `{}` designates must be a bare global name, and this \
                     is not: it is emitted bare at each use site and instantiated there, \
                     so a written type application — or anything unnamed — would pin this \
                     declaration's arguments rather than the caller's \
                     (docs/operators-onto-classes-design.md §3.2). Name the operation, or \
                     declare one that wraps it",
                    d.symbol
                ),
                d.op.span,
            );
        };
        if self.lookup_global(op.as_str()).is_none() && self.ctor_of(op.as_str()).is_none() {
            return Err(self.name_miss(
                op.as_str(),
                format!(
                    "`{op}` is not in scope, so `{}` cannot designate it at `{head}`",
                    d.symbol
                ),
                d.op.span,
            ));
        }
        let op = self.key_of(op.as_str()).unwrap_or_else(|| op.clone());
        let written = format!(
            "designation {}{} at {} := {}",
            match d.fixity {
                OpFixity::Prefix => "prefix ",
                OpFixity::Postfix => "postfix ",
                OpFixity::Infix => "",
            },
            d.symbol,
            render_ty(&d.carrier),
            render_expr(&d.op)
        );
        // The carrier as the table keys it: the *declaration* the head names,
        // not the head's spelling
        // (issues/designation-key-collides-across-modules.md). `head` itself
        // stays the written string — it is what a diagnostic prints and what
        // `DesignationInfo::carrier` keeps for the read side.
        let head_key = self.carrier_key(&head);
        let key = designation_key(d.fixity, &d.symbol, &head_key);
        if let Some(prev) = self.traits.designation(&key) {
            return err(
                format!(
                    "`{}` already designates `{}` at `{head_key}` (`{}`): a designation is \
                     keyed on its symbol and its **resolved** carrier, so this is the same \
                     carrier declaration and not merely the same written name — one entry \
                     per (symbol, carrier), refused rather than silently overwritten. Two \
                     operations at one carrier are two *symbols* — which is how `+` is \
                     `or` and `*` is `and` at `Bool` \
                     (docs/instance-resolved-key-design.md §3)",
                    d.symbol, prev.op, prev.written
                ),
                d.span,
            );
        }
        let info = DesignationInfo { op, written, carrier: head };
        self.semantic_commit_designation(key, info);
        Ok(())
    }

    /// The operation `sym` designates at the carrier `head_key`, if any. The
    /// whole of the designation table's read side.
    ///
    /// `head_key` is **resolved**, never a written head: every caller reaches
    /// this through [`Elaborator::carrier_of_ty`] (a lowered operand) or
    /// [`Elaborator::carrier_key`] (a name the writer spelled), so that a
    /// lookup lands on the key the declaration registered even where two
    /// modules declare the head's name.
    pub(crate) fn designated(&self, sym: &str, fixity: OpFixity, head_key: &str) -> Option<String> {
        self.traits
            .designated(fixity, sym, head_key)
            .map(str::to_string)
    }

    /// Every designation at one carrier, as `` (`+`, `or`) `` pairs sorted by
    /// symbol — what a value-slot refusal lists so that the reader is told
    /// which binder would have worked (§6, §7). `head_key` is resolved, as
    /// [`Self::designated`]'s is.
    pub(crate) fn designations_at(&self, head_key: &str) -> Vec<(String, String)> {
        self.traits.designations_at(head_key)
    }

    // -- instances ----------------------------------------------------------

    /// `instance C<T⃗> { … }` (design §4).
    ///
    /// All-or-nothing, like every other declaration form: an instance emits
    /// several globals (its members, its value, its synthesized parents, its
    /// agreement certificates) and a failure at any of them must leave none of
    /// them behind. `Elaborator` is cheaply clonable exactly so that this kind
    /// of speculative work is expressible (`lib.rs`, the `Clone` note).
    pub(crate) fn elab_instance(&mut self, d: &InstanceDecl) -> R<()> {
        let snapshot = self.clone();
        let r = self.elab_instance_inner(d);
        if r.is_err() {
            // Through `restore_from_clone`, never `*self = snapshot`: the
            // kernel gate is the module's, not this declaration's, and a
            // clone's is inline and empty (`lib.rs`, and
            // `docs/parallel-kernel-gate-design.md` §5.1).
            self.restore_from_clone(snapshot);
        }
        r
    }

    fn elab_instance_inner(&mut self, d: &InstanceDecl) -> R<()> {
        let class = match self.lookup_class(&d.class.name) {
            Some(c) => c,
            None => return Err(self.not_a_class(&d.class.name, "instance", d.class.span)),
        };
        let class_key = self
            .key_of(&d.class.name)
            .expect("a class that resolved has a key");
        if class.params.len() != d.class.args.len() {
            return err(
                format!(
                    "`{}` takes {} type argument(s), {} given",
                    d.class.name,
                    class.params.len(),
                    d.class.args.len()
                ),
                d.class.span,
            );
        }
        let carrier = &d.class.args[0];
        self.check_binders(d)?;
        // Most carriers own an ordinary namespace (`Le::Decide`). Equality is
        // the one headless former whose instances have a better owner: the
        // endpoints' inferred type. The registry therefore distinguishes Nat
        // equality from Bool equality by the same resolved declaration keys
        // every other carrier uses, while the full instance type remains what
        // candidate trial checks against a goal.
        let (head, head_key, headless_suffix) = if matches!(carrier.kind, TyKind::Eq(..)) {
            let cx = self.instance_head_cx(d)?;
            let (lowered, _) = self.elab_ty(&cx, carrier)?;
            let crate::Type::Id { ty, .. } = lowered else {
                unreachable!("a lowered equality carrier is an identity type")
            };
            let Some(owner) = self.carrier_of_ty(&cx, &ty, carrier.span) else {
                return err(
                    format!(
                        "the equality carrier `{}` has endpoints at a type with no \
                         nominal owner, so its instance cannot be registered: equality \
                         instances are keyed by the endpoints' type (for example `Nat` \
                         in `n = m`), which keeps equality at different types distinct",
                        render_ty(carrier)
                    ),
                    carrier.span,
                );
            };
            // `Decide<Nat>` and `Decide<n = m>` must not share a key. `#`
            // cannot begin a source name, so this is a structural registry
            // component rather than a spelling that could resolve elsewhere.
            let equality_key = format!("#Eq@{}", owner.key);
            (owner.written, equality_key, "#Eq")
        } else if matches!(carrier.kind, TyKind::Fn { binder: None, implicit: false, .. }) {
            // Implication is the other headless former a class is for:
            // `Decide<P → Q>` decides a guard's side condition as written
            // (issues/decide-bit-is-the-comparison.md). An arrow has no
            // endpoint type to own it, so the class owns it: one structural
            // key per class, `Decide::Decide#Fn`, which `#` keeps unwritable.
            let owner = d.class.name.clone();
            let key = format!("#Fn@{}", class_key);
            (owner, key, "#Fn")
        } else {
            let Some(head) = head_name(carrier) else {
                return err(
                    format!(
                        "the carrier `{}` has no head type name, so this instance has no \
                         canonical name (docs/traits-layer1-design.md §4.1)",
                        render_ty(carrier)
                    ),
                    carrier.span,
                );
            };
            let head = head.to_string();
            if !self.names_a_carrier(&head) {
                return err(
                    format!(
                        "`{head}` is not a type or a type former in scope, so `{head}::{}` \
                         attaches to nothing",
                        d.class.name
                    ),
                    carrier.span,
                );
            }
            let key = self.carrier_key(&head);
            (head, key, "")
        };
        // The index (docs/operation-indexed-classes-design.md §3.1). Its
        // spelling joins the registry key, so it is computed from the
        // declaration alone and an unspellable one is refused here.
        if class.valparams.len() != d.class.index.len() {
            return err(
                format!(
                    "`{}` takes {} index argument(s), {} given: an instance names its \
                     index in the head (`instance {}<{}>({})`)",
                    class.name,
                    class.valparams.len(),
                    d.class.index.len(),
                    class.name,
                    render_ty(carrier),
                    class
                        .valparams
                        .iter()
                        .map(|p| p.name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                d.class.span,
            );
        }
        let index = self.index_spelling(&d.class, &class, d)?;
        let prefix = if index.is_empty() {
            format!("{head}::{}{headless_suffix}", class.name)
        } else {
            // Two instances of one class at one carrier are the point (§3), so
            // the canonical name carries the index. `#` never begins an
            // identifier, so the suffix is unwritable and `Bool::Monoid(or)`
            // — the `T::C(args)` spelling of §5.1 — is how it is reached.
            format!(
                "{head}::{}{headless_suffix}#{}",
                class.name,
                name_suffix(&index)
            )
        };
        // The carrier as the registry keys it: the *declaration* the head
        // names, not the head's spelling
        // (docs/instance-resolved-key-design.md §3). `head` itself stays the
        // written string, because it is what the canonical name is built from
        // and what a diagnostic should print.
        let key = instance_key(&class_key, &head_key, &index);
        if let Some(prev) = self.traits.instance(&key) {
            return err(
                format!(
                    "`{}` already has an instance of `{}`{} (`{}`), declared as `{}`: an \
                     instance is keyed on its class and its **resolved** carrier, so this \
                     is the same carrier declaration and not merely the same written name \
                     — refused rather than silently overwritten \
                     (docs/instance-resolved-key-design.md §3)",
                    head_key,
                    class_key,
                    if index.is_empty() {
                        String::new()
                    } else {
                        format!(" at the index `{index}`")
                    },
                    prev.global,
                    prev.written
                ),
                d.class.span,
            );
        }
        if let Some(prev) = self.traits.generic_index_overlap(&class_key, &head_key, &index) {
            return err(
                format!(
                    "`{}` already has an overlapping generic-index instance of `{}` \
                     (`{}`), declared as `{}`: a generic index matches every concrete \
                     index at this class and carrier, so the two instances would make \
                     resolution order-dependent",
                    head_key, class_key, prev.global, prev.written
                ),
                d.class.span,
            );
        }
        let parameterized =
            !d.tyvars.is_empty() || !d.requires.is_empty() || !d.valparams.is_empty();
        let written = class_ref_written(&d.class);
        // Termination, checked here rather than detected when it hangs
        // (docs/traits-layer2-design.md §6).
        self.check_decrease(d, &written)?;

        // The class type as a surface type: `Monoid<Rat>`, or `Monoid<Nat>(add)`
        // where the class is indexed.
        let class_ty = heather_syntax::class_ty(
            d.class.name.clone(),
            d.class.args.clone(),
            d.class.index.clone(),
            d.class.span,
        );

        // 1. Block members, in order, each a real global under the prefix.
        let mut member_names: Vec<String> = Vec::new();
        if let InstanceBody::Block(members) = &d.body {
            for m in members {
                if m.name.contains("::") {
                    return err(
                        format!(
                            "`{}` is a member of this instance's namespace and is written \
                             unqualified: the prefix `{prefix}` is the declaration's",
                            m.name
                        ),
                        m.span,
                    );
                }
                if class
                    .fields
                    .iter()
                    .all(|f| f.name.as_deref() != Some(m.name.as_str()))
                {
                    return err(
                        format!(
                            "`{}` is not a field of `{}`: an instance's members are its \
                             class's fields",
                            m.name, class.name
                        ),
                        m.span,
                    );
                }
                if member_names.iter().any(|n| n == &m.name) {
                    return err(format!("duplicate member `{}`", m.name), m.span);
                }
                // A `meta fn` is elaborator-held and never reaches Ψ, so it
                // cannot be a field's value; and an elaboration template's slot
                // is claimed program-wide, which an instance's namespace has no
                // business doing. Both are refused by name.
                if m.is_meta || m.elaborates.is_some() {
                    return err(
                        format!(
                            "`{}` cannot be a `meta fn`: an instance member is the value of \
                             a field, and a meta definition never reaches Ψ",
                            m.name
                        ),
                        m.span,
                    );
                }
                let full = format!("{prefix}::{}", m.name);
                let decl = Decl {
                    kind: m.kind,
                    is_meta: m.is_meta,
                    is_evidence: m.is_evidence,
                    value: m.value,
                    elaborates: m.elaborates.clone(),
                    name: full,
                    tyvars: d
                        .tyvars
                        .iter()
                        .cloned()
                        .chain(m.tyvars.iter().cloned())
                        .collect(),
                    params: instance_params(d)
                        .into_iter()
                        .chain(m.params.iter().cloned())
                        .collect(),
                    result: m.result.clone(),
                    decreases: m.decreases.clone(),
                    body: m.body.clone(),
                    span: m.span,
                };
                self.elab_decl_unowned(&decl)?;
                // Only *after* it lands does the name become visible to the
                // members after it (design §4.2): a member cannot reference
                // itself or a later one by short name.
                member_names.push(m.name.clone());
                self.instance_scope
                    .push((m.name.clone(), format!("{prefix}::{}", m.name)));
            }
        }
        // The scope is a block-local device and must not survive the block.
        // On the failure path the whole snapshot is restored, which clears it
        // too.
        let r = self.assemble_instance(d, &class, &head, &head_key, &prefix, &class_ty, &written);
        self.instance_scope.clear();
        r?;
        let global = qkey(self.names.module(), &prefix);
        let info = InstanceInfo { global, written, index, parameterized };
        self.semantic_commit_instance(key, info);
        Ok(())
    }

    /// Fields 2–4 of design §4.3, then the canonical parents (§4.4) and the
    /// override certificates (§4.5).
    #[allow(clippy::too_many_arguments)]
    fn assemble_instance(
        &mut self,
        d: &InstanceDecl,
        class: &ClassInfo,
        head: &str,
        head_key: &str,
        prefix: &str,
        class_ty: &Ty,
        written: &str,
    ) -> R<()> {
        let span = d.class.span;
        // A reference to one of this instance's members no longer applies the
        // `requires` binders: they are **solver parameters**
        // (docs/traits-layer2-design.md §1, §9.3), so the reference leaves
        // them to resolution, which finds them where they are — as locals of
        // this very declaration, the first ascending scope. Layer 1 passed
        // them by hand, and that is exactly the rule this round retires.

        // The instance's own type parameters, as type arguments. They are
        // written *explicitly* rather than left implicit because the reference
        // is a partial application — the member still wants its own arguments
        // — and mixing partial application with implicit insertion is refused
        // by the applicator (docs/unifier-completeness-design.md §5.3). Under
        // `f<A, B>` the leading type parameters are consumed by the
        // `param_offset` route and the remainder may be a prefix — which at
        // layer 2 is exactly the solver parameters, filled by resolution from
        // this declaration's own binders (docs/traits-layer2-design.md §9.3).
        let tyargs: Vec<Ty> = d
            .tyvars
            .iter()
            .map(|t| Ty {
                kind: TyKind::Named {
                    name: t.name.clone(),
                    args: vec![],
                },
                span,
            })
            .collect();
        let member_ref = |name: &str| -> Expr {
            let full = format!("{prefix}::{name}");
            if tyargs.is_empty() {
                var(&full, span)
            } else {
                span_expr(
                    ExprKind::TyApp {
                        head: Box::new(var(&full, span)),
                        args: tyargs.clone(),
                    },
                    span,
                )
            }
        };

        // What the body says about each field, by name.
        let mut written_fields: HashMap<String, Expr> = HashMap::new();
        match &d.body {
            InstanceBody::Block(members) => {
                for m in members {
                    written_fields.insert(m.name.clone(), member_ref(&m.name));
                }
            }
            InstanceBody::Literal(fields) => {
                for InstanceField {
                    name,
                    expr,
                    span: fspan,
                } in fields
                {
                    if class
                        .fields
                        .iter()
                        .all(|f| f.name.as_deref() != Some(name.as_str()))
                    {
                        return err(
                            format!("`{name}` is not a field of `{}`", class.name),
                            *fspan,
                        );
                    }
                    if written_fields.insert(name.clone(), expr.clone()).is_some() {
                        return err(format!("duplicate field `{name}`"), *fspan);
                    }
                }
            }
        }

        // An ancestor's arguments are written in terms of *the class's* type
        // parameters (design §3), so instantiating the class at `T⃗`
        // instantiates its ancestors by the same positional substitution. The
        // §3 restriction is what makes this a lookup rather than a walk.
        let anc_args = |a: &ClassRef| -> Vec<Ty> {
            a.args
                .iter()
                .map(|arg| match &arg.kind {
                    TyKind::Named { name, args } if args.is_empty() => class
                        .params
                        .iter()
                        .position(|p| p == name)
                        .map(|i| d.class.args[i].clone())
                        .unwrap_or_else(|| arg.clone()),
                    _ => arg.clone(),
                })
                .collect()
        };
        // The same substitution at the index: an ancestor's index arguments are
        // the child's own value-parameter names (`parent_view`'s restriction),
        // so instantiating is the positional lookup again.
        let anc_index = |a: &ClassRef| -> Vec<Expr> {
            a.index
                .iter()
                .map(|arg| match &arg.kind {
                    ExprKind::Var(name) => class
                        .valparams
                        .iter()
                        .position(|p| p.name == *name)
                        .and_then(|i| d.class.index.get(i).cloned())
                        .unwrap_or_else(|| arg.clone()),
                    _ => arg.clone(),
                })
                .collect()
        };
        let anc_ref = |a: &ClassRef| -> ClassRef {
            ClassRef {
                name: a.name.clone(),
                args: anc_args(a),
                index: anc_index(a),
                path: a.path.clone(),
                span,
            }
        };

        // Ancestors that already have a canonical instance at this carrier —
        // the fill-by-reference source (design §4.3 rule 3) and the agreement
        // partner (§4.5).
        let mut registered: Vec<(ClassRef, Rc<ClassInfo>, String)> = Vec::new();
        for a in &class.ancestors {
            let Some(akey) = self.key_of(&a.name) else {
                continue;
            };
            let Some(ainfo) = self.traits.class(&akey).cloned() else {
                continue;
            };
            let aindex = self.index_spelling(&anc_ref(a), &ainfo, d)?;
            let Some(inst) = self
                .traits
                .instance(&instance_key(&akey, head_key, &aindex))
            else {
                continue;
            };
            // A *parameterized* canonical parent (a generic instance, or one
            // with `requires` binders) offers neither fill-by-reference nor an
            // agreement partner at layer 1: its value is a function, and
            // deciding what to apply it to is resolution, which does not exist
            // yet. It is skipped rather than refused — the consequence is an
            // honest missing-field error if the child leaves the field out
            // (docs/traits-layer1-design.md §8).
            if inst.parameterized {
                continue;
            }
            let g = inst.global.clone();
            let Some(ainfo) = self.traits.class(&akey).cloned() else {
                continue;
            };
            registered.push((a.clone(), ainfo, g));
        }

        // 2. The field values, in declaration order.
        let mut lit_fields: Vec<RecordLitField> = Vec::new();
        let mut agreements: Vec<(String, Expr, Expr, String)> = Vec::new();
        let mut missing: Vec<String> = Vec::new();
        for f in &class.fields {
            let Some(fname) = f.name.clone() else {
                continue;
            };
            // A tagged parent field is filled with its complete canonical
            // dictionary. An untagged inherited field keeps the original
            // fill-by-projection behavior. Tagged ancestors never participate
            // in that latter search: their components live below the tag.
            let tagged_ref = self.class_ref_of_ty(&f.ty);
            let from_parent = tagged_ref
                .as_ref()
                .and_then(|field_ref| {
                    registered.iter().find(|(ancestor, _, _)| {
                        ancestor.path.len() == 1
                            && ancestor.path[0] == fname
                            && same_parent_fiber(field_ref, ancestor)
                    })
                })
                .map(|(ancestor, _, g)| (ancestor.name.clone(), var(g, span)))
                .or_else(|| {
                    registered
                        .iter()
                        .find(|(ancestor, info, _)| {
                            ancestor.path.is_empty()
                                && info.fields.iter().any(|g| {
                                    g.name.as_deref() == Some(fname.as_str())
                                })
                        })
                        .map(|(ancestor, _, g)| {
                            (
                                ancestor.name.clone(),
                                span_expr(
                                    ExprKind::Dot {
                                        recv: Box::new(var(g, span)),
                                        name: fname.clone(),
                                        tyargs: Vec::new(),
                                        args: None,
                                        named: Vec::new(),
                                    },
                                    span,
                                ),
                            )
                        })
                });
            match (written_fields.get(&fname), from_parent) {
                (Some(e), Some((aname, pe))) => {
                    // An override of a field a canonical value already holds
                    // owes agreement (design §4.5).
                    agreements.push((fname.clone(), e.clone(), pe, aname));
                    lit_fields.push(RecordLitField {
                        name: fname,
                        expr: e.clone(),
                        span,
                    });
                }
                (Some(e), None) => lit_fields.push(RecordLitField {
                    name: fname,
                    expr: e.clone(),
                    span,
                }),
                (None, Some((_, pe))) => lit_fields.push(RecordLitField {
                    name: fname,
                    expr: pe,
                    span,
                }),
                (None, None) => missing.push(fname),
            }
        }
        if !missing.is_empty() {
            return err(
                format!(
                    "`instance {written}` is missing {}: {}",
                    if missing.len() == 1 {
                        "a field"
                    } else {
                        "fields"
                    },
                    missing.join(", ")
                ),
                span,
            );
        }

        // 3. The value itself. At an **indexed** class the type arguments are
        // left off: a record literal with them written is an inference-position
        // spelling, and the index has to come from the expected type, which is
        // exactly what checking mode against `class_ty` supplies.
        let lit = span_expr(
            ExprKind::RecordLit {
                name: class.name.clone(),
                tyargs: if class.valparams.is_empty() && !class.is_kinded() {
                    d.class.args.clone()
                } else {
                    Vec::new()
                },
                fields: lit_fields.clone(),
            },
            span,
        );
        self.synth_decl(DeclKind::Fn, prefix, d, class_ty.clone(), lit, span)?;

        // 4. Override agreements — kernel-checked convertibility, as a real
        // certificate rather than a side-effect (design §4.5).
        for (fname, over, parent, aname) in agreements {
            let stmt = Ty {
                kind: TyKind::Eq(Box::new(over), Box::new(parent)),
                span,
            };
            let name = format!("{prefix}::{fname}#agrees");
            let proof = span_expr(ExprKind::Refl, span);
            self.synth_decl(DeclKind::Theorem, &name, d, stmt, proof, span)
                .map_err(|e| ElabError::Elab {
                    msg: format!(
                        "`instance {written}` overrides `{fname}`, which the canonical \
                         `{aname}` at `{head}` already holds, and the two are not \
                         convertible: an override owes agreement \
                         (docs/traits-layer1-design.md §4.5). The kernel said: {}",
                        e
                    ),
                    span,
                })?;
        }

        // 4b. Shared ancestors. A tagged parent may re-reach a proof-only
        // ancestor the class already holds (a setoid `Equivalence(≈)` inside
        // a tagged `MonoidRel(≈, *)` beside the flat one). One copy is
        // canonical (`elab_class`), so every other copy owes agreement with
        // it, field by field: two dictionaries for one fiber never register
        // side by side.
        let tag_ty = |r: &ClassRef| -> Ty {
            let r = anc_ref(r);
            heather_syntax::class_ty(r.name, r.args, r.index, span)
        };
        for (fname, (over, parent)) in self.shared_ancestor_agreements(&class, &lit_fields, &tag_ty, span) {
            let stmt = Ty {
                kind: TyKind::Eq(Box::new(over), Box::new(parent)),
                span,
            };
            let name = format!("{prefix}::{}#shared", fname.replace('.', "#"));
            let proof = span_expr(ExprKind::Refl, span);
            self.synth_decl(DeclKind::Theorem, &name, d, stmt, proof, span)
                .map_err(|e| ElabError::Elab {
                    msg: format!(
                        "`instance {written}`'s `{fname}` disagrees with the canonical \
                         copy of the same field: a tagged parent that re-reaches an \
                         ancestor the class already holds owes agreement with it, by \
                         conversion. The kernel said: {}",
                        e
                    ),
                    span,
                })?;
        }

        // 5. Canonical parents not yet registered — synthesized as this
        // instance's projections, sharing its very field expressions, so a
        // diamond collapses by construction (design §4.4).
        let parameterized =
            !d.tyvars.is_empty() || !d.requires.is_empty() || !d.valparams.is_empty();
        for a in class.ancestors.clone() {
            let Some(akey) = self.key_of(&a.name) else {
                return err(format!("`{}` is not a class in scope", a.name), span);
            };
            let Some(ainfo) = self.traits.class(&akey).cloned() else {
                continue;
            };
            let aref = anc_ref(&a);
            let aindex = self.index_spelling(&aref, &ainfo, d)?;
            if self
                .traits
                .has_instance(&instance_key(&akey, head_key, &aindex))
            {
                continue;
            }
            let aname = if aindex.is_empty() {
                format!("{head}::{}", ainfo.name)
            } else {
                format!("{head}::{}#{}", ainfo.name, name_suffix(&aindex))
            };
            let aargs = anc_args(&a);
            let aty =
                heather_syntax::class_ty(a.name.clone(), aargs.clone(), aref.index.clone(), span);
            // An untagged ancestor is rebuilt from the child's flattened field
            // expressions. A tagged ancestor is rebuilt from projections of
            // the dictionary at its path. Both routes preserve the exact
            // component expressions and therefore the existing canonical-parent
            // and diamond guarantees.
            let tagged_root = if let Some(root_name) = a.path.first() {
                let Some(root_value) = lit_fields.iter().find(|x| x.name == *root_name) else {
                    return err(
                        format!(
                            "internal: `{}` reaches `{}` through `{}`, but that tagged \
                             parent field is absent",
                            class.name,
                            ainfo.name,
                            a.path.join(".")
                        ),
                        span,
                    );
                };
                let Some(root_field) = class
                    .fields
                    .iter()
                    .find(|x| x.name.as_deref() == Some(root_name.as_str()))
                else {
                    return err("internal: tagged parent has no field declaration", span);
                };
                let Some(root_ref) = self.class_ref_of_ty(&root_field.ty) else {
                    return err("internal: tagged parent field is not a class", span);
                };
                let root_ref = anc_ref(&root_ref);
                let is_direct = same_parent_fiber(&root_ref, &aref);
                let root_ty = heather_syntax::class_ty(
                    root_ref.name,
                    root_ref.args,
                    root_ref.index,
                    span,
                );
                Some((root_value.expr.clone(), root_ty, is_direct))
            } else {
                None
            };
            let mut afields: Vec<RecordLitField> = Vec::new();
            for n in ainfo.fields.iter().filter_map(|g| g.name.clone()) {
                if a.path.is_empty() {
                    match lit_fields.iter().find(|x| x.name == n) {
                        Some(x) => afields.push(x.clone()),
                        None => {
                            return err(
                                format!(
                                    "internal: `{}` inherits `{n}` from `{}`, which the \
                                     flattened field list does not have",
                                    class.name, ainfo.name
                                ),
                                span,
                            );
                        }
                    }
                } else {
                    let mut source = var("__tagged_parent", span);
                    for component in a.path.iter().skip(1) {
                        source = span_expr(
                            ExprKind::Dot {
                                recv: Box::new(source),
                                name: component.clone(),
                                tyargs: Vec::new(),
                                args: None,
                                named: Vec::new(),
                            },
                            span,
                        );
                    }
                    afields.push(RecordLitField {
                        name: n.clone(),
                        expr: span_expr(
                            ExprKind::Dot {
                                recv: Box::new(source),
                                name: n,
                                tyargs: Vec::new(),
                                args: None,
                                named: Vec::new(),
                            },
                            span,
                        ),
                        span,
                    });
                }
            }
            let mut alit = span_expr(
                ExprKind::RecordLit {
                    name: ainfo.name.clone(),
                    tyargs: if ainfo.valparams.is_empty() && !ainfo.is_kinded() {
                        aargs.clone()
                    } else {
                        Vec::new()
                    },
                    fields: afields,
                },
                span,
            );
            if let Some((root_value, root_ty, is_direct)) = tagged_root {
                if is_direct {
                    // The tagged field already is the canonical parent. Do
                    // not eta-expand it: retaining the exact dictionary is
                    // both cheaper and the strongest proof-relevance story.
                    alit = root_value;
                } else {
                    alit = span_expr(
                        ExprKind::Block(Box::new(Block {
                            stmts: vec![Stmt::Let {
                                name: "__tagged_parent".into(),
                                ty: Some(root_ty),
                                expr: root_value,
                                span,
                                opaque: false,
                            }],
                            result: Box::new(alit),
                            ons: Vec::new(),
                            span,
                        })),
                        span,
                    );
                }
            }
            self.synth_decl(DeclKind::Fn, &aname, d, aty, alit, span)?;
            let global = qkey(self.names.module(), &aname);
            let key = instance_key(&akey, head_key, &aindex);
            let info = InstanceInfo {
                global,
                written: class_ref_written(&aref),
                index: aindex,
                parameterized,
            };
            self.semantic_commit_instance(key, info);
        }
        Ok(())
    }

    /// The agreements a class's shared ancestors owe at one instance. For
    /// every ancestor reached inside a tagged parent at a fiber the class
    /// keeps canonically at another path (untagged, or under an earlier tag),
    /// each of that ancestor's fields, as (`tag.….field`, (the copy under the
    /// tag, the canonical copy)). A copy under a tag is read through a `let`
    /// at the tag's class type at this instance (`tag_ty`), as the
    /// canonical-parent synthesis reads it.
    fn shared_ancestor_agreements(
        &self,
        class: &ClassInfo,
        lit_fields: &[RecordLitField],
        tag_ty: &dyn Fn(&ClassRef) -> Ty,
        span: Span,
    ) -> Vec<(String, (Expr, Expr))> {
        let dot = |recv: Expr, name: &str| {
            span_expr(
                ExprKind::Dot {
                    recv: Box::new(recv),
                    name: name.to_string(),
                    tyargs: Vec::new(),
                    args: None,
                    named: Vec::new(),
                },
                span,
            )
        };
        // Field `n` of the ancestor at `path`, out of this instance's fields.
        let read = |path: &[String], n: &str| -> Option<Expr> {
            let Some((root, inner)) = path.split_first() else {
                return lit_fields.iter().find(|x| x.name == n).map(|x| x.expr.clone());
            };
            let value = lit_fields.iter().find(|x| x.name == *root)?;
            let field = class.fields.iter().find(|x| x.name.as_deref() == Some(root.as_str()))?;
            let tref = self.class_ref_of_ty(&field.ty)?;
            let mut source = var("__tagged_parent", span);
            for component in inner {
                source = dot(source, component);
            }
            Some(span_expr(
                ExprKind::Block(Box::new(Block {
                    stmts: vec![Stmt::Let {
                        name: "__tagged_parent".into(),
                        ty: Some(tag_ty(&tref)),
                        expr: value.expr.clone(),
                        span,
                        opaque: false,
                    }],
                    result: Box::new(dot(source, n)),
                    ons: Vec::new(),
                    span,
                })),
                span,
            ))
        };
        let mut out: Vec<(String, (Expr, Expr))> = Vec::new();
        for f in &class.fields {
            let Some(tag) = f.name.clone() else { continue };
            if !class.ancestors.iter().any(|a| a.path.len() == 1 && a.path[0] == tag) {
                continue;
            }
            let Some(tref) = self.class_ref_of_ty(&f.ty) else { continue };
            let Some(tinfo) = self.lookup_class(&tref.name) else { continue };
            // The tag's class and its ancestors, spelled in this class's names.
            let mut rename = Ren::new();
            for (p, a) in tinfo.params.iter().zip(&tref.args) {
                if let TyKind::Named { name, args } = &a.kind
                    && args.is_empty()
                {
                    rename.insert(p.clone(), name.clone());
                }
            }
            for (p, a) in tinfo.valparams.iter().zip(&tref.index) {
                if let ExprKind::Var(n) = &a.kind {
                    rename.insert(p.name.clone(), n.clone());
                }
            }
            let own = ClassRef {
                name: tinfo.name.clone(),
                args: tinfo
                    .params
                    .iter()
                    .map(|p| Ty {
                        kind: TyKind::Named {
                            name: p.clone(),
                            args: vec![],
                        },
                        span,
                    })
                    .collect(),
                index: tinfo.valparams.iter().map(|p| var(&p.name, span)).collect(),
                path: Vec::new(),
                span,
            };
            for c in std::iter::once(&own).chain(tinfo.ancestors.iter()) {
                let mut path = vec![tag.clone()];
                path.extend(c.path.iter().cloned());
                let renamed = ClassRef {
                    name: c.name.clone(),
                    args: c.args.iter().map(|t| rename_ty(&rename, t)).collect(),
                    index: c.index.iter().map(|e| rename_expr(&rename, e)).collect(),
                    path,
                    span,
                };
                let Some(canon) = class.ancestors.iter().find(|o| same_parent_fiber(o, &renamed)) else {
                    continue;
                };
                if canon.path == renamed.path {
                    continue;
                }
                let Some(cinfo) = self.lookup_class(&c.name) else { continue };
                for n in cinfo.fields.iter().filter_map(|g| g.name.clone()) {
                    let label = renamed.path.iter().map(String::as_str)
                        .chain(std::iter::once(n.as_str()))
                        .collect::<Vec<_>>()
                        .join(".");
                    // `Equivalence` and its own `Reflexive` parent name one
                    // field; it owes one agreement.
                    if out.iter().any(|(l, _)| *l == label) {
                        continue;
                    }
                    let (Some(over), Some(canonical)) = (read(&renamed.path, &n), read(&canon.path, &n)) else {
                        continue;
                    };
                    out.push((label, (over, canonical)));
                }
            }
        }
        out
    }

    /// Every binder of an instance has to be **recoverable**: a binder the goal
    /// cannot determine is a metavariable nothing can ever solve
    /// (docs/value-generic-instances-design.md §4,
    /// issues/instance-binder-occurrence.md).
    ///
    /// Left unchecked, such an instance still *declares*, and the consequences
    /// are two. The visible one is a rejection at every use site instead of one
    /// at the declaration, far from the name to blame. The invisible one is
    /// worse: it is a registry entry no goal can use and every goal must still
    /// try, since selection walks every candidate of a class in sorted order
    /// (issues/resolution-candidate-fan-out.md) — a permanent per-goal cost with
    /// no possible payoff.
    ///
    /// **The rule is not uniform, and deliberately so.** The two binder kinds
    /// differ in *where a goal can determine them from*, and the check follows
    /// that rather than being tidy:
    ///
    /// - A **type parameter** may occur in the class arguments or in the
    ///   **index**. An index argument may be a global reference at this
    ///   instance's own type parameters, and the index is part of the class
    ///   type, so a goal determines it there —
    ///   `instance<A> Mag<Bool2>(pick<A>)` both declares and resolves.
    /// - A **value binder** counts the class arguments and index. A generic
    ///   index receives an alpha-stable registry component and is recovered by
    ///   the same candidate-head unification as a binder in the carrier.
    fn check_binders(&self, d: &InstanceDecl) -> R<()> {
        let head = class_ref_written(&d.class);
        // A binder absent from the head is usually one of three wishes, and the
        // message routes all three: two have a spelling that works and the third
        // is unavailable on purpose.
        let routes = |what: &str, name: &str| {
            format!(
                "the {what} `{name}` does not occur in the head `{head}`, so resolution \
                 has no way to determine it — a binder is recovered by unifying the head \
                 against the goal, and one the head does not mention would stay an \
                 unsolved metavariable at every use site, in an instance every search of \
                 this class would still have to try. If `{name}` was meant to select \
                 between structures at one carrier, that is a class **index** \
                 (`class C<A>(op)`), which joins the registry key so the alternatives \
                 coexist; if it was meant to be filled by hand, a `fn` is a value with no \
                 registry entry. Resolution choosing `{name}` for itself is the one \
                 reading that is unavailable, deliberately: search selects among \
                 candidates and never guesses an argument \
                 (issues/instance-binder-occurrence.md)"
            )
        };
        // A binder the written head does not name may still be in what the
        // resolver unifies: [`Self::binder_in_elaborated_head`].
        let determined_by_elaboration = |k: usize| self.binder_in_elaborated_head(d, k);
        // Type parameters: arguments or index, either determines.
        for (k, t) in d.tyvars.iter().enumerate() {
            if head_var_count(&d.class, &t.name) + index_var_count(&d.class, &t.name) == 0
                && !determined_by_elaboration(k)
            {
                return err(routes("type parameter", &t.name), d.class.span);
            }
        }
        for (i, p) in d.valparams.iter().enumerate() {
            if d.tyvars.iter().any(|t| t.name == p.name) {
                return err(
                    format!(
                        "`{}` is already a type parameter of this instance: one binder \
                         list cannot rebind the other's name",
                        p.name
                    ),
                    p.span,
                );
            }
            if d.valparams[..i].iter().any(|q| q.name == p.name) {
                return err(format!("duplicate value binder `{}`", p.name), p.span);
            }
            if head_var_count(&d.class, &p.name) + index_var_count(&d.class, &p.name) == 0
                && !determined_by_elaboration(d.tyvars.len() + i)
            {
                return err(routes("value binder", &p.name), p.span);
            }
        }
        Ok(())
    }

    /// Does binder `k` of the instance's telescope (type parameters, then
    /// value binders) occur in the **elaborated** class arguments? What the
    /// resolver unifies against a goal is the elaborated head, and
    /// elaboration writes binders the source does not: the endpoint type of
    /// an equation (`Decide<xs = ys>` at `xs: List<A>` carries `List<A>`) and
    /// a call's inserted implicits (`Decide<BitVec::unsigned_lt(a, b)>` at
    /// `a, b: BitVec(n)` is `unsigned_lt(n, a, b)`)
    /// (issues/instance-binder-occurrence-through-binder-types.md). Asked
    /// only after the written head's count came out zero, so a head that
    /// names its binders is never elaborated here. The index is not
    /// consulted: it joins the registry key as a spelling.
    fn binder_in_elaborated_head(&self, d: &InstanceDecl, k: usize) -> bool {
        let Ok(cx) = self.instance_head_cx(d) else {
            return false;
        };
        let m = (d.tyvars.len() + d.valparams.len()) as u32;
        d.class.args.iter().any(|a| {
            self.elab_ty(&cx, a)
                .is_ok_and(|(t, _)| crate::unification::mentions_binder(&t, m, m - 1 - k as u32))
        })
    }

    /// Structural decrease of the `requires` subgoals against the instance
    /// head (docs/traits-layer2-design.md §6, record §6.3): Paterson's
    /// condition, checked at the declaration over the *written* types.
    ///
    /// A `requires` binder whose type is not a class is not a subgoal at all —
    /// it is an `infer` goal, answered by the scope and never by backchaining
    /// — so it cannot feed a loop and is skipped.
    fn check_decrease(&self, d: &InstanceDecl, written: &str) -> R<()> {
        // Value binders are counted alongside type parameters: Paterson's
        // variable condition is about what a subgoal may *duplicate*, and a
        // value binder duplicates exactly as a type parameter does —
        // `instance(n: Nat) C<F(n)> requires D<G(n, n)>` grows the term it
        // searches at, whichever kind of binder `n` is.
        let vars: Vec<&str> = d
            .tyvars
            .iter()
            .map(|t| t.name.as_str())
            .chain(d.valparams.iter().map(|p| p.name.as_str()))
            .collect();
        let head: usize = d.class.args.iter().map(ty_size).sum();
        for p in &d.requires {
            // `instance<A: Mag> …` — the inline form's class is checked here,
            // the first place the instance head is known to be one.
            self.check_constraint_param(p)?;
            let TyKind::Named { name, args } = &p.ty.kind else {
                continue;
            };
            if args.is_empty() || self.lookup_class(name).is_none() {
                continue;
            }
            let sub: usize = args.iter().map(ty_size).sum();
            let refuse = |why: String| {
                err::<()>(
                    format!(
                        "`instance {written}` cannot be resolved for: the subgoal \
                         `{}: {}` {why}, so a search that used this instance could \
                         feed itself forever. Each `requires` subgoal must be \
                         structurally smaller than the instance head \
                         (docs/traits-layer2-design.md §6); the escape is a named \
                         instance value, applied by hand.",
                        p.name,
                        render_ty(&p.ty)
                    ),
                    p.span,
                )
            };
            // The variable condition first: where both fail it is the more
            // specific complaint, and it is the one a reader can act on.
            for (k, v) in vars.iter().enumerate() {
                let written: usize = d.class.args.iter().map(|a| ty_var_count(a, v)).sum();
                // A binder the written head reaches only through elaboration
                // counts once: a lower bound on its elaborated occurrences,
                // so this can only refuse more than the true count would.
                let in_head = if written == 0 && self.binder_in_elaborated_head(d, k) {
                    1
                } else {
                    written
                };
                if ty_var_count(&p.ty, v) > in_head {
                    refuse(format!("mentions `{v}` more often than the head does"))?;
                }
            }
            if sub >= head {
                refuse(format!(
                    "is not smaller than the head `{}` ({sub} against {head})",
                    class_ref_written(&d.class)
                ))?;
            }
        }
        Ok(())
    }

    /// One synthesized declaration carrying the instance's own telescope.
    fn synth_decl(
        &mut self,
        kind: DeclKind,
        name: &str,
        d: &InstanceDecl,
        result: Ty,
        body: Expr,
        span: Span,
    ) -> R<()> {
        let decl = Decl {
            kind,
            is_meta: false,
            is_evidence: false,
            value: false,
            elaborates: None,
            name: name.to_string(),
            tyvars: d.tyvars.clone(),
            params: instance_params(d),
            result,
            decreases: None,
            body: body_of(body),
            span,
        };
        self.elab_decl_unowned(&decl)
    }
}
