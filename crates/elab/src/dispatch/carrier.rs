//! Canonical carrier identity and carrier-owner queries.
//!
//! Dispatch policies consume a carrier as two deliberately distinct names:
//! the spelling diagnostics show and the declaration key registries compare.

use heather_kernel::term::{GlobalBinding, Term, Type};
use heather_syntax::Span;

use crate::inductive::Inductive;
use crate::{Cx, Elaborator};

/// A carrier the operator path read off a type: what a diagnostic prints, and
/// what a registry is keyed by.
///
/// The two are different strings and the distinction is the whole content of
/// `issues/designation-key-collides-across-modules.md`: `written` is `List`,
/// which is what the writer typed and what a message must quote; `key` is
/// `list::List`, the declaration, which is what the designation table is
/// keyed on so that two modules' `List`s are two carriers.
#[derive(Clone)]
pub(crate) struct Carrier {
    pub(crate) written: String,
    pub(crate) key: String,
}

impl Carrier {
    fn of_ind(ind: &Inductive) -> Self {
        Carrier {
            written: ind.name.clone(),
            key: crate::names::qkey(&ind.scope.module, &ind.name),
        }
    }

    /// A carrier the language declares itself — `Nat`. Written and key are the
    /// same string, and that is not a spelling escaping into a key: nothing
    /// can declare a second one (see [`Elaborator::carrier_key`]).
    fn constant(name: &str) -> Self {
        Carrier {
            written: name.to_string(),
            key: name.to_string(),
        }
    }
}

impl Elaborator {
    /// Does this name refer to a *type* here — a declared inductive/record, or
    /// a kernel type that has no declaration? Used only to check a member
    /// declaration's qualifier, so a false answer costs a rejection at the
    /// declaration and never a mis-resolution at a use.
    pub(crate) fn names_a_type(&self, name: &str) -> bool {
        // `True` for the same reason `Nat` is here: a kernel type (`Unit^0`)
        // claimed as a surface type name with no declaration behind it
        // (`inductive.rs`'s claim, issues/true-prop-trivial-hypotheses.md). A
        // file that declares its own `True` is answered by `lookup_inductive`
        // first, exactly as the claim itself is.
        self.lookup_inductive(name).is_some() || name == "Nat" || name == "Type" || name == "True"
    }

    /// Does this name refer to a **type former** — a global whose result, after
    /// every argument is supplied, is a universe? `Not : Π(P: Ty l). Ty l` and
    /// `Le : Π(n: Nat). Π(m: Nat). Ty 0` both answer yes.
    ///
    /// This is the *carrier-owner* half of an instance's canonical name
    /// (docs/traits-layer1-design.md §4.1, widened 2026-08-17). A carrier like
    /// `Le(n, m)` has a perfectly good head — `Le` — but `Le` names a `fn`
    /// rather than an inductive, so [`Self::names_a_type`] refused it and
    /// `Le::Decide` had nothing to attach to. The refusal was about the
    /// *namespace*, never about resolution: candidates are selected by trying
    /// each instance of the class against the goal (`resolve.rs`'s candidate
    /// loop), and the head never enters that search at all.
    ///
    /// Type formers and not merely *any* global, because the name has to keep
    /// meaning what it says: `Le::Decide` reads as "the `Decide` at `Le`", and
    /// that is only a sentence when `Le` is something a proposition can be *of*.
    /// A global returning `Nat` is not, and still refuses here.
    fn names_a_type_former(&self, name: &str) -> bool {
        let Some(info) = self.lookup_global(name) else {
            return false;
        };
        let GlobalBinding::Tm { ty, .. } = &self.psi.bindings[info.abs as usize] else {
            return false;
        };
        // Peel arguments to the result. `UPi` is peeled too: a level-polymorphic
        // former is still a former, and its body is where the universe is.
        let mut t: &Type = ty;
        loop {
            match t {
                Type::Pi { cod, .. } => t = cod,
                Type::UPi { body, .. } => t = body,
                _ => return matches!(t, Type::Ty(_)),
            }
        }
    }

    /// The owner rule for a canonical instance name: a type, or a type former.
    /// One place, so `instance` and `designation` cannot drift apart on what a
    /// carrier is allowed to be.
    pub(crate) fn names_a_carrier(&self, name: &str) -> bool {
        self.names_a_type(name) || self.names_a_type_former(name)
    }

    /// Does this name refer to a **function** — a global that keeps its body,
    /// which is what a `fn` is in Ψ and a `theorem` or `axiom` is not? The
    /// other owner of a member namespace (issues/function-owned-members.md):
    /// `theorem ten_pow::pos(i): 0 < ten_pow(i)` names a fact about `ten_pow`
    /// under it. A type former is a function too, so this widens
    /// [`Self::names_a_carrier`] for member declarations without moving the
    /// instance and designation owner rule, which stays the carrier one.
    pub(crate) fn names_a_function(&self, name: &str) -> bool {
        self.lookup_global(name).is_some_and(|info| {
            matches!(
                &self.psi.bindings[info.abs as usize],
                GlobalBinding::Tm { body: Some(_), .. }
            )
        })
    }

    /// The name of the declaration a lowered type belongs to — the type's own
    /// namespace, for a receiver-directed member lookup. `Nat` is a kernel
    /// type with no declaration and answers for itself; anything with no
    /// nominal tag has no namespace and answers `None`.
    pub(crate) fn type_namespace(&self, cx: &Cx, ty: &Type, span: Span) -> Option<String> {
        self.carrier_of_ty(cx, ty, span).map(|c| c.written)
    }

    /// [`Self::type_namespace`], plus the **key** the registries hold that
    /// declaration under (issues/designation-key-collides-across-modules.md).
    ///
    /// The key is read off the declaration itself — `qkey(ind.scope.module,
    /// ind.name)`, exactly the string `inductives` is keyed by — and
    /// deliberately *not* by resolving the written name at the use site:
    /// `carrier_key` is right for a name the writer spelled (it resolves where
    /// they wrote it), but a lowered operand's declaration is already known,
    /// and re-resolving its bare name in a file that imports two `List`s would
    /// answer "ambiguous" about a type there is nothing ambiguous about.
    ///
    /// `Nat` has no declaration and answers for itself, which agrees with
    /// [`Self::carrier_key`]'s fallback: the three names `names_a_type` claims
    /// with nothing behind them are the language's own, so a bare key for them
    /// is a constant rather than a spelling.
    pub(crate) fn carrier_of_ty(&self, cx: &Cx, ty: &Type, span: Span) -> Option<Carrier> {
        if matches!(ty, Type::Nat) {
            return Some(Carrier::constant("Nat"));
        }
        if let Some(ind) = self.tag_of(ty) {
            return Some(Carrier::of_ind(&ind));
        }
        // Same fallback as `record_of_at`: a receiver whose type arrived
        // through a `Val -> Type` value is `El` of a redex, and the structural
        // read is deliberately context-free.
        let head = self.whnf(cx, ty, span).ok()?;
        if matches!(head, Type::Nat) {
            return Some(Carrier::constant("Nat"));
        }
        self.tag_of(&head).map(|ind| Carrier::of_ind(&ind))
    }

    /// Is `ty` a type variable of the context, a section's carrier `K`: a
    /// type with no nominal carrier, whose operations are a dictionary's in
    /// scope (operator rung 2b, numerals at a class carrier).
    pub(crate) fn is_local_carrier(&self, cx: &Cx, ty: &Type, span: Span) -> bool {
        let is_var = |t: &Type| matches!(t, Type::El { tm, .. } if matches!(**tm, Term::Var(_)));
        // A nominal type is never one, and is the common case: no whnf.
        if is_var(ty) {
            return true;
        }
        if matches!(ty, Type::Nat) || self.tag_of(ty).is_some() {
            return false;
        }
        self.whnf(cx, ty, span).is_ok_and(|head| is_var(&head))
    }
}
