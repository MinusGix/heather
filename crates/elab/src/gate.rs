//! The kernel gate as an interceptable boundary
//! (`issues/parallel-checking-and-caching.md`, `docs/cache-v1-design.md` §1).
//!
//! Every finished definition or theorem passes one `typing::check_type` +
//! `typing::check_term` pair before it is committed, at exactly three sites:
//! [`crate::Elaborator::elab_decl_inner`] (user `fn`/`theorem`),
//! `gendefs::push_gen_def` (the generated definitions) — both of which push
//! the checked binding to Ψ — and `quote.rs`'s `elab_meta_decl_inner` (a
//! `meta fn`, checked at `Layer::Meta` and registered in the meta-def table
//! rather than pushed; `lands_in_psi` is how an oracle tells the two apart).
//! This module is the seam that lets something outside the elaborator watch
//! those sites and, if it can vouch for the declaration, say so. Explicit
//! axioms have no term gate; [`KernelGate::assumption`] announces their
//! separately checked statement so caches retain the trust distinction.
//!
//! It is deliberately the smallest surface that can carry a content-addressed
//! cache: one trait, one item struct, one setter. The elaborator holds no
//! cache, knows no hash function, and does no IO — an installed gate is an
//! opaque oracle, and with none installed nothing about elaboration changes.
//!
//! **The gate is trusted.** `admits` returning `true` means the kernel does
//! not run on that declaration and it is pushed to Ψ regardless. Whoever
//! installs one owns the trust argument (`docs/cache-v1-design.md` §6).

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};

/// The declaration about to face the kernel gate: exactly the arguments the
/// two `typing::check_*` calls get, plus the two facts a cache needs that the
/// kernel does not (what it is called, and whether it will be pushed opaque).
pub struct GateItem<'a> {
    /// For diagnostics and for the cache file's human-readable column only.
    /// Identity is the content hash; the name is metadata (Unison's rule).
    pub name: &'a str,
    pub ctx: &'a LocalCtx,
    /// The statement, checked at `Layer::Prog`.
    pub ty: &'a Type,
    pub level: &'a Level,
    /// The proof/body, checked at `Layer::Code` against `ty`.
    pub body: &'a Term,
    /// True for a `theorem`: it is pushed with `body: None`, so its body is
    /// invisible to every dependent. This is the interface split of
    /// `issues/parallel-checking-and-caching.md`, and the elaborator is the
    /// only place that knows it before the binding is built.
    pub opaque: bool,
    /// The layer the body is checked at — `Layer::Code` at the two Ψ sites
    /// (statement at `Prog`), `Layer::Meta` for a `meta fn` (statement at
    /// `Meta` too; the pairing is a function of this field). Part of the
    /// item's identity: the same `(ty, body)` checked at two layers is two
    /// different kernel questions, and a cache key must never conflate them.
    pub layer: Layer,
    /// Whether the binding lands in Ψ when the gate passes. False for a
    /// `meta fn`, which registers in the meta-def table instead — an oracle
    /// tracking Ψ (the cache's prefix of interface hashes) must not expect
    /// this item to appear there.
    pub lands_in_psi: bool,
}

impl GateItem<'_> {
    /// The binding this item will become if it passes — the *interface*, in
    /// the sense the design uses: a theorem loses its proof here.
    pub fn binding(&self) -> heather_kernel::term::GlobalBinding {
        heather_kernel::term::GlobalBinding::Tm {
            ctx: self.ctx.clone(),
            layer: self.layer,
            ty: Rc::new(self.ty.clone()),
            level: self.level.clone(),
            body: if self.opaque {
                None
            } else {
                Some(Rc::new(self.body.clone()))
            },
        }
    }
}

/// An oracle consulted at the kernel gate.
///
/// Both methods take `&self`: a gate is shared (`Rc`) and outlives any one
/// elaborator, so mutable state belongs behind a `Cell`/`RefCell` of its own.
pub trait KernelGate {
    /// May the kernel gate be skipped for `item`, against the global context
    /// `psi` it would be checked in? `false` is always safe.
    fn admits(&self, psi: &GlobalCtx, item: &GateItem<'_>) -> bool;

    /// `item` just passed the real kernel gate in `psi`. Called only after a
    /// `false` from [`Self::admits`] — never after a hit, so a gate cannot
    /// mistake its own vouching for evidence.
    ///
    /// `unsealed` lists, by absolute Ψ index, the sealed theorem proofs the
    /// check opened (`heather_kernel::unseal`;
    /// `issues/theorem-witness-unfolding.md`). A verdict with any is a
    /// verdict about those proofs' bodies as well as about `item`, and a
    /// theorem's interface leaves its proof out: whatever the oracle keys a
    /// verdict on must account for them, or not keep the verdict.
    fn accepted(&self, psi: &GlobalCtx, item: &GateItem<'_>, unsealed: &[usize]);

    /// An explicit axiom's statement passed `check_type` and is about to land
    /// as an opaque binding. A cache observes this separately so an axiom and
    /// a proved theorem with the same statement never share an interface
    /// identity. This is notification only: axioms have no proof gate to skip.
    fn assumption(
        &self,
        _psi: &GlobalCtx,
        _name: &str,
        _binding: &heather_kernel::term::GlobalBinding,
    ) {
    }

    /// Every question `admits` opened at a Ψ length ≥ `psi.bindings.len()`
    /// is dead: the declaration it was asked about was refused (or the pass
    /// carrying it discarded), so nothing will land there and no `accepted`
    /// will follow. Called on every declaration failure. A gate that
    /// remembers an open question by its Ψ position — the cache does, so
    /// that `accepted` never re-hashes what `admits` hashed — must forget
    /// it here, or the next declaration at that position could inherit it.
    fn abandon(&self, _psi: &GlobalCtx) {}

    /// May the statement check of `binding`, a declaration without a body
    /// (a theorem's statement, an opaque declaration) about to land at
    /// `psi.bindings.len()`, be skipped? Asked only by module-image replay,
    /// which otherwise re-checks every such statement on every load: a
    /// verdict about the body's absence is all a definition's [`Self::admits`]
    /// already covers, and these bindings have no body to key one on
    /// (`issues/native-process-fixed-cost.md`). The default vouches for
    /// nothing.
    fn admits_statement(&self, _psi: &GlobalCtx, _binding: &heather_kernel::term::GlobalBinding) -> bool {
        false
    }

    /// `binding`'s statement just passed the kernel in `psi`, opening the
    /// sealed proofs `unsealed`. Called only after a `false` from
    /// [`Self::admits_statement`]; the same rule as [`Self::accepted`] holds
    /// for `unsealed`.
    fn statement_accepted(&self, _psi: &GlobalCtx, _binding: &heather_kernel::term::GlobalBinding, _unsealed: &[usize]) {}
}

/// A gate that never admits anything: the identity, useful as a control.
pub struct NoGate;

impl KernelGate for NoGate {
    fn admits(&self, _psi: &GlobalCtx, _item: &GateItem<'_>) -> bool {
        false
    }
    fn accepted(&self, _psi: &GlobalCtx, _item: &GateItem<'_>, _unsealed: &[usize]) {}
}

/// A gate that never admits the named declarations and never learns that
/// they passed: `heather check --only` wraps the verdict store in one so the
/// probed items face the kernel on every run and the store is left exactly
/// as it was found (`docs/check-only-design.md` §2). Names are matched
/// bare — the gate sees `GateItem::name`, not the module — which is the
/// probe's own granularity.
pub struct Except {
    inner: Rc<dyn KernelGate>,
    names: std::collections::BTreeSet<String>,
}

impl Except {
    pub fn new(inner: Rc<dyn KernelGate>, names: std::collections::BTreeSet<String>) -> Except {
        Except { inner, names }
    }
}

impl KernelGate for Except {
    fn admits(&self, psi: &GlobalCtx, item: &GateItem<'_>) -> bool {
        !self.names.contains(item.name) && self.inner.admits(psi, item)
    }

    fn accepted(&self, psi: &GlobalCtx, item: &GateItem<'_>, unsealed: &[usize]) {
        if !self.names.contains(item.name) {
            self.inner.accepted(psi, item, unsealed);
        }
    }

    fn assumption(&self, psi: &GlobalCtx, name: &str, binding: &heather_kernel::term::GlobalBinding) {
        self.inner.assumption(psi, name, binding);
    }

    fn abandon(&self, psi: &GlobalCtx) {
        self.inner.abandon(psi);
    }

    // Statement verdicts are asked only by image replay, which never runs a
    // probed item (`--only` elaborates those), so there is no name to match.
    fn admits_statement(&self, psi: &GlobalCtx, binding: &heather_kernel::term::GlobalBinding) -> bool {
        self.inner.admits_statement(psi, binding)
    }

    fn statement_accepted(&self, psi: &GlobalCtx, binding: &heather_kernel::term::GlobalBinding, unsealed: &[usize]) {
        self.inner.statement_accepted(psi, binding, unsealed);
    }
}
