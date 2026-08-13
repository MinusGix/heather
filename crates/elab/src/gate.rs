//! The kernel gate as an interceptable boundary
//! (`issues/parallel-checking-and-caching.md`, `docs/cache-v1-design.md` §1).
//!
//! Every finished declaration passes one `typing::check_type` +
//! `typing::check_term` pair before it is committed, at exactly three sites:
//! [`crate::Elaborator::elab_decl_inner`] (user `fn`/`theorem`),
//! `gendefs::push_gen_def` (the generated definitions) — both of which push
//! the checked binding to Ψ — and `quote.rs`'s `elab_meta_decl_inner` (a
//! `meta fn`, checked at `Layer::Meta` and registered in the meta-def table
//! rather than pushed; `lands_in_psi` is how an oracle tells the two apart).
//! This module is the seam that lets something outside the elaborator watch
//! those sites and, if it can vouch for the declaration, say so.
//!
//! It is deliberately the smallest surface that can carry a content-addressed
//! cache: one trait, one item struct, one setter. The elaborator holds no
//! cache, knows no hash function, and does no IO — an installed gate is an
//! opaque oracle, and with none installed nothing about elaboration changes.
//!
//! **The gate is trusted.** `admits` returning `true` means the kernel does
//! not run on that declaration and it is pushed to Ψ regardless. Whoever
//! installs one owns the trust argument (`docs/cache-v1-design.md` §6).

use std::rc::Rc;

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
            body: if self.opaque { None } else { Some(Rc::new(self.body.clone())) },
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
    fn accepted(&self, psi: &GlobalCtx, item: &GateItem<'_>);
}

/// A gate that never admits anything: the identity, useful as a control.
pub struct NoGate;

impl KernelGate for NoGate {
    fn admits(&self, _psi: &GlobalCtx, _item: &GateItem<'_>) -> bool {
        false
    }
    fn accepted(&self, _psi: &GlobalCtx, _item: &GateItem<'_>) {}
}
