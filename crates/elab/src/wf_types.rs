//! Representation roles at the recursive telescope boundary.
//!
//! Private fields and no Deref/From<Type> implementation keep a structural
//! Wf from silently becoming an emitted annotation. The raw kernel AST still
//! uses Type; crossing back to it is explicit at the emission/read sites.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, Term, Type};

use crate::{Cx, Elaborator};

/// A borrowed structural Wf, validated once before telescope construction.
#[derive(Clone, Copy)]
pub(crate) struct StructuralWf<'a>(&'a Type);

impl<'a> StructuralWf<'a> {
    pub(crate) fn new(ty: &'a Type) -> Option<Self> {
        matches!(ty, Type::Wf { .. }).then_some(Self(ty))
    }

    /// Explicit access for structural readers, not an annotation conversion.
    pub(crate) fn as_type(&self) -> &'a Type {
        self.0
    }

    pub(crate) fn shifted_structure(&self, depth: u32) -> Type {
        self.0.shift_local(depth)
    }

    /// The only constructor of an emitted type in this boundary: the shared
    /// annotation policy handles both registered names and its safe fallback.
    pub(crate) fn annotation(&self, el: &Elaborator, cx: &Cx) -> EmittedType {
        EmittedType(el.annotation_type(cx, self.0, 0))
    }

    /// The kernel remains the sole transcription of the telescope. This
    /// bridge requires the emitted representation for its element annotation;
    /// passing this structural wrapper (or a raw Type) there cannot compile.
    pub(crate) fn telescope(
        &self,
        gamma: &LocalCtx,
        motive_level: &Level,
        motive: &Rc<Type>,
        element: &EmittedType,
        slots: (&Rc<Type>, &Rc<Term>),
    ) -> (Type, Type, Type) {
        let Type::Wf { level, shape, arity } = self.0 else {
            unreachable!("StructuralWf is constructed only for a Wf")
        };
        heather_kernel::term::wf_step_telescope_at(
            gamma, level, motive_level, shape, arity, motive,
            element.as_type(), Some(slots),
        )
    }
}

/// An annotation selected by the emission policy. Shifting preserves its
/// role; there is no implicit escape to the unclassified kernel Type.
#[derive(Clone)]
pub(crate) struct EmittedType(Type);

impl EmittedType {
    pub(crate) fn shift_local(&self, depth: u32) -> Self {
        Self(self.0.shift_local(depth))
    }

    pub(crate) fn as_type(&self) -> &Type {
        &self.0
    }

    /// Explicit boundary to a kernel AST annotation slot.
    pub(crate) fn into_type(self) -> Type {
        self.0
    }
}
