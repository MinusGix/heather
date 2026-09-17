//! Bounded, versioned wire format for semantic module images.
//!
//! This module deliberately owns a manual codec rather than deriving a
//! general-purpose deserializer for kernel or elaborator state. Every length
//! is checked before allocation, every recursive node consumes both a node
//! and depth budget, and decoded values remain inert until `ModuleDelta`'s
//! ordinary replay boundary validates and publishes them.

use std::fmt;
use std::collections::HashSet;
use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    Motives, SubstTail, Term, Type,
};
use heather_syntax::{
    Arm, Block, ClassRef, Decl, DeclKind, Expr, ExprKind, FieldDecl, LamBinder, MatchForm,
    NamedArg, OnStmt, OnTarget, OpFixity, Param, ParamOrigin, Pat, RecordLitField,
    RecordPatField, SlotPath, Solver, Span, Stmt, Ty, TyKind, TyParam,
};

use crate::application::{ParamMeta, Skel, SkelBinder};
use crate::datarepr::{CtorView, DatareprInfo, FieldView, ImplEntry, Obligation, Provenance};
use crate::gendefs::{GenDef, SpineCodes, TyCodeFn, WfSlots};
use crate::inductive::{Ctor, FieldKind, IdxPat, IdxTy, Inductive};
use crate::metaprograms::MetaDef;
use crate::module_delta::{DeltaEvent, ModuleDelta, ModuleDependencyIdentity};
use crate::names::{GlobalRegistration, ImportSpec, NameKind, Scope};
use crate::resolve::DerivedInst;
use crate::slots::Slot;
use crate::traits::{ClassInfo, DesignationInfo, InstanceInfo};

const MAGIC: &[u8; 8] = b"HTHMOD\0\x07";
const INTERFACE_MAGIC: &[u8; 8] = b"HTHIFC\0\x06";

/// Hard limits applied before any decoded collection or string allocation.
/// The loader may choose a smaller policy; these defaults are deliberately
/// generous enough for Heather's present standard library without making a
/// corrupt count an allocation request.
///
/// `max_nodes` bounds decoding *work*, not allocation (the sequence and
/// string limits do that), so it is sized loosely: the showcase's parser
/// module was 29 M nodes on 2026-09-17 against the earlier 16 M, and an image
/// past the budget is the worst of both worlds — decoded up to the budget,
/// refused, and rebuilt on every warm run. The writer now refuses to publish
/// past it (`heather_cache::module_image::ModuleCacheError::OverBudget`).
#[derive(Clone, Copy, Debug)]
pub struct ModuleImageLimits {
    pub max_bytes: usize,
    pub max_nodes: u64,
    pub max_sequence: usize,
    pub max_string_bytes: usize,
    pub max_depth: u32,
}

impl Default for ModuleImageLimits {
    fn default() -> Self {
        Self {
            max_bytes: 512 * 1024 * 1024,
            max_nodes: 256_000_000,
            max_sequence: 2_000_000,
            max_string_bytes: 16 * 1024 * 1024,
            max_depth: 2_048,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleImageDecodeError {
    TooLarge,
    Truncated,
    UnsupportedFormat,
    InvalidTag { sort: &'static str, tag: u8 },
    InvalidBool(u8),
    InvalidUtf8,
    SequenceTooLong,
    StringTooLong,
    NodeBudget,
    DepthBudget,
    TrailingBytes,
    DependencyPrefixLength { expected: usize, actual: usize },
    InvalidStructure(&'static str),
}

impl fmt::Display for ModuleImageDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge => write!(f, "module image exceeds the byte budget"),
            Self::Truncated => write!(f, "module image is truncated"),
            Self::UnsupportedFormat => write!(f, "unsupported module-image format"),
            Self::InvalidTag { sort, tag } => write!(f, "invalid {sort} tag {tag:#04x}"),
            Self::InvalidBool(value) => write!(f, "invalid boolean byte {value}"),
            Self::InvalidUtf8 => write!(f, "module image contains invalid UTF-8"),
            Self::SequenceTooLong => write!(f, "module-image sequence exceeds its budget"),
            Self::StringTooLong => write!(f, "module-image string exceeds its budget"),
            Self::NodeBudget => write!(f, "module image exceeds its syntax-node budget"),
            Self::DepthBudget => write!(f, "module image exceeds its nesting-depth budget"),
            Self::TrailingBytes => write!(f, "module image has trailing bytes"),
            Self::DependencyPrefixLength { expected, actual } => write!(
                f, "module image expects {expected} dependency bindings, but the accepted prefix has {actual}"
            ),
            Self::InvalidStructure(message) => write!(f, "invalid module-image structure: {message}"),
        }
    }
}

impl std::error::Error for ModuleImageDecodeError {}

struct Writer {
    bytes: Vec<u8>,
    interface: bool,
    /// Syntax nodes written, counted at exactly the sites the reader charges
    /// its node budget, so a writer knows before publication whether the
    /// reader would refuse the image (`ModuleImageLimits::max_nodes`).
    nodes: u64,
}

impl Default for Writer {
    fn default() -> Self {
        Self { bytes: Vec::new(), interface: false, nodes: 0 }
    }
}

impl Writer {
    fn byte(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn bool(&mut self, value: bool) {
        self.byte(u8::from(value));
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn len(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn string(&mut self, value: &str) {
        self.len(value.len());
        self.bytes.extend_from_slice(value.as_bytes());
    }

    fn option<T>(&mut self, value: Option<&T>, put: impl FnOnce(&mut Self, &T)) {
        match value {
            None => self.bool(false),
            Some(value) => {
                self.bool(true);
                put(self, value);
            }
        }
    }

    fn vec<T>(&mut self, values: &[T], mut put: impl FnMut(&mut Self, &T)) {
        self.len(values.len());
        for value in values {
            put(self, value);
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
    limits: ModuleImageLimits,
    nodes_left: u64,
    depth: u32,
    /// Added to every span read: a replayed declaration slice is decoded
    /// at the position its text now has in the edited source
    /// (`docs/declaration-slice-replay-design.md` §4). Zero for an image.
    span_offset: i64,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8], limits: ModuleImageLimits) -> Result<Self, ModuleImageDecodeError> {
        if bytes.len() > limits.max_bytes {
            return Err(ModuleImageDecodeError::TooLarge);
        }
        Ok(Self {
            bytes,
            at: 0,
            limits,
            nodes_left: limits.max_nodes,
            depth: 0,
            span_offset: 0,
        })
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], ModuleImageDecodeError> {
        let end = self.at.checked_add(count).ok_or(ModuleImageDecodeError::Truncated)?;
        let bytes = self
            .bytes
            .get(self.at..end)
            .ok_or(ModuleImageDecodeError::Truncated)?;
        self.at = end;
        Ok(bytes)
    }

    fn byte(&mut self) -> Result<u8, ModuleImageDecodeError> {
        Ok(self.take(1)?[0])
    }

    fn bool(&mut self) -> Result<bool, ModuleImageDecodeError> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            value => Err(ModuleImageDecodeError::InvalidBool(value)),
        }
    }

    fn u32(&mut self) -> Result<u32, ModuleImageDecodeError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, ModuleImageDecodeError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn usize(&mut self) -> Result<usize, ModuleImageDecodeError> {
        usize::try_from(self.u64()?).map_err(|_| ModuleImageDecodeError::SequenceTooLong)
    }

    fn len(&mut self) -> Result<usize, ModuleImageDecodeError> {
        let len = self.usize()?;
        if len > self.limits.max_sequence {
            return Err(ModuleImageDecodeError::SequenceTooLong);
        }
        Ok(len)
    }

    fn string(&mut self) -> Result<String, ModuleImageDecodeError> {
        let len = self.usize()?;
        if len > self.limits.max_string_bytes {
            return Err(ModuleImageDecodeError::StringTooLong);
        }
        let bytes = self.take(len)?;
        let value = std::str::from_utf8(bytes).map_err(|_| ModuleImageDecodeError::InvalidUtf8)?;
        Ok(value.to_string())
    }

    fn option<T>(
        &mut self,
        get: impl FnOnce(&mut Self) -> Result<T, ModuleImageDecodeError>,
    ) -> Result<Option<T>, ModuleImageDecodeError> {
        self.bool()?.then(|| get(self)).transpose()
    }

    fn vec<T>(
        &mut self,
        mut get: impl FnMut(&mut Self) -> Result<T, ModuleImageDecodeError>,
    ) -> Result<Vec<T>, ModuleImageDecodeError> {
        let len = self.len()?;
        // Every sequence element in this format has at least a one-byte tag
        // or scalar. Reject an impossible count before `with_capacity`, even
        // when a caller deliberately supplies maximally permissive limits.
        if len > self.bytes.len().saturating_sub(self.at) {
            return Err(ModuleImageDecodeError::Truncated);
        }
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(get(self)?);
        }
        Ok(values)
    }

    fn node<T>(
        &mut self,
        get: impl FnOnce(&mut Self) -> Result<T, ModuleImageDecodeError>,
    ) -> Result<T, ModuleImageDecodeError> {
        self.nodes_left = self
            .nodes_left
            .checked_sub(1)
            .ok_or(ModuleImageDecodeError::NodeBudget)?;
        if self.depth >= self.limits.max_depth {
            return Err(ModuleImageDecodeError::DepthBudget);
        }
        self.depth += 1;
        let result = get(self);
        self.depth -= 1;
        result
    }

    fn finish(self) -> Result<(), ModuleImageDecodeError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(ModuleImageDecodeError::TrailingBytes)
        }
    }
}

mod tag {
    pub const LEVEL_VAR: u8 = 0;
    pub const LEVEL_ZERO: u8 = 1;
    pub const LEVEL_SUCC: u8 = 2;
    pub const LEVEL_MAX: u8 = 3;
    pub const LEVEL_OMEGA: u8 = 4;

    pub const LAYER_VAR: u8 = 0;
    pub const LAYER_CODE: u8 = 1;
    pub const LAYER_PROG: u8 = 2;
    pub const LAYER_META: u8 = 3;

    pub const BASE_NIL: u8 = 0;
    pub const BASE_VAR: u8 = 1;
    pub const TAIL_EMPTY: u8 = 0;
    pub const TAIL_WK: u8 = 1;

    pub const BINDING_CTX: u8 = 0;
    pub const BINDING_TY: u8 = 1;
    pub const BINDING_TM: u8 = 2;
}

fn put_level(w: &mut Writer, level: &Level) {
    w.nodes += 1;
    match level {
        Level::Var(var) => {
            w.byte(tag::LEVEL_VAR);
            w.u32(var.0);
        }
        Level::Zero => w.byte(tag::LEVEL_ZERO),
        Level::Succ(level) => {
            w.byte(tag::LEVEL_SUCC);
            put_level(w, level);
        }
        Level::Max(left, right) => {
            w.byte(tag::LEVEL_MAX);
            put_level(w, left);
            put_level(w, right);
        }
        Level::Omega => w.byte(tag::LEVEL_OMEGA),
    }
}

fn get_level(r: &mut Reader<'_>) -> Result<Level, ModuleImageDecodeError> {
    r.node(|r| match r.byte()? {
        tag::LEVEL_VAR => Ok(Level::Var(UnivVar(r.u32()?))),
        tag::LEVEL_ZERO => Ok(Level::Zero),
        tag::LEVEL_SUCC => Ok(Level::Succ(Rc::new(get_level(r)?))),
        tag::LEVEL_MAX => Ok(Level::Max(Rc::new(get_level(r)?), Rc::new(get_level(r)?))),
        tag::LEVEL_OMEGA => Ok(Level::Omega),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "level", tag }),
    })
}

fn put_layer(w: &mut Writer, layer: Layer) {
    w.byte(match layer {
        Layer::Var => tag::LAYER_VAR,
        Layer::Code => tag::LAYER_CODE,
        Layer::Prog => tag::LAYER_PROG,
        Layer::Meta => tag::LAYER_META,
    });
}

fn get_layer(r: &mut Reader<'_>) -> Result<Layer, ModuleImageDecodeError> {
    match r.byte()? {
        tag::LAYER_VAR => Ok(Layer::Var),
        tag::LAYER_CODE => Ok(Layer::Code),
        tag::LAYER_PROG => Ok(Layer::Prog),
        tag::LAYER_META => Ok(Layer::Meta),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "layer", tag }),
    }
}

fn put_base(w: &mut Writer, base: CtxBase) {
    match base {
        CtxBase::Nil => w.byte(tag::BASE_NIL),
        CtxBase::Var(var) => {
            w.byte(tag::BASE_VAR);
            w.u32(var.0);
        }
    }
}

fn get_base(r: &mut Reader<'_>) -> Result<CtxBase, ModuleImageDecodeError> {
    match r.byte()? {
        tag::BASE_NIL => Ok(CtxBase::Nil),
        tag::BASE_VAR => Ok(CtxBase::Var(GlobalVar(r.u32()?))),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "context base", tag }),
    }
}

fn put_ctx(w: &mut Writer, ctx: &LocalCtx) {
    put_base(w, ctx.base);
    w.len(ctx.entries.len());
    for entry in ctx.entries.iter() {
        put_type(w, &entry.ty);
        put_level(w, &entry.level);
    }
}

fn get_ctx(r: &mut Reader<'_>) -> Result<LocalCtx, ModuleImageDecodeError> {
    let base = get_base(r)?;
    let entries = r.vec(|r| {
        Ok(CtxEntry {
            ty: Rc::new(get_type(r)?),
            level: get_level(r)?,
        })
    })?;
    Ok(LocalCtx::from_vec(base, entries))
}

fn put_subst(w: &mut Writer, subst: &LocalSubst) {
    match subst.tail {
        SubstTail::Empty { len, base } => {
            w.byte(tag::TAIL_EMPTY);
            w.u32(len);
            put_base(w, base);
        }
        SubstTail::Wk { len, ctx_var } => {
            w.byte(tag::TAIL_WK);
            w.u32(len);
            w.u32(ctx_var.0);
        }
    }
    w.vec(&subst.terms, |w, term| put_term(w, term));
}

fn get_subst(r: &mut Reader<'_>) -> Result<LocalSubst, ModuleImageDecodeError> {
    let tail = match r.byte()? {
        tag::TAIL_EMPTY => SubstTail::Empty {
            len: r.u32()?,
            base: get_base(r)?,
        },
        tag::TAIL_WK => SubstTail::Wk {
            len: r.u32()?,
            ctx_var: GlobalVar(r.u32()?),
        },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "substitution tail", tag }),
    };
    let terms = r.vec(|r| Ok(Rc::new(get_term(r)?)))?;
    Ok(LocalSubst { tail, terms })
}

// Kernel node codecs follow below. They use a tag namespace per sort: the
// caller always knows which sort it is decoding, so tags stay compact while
// every exhaustive match remains a compile-time schema tripwire.

fn put_type(w: &mut Writer, ty: &Type) {
    w.nodes += 1;
    match ty {
        Type::Nat => w.byte(0),
        Type::Pi { dom_level, cod_level, dom, cod } => {
            w.byte(1); put_level(w, dom_level); put_level(w, cod_level); put_type(w, dom); put_type(w, cod);
        }
        Type::Ty(level) => { w.byte(2); put_level(w, level); }
        Type::UPi { num_vars, level, body } => {
            w.byte(3); w.u32(*num_vars); put_level(w, level); put_type(w, body);
        }
        Type::El { level, tm } => { w.byte(4); put_level(w, level); put_term(w, tm); }
        Type::Id { level, ty, lhs, rhs } => {
            w.byte(5); put_level(w, level); put_type(w, ty); put_term(w, lhs); put_term(w, rhs);
        }
        Type::SEq { level, ty, lhs, rhs } => {
            w.byte(6); put_level(w, level); put_type(w, ty); put_term(w, lhs); put_term(w, rhs);
        }
        Type::SEmpty { level } => { w.byte(7); put_level(w, level); }
        Type::Squash { level, ty } => { w.byte(8); put_level(w, level); put_type(w, ty); }
        Type::Sigma { fst_level, snd_level, fst, snd } => {
            w.byte(9); put_level(w, fst_level); put_level(w, snd_level); put_type(w, fst); put_type(w, snd);
        }
        Type::Unit { level } => { w.byte(10); put_level(w, level); }
        Type::Empty { level } => { w.byte(11); put_level(w, level); }
        Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
            w.byte(12); put_level(w, lhs_level); put_level(w, rhs_level); put_type(w, lhs); put_type(w, rhs);
        }
        Type::W { shape_level, pos_level, shape, pos } => {
            w.byte(13); put_level(w, shape_level); put_level(w, pos_level); put_type(w, shape); put_type(w, pos);
        }
        Type::Vec { level, elem, len } => {
            w.byte(14); put_level(w, level); put_type(w, elem); put_term(w, len);
        }
        Type::Fin { len } => { w.byte(15); put_term(w, len); }
        Type::Wf { level, shape, arity } => {
            w.byte(16); put_level(w, level); put_type(w, shape); put_term(w, arity);
        }
        Type::GlobalTy { var, subst } => { w.byte(17); w.u32(var.0); put_subst(w, subst); }
        Type::CtxPi { level, body } => { w.byte(18); put_level(w, level); put_type(w, body); }
        Type::TyPi { ctx, arg_level, body_level, body } => {
            w.byte(19); put_ctx(w, ctx); put_level(w, arg_level); put_level(w, body_level); put_type(w, body);
        }
        Type::CodeTy { ctx, level } => { w.byte(20); put_ctx(w, ctx); put_level(w, level); }
        Type::CodeTm { ctx, ty, level } => {
            w.byte(21); put_ctx(w, ctx); put_type(w, ty); put_level(w, level);
        }
    }
}

fn get_type(r: &mut Reader<'_>) -> Result<Type, ModuleImageDecodeError> {
    r.node(|r| Ok(match r.byte()? {
        0 => Type::Nat,
        1 => Type::Pi { dom_level: get_level(r)?, cod_level: get_level(r)?, dom: Rc::new(get_type(r)?), cod: Rc::new(get_type(r)?) },
        2 => Type::Ty(get_level(r)?),
        3 => Type::UPi { num_vars: r.u32()?, level: get_level(r)?, body: Rc::new(get_type(r)?) },
        4 => Type::El { level: get_level(r)?, tm: Rc::new(get_term(r)?) },
        5 => Type::Id { level: get_level(r)?, ty: Rc::new(get_type(r)?), lhs: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?) },
        6 => Type::SEq { level: get_level(r)?, ty: Rc::new(get_type(r)?), lhs: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?) },
        7 => Type::SEmpty { level: get_level(r)? },
        8 => Type::Squash { level: get_level(r)?, ty: Rc::new(get_type(r)?) },
        9 => Type::Sigma { fst_level: get_level(r)?, snd_level: get_level(r)?, fst: Rc::new(get_type(r)?), snd: Rc::new(get_type(r)?) },
        10 => Type::Unit { level: get_level(r)? },
        11 => Type::Empty { level: get_level(r)? },
        12 => Type::Sum { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: Rc::new(get_type(r)?), rhs: Rc::new(get_type(r)?) },
        13 => Type::W { shape_level: get_level(r)?, pos_level: get_level(r)?, shape: Rc::new(get_type(r)?), pos: Rc::new(get_type(r)?) },
        14 => Type::Vec { level: get_level(r)?, elem: Rc::new(get_type(r)?), len: Rc::new(get_term(r)?) },
        15 => Type::Fin { len: Rc::new(get_term(r)?) },
        16 => Type::Wf { level: get_level(r)?, shape: Rc::new(get_type(r)?), arity: Rc::new(get_term(r)?) },
        17 => Type::GlobalTy { var: GlobalVar(r.u32()?), subst: get_subst(r)? },
        18 => Type::CtxPi { level: get_level(r)?, body: Rc::new(get_type(r)?) },
        19 => Type::TyPi { ctx: get_ctx(r)?, arg_level: get_level(r)?, body_level: get_level(r)?, body: Rc::new(get_type(r)?) },
        20 => Type::CodeTy { ctx: get_ctx(r)?, level: get_level(r)? },
        21 => Type::CodeTm { ctx: get_ctx(r)?, ty: Rc::new(get_type(r)?), level: get_level(r)? },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "type", tag }),
    }))
}

fn put_term(w: &mut Writer, term: &Term) {
    w.nodes += 1;
    match term {
        Term::Var(var) => { w.byte(0); w.u32(var.0); }
        Term::TmNat => w.byte(1),
        Term::TmPi { dom_level, cod_level, dom, cod } => {
            w.byte(2); put_level(w, dom_level); put_level(w, cod_level); put_term(w, dom); put_term(w, cod);
        }
        Term::TmTy(level) => { w.byte(3); put_level(w, level); }
        Term::TmId { level, ty, lhs, rhs } => {
            w.byte(4); put_level(w, level); put_term(w, ty); put_term(w, lhs); put_term(w, rhs);
        }
        Term::TmSEq { level, ty, lhs, rhs } => {
            w.byte(5); put_level(w, level); put_term(w, ty); put_term(w, lhs); put_term(w, rhs);
        }
        Term::TmSEmpty { level } => { w.byte(6); put_level(w, level); }
        Term::TmSquash { level, ty } => { w.byte(7); put_level(w, level); put_term(w, ty); }
        Term::TmSigma { fst_level, snd_level, fst, snd } => {
            w.byte(8); put_level(w, fst_level); put_level(w, snd_level); put_term(w, fst); put_term(w, snd);
        }
        Term::TmUnit { level } => { w.byte(9); put_level(w, level); }
        Term::TmEmpty { level } => { w.byte(10); put_level(w, level); }
        Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
            w.byte(11); put_level(w, lhs_level); put_level(w, rhs_level); put_term(w, lhs); put_term(w, rhs);
        }
        Term::TmW { shape_level, pos_level, shape, pos } => {
            w.byte(12); put_level(w, shape_level); put_level(w, pos_level); put_term(w, shape); put_term(w, pos);
        }
        Term::TmVec { level, elem, len } => {
            w.byte(13); put_level(w, level); put_term(w, elem); put_term(w, len);
        }
        Term::TmFin { len } => { w.byte(14); put_term(w, len); }
        Term::TmWf { level, shape, arity } => {
            w.byte(15); put_level(w, level); put_term(w, shape); put_term(w, arity);
        }
        Term::Zero => w.byte(16),
        Term::Succ(term) => { w.byte(17); put_term(w, term); }
        Term::ElimNat { level, motive, base, step, scrut } => {
            w.byte(18); put_level(w, level); put_type(w, motive); put_term(w, base); put_term(w, step); put_term(w, scrut);
        }
        Term::Refl { level, ty, tm } => {
            w.byte(19); put_level(w, level); put_type(w, ty); put_term(w, tm);
        }
        Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
            w.byte(20); put_level(w, ty_level); put_level(w, motive_level); put_type(w, ty); put_term(w, lhs); put_type(w, motive); put_term(w, case); put_term(w, rhs); put_term(w, proof);
        }
        Term::SRefl { level, ty, tm } => {
            w.byte(21); put_level(w, level); put_type(w, ty); put_term(w, tm);
        }
        Term::Squash { level, ty, tm } => {
            w.byte(22); put_level(w, level); put_type(w, ty); put_term(w, tm);
        }
        Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
            w.byte(23); put_level(w, ty_level); put_level(w, motive_level); put_type(w, ty); put_type(w, motive); put_term(w, lhs); put_term(w, rhs); put_term(w, proof); put_term(w, tm);
        }
        Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
            w.byte(24); put_level(w, level); put_level(w, scrut_level); put_type(w, motive); put_term(w, scrut);
        }
        Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
            w.byte(25); put_level(w, src_level); put_level(w, dst_level); put_type(w, src_ty); put_type(w, motive); put_term(w, case); put_term(w, scrut);
        }
        Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => {
            w.byte(26); put_level(w, fst_level); put_level(w, snd_level); put_type(w, fst_ty); put_type(w, snd_ty); put_term(w, fst); put_term(w, snd);
        }
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
            w.byte(27); put_level(w, fst_level); put_level(w, snd_level); put_type(w, fst_ty); put_type(w, snd_ty); put_term(w, pair);
        }
        Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
            w.byte(28); put_level(w, fst_level); put_level(w, snd_level); put_type(w, fst_ty); put_type(w, snd_ty); put_term(w, pair);
        }
        Term::Triv { level } => { w.byte(29); put_level(w, level); }
        Term::ElimEmpty { level, scrut_level, motive, scrut } => {
            w.byte(30); put_level(w, level); put_level(w, scrut_level); put_type(w, motive); put_term(w, scrut);
        }
        Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
            w.byte(31); put_level(w, lhs_level); put_level(w, rhs_level); put_type(w, lhs); put_type(w, rhs); put_term(w, val);
        }
        Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
            w.byte(32); put_level(w, lhs_level); put_level(w, rhs_level); put_type(w, lhs); put_type(w, rhs); put_term(w, val);
        }
        Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, scrut } => {
            w.byte(33); put_level(w, lhs_level); put_level(w, rhs_level); put_level(w, motive_level); put_type(w, lhs); put_type(w, rhs); put_type(w, motive); put_term(w, case_l); put_term(w, case_r); put_term(w, scrut);
        }
        Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
            w.byte(34); put_level(w, shape_level); put_level(w, pos_level); put_type(w, shape_ty); put_type(w, pos_ty); put_term(w, label); put_term(w, children);
        }
        Term::ElimW { shape_level, pos_level, motive_level, shape, pos, motive, step, scrut } => {
            w.byte(35); put_level(w, shape_level); put_level(w, pos_level); put_level(w, motive_level); put_type(w, shape); put_type(w, pos); put_type(w, motive); put_term(w, step); put_term(w, scrut);
        }
        Term::Supf { level, shape, arity, label, children } => {
            w.byte(36); put_level(w, level); put_type(w, shape); put_term(w, arity); put_term(w, label); put_term(w, children);
        }
        Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
            w.byte(37); put_level(w, level); put_level(w, motive_level); put_type(w, shape); put_term(w, arity); put_type(w, motive); put_term(w, step); put_term(w, scrut);
        }
        Term::Lam { dom_level, cod_level, dom, body } => {
            w.byte(38); put_level(w, dom_level); put_level(w, cod_level); put_type(w, dom); put_term(w, body);
        }
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
            w.byte(39); put_term(w, fun); put_level(w, dom_level); put_level(w, cod_level); put_type(w, dom); put_type(w, cod); put_term(w, arg);
        }
        Term::ULam { num_vars, level, body } => {
            w.byte(40); w.u32(*num_vars); put_level(w, level); put_term(w, body);
        }
        Term::UApp { fun, levels } => {
            w.byte(41); put_term(w, fun); w.vec(levels, put_level);
        }
        Term::GlobalTm { var, subst } => { w.byte(42); w.u32(var.0); put_subst(w, subst); }
        Term::CtxLam { level, body } => { w.byte(43); put_level(w, level); put_term(w, body); }
        Term::CtxApp { fun, ctx } => { w.byte(44); put_term(w, fun); put_ctx(w, ctx); }
        Term::TyLam { ctx, arg_level, body_level, body } => {
            w.byte(45); put_ctx(w, ctx); put_level(w, arg_level); put_level(w, body_level); put_term(w, body);
        }
        Term::TyApp { fun, arg } => { w.byte(46); put_term(w, fun); put_type(w, arg); }
        Term::BoxTy(ty) => { w.byte(47); put_type(w, ty); }
        Term::BoxTm(term) => { w.byte(48); put_term(w, term); }
        Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
            w.byte(49); put_level(w, motive_level); put_level(w, code_level); put_ctx(w, ctx); put_type(w, motive); put_term(w, body); put_term(w, scrut);
        }
        Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
            w.byte(50); put_level(w, motive_level); put_level(w, code_level); put_ctx(w, ctx); put_type(w, ty); put_type(w, motive); put_term(w, body); put_term(w, scrut);
        }
        Term::ElimCodeTy { ty_motive_level, tm_motive_level, motives, branches, code_level, ctx, scrut } => {
            w.byte(51); put_level(w, ty_motive_level); put_level(w, tm_motive_level); put_motives(w, motives); put_branches(w, branches); put_level(w, code_level); put_ctx(w, ctx); put_term(w, scrut);
        }
        Term::ElimCodeTm { ty_motive_level, tm_motive_level, motives, branches, code_level, ctx, ty, scrut } => {
            w.byte(52); put_level(w, ty_motive_level); put_level(w, tm_motive_level); put_motives(w, motives); put_branches(w, branches); put_level(w, code_level); put_ctx(w, ctx); put_type(w, ty); put_term(w, scrut);
        }
        Term::NatLit(n) => { w.byte(53); w.u64(*n); }
    }
}

fn get_term(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    r.node(|r| Ok(match r.byte()? {
        0 => Term::Var(LocalVar(r.u32()?)),
        1 => Term::TmNat,
        2 => Term::TmPi { dom_level: get_level(r)?, cod_level: get_level(r)?, dom: Rc::new(get_term(r)?), cod: Rc::new(get_term(r)?) },
        3 => Term::TmTy(get_level(r)?),
        4 => Term::TmId { level: get_level(r)?, ty: Rc::new(get_term(r)?), lhs: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?) },
        5 => Term::TmSEq { level: get_level(r)?, ty: Rc::new(get_term(r)?), lhs: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?) },
        6 => Term::TmSEmpty { level: get_level(r)? },
        7 => Term::TmSquash { level: get_level(r)?, ty: Rc::new(get_term(r)?) },
        8 => Term::TmSigma { fst_level: get_level(r)?, snd_level: get_level(r)?, fst: Rc::new(get_term(r)?), snd: Rc::new(get_term(r)?) },
        9 => Term::TmUnit { level: get_level(r)? },
        10 => Term::TmEmpty { level: get_level(r)? },
        11 => Term::TmSum { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?) },
        12 => Term::TmW { shape_level: get_level(r)?, pos_level: get_level(r)?, shape: Rc::new(get_term(r)?), pos: Rc::new(get_term(r)?) },
        13 => Term::TmVec { level: get_level(r)?, elem: Rc::new(get_term(r)?), len: Rc::new(get_term(r)?) },
        14 => Term::TmFin { len: Rc::new(get_term(r)?) },
        15 => Term::TmWf { level: get_level(r)?, shape: Rc::new(get_term(r)?), arity: Rc::new(get_term(r)?) },
        16 => Term::Zero,
        17 => Term::Succ(Rc::new(get_term(r)?)),
        18 => Term::ElimNat { level: get_level(r)?, motive: Rc::new(get_type(r)?), base: Rc::new(get_term(r)?), step: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        19 => Term::Refl { level: get_level(r)?, ty: Rc::new(get_type(r)?), tm: Rc::new(get_term(r)?) },
        20 => Term::J { ty_level: get_level(r)?, motive_level: get_level(r)?, ty: Rc::new(get_type(r)?), lhs: Rc::new(get_term(r)?), motive: Rc::new(get_type(r)?), case: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?), proof: Rc::new(get_term(r)?) },
        21 => Term::SRefl { level: get_level(r)?, ty: Rc::new(get_type(r)?), tm: Rc::new(get_term(r)?) },
        22 => Term::Squash { level: get_level(r)?, ty: Rc::new(get_type(r)?), tm: Rc::new(get_term(r)?) },
        23 => Term::Transp { ty_level: get_level(r)?, motive_level: get_level(r)?, ty: Rc::new(get_type(r)?), motive: Rc::new(get_type(r)?), lhs: Rc::new(get_term(r)?), rhs: Rc::new(get_term(r)?), proof: Rc::new(get_term(r)?), tm: Rc::new(get_term(r)?) },
        24 => Term::ElimSEmpty { level: get_level(r)?, scrut_level: get_level(r)?, motive: Rc::new(get_type(r)?), scrut: Rc::new(get_term(r)?) },
        25 => Term::ElimSquash { src_level: get_level(r)?, dst_level: get_level(r)?, src_ty: Rc::new(get_type(r)?), motive: Rc::new(get_type(r)?), case: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        26 => Term::Pair { fst_level: get_level(r)?, snd_level: get_level(r)?, fst_ty: Rc::new(get_type(r)?), snd_ty: Rc::new(get_type(r)?), fst: Rc::new(get_term(r)?), snd: Rc::new(get_term(r)?) },
        27 => Term::Fst { fst_level: get_level(r)?, snd_level: get_level(r)?, fst_ty: Rc::new(get_type(r)?), snd_ty: Rc::new(get_type(r)?), pair: Rc::new(get_term(r)?) },
        28 => Term::Snd { fst_level: get_level(r)?, snd_level: get_level(r)?, fst_ty: Rc::new(get_type(r)?), snd_ty: Rc::new(get_type(r)?), pair: Rc::new(get_term(r)?) },
        29 => Term::Triv { level: get_level(r)? },
        30 => Term::ElimEmpty { level: get_level(r)?, scrut_level: get_level(r)?, motive: Rc::new(get_type(r)?), scrut: Rc::new(get_term(r)?) },
        31 => Term::Inl { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: Rc::new(get_type(r)?), rhs: Rc::new(get_type(r)?), val: Rc::new(get_term(r)?) },
        32 => Term::Inr { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: Rc::new(get_type(r)?), rhs: Rc::new(get_type(r)?), val: Rc::new(get_term(r)?) },
        33 => Term::Case { lhs_level: get_level(r)?, rhs_level: get_level(r)?, motive_level: get_level(r)?, lhs: Rc::new(get_type(r)?), rhs: Rc::new(get_type(r)?), motive: Rc::new(get_type(r)?), case_l: Rc::new(get_term(r)?), case_r: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        34 => Term::Sup { shape_level: get_level(r)?, pos_level: get_level(r)?, shape_ty: Rc::new(get_type(r)?), pos_ty: Rc::new(get_type(r)?), label: Rc::new(get_term(r)?), children: Rc::new(get_term(r)?) },
        35 => Term::ElimW { shape_level: get_level(r)?, pos_level: get_level(r)?, motive_level: get_level(r)?, shape: Rc::new(get_type(r)?), pos: Rc::new(get_type(r)?), motive: Rc::new(get_type(r)?), step: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        36 => Term::Supf { level: get_level(r)?, shape: Rc::new(get_type(r)?), arity: Rc::new(get_term(r)?), label: Rc::new(get_term(r)?), children: Rc::new(get_term(r)?) },
        37 => Term::ElimWf { level: get_level(r)?, motive_level: get_level(r)?, shape: Rc::new(get_type(r)?), arity: Rc::new(get_term(r)?), motive: Rc::new(get_type(r)?), step: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        38 => Term::Lam { dom_level: get_level(r)?, cod_level: get_level(r)?, dom: Rc::new(get_type(r)?), body: Rc::new(get_term(r)?) },
        39 => Term::App { fun: Rc::new(get_term(r)?), dom_level: get_level(r)?, cod_level: get_level(r)?, dom: Rc::new(get_type(r)?), cod: Rc::new(get_type(r)?), arg: Rc::new(get_term(r)?) },
        40 => Term::ULam { num_vars: r.u32()?, level: get_level(r)?, body: Rc::new(get_term(r)?) },
        41 => Term::UApp { fun: Rc::new(get_term(r)?), levels: r.vec(get_level)? },
        42 => Term::GlobalTm { var: GlobalVar(r.u32()?), subst: get_subst(r)? },
        43 => Term::CtxLam { level: get_level(r)?, body: Rc::new(get_term(r)?) },
        44 => Term::CtxApp { fun: Rc::new(get_term(r)?), ctx: get_ctx(r)? },
        45 => Term::TyLam { ctx: get_ctx(r)?, arg_level: get_level(r)?, body_level: get_level(r)?, body: Rc::new(get_term(r)?) },
        46 => Term::TyApp { fun: Rc::new(get_term(r)?), arg: Rc::new(get_type(r)?) },
        47 => Term::BoxTy(Rc::new(get_type(r)?)),
        48 => Term::BoxTm(Rc::new(get_term(r)?)),
        49 => Term::LetBoxTy { motive_level: get_level(r)?, code_level: get_level(r)?, ctx: get_ctx(r)?, motive: Rc::new(get_type(r)?), body: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        50 => Term::LetBoxTm { motive_level: get_level(r)?, code_level: get_level(r)?, ctx: get_ctx(r)?, ty: Rc::new(get_type(r)?), motive: Rc::new(get_type(r)?), body: Rc::new(get_term(r)?), scrut: Rc::new(get_term(r)?) },
        51 => Term::ElimCodeTy { ty_motive_level: get_level(r)?, tm_motive_level: get_level(r)?, motives: Rc::new(get_motives(r)?), branches: Rc::new(get_branches(r)?), code_level: get_level(r)?, ctx: get_ctx(r)?, scrut: Rc::new(get_term(r)?) },
        52 => Term::ElimCodeTm { ty_motive_level: get_level(r)?, tm_motive_level: get_level(r)?, motives: Rc::new(get_motives(r)?), branches: Rc::new(get_branches(r)?), code_level: get_level(r)?, ctx: get_ctx(r)?, ty: Rc::new(get_type(r)?), scrut: Rc::new(get_term(r)?) },
        53 => Term::NatLit(r.u64()?),
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "term", tag }),
    }))
}

fn put_motives(w: &mut Writer, motives: &Motives) {
    put_type(w, &motives.ty_motive);
    put_type(w, &motives.tm_motive);
}

fn get_motives(r: &mut Reader<'_>) -> Result<Motives, ModuleImageDecodeError> {
    Ok(Motives {
        ty_motive: Rc::new(get_type(r)?),
        tm_motive: Rc::new(get_type(r)?),
    })
}

fn branch_terms(branches: &Branches) -> [&Rc<Term>; 56] {
    let Branches {
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl, tm_transp,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
    } = branches;
    [
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl, tm_transp,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
    ]
}

fn put_branches(w: &mut Writer, branches: &Branches) {
    for term in branch_terms(branches) {
        put_term(w, term);
    }
}

fn get_branches(r: &mut Reader<'_>) -> Result<Branches, ModuleImageDecodeError> {
    let mut terms = Vec::with_capacity(56);
    for _ in 0..56 {
        terms.push(Rc::new(get_term(r)?));
    }
    let [
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl, tm_transp,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
    ]: [Rc<Term>; 56] = terms.try_into().unwrap();
    Ok(Branches {
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl, tm_transp,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
    })
}

fn put_binding(w: &mut Writer, binding: &GlobalBinding) {
    w.nodes += 1;
    match binding {
        GlobalBinding::Ctx => w.byte(tag::BINDING_CTX),
        GlobalBinding::Ty { ctx, layer, level } => {
            w.byte(tag::BINDING_TY); put_ctx(w, ctx); put_layer(w, *layer); put_level(w, level);
        }
        GlobalBinding::Tm { ctx, layer, ty, level, body } => {
            w.byte(tag::BINDING_TM); put_ctx(w, ctx); put_layer(w, *layer); put_type(w, ty); put_level(w, level);
            w.option(body.as_deref(), put_term);
        }
    }
}

fn get_binding(r: &mut Reader<'_>) -> Result<GlobalBinding, ModuleImageDecodeError> {
    r.node(|r| Ok(match r.byte()? {
        tag::BINDING_CTX => GlobalBinding::Ctx,
        tag::BINDING_TY => GlobalBinding::Ty {
            ctx: get_ctx(r)?, layer: get_layer(r)?, level: get_level(r)?,
        },
        tag::BINDING_TM => GlobalBinding::Tm {
            ctx: get_ctx(r)?,
            layer: get_layer(r)?,
            ty: Rc::new(get_type(r)?),
            level: get_level(r)?,
            body: r.option(|r| Ok(Rc::new(get_term(r)?)))?,
        },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "global binding", tag }),
    }))
}

// Surface nodes are persisted because they are semantic metadata: named and
// implicit application, repr generation and diagnostics consult them after a
// module has been loaded. Spans are byte offsets, not source identities; they
// remain useful when the loader retains the matching source artifact.

fn put_span(w: &mut Writer, span: Span) {
    if w.interface {
        w.usize(0);
        w.usize(0);
    } else {
        w.usize(span.start);
        w.usize(span.end);
    }
}

fn get_span(r: &mut Reader<'_>) -> Result<Span, ModuleImageDecodeError> {
    let (start, end) = (r.usize()?, r.usize()?);
    if r.span_offset == 0 {
        return Ok(Span { start, end });
    }
    let shift = |at: usize| {
        usize::try_from(i64::try_from(at).ok()? + r.span_offset).ok()
    };
    match (shift(start), shift(end)) {
        (Some(start), Some(end)) => Ok(Span { start, end }),
        _ => Err(ModuleImageDecodeError::InvalidStructure("a relocated span leaves the source")),
    }
}

fn put_fixity(w: &mut Writer, fixity: OpFixity) {
    w.byte(match fixity { OpFixity::Prefix => 0, OpFixity::Infix => 1 });
}

fn get_fixity(r: &mut Reader<'_>) -> Result<OpFixity, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(OpFixity::Prefix),
        1 => Ok(OpFixity::Infix),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "operator fixity", tag }),
    }
}

fn put_ty(w: &mut Writer, ty: &Ty) {
    w.nodes += 1;
    put_span(w, ty.span);
    match &ty.kind {
        TyKind::Nat => w.byte(0),
        TyKind::Eq(lhs, rhs) => { w.byte(1); put_expr(w, lhs); put_expr(w, rhs); }
        TyKind::Univ { level } => { w.byte(2); w.u64(*level); }
        TyKind::OfExpr(expr) => { w.byte(3); put_expr(w, expr); }
        TyKind::Named { name, args } => { w.byte(4); w.string(name); w.vec(args, put_ty); }
        TyKind::Vec { elem, len } => { w.byte(5); put_ty(w, elem); put_expr(w, len); }
        TyKind::Fin(len) => { w.byte(6); put_expr(w, len); }
        TyKind::Squash(ty) => { w.byte(7); put_ty(w, ty); }
        TyKind::Fn { binder, implicit, dom, cod } => {
            w.byte(8); w.option(binder.as_ref(), |w, s| w.string(s)); w.bool(*implicit);
            put_ty(w, dom); put_ty(w, cod);
        }
        TyKind::Ctx => w.byte(9),
        TyKind::TyCode { ctx } => { w.byte(10); w.string(ctx); }
        TyKind::Code { ctx, ty } => { w.byte(11); w.string(ctx); put_ty(w, ty); }
        TyKind::Splice { name } => { w.byte(12); w.string(name); }
    }
}

fn get_ty(r: &mut Reader<'_>) -> Result<Ty, ModuleImageDecodeError> {
    r.node(|r| {
        let span = get_span(r)?;
        let kind = match r.byte()? {
            0 => TyKind::Nat,
            1 => TyKind::Eq(Box::new(get_expr(r)?), Box::new(get_expr(r)?)),
            2 => TyKind::Univ { level: r.u64()? },
            3 => TyKind::OfExpr(Box::new(get_expr(r)?)),
            4 => TyKind::Named { name: r.string()?, args: r.vec(get_ty)? },
            5 => TyKind::Vec { elem: Box::new(get_ty(r)?), len: Box::new(get_expr(r)?) },
            6 => TyKind::Fin(Box::new(get_expr(r)?)),
            7 => TyKind::Squash(Box::new(get_ty(r)?)),
            8 => TyKind::Fn {
                binder: r.option(Reader::string)?, implicit: r.bool()?,
                dom: Box::new(get_ty(r)?), cod: Box::new(get_ty(r)?),
            },
            9 => TyKind::Ctx,
            10 => TyKind::TyCode { ctx: r.string()? },
            11 => TyKind::Code { ctx: r.string()?, ty: Box::new(get_ty(r)?) },
            12 => TyKind::Splice { name: r.string()? },
            tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "surface type", tag }),
        };
        Ok(Ty { kind, span })
    })
}

fn put_pat(w: &mut Writer, pat: &Pat) {
    w.nodes += 1;
    match pat {
        Pat::Var { name, span } => { w.byte(0); w.string(name); put_span(w, *span); }
        Pat::Ctor { name, args, span } => {
            w.byte(1); w.string(name); w.vec(args, put_pat); put_span(w, *span);
        }
        Pat::Named { field, pat, span } => {
            w.byte(2); w.string(field); put_pat(w, pat); put_span(w, *span);
        }
    }
}

fn get_pat(r: &mut Reader<'_>) -> Result<Pat, ModuleImageDecodeError> {
    r.node(|r| match r.byte()? {
        0 => Ok(Pat::Var { name: r.string()?, span: get_span(r)? }),
        1 => Ok(Pat::Ctor { name: r.string()?, args: r.vec(get_pat)?, span: get_span(r)? }),
        2 => Ok(Pat::Named {
            field: r.string()?, pat: Box::new(get_pat(r)?), span: get_span(r)?,
        }),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "pattern", tag }),
    })
}

fn put_arm(w: &mut Writer, arm: &Arm) {
    w.string(&arm.ctor); w.bool(arm.default); w.vec(&arm.binders, put_pat);
    put_expr(w, &arm.body); put_span(w, arm.span);
}

fn get_arm(r: &mut Reader<'_>) -> Result<Arm, ModuleImageDecodeError> {
    Ok(Arm {
        ctor: r.string()?, default: r.bool()?, binders: r.vec(get_pat)?,
        body: get_expr(r)?, span: get_span(r)?,
    })
}

fn put_named_arg(w: &mut Writer, arg: &NamedArg) {
    w.string(&arg.name); put_span(w, arg.name_span); put_expr(w, &arg.expr); put_span(w, arg.span);
}

fn get_named_arg(r: &mut Reader<'_>) -> Result<NamedArg, ModuleImageDecodeError> {
    Ok(NamedArg {
        name: r.string()?, name_span: get_span(r)?, expr: get_expr(r)?, span: get_span(r)?,
    })
}

fn put_lam_binder(w: &mut Writer, binder: &LamBinder) {
    w.string(&binder.name); w.option(binder.ty.as_ref(), put_ty); w.bool(binder.implicit);
    put_span(w, binder.span);
}

fn get_lam_binder(r: &mut Reader<'_>) -> Result<LamBinder, ModuleImageDecodeError> {
    Ok(LamBinder {
        name: r.string()?, ty: r.option(get_ty)?, implicit: r.bool()?, span: get_span(r)?,
    })
}

fn put_match_form(w: &mut Writer, form: MatchForm) {
    w.byte(match form { MatchForm::Match => 0, MatchForm::Split => 1, MatchForm::If => 2, MatchForm::IfLet => 3 });
}

fn get_match_form(r: &mut Reader<'_>) -> Result<MatchForm, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(MatchForm::Match), 1 => Ok(MatchForm::Split),
        2 => Ok(MatchForm::If), 3 => Ok(MatchForm::IfLet),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "match form", tag }),
    }
}

fn put_expr(w: &mut Writer, expr: &Expr) {
    w.nodes += 1;
    put_span(w, expr.span);
    match &expr.kind {
        ExprKind::Var(name) => { w.byte(0); w.string(name); }
        ExprKind::OpSymbol { symbol, fixity } => { w.byte(1); w.string(symbol); put_fixity(w, *fixity); }
        ExprKind::Univ { level } => { w.byte(2); w.u64(*level); }
        ExprKind::Num(value) => { w.byte(3); w.u64(*value); }
        ExprKind::ArgSlot(slot) => { w.byte(4); w.option(slot.as_ref(), |w, n| w.u64(*n)); }
        ExprKind::App { head, args, named, explicit, goal_oriented } => {
            w.byte(5); put_expr(w, head); w.vec(args, put_expr); w.vec(named, put_named_arg);
            w.bool(*explicit); w.bool(*goal_oriented);
        }
        ExprKind::TyApp { head, args } => { w.byte(6); put_expr(w, head); w.vec(args, put_ty); }
        ExprKind::Lam { binders, body } => { w.byte(7); w.vec(binders, put_lam_binder); put_expr(w, body); }
        ExprKind::CollectionLit(values) => { w.byte(8); w.vec(values, put_expr); }
        ExprKind::Eq(lhs, rhs) => { w.byte(9); put_expr(w, lhs); put_expr(w, rhs); }
        ExprKind::TyLit(ty) => { w.byte(10); put_ty(w, ty); }
        ExprKind::Refl => w.byte(11),
        ExprKind::AutoRefl => w.byte(12),
        ExprKind::Hole(name) => { w.byte(13); w.option(name.as_ref(), |w, s| w.string(s)); }
        ExprKind::Match { form, generated, scrut, eqbind, motive, arms } => {
            w.byte(14); put_match_form(w, *form); w.bool(*generated); put_expr(w, scrut);
            w.option(eqbind.as_ref(), |w, s| w.string(s));
            w.option(motive.as_deref(), put_expr); w.vec(arms, put_arm);
        }
        ExprKind::MatchCode { scrut, motive, arms } => {
            w.byte(15); put_expr(w, scrut); put_ty(w, motive); w.vec(arms, put_arm);
        }
        ExprKind::Dot { recv, name, args, named } => {
            w.byte(16); put_expr(w, recv); w.string(name);
            w.option(args.as_ref(), |w, args| w.vec(args, put_expr)); w.vec(named, put_named_arg);
        }
        ExprKind::Index { recv, idx } => { w.byte(17); put_expr(w, recv); put_expr(w, idx); }
        ExprKind::RecordLit { name, tyargs, fields } => {
            w.byte(18); w.string(name); w.vec(tyargs, put_ty);
            w.vec(fields, |w, field| {
                w.string(&field.name); put_expr(w, &field.expr); put_span(w, field.span);
            });
        }
        ExprKind::Block(block) => { w.byte(19); put_block(w, block); }
        ExprKind::Quote(expr) => { w.byte(20); put_expr(w, expr); }
        ExprKind::Splice(expr) => { w.byte(21); put_expr(w, expr); }
        ExprKind::J { proof, motive, case } => {
            w.byte(22); put_expr(w, proof); put_expr(w, motive); put_expr(w, case);
        }
    }
}

fn get_expr(r: &mut Reader<'_>) -> Result<Expr, ModuleImageDecodeError> {
    r.node(|r| {
        let span = get_span(r)?;
        let kind = match r.byte()? {
            0 => ExprKind::Var(r.string()?),
            1 => ExprKind::OpSymbol { symbol: r.string()?, fixity: get_fixity(r)? },
            2 => ExprKind::Univ { level: r.u64()? },
            3 => ExprKind::Num(r.u64()?),
            4 => ExprKind::ArgSlot(r.option(Reader::u64)?),
            5 => ExprKind::App {
                head: Box::new(get_expr(r)?), args: r.vec(get_expr)?, named: r.vec(get_named_arg)?,
                explicit: r.bool()?, goal_oriented: r.bool()?,
            },
            6 => ExprKind::TyApp { head: Box::new(get_expr(r)?), args: r.vec(get_ty)? },
            7 => ExprKind::Lam { binders: r.vec(get_lam_binder)?, body: Box::new(get_expr(r)?) },
            8 => ExprKind::CollectionLit(r.vec(get_expr)?),
            9 => ExprKind::Eq(Box::new(get_expr(r)?), Box::new(get_expr(r)?)),
            10 => ExprKind::TyLit(Box::new(get_ty(r)?)),
            11 => ExprKind::Refl,
            12 => ExprKind::AutoRefl,
            13 => ExprKind::Hole(r.option(Reader::string)?),
            14 => ExprKind::Match {
                form: get_match_form(r)?, generated: r.bool()?, scrut: Box::new(get_expr(r)?),
                eqbind: r.option(Reader::string)?, motive: r.option(|r| Ok(Box::new(get_expr(r)?)))?,
                arms: r.vec(get_arm)?,
            },
            15 => ExprKind::MatchCode {
                scrut: Box::new(get_expr(r)?), motive: Box::new(get_ty(r)?), arms: r.vec(get_arm)?,
            },
            16 => ExprKind::Dot {
                recv: Box::new(get_expr(r)?), name: r.string()?,
                args: r.option(|r| r.vec(get_expr))?, named: r.vec(get_named_arg)?,
            },
            17 => ExprKind::Index { recv: Box::new(get_expr(r)?), idx: Box::new(get_expr(r)?) },
            18 => ExprKind::RecordLit {
                name: r.string()?, tyargs: r.vec(get_ty)?, fields: r.vec(|r| Ok(RecordLitField {
                    name: r.string()?, expr: get_expr(r)?, span: get_span(r)?,
                }))?,
            },
            19 => ExprKind::Block(Box::new(get_block(r)?)),
            20 => ExprKind::Quote(Box::new(get_expr(r)?)),
            21 => ExprKind::Splice(Box::new(get_expr(r)?)),
            22 => ExprKind::J {
                proof: Box::new(get_expr(r)?), motive: Box::new(get_expr(r)?), case: Box::new(get_expr(r)?),
            },
            tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "expression", tag }),
        };
        Ok(Expr { kind, span })
    })
}

fn put_stmt(w: &mut Writer, stmt: &Stmt) {
    match stmt {
        Stmt::Let { name, ty, expr, span } => {
            w.byte(0); w.string(name); w.option(ty.as_ref(), put_ty); put_expr(w, expr); put_span(w, *span);
        }
        Stmt::LetRecord { fields, expr, span } => {
            w.byte(1); w.vec(fields, |w, field| {
                w.string(&field.name); put_pat(w, &field.pat); put_span(w, field.span);
            }); put_expr(w, expr); put_span(w, *span);
        }
        Stmt::LetCode { name, expr, span } => {
            w.byte(2); w.string(name); put_expr(w, expr); put_span(w, *span);
        }
    }
}

fn get_stmt(r: &mut Reader<'_>) -> Result<Stmt, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(Stmt::Let {
            name: r.string()?, ty: r.option(get_ty)?, expr: get_expr(r)?, span: get_span(r)?,
        }),
        1 => Ok(Stmt::LetRecord {
            fields: r.vec(|r| Ok(RecordPatField {
                name: r.string()?, pat: get_pat(r)?, span: get_span(r)?,
            }))?, expr: get_expr(r)?, span: get_span(r)?,
        }),
        2 => Ok(Stmt::LetCode { name: r.string()?, expr: get_expr(r)?, span: get_span(r)? }),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "statement", tag }),
    }
}

fn put_on(w: &mut Writer, on: &OnStmt) {
    match &on.target {
        OnTarget::Name(name) => { w.byte(0); w.string(name); }
        OnTarget::Stmt(ty) => { w.byte(1); put_ty(w, ty); }
        OnTarget::Ctor { ctor, binders, default } => {
            w.byte(2); w.string(ctor); w.vec(binders, put_pat); w.bool(*default);
        }
    }
    put_expr(w, &on.expr); put_span(w, on.span);
}

fn get_on(r: &mut Reader<'_>) -> Result<OnStmt, ModuleImageDecodeError> {
    let target = match r.byte()? {
        0 => OnTarget::Name(r.string()?),
        1 => OnTarget::Stmt(get_ty(r)?),
        2 => OnTarget::Ctor { ctor: r.string()?, binders: r.vec(get_pat)?, default: r.bool()? },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "on target", tag }),
    };
    Ok(OnStmt { target, expr: get_expr(r)?, span: get_span(r)? })
}

fn put_block(w: &mut Writer, block: &Block) {
    w.vec(&block.stmts, put_stmt); put_expr(w, &block.result); w.vec(&block.ons, put_on);
    put_span(w, block.span);
}

fn get_block(r: &mut Reader<'_>) -> Result<Block, ModuleImageDecodeError> {
    Ok(Block {
        stmts: r.vec(get_stmt)?, result: Box::new(get_expr(r)?), ons: r.vec(get_on)?,
        span: get_span(r)?,
    })
}

fn put_param(w: &mut Writer, param: &Param) {
    w.string(&param.name); put_ty(w, &param.ty); w.bool(param.implicit); w.bool(param.is_self);
    w.option(param.solver.as_ref(), |w, solver| match solver { Solver::Infer => w.byte(0) });
    w.byte(match param.origin {
        ParamOrigin::Written => 0, ParamOrigin::InlineConstraint => 1, ParamOrigin::Assuming => 2,
    });
    w.option(param.symbol.as_ref(), |w, s| w.string(s)); put_span(w, param.span);
}

fn get_param(r: &mut Reader<'_>) -> Result<Param, ModuleImageDecodeError> {
    let name = r.string()?;
    let ty = get_ty(r)?;
    let implicit = r.bool()?;
    let is_self = r.bool()?;
    let solver = r.option(|r| match r.byte()? {
        0 => Ok(Solver::Infer),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "solver", tag }),
    })?;
    let origin = match r.byte()? {
        0 => ParamOrigin::Written, 1 => ParamOrigin::InlineConstraint, 2 => ParamOrigin::Assuming,
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "parameter origin", tag }),
    };
    Ok(Param {
        name, ty, implicit, is_self, solver, origin,
        symbol: r.option(Reader::string)?, span: get_span(r)?,
    })
}

fn put_decl(w: &mut Writer, decl: &Decl) {
    w.byte(match decl.kind { DeclKind::Fn => 0, DeclKind::Theorem => 1, DeclKind::Axiom => 2 });
    w.bool(decl.is_meta);
    w.option(decl.elaborates.as_ref(), |w, slot| {
        w.string(&slot.family); w.string(&slot.name); put_span(w, slot.span);
    });
    w.string(&decl.name);
    w.vec(&decl.tyvars, |w, var| { w.string(&var.name); w.u64(var.level); put_span(w, var.span); });
    w.vec(&decl.params, put_param); put_ty(w, &decl.result);
    w.option(decl.decreases.as_ref(), put_expr);
    if w.interface && matches!(decl.kind, DeclKind::Theorem | DeclKind::Axiom) {
        // The checked kernel binding retains the statement and opacity bit.
        // The proof block is neither delta-visible nor re-lowered downstream.
        w.byte(0xff);
    } else {
        put_block(w, &decl.body);
    }
    put_span(w, decl.span);
}

fn get_decl(r: &mut Reader<'_>) -> Result<Decl, ModuleImageDecodeError> {
    let kind = match r.byte()? {
        0 => DeclKind::Fn, 1 => DeclKind::Theorem, 2 => DeclKind::Axiom,
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "declaration kind", tag }),
    };
    Ok(Decl {
        kind, is_meta: r.bool()?, elaborates: r.option(|r| Ok(SlotPath {
            family: r.string()?, name: r.string()?, span: get_span(r)?,
        }))?, name: r.string()?, tyvars: r.vec(|r| Ok(TyParam {
            name: r.string()?, level: r.u64()?, span: get_span(r)?,
        }))?, params: r.vec(get_param)?, result: get_ty(r)?, decreases: r.option(get_expr)?,
        body: get_block(r)?, span: get_span(r)?,
    })
}

fn put_scope(w: &mut Writer, scope: &Scope) {
    w.string(&scope.module);
    w.vec(&scope.imports, |w, import| {
        w.string(&import.module);
        w.vec(&import.listed, |w, name| w.string(name));
        w.vec(&import.exported, |w, name| w.string(name));
    });
}

fn get_scope(r: &mut Reader<'_>) -> Result<Scope, ModuleImageDecodeError> {
    Ok(Scope {
        module: r.string()?,
        imports: r.vec(|r| Ok(ImportSpec { module: r.string()?, listed: r.vec(Reader::string)?, exported: r.vec(Reader::string)? }))?,
    })
}

fn put_name_kind(w: &mut Writer, kind: NameKind) {
    w.byte(match kind { NameKind::Global => 0, NameKind::Inductive => 1, NameKind::Ctor => 2, NameKind::Meta => 3 });
}

fn get_name_kind(r: &mut Reader<'_>) -> Result<NameKind, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(NameKind::Global), 1 => Ok(NameKind::Inductive),
        2 => Ok(NameKind::Ctor), 3 => Ok(NameKind::Meta),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "name kind", tag }),
    }
}

fn put_skel(w: &mut Writer, skel: &Skel) {
    w.nodes += 1;
    w.vec(&skel.params, |w, binder| {
        w.option(binder.name.as_ref(), |w, name| w.string(name));
        w.bool(binder.implicit); w.bool(binder.is_type);
        w.option(binder.dom.as_deref(), put_skel);
    });
}

fn get_skel(r: &mut Reader<'_>) -> Result<Skel, ModuleImageDecodeError> {
    r.node(|r| Ok(Skel { params: r.vec(|r| Ok(SkelBinder {
        name: r.option(Reader::string)?, implicit: r.bool()?, is_type: r.bool()?,
        dom: r.option(|r| Ok(Rc::new(get_skel(r)?)))?,
    }))? }))
}

fn put_param_meta(w: &mut Writer, param: &ParamMeta) {
    w.string(&param.name); w.bool(param.implicit); w.bool(param.is_type); w.bool(param.is_self);
    w.option(param.skel.as_deref(), put_skel); w.option(param.solver.as_deref(), put_ty);
}

fn get_param_meta(r: &mut Reader<'_>) -> Result<ParamMeta, ModuleImageDecodeError> {
    Ok(ParamMeta {
        name: r.string()?, implicit: r.bool()?, is_type: r.bool()?, is_self: r.bool()?,
        skel: r.option(|r| Ok(Rc::new(get_skel(r)?)))?,
        solver: r.option(|r| Ok(Rc::new(get_ty(r)?)))?,
    })
}

fn put_registration(w: &mut Writer, registration: &GlobalRegistration) {
    w.string(&registration.name); w.string(&registration.key);
    w.vec(&registration.params, put_param_meta);
    w.option(registration.member_base.as_ref(), |w, name| w.string(name));
    put_decl(w, &registration.surface);
}

fn get_registration(r: &mut Reader<'_>) -> Result<GlobalRegistration, ModuleImageDecodeError> {
    Ok(GlobalRegistration {
        name: r.string()?, key: r.string()?, params: Rc::new(r.vec(get_param_meta)?),
        member_base: r.option(Reader::string)?, surface: get_decl(r)?,
    })
}

fn put_gen_def(w: &mut Writer, key: GenDef) {
    match key {
        GenDef::Mu(tag) => { w.byte(0); w.u32(tag); }
        GenDef::IdxTag(tag, ctor) => { w.byte(1); w.u32(tag); w.usize(ctor); }
        GenDef::IdxChild(tag, ctor, child) => { w.byte(2); w.u32(tag); w.usize(ctor); w.usize(child); }
        GenDef::IdxCode(tag) => { w.byte(3); w.u32(tag); }
        GenDef::SkelCode(tag) => { w.byte(4); w.u32(tag); }
        GenDef::TyCode(tag) => { w.byte(5); w.u32(tag); }
        GenDef::ShapeCode(tag) => { w.byte(6); w.u32(tag); }
        GenDef::ArityFn(tag) => { w.byte(7); w.u32(tag); }
        GenDef::Fam(tag) => { w.byte(8); w.u32(tag); }
        GenDef::RecProj(tag, field) => { w.byte(9); w.u32(tag); w.usize(field); }
        GenDef::RecTail(tag, field) => { w.byte(10); w.u32(tag); w.usize(field); }
        GenDef::RecFam(tag, field) => { w.byte(11); w.u32(tag); w.usize(field); }
        GenDef::PayloadCode(tag, ctor) => { w.byte(12); w.u32(tag); w.usize(ctor); }
        GenDef::SuffixCode(tag, ctor) => { w.byte(13); w.u32(tag); w.usize(ctor); }
        GenDef::TyCodeFn(tag) => { w.byte(14); w.u32(tag); }
    }
}

fn get_gen_def(r: &mut Reader<'_>) -> Result<GenDef, ModuleImageDecodeError> {
    Ok(match r.byte()? {
        0 => GenDef::Mu(r.u32()?), 1 => GenDef::IdxTag(r.u32()?, r.usize()?),
        2 => GenDef::IdxChild(r.u32()?, r.usize()?, r.usize()?),
        3 => GenDef::IdxCode(r.u32()?), 4 => GenDef::SkelCode(r.u32()?),
        5 => GenDef::TyCode(r.u32()?), 6 => GenDef::ShapeCode(r.u32()?),
        7 => GenDef::ArityFn(r.u32()?), 8 => GenDef::Fam(r.u32()?),
        9 => GenDef::RecProj(r.u32()?, r.usize()?),
        10 => GenDef::RecTail(r.u32()?, r.usize()?),
        11 => GenDef::RecFam(r.u32()?, r.usize()?),
        12 => GenDef::PayloadCode(r.u32()?, r.usize()?),
        13 => GenDef::SuffixCode(r.u32()?, r.usize()?),
        14 => GenDef::TyCodeFn(r.u32()?),
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "generated definition", tag }),
    })
}

fn put_field_kind(w: &mut Writer, kind: FieldKind) {
    match kind {
        FieldKind::Payload => w.byte(0), FieldKind::Plain => w.byte(1),
        FieldKind::Container { len_payload } => { w.byte(2); w.usize(len_payload); }
        FieldKind::IndexVar => w.byte(3),
    }
}

fn get_field_kind(r: &mut Reader<'_>) -> Result<FieldKind, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(FieldKind::Payload), 1 => Ok(FieldKind::Plain),
        2 => Ok(FieldKind::Container { len_payload: r.usize()? }),
        3 => Ok(FieldKind::IndexVar),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "inductive field kind", tag }),
    }
}

fn put_ctor(w: &mut Writer, ctor: &Ctor) {
    w.string(&ctor.name);
    w.vec(&ctor.fields, |w, (name, ty)| {
        w.option(name.as_ref(), |w, name| w.string(name)); put_ty(w, ty);
    });
    w.vec(&ctor.kind, |w, kind| put_field_kind(w, *kind));
    w.option(ctor.res.as_ref(), |w, pat| {
        w.usize(pat.ctor); w.vec(&pat.vars, |w, var| w.usize(*var));
    });
    w.vec(&ctor.rec_at, |w, at| w.option(at.as_ref(), |w, at| w.usize(*at)));
    w.option(ctor.res_expr.as_ref(), put_expr);
}

fn get_ctor(r: &mut Reader<'_>) -> Result<Ctor, ModuleImageDecodeError> {
    Ok(Ctor {
        name: r.string()?,
        fields: r.vec(|r| Ok((r.option(Reader::string)?, get_ty(r)?)))?,
        kind: r.vec(get_field_kind)?,
        res: r.option(|r| Ok(IdxPat { ctor: r.usize()?, vars: r.vec(Reader::usize)? }))?,
        rec_at: r.vec(|r| r.option(Reader::usize))?,
        res_expr: r.option(get_expr)?,
    })
}

fn put_inductive(w: &mut Writer, info: &Inductive) {
    w.nodes += 1;
    w.string(&info.name); put_scope(w, &info.scope); w.u32(info.tag);
    w.vec(&info.params, |w, name| w.string(name));
    w.vec(&info.valparams, |w, (name, ty)| { w.string(name); put_ty(w, ty); });
    w.vec(&info.op_symbols, |w, (symbol, name)| { w.string(symbol); w.string(name); });
    w.vec(&info.ctors, put_ctor); w.bool(info.recursive); w.bool(info.is_record);
    w.option(info.index.as_ref(), |w, index| w.string(index));
    w.option(info.index_ty.as_ref(), |w, ty| match ty {
        IdxTy::Nat => w.byte(0),
        IdxTy::Decl(info) => { w.byte(1); put_inductive(w, info); }
    });
    w.option(info.skel.as_deref(), put_inductive);
}

fn get_inductive(r: &mut Reader<'_>) -> Result<Inductive, ModuleImageDecodeError> {
    r.node(|r| Ok(Inductive {
        name: r.string()?, scope: Rc::new(get_scope(r)?), tag: r.u32()?,
        params: r.vec(Reader::string)?,
        valparams: r.vec(|r| Ok((r.string()?, get_ty(r)?)))?,
        op_symbols: r.vec(|r| Ok((r.string()?, r.string()?)))?,
        ctors: r.vec(get_ctor)?, recursive: r.bool()?, is_record: r.bool()?,
        index: r.option(Reader::string)?,
        index_ty: r.option(|r| match r.byte()? {
            0 => Ok(IdxTy::Nat), 1 => Ok(IdxTy::Decl(Rc::new(get_inductive(r)?))),
            tag => Err(ModuleImageDecodeError::InvalidTag { sort: "index type", tag }),
        })?,
        skel: r.option(|r| Ok(Rc::new(get_inductive(r)?)))?,
    }))
}

fn put_field_decl(w: &mut Writer, field: &FieldDecl) {
    w.option(field.name.as_ref(), |w, name| w.string(name)); put_ty(w, &field.ty); put_span(w, field.span);
}

fn get_field_decl(r: &mut Reader<'_>) -> Result<FieldDecl, ModuleImageDecodeError> {
    Ok(FieldDecl { name: r.option(Reader::string)?, ty: get_ty(r)?, span: get_span(r)? })
}

fn put_class_ref(w: &mut Writer, class: &ClassRef) {
    w.string(&class.name); w.vec(&class.args, put_ty); w.vec(&class.index, put_expr);
    w.vec(&class.path, |w, part| w.string(part)); put_span(w, class.span);
}

fn get_class_ref(r: &mut Reader<'_>) -> Result<ClassRef, ModuleImageDecodeError> {
    Ok(ClassRef {
        name: r.string()?, args: r.vec(get_ty)?, index: r.vec(get_expr)?,
        path: r.vec(Reader::string)?, span: get_span(r)?,
    })
}

fn put_class(w: &mut Writer, info: &ClassInfo) {
    w.string(&info.name); w.vec(&info.params, |w, s| w.string(s)); w.vec(&info.valparams, put_param);
    w.vec(&info.fields, put_field_decl); w.vec(&info.ancestors, put_class_ref);
    w.vec(&info.owner, |w, owner| w.option(owner.as_ref(), |w, s| w.string(s)));
}

fn get_class(r: &mut Reader<'_>) -> Result<ClassInfo, ModuleImageDecodeError> {
    Ok(ClassInfo {
        name: r.string()?, params: r.vec(Reader::string)?, valparams: r.vec(get_param)?,
        fields: r.vec(get_field_decl)?, ancestors: r.vec(get_class_ref)?,
        owner: r.vec(|r| r.option(Reader::string))?,
    })
}

fn put_provenance(w: &mut Writer, provenance: Provenance) {
    w.byte(match provenance { Provenance::Named => 0, Provenance::Inline => 1, Provenance::Derived => 2, Provenance::ViaDerived => 3 });
}

fn get_provenance(r: &mut Reader<'_>) -> Result<Provenance, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(Provenance::Named), 1 => Ok(Provenance::Inline),
        2 => Ok(Provenance::Derived), 3 => Ok(Provenance::ViaDerived),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "artifact provenance", tag }),
    }
}

fn put_obligation(w: &mut Writer, obligation: &Obligation) {
    w.string(&obligation.owner); w.string(&obligation.path); w.string(&obligation.field);
    w.byte(match obligation.state { "supplied" => 0, "defaulted" => 1, state => panic!("unpersistable obligation state {state}") });
    w.option(obligation.provenance.as_ref(), |w, p| put_provenance(w, *p));
    w.string(&obligation.statement);
}

fn get_obligation(r: &mut Reader<'_>) -> Result<Obligation, ModuleImageDecodeError> {
    let owner = r.string()?; let path = r.string()?; let field = r.string()?;
    let state = match r.byte()? {
        0 => "supplied", 1 => "defaulted",
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "obligation state", tag }),
    };
    Ok(Obligation {
        owner, path, field, state, provenance: r.option(get_provenance)?, statement: r.string()?,
    })
}

fn put_slot(w: &mut Writer, slot: Slot) {
    w.byte(match slot {
        Slot::VecMap => 0, Slot::VecFold => 1, Slot::VecTabulate => 2, Slot::VecNth => 3,
        Slot::CertgenTranscribe => 4, Slot::CertgenCheckSig => 5,
    });
}

fn get_slot(r: &mut Reader<'_>) -> Result<Slot, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(Slot::VecMap), 1 => Ok(Slot::VecFold), 2 => Ok(Slot::VecTabulate),
        3 => Ok(Slot::VecNth), 4 => Ok(Slot::CertgenTranscribe), 5 => Ok(Slot::CertgenCheckSig),
        tag => Err(ModuleImageDecodeError::InvalidTag { sort: "elaboration slot", tag }),
    }
}

fn put_instance(w: &mut Writer, info: &InstanceInfo) {
    w.string(&info.global); w.string(&info.written); w.string(&info.index); w.bool(info.parameterized);
}

fn get_instance(r: &mut Reader<'_>) -> Result<InstanceInfo, ModuleImageDecodeError> {
    Ok(InstanceInfo {
        global: r.string()?, written: r.string()?, index: r.string()?, parameterized: r.bool()?,
    })
}

fn put_designation(w: &mut Writer, info: &DesignationInfo) {
    w.string(&info.op); w.string(&info.written); w.string(&info.carrier);
}

fn get_designation(r: &mut Reader<'_>) -> Result<DesignationInfo, ModuleImageDecodeError> {
    Ok(DesignationInfo { op: r.string()?, written: r.string()?, carrier: r.string()? })
}

fn put_derived(w: &mut Writer, info: &DerivedInst) {
    w.string(&info.name); w.u32(info.abs); put_type(w, &info.ty); put_level(w, &info.level); w.u32(info.at);
    w.option(info.head.as_ref(), |w, head| w.string(head));
}

fn get_derived(r: &mut Reader<'_>) -> Result<DerivedInst, ModuleImageDecodeError> {
    Ok(DerivedInst {
        name: r.string()?, abs: r.u32()?, ty: get_type(r)?, level: get_level(r)?, at: r.u32()?,
        head: r.option(|r| r.string())?,
    })
}

fn put_datarepr(w: &mut Writer, info: &DatareprInfo) {
    w.string(&info.global); w.string(&info.written); w.string(&info.carrier); w.string(&info.record);
    w.vec(&info.ctors, |w, ctor| {
        w.string(&ctor.name);
        w.vec(&ctor.fields, |w, field| {
            w.string(&field.binder); w.bool(field.rec); w.string(&field.spell);
        });
    });
}

fn get_datarepr(r: &mut Reader<'_>) -> Result<DatareprInfo, ModuleImageDecodeError> {
    Ok(DatareprInfo {
        global: r.string()?, written: r.string()?, carrier: r.string()?, record: r.string()?,
        ctors: Rc::new(r.vec(|r| Ok(CtorView {
            name: r.string()?, fields: r.vec(|r| Ok(FieldView {
                binder: r.string()?, rec: r.bool()?, spell: r.string()?,
            }))?,
        }))?),
    })
}

fn put_meta(w: &mut Writer, definition: &MetaDef) {
    put_term(w, &definition.term); put_type(w, &definition.stmt); w.u32(definition.psi_len);
    w.vec(&definition.order, |w, index| w.usize(*index));
}

fn get_meta(r: &mut Reader<'_>) -> Result<MetaDef, ModuleImageDecodeError> {
    Ok(MetaDef {
        term: Rc::new(get_term(r)?), stmt: Rc::new(get_type(r)?), psi_len: r.u32()?,
        order: r.vec(Reader::usize)?,
    })
}

/// The deterministic encoding of a run of events, for comparing two runs
/// structurally (`ModuleDelta` slices: `docs/declaration-slice-replay-design.md`
/// §4). With `interface`, the projection a dependent observes — spans
/// zeroed, theorem proofs and proof dependency edges dropped — which is what
/// "the same contribution" means for the declarations after it.
pub(crate) fn encode_events(events: &[DeltaEvent], interface: bool) -> Vec<u8> {
    let mut w = Writer { bytes: Vec::new(), interface, nodes: 0 };
    w.vec(events, put_event);
    w.bytes
}

/// The same events with every span moved by `offset`: a replayed slice's
/// events, at the position its unchanged text now has. Through the image
/// encoding, because `put_span`/`get_span` are the one place every span in
/// every event payload passes.
pub(crate) fn relocate_events(
    events: &[DeltaEvent],
    offset: i64,
) -> Result<Vec<DeltaEvent>, ModuleImageDecodeError> {
    if offset == 0 {
        return Ok(events.to_vec());
    }
    let bytes = encode_events(events, false);
    let mut r = Reader::new(&bytes, ModuleImageLimits::default())?;
    r.span_offset = offset;
    let events = r.vec(get_event)?;
    r.finish()?;
    Ok(events)
}

fn put_event(w: &mut Writer, event: &DeltaEvent) {
    match event {
        DeltaEvent::Name { name, kind } => { w.byte(0); w.string(name); put_name_kind(w, *kind); }
        DeltaEvent::Global { abs, registration, is_axiom, direct_dependencies } => {
            w.byte(1); w.u32(*abs); put_registration(w, registration); w.bool(*is_axiom);
            if w.interface {
                // Proof dependency edges feed provenance reports dynamically
                // from the restored prefix; dependent elaboration does not
                // specialize against the body of an opaque theorem.
                w.len(0);
            } else {
                w.vec(direct_dependencies, |w, dependency| w.string(dependency));
            }
        }
        DeltaEvent::GenDef { key, abs } => { w.byte(2); put_gen_def(w, *key); w.u32(*abs); }
        DeltaEvent::GenTyCode { tag, inline, level } => {
            w.byte(3); w.u32(*tag); put_type(w, inline); put_level(w, level);
        }
        DeltaEvent::GenWfSlots { tag, slots } => {
            w.byte(4); w.u32(*tag); put_type(w, &slots.shape); put_type(w, &slots.shape_decoded);
            put_term(w, &slots.arity); put_level(w, &slots.level);
        }
        DeltaEvent::GenFamLevels { tag, level, index_level } => {
            w.byte(5); w.u32(*tag); put_level(w, level); put_level(w, index_level);
        }
        DeltaEvent::Inductive { module, info } => {
            w.byte(6); w.string(module); put_inductive(w, info);
        }
        DeltaEvent::Class { key, info } => { w.byte(7); w.string(key); put_class(w, info); }
        DeltaEvent::Instance { key, info } => {
            w.byte(8); w.string(&key.0); w.string(&key.1); w.string(&key.2); put_instance(w, info);
        }
        DeltaEvent::Designation { key, info } => {
            w.byte(9); put_fixity(w, key.0); w.string(&key.1); w.string(&key.2); put_designation(w, info);
        }
        DeltaEvent::Derived(info) => { w.byte(10); put_derived(w, info); }
        DeltaEvent::Repr { key, name, info, monomorph, obligations } => {
            w.byte(11); w.option(key.0.as_ref(), |w, tag| w.u32(*tag)); w.string(&key.1);
            w.string(name); put_datarepr(w, info);
            w.option(monomorph.as_ref(), |w, (tag, name)| { w.u32(*tag); w.string(name); });
            w.vec(obligations, put_obligation);
        }
        DeltaEvent::Impl { repr, op, entry, obligations } => {
            w.byte(12); w.string(repr); w.string(op); w.string(&entry.global);
            put_provenance(w, entry.provenance); w.vec(obligations, put_obligation);
        }
        DeltaEvent::Access { designed, minted } => { w.byte(13); w.string(designed); w.string(minted); }
        DeltaEvent::InternalAccess { minted, owner } => { w.byte(14); w.string(minted); w.string(owner); }
        DeltaEvent::Meta { module, name, slot, definition } => {
            w.byte(15); w.string(module); w.string(name); w.option(slot.as_ref(), |w, slot| put_slot(w, *slot));
            put_meta(w, definition);
        }
        DeltaEvent::GenTyCodeFn { tag, entry } => {
            w.byte(17); w.u32(*tag); put_type(w, &entry.template); put_type(w, &entry.stmt);
            w.vec(&entry.param_levels, put_level); put_level(w, &entry.level);
        }
        DeltaEvent::GenSpineCodes { tag, codes } => {
            w.byte(16); w.u32(*tag);
            w.vec(&codes.ctors, |w, (ty, level)| { put_type(w, ty); put_level(w, level); });
            w.vec(&codes.tails, |w, (ty, level)| { put_type(w, ty); put_level(w, level); });
        }
    }
}

fn get_event(r: &mut Reader<'_>) -> Result<DeltaEvent, ModuleImageDecodeError> {
    Ok(match r.byte()? {
        0 => DeltaEvent::Name { name: r.string()?, kind: get_name_kind(r)? },
        1 => DeltaEvent::Global {
            abs: r.u32()?, registration: get_registration(r)?, is_axiom: r.bool()?,
            direct_dependencies: r.vec(Reader::string)?,
        },
        2 => DeltaEvent::GenDef { key: get_gen_def(r)?, abs: r.u32()? },
        3 => DeltaEvent::GenTyCode { tag: r.u32()?, inline: Rc::new(get_type(r)?), level: get_level(r)? },
        4 => DeltaEvent::GenWfSlots { tag: r.u32()?, slots: WfSlots {
            shape: Rc::new(get_type(r)?), shape_decoded: Rc::new(get_type(r)?),
            arity: Rc::new(get_term(r)?), level: get_level(r)?,
        } },
        5 => DeltaEvent::GenFamLevels { tag: r.u32()?, level: get_level(r)?, index_level: get_level(r)? },
        6 => DeltaEvent::Inductive { module: r.string()?, info: Rc::new(get_inductive(r)?) },
        7 => DeltaEvent::Class { key: r.string()?, info: get_class(r)? },
        8 => DeltaEvent::Instance {
            key: (r.string()?, r.string()?, r.string()?), info: get_instance(r)?,
        },
        9 => DeltaEvent::Designation {
            key: (get_fixity(r)?, r.string()?, r.string()?), info: get_designation(r)?,
        },
        10 => DeltaEvent::Derived(get_derived(r)?),
        11 => DeltaEvent::Repr {
            key: (r.option(Reader::u32)?, r.string()?), name: r.string()?, info: get_datarepr(r)?,
            monomorph: r.option(|r| Ok((r.u32()?, r.string()?)))?, obligations: r.vec(get_obligation)?,
        },
        12 => DeltaEvent::Impl {
            repr: r.string()?, op: r.string()?,
            entry: ImplEntry { global: r.string()?, provenance: get_provenance(r)? },
            obligations: r.vec(get_obligation)?,
        },
        13 => DeltaEvent::Access { designed: r.string()?, minted: r.string()? },
        14 => DeltaEvent::InternalAccess { minted: r.string()?, owner: r.string()? },
        15 => DeltaEvent::Meta {
            module: r.string()?, name: r.string()?, slot: r.option(get_slot)?, definition: get_meta(r)?,
        },
        17 => DeltaEvent::GenTyCodeFn { tag: r.u32()?, entry: TyCodeFn {
            template: Rc::new(get_type(r)?), stmt: Rc::new(get_type(r)?),
            param_levels: r.vec(get_level)?, level: get_level(r)?,
        } },
        16 => DeltaEvent::GenSpineCodes { tag: r.u32()?, codes: SpineCodes {
            ctors: r.vec(|r| Ok((Rc::new(get_type(r)?), get_level(r)?)))?,
            tails: r.vec(|r| Ok((Rc::new(get_type(r)?), get_level(r)?)))?,
        } },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "module event", tag }),
    })
}

fn validate_inductive(info: &Inductive) -> Result<(), ModuleImageDecodeError> {
    if info.index.is_some() != info.index_ty.is_some() {
        return Err(ModuleImageDecodeError::InvalidStructure("inductive index name/type disagree"));
    }
    for ctor in &info.ctors {
        if ctor.fields.len() != ctor.kind.len() || ctor.fields.len() != ctor.rec_at.len() {
            return Err(ModuleImageDecodeError::InvalidStructure("constructor field tables disagree"));
        }
        if let Some(pat) = &ctor.res
            && pat.vars.iter().any(|index| *index >= ctor.fields.len())
        {
            return Err(ModuleImageDecodeError::InvalidStructure("constructor index pattern is out of bounds"));
        }
    }
    if let Some(IdxTy::Decl(index)) = &info.index_ty { validate_inductive(index)?; }
    if let Some(skel) = &info.skel { validate_inductive(skel)?; }
    Ok(())
}

fn validate_delta(delta: &ModuleDelta) -> Result<(), ModuleImageDecodeError> {
    let base = delta.dependency_psi.bindings.len();
    let end = base.checked_add(delta.extension.len()).ok_or(ModuleImageDecodeError::InvalidStructure("global range overflows"))?;
    let valid_abs = |abs: u32| usize::try_from(abs).is_ok_and(|abs| (base..end).contains(&abs));
    let mut globals = HashSet::new();
    let mut global_positions = HashSet::new();
    let mut gen_defs = HashSet::new();
    let mut gen_positions = HashSet::new();
    let mut ty_codes = HashSet::new();
    let mut ty_code_fns = HashSet::new();
    let mut wf_slots = HashSet::new();
    let mut spine_codes = HashSet::new();
    let mut fam_levels = HashSet::new();
    let mut inductives = HashSet::new();
    let mut inductive_tags = HashSet::new();
    let mut classes = HashSet::new();
    let mut instances = HashSet::new();
    let mut designations = HashSet::new();
    let mut derived = HashSet::new();
    let mut reprs = HashSet::new();
    let mut repr_names = HashSet::new();
    let mut monomorphs = HashSet::new();
    let mut impls = HashSet::new();
    let mut access = HashSet::new();
    let mut restricted_names = HashSet::new();
    let mut metas = HashSet::new();
    let mut meta_slots = HashSet::new();
    for event in &delta.events {
        match event {
            DeltaEvent::Global { abs, .. } if !valid_abs(*abs) => {
                return Err(ModuleImageDecodeError::InvalidStructure("event references a global outside the module suffix"));
            }
            DeltaEvent::Global { abs, registration, .. } => {
                if registration.key != format!("{}::{}", delta.module, registration.name)
                    || registration.surface.name != registration.name
                {
                    return Err(ModuleImageDecodeError::InvalidStructure("global registration names disagree"));
                }
                if !globals.insert(registration.key.clone()) || !global_positions.insert(*abs) {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate global registration"));
                }
            }
            DeltaEvent::GenDef { key, abs } if !valid_abs(*abs) => {
                return Err(ModuleImageDecodeError::InvalidStructure("event references a global outside the module suffix"));
            }
            DeltaEvent::GenDef { key, abs } => {
                if !gen_defs.insert(*key) || !gen_positions.insert(*abs) {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated-definition registration"));
                }
            }
            DeltaEvent::GenTyCode { tag, .. } if !ty_codes.insert(*tag) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated type-code guard"));
            }
            DeltaEvent::GenTyCodeFn { tag, .. } if !ty_code_fns.insert(*tag) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated type-code function guard"));
            }
            DeltaEvent::GenWfSlots { tag, .. } if !wf_slots.insert(*tag) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated Wf-slot guard"));
            }
            DeltaEvent::GenSpineCodes { tag, codes } => {
                if !spine_codes.insert(*tag) {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated spine-code guard"));
                }
                if codes.ctors.len() < 2 || codes.tails.len() + 1 != codes.ctors.len() {
                    return Err(ModuleImageDecodeError::InvalidStructure("generated spine-code guard is not a spine"));
                }
            }
            DeltaEvent::GenFamLevels { tag, .. } if !fam_levels.insert(*tag) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated family-level entry"));
            }
            DeltaEvent::Derived(info) if !valid_abs(info.abs) => {
                return Err(ModuleImageDecodeError::InvalidStructure("derived instance references a global outside the module suffix"));
            }
            DeltaEvent::Derived(info) if !derived.insert(info.abs) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate derived instance"));
            }
            DeltaEvent::Inductive { module, info } => {
                if module != &delta.module || info.scope.module != delta.module {
                    return Err(ModuleImageDecodeError::InvalidStructure("inductive belongs to another module"));
                }
                if !inductives.insert((module.clone(), info.name.clone())) {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate inductive registration"));
                }
                if !inductive_tags.insert(info.tag)
                    || info.skel.as_ref().is_some_and(|skel| !inductive_tags.insert(skel.tag))
                {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate inductive tag"));
                }
                validate_inductive(info)?;
            }
            DeltaEvent::Class { info, .. } if info.fields.len() != info.owner.len() => {
                return Err(ModuleImageDecodeError::InvalidStructure("class field/owner tables disagree"));
            }
            DeltaEvent::Class { key, .. } if !classes.insert(key.clone()) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate class registration"));
            }
            DeltaEvent::Instance { key, .. } if !instances.insert(key.clone()) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate instance registration"));
            }
            DeltaEvent::Designation { key, .. } if !designations.insert(key.clone()) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate designation registration"));
            }
            DeltaEvent::Repr { key, name, .. }
                if !reprs.insert(key.clone()) || !repr_names.insert(name.clone()) =>
            {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate representation registration"));
            }
            DeltaEvent::Repr { monomorph: Some(key), .. } if !monomorphs.insert(key.clone()) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate representation monomorph"));
            }
            DeltaEvent::Impl { repr, op, .. } if !impls.insert((repr.clone(), op.clone())) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate implementation registration"));
            }
            DeltaEvent::Access { designed, minted }
                if !access.insert(designed.clone()) || !restricted_names.insert(minted.clone()) =>
            {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate designed access path"));
            }
            DeltaEvent::InternalAccess { minted, .. } if !restricted_names.insert(minted.clone()) => {
                return Err(ModuleImageDecodeError::InvalidStructure("duplicate internal access path"));
            }
            DeltaEvent::Meta { module, name, slot, .. } => {
                if module != &delta.module {
                    return Err(ModuleImageDecodeError::InvalidStructure("meta-program belongs to another module"));
                }
                if !metas.insert((module.clone(), name.clone()))
                    || slot.is_some_and(|slot| !meta_slots.insert(slot))
                {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate meta-program registration"));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub(crate) fn encode_delta(delta: &ModuleDelta) -> Vec<u8> {
    encode_delta_counted(delta).0
}

/// The image bytes and the syntax-node count the reader will charge for
/// them — the number a publisher compares against `max_nodes` before writing
/// an image the reader would only decode up to the budget and refuse.
pub(crate) fn encode_delta_counted(delta: &ModuleDelta) -> (Vec<u8>, u64) {
    let mut w = Writer::default();
    encode_delta_into(&mut w, delta, MAGIC);
    (w.bytes, w.nodes)
}

pub(crate) fn encode_delta_interface(delta: &ModuleDelta) -> Vec<u8> {
    let mut w = Writer { bytes: Vec::new(), interface: true, nodes: 0 };
    encode_delta_into(&mut w, delta, INTERFACE_MAGIC);
    w.bytes
}

fn encode_delta_into(w: &mut Writer, delta: &ModuleDelta, magic: &[u8; 8]) {
    w.bytes.extend_from_slice(magic);
    w.string(&delta.module);
    w.len(delta.dependencies.ordered_interface_hashes().len());
    for hash in delta.dependencies.ordered_interface_hashes() { w.bytes.extend_from_slice(hash); }
    w.len(delta.dependency_psi.bindings.len());
    w.vec(&delta.extension, put_binding); put_scope(w, &delta.scope); w.vec(&delta.events, put_event);
    // The declaration slices (`docs/declaration-slice-replay-design.md` §3):
    // the semantic image only, never the interface projection, since a
    // slice's text is not something a dependent observes.
    if !w.interface {
        w.vec(&delta.items, put_slice);
        w.option(delta.scope_at_entry.as_ref(), put_scope);
    }
}

fn put_slice(w: &mut Writer, slice: &crate::module_delta::ItemSlice) {
    w.string(&slice.source);
    w.usize(slice.start);
    for range in [&slice.psi, &slice.events, &slice.warnings] {
        w.usize(range.start);
        w.usize(range.end);
    }
}

fn get_slice(r: &mut Reader<'_>) -> Result<crate::module_delta::ItemSlice, ModuleImageDecodeError> {
    let source = r.string()?;
    let start = r.usize()?;
    let mut ranges = [0..0, 0..0, 0..0];
    for range in &mut ranges {
        let (a, b) = (r.usize()?, r.usize()?);
        if a > b {
            return Err(ModuleImageDecodeError::InvalidStructure("a slice range is reversed"));
        }
        *range = a..b;
    }
    let [psi, events, warnings] = ranges;
    Ok(crate::module_delta::ItemSlice { source, start, psi, events, warnings })
}

pub(crate) fn decode_delta(
    bytes: &[u8],
    dependency_psi: GlobalCtx,
    limits: ModuleImageLimits,
) -> Result<ModuleDelta, ModuleImageDecodeError> {
    let mut r = Reader::new(bytes, limits)?;
    if r.take(MAGIC.len())? != MAGIC { return Err(ModuleImageDecodeError::UnsupportedFormat); }
    let module = r.string()?;
    let hash_count = r.len()?;
    if hash_count > r.bytes.len().saturating_sub(r.at) / 32 {
        return Err(ModuleImageDecodeError::Truncated);
    }
    let mut hashes = Vec::with_capacity(hash_count);
    for _ in 0..hash_count { hashes.push(r.take(32)?.try_into().unwrap()); }
    let expected = r.len()?;
    let actual = dependency_psi.bindings.len();
    if expected != actual {
        return Err(ModuleImageDecodeError::DependencyPrefixLength { expected, actual });
    }
    let extension = r.vec(get_binding)?;
    let scope = get_scope(&mut r)?;
    let events = r.vec(get_event)?;
    let items = r.vec(get_slice)?;
    let scope_at_entry = r.option(get_scope)?;
    r.finish()?;
    if scope.module != module {
        return Err(ModuleImageDecodeError::InvalidStructure("module and scope names disagree"));
    }
    // Slices partition the extension and the events in order; the warning
    // ranges are checked by whoever decodes the warnings beside this image.
    let (mut psi_at, mut events_at) = (0, 0);
    for slice in &items {
        if slice.psi.start != psi_at || slice.events.start != events_at {
            return Err(ModuleImageDecodeError::InvalidStructure("slices do not partition the delta"));
        }
        psi_at = slice.psi.end;
        events_at = slice.events.end;
    }
    if !items.is_empty() && (psi_at != extension.len() || events_at != events.len()) {
        return Err(ModuleImageDecodeError::InvalidStructure("slices do not cover the delta"));
    }
    let delta = ModuleDelta {
        module, dependencies: ModuleDependencyIdentity::new(hashes), dependency_psi,
        extension, scope, events,
        items,
        warnings: Vec::new(),
        scope_at_entry,
    };
    validate_delta(&delta)?;
    Ok(delta)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Elaborator;

    #[test]
    fn the_envelope_magic_and_basic_budgets_are_total() {
        assert_eq!(MAGIC.len(), 8);
        let limits = ModuleImageLimits { max_bytes: 3, ..ModuleImageLimits::default() };
        assert_eq!(
            Reader::new(&[0; 4], limits).err().expect("byte budget must fail"),
            ModuleImageDecodeError::TooLarge
        );

        let mut r = Reader::new(&[2], ModuleImageLimits::default()).unwrap();
        assert_eq!(r.bool().unwrap_err(), ModuleImageDecodeError::InvalidBool(2));
    }

    fn ordinary_delta() -> (GlobalCtx, ModuleDelta) {
        let mut elaborator = Elaborator::new();
        let prefix = elaborator.psi().clone();
        let identity = ModuleDependencyIdentity::new(vec![[0x17; 32], [0xa4; 32]]);
        let delta = elaborator
            .elab_module_delta(
                "codec",
                "fn id(x: Nat) -> Nat { x }\ntheorem id_zero(): id(0) = 0 { refl }",
                identity,
            )
            .expect("build test delta");
        (prefix, delta)
    }

    #[test]
    fn module_image_is_deterministic_roundtrips_and_replays() {
        let (prefix, delta) = ordinary_delta();
        let bytes = delta.to_image_bytes();
        let decoded = ModuleDelta::from_image_bytes(
            &bytes,
            prefix,
            ModuleImageLimits::default(),
        )
        .expect("decode image");
        assert_eq!(decoded.to_image_bytes(), bytes);
        assert_eq!(decoded.dependencies, delta.dependencies);

        let mut target = Elaborator::new();
        target
            .replay_module_delta(&decoded, &delta.dependencies)
            .expect("recheck decoded suffix");

        let (_, rebuilt) = ordinary_delta();
        assert_eq!(rebuilt.to_image_bytes(), bytes);
    }

    #[test]
    fn every_truncation_and_any_trailing_byte_is_rejected() {
        let (prefix, delta) = ordinary_delta();
        let bytes = delta.to_image_bytes();
        for cut in 0..bytes.len() {
            assert!(
                ModuleDelta::from_image_bytes(
                    &bytes[..cut],
                    prefix.clone(),
                    ModuleImageLimits::default(),
                )
                .is_err(),
                "accepted truncation at {cut} of {} bytes",
                bytes.len()
            );
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert_eq!(
            ModuleDelta::from_image_bytes(&trailing, prefix, ModuleImageLimits::default())
                .err().expect("trailing byte must fail"),
            ModuleImageDecodeError::TrailingBytes
        );
    }

    #[test]
    fn hostile_lengths_and_recursion_budgets_fail_before_publication() {
        let mut huge_string = MAGIC.to_vec();
        huge_string.extend_from_slice(&u64::MAX.to_le_bytes());
        assert_eq!(
            ModuleDelta::from_image_bytes(
                &huge_string,
                GlobalCtx::default(),
                ModuleImageLimits::default(),
            )
            .err().expect("huge string must fail"),
            ModuleImageDecodeError::StringTooLong
        );

        let mut impossible_hashes = MAGIC.to_vec();
        impossible_hashes.extend_from_slice(&0_u64.to_le_bytes());
        impossible_hashes.extend_from_slice(&u64::MAX.to_le_bytes());
        let permissive = ModuleImageLimits {
            max_sequence: usize::MAX,
            ..ModuleImageLimits::default()
        };
        assert_eq!(
            ModuleDelta::from_image_bytes(&impossible_hashes, GlobalCtx::default(), permissive)
                .err().expect("impossible hash count must fail"),
            ModuleImageDecodeError::Truncated
        );

        let (prefix, delta) = ordinary_delta();
        let bytes = delta.to_image_bytes();
        let no_sequences = ModuleImageLimits { max_sequence: 0, ..ModuleImageLimits::default() };
        assert_eq!(
            ModuleDelta::from_image_bytes(&bytes, prefix.clone(), no_sequences)
                .err().expect("sequence budget must fail"),
            ModuleImageDecodeError::SequenceTooLong
        );
        let no_nodes = ModuleImageLimits { max_nodes: 0, ..ModuleImageLimits::default() };
        assert_eq!(
            ModuleDelta::from_image_bytes(&bytes, prefix.clone(), no_nodes)
                .err().expect("node budget must fail"),
            ModuleImageDecodeError::NodeBudget
        );
        let no_depth = ModuleImageLimits { max_depth: 0, ..ModuleImageLimits::default() };
        assert_eq!(
            ModuleDelta::from_image_bytes(&bytes, prefix, no_depth)
                .err().expect("depth budget must fail"),
            ModuleImageDecodeError::DepthBudget
        );
    }

    #[test]
    fn decoded_absolute_references_must_point_into_the_suffix() {
        let delta = ModuleDelta {
            module: "bad".into(),
            dependencies: ModuleDependencyIdentity::default(),
            dependency_psi: GlobalCtx::default(),
            extension: vec![GlobalBinding::Ctx],
            scope: Scope::new("bad"),
            events: vec![DeltaEvent::GenDef { key: GenDef::Mu(0), abs: 99 }],
            items: Vec::new(),
            warnings: Vec::new(),
            scope_at_entry: None,
        };
        assert_eq!(
            ModuleDelta::from_image_bytes(
                &delta.to_image_bytes(),
                GlobalCtx::default(),
                ModuleImageLimits::default(),
            )
            .err().expect("dangling absolute reference must fail"),
            ModuleImageDecodeError::InvalidStructure(
                "event references a global outside the module suffix"
            )
        );
    }

    #[test]
    fn duplicate_correlated_events_are_rejected() {
        let delta = ModuleDelta {
            module: "bad".into(),
            dependencies: ModuleDependencyIdentity::default(),
            dependency_psi: GlobalCtx::default(),
            extension: vec![GlobalBinding::Ctx, GlobalBinding::Ctx],
            scope: Scope::new("bad"),
            events: vec![
                DeltaEvent::GenDef { key: GenDef::Mu(0), abs: 0 },
                DeltaEvent::GenDef { key: GenDef::Mu(0), abs: 1 },
            ],
            items: Vec::new(),
            warnings: Vec::new(),
            scope_at_entry: None,
        };
        assert_eq!(
            ModuleDelta::from_image_bytes(
                &delta.to_image_bytes(),
                GlobalCtx::default(),
                ModuleImageLimits::default(),
            )
            .err().expect("duplicate generated definition must fail"),
            ModuleImageDecodeError::InvalidStructure(
                "duplicate generated-definition registration"
            )
        );
    }

    #[test]
    fn rich_frontend_registry_payloads_roundtrip_and_replay() {
        let mut source = Elaborator::with_prelude().expect("build prelude");
        let prefix = source.psi().clone();
        let identity = ModuleDependencyIdentity::new(vec![[0x42; 32]]);
        let delta = source
            .elab_module_delta(
                "features",
                r#"
inductive Z { Z0 }
inductive Chain { End, Link(tail: Chain) }
fn zop(x: Z, y: Z) -> Z { x }
class Mag<A> { op: A -> A -> A }
class Pointed<A>(op: A -> A -> A) {
    point: A,
    stable: (x, y: A) -> op(x, y) = op(x, y),
}
class TwoPointed<A>(first, second: A -> A -> A)
    extends Pointed<A>(first) as first_laws,
            Pointed<A>(second) as second_laws
{}
instance Mag<Z> { op := zop }
designation + at Z := zop
meta fn zero_code(g: Ctx) -> Code(g |- Nat) { code { 0 } }
datarepr NatN for Nat := repr::naive();
"#,
                identity.clone(),
            )
            .expect("build registry-rich delta");
        let bytes = delta.to_image_bytes();
        let decoded = ModuleDelta::from_image_bytes(
            &bytes,
            prefix,
            ModuleImageLimits::default(),
        )
        .expect("decode registry-rich image");
        assert_eq!(decoded.to_image_bytes(), bytes);

        let mut target = Elaborator::with_prelude().expect("rebuild prelude");
        target
            .replay_module_delta(&decoded, &identity)
            .expect("recheck and publish registry-rich image");
        assert_eq!(target.psi(), source.psi());
    }

    #[test]
    fn replay_reports_dependency_metadata_conflicts_without_panicking() {
        const META: &str =
            "meta fn zero_code(g: Ctx) -> Code(g |- Nat) { code { 0 } }";
        let mut source = Elaborator::with_prelude().expect("build source prelude");
        let prefix = source.psi().clone();
        let identity = ModuleDependencyIdentity::new(vec![[0x81; 32]]);
        let delta = source
            .elab_module_delta("templates", META, identity.clone())
            .expect("build meta delta");
        let decoded = ModuleDelta::from_image_bytes(
            &delta.to_image_bytes(),
            prefix,
            ModuleImageLimits::default(),
        )
        .expect("decode meta image");

        let mut target = Elaborator::with_prelude().expect("build target prelude");
        target.elab_module_source("templates", META).expect("install conflicting metadata");
        assert!(matches!(
            target.replay_module_delta(&decoded, &identity),
            Err(crate::ModuleReplayError::MetadataConflict(_))
        ));
    }
}
