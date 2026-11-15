//! Bounded, versioned wire format for semantic module images.
//!
//! This module deliberately owns a manual codec rather than deriving a
//! general-purpose deserializer for kernel or elaborator state. Every length
//! is checked before allocation, every recursive node consumes both a node
//! and depth budget, and decoded values remain inert until `ModuleDelta`'s
//! ordinary replay boundary validates and publishes them.

use std::fmt;
use std::collections::{HashMap, HashSet};
use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::term::{Numeral, 
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, IWfSig, MSig, LocalCtx, LocalSubst, LocalVar,
    Motives, ProofSource, SealedProof, SubstTail, Term, Type,
};
use heather_syntax::{
    Arm, Block, ClassRef, Decl, DeclKind, Expr, ExprKind, FieldDecl, LamBinder, MatchForm,
    NamedArg, OnStmt, OnTarget, OpFixity, Param, ParamOrigin, Pat, RecordLitField,
    RecordPatField, SlotPath, Solver, Span, Stmt, Ty, TyKind, TyParam,
};

use crate::application::{ParamDefault, ParamMeta, Skel, SkelBinder};
use crate::datarepr::{CtorView, DatareprInfo, FieldView, ImplEntry, Obligation, Provenance};
use crate::gendefs::{GenDef, SpineCodes, TyCodeFn, WfSlots};
use crate::inductive::{Ctor, FieldKind, IdxPat, IdxTy, Inductive, Member};
use crate::metaprograms::MetaDef;
use crate::module_delta::{DeltaEvent, ModuleDelta, ModuleDependencyIdentity};
use crate::names::{GlobalRegistration, ImportSpec, NameKind, Scope};
use crate::resolve::DerivedInst;
use crate::slots::Slot;
use crate::traits::{ClassInfo, DesignationInfo, EvidenceRule, InstanceInfo};

const MAGIC: &[u8; 8] = b"HTHMOD\0\x24";
const INTERFACE_MAGIC: &[u8; 8] = b"HTHIFC\0\x1e";

/// The two encodings' versions, image then interface: what a module cache
/// key covers, so a bump of either is a clean miss for every reader rather
/// than a stored image whose header still answers for its key while its
/// body no longer decodes (`issues/library-gate-native-tests-fresh-box-rail.md`).
pub fn image_format() -> [u8; 16] {
    let mut out = [0; 16];
    out[..8].copy_from_slice(MAGIC);
    out[8..].copy_from_slice(INTERFACE_MAGIC);
    out
}

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
    /// The OS would not give the decoder the stack its depth budget needs
    /// ([`decode_on_own_stack`]). Refused rather than decoded on the
    /// caller's stack, which the budget was not sized for.
    NoStack,
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
            Self::NoStack => write!(f, "cannot start a thread with the module-image decoder's stack"),
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
    share: Share,
}

impl Default for Writer {
    fn default() -> Self {
        Self { bytes: Vec::new(), interface: false, nodes: 0, share: Share::default() }
    }
}

/// The writer's side of the image's node sharing. A term or type is written
/// once; every later occurrence of an equal one is [`tag::SHARED`] and the
/// index the reader gave the first ([`Reader::terms`]). Without it an image
/// was a tree: the elaborator's terms share subterms freely (one `Arc` under
/// many parents), and a module whose definitions are such DAGs wrote, and
/// every replay decoded, each shared subterm once per path to it — the
/// tactic modules' images were a hundred megabytes and took seconds and
/// gigabytes to decode in every process that replayed them.
///
/// Equal means structurally equal, not the same allocation: each node gets
/// a canonical number from its shallow encoding with its children as their
/// numbers ([`Writer::canonical_term`]), so the bytes are a function of the
/// terms alone. An interface hash or `same_proof` compares encodings made by
/// different processes, whose terms share differently in memory, and must
/// still see equal terms as equal bytes. Allocations are only a memo: a
/// shared child is numbered once per encoding, which keeps the walk linear
/// in the DAG. The memo holds each `Arc` it keys by, so an address is never
/// reused for another node while the encoding runs.
#[derive(Default)]
struct Share {
    /// Inside [`Writer::canonical_term`]: children are written as their
    /// canonical numbers, the key of the node being numbered.
    keying: bool,
    term_at: KeyMap<*const Term, (Rc<Term>, u32)>,
    type_at: KeyMap<*const Type, (Rc<Type>, u32)>,
    term_keys: KeyMap<Box<[u8]>, u32>,
    type_keys: KeyMap<Box<[u8]>, u32>,
    /// Emptied key buffers, so numbering a node allocates only for a key
    /// not seen before.
    spare: Vec<Vec<u8>>,
    /// By canonical number: the reader's index of the node once written.
    term_written: Vec<Option<u32>>,
    type_written: Vec<Option<u32>>,
    terms: u32,
    types: u32,
}

/// The writer's own allocations and its own shallow encodings are the keys,
/// not input anyone chooses, so a multiply-mix replaces SipHash, which cost
/// more than the encoding it keys (as `heather_kernel::value::PtrHasher`).
#[derive(Default, Clone, Copy)]
struct KeyHasher(u64);

impl std::hash::Hasher for KeyHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            self.write_u64(u64::from_le_bytes(chunk.try_into().unwrap()));
        }
        let mut last = [0_u8; 8];
        last[..chunks.remainder().len()].copy_from_slice(chunks.remainder());
        self.write_u64(u64::from_le_bytes(last));
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0.rotate_left(5) ^ n).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64);
    }
}

type KeyMap<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<KeyHasher>>;

/// A position that holds a term (`T = Term`) or type: inline, or behind an
/// `Arc` the writer may memoise by allocation. The reader treats both alike.
trait Site<T> {
    fn node(&self) -> &T;
    fn shared(&self) -> Option<&Rc<T>>;
}

impl<T> Site<T> for T {
    fn node(&self) -> &T { self }
    fn shared(&self) -> Option<&Rc<T>> { None }
}

impl<T> Site<T> for Rc<T> {
    fn node(&self) -> &T { self }
    fn shared(&self) -> Option<&Rc<T>> { Some(self) }
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

    /// A numeral of any size: its limb count, then its little-endian limbs.
    fn numeral(&mut self, value: &Numeral) {
        self.len(value.limbs().len());
        for &limb in value.limbs() {
            self.u64(limb);
        }
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

    /// The canonical number of a term: its node written shallowly, children
    /// as their own numbers, looked up among the keys seen so far.
    fn canonical_term(&mut self, site: &(impl Site<Term> + ?Sized)) -> u32 {
        if let Some(rc) = site.shared() {
            if let Some((_, n)) = self.share.term_at.get(&Rc::as_ptr(rc)) {
                return *n;
            }
        }
        let key = self.key(|w| put_term_node(w, site.node()));
        let n = Self::number(&mut self.share.term_keys, &mut self.share.spare, key);
        if let Some(rc) = site.shared() {
            self.share.term_at.insert(Rc::as_ptr(rc), (rc.clone(), n));
        }
        n
    }

    /// [`Writer::canonical_term`] for a type.
    fn canonical_type(&mut self, site: &(impl Site<Type> + ?Sized)) -> u32 {
        if let Some(rc) = site.shared() {
            if let Some((_, n)) = self.share.type_at.get(&Rc::as_ptr(rc)) {
                return *n;
            }
        }
        let key = self.key(|w| put_type_node(w, site.node()));
        let n = Self::number(&mut self.share.type_keys, &mut self.share.spare, key);
        if let Some(rc) = site.shared() {
            self.share.type_at.insert(Rc::as_ptr(rc), (rc.clone(), n));
        }
        n
    }

    /// What `put` writes in keying mode, leaving the image and its node
    /// count as they were.
    fn key(&mut self, put: impl FnOnce(&mut Self)) -> Vec<u8> {
        let bytes = std::mem::replace(&mut self.bytes, self.share.spare.pop().unwrap_or_default());
        let (nodes, keying) = (self.nodes, std::mem::replace(&mut self.share.keying, true));
        put(self);
        self.nodes = nodes;
        self.share.keying = keying;
        std::mem::replace(&mut self.bytes, bytes)
    }

    /// The number of `key` among `keys`, a new one if it is new.
    fn number(keys: &mut KeyMap<Box<[u8]>, u32>, spare: &mut Vec<Vec<u8>>, mut key: Vec<u8>) -> u32 {
        let n = match keys.get(key.as_slice()) {
            Some(&n) => n,
            None => {
                let n = keys.len() as u32;
                keys.insert(key.as_slice().into(), n);
                n
            }
        };
        key.clear();
        spare.push(key);
        n
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
    /// (`docs/infrastructure/declaration-slice-replay-design.md` §4). Zero for an image.
    span_offset: i64,
    /// Every term and type decoded so far, in the order their nodes ended:
    /// what a [`tag::SHARED`] reference indexes ([`Share`]).
    terms: Vec<Rc<Term>>,
    types: Vec<Rc<Type>>,
    /// The lowest stack address a node was decoded at, for the frame-cost
    /// tests.
    #[cfg(test)]
    low_water: usize,
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
            terms: Vec::new(),
            types: Vec::new(),
            #[cfg(test)]
            low_water: usize::MAX,
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

    fn numeral(&mut self) -> Result<Numeral, ModuleImageDecodeError> {
        let len = self.len()?;
        let mut limbs = Vec::with_capacity(len);
        for _ in 0..len {
            limbs.push(self.u64()?);
        }
        Ok(Numeral::from_limbs(limbs))
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
        #[cfg(test)]
        {
            let here = 0_u8;
            self.low_water = self.low_water.min(std::hint::black_box(&here) as *const u8 as usize);
        }
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

    /// The index after a [`tag::SHARED`] byte, if that is what comes next,
    /// charged as one node like the reference the writer counted.
    fn shared(&mut self) -> Result<Option<usize>, ModuleImageDecodeError> {
        if self.bytes.get(self.at) != Some(&tag::SHARED) {
            return Ok(None);
        }
        self.node(|r| {
            r.at += 1;
            Ok(Some(r.u32()? as usize))
        })
    }
}

mod tag {
    // 0–3 were the tree spelling before levels were canonical.
    pub const LEVEL_OMEGA: u8 = 4;
    pub const LEVEL_NF: u8 = 5;

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

    /// In a term's or type's place: a node written earlier ([`super::Share`]).
    pub const SHARED: u8 = 0xff;
}

/// A level as its canonical parts: `ω`, or the optional constant and the
/// `(ℓ, n)` terms. Decoding rebuilds through [`Level::of_parts`], so no image
/// can produce a non-canonical level.
fn put_level(w: &mut Writer, level: &Level) {
    w.nodes += 1;
    let Some((konst, vars)) = level.parts() else { return w.byte(tag::LEVEL_OMEGA) };
    w.byte(tag::LEVEL_NF);
    match konst {
        Some(k) => {
            w.byte(1);
            w.u64(k);
        }
        None => w.byte(0),
    }
    w.len(vars.len());
    for (var, n) in vars {
        w.u32(var.0);
        w.u64(n);
    }
}

fn get_level(r: &mut Reader<'_>) -> Result<Level, ModuleImageDecodeError> {
    r.node(|r| match r.byte()? {
        tag::LEVEL_NF => {
            let konst = match r.byte()? {
                0 => None,
                1 => Some(r.u64()?),
                tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "level constant", tag }),
            };
            let len = r.len()?;
            let mut vars = Vec::with_capacity(len);
            for _ in 0..len {
                vars.push((UnivVar(r.u32()?), r.u64()?));
            }
            Ok(Level::of_parts(konst, vars))
        }
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
            w.u32(var.key());
        }
    }
}

fn get_base(r: &mut Reader<'_>) -> Result<CtxBase, ModuleImageDecodeError> {
    match r.byte()? {
        tag::BASE_NIL => Ok(CtxBase::Nil),
        tag::BASE_VAR => Ok(CtxBase::Var(GlobalVar::from_key(r.u32()?))),
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
            ty: type_rc(r)?,
            level: get_level(r)?,
        })
    })?;
    Ok(LocalCtx::from_vec(base, entries))
}

fn put_subst(w: &mut Writer, subst: &LocalSubst) {
    match subst.tail {
        SubstTail::Empty => w.byte(tag::TAIL_EMPTY),
        SubstTail::Wk { len, ctx_var } => {
            w.byte(tag::TAIL_WK);
            w.u32(len);
            w.u32(ctx_var.key());
        }
    }
    w.vec(&subst.terms, |w, term| put_term(w, term));
}

fn get_subst(r: &mut Reader<'_>) -> Result<LocalSubst, ModuleImageDecodeError> {
    let tail = match r.byte()? {
        tag::TAIL_EMPTY => SubstTail::Empty,
        tag::TAIL_WK => SubstTail::Wk {
            len: r.u32()?,
            ctx_var: GlobalVar::from_key(r.u32()?),
        },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "substitution tail", tag }),
    };
    let terms = r.vec(|r| Ok(term_rc(r)?))?;
    Ok(LocalSubst { tail, terms })
}

// Kernel node codecs follow below. They use a tag namespace per sort: the
// caller always knows which sort it is decoding, so tags stay compact while
// every exhaustive match remains a compile-time schema tripwire.

fn put_type(w: &mut Writer, site: &(impl Site<Type> + ?Sized)) {
    let n = w.canonical_type(site);
    if w.share.keying {
        return w.u32(n);
    }
    if let Some(&Some(at)) = w.share.type_written.get(n as usize) {
        w.nodes += 1;
        w.byte(tag::SHARED);
        return w.u32(at);
    }
    put_type_node(w, site.node());
    if w.share.type_written.len() <= n as usize {
        w.share.type_written.resize(n as usize + 1, None);
    }
    w.share.type_written[n as usize] = Some(w.share.types);
    w.share.types += 1;
}

fn put_type_node(w: &mut Writer, ty: &Type) {
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
        Type::GlobalTy { var, subst } => { w.byte(17); w.u32(var.key()); put_subst(w, subst); }
        Type::DVec { level, len, fam } => {
            w.byte(22); put_level(w, level); put_term(w, len); put_type(w, fam);
        }
        Type::IWf { sig, index } => {
            let IWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
            w.byte(23); put_level(w, level); put_level(w, idx_level); put_type(w, idx); put_type(w, shape); put_term(w, arity); put_term(w, out); put_term(w, child); put_term(w, index);
        }
        Type::M { sig, index } => { w.byte(24); put_m_sig(w, sig); put_term(w, index); }
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

// A term's or type's children are decoded out of line. Inlined into
// `get_term`'s match, every arm's decoded fields got stack of their own, and
// a level of term nesting cost 16 KiB (`DECODE_FRAME_BYTES`).
#[inline(never)]
fn term_rc(r: &mut Reader<'_>) -> Result<Rc<Term>, ModuleImageDecodeError> {
    if let Some(at) = r.shared()? {
        return r.terms.get(at).cloned().ok_or(ModuleImageDecodeError::InvalidStructure("shared term index"));
    }
    let term = Rc::new(get_term_node(r)?);
    r.terms.push(term.clone());
    Ok(term)
}

/// A term in an inline position: a shared one is cloned out of its `Arc`,
/// which copies one node.
#[inline(never)]
fn get_term(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    Ok(Rc::unwrap_or_clone(term_rc(r)?))
}

/// An `IWf` signature, in the order tags 23 and 63 write it. Out of line
/// for the reason `term_rc` is.
#[inline(never)]
fn get_iwf_sig(r: &mut Reader<'_>) -> Result<Rc<IWfSig>, ModuleImageDecodeError> {
    let (level, idx_level) = (get_level(r)?, get_level(r)?);
    let (idx, shape) = (type_rc(r)?, type_rc(r)?);
    let (arity, out, child) = (term_rc(r)?, term_rc(r)?, term_rc(r)?);
    Ok(Rc::new(IWfSig { level, idx_level, idx, shape, arity, out, child }))
}

/// Tag 64's fields: the three levels first, `motive_level` among them, as
/// `put_term` writes them (the layout predates the shared signature). Out
/// of line for the reason `term_rc` is.
#[inline(never)]
fn get_elim_iwf(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    let (level, idx_level, motive_level) = (get_level(r)?, get_level(r)?, get_level(r)?);
    let (idx, shape) = (type_rc(r)?, type_rc(r)?);
    let (arity, out, child) = (term_rc(r)?, term_rc(r)?, term_rc(r)?);
    Ok(Term::ElimIWf {
        sig: Rc::new(IWfSig { level, idx_level, idx, shape, arity, out, child }),
        motive_level,
        motive: type_rc(r)?,
        step: term_rc(r)?,
        index: term_rc(r)?,
        scrut: term_rc(r)?,
    })
}

/// An `M` signature, as tags 24, 65 and 66 write it: the three levels,
/// then the components.
fn put_m_sig(w: &mut Writer, sig: &MSig) {
    let MSig { level, pos_level, idx_level, idx, shape, pos, next } = sig;
    put_level(w, level); put_level(w, pos_level); put_level(w, idx_level);
    put_type(w, idx); put_type(w, shape); put_type(w, pos); put_term(w, next);
}

/// [`put_m_sig`]'s reader. Out of line for the reason `term_rc` is.
#[inline(never)]
fn get_m_sig(r: &mut Reader<'_>) -> Result<Rc<MSig>, ModuleImageDecodeError> {
    let (level, pos_level, idx_level) = (get_level(r)?, get_level(r)?, get_level(r)?);
    let (idx, shape, pos) = (type_rc(r)?, type_rc(r)?, type_rc(r)?);
    Ok(Rc::new(MSig { level, pos_level, idx_level, idx, shape, pos, next: term_rc(r)? }))
}

/// Tag 67's fields. Out of line for the reason `term_rc` is.
#[inline(never)]
fn get_tm_m(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    let (level, pos_level, idx_level) = (get_level(r)?, get_level(r)?, get_level(r)?);
    Ok(Term::TmM {
        level,
        pos_level,
        idx_level,
        idx: term_rc(r)?,
        shape: term_rc(r)?,
        pos: term_rc(r)?,
        next: term_rc(r)?,
        index: term_rc(r)?,
    })
}

/// Tag 69's fields. Out of line for the reason `term_rc` is.
#[inline(never)]
fn get_tm_iwf(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    let (level, idx_level) = (get_level(r)?, get_level(r)?);
    Ok(Term::TmIWf {
        level,
        idx_level,
        idx: term_rc(r)?,
        shape: term_rc(r)?,
        arity: term_rc(r)?,
        out: term_rc(r)?,
        child: term_rc(r)?,
        index: term_rc(r)?,
    })
}

/// Tag 65's fields. Out of line for the reason `term_rc` is.
#[inline(never)]
fn get_corec(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    let sig = get_m_sig(r)?;
    let carrier_level = get_level(r)?;
    Ok(Term::Corec {
        sig,
        carrier_level,
        carrier: type_rc(r)?,
        step: term_rc(r)?,
        index: term_rc(r)?,
        seed: term_rc(r)?,
    })
}

#[inline(never)]
fn type_rc(r: &mut Reader<'_>) -> Result<Rc<Type>, ModuleImageDecodeError> {
    if let Some(at) = r.shared()? {
        return r.types.get(at).cloned().ok_or(ModuleImageDecodeError::InvalidStructure("shared type index"));
    }
    let ty = Rc::new(get_type_node(r)?);
    r.types.push(ty.clone());
    Ok(ty)
}

/// [`get_term`] for a type.
#[inline(never)]
fn get_type(r: &mut Reader<'_>) -> Result<Type, ModuleImageDecodeError> {
    Ok(Rc::unwrap_or_clone(type_rc(r)?))
}

fn get_type_node(r: &mut Reader<'_>) -> Result<Type, ModuleImageDecodeError> {
    r.node(|r| Ok(match r.byte()? {
        0 => Type::Nat,
        1 => Type::Pi { dom_level: get_level(r)?, cod_level: get_level(r)?, dom: type_rc(r)?, cod: type_rc(r)? },
        2 => Type::Ty(get_level(r)?),
        3 => Type::UPi { num_vars: r.u32()?, level: get_level(r)?, body: type_rc(r)? },
        4 => Type::El { level: get_level(r)?, tm: term_rc(r)? },
        5 => Type::Id { level: get_level(r)?, ty: type_rc(r)?, lhs: term_rc(r)?, rhs: term_rc(r)? },
        6 => Type::SEq { level: get_level(r)?, ty: type_rc(r)?, lhs: term_rc(r)?, rhs: term_rc(r)? },
        7 => Type::SEmpty { level: get_level(r)? },
        8 => Type::Squash { level: get_level(r)?, ty: type_rc(r)? },
        9 => Type::Sigma { fst_level: get_level(r)?, snd_level: get_level(r)?, fst: type_rc(r)?, snd: type_rc(r)? },
        10 => Type::Unit { level: get_level(r)? },
        11 => Type::Empty { level: get_level(r)? },
        12 => Type::Sum { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: type_rc(r)?, rhs: type_rc(r)? },
        13 => Type::W { shape_level: get_level(r)?, pos_level: get_level(r)?, shape: type_rc(r)?, pos: type_rc(r)? },
        14 => Type::Vec { level: get_level(r)?, elem: type_rc(r)?, len: term_rc(r)? },
        15 => Type::Fin { len: term_rc(r)? },
        16 => Type::Wf { level: get_level(r)?, shape: type_rc(r)?, arity: term_rc(r)? },
        17 => Type::GlobalTy { var: GlobalVar::from_key(r.u32()?), subst: get_subst(r)? },
        18 => Type::CtxPi { level: get_level(r)?, body: type_rc(r)? },
        19 => Type::TyPi { ctx: get_ctx(r)?, arg_level: get_level(r)?, body_level: get_level(r)?, body: type_rc(r)? },
        20 => Type::CodeTy { ctx: get_ctx(r)?, level: get_level(r)? },
        21 => Type::CodeTm { ctx: get_ctx(r)?, ty: type_rc(r)?, level: get_level(r)? },
        22 => Type::DVec { level: get_level(r)?, len: term_rc(r)?, fam: type_rc(r)? },
        23 => Type::IWf { sig: get_iwf_sig(r)?, index: term_rc(r)? },
        24 => Type::M { sig: get_m_sig(r)?, index: term_rc(r)? },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "type", tag }),
    }))
}

fn put_term(w: &mut Writer, site: &(impl Site<Term> + ?Sized)) {
    let n = w.canonical_term(site);
    if w.share.keying {
        return w.u32(n);
    }
    if let Some(&Some(at)) = w.share.term_written.get(n as usize) {
        w.nodes += 1;
        w.byte(tag::SHARED);
        return w.u32(at);
    }
    put_term_node(w, site.node());
    if w.share.term_written.len() <= n as usize {
        w.share.term_written.resize(n as usize + 1, None);
    }
    w.share.term_written[n as usize] = Some(w.share.terms);
    w.share.terms += 1;
}

fn put_term_node(w: &mut Writer, term: &Term) {
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
        Term::TmDVec { level, len, fam } => {
            w.byte(68); put_level(w, level); put_term(w, len); put_term(w, fam);
        }
        Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => {
            w.byte(69); put_level(w, level); put_level(w, idx_level); put_term(w, idx); put_term(w, shape); put_term(w, arity); put_term(w, out); put_term(w, child); put_term(w, index);
        }
        Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => {
            w.byte(67); put_level(w, level); put_level(w, pos_level); put_level(w, idx_level); put_term(w, idx); put_term(w, shape); put_term(w, pos); put_term(w, next); put_term(w, index);
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
        // 23 was `transp` (retired with it; docs/kernel/iwf-former-design.md §13).
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
        Term::Supi { sig, label, children } => {
            let IWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
            w.byte(63); put_level(w, level); put_level(w, idx_level); put_type(w, idx); put_type(w, shape); put_term(w, arity); put_term(w, out); put_term(w, child); put_term(w, label); put_term(w, children);
        }
        Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => {
            let IWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
            w.byte(64); put_level(w, level); put_level(w, idx_level); put_level(w, motive_level); put_type(w, idx); put_type(w, shape); put_term(w, arity); put_term(w, out); put_term(w, child); put_type(w, motive); put_term(w, step); put_term(w, index); put_term(w, scrut);
        }
        Term::Corec { sig, carrier_level, carrier, step, index, seed } => {
            w.byte(65); put_m_sig(w, sig); put_level(w, carrier_level); put_type(w, carrier); put_term(w, step); put_term(w, index); put_term(w, seed);
        }
        Term::Out { sig, index, scrut } => {
            w.byte(66); put_m_sig(w, sig); put_term(w, index); put_term(w, scrut);
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
        Term::GlobalTm { var, subst } => { w.byte(42); w.u32(var.key()); put_subst(w, subst); }
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
        Term::NatLit(n) => { w.byte(53); w.numeral(n); }
        // The checked spellings (docs/elaborator/intro-by-type-design.md). New tags, so
        // an older reader refuses the byte rather than mis-decoding it; the
        // image's `SemanticsIdentity` already changes with the kernel's
        // sources, so a stored image from before this change is a miss and
        // never reaches this reader at all.
        // The intros' annotation is optional (design §2.1) and gets its own
        // tag rather than a presence byte, so the unannotated spelling — the
        // one the emitters write almost everywhere — costs one byte and no
        // type at all.
        Term::PairAt { ty: Some(ty), fst, snd } => { w.byte(54); put_type(w, ty); put_term(w, fst); put_term(w, snd); }
        Term::InlAt { ty: Some(ty), val } => { w.byte(55); put_type(w, ty); put_term(w, val); }
        Term::InrAt { ty: Some(ty), val } => { w.byte(56); put_type(w, ty); put_term(w, val); }
        Term::FstAt { pair } => { w.byte(57); put_term(w, pair); }
        Term::SndAt { pair } => { w.byte(58); put_term(w, pair); }
        Term::PairAt { ty: None, fst, snd } => { w.byte(59); put_term(w, fst); put_term(w, snd); }
        Term::InlAt { ty: None, val } => { w.byte(60); put_term(w, val); }
        Term::InrAt { ty: None, val } => { w.byte(61); put_term(w, val); }
        Term::AppAt { fun, arg } => { w.byte(62); put_term(w, fun); put_term(w, arg); }
        // A packed vector literal (docs/kernel/bitvector-literal-entry-design.md
        // §3): its two elements and its word, never the chain it spells.
        Term::VecLit { level, elem, zero, one, width, bits } => {
            w.byte(70); put_level(w, level); put_type(w, elem); put_term(w, zero); put_term(w, one); w.u32(*width); w.u64(*bits);
        }
        // A vector-items node: its live elements, written from the start.
        Term::VecItems { level, elem, items, from } => {
            let live = items.get(*from as usize..).unwrap_or(&[]);
            w.byte(71); put_level(w, level); put_type(w, elem); w.len(live.len());
            for item in live {
                put_term(w, item);
            }
        }
    }
}

fn get_term_node(r: &mut Reader<'_>) -> Result<Term, ModuleImageDecodeError> {
    r.node(|r| Ok(match r.byte()? {
        0 => Term::Var(LocalVar(r.u32()?)),
        1 => Term::TmNat,
        2 => Term::TmPi { dom_level: get_level(r)?, cod_level: get_level(r)?, dom: term_rc(r)?, cod: term_rc(r)? },
        3 => Term::TmTy(get_level(r)?),
        4 => Term::TmId { level: get_level(r)?, ty: term_rc(r)?, lhs: term_rc(r)?, rhs: term_rc(r)? },
        5 => Term::TmSEq { level: get_level(r)?, ty: term_rc(r)?, lhs: term_rc(r)?, rhs: term_rc(r)? },
        6 => Term::TmSEmpty { level: get_level(r)? },
        7 => Term::TmSquash { level: get_level(r)?, ty: term_rc(r)? },
        8 => Term::TmSigma { fst_level: get_level(r)?, snd_level: get_level(r)?, fst: term_rc(r)?, snd: term_rc(r)? },
        9 => Term::TmUnit { level: get_level(r)? },
        10 => Term::TmEmpty { level: get_level(r)? },
        11 => Term::TmSum { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: term_rc(r)?, rhs: term_rc(r)? },
        12 => Term::TmW { shape_level: get_level(r)?, pos_level: get_level(r)?, shape: term_rc(r)?, pos: term_rc(r)? },
        13 => Term::TmVec { level: get_level(r)?, elem: term_rc(r)?, len: term_rc(r)? },
        14 => Term::TmFin { len: term_rc(r)? },
        15 => Term::TmWf { level: get_level(r)?, shape: term_rc(r)?, arity: term_rc(r)? },
        16 => Term::Zero,
        17 => Term::Succ(term_rc(r)?),
        18 => Term::ElimNat { level: get_level(r)?, motive: type_rc(r)?, base: term_rc(r)?, step: term_rc(r)?, scrut: term_rc(r)? },
        19 => Term::Refl { level: get_level(r)?, ty: type_rc(r)?, tm: term_rc(r)? },
        20 => Term::J { ty_level: get_level(r)?, motive_level: get_level(r)?, ty: type_rc(r)?, lhs: term_rc(r)?, motive: type_rc(r)?, case: term_rc(r)?, rhs: term_rc(r)?, proof: term_rc(r)? },
        21 => Term::SRefl { level: get_level(r)?, ty: type_rc(r)?, tm: term_rc(r)? },
        22 => Term::Squash { level: get_level(r)?, ty: type_rc(r)?, tm: term_rc(r)? },
        24 => Term::ElimSEmpty { level: get_level(r)?, scrut_level: get_level(r)?, motive: type_rc(r)?, scrut: term_rc(r)? },
        25 => Term::ElimSquash { src_level: get_level(r)?, dst_level: get_level(r)?, src_ty: type_rc(r)?, motive: type_rc(r)?, case: term_rc(r)?, scrut: term_rc(r)? },
        26 => Term::Pair { fst_level: get_level(r)?, snd_level: get_level(r)?, fst_ty: type_rc(r)?, snd_ty: type_rc(r)?, fst: term_rc(r)?, snd: term_rc(r)? },
        27 => Term::Fst { fst_level: get_level(r)?, snd_level: get_level(r)?, fst_ty: type_rc(r)?, snd_ty: type_rc(r)?, pair: term_rc(r)? },
        28 => Term::Snd { fst_level: get_level(r)?, snd_level: get_level(r)?, fst_ty: type_rc(r)?, snd_ty: type_rc(r)?, pair: term_rc(r)? },
        29 => Term::Triv { level: get_level(r)? },
        30 => Term::ElimEmpty { level: get_level(r)?, scrut_level: get_level(r)?, motive: type_rc(r)?, scrut: term_rc(r)? },
        31 => Term::Inl { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: type_rc(r)?, rhs: type_rc(r)?, val: term_rc(r)? },
        32 => Term::Inr { lhs_level: get_level(r)?, rhs_level: get_level(r)?, lhs: type_rc(r)?, rhs: type_rc(r)?, val: term_rc(r)? },
        33 => Term::Case { lhs_level: get_level(r)?, rhs_level: get_level(r)?, motive_level: get_level(r)?, lhs: type_rc(r)?, rhs: type_rc(r)?, motive: type_rc(r)?, case_l: term_rc(r)?, case_r: term_rc(r)?, scrut: term_rc(r)? },
        34 => Term::Sup { shape_level: get_level(r)?, pos_level: get_level(r)?, shape_ty: type_rc(r)?, pos_ty: type_rc(r)?, label: term_rc(r)?, children: term_rc(r)? },
        35 => Term::ElimW { shape_level: get_level(r)?, pos_level: get_level(r)?, motive_level: get_level(r)?, shape: type_rc(r)?, pos: type_rc(r)?, motive: type_rc(r)?, step: term_rc(r)?, scrut: term_rc(r)? },
        36 => Term::Supf { level: get_level(r)?, shape: type_rc(r)?, arity: term_rc(r)?, label: term_rc(r)?, children: term_rc(r)? },
        37 => Term::ElimWf { level: get_level(r)?, motive_level: get_level(r)?, shape: type_rc(r)?, arity: term_rc(r)?, motive: type_rc(r)?, step: term_rc(r)?, scrut: term_rc(r)? },
        38 => Term::Lam { dom_level: get_level(r)?, cod_level: get_level(r)?, dom: type_rc(r)?, body: term_rc(r)? },
        39 => Term::App { fun: term_rc(r)?, dom_level: get_level(r)?, cod_level: get_level(r)?, dom: type_rc(r)?, cod: type_rc(r)?, arg: term_rc(r)? },
        40 => Term::ULam { num_vars: r.u32()?, level: get_level(r)?, body: term_rc(r)? },
        41 => Term::UApp { fun: term_rc(r)?, levels: r.vec(get_level)? },
        42 => Term::GlobalTm { var: GlobalVar::from_key(r.u32()?), subst: get_subst(r)? },
        43 => Term::CtxLam { level: get_level(r)?, body: term_rc(r)? },
        44 => Term::CtxApp { fun: term_rc(r)?, ctx: get_ctx(r)? },
        45 => Term::TyLam { ctx: get_ctx(r)?, arg_level: get_level(r)?, body_level: get_level(r)?, body: term_rc(r)? },
        46 => Term::TyApp { fun: term_rc(r)?, arg: type_rc(r)? },
        47 => Term::BoxTy(type_rc(r)?),
        48 => Term::BoxTm(term_rc(r)?),
        49 => Term::LetBoxTy { motive_level: get_level(r)?, code_level: get_level(r)?, ctx: get_ctx(r)?, motive: type_rc(r)?, body: term_rc(r)?, scrut: term_rc(r)? },
        50 => Term::LetBoxTm { motive_level: get_level(r)?, code_level: get_level(r)?, ctx: get_ctx(r)?, ty: type_rc(r)?, motive: type_rc(r)?, body: term_rc(r)?, scrut: term_rc(r)? },
        51 => Term::ElimCodeTy { ty_motive_level: get_level(r)?, tm_motive_level: get_level(r)?, motives: Rc::new(get_motives(r)?), branches: Rc::new(get_branches(r)?), code_level: get_level(r)?, ctx: get_ctx(r)?, scrut: term_rc(r)? },
        52 => Term::ElimCodeTm { ty_motive_level: get_level(r)?, tm_motive_level: get_level(r)?, motives: Rc::new(get_motives(r)?), branches: Rc::new(get_branches(r)?), code_level: get_level(r)?, ctx: get_ctx(r)?, ty: type_rc(r)?, scrut: term_rc(r)? },
        53 => Term::NatLit(r.numeral()?),
        54 => Term::PairAt { ty: Some(type_rc(r)?), fst: term_rc(r)?, snd: term_rc(r)? },
        55 => Term::InlAt { ty: Some(type_rc(r)?), val: term_rc(r)? },
        56 => Term::InrAt { ty: Some(type_rc(r)?), val: term_rc(r)? },
        57 => Term::FstAt { pair: term_rc(r)? },
        58 => Term::SndAt { pair: term_rc(r)? },
        59 => Term::PairAt { ty: None, fst: term_rc(r)?, snd: term_rc(r)? },
        60 => Term::InlAt { ty: None, val: term_rc(r)? },
        61 => Term::InrAt { ty: None, val: term_rc(r)? },
        62 => Term::AppAt { fun: term_rc(r)?, arg: term_rc(r)? },
        63 => Term::Supi { sig: get_iwf_sig(r)?, label: term_rc(r)?, children: term_rc(r)? },
        64 => get_elim_iwf(r)?,
        65 => get_corec(r)?,
        66 => Term::Out { sig: get_m_sig(r)?, index: term_rc(r)?, scrut: term_rc(r)? },
        67 => get_tm_m(r)?,
        68 => Term::TmDVec { level: get_level(r)?, len: term_rc(r)?, fam: term_rc(r)? },
        69 => get_tm_iwf(r)?,
        70 => {
            let (level, elem, zero, one) = (get_level(r)?, type_rc(r)?, term_rc(r)?, term_rc(r)?);
            let (width, bits) = (r.u32()?, r.u64()?);
            Term::VecLit { level, elem, zero, one, width, bits }
        }
        71 => {
            let (level, elem) = (get_level(r)?, type_rc(r)?);
            let n = r.len()?;
            let items = (0..n).map(|_| term_rc(r)).collect::<Result<Vec<_>, _>>()?;
            if items.is_empty() {
                return Err(ModuleImageDecodeError::InvalidTag { sort: "term", tag: 71 });
            }
            Term::VecItems { level, elem, items: items.into(), from: 0 }
        }
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "term", tag }),
    }))
}

fn put_motives(w: &mut Writer, motives: &Motives) {
    put_type(w, &motives.ty_motive);
    put_type(w, &motives.tm_motive);
}

fn get_motives(r: &mut Reader<'_>) -> Result<Motives, ModuleImageDecodeError> {
    Ok(Motives {
        ty_motive: type_rc(r)?,
        tm_motive: type_rc(r)?,
    })
}

fn branch_terms(branches: &Branches) -> [&Rc<Term>; 65] {
    let Branches {
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
    } = branches;
    [
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
    ]
}

fn put_branches(w: &mut Writer, branches: &Branches) {
    for term in branch_terms(branches) {
        put_term(w, term);
    }
}

fn get_branches(r: &mut Reader<'_>) -> Result<Branches, ModuleImageDecodeError> {
    let mut terms = Vec::with_capacity(65);
    for _ in 0..65 {
        terms.push(term_rc(r)?);
    }
    let [
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
    ]: [Rc<Term>; 65] = terms.try_into().unwrap();
    Ok(Branches {
        ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty,
        tm_var, tm_nat, tm_pi, tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app,
        tm_id, tm_refl, tm_j, tm_sigma, tm_pair, tm_fst, tm_snd, tm_unit, tm_empty,
        tm_triv, tm_elim_empty, ty_sum, tm_sum, tm_inl, tm_inr, tm_case, ty_w, tm_w,
        tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin, ty_wf, tm_wf, tm_supf,
        tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl,
        tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash,
        ty_m, tm_m, tm_corec, tm_out,
        ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
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
            ty: type_rc(r)?,
            level: get_level(r)?,
            body: r.option(|r| Ok(term_rc(r)?))?,
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
    w.byte(match fixity { OpFixity::Prefix => 0, OpFixity::Infix => 1, OpFixity::Postfix => 2 });
}

fn get_fixity(r: &mut Reader<'_>) -> Result<OpFixity, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(OpFixity::Prefix),
        1 => Ok(OpFixity::Infix),
        2 => Ok(OpFixity::Postfix),
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
        TyKind::TypeOf(expr) => { w.byte(13); put_expr(w, expr); }
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
            13 => TyKind::TypeOf(Box::new(get_expr(r)?)),
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
        ExprKind::Num(value) => { w.byte(3); w.numeral(value); }
        ExprKind::SuffixedNum { value, suffix } => { w.byte(27); w.numeral(value); w.string(suffix); }
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
        ExprKind::Ascribe { expr, ty } => { w.byte(28); put_expr(w, expr); put_ty(w, ty); }
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
        ExprKind::Dot { recv, name, tyargs, args, named } => {
            w.byte(16); put_expr(w, recv); w.string(name);
            w.vec(tyargs, put_ty);
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
        ExprKind::Char(c) => { w.byte(23); w.u64(u64::from(u32::from(*c))); }
        ExprKind::Str(text) => { w.byte(24); w.string(text); }
        ExprKind::RecordUpdate { base, fields } => {
            w.byte(25); put_expr(w, base);
            w.vec(fields, |w, field| {
                w.string(&field.name); put_expr(w, &field.expr); put_span(w, field.span);
            });
        }
        ExprKind::Scaled(lit) => {
            w.byte(26); w.numeral(&lit.mant); w.u64(lit.exp as u64); w.bool(lit.hex);
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
            3 => ExprKind::Num(r.numeral()?),
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
                tyargs: r.vec(get_ty)?,
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
            // A character payload is a scalar value by construction: the
            // lexer refuses anything else, so a code that is not one means a
            // corrupt image rather than a widened surface.
            23 => ExprKind::Char(
                u32::try_from(r.u64()?)
                    .ok()
                    .and_then(char::from_u32)
                    .ok_or(ModuleImageDecodeError::InvalidTag { sort: "character literal", tag: 23 })?,
            ),
            24 => ExprKind::Str(r.string()?),
            25 => ExprKind::RecordUpdate {
                base: Box::new(get_expr(r)?), fields: r.vec(|r| Ok(RecordLitField {
                    name: r.string()?, expr: get_expr(r)?, span: get_span(r)?,
                }))?,
            },
            27 => ExprKind::SuffixedNum { value: r.numeral()?, suffix: r.string()? },
            28 => ExprKind::Ascribe { expr: Box::new(get_expr(r)?), ty: Box::new(get_ty(r)?) },
            26 => ExprKind::Scaled(heather_syntax::ScaledLit { mant: r.numeral()?, exp: r.u64()? as i64, hex: r.bool()? }),
            tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "expression", tag }),
        };
        Ok(Expr { kind, span })
    })
}

fn put_stmt(w: &mut Writer, stmt: &Stmt) {
    match stmt {
        // A `have` is its own tag (docs/language/have-design.md §5) rather than a
        // flag byte, so an image written before `have` existed still reads.
        Stmt::Let { name, ty, expr, span, opaque } => {
            w.byte(if *opaque { 3 } else { 0 }); w.string(name); w.option(ty.as_ref(), put_ty); put_expr(w, expr); put_span(w, *span);
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
        tag @ (0 | 3) => Ok(Stmt::Let {
            name: r.string()?, ty: r.option(get_ty)?, expr: get_expr(r)?, span: get_span(r)?,
            opaque: tag == 3,
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
    w.option(param.default.as_deref(), put_expr);
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
    let default = r.option(|r| Ok(Box::new(get_expr(r)?)))?;
    let origin = match r.byte()? {
        0 => ParamOrigin::Written, 1 => ParamOrigin::InlineConstraint, 2 => ParamOrigin::Assuming,
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "parameter origin", tag }),
    };
    Ok(Param {
        name, ty, implicit, is_self, solver, default, origin,
        symbol: r.option(Reader::string)?, span: get_span(r)?,
    })
}

fn put_decl(w: &mut Writer, decl: &Decl) {
    // A `def` is a `Fn` with the value flag, tagged 3: an image written
    // before `def` existed never holds the tag, so it still decodes.
    w.byte(match decl.kind {
        DeclKind::Fn if decl.value => 3,
        DeclKind::Fn => 0,
        DeclKind::Theorem => 1,
        DeclKind::Axiom => 2,
    });
    w.bool(decl.is_meta);
    w.bool(decl.is_evidence);
    w.bool(decl.is_interface);
    w.option(decl.elaborates.as_ref(), |w, slot| {
        w.string(&slot.family); w.string(&slot.name); put_span(w, slot.span);
    });
    w.string(&decl.name);
    w.vec(&decl.tyvars, |w, var| { w.string(&var.name); w.u64(var.level); put_span(w, var.span); });
    w.vec(&decl.params, put_param); put_ty(w, &decl.result);
    w.option(decl.decreases.as_ref(), put_expr);
    w.vec(&decl.unfolding, |w, name| w.string(name));
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
    let (kind, value) = match r.byte()? {
        0 => (DeclKind::Fn, false), 1 => (DeclKind::Theorem, false), 2 => (DeclKind::Axiom, false),
        3 => (DeclKind::Fn, true),
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "declaration kind", tag }),
    };
    Ok(Decl {
        kind, value, is_meta: r.bool()?, is_evidence: r.bool()?, is_interface: r.bool()?, partial: None, elaborates: r.option(|r| Ok(SlotPath {
            family: r.string()?, name: r.string()?, span: get_span(r)?,
        }))?, name: r.string()?, tyvars: r.vec(|r| Ok(TyParam {
            name: r.string()?, level: r.u64()?, span: get_span(r)?,
        }))?, params: r.vec(get_param)?, result: get_ty(r)?, decreases: r.option(get_expr)?, unfolding: r.vec(Reader::string)?,
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
    w.option(param.default.as_deref(), |w, default| {
        put_expr(w, &default.expr); put_scope(w, &default.scope);
        w.string(&default.owner); w.usize(default.index);
    });
}

fn get_param_meta(r: &mut Reader<'_>) -> Result<ParamMeta, ModuleImageDecodeError> {
    Ok(ParamMeta {
        name: r.string()?, implicit: r.bool()?, is_type: r.bool()?, is_self: r.bool()?,
        skel: r.option(|r| Ok(Rc::new(get_skel(r)?)))?,
        solver: r.option(|r| Ok(Rc::new(get_ty(r)?)))?,
        default: r.option(|r| Ok(Rc::new(ParamDefault {
            expr: get_expr(r)?, scope: Rc::new(get_scope(r)?),
            owner: r.string()?, index: r.usize()?,
        })))?,
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
        // 0–2 and 4 were route 2b's `μ`, index devices and skeleton code.
        GenDef::IdxCode(tag) => { w.byte(3); w.u32(tag); }
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
        GenDef::WCanon(tag) => { w.byte(15); w.u32(tag); }
        GenDef::MShape(tag) => { w.byte(16); w.u32(tag); }
        GenDef::MPos(tag) => { w.byte(17); w.u32(tag); }
        GenDef::MNext(tag) => { w.byte(18); w.u32(tag); }
        GenDef::IArity(tag) => { w.byte(19); w.u32(tag); }
        GenDef::IOut(tag) => { w.byte(20); w.u32(tag); }
        GenDef::IChild(tag) => { w.byte(21); w.u32(tag); }
        GenDef::IDnth(tag) => { w.byte(22); w.u32(tag); }
    }
}

fn get_gen_def(r: &mut Reader<'_>) -> Result<GenDef, ModuleImageDecodeError> {
    Ok(match r.byte()? {
        3 => GenDef::IdxCode(r.u32()?),
        5 => GenDef::TyCode(r.u32()?), 6 => GenDef::ShapeCode(r.u32()?),
        7 => GenDef::ArityFn(r.u32()?), 8 => GenDef::Fam(r.u32()?),
        9 => GenDef::RecProj(r.u32()?, r.usize()?),
        10 => GenDef::RecTail(r.u32()?, r.usize()?),
        11 => GenDef::RecFam(r.u32()?, r.usize()?),
        12 => GenDef::PayloadCode(r.u32()?, r.usize()?),
        13 => GenDef::SuffixCode(r.u32()?, r.usize()?),
        14 => GenDef::TyCodeFn(r.u32()?), 15 => GenDef::WCanon(r.u32()?),
        16 => GenDef::MShape(r.u32()?), 17 => GenDef::MPos(r.u32()?), 18 => GenDef::MNext(r.u32()?),
        19 => GenDef::IArity(r.u32()?), 20 => GenDef::IOut(r.u32()?), 21 => GenDef::IChild(r.u32()?),
        22 => GenDef::IDnth(r.u32()?),
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "generated definition", tag }),
    })
}

fn put_field_kind(w: &mut Writer, kind: FieldKind) {
    match kind {
        FieldKind::Payload => w.byte(0), FieldKind::Plain => w.byte(1),
        FieldKind::Container { len_payload } => { w.byte(2); w.usize(len_payload); }
        FieldKind::IndexVar => w.byte(3),
        FieldKind::FnChild => w.byte(4),
    }
}

fn get_field_kind(r: &mut Reader<'_>) -> Result<FieldKind, ModuleImageDecodeError> {
    match r.byte()? {
        0 => Ok(FieldKind::Payload), 1 => Ok(FieldKind::Plain),
        2 => Ok(FieldKind::Container { len_payload: r.usize()? }),
        3 => Ok(FieldKind::IndexVar),
        4 => Ok(FieldKind::FnChild),
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
    w.vec(&ctor.defaults, |w, default| w.option(default.as_ref(), put_expr));
    w.vec(&ctor.child_index, |w, at| w.option(at.as_ref(), |w, es| w.vec(es, put_expr)));
}

fn get_ctor(r: &mut Reader<'_>) -> Result<Ctor, ModuleImageDecodeError> {
    Ok(Ctor {
        name: r.string()?,
        fields: r.vec(|r| Ok((r.option(Reader::string)?, get_ty(r)?)))?,
        kind: r.vec(get_field_kind)?,
        res: r.option(|r| Ok(IdxPat { ctor: r.usize()?, vars: r.vec(Reader::usize)? }))?,
        rec_at: r.vec(|r| r.option(Reader::usize))?,
        res_expr: r.option(get_expr)?,
        defaults: r.vec(|r| r.option(get_expr))?,
        child_index: r.vec(|r| r.option(|r| r.vec(get_expr)))?,
    })
}

fn put_inductive(w: &mut Writer, info: &Inductive) {
    w.nodes += 1;
    w.string(&info.name); put_scope(w, &info.scope); w.u32(info.tag);
    w.vec(&info.params, |w, name| w.string(name));
    w.option(info.varies.as_ref(), |w, k| w.u32(*k as u32));
    w.vec(&info.valparams, |w, (name, ty)| { w.string(name); put_ty(w, ty); });
    w.vec(&info.valparam_defaults, |w, d| w.option(d.as_deref(), put_expr));
    w.vec(&info.op_symbols, |w, (symbol, name)| { w.string(symbol); w.string(name); });
    w.vec(&info.ctors, put_ctor); w.bool(info.recursive); w.bool(info.is_record); w.bool(info.codata);
    w.option(info.index.as_ref(), |w, index| w.string(index));
    w.option(info.index_ty.as_ref(), |w, ty| match ty {
        IdxTy::Nat => w.byte(0),
        IdxTy::Decl(info) => { w.byte(1); put_inductive(w, info); }
        IdxTy::Open { ty, name } => { w.byte(2); put_ty(w, ty); w.string(name); }
    });
    w.option(info.skel.as_deref(), put_inductive);
    w.vec(&info.co_index, |w, (name, ty)| { w.string(name); put_ty(w, ty); });
    w.vec(&info.members, |w, m| {
        w.string(&m.name);
        w.option(m.index.as_ref(), |w, index| w.string(index));
        w.vec(&m.ctors, |w, k| w.u32(*k as u32));
    });
}

fn get_inductive(r: &mut Reader<'_>) -> Result<Inductive, ModuleImageDecodeError> {
    r.node(|r| Ok(Inductive {
        name: r.string()?, scope: Rc::new(get_scope(r)?), tag: r.u32()?,
        params: r.vec(Reader::string)?,
        varies: r.option(|r| Ok(r.u32()? as usize))?,
        valparams: r.vec(|r| Ok((r.string()?, get_ty(r)?)))?,
        valparam_defaults: r.vec(|r| r.option(|r| Ok(Rc::new(get_expr(r)?))))?,
        op_symbols: r.vec(|r| Ok((r.string()?, r.string()?)))?,
        ctors: r.vec(get_ctor)?, recursive: r.bool()?, is_record: r.bool()?, codata: r.bool()?,
        index: r.option(Reader::string)?,
        index_ty: r.option(|r| match r.byte()? {
            0 => Ok(IdxTy::Nat), 1 => Ok(IdxTy::Decl(Rc::new(get_inductive(r)?))),
            2 => Ok(IdxTy::Open { ty: get_ty(r)?, name: r.string()? }),
            tag => Err(ModuleImageDecodeError::InvalidTag { sort: "index type", tag }),
        })?,
        skel: r.option(|r| Ok(Rc::new(get_inductive(r)?)))?,
        co_index: r.vec(|r| Ok((r.string()?, get_ty(r)?)))?,
        members: r.vec(|r| Ok(Member {
            name: r.string()?,
            index: r.option(Reader::string)?,
            ctors: r.vec(|r| Ok(r.u32()? as usize))?,
        }))?,
    }))
}

fn put_field_decl(w: &mut Writer, field: &FieldDecl) {
    w.option(field.name.as_ref(), |w, name| w.string(name)); put_ty(w, &field.ty);
    w.option(field.default.as_deref(), put_expr); put_span(w, field.span);
}

fn get_field_decl(r: &mut Reader<'_>) -> Result<FieldDecl, ModuleImageDecodeError> {
    Ok(FieldDecl { name: r.option(Reader::string)?, ty: get_ty(r)?, default: r.option(get_expr)?.map(Box::new), span: get_span(r)? })
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
    w.string(&info.name); w.vec(&info.params, |w, s| w.string(s));
    w.vec(&info.kinds, |w, k| w.option(k.as_ref(), put_ty)); w.vec(&info.valparams, put_param);
    w.vec(&info.fields, put_field_decl); w.vec(&info.ancestors, put_class_ref);
    w.vec(&info.owner, |w, owner| w.option(owner.as_ref(), |w, s| w.string(s)));
}

fn get_class(r: &mut Reader<'_>) -> Result<ClassInfo, ModuleImageDecodeError> {
    Ok(ClassInfo {
        name: r.string()?, params: r.vec(Reader::string)?, kinds: r.vec(|r| r.option(get_ty))?,
        valparams: r.vec(get_param)?,
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
        term: term_rc(r)?, stmt: type_rc(r)?, psi_len: r.u32()?,
        order: r.vec(Reader::usize)?,
    })
}

/// The deterministic encoding of a run of events, for comparing two runs
/// structurally (`ModuleDelta` slices: `docs/infrastructure/declaration-slice-replay-design.md`
/// §4). With `interface`, the projection a dependent observes — spans
/// zeroed, theorem proofs and proof dependency edges dropped — which is what
/// "the same contribution" means for the declarations after it.
pub(crate) fn encode_events(events: &[DeltaEvent], interface: bool) -> Vec<u8> {
    let mut w = Writer { interface, ..Writer::default() };
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
    let limits = ModuleImageLimits::default();
    decode_on_own_stack(&limits, || {
        let mut r = Reader::new(&bytes, limits)?;
        r.span_offset = offset;
        let events = r.vec(get_event)?;
        r.finish()?;
        Ok(events)
    })
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
        DeltaEvent::GenTyCode { tag, inline, level, at } => {
            w.byte(3); w.u32(*tag); put_type(w, inline); put_level(w, level); w.u32(*at);
        }
        DeltaEvent::GenWfSlots { tag, slots, at } => {
            w.byte(4); w.u32(*tag); put_type(w, &slots.shape); put_type(w, &slots.shape_decoded);
            put_term(w, &slots.arity); put_level(w, &slots.level); w.u32(*at);
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
        DeltaEvent::Evidence(rule) => {
            w.byte(18); w.string(&rule.global); w.string(&rule.relation);
            w.vec(&rule.heads, |w, head| w.option(head.as_ref(), |w, head| w.string(head)));
        }
        DeltaEvent::Registered { ty, global } => { w.byte(20); w.string(ty); w.string(global); }
        DeltaEvent::Interface { key, info } => {
            w.byte(19); w.string(key); w.string(&info.module); w.u32(info.arity); w.string(&info.name);
            w.vec(&info.equations, |w, eq| w.string(eq));
        }
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
        DeltaEvent::GenTyCodeFn { tag, entry, at } => {
            w.byte(17); w.u32(*tag); put_type(w, &entry.template); put_type(w, &entry.stmt);
            w.vec(&entry.param_levels, put_level); put_level(w, &entry.level); w.u32(*at);
        }
        DeltaEvent::GenSpineCodes { tag, codes, at } => {
            w.byte(16); w.u32(*tag);
            w.vec(&codes.ctors, |w, (ty, level)| { put_type(w, ty); put_level(w, level); });
            w.vec(&codes.nodes, |w, (ty, level)| { put_type(w, ty); put_level(w, level); });
            w.u32(*at);
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
        3 => DeltaEvent::GenTyCode { tag: r.u32()?, inline: type_rc(r)?, level: get_level(r)?, at: r.u32()? },
        4 => DeltaEvent::GenWfSlots { tag: r.u32()?, slots: WfSlots {
            shape: type_rc(r)?, shape_decoded: type_rc(r)?,
            arity: term_rc(r)?, level: get_level(r)?,
        }, at: r.u32()? },
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
        18 => DeltaEvent::Evidence(EvidenceRule {
            global: r.string()?, relation: r.string()?, heads: r.vec(|r| r.option(Reader::string))?,
        }),
        20 => DeltaEvent::Registered { ty: r.string()?, global: r.string()? },
        19 => DeltaEvent::Interface { key: r.string()?, info: crate::interfaces::InterfaceInfo {
            module: r.string()?, arity: r.u32()?, name: r.string()?, equations: r.vec(Reader::string)?,
        } },
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
            template: type_rc(r)?, stmt: type_rc(r)?,
            param_levels: r.vec(get_level)?, level: get_level(r)?,
        }, at: r.u32()? },
        16 => DeltaEvent::GenSpineCodes { tag: r.u32()?, codes: SpineCodes {
            ctors: r.vec(|r| Ok((type_rc(r)?, get_level(r)?)))?,
            nodes: r.vec(|r| Ok((type_rc(r)?, get_level(r)?)))?,
        }, at: r.u32()? },
        tag => return Err(ModuleImageDecodeError::InvalidTag { sort: "module event", tag }),
    })
}

fn validate_inductive(info: &Inductive) -> Result<(), ModuleImageDecodeError> {
    if info.index.is_some() != info.index_ty.is_some() {
        return Err(ModuleImageDecodeError::InvalidStructure("inductive index name/type disagree"));
    }
    for ctor in &info.ctors {
        if ctor.fields.len() != ctor.kind.len() || ctor.fields.len() != ctor.rec_at.len()
            || !(ctor.child_index.is_empty() || ctor.fields.len() == ctor.child_index.len())
        {
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
    // A group's members partition its family's constructors, one member per
    // constructor of the family's index type.
    if !info.members.is_empty() {
        let Some(IdxTy::Decl(index)) = &info.index_ty else {
            return Err(ModuleImageDecodeError::InvalidStructure("a mutual family has no member index"));
        };
        let mut seen = vec![false; info.ctors.len()];
        for m in &info.members {
            for &k in &m.ctors {
                if k >= seen.len() || std::mem::replace(&mut seen[k], true) {
                    return Err(ModuleImageDecodeError::InvalidStructure("mutual members do not partition the constructors"));
                }
            }
        }
        if info.members.len() != index.ctors.len() || seen.contains(&false) {
            return Err(ModuleImageDecodeError::InvalidStructure("mutual members do not partition the constructors"));
        }
    }
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
            DeltaEvent::GenSpineCodes { tag, codes, .. } => {
                if !spine_codes.insert(*tag) {
                    return Err(ModuleImageDecodeError::InvalidStructure("duplicate generated spine-code guard"));
                }
                if codes.ctors.len() < 2 || codes.nodes.len() + 1 != codes.ctors.len() {
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

/// A scope's interface encoding, for a registry projection
/// (`module_relocate::RegistryPart`).
pub(crate) fn encode_interface_scope(scope: &Scope) -> Vec<u8> {
    let mut w = Writer { interface: true, ..Writer::default() };
    put_scope(&mut w, scope);
    w.bytes
}

/// A global's surface signature — its parameter metadata and declaration,
/// spans zeroed — for a name observation
/// (`NameWorld::observations`).
pub(crate) fn encode_interface_signature(params: &[ParamMeta], surface: Option<&Decl>) -> Vec<u8> {
    let mut w = Writer { interface: true, ..Writer::default() };
    w.vec(params, put_param_meta);
    w.option(surface, put_decl);
    w.bytes
}

pub(crate) fn encode_delta(delta: &ModuleDelta) -> Vec<u8> {
    encode_delta_counted(delta).0
}

/// The image bytes and the syntax-node count the reader will charge for
/// them — the number a publisher compares against `max_nodes` before writing
/// an image the reader would only decode up to the budget and refuse.
/// The syntax nodes `ty` costs in an image, counted by the writer itself so
/// the number is the one the decode budget charges: its distinct subterms,
/// each repeat one more ([`Share`]). For `HEATHER_IMAGE_ATTRIBUTION`
/// (`emission_walk::tally_decl`).
pub(crate) fn type_image_nodes(ty: &Type) -> u64 {
    let mut w = Writer::default();
    put_type(&mut w, ty);
    w.nodes
}

/// [`type_image_nodes`] for a term.
pub(crate) fn term_image_nodes(t: &Term) -> u64 {
    let mut w = Writer::default();
    put_term(&mut w, t);
    w.nodes
}

pub(crate) fn encode_delta_counted(delta: &ModuleDelta) -> (Vec<u8>, u64) {
    let mut w = Writer::default();
    encode_delta_into(&mut w, delta, MAGIC);
    (w.bytes, w.nodes)
}

pub(crate) fn encode_delta_interface(delta: &ModuleDelta) -> Vec<u8> {
    let mut w = Writer { interface: true, ..Writer::default() };
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
    // The declaration slices (`docs/infrastructure/declaration-slice-replay-design.md` §3):
    // the semantic image only, never the interface projection, since a
    // slice's text is not something a dependent observes.
    if !w.interface {
        w.vec(&delta.items, put_slice);
        w.option(delta.scope_at_entry.as_ref(), put_scope);
        // Sealed proofs (`issues/theorem-witness-unfolding.md`): the
        // semantic image only, like the slices. A dependent observes a proof
        // by opening it and records the copy it opened, so leaving proofs out
        // of the interface is what keeps a proof edit from invalidating
        // every dependent.
        w.vec(&delta.sealed, put_sealed);
        w.vec(&delta.opened_dependencies, put_sealed);
    }
}

fn put_sealed(w: &mut Writer, (at, proof): &(usize, Rc<SealedProof>)) {
    w.usize(*at);
    match ImageProof::of(proof) {
        // Kept as its encoding: written back as it was read, unloaded.
        Some(image) => {
            w.bytes.extend_from_slice(&image.bytes);
            w.nodes += image.nodes;
        }
        // Its own sharing scope: the bytes are kept and decoded apart from
        // the image ([`ImageProof::load`]), so they may not refer outside.
        None => {
            let outer = std::mem::take(&mut w.share);
            put_term(w, proof.term());
            w.share = outer;
        }
    }
}

/// A sealed proof as an image encodes it, kept unloaded
/// (`issues/sealed-proof-memory.md`). The decode is checked, then let go: a
/// warm run holds each kept proof as its encoding until something opens
/// it, and an opened one is decoded again from these bytes.
fn get_sealed(r: &mut Reader<'_>) -> Result<(usize, Rc<SealedProof>), ModuleImageDecodeError> {
    let at = r.usize()?;
    let (start, budget) = (r.at, r.nodes_left);
    let outer = (std::mem::take(&mut r.terms), std::mem::take(&mut r.types));
    drop(get_term(r)?);
    (r.terms, r.types) = outer;
    let image = ImageProof { bytes: r.bytes[start..r.at].into(), nodes: budget - r.nodes_left, limits: r.limits };
    Ok((at, Rc::new(SealedProof::lazy(image))))
}

/// The [`ProofSource`] of a sealed proof read from an image: the bytes of
/// its term exactly as [`put_term`] wrote them, which decoded once already
/// when the image was read.
pub(crate) struct ImageProof {
    bytes: Box<[u8]>,
    /// The reader's node charge for the term, so re-writing the bytes keeps
    /// the writer's count the one a reader of the new image pays.
    nodes: u64,
    limits: ModuleImageLimits,
}

impl ImageProof {
    pub(crate) fn of(proof: &SealedProof) -> Option<&ImageProof> {
        proof.source()?.as_any().downcast_ref()
    }
}

impl ProofSource for ImageProof {
    fn load(&self) -> Term {
        decode_on_own_stack(&self.limits, || {
            let mut r = Reader::new(&self.bytes, self.limits)?;
            let term = get_term(&mut r)?;
            r.finish()?;
            Ok(term)
        })
        .expect("a sealed proof decodes as it did when its image was read")
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

/// Two sealed proofs are the same proof: one allocation, the same encoding,
/// or equal terms. A proof kept as its encoding is compared as one — the
/// other side is encoded, never this side decoded — so asking whether an
/// unopened dependency proof changed leaves it unloaded. The encoding is
/// faithful and canonical ([`Share`]), so equal bytes are equal terms and
/// equal terms equal bytes.
pub(crate) fn same_proof(a: &Rc<SealedProof>, b: &Rc<SealedProof>) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    let encoded = |t: &Term| {
        let mut w = Writer::default();
        put_term(&mut w, t);
        w.bytes
    };
    match (ImageProof::of(a), ImageProof::of(b)) {
        (Some(x), Some(y)) => x.bytes == y.bytes,
        (Some(x), None) => *x.bytes == *encoded(b.term()),
        (None, Some(y)) => *encoded(a.term()) == *y.bytes,
        (None, None) => a.term() == b.term(),
    }
}

fn put_slice(w: &mut Writer, slice: &crate::module_delta::ItemSlice) {
    w.string(&slice.source);
    w.usize(slice.start);
    for range in [&slice.psi, &slice.events, &slice.warnings] {
        w.usize(range.start);
        w.usize(range.end);
    }
    w.vec(&slice.unsealed, |w, at| w.usize(*at));
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
    let unsealed = r.vec(|r| r.usize())?;
    Ok(crate::module_delta::ItemSlice { source, start, psi, events, warnings, unsealed })
}

/// The stack one nesting level of decoding stands on, at most. `node` is the
/// only recursion the decoder has, so a thread with `max_depth` of these
/// (plus [`DECODE_BASE_BYTES`]) answers `DepthBudget` before it can overflow.
/// Measured by `tests::every_nesting_level_fits_the_decoders_frame_bound`,
/// which fails when a level outgrows it;
/// the deepest shape today is a surface block's `let`, at about 2.5 KiB.
/// A kernel term level was 16 KiB until its children were decoded through
/// [`term_rc`]/[`type_rc`], out of line, so that the one large match holds
/// pointers rather than every arm's decoded fields.
const DECODE_FRAME_BYTES: usize = 4 << 10;

/// The decoder's frames outside any node (the envelope, an event, a
/// declaration) and the thread's own start.
const DECODE_BASE_BYTES: usize = 1 << 20;

/// Run a decode on a thread whose stack is sized from `limits.max_depth`, so
/// the depth budget holds whatever stack the caller has: the main thread's
/// 8 MiB, a spawned thread's 2 MiB default, or a test runner's
/// (issues/module-image-decode-depth-vs-stack.md).
fn decode_on_own_stack<T: Send>(
    limits: &ModuleImageLimits,
    decode: impl FnOnce() -> Result<T, ModuleImageDecodeError> + Send,
) -> Result<T, ModuleImageDecodeError> {
    let stack = (limits.max_depth as usize)
        .saturating_mul(DECODE_FRAME_BYTES)
        .saturating_add(DECODE_BASE_BYTES);
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("module-image".into())
            .stack_size(stack)
            .spawn_scoped(scope, decode)
            .map_err(|_| ModuleImageDecodeError::NoStack)?
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

pub(crate) fn decode_delta(
    bytes: &[u8],
    dependency_psi: GlobalCtx,
    limits: ModuleImageLimits,
) -> Result<ModuleDelta, ModuleImageDecodeError> {
    decode_on_own_stack(&limits, || decode_delta_here(bytes, dependency_psi, limits))
}

fn decode_delta_here(
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
    let sealed = r.vec(get_sealed)?;
    let opened_dependencies = r.vec(get_sealed)?;
    r.finish()?;
    // A sealed proof sits beside a theorem of the extension, in order; an
    // opened dependency proof inside the prefix it was opened from.
    let theorem = |k: usize| matches!(extension.get(k), Some(GlobalBinding::Tm { body: None, .. }));
    if sealed.windows(2).any(|w| w[0].0 >= w[1].0) || sealed.iter().any(|(k, _)| !theorem(*k)) {
        return Err(ModuleImageDecodeError::InvalidStructure("a sealed proof is not beside a theorem"));
    }
    if opened_dependencies.windows(2).any(|w| w[0].0 >= w[1].0)
        || opened_dependencies.iter().any(|(i, _)| *i >= actual)
    {
        return Err(ModuleImageDecodeError::InvalidStructure("an opened proof is outside the dependency prefix"));
    }
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
        extension, sealed, opened_dependencies, scope, events,
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

    /// Deep spines through each recursive path of the decoder, for the stack
    /// tests below. Each returns the spine's image and its depth in nodes.
    mod deep {
        use super::*;

        fn sp() -> Span { Span { start: 0, end: 0 } }
        fn var() -> Expr { Expr { kind: ExprKind::Var("x".into()), span: sp() } }

        fn terms(levels: u32, per: u32, wrap: impl Fn(Term) -> Term) -> (Vec<u8>, u32) {
            let mut t = Term::Zero;
            for _ in 0..levels / per { t = wrap(t); }
            let mut w = Writer::default();
            put_term(&mut w, &t);
            (w.bytes, levels / per * per + 1)
        }

        fn exprs(levels: u32, per: u32, wrap: impl Fn(Expr) -> Expr) -> (Vec<u8>, u32) {
            let mut e = var();
            for _ in 0..levels / per { e = wrap(e); }
            let mut w = Writer::default();
            put_expr(&mut w, &e);
            (w.bytes, levels / per * per + 1)
        }

        pub(super) type Decode = fn(&mut Reader<'_>) -> Result<(), ModuleImageDecodeError>;

        /// Every spine at about `levels` nodes deep: its name, image, depth
        /// and the decoder for its root sort.
        pub(super) fn spines(levels: u32) -> Vec<(&'static str, Vec<u8>, u32, Decode)> {
            let term: Decode = |r| get_term(r).map(drop);
            let expr: Decode = |r| get_expr(r).map(drop);
            let (block, block_depth) = exprs(levels, 1, |e| Expr { kind: ExprKind::Block(Box::new(Block {
                stmts: vec![Stmt::Let { name: "x".into(), ty: None, expr: e, span: sp(), opaque: false }],
                result: Box::new(var()), ons: vec![], span: sp() })), span: sp() });
            let (arm, arm_depth) = exprs(levels, 1, |e| Expr { kind: ExprKind::Match {
                form: MatchForm::Match, generated: false, scrut: Box::new(var()), eqbind: None, motive: None,
                arms: vec![Arm { ctor: "C".into(), default: false, binders: vec![], body: e, span: sp() }] }, span: sp() });
            let (arg, arg_depth) = exprs(levels, 1, |e| Expr { kind: ExprKind::App {
                head: Box::new(var()), args: vec![e], named: vec![], explicit: false, goal_oriented: false }, span: sp() });
            let (ty, ty_depth) = exprs(levels, 2, |e| Expr {
                kind: ExprKind::TyLit(Box::new(Ty { kind: TyKind::OfExpr(Box::new(e)), span: sp() })), span: sp() });
            let (succ, succ_depth) = terms(levels, 1, |t| Term::Succ(Rc::new(t)));
            let (fun, fun_depth) = terms(levels, 1, |t| Term::AppAt { fun: Rc::new(t), arg: Rc::new(Term::Zero) });
            let (subst, subst_depth) = terms(levels, 1, |t| Term::GlobalTm { var: GlobalVar::index(0), subst: LocalSubst {
                tail: SubstTail::Wk { len: 0, ctx_var: GlobalVar::index(0) }, terms: vec![Rc::new(t)] } });
            let (el, el_depth) = terms(levels, 2, |t| Term::BoxTy(Rc::new(Type::El { level: Level::Zero, tm: Rc::new(t) })));
            vec![
                ("term succ", succ, succ_depth, term),
                ("term application head", fun, fun_depth, term),
                ("term substitution", subst, subst_depth, term),
                ("type through term", el, el_depth, term),
                ("block let", block, block_depth, expr),
                ("match arm", arm, arm_depth, expr),
                ("call argument", arg, arg_depth, expr),
                ("type through expression", ty, ty_depth, expr),
            ]
        }
    }

    /// Run `f` where a frame past the bound fails an assertion rather than
    /// the process.
    fn on_large_stack<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new().stack_size(256 << 20).spawn(f).unwrap().join().unwrap()
    }

    #[test]
    fn every_nesting_level_fits_the_decoders_frame_bound() {
        on_large_stack(|| {
            for (name, bytes, depth, decode) in deep::spines(ModuleImageLimits::default().max_depth - 1) {
                let mut r = Reader::new(&bytes, ModuleImageLimits::default()).unwrap();
                let top = 0_u8;
                let top = std::hint::black_box(&top) as *const u8 as usize;
                decode(&mut r).unwrap();
                let per_level = (top - r.low_water) / depth as usize;
                r.finish().unwrap();
                assert!(
                    per_level <= DECODE_FRAME_BYTES,
                    "a {name} level decodes on {per_level} bytes of stack, past DECODE_FRAME_BYTES ({DECODE_FRAME_BYTES})"
                );
            }
        });
    }

    #[test]
    fn the_depth_budget_holds_on_a_small_callers_stack() {
        let limits = ModuleImageLimits::default();
        let (at_budget, over_budget) = on_large_stack(move || (deep::spines(limits.max_depth - 1), deep::spines(limits.max_depth + 2)));
        // A quarter of a megabyte: far below what any spine needs natively.
        std::thread::Builder::new().stack_size(256 << 10).spawn(move || {
            for (name, bytes, depth, decode) in at_budget {
                assert!(depth <= limits.max_depth, "{name}");
                decode_on_own_stack(&limits, || {
                    let mut r = Reader::new(&bytes, limits)?;
                    decode(&mut r)?;
                    r.finish()
                }).unwrap_or_else(|e| panic!("{name} at depth {depth}: {e}"));
            }
            for (name, bytes, depth, decode) in over_budget {
                assert!(depth > limits.max_depth, "{name}");
                let refused = decode_on_own_stack(&limits, || decode(&mut Reader::new(&bytes, limits)?));
                assert_eq!(refused, Err(ModuleImageDecodeError::DepthBudget), "{name}");
            }
        }).unwrap().join().unwrap();
    }

    /// The writer recurses through a term's children three frames a level
    /// while it numbers them ([`Writer::canonical_term`]), on its caller's
    /// stack. Every spine at the depth budget, the deepest a reader takes,
    /// encodes on half the 8 MiB a main thread has.
    #[test]
    fn the_depth_budget_encodes_on_half_a_main_threads_stack() {
        let limits = ModuleImageLimits::default();
        std::thread::Builder::new().stack_size(4 << 20).spawn(move || {
            assert!(!deep::spines(limits.max_depth - 1).is_empty());
        }).unwrap().join().unwrap();
    }

    /// A term whose every level uses the one below twice: `2^levels` nodes
    /// as a tree, `levels` as allocated.
    fn doubling(levels: usize, share: bool) -> Rc<Term> {
        match levels {
            0 => Rc::new(Term::Zero),
            _ if share => {
                let t = doubling(levels - 1, true);
                Rc::new(Term::AppAt { fun: t.clone(), arg: t })
            }
            _ => Rc::new(Term::AppAt { fun: doubling(levels - 1, false), arg: doubling(levels - 1, false) }),
        }
    }

    fn encode(t: &Rc<Term>) -> (Vec<u8>, u64) {
        let mut w = Writer::default();
        put_term(&mut w, t);
        (w.bytes, w.nodes)
    }

    fn decode(bytes: &[u8]) -> Rc<Term> {
        let mut r = Reader::new(bytes, ModuleImageLimits::default()).unwrap();
        let t = term_rc(&mut r).unwrap();
        r.finish().unwrap();
        t
    }

    /// A shared subterm is written once and read back as one allocation:
    /// the image and its node charge grow with the DAG, not the tree.
    #[test]
    fn shared_subterms_are_written_once() {
        let (bytes, nodes) = encode(&doubling(40, true));
        assert!(nodes <= 2 * 41, "{nodes} nodes charged for 41 distinct ones");
        assert!(bytes.len() < 41 * 16, "{} bytes for 41 distinct nodes", bytes.len());
        let back = decode(&bytes);
        let Term::AppAt { fun, arg } = &*back else { panic!("an application") };
        assert!(Rc::ptr_eq(fun, arg), "the shared child decodes as one allocation");
        assert_eq!(encode(&back).0, bytes);
    }

    /// Sharing is by equal structure, so the bytes do not depend on how the
    /// writer's terms happened to share memory: an interface hash or
    /// `same_proof` compares encodings made by different processes.
    #[test]
    fn the_encoding_does_not_depend_on_allocation() {
        let shared = encode(&doubling(12, true));
        assert_eq!(encode(&doubling(12, false)), shared);
        // An inline position shares too: the second copy of `t` refers to the
        // first.
        let t = doubling(3, true);
        let mut w = Writer::default();
        put_term(&mut w, &*t);
        put_term(&mut w, &Term::clone(&t));
        let mut r = Reader::new(&w.bytes, ModuleImageLimits::default()).unwrap();
        let (a, b) = (get_term(&mut r).unwrap(), get_term(&mut r).unwrap());
        assert_eq!(r.terms.len(), 4, "four distinct nodes decoded, the copy by reference");
        r.finish().unwrap();
        assert!(a == *t && b == *t);
    }

    /// A reference past the nodes read so far is refused, not followed.
    #[test]
    fn a_shared_reference_must_point_backwards() {
        let mut bytes = vec![tag::SHARED];
        bytes.extend_from_slice(&0_u32.to_le_bytes());
        let mut r = Reader::new(&bytes, ModuleImageLimits::default()).unwrap();
        assert_eq!(term_rc(&mut r), Err(ModuleImageDecodeError::InvalidStructure("shared term index")));
    }

    fn ordinary_delta() -> (GlobalCtx, ModuleDelta) {
        let mut elaborator = Elaborator::new();
        let prefix = elaborator.psi().clone();
        let identity = ModuleDependencyIdentity::new(vec![[0x17; 32], [0xa4; 32]]);
        let delta = elaborator
            .elab_module_delta(
                "codec",
                "inductive Box<A> { Wrap(A) }\n\
                 fn Box::get<A>(self b: Box<A>) -> A { match b { Wrap(x) => x } }\n\
                 theorem get_zero(): Wrap(0).get<Nat>() = 0 { refl }\n\
                 fn id(x: Nat) -> Nat { x }\n\
                 theorem id_zero(): id(0) = 0 { refl }\n\
                 def five: Nat = 5;\n\
                 def six = Succ(five);",
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
            events: vec![DeltaEvent::GenDef { key: GenDef::TyCode(0), abs: 99 }],
            items: Vec::new(),
            warnings: Vec::new(),
            scope_at_entry: None,
            sealed: Vec::new(),
            opened_dependencies: Vec::new(),
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
                DeltaEvent::GenDef { key: GenDef::TyCode(0), abs: 0 },
                DeltaEvent::GenDef { key: GenDef::TyCode(0), abs: 1 },
            ],
            items: Vec::new(),
            warnings: Vec::new(),
            scope_at_entry: None,
            sealed: Vec::new(),
            opened_dependencies: Vec::new(),
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
fn twice<A>(a: A, f: A -> A) -> A { have b: A = f(a); let c = f(b); c }
fn twice_zero(f: Z -> Z) -> Z { twice(Z0, f) }
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
