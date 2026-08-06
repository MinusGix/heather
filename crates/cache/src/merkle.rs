//! Content addressing: the hash of an elaborated declaration with every
//! global reference replaced by the hash of its referent's interface
//! (`docs/cache-v1-design.md` §3 and §5, `issues/parallel-checking-and-caching.md`).
//!
//! # A structural walker, not a rendering
//!
//! v1 hashed `heather_kernel::fmt::write_exact`'s *printed* form through a
//! scanner that rewrote `u<d>`/`U<d>`/`g<d>` into referent hashes. That is
//! gone (design doc §3, superseded by §12). Two reasons, and the second is the
//! one that matters:
//!
//! - **Cost.** One `write_exact` pass over `lib/ir_v1.hthr` was ~7 s — the
//!   whole of the cold run's +15% and ~90% of a warm one — essentially all of
//!   it `std::fmt` machinery producing bytes nobody read.
//! - **Totality.** The scanner rested on a stated assumption about the
//!   kernel's printed form, and the printed form is not obliged to be
//!   injective. It is not: `fmt`'s [`Branches`] impl prints 37 of the struct's
//!   52 fields, so under v1 two code recursors differing *only* in (say) their
//!   `tm_elim_wf` branch had the same cache identity. Nothing in the library
//!   exercises that today, which is exactly why a stated assumption was the
//!   wrong instrument.
//!
//! The walker below is an exhaustive `match` over every kernel node kind, and
//! every struct is destructured **without** a `..` rest pattern. A new kernel
//! constructor, or a new field on `Branches`, is therefore a compile error
//! here rather than a field that silently leaves the hash. That is the whole
//! robustness point; do not "fix" a build break by adding a `_` arm.
//!
//! # Framing, and why the encoding is injective
//!
//! The walker feeds the hasher a byte stream built from four kinds of piece:
//!
//! - a **tag**: one byte, unique across *all* node kinds of all sorts (see
//!   the `tag` module — the value space is partitioned, not reused per sort);
//! - a **fixed-width integer**: `u32` little-endian for de Bruijn indices,
//!   binder counts and lengths;
//! - a **referent hash**: exactly 32 raw bytes, at the five global-reference
//!   sites listed below;
//! - a **sub-encoding**: the same scheme, recursively.
//!
//! Sequences (a `UApp`'s levels, a substitution's terms, a context's entries)
//! are preceded by their length as a `u32`. Nothing else is variable-length.
//!
//! *Injectivity.* The encoding is prefix-free, hence injective, by induction
//! on the tree: the leading tag byte determines the node kind, and the node
//! kind determines the exact sequence of pieces that follows — how many
//! fixed-width integers, of what width, and how many sub-encodings of which
//! sorts, with any repetition count read from a length field that precedes it.
//! So a decoder can be written that consumes exactly the bytes one node
//! occupies and no more; a function with a left inverse is injective. Two
//! distinct trees therefore have distinct byte streams, and (SHA-256's
//! collision resistance aside) distinct hashes. Note this is a *stronger*
//! claim than v1 could make: v1 explicitly did **not** claim `write_exact`
//! was injective, it inherited "injective enough" from the golden-hash test —
//! and §Totality above is what that gap actually cost.
//!
//! *Substitution.* Global references are the one place the encoding is not a
//! function of the tree alone. At exactly five sites a `GlobalVar` is replaced
//! by the 32 bytes of its referent's interface hash:
//!
//! | site | what it is |
//! |---|---|
//! | [`Term::GlobalTm`] | `u^δ` |
//! | [`Type::GlobalTy`] | `U^δ` |
//! | [`CtxBase::Var`] | a context variable `g` as a context's base |
//! | [`SubstTail::Wk`] | `wk^k_g` — the tail names `g` |
//! | [`SubstTail::Empty`]'s `base` | `·^k_g` — likewise, through `CtxBase` |
//!
//! Those are every occurrence of `GlobalVar` in `crates/kernel/src/term.rs`,
//! and the walker reaches them through `CtxBase`/`SubstTail` rather than by
//! pattern-matching on spellings. The replacement is fixed-width, so framing
//! is untouched; and because it drops the *position*, a declaration hashes the
//! same wherever in Ψ it and its referents sit — which is the property the
//! whole scheme exists for (a Ψ index is a position, and any key that keeps
//! one dies on the first merge that renumbers a suffix).
//!
//! *Fail-closed.* If a reference resolves outside the known prefix, or onto a
//! **poisoned** entry (one whose own hash could not be computed), the walk is
//! poisoned and the whole computation returns `None`: the declaration is not
//! cacheable and is simply re-checked. A missing key can only cost time.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, LocalCtx, LocalSubst, Motives, SubstTail, Term,
    Type,
};

use crate::sha256::Sha256;

/// A 32-byte content hash.
pub type Hash = [u8; 32];

/// Domain separation. The two hash families must never be confusable: an
/// interface hash answers "what do dependents see", a check key answers "did
/// the kernel accept this", and they are computed over overlapping material.
///
/// **Bumped to `/2` with the walker.** The domain string names the *scheme*,
/// not just the family: v1's preimage was a rewritten rendering and this one
/// is a framed byte stream, so an accidental agreement between the two would
/// be a v1 entry believed about a v2 declaration. Bumping makes that
/// impossible by construction rather than merely unlikely. (`store::FORMAT` is
/// bumped alongside, which is what makes the invalidation *loud* — see
/// `docs/cache-v1-design.md` §12.)
const DOMAIN_IFACE: &[u8] = b"heather/iface/2\0";
const DOMAIN_CHECK: &[u8] = b"heather/check/2\0";

/// The interface hashes of a Ψ prefix, in binding order.
///
/// `None` at an index is a **poisoned** binding: one whose own hash could not
/// be computed. Anything referencing it is not hashable either, so the poison
/// propagates and the declaration is never cached.
pub type Prefix = [Option<Hash>];

/// Every tag byte, in one place, so that "unique across all sorts" is
/// checkable by reading a single table rather than by trusting each `match`.
///
/// The ranges are deliberate: `0x01–0x1F` the small structural sorts,
/// `0x20–0x3F` [`Type`], `0x40–0x7F` [`Term`]. Values are frozen — changing
/// one changes every cache key, so it belongs with a domain-string bump.
#[rustfmt::skip]
mod tag {
    // levels
    pub const L_VAR: u8 = 0x01;
    pub const L_ZERO: u8 = 0x02;
    pub const L_SUCC: u8 = 0x03;
    pub const L_MAX: u8 = 0x04;
    pub const L_OMEGA: u8 = 0x05;
    // layers
    pub const LAYER_VAR: u8 = 0x08;
    pub const LAYER_CODE: u8 = 0x09;
    pub const LAYER_PROG: u8 = 0x0a;
    pub const LAYER_META: u8 = 0x0b;
    // contexts and substitutions
    pub const BASE_NIL: u8 = 0x0c;
    pub const BASE_VAR: u8 = 0x0d;
    pub const TAIL_EMPTY: u8 = 0x0e;
    pub const TAIL_WK: u8 = 0x0f;
    pub const LOCAL_CTX: u8 = 0x10;
    pub const LOCAL_SUBST: u8 = 0x11;
    pub const CTX_ENTRY: u8 = 0x12;
    // global bindings and the recursor payloads
    pub const B_CTX: u8 = 0x14;
    pub const B_TY: u8 = 0x15;
    pub const B_TM: u8 = 0x16;
    pub const BODY_NONE: u8 = 0x17;
    pub const BODY_SOME: u8 = 0x18;
    pub const MOTIVES: u8 = 0x19;
    pub const BRANCHES: u8 = 0x1a;
    // check-key shapes
    pub const KEY_DEF: u8 = 0x1c;
    pub const KEY_PROOF: u8 = 0x1d;

    // types
    pub const T_NAT: u8 = 0x20;
    pub const T_PI: u8 = 0x21;
    pub const T_TY: u8 = 0x22;
    pub const T_UPI: u8 = 0x23;
    pub const T_EL: u8 = 0x24;
    pub const T_ID: u8 = 0x25;
    pub const T_SEQ: u8 = 0x26;
    pub const T_SEMPTY: u8 = 0x27;
    pub const T_SIGMA: u8 = 0x28;
    pub const T_UNIT: u8 = 0x29;
    pub const T_EMPTY: u8 = 0x2a;
    pub const T_SUM: u8 = 0x2b;
    pub const T_W: u8 = 0x2c;
    pub const T_VEC: u8 = 0x2d;
    pub const T_FIN: u8 = 0x2e;
    pub const T_WF: u8 = 0x2f;
    pub const T_GLOBAL: u8 = 0x30;
    pub const T_CTXPI: u8 = 0x31;
    pub const T_TYPI: u8 = 0x32;
    pub const T_CODETY: u8 = 0x33;
    pub const T_CODETM: u8 = 0x34;

    // terms
    pub const E_VAR: u8 = 0x40;
    pub const E_TMNAT: u8 = 0x41;
    pub const E_TMPI: u8 = 0x42;
    pub const E_TMTY: u8 = 0x43;
    pub const E_TMID: u8 = 0x44;
    pub const E_TMSEQ: u8 = 0x45;
    pub const E_TMSEMPTY: u8 = 0x46;
    pub const E_TMSIGMA: u8 = 0x47;
    pub const E_TMUNIT: u8 = 0x48;
    pub const E_TMEMPTY: u8 = 0x49;
    pub const E_TMSUM: u8 = 0x4a;
    pub const E_TMW: u8 = 0x4b;
    pub const E_TMVEC: u8 = 0x4c;
    pub const E_TMFIN: u8 = 0x4d;
    pub const E_TMWF: u8 = 0x4e;
    pub const E_ZERO: u8 = 0x4f;
    pub const E_SUCC: u8 = 0x50;
    pub const E_ELIMNAT: u8 = 0x51;
    pub const E_REFL: u8 = 0x52;
    pub const E_J: u8 = 0x53;
    pub const E_SREFL: u8 = 0x54;
    pub const E_TRANSP: u8 = 0x55;
    pub const E_ELIMSEMPTY: u8 = 0x56;
    pub const E_PAIR: u8 = 0x57;
    pub const E_FST: u8 = 0x58;
    pub const E_SND: u8 = 0x59;
    pub const E_TRIV: u8 = 0x5a;
    pub const E_ELIMEMPTY: u8 = 0x5b;
    pub const E_INL: u8 = 0x5c;
    pub const E_INR: u8 = 0x5d;
    pub const E_CASE: u8 = 0x5e;
    pub const E_SUP: u8 = 0x5f;
    pub const E_ELIMW: u8 = 0x60;
    pub const E_SUPF: u8 = 0x61;
    pub const E_ELIMWF: u8 = 0x62;
    pub const E_LAM: u8 = 0x63;
    pub const E_APP: u8 = 0x64;
    pub const E_ULAM: u8 = 0x65;
    pub const E_UAPP: u8 = 0x66;
    pub const E_GLOBAL: u8 = 0x67;
    pub const E_CTXLAM: u8 = 0x68;
    pub const E_CTXAPP: u8 = 0x69;
    pub const E_TYLAM: u8 = 0x6a;
    pub const E_TYAPP: u8 = 0x6b;
    pub const E_BOXTY: u8 = 0x6c;
    pub const E_BOXTM: u8 = 0x6d;
    pub const E_LETBOXTY: u8 = 0x6e;
    pub const E_LETBOXTM: u8 = 0x6f;
    pub const E_ELIMCODETY: u8 = 0x70;
    pub const E_ELIMCODETM: u8 = 0x71;
}

/// The walk in progress: a SHA-256 state, a small staging buffer, and the Ψ
/// prefix the global references resolve against.
struct Walk<'a> {
    hasher: Sha256,
    /// Tags and small integers arrive a few bytes at a time and there are tens
    /// of millions of them. `Sha256::update` per byte would spend all its time
    /// in partial-block bookkeeping (this was measured on the v1 scanner, for
    /// the same reason), so the stream is staged here and handed over a block
    /// at a time.
    buf: Vec<u8>,
    prefix: &'a Prefix,
    /// The length of Ψ the walked structure is scoped over. A reference
    /// `GlobalVar(k)` denotes absolute index `len − 1 − k`.
    len: u32,
    /// Set when a reference failed to resolve. The result is then discarded
    /// entirely: no key is produced at all.
    poisoned: bool,
}

/// Staging capacity: two SHA-256 blocks' worth of headroom over the flush
/// threshold, so a single `put_hash` never needs a bounds dance.
const FLUSH_AT: usize = 8192;

impl<'a> Walk<'a> {
    fn new(domain: &[u8], prefix: &'a Prefix, len: u32) -> Walk<'a> {
        let mut w = Walk {
            hasher: Sha256::new(),
            buf: Vec::with_capacity(FLUSH_AT + 64),
            prefix,
            len,
            poisoned: false,
        };
        w.buf.extend_from_slice(domain);
        w
    }

    #[inline]
    fn tag(&mut self, t: u8) {
        self.buf.push(t);
        if self.buf.len() >= FLUSH_AT {
            self.flush();
        }
    }

    #[inline]
    fn u32(&mut self, n: u32) {
        self.buf.extend_from_slice(&n.to_le_bytes());
        if self.buf.len() >= FLUSH_AT {
            self.flush();
        }
    }

    /// A sequence length. `u32` like every other integer here; a context or
    /// substitution longer than 4 billion entries cannot be built in the first
    /// place (they are `Vec`s of `Rc`s), and saturating keeps the width fixed.
    #[inline]
    fn seq_len(&mut self, n: usize) {
        self.u32(u32::try_from(n).unwrap_or(u32::MAX));
    }

    fn flush(&mut self) {
        self.hasher.update(&self.buf);
        self.buf.clear();
    }

    /// Emit the referent's interface hash in place of the positional index —
    /// the Merkle substitution, at all five sites (see the module docs).
    fn global(&mut self, var: u32) {
        match self
            .len
            .checked_sub(1)
            .and_then(|l| l.checked_sub(var))
            .and_then(|abs| self.prefix.get(abs as usize).copied().flatten())
        {
            Some(h) => {
                self.buf.extend_from_slice(&h);
                if self.buf.len() >= FLUSH_AT {
                    self.flush();
                }
            }
            // Still write *something* fixed-width, so a poisoned walk does not
            // also desynchronize the framing of whatever follows it. The
            // result is discarded either way.
            None => {
                self.poisoned = true;
                self.buf.extend_from_slice(&[0u8; 32]);
                if self.buf.len() >= FLUSH_AT {
                    self.flush();
                }
            }
        }
    }

    fn finish(mut self) -> Option<Hash> {
        if self.poisoned {
            return None;
        }
        self.flush();
        Some(self.hasher.finish())
    }

    // ---- the walk itself -------------------------------------------------
    //
    // Every `match` below is exhaustive with no `_` arm, and every struct is
    // destructured with no `..`. That is load-bearing: see the module docs.

    fn layer(&mut self, l: Layer) {
        self.tag(match l {
            Layer::Var => tag::LAYER_VAR,
            Layer::Code => tag::LAYER_CODE,
            Layer::Prog => tag::LAYER_PROG,
            Layer::Meta => tag::LAYER_META,
        });
    }

    fn level(&mut self, l: &Level) {
        match l {
            Level::Var(v) => {
                self.tag(tag::L_VAR);
                self.u32(v.0);
            }
            Level::Zero => self.tag(tag::L_ZERO),
            Level::Succ(l) => {
                self.tag(tag::L_SUCC);
                self.level(l);
            }
            Level::Max(a, b) => {
                self.tag(tag::L_MAX);
                self.level(a);
                self.level(b);
            }
            Level::Omega => self.tag(tag::L_OMEGA),
        }
    }

    fn base(&mut self, b: CtxBase) {
        match b {
            CtxBase::Nil => self.tag(tag::BASE_NIL),
            CtxBase::Var(g) => {
                self.tag(tag::BASE_VAR);
                self.global(g.0);
            }
        }
    }

    fn ctx(&mut self, c: &LocalCtx) {
        let LocalCtx { base, entries } = c;
        self.tag(tag::LOCAL_CTX);
        self.base(*base);
        self.seq_len(entries.len());
        for e in entries {
            let CtxEntry { ty, level } = e;
            self.tag(tag::CTX_ENTRY);
            self.ty(ty);
            self.level(level);
        }
    }

    fn subst(&mut self, s: &LocalSubst) {
        let LocalSubst { tail, terms } = s;
        self.tag(tag::LOCAL_SUBST);
        match *tail {
            SubstTail::Empty { len, base } => {
                self.tag(tag::TAIL_EMPTY);
                self.u32(len);
                self.base(base);
            }
            SubstTail::Wk { len, ctx_var } => {
                self.tag(tag::TAIL_WK);
                self.u32(len);
                self.global(ctx_var.0);
            }
        }
        self.seq_len(terms.len());
        for t in terms {
            self.term(t);
        }
    }

    fn ty(&mut self, t: &Type) {
        match t {
            Type::Nat => self.tag(tag::T_NAT),
            Type::Pi { dom_level, cod_level, dom, cod } => {
                self.tag(tag::T_PI);
                self.level(dom_level);
                self.level(cod_level);
                self.ty(dom);
                self.ty(cod);
            }
            Type::Ty(l) => {
                self.tag(tag::T_TY);
                self.level(l);
            }
            Type::UPi { num_vars, level, body } => {
                self.tag(tag::T_UPI);
                self.u32(*num_vars);
                self.level(level);
                self.ty(body);
            }
            Type::El { level, tm } => {
                self.tag(tag::T_EL);
                self.level(level);
                self.term(tm);
            }
            Type::Id { level, ty, lhs, rhs } => {
                self.tag(tag::T_ID);
                self.level(level);
                self.ty(ty);
                self.term(lhs);
                self.term(rhs);
            }
            Type::SEq { level, ty, lhs, rhs } => {
                self.tag(tag::T_SEQ);
                self.level(level);
                self.ty(ty);
                self.term(lhs);
                self.term(rhs);
            }
            Type::SEmpty { level } => {
                self.tag(tag::T_SEMPTY);
                self.level(level);
            }
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                self.tag(tag::T_SIGMA);
                self.level(fst_level);
                self.level(snd_level);
                self.ty(fst);
                self.ty(snd);
            }
            Type::Unit { level } => {
                self.tag(tag::T_UNIT);
                self.level(level);
            }
            Type::Empty { level } => {
                self.tag(tag::T_EMPTY);
                self.level(level);
            }
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                self.tag(tag::T_SUM);
                self.level(lhs_level);
                self.level(rhs_level);
                self.ty(lhs);
                self.ty(rhs);
            }
            Type::W { shape_level, pos_level, shape, pos } => {
                self.tag(tag::T_W);
                self.level(shape_level);
                self.level(pos_level);
                self.ty(shape);
                self.ty(pos);
            }
            Type::Vec { level, elem, len } => {
                self.tag(tag::T_VEC);
                self.level(level);
                self.ty(elem);
                self.term(len);
            }
            Type::Fin { len } => {
                self.tag(tag::T_FIN);
                self.term(len);
            }
            Type::Wf { level, shape, arity } => {
                self.tag(tag::T_WF);
                self.level(level);
                self.ty(shape);
                self.term(arity);
            }
            // Reference site 2 of 5.
            Type::GlobalTy { var, subst } => {
                self.tag(tag::T_GLOBAL);
                self.global(var.0);
                self.subst(subst);
            }
            Type::CtxPi { level, body } => {
                self.tag(tag::T_CTXPI);
                self.level(level);
                self.ty(body);
            }
            Type::TyPi { ctx, arg_level, body_level, body } => {
                self.tag(tag::T_TYPI);
                self.ctx(ctx);
                self.level(arg_level);
                self.level(body_level);
                self.ty(body);
            }
            Type::CodeTy { ctx, level } => {
                self.tag(tag::T_CODETY);
                self.ctx(ctx);
                self.level(level);
            }
            Type::CodeTm { ctx, ty, level } => {
                self.tag(tag::T_CODETM);
                self.ctx(ctx);
                self.ty(ty);
                self.level(level);
            }
        }
    }

    fn term(&mut self, t: &Term) {
        match t {
            Term::Var(v) => {
                self.tag(tag::E_VAR);
                self.u32(v.0);
            }
            Term::TmNat => self.tag(tag::E_TMNAT),
            Term::TmPi { dom_level, cod_level, dom, cod } => {
                self.tag(tag::E_TMPI);
                self.level(dom_level);
                self.level(cod_level);
                self.term(dom);
                self.term(cod);
            }
            Term::TmTy(l) => {
                self.tag(tag::E_TMTY);
                self.level(l);
            }
            Term::TmId { level, ty, lhs, rhs } => {
                self.tag(tag::E_TMID);
                self.level(level);
                self.term(ty);
                self.term(lhs);
                self.term(rhs);
            }
            Term::TmSEq { level, ty, lhs, rhs } => {
                self.tag(tag::E_TMSEQ);
                self.level(level);
                self.term(ty);
                self.term(lhs);
                self.term(rhs);
            }
            Term::TmSEmpty { level } => {
                self.tag(tag::E_TMSEMPTY);
                self.level(level);
            }
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                self.tag(tag::E_TMSIGMA);
                self.level(fst_level);
                self.level(snd_level);
                self.term(fst);
                self.term(snd);
            }
            Term::TmUnit { level } => {
                self.tag(tag::E_TMUNIT);
                self.level(level);
            }
            Term::TmEmpty { level } => {
                self.tag(tag::E_TMEMPTY);
                self.level(level);
            }
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                self.tag(tag::E_TMSUM);
                self.level(lhs_level);
                self.level(rhs_level);
                self.term(lhs);
                self.term(rhs);
            }
            Term::TmW { shape_level, pos_level, shape, pos } => {
                self.tag(tag::E_TMW);
                self.level(shape_level);
                self.level(pos_level);
                self.term(shape);
                self.term(pos);
            }
            Term::TmVec { level, elem, len } => {
                self.tag(tag::E_TMVEC);
                self.level(level);
                self.term(elem);
                self.term(len);
            }
            Term::TmFin { len } => {
                self.tag(tag::E_TMFIN);
                self.term(len);
            }
            Term::TmWf { level, shape, arity } => {
                self.tag(tag::E_TMWF);
                self.level(level);
                self.term(shape);
                self.term(arity);
            }
            Term::Zero => self.tag(tag::E_ZERO),
            Term::Succ(t) => {
                self.tag(tag::E_SUCC);
                self.term(t);
            }
            Term::ElimNat { level, motive, base, step, scrut } => {
                self.tag(tag::E_ELIMNAT);
                self.level(level);
                self.ty(motive);
                self.term(base);
                self.term(step);
                self.term(scrut);
            }
            Term::Refl { level, ty, tm } => {
                self.tag(tag::E_REFL);
                self.level(level);
                self.ty(ty);
                self.term(tm);
            }
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
                self.tag(tag::E_J);
                self.level(ty_level);
                self.level(motive_level);
                self.ty(ty);
                self.term(lhs);
                self.ty(motive);
                self.term(case);
                self.term(rhs);
                self.term(proof);
            }
            Term::SRefl { level, ty, tm } => {
                self.tag(tag::E_SREFL);
                self.level(level);
                self.ty(ty);
                self.term(tm);
            }
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
                self.tag(tag::E_TRANSP);
                self.level(ty_level);
                self.level(motive_level);
                self.ty(ty);
                self.ty(motive);
                self.term(lhs);
                self.term(rhs);
                self.term(proof);
                self.term(tm);
            }
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                self.tag(tag::E_ELIMSEMPTY);
                self.level(level);
                self.level(scrut_level);
                self.ty(motive);
                self.term(scrut);
            }
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => {
                self.tag(tag::E_PAIR);
                self.level(fst_level);
                self.level(snd_level);
                self.ty(fst_ty);
                self.ty(snd_ty);
                self.term(fst);
                self.term(snd);
            }
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                self.tag(tag::E_FST);
                self.level(fst_level);
                self.level(snd_level);
                self.ty(fst_ty);
                self.ty(snd_ty);
                self.term(pair);
            }
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                self.tag(tag::E_SND);
                self.level(fst_level);
                self.level(snd_level);
                self.ty(fst_ty);
                self.ty(snd_ty);
                self.term(pair);
            }
            Term::Triv { level } => {
                self.tag(tag::E_TRIV);
                self.level(level);
            }
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                self.tag(tag::E_ELIMEMPTY);
                self.level(level);
                self.level(scrut_level);
                self.ty(motive);
                self.term(scrut);
            }
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
                self.tag(tag::E_INL);
                self.level(lhs_level);
                self.level(rhs_level);
                self.ty(lhs);
                self.ty(rhs);
                self.term(val);
            }
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
                self.tag(tag::E_INR);
                self.level(lhs_level);
                self.level(rhs_level);
                self.ty(lhs);
                self.ty(rhs);
                self.term(val);
            }
            Term::Case {
                lhs_level,
                rhs_level,
                motive_level,
                lhs,
                rhs,
                motive,
                case_l,
                case_r,
                scrut,
            } => {
                self.tag(tag::E_CASE);
                self.level(lhs_level);
                self.level(rhs_level);
                self.level(motive_level);
                self.ty(lhs);
                self.ty(rhs);
                self.ty(motive);
                self.term(case_l);
                self.term(case_r);
                self.term(scrut);
            }
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
                self.tag(tag::E_SUP);
                self.level(shape_level);
                self.level(pos_level);
                self.ty(shape_ty);
                self.ty(pos_ty);
                self.term(label);
                self.term(children);
            }
            Term::ElimW {
                shape_level,
                pos_level,
                motive_level,
                shape,
                pos,
                motive,
                step,
                scrut,
            } => {
                self.tag(tag::E_ELIMW);
                self.level(shape_level);
                self.level(pos_level);
                self.level(motive_level);
                self.ty(shape);
                self.ty(pos);
                self.ty(motive);
                self.term(step);
                self.term(scrut);
            }
            Term::Supf { level, shape, arity, label, children } => {
                self.tag(tag::E_SUPF);
                self.level(level);
                self.ty(shape);
                self.term(arity);
                self.term(label);
                self.term(children);
            }
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                self.tag(tag::E_ELIMWF);
                self.level(level);
                self.level(motive_level);
                self.ty(shape);
                self.term(arity);
                self.ty(motive);
                self.term(step);
                self.term(scrut);
            }
            Term::Lam { dom_level, cod_level, dom, body } => {
                self.tag(tag::E_LAM);
                self.level(dom_level);
                self.level(cod_level);
                self.ty(dom);
                self.term(body);
            }
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
                self.tag(tag::E_APP);
                self.term(fun);
                self.level(dom_level);
                self.level(cod_level);
                self.ty(dom);
                self.ty(cod);
                self.term(arg);
            }
            Term::ULam { num_vars, level, body } => {
                self.tag(tag::E_ULAM);
                self.u32(*num_vars);
                self.level(level);
                self.term(body);
            }
            Term::UApp { fun, levels } => {
                self.tag(tag::E_UAPP);
                self.term(fun);
                self.seq_len(levels.len());
                for l in levels {
                    self.level(l);
                }
            }
            // Reference site 1 of 5.
            Term::GlobalTm { var, subst } => {
                self.tag(tag::E_GLOBAL);
                self.global(var.0);
                self.subst(subst);
            }
            Term::CtxLam { level, body } => {
                self.tag(tag::E_CTXLAM);
                self.level(level);
                self.term(body);
            }
            Term::CtxApp { fun, ctx } => {
                self.tag(tag::E_CTXAPP);
                self.term(fun);
                self.ctx(ctx);
            }
            Term::TyLam { ctx, arg_level, body_level, body } => {
                self.tag(tag::E_TYLAM);
                self.ctx(ctx);
                self.level(arg_level);
                self.level(body_level);
                self.term(body);
            }
            Term::TyApp { fun, arg } => {
                self.tag(tag::E_TYAPP);
                self.term(fun);
                self.ty(arg);
            }
            Term::BoxTy(t) => {
                self.tag(tag::E_BOXTY);
                self.ty(t);
            }
            Term::BoxTm(t) => {
                self.tag(tag::E_BOXTM);
                self.term(t);
            }
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                self.tag(tag::E_LETBOXTY);
                self.level(motive_level);
                self.level(code_level);
                self.ctx(ctx);
                self.ty(motive);
                self.term(body);
                self.term(scrut);
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
                self.tag(tag::E_LETBOXTM);
                self.level(motive_level);
                self.level(code_level);
                self.ctx(ctx);
                self.ty(ty);
                self.ty(motive);
                self.term(body);
                self.term(scrut);
            }
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                scrut,
            } => {
                self.tag(tag::E_ELIMCODETY);
                self.level(ty_motive_level);
                self.level(tm_motive_level);
                self.motives(motives);
                self.branches(branches);
                self.level(code_level);
                self.ctx(ctx);
                self.term(scrut);
            }
            Term::ElimCodeTm {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                ty,
                scrut,
            } => {
                self.tag(tag::E_ELIMCODETM);
                self.level(ty_motive_level);
                self.level(tm_motive_level);
                self.motives(motives);
                self.branches(branches);
                self.level(code_level);
                self.ctx(ctx);
                self.ty(ty);
                self.term(scrut);
            }
        }
    }

    fn motives(&mut self, m: &Motives) {
        let Motives { ty_motive, tm_motive } = m;
        self.tag(tag::MOTIVES);
        self.ty(ty_motive);
        self.ty(tm_motive);
    }

    /// All 52 branches of the mutual code recursors, in declaration order.
    ///
    /// Destructured without `..` deliberately: `fmt`'s `Debug` for this struct
    /// prints only 37 of the fields, which is precisely the defect the v1
    /// rendering-based identity inherited (module docs, §Totality). A new
    /// branch must break this build.
    fn branches(&mut self, b: &Branches) {
        let Branches {
            ty_nat,
            ty_pi,
            ty_ty,
            ty_el,
            ty_id,
            ty_sigma,
            ty_unit,
            ty_empty,
            tm_var,
            tm_nat,
            tm_pi,
            tm_ty,
            tm_zero,
            tm_succ,
            tm_elim_nat,
            tm_lam,
            tm_app,
            tm_id,
            tm_refl,
            tm_j,
            tm_sigma,
            tm_pair,
            tm_fst,
            tm_snd,
            tm_unit,
            tm_empty,
            tm_triv,
            tm_elim_empty,
            ty_sum,
            tm_sum,
            tm_inl,
            tm_inr,
            tm_case,
            ty_w,
            tm_w,
            tm_sup,
            tm_elim_w,
            ty_vec,
            tm_vec,
            ty_fin,
            tm_fin,
            ty_wf,
            tm_wf,
            tm_supf,
            tm_elim_wf,
            ty_seq,
            tm_seq,
            ty_sempty,
            tm_sempty,
            tm_srefl,
            tm_transp,
            tm_elim_sempty,
        } = b;
        self.tag(tag::BRANCHES);
        for t in [
            ty_nat,
            ty_pi,
            ty_ty,
            ty_el,
            ty_id,
            ty_sigma,
            ty_unit,
            ty_empty,
            tm_var,
            tm_nat,
            tm_pi,
            tm_ty,
            tm_zero,
            tm_succ,
            tm_elim_nat,
            tm_lam,
            tm_app,
            tm_id,
            tm_refl,
            tm_j,
            tm_sigma,
            tm_pair,
            tm_fst,
            tm_snd,
            tm_unit,
            tm_empty,
            tm_triv,
            tm_elim_empty,
            ty_sum,
            tm_sum,
            tm_inl,
            tm_inr,
            tm_case,
            ty_w,
            tm_w,
            tm_sup,
            tm_elim_w,
            ty_vec,
            tm_vec,
            ty_fin,
            tm_fin,
            ty_wf,
            tm_wf,
            tm_supf,
            tm_elim_wf,
            ty_seq,
            tm_seq,
            ty_sempty,
            tm_sempty,
            tm_srefl,
            tm_transp,
            tm_elim_sempty,
        ] {
            self.term(t);
        }
    }

    /// One binding as its **interface** — which is simply the binding as Ψ
    /// stores it, because Ψ already implements the interface split: a
    /// `theorem` is pushed with `body: None`, a `fn` with its body
    /// (`docs/cache-v1-design.md` §4).
    fn binding(&mut self, b: &GlobalBinding) {
        match b {
            GlobalBinding::Ctx => self.tag(tag::B_CTX),
            GlobalBinding::Ty { ctx, layer, level } => {
                self.tag(tag::B_TY);
                self.ctx(ctx);
                self.layer(*layer);
                self.level(level);
            }
            GlobalBinding::Tm { ctx, layer, ty, level, body } => {
                self.tag(tag::B_TM);
                self.ctx(ctx);
                self.layer(*layer);
                self.ty(ty);
                self.level(level);
                // Opaque-vs-transparent is part of the interface: a `fn`'s
                // body is δ-visible downstream, a `theorem`'s is not.
                match body {
                    None => self.tag(tag::BODY_NONE),
                    Some(t) => {
                        self.tag(tag::BODY_SOME);
                        self.term(t);
                    }
                }
            }
        }
    }
}

/// The interface hash of the binding that will sit at absolute index
/// `prefix.len()`, given the interface hashes of everything before it.
///
/// `None` means "not hashable" — a reference this module could not resolve —
/// and every caller treats that as "do not cache", never as an error.
pub fn interface_hash(prefix: &Prefix, b: &GlobalBinding) -> Option<Hash> {
    let mut w = Walk::new(DOMAIN_IFACE, prefix, prefix.len() as u32);
    w.binding(b);
    w.finish()
}

/// The cache identity of one kernel gate: "the kernel accepted *this* proof of
/// *this* interface, in a context whose interfaces hash thus".
///
/// The proof term is here and not in a theorem's interface hash, which is the
/// whole of the red-green rule (`docs/cache-v1-design.md` §5): editing a proof
/// moves this and nothing else; editing a statement moves this *and* the
/// interface, hence every dependent's key.
///
/// A **transparent** declaration needs nothing beyond its interface hash: a
/// `fn`'s body is already in there, because it is δ-visible downstream. So
/// only a theorem pays a second walk, and the total walking cost of a
/// declaration is its own content exactly once.
pub fn check_key(prefix: &Prefix, body: &Term, opaque: bool, iface: &Hash) -> Option<Hash> {
    let mut w = Walk::new(DOMAIN_CHECK, prefix, prefix.len() as u32);
    w.buf.extend_from_slice(iface);
    if !opaque {
        w.tag(tag::KEY_DEF);
        return w.finish();
    }
    w.tag(tag::KEY_PROOF);
    w.term(body);
    w.finish()
}

/// The walker applied to a bare term, at an explicit Ψ length.
///
/// Test support (`tests/merkle.rs`), and the reason it exists rather than the
/// canaries going through [`interface_hash`]: the reference sites live in
/// terms, types, contexts and substitution tails, and a canary wants to place
/// one *exactly* where it means to and ask whether the hash moved. Wrapping
/// each fixture in a `GlobalBinding` would work but would test the wrapper.
///
/// Uses the interface domain; it is not a key of anything.
#[doc(hidden)]
pub fn term_hash(prefix: &Prefix, len: u32, t: &Term) -> Option<Hash> {
    let mut w = Walk::new(DOMAIN_IFACE, prefix, len);
    w.term(t);
    w.finish()
}
