//! Tier-0 inductive declarations: the lowering to sums-of-Σs.
//!
//! This module is the mechanization of `docs/inductive-tier0-lowering.md`, and
//! is meant to be read against it — the section numbers in the comments are
//! that document's. The doctrine (issues/inductive-compiler.md): the lowering
//! is *untrusted* like the rest of the elaborator (the kernel re-checks every
//! emitted declaration), but unlike the rest of the elaborator a bug here
//! produces a checked theorem about the wrong type rather than a rejection.
//! Hence: no clever shortcuts, one function per numbered rule, and the
//! annotations always read off the type being eliminated rather than rebuilt.
//!
//! Tier 1 (recursive, branching) shares this module: its shape is *this*
//! lowering with the recursive fields deleted, and the `Wf` former wraps it
//! (`docs/inductive-tier1-wf-lowering.md`, mechanized in `wf.rs`). Sharing
//! `lower_ctor`/`spine`/`const_case_tree` between the tiers is deliberate —
//! it is what makes a divergence in payload handling impossible rather than
//! merely unlikely.
//!
//! Tier 2 (a recursive *function* field, `k: A -> D`) shares it the same way:
//! the shape is again this lowering with the recursive fields deleted, and the
//! `W` former plus a leaf predicate wraps it
//! (`docs/inductive-tier2-w-lowering.md`, mechanized in `infinitary.rs`).
//!
//! Not here yet: nested recursion (`Rose`). It is classified and rejected,
//! not mis-lowered.

use std::borrow::{Borrow, Cow};
use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Arm, CtorDecl, Expr, ExprKind, InductiveDecl, MatchForm, Span, Ty, TyKind};

use crate::names::{NameKind, Scope, qkey};
use crate::stats::decline;
use crate::{Alias, Cx, Elaborator, R, TyVar, embed, err};

type Equation = (Term, Type, Level, Rc<Term>, Rc<Term>);
type CtorEquation = (
    Term,
    Rc<Inductive>,
    Type,
    Level,
    Rc<Term>,
    Rc<Term>,
    (usize, Vec<Rc<Term>>),
    (usize, Vec<Rc<Term>>),
);

/// A constructor shell whose plain recursive children have yet to be checked.
/// Expressions stay borrowed from the caller's surface tree.
struct PreparedCtor<'a> {
    term: Term,
    children: Vec<&'a Expr>,
    container: Option<(&'a Expr, Rc<Term>)>,
}

struct CtorWorkFrame<'a> {
    prepared: PreparedCtor<'a>,
    children: Term,
    tail_len: Term,
}

/// A declared inductive, kept in surface form: the field types are lowered
/// afresh at each instantiation, since type parameters are monomorphized
/// (§2 — `Option<Nat>` and `Option<Bool>` are unrelated kernel types).
pub(crate) struct Inductive {
    pub name: String,
    /// The name-resolution environment in which the stored surface field and
    /// value-parameter types were declared. Re-lowering those nodes at a use
    /// site must mean what they meant here, regardless of later imports.
    pub scope: Rc<Scope>,
    /// The nominal tag (§3.3): sequential per elaborator, carried as the first
    /// field of every constructor (see [`tag_type`]) so that structurally
    /// identical declarations do not share a kernel type.
    pub tag: u32,
    pub params: Vec<String>,
    /// `record R(p: Prog, env: Val)` — value parameters, kept in surface form
    /// for the same reason the field types are: they are elaborated afresh in
    /// the *ambient* context at every use site
    /// (docs/surface-value-parameters.md §2). Each one's type may mention the
    /// value parameters before it, so the list is a telescope.
    ///
    /// Empty for every declaration without the `(…)` list, which is the state
    /// every check below degenerates to.
    pub valparams: Vec<(String, Ty)>,
    /// `class Semigroup<A>(op as ∙: A -> A -> A)` — the **body spellings** the
    /// value parameters install, as (symbol, value-parameter name) in written
    /// order (issues/binder-symbol-as-notation.md).
    ///
    /// Kept beside [`Self::valparams`] rather than inside it because it is a
    /// different thing about the same binder: the identifier is the
    /// *interface* spelling — what a constraint slot links to, what a call
    /// site passes, what every diagnostic says — and the symbol is the *body*
    /// spelling, live only while this declaration's own field types are
    /// lowered. Empty for every declaration whose head writes no `as`, which
    /// is every one written before this grammar existed, and empty by
    /// construction for a `record` (the parser refuses `as` there).
    pub op_symbols: Vec<(String, String)>,
    pub ctors: Vec<Ctor>,
    /// Tier 1: some constructor has a recursive field, so the lowering is
    /// `Wf^l(x : S). n` rather than the bare sum-of-Σs `S`
    /// (`docs/inductive-tier1-wf-lowering.md` §1). Computed once, at
    /// declaration time; every tier-1 branch below is guarded by it.
    pub recursive: bool,
    /// Declared with `record` (docs/surface-records.md §2): exactly one
    /// constructor, every field named. The lowering is unchanged — this is
    /// what makes `m.f` a projection and `D { … }` a literal.
    pub is_record: bool,
    /// An indexed family's index binder name (`inductive Vec<A> : (n: Nat) ->
    /// Type`) (docs/inductive-indexed-lowering.md §2). When set, the
    /// declaration lowers by recursion on the index (`indexed.rs`), **never**
    /// onto `Wf` — every `recursive`-guarded branch must check this first.
    pub index: Option<String>,
    /// What the index is a value of: `Nat`, or a previously declared
    /// inductive (§8.2). `Some` exactly when [`Self::index`] is.
    pub index_ty: Option<IdxTy>,
    /// Route 2b (`docs/inductive-fording-lowering.md` §4): the **skeleton** —
    /// this declaration with every index erased, lowered by the unindexed
    /// tiers verbatim. `Some` exactly for a forded family, and it is what
    /// makes "route 1 or route 2b" one test rather than a flag.
    ///
    /// Built once, from the declaration, at declaration time, and never edited
    /// afterwards (§14.6: two skeletons, one declaration).
    pub skel: Option<Rc<Inductive>>,
}

/// The type an indexed declaration is indexed **by**
/// (docs/inductive-indexed-lowering.md §2, §8.2). The scheme is not
/// `Nat`-specific — "one family branch per index constructor, `rec` at each
/// recursive argument of the index constructor" — so what varies between the
/// two is only which eliminator carries the family: `elim_Nat`, a `Case` tree
/// (a non-recursive declared index), or `elim_Wf` (a recursive one).
pub(crate) enum IdxTy {
    Nat,
    /// A declared inductive with no parameters and no index of its own.
    Decl(Rc<Inductive>),
}

/// One index-type constructor, as the indexed lowering reads it: its name and
/// which of its arguments are *recursive* occurrences of the index type. The
/// recursive ones are the only positions a recursive family field may sit at
/// (§8.2's generalization of condition 2) — at an enum index there are none,
/// and that is what makes recursion inexpressible there rather than wrong.
pub(crate) struct IdxCtor {
    pub name: String,
    pub rec: Vec<bool>,
}

impl IdxTy {
    /// `Nat`'s constructors are the primitive `Zero`/`Succ`; a declared
    /// index's are its own, with a `Plain` field being the recursive argument.
    pub fn ctors(&self) -> Vec<IdxCtor> {
        match self {
            IdxTy::Nat => vec![
                IdxCtor {
                    name: "Zero".into(),
                    rec: vec![],
                },
                IdxCtor {
                    name: "Succ".into(),
                    rec: vec![true],
                },
            ],
            IdxTy::Decl(i) => i
                .ctors
                .iter()
                .map(|c| IdxCtor {
                    name: c.name.clone(),
                    rec: c.kind.iter().map(|k| *k == FieldKind::Plain).collect(),
                })
                .collect(),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            IdxTy::Nat => "Nat",
            IdxTy::Decl(i) => &i.name,
        }
    }
}

impl Inductive {
    /// Tier 2: some constructor has a recursive function field, so the
    /// lowering is `Σ(t : W₀). El(canon t)` (docs/inductive-tier2-w-lowering.md
    /// §5) and [`Self::recursive`] — which means "lowered onto `Wf`" — is false.
    /// Derived from the field kinds, so it needs no storage of its own.
    pub fn infinitary(&self) -> bool {
        self.ctors
            .iter()
            .any(|c| c.kind.contains(&FieldKind::FnChild))
    }

    /// The index of field `name` in this record's single constructor, or
    /// `None`. Always `None` for a non-record: an `inductive`'s field names
    /// are positional and are not accessors.
    pub fn field_index(&self, name: &str) -> Option<usize> {
        if !self.is_record {
            return None;
        }
        self.ctors[0]
            .fields
            .iter()
            .position(|(n, _)| n.as_deref() == Some(name))
    }
}

/// The per-field implicitness skeletons an arm's binder aliases carry
/// (docs/implicit-binders-design.md §3.1), aligned with the Σ walk — which
/// is only the declaration order when the constructor has no children, so a
/// ctor with any recursive field gets none rather than a misaligned table.
fn arm_field_skels(ind: &Inductive, j: usize) -> Vec<Option<Rc<crate::Skel>>> {
    let ctor = &ind.ctors[j];
    if ctor.kind.iter().any(|k| k.is_child()) {
        return Vec::new();
    }
    ctor.fields
        .iter()
        .map(|(_, t)| crate::skel_of_ty(t))
        .collect()
}

pub(crate) struct Ctor {
    pub name: String,
    /// `(optional field name, field type)`. A named field is in scope in the
    /// types of the fields after it, which is why the spine is a Σ.
    pub fields: Vec<(Option<String>, Ty)>,
    /// Parallel to [`Self::fields`]: what each one contributes
    /// (`docs/container-fields.md` §3.1). Neither recursive kind is part of
    /// the shape — both are children in the `Vec` — so both are skipped by
    /// every payload walk here and reappear only in `wf.rs`.
    pub kind: Vec<FieldKind>,
    /// An indexed declaration's result index pattern
    /// (docs/inductive-indexed-lowering.md §2): `Some` exactly when the
    /// declaration has an index telescope. `None` everywhere else.
    pub res: Option<IdxPat>,
    /// Parallel to [`Self::fields`]: at a recursive field of an indexed
    /// declaration, which *argument of the result index's constructor* the
    /// field sits at — the position whose `rec` the recursion draws from
    /// (§8.2). `None` at every other field, and at every field of an
    /// unindexed declaration.
    ///
    /// Route 2b reads this slot differently, and deliberately: at a **child**
    /// it is the surface position of that child's *index variable* field
    /// (`docs/inductive-fording-lowering.md` §3.2, F1) — the field `μ`
    /// recomputes and the eliminator binds. The two meanings never meet,
    /// because a declaration is on exactly one route.
    pub rec_at: Vec<Option<usize>>,
    /// Route 2b: the constructor's **written result index**
    /// (`docs/inductive-fording-lowering.md` §2), any expression at the index
    /// type over this constructor's child-index and payload fields. `None` on
    /// route 1 (where [`Self::res`] carries the pattern instead) and on every
    /// unindexed declaration.
    pub res_expr: Option<Expr>,
    /// Parallel to [`Self::fields`]: a record field's default
    /// (`name: T := e`), what fills it when a construction leaves it out.
    /// It has no positional slot (docs/named-arguments-design.md §9.2).
    pub defaults: Vec<Option<Expr>>,
}

/// A constructor's result index, decomposed: depth-one, constructor-headed,
/// linear (docs/inductive-indexed-lowering.md §3). Everything else was
/// rejected at declaration time.
///
/// `Nat`'s constructors are numbered as [`IdxTy::ctors`] lists them —
/// `Zero` is 0, `Succ` is 1 — so nothing below has to special-case the
/// primitive index.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct IdxPat {
    /// Which constructor of the index type heads the result index.
    pub ctor: usize,
    /// For each argument of that constructor, the position among *this*
    /// constructor's surface fields of the pattern variable filling it. Those
    /// fields are the index, not payload ([`FieldKind::IndexVar`]).
    pub vars: Vec<usize>,
}

/// What a constructor field contributes to the lowering.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum FieldKind {
    /// Any type not mentioning `D`: a Σ component of the shape.
    Payload,
    /// `D` itself, uniform and direct (tier 1 §1): exactly one child.
    Plain,
    /// `[D; len]` (`docs/container-fields.md` §3.1): `len` children, where
    /// `len_payload` is the *payload* index of the `Nat` field naming the
    /// length. At most one per constructor, last among the child-contributing
    /// fields.
    Container { len_payload: usize },
    /// An indexed constructor's pattern variable
    /// (docs/inductive-indexed-lowering.md §4.1): the field named by the
    /// result index. It is **not stored** — the branch's `elim_Nat` binder is
    /// what it denotes — so it is neither payload nor child.
    IndexVar,
    /// `(y: A) -> D` — a recursive **function** field
    /// (docs/inductive-tier2-w-lowering.md §1): one child per inhabitant of
    /// `A`. Its presence puts the whole declaration on tier 2, the `W`
    /// lowering (`infinitary.rs`), where a [`FieldKind::Plain`] child is the
    /// `Unit`-positioned case of the same thing.
    FnChild,
}

impl FieldKind {
    pub fn is_child(self) -> bool {
        !matches!(self, FieldKind::Payload)
    }
}

impl Ctor {
    /// How many **plain** children this constructor carries: the `kᵢ` of
    /// `docs/container-fields.md` §3.3. Without a container field this is the
    /// whole arity (tier 1's `mᵢ`); with one, the arity is
    /// `Succ^{kᵢ}(len)` and only these `kᵢ` are reachable by a literal index.
    pub fn arity(&self) -> usize {
        self.kind.iter().filter(|k| **k == FieldKind::Plain).count()
    }

    /// This constructor's container field, if it has one: its index among the
    /// surface fields, and the payload index of its length.
    pub fn container(&self) -> Option<(usize, usize)> {
        self.kind.iter().enumerate().find_map(|(k, f)| match f {
            FieldKind::Container { len_payload } => Some((k, *len_payload)),
            _ => None,
        })
    }

    /// The payload fields — everything the *shape* carries — in declaration
    /// order, paired with their index among the surface fields. An
    /// [`FieldKind::IndexVar`] is not payload either: it is the index, and
    /// storing it is exactly what the indexed scheme exists to avoid
    /// (docs/inductive-indexed-lowering.md §4.1).
    pub fn payload(&self) -> impl Iterator<Item = (usize, &(Option<String>, Ty))> {
        self.fields
            .iter()
            .enumerate()
            .filter(|(k, _)| matches!(self.kind[*k], FieldKind::Payload))
    }
}

/// A kernel type read back as a tag spine (§3.2). Everything the constructor
/// and `match` lowerings need is here, taken from the type itself rather than
/// regenerated, so the annotations cannot drift from what is being eliminated.
pub(crate) struct Spine {
    /// `(⟦c_i⟧, its level)` for each constructor.
    pub ctors: Vec<(Rc<Type>, Level)>,
    /// `(R_{i+1}, its level)` — the right operand of the `i`-th `+`, for
    /// `i < n-1`.
    pub tails: Vec<(Rc<Type>, Level)>,
}

/// The nominal tag *type* for declaration `k` (§3.3): the strict equality
/// `sEq⁰(Nat; k; k)`, with `k` spelled by [`nat_lit`] and nothing else.
///
/// Three properties, and the tag needs all of them:
///
/// - **Distinct per declaration.** Type conversion compares an `sEq`'s
///   endpoints, and irrelevance collapses proofs, never endpoints
///   (docs/sprop-design.md §7), so different `k` are different types.
/// - **Proof-irrelevant.** Any two terms at an `sEq` type are convertible
///   (the `conv.rs` irrelevance arm). This is what a dependent motive needs:
///   an arm's binder `x : ⟦c_i⟧` is neutral, and the motive puts it back
///   together as `inl x`, which must still be convertible with the canonical
///   `inl (pair srefl ⟨⟩)`. An `Id`-based tag fails exactly here — `Id` has no
///   η, so a neutral `fst x` is not convertible with `refl`.
/// - **One spelling.** Boxed code compares syntactically, so a tag spelled
///   `Succ^k(Zero)` in one place and `NatLit(k)` in another would give one
///   declaration two codes. [`nat_lit`] is the only spelling, and
///   [`read_tag`] reads no other.
///
/// Until 2026-09-26 the tag was `k`'s binary digits as a right-nested Σ of
/// `Unit`s, irrelevant by *derivation*: Σ-η projected its way down the nest
/// on every comparison of two values, which was most of what comparing
/// declared-inductive data cost (`issues/nominal-tag-conversion-cost.md`).
pub(crate) fn tag_type(k: u32) -> Type {
    let k = Rc::new(nat_lit(k as usize));
    Type::SEq {
        level: Level::Zero,
        ty: Rc::new(Type::Nat),
        lhs: Rc::clone(&k),
        rhs: k,
    }
}

/// A tag index as [`tag_type`] spells it: `Zero` or a compact literal.
fn tag_index(t: &Term) -> Option<u32> {
    match t {
        Term::Zero => Some(0),
        Term::NatLit(k) if !k.is_zero() => k.as_u64().and_then(|k| u32::try_from(k).ok()),
        _ => None,
    }
}

/// Read a tag type back to its declaration index — the inverse of [`tag_type`].
fn read_tag(t: &Type) -> Option<u32> {
    match &*decoded(t) {
        Type::SEq { ty, lhs, rhs, .. } if matches!(*decoded(ty), Type::Nat) => {
            let k = tag_index(lhs)?;
            (tag_index(rhs)? == k).then_some(k)
        }
        _ => None,
    }
}

/// A lowered type's **structural** view, looking through `El` of a code.
///
/// `El ⌜T⌝ ⇝ T` is a *lazy* decode in the kernel: decoding a code former
/// leaves each child still `El`-wrapped (`reduce.rs`'s `step_type`). A type
/// that reached the elaborator through a δ-transparent type abbreviation —
/// `Refines(p, i, q, j)` elaborated as `El` of a `fn` call
/// (`docs/types-as-expressions.md`) — is therefore `El`-headed at *every*
/// level below the first, and the readers above (`spine`, `tag_of`,
/// `read_tag`) would otherwise see a code where they expect a `Σ`. So every
/// structural step goes through this.
///
/// Context-free on purpose, and that is what makes the empty local context
/// sound: the guard admits only an `El` whose code is a **canonical former**,
/// and those rules of `step_type` are pure rewrites that never consult
/// `gamma` or δ. An `El` of a *neutral* code (an unapplied abbreviation, a
/// variable at `Type<n>`) is left exactly as it is — unfolding that is
/// conversion's job, lazily, not this walk's.
pub(crate) fn decoded(t: &Type) -> Cow<'_, Type> {
    fn is_code_former(t: &Term) -> bool {
        matches!(
            t,
            Term::TmNat
                | Term::TmTy(_)
                | Term::TmPi { .. }
                | Term::TmId { .. }
                | Term::TmSigma { .. }
                | Term::TmUnit { .. }
                | Term::TmEmpty { .. }
                | Term::TmSum { .. }
                | Term::TmW { .. }
                | Term::TmVec { .. }
                | Term::TmFin { .. }
                | Term::TmWf { .. }
                | Term::TmSEq { .. }
        )
    }
    let empty = LocalCtx::nil();
    let mut cur = Cow::Borrowed(t);
    loop {
        let next = match &*cur {
            Type::El { tm, .. } if is_code_former(tm) => {
                match heather_kernel::reduce::step_type(&cur, &empty) {
                    Ok(Some(next)) => next,
                    Ok(None) | Err(_) => break,
                }
            }
            _ => break,
        };
        cur = Cow::Owned(next);
    }
    cur
}

/// [`decoded`] pushed through every **type** component: the fully inline
/// spelling of a type the kernel's lazy decode handed back one level at a
/// time. `None` when nothing was a code literal, so callers keep their
/// original and its sharing.
///
/// For **emitted annotations** only (issues/emission-site-respell-audit.md).
/// A record type that arrives as `El ⌜Σ…⌝` — the quote of a `→ Type` body,
/// or a type argument — whnf's to `Σ(El ⌜A⌝). El ⌜B⌝`, and a projection
/// chain that writes those components verbatim spells every `snd_ty` as the
/// *un*decoded literal of a tail whose own annotations, one node down, are
/// its decode: the kernel then evaluates the whole literal at every link
/// (`MachineState<M>`'s 216 K-character instance, 154 queries of the
/// five-node FunctionIR/x86 module, 2026-09-06). Spelled inline at every
/// link, adjacent links compare syntactically. Terms inside types — `El`
/// of a *neutral* code, `Id` endpoints, `Vec` lengths — are left as they
/// are: decoding is a rewrite on canonical formers only, exactly
/// [`decoded`]'s guard.
///
/// The property the adjacent-link argument rests on — this decode commutes
/// with local substitution — is a kernel law, tested against `step_type`
/// directly on random terms in `crates/kernel/tests/decode_laws.rs`.
pub(crate) fn decode_deep(t: &Type) -> Option<Type> {
    let head = decoded(t);
    let changed_head = matches!(head, Cow::Owned(_));
    let or = |orig: &Rc<Type>, new: Option<Type>| match new {
        Some(t) => Rc::new(t),
        None => Rc::clone(orig),
    };
    let rebuilt = match &*head {
        Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } => {
            let nd = decode_deep(dom);
            let nc = decode_deep(cod);
            (nd.is_some() || nc.is_some()).then(|| Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: or(dom, nd),
                cod: or(cod, nc),
            })
        }
        Type::Sigma {
            fst_level,
            snd_level,
            fst,
            snd,
        } => {
            let nf = decode_deep(fst);
            let ns = decode_deep(snd);
            (nf.is_some() || ns.is_some()).then(|| Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: or(fst, nf),
                snd: or(snd, ns),
            })
        }
        Type::Sum {
            lhs_level,
            rhs_level,
            lhs,
            rhs,
        } => {
            let nl = decode_deep(lhs);
            let nr = decode_deep(rhs);
            (nl.is_some() || nr.is_some()).then(|| Type::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: or(lhs, nl),
                rhs: or(rhs, nr),
            })
        }
        Type::Vec { level, elem, len } => decode_deep(elem).map(|ne| Type::Vec {
            level: level.clone(),
            elem: Rc::new(ne),
            len: Rc::clone(len),
        }),
        Type::Wf {
            level,
            shape,
            arity,
        } => {
            // The arity goes with the shape: its constant case tree's `Case`
            // annotations are the shape's own components, and a respell
            // downstream (`respell_ty_deep`'s `Wf` arm) treats the two as one
            // spelling, so a decoded shape over literal-spelled annotations
            // would be the very mismatch that arm exists to avoid.
            let ns = decode_deep(shape);
            let na = decode_arity_deep(arity);
            (ns.is_some() || na.is_some()).then(|| Type::Wf {
                level: level.clone(),
                shape: or(shape, ns),
                arity: match na {
                    Some(a) => Rc::new(a),
                    None => Rc::clone(arity),
                },
            })
        }
        Type::Id {
            level,
            ty,
            lhs,
            rhs,
        } => decode_deep(ty).map(|nt| Type::Id {
            level: level.clone(),
            ty: Rc::new(nt),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        }),
        Type::SEq {
            level,
            ty,
            lhs,
            rhs,
        } => decode_deep(ty).map(|nt| Type::SEq {
            level: level.clone(),
            ty: Rc::new(nt),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        }),
        Type::Squash { level, ty } => decode_deep(ty).map(|nt| Type::Squash {
            level: level.clone(),
            ty: Rc::new(nt),
        }),
        _ => None,
    };
    match (rebuilt, changed_head) {
        (Some(t), _) => Some(t),
        (None, true) => Some(head.into_owned()),
        (None, false) => None,
    }
}

/// [`decode_deep`] over the `Case` annotations of a `Wf` arity's constant
/// case tree (the form `lower_arity` writes); any other term is left as it
/// is. `None` when nothing changed.
fn decode_arity_deep(t: &Term) -> Option<Term> {
    match t {
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
            let nl = decode_deep(lhs);
            let nr = decode_deep(rhs);
            let cl = decode_arity_deep(case_l);
            let cr = decode_arity_deep(case_r);
            if nl.is_none() && nr.is_none() && cl.is_none() && cr.is_none() {
                return None;
            }
            Some(Term::Case {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                motive_level: motive_level.clone(),
                lhs: nl.map_or_else(|| Rc::clone(lhs), Rc::new),
                rhs: nr.map_or_else(|| Rc::clone(rhs), Rc::new),
                motive: Rc::clone(motive),
                case_l: cl.map_or_else(|| Rc::clone(case_l), Rc::new),
                case_r: cr.map_or_else(|| Rc::clone(case_r), Rc::new),
                scrut: Rc::clone(scrut),
            })
        }
        Term::Succ(p) => decode_arity_deep(p).map(|np| Term::Succ(Rc::new(np))),
        _ => None,
    }
}

/// The injection path into a tag spine (§3.2/§4): `Inl` unless this is the
/// last constructor, under `i` `Inr`s. `d` weakens the spine's components,
/// which are scoped where the spine was read back — 0 at a constructor, and
/// however many binders the step's case tree has pushed inside `match`.
pub(crate) fn inject(spine: &Spine, i: usize, n: usize, val: Term, d: u32) -> Term {
    inject_at(spine, i, n, val, d, None)
}

/// [`inject`] with the **checked spelling** at its outermost layer
/// (`docs/intro-by-type-design.md` §4.1): `at` is the un-reduced type the
/// whole injection was checked at — `build_ctor`'s `pre_whnf` — and replaces
/// that layer's `lhs`/`rhs`, which are the two summands of its whnf.
///
/// Only the outermost layer takes it, and the reason is that the inner layers
/// have no un-reduced spelling: layer `j+1`'s type is layer `j`'s whnf's
/// *right* summand, and a selection of a component is a checker-internal
/// `ITy::Sel`, not syntax (§3.2). So the inner layers are **unannotated**
/// checked spellings (§2.1): each is the value of the one above it, a
/// checking position, and the kernel checks it against a description of that
/// summand. With `at` absent every layer is the component form, as before.
pub(crate) fn inject_at(
    spine: &Spine,
    i: usize,
    n: usize,
    val: Term,
    d: u32,
    at: Option<Rc<Type>>,
) -> Term {
    // The layers, innermost first; the last one applied is the outermost and
    // is the one `at` describes.
    let mut layers: Vec<(bool, usize)> = Vec::new();
    if i + 1 < n {
        layers.push((true, i));
    }
    layers.extend((0..i).rev().map(|j| (false, j)));
    let last = layers.len().saturating_sub(1);
    let mut val = val;
    // A single-constructor declaration has no injection layer, so the tuple
    // is the outermost value and takes `at` itself: it is the one layer that
    // may meet an inferring position (a projection's receiver, a scrutinee).
    if layers.is_empty() {
        if let (Some(ty), Term::PairAt { ty: slot @ None, .. }) = (&at, &mut val) {
            *slot = Some(Rc::clone(ty));
        }
    }
    for (k, (is_inl, j)) in layers.into_iter().enumerate() {
        let outermost = k == last;
        val = match at.as_ref() {
            Some(ty) if is_inl => Term::InlAt {
                ty: outermost.then(|| Rc::clone(ty)),
                val: Rc::new(val),
            },
            Some(ty) => Term::InrAt {
                ty: outermost.then(|| Rc::clone(ty)),
                val: Rc::new(val),
            },
            None if is_inl => Term::Inl {
                lhs_level: spine.ctors[j].1.clone(),
                rhs_level: spine.tails[j].1.clone(),
                lhs: Rc::new(spine.ctors[j].0.shift_local(d)),
                rhs: Rc::new(spine.tails[j].0.shift_local(d)),
                val: Rc::new(val),
            },
            None => Term::Inr {
                lhs_level: spine.ctors[j].1.clone(),
                rhs_level: spine.tails[j].1.clone(),
                lhs: Rc::new(spine.ctors[j].0.shift_local(d)),
                rhs: Rc::new(spine.tails[j].0.shift_local(d)),
                val: Rc::new(val),
            },
        };
    }
    val
}

/// `k` as a `Nat` literal.
/// The `usize` a `Nat` literal denotes, if it is one. `Vec` reduces on the
/// whnf of its length, so "is this a literal" is exactly "can this be
/// unfolded to a Σ-chain of known width".
pub(crate) fn nat_value(t: &Term) -> Option<usize> {
    match t {
        Term::Zero => Some(0),
        Term::NatLit(n) => n.as_u64().and_then(|n| usize::try_from(n).ok()),
        Term::Succ(p) => nat_value(p).map(|k| k + 1),
        _ => None,
    }
}

/// The constructor view of a weak-head-normal natural. Compact `NatLit`
/// producers and ordinary unary syntax must be indistinguishable to surface
/// features that inspect `Vec`/`Fin` lengths.
pub(crate) enum NatHead {
    Zero,
    Succ(Rc<Term>),
    Neutral,
}

/// A closed numeral's value at any size: `Zero`, a literal, or successors of
/// one (docs/wide-numerals-design.md). [`nat_value`] is this capped at a
/// `usize`, for the readers that index with it.
pub(crate) fn nat_numeral(t: &Term) -> Option<heather_kernel::term::Numeral> {
    match t {
        Term::Zero => Some(heather_kernel::term::Numeral::ZERO),
        Term::NatLit(n) => Some(n.clone()),
        Term::Succ(p) => nat_numeral(p).map(|n| n.succ()),
        _ => None,
    }
}

pub(crate) fn nat_head(t: &Term) -> NatHead {
    match t {
        Term::Zero => NatHead::Zero,
        Term::NatLit(n) if n.is_zero() => NatHead::Zero,
        Term::Succ(pred) => NatHead::Succ(Rc::clone(pred)),
        Term::NatLit(n) => NatHead::Succ(Rc::new(heather_kernel::term::nat_lit_pred(n))),
        _ => NatHead::Neutral,
    }
}

/// A closed numeral as the kernel spells one: `Zero`, or the packed
/// `NatLit` that stands for `Succ^k(Zero)`. It was a unary `Succ` chain until
/// 2026-09-11, which made every vector-literal annotation carry its length in
/// unary and the annotated term quadratic in the literal
/// (`issues/elf-mutation-test-shape.md`).
pub(crate) fn nat_lit(k: usize) -> Term {
    if k == 0 { Term::Zero } else { Term::NatLit((k as u64).into()) }
}

/// The tag's inhabitant: `srefl⁰(Nat; k)`. Which inhabitant hardly matters —
/// the type is proof-irrelevant — but it has to be *an* inhabitant for the
/// kernel to accept the constructor.
///
/// Rebuilt from the index rather than copied off `t`: a tag type that arrived
/// as *code* decodes (through [`decoded`], docs/types-as-expressions.md) to an
/// `sEq` whose element type is still `El ⌜Nat⌝`, and copying that would put a
/// quote in every constructor value's annotation slot.
pub(crate) fn tag_value(t: &Type) -> Term {
    match read_tag(t) {
        Some(k) => Term::SRefl {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            tm: Rc::new(nat_lit(k as usize)),
        },
        None => Term::Triv { level: Level::Zero },
    }
}

impl Elaborator {
    // -- declaration --------------------------------------------------------

    /// Register an `inductive` declaration: classify its tier, check its names,
    /// and assign its nominal tag. Nothing is emitted here — an inductive has
    /// no kernel counterpart of its own; it is lowered at each use (§2).
    pub(crate) fn elab_inductive(&mut self, d: &InductiveDecl) -> R<()> {
        if self.own_declares(&d.name, &[NameKind::Inductive, NameKind::Global]) {
            return err(format!("duplicate name `{}`", d.name), d.span);
        }
        self.check_declarable(&d.name, d.span)?;
        if d.name == "Nat" {
            return err("`Nat` is built in", d.span);
        }
        reject_function_fields(d)?;
        for (i, p) in d.params.iter().enumerate() {
            if d.params[..i].contains(p) {
                return err(format!("duplicate type parameter `{p}`"), d.span);
            }
        }
        // Value parameters (docs/surface-value-parameters.md §1, §6). On a
        // `record` uniformity across constructors is free; on an `inductive`
        // it is what `classify_fields` checks at every recursive occurrence
        // (`D<p̄>(v̄)` with the declaration's own parameters, in order), so a
        // parameter is substituted at lowering and never read as an index.
        // Beside an index it stays refused: the index telescope would have to
        // be read under the parameters, and nothing asks for that yet.
        if !d.valparams.is_empty()
            && let Some(ix) = &d.index
        {
            return err(
                format!(
                    "`{}` has both value parameters and an index: the two do not combine \
                     this round. Write the uniform argument as a value parameter and drop \
                     the index, or state the varying one as the index alone \
                     (docs/surface-value-parameters.md §6)",
                    d.name
                ),
                ix.span,
            );
        }
        for (i, p) in d.valparams.iter().enumerate() {
            if d.valparams[..i].iter().any(|o| o.name == p.name) {
                return err(format!("duplicate value parameter `{}`", p.name), p.span);
            }
            // A value parameter's type is re-lowered per instantiation with
            // no skeleton slot, so an implicit mark in it has no consumer
            // (docs/implicit-binders-design.md §3.4).
            if crate::has_implicit_mark(&p.ty) {
                return err(crate::IMPLICIT_MARK_REFUSED, p.ty.span);
            }
            if d.params.contains(&p.name) {
                return err(
                    format!(
                        "`{}` is already a type parameter of `{}`: a value parameter is a \
                         term and a type parameter is a type, so one name cannot be both",
                        p.name, d.name
                    ),
                    p.span,
                );
            }
            // §5.2's uniqueness rule over the SYMBOL namespace
            // (issues/binder-symbol-as-notation.md): a declaration installs a
            // spelling once. The identifier half is the duplicate-name check
            // above — `as` adds no identifier, it adds a second *role* for the
            // one the binder already has.
            if let Some(sym) = &p.symbol
                && d.valparams[..i]
                    .iter()
                    .any(|o| o.symbol.as_deref() == Some(sym.as_str()))
            {
                return err(
                    format!(
                        "`{sym}` is already a body spelling in this head: each spelling                          binds one referent, so `{}` installs a symbol at most once                          (docs/operators-onto-classes-design.md §5.2)",
                        d.name
                    ),
                    p.span,
                );
            }
            // A field shadows a value parameter of the same name in the later
            // field types, which is legal but never what anyone means — and on
            // an `inductive` it would also make a recursive `D(p)` after it
            // name the field rather than the parameter. Every constructor.
            if let Some(c) = d.ctors.iter().find(|c| {
                c.fields
                    .iter()
                    .any(|f| f.name.as_deref() == Some(p.name.as_str()))
            }) {
                return err(
                    if d.is_record {
                        format!(
                            "`{}` is both a value parameter and a field of `{}`: the field \
                             would shadow the parameter in the field types after it",
                            p.name, d.name
                        )
                    } else {
                        format!(
                            "`{}` is both a value parameter of `{}` and a field of its \
                             constructor `{}`: the field would shadow the parameter in the \
                             field types after it",
                            p.name, d.name, c.name
                        )
                    },
                    p.span,
                );
            }
        }
        // The index telescope (docs/inductive-indexed-lowering.md §2): one
        // `Nat` binder into bare `Type`, this round. The grammar parses any
        // type; the shape is validated here so the message can say what the
        // round supports rather than "parse error".
        let (index, index_ty) = match &d.index {
            None => (None, None),
            Some(ty) => {
                let TyKind::Fn {
                    binder: Some(n),
                    implicit,
                    dom,
                    cod,
                } = &ty.kind
                else {
                    return err(
                        "an indexed declaration's head is `: (n: I) -> Type` \
                         (docs/inductive-indexed-lowering.md §2)",
                        ty.span,
                    );
                };
                if *implicit {
                    return err(crate::IMPLICIT_MARK_REFUSED, ty.span);
                }
                let ity = self.index_type(dom, &d.name)?;
                if !matches!(cod.kind, TyKind::Univ { level: 0 }) {
                    return err(
                        "an index telescope ends in bare `Type`; the family's level is \
                         computed from the fields (docs/inductive-indexed-lowering.md §2)",
                        cod.span,
                    );
                }
                if d.is_record {
                    return err(
                        format!(
                            "`{}` is a `record` and cannot be indexed: an index varies \
                             per constructor result, and a record has one constructor",
                            d.name
                        ),
                        ty.span,
                    );
                }
                if d.ctors.is_empty() {
                    return err(
                        "an indexed declaration needs at least one constructor; for an \
                         uninhabited type, declare it unindexed",
                        d.span,
                    );
                }
                (Some(n.clone()), Some(ity))
            }
        };
        // Which indexed fragment this declaration is in
        // (`docs/inductive-fording-lowering.md` §3): route 1, route 2b, or
        // neither. Computed once, before the per-constructor walk, because
        // routing is **per declaration** — a declaration with one non-route-1
        // constructor fords whole (§3, and §10's rejected route 3).
        let route = match &index_ty {
            None => None,
            Some(ity) => Some(classify_indexed_route(d, ity)?),
        };
        let mut ctors = Vec::new();
        for (i, c) in d.ctors.iter().enumerate() {
            if d.ctors[..i].iter().any(|o| o.name == c.name) {
                return err(format!("duplicate constructor `{}`", c.name), c.span);
            }
            if matches!(c.name.as_str(), "Zero" | "Succ" | "refl") {
                return err(
                    format!("`{}` is built in and cannot be a constructor name", c.name),
                    c.span,
                );
            }
            // Per *module* now (docs/modules-design.md §4): two modules may
            // each declare a `Cons`, and a use picks by uniqueness, by
            // `List::Cons`, or errors. Within one module a constructor name
            // still belongs to one type.
            if let Some((other, _)) = self.types.constructor(&qkey(self.names.module(), &c.name)) {
                return err(
                    format!("`{}` is already a constructor of `{}`", c.name, other.name),
                    c.span,
                );
            }
            if self.own_declares(&c.name, &[NameKind::Global, NameKind::Inductive]) {
                return err(format!("duplicate name `{}`", c.name), c.span);
            }
            self.check_declarable(&c.name, c.span)?;
            // The result annotation: mandatory on an indexed declaration's
            // constructors, an error elsewhere
            // (docs/inductive-indexed-lowering.md §2).
            if index.is_none()
                && let Some(r) = &c.result
            {
                return err(
                    format!(
                        "`{}` has a result annotation, but `{}` is not indexed: only \
                         an indexed declaration's constructors state their index",
                        c.name, d.name
                    ),
                    r.span,
                );
            }
            // Tier classification (tier 0 §2; tier 1 §1). With no function
            // types in field position there is no *negative* occurrence to
            // find yet, so an occurrence is either the uniform recursive one
            // — tier 1, lowered onto `Wf` — or a rejection, never a silent
            // lowering. An indexed declaration classifies by its own rules —
            // route 1's (docs/inductive-indexed-lowering.md §3) or route 2b's
            // (docs/inductive-fording-lowering.md §3.2) — and `route` already
            // decided which, for the declaration as a whole.
            let (res, res_expr, kind, rec_at) = match &route {
                None => {
                    let vnames: Vec<String> =
                        d.valparams.iter().map(|p| p.name.clone()).collect();
                    let kind = classify_fields(c, &d.name, &d.params, &vnames)?;
                    let rec_at = vec![None; kind.len()];
                    (None, None, kind, rec_at)
                }
                Some(IdxRoute::One(rows)) => {
                    let (pat, kind, rec_at) = rows[i].clone();
                    (Some(pat), None, kind, rec_at)
                }
                Some(IdxRoute::Forded(rows)) => {
                    let (e, kind, rec_at) = rows[i].clone();
                    (None, Some(e), kind, rec_at)
                }
            };
            // A default fills a record's field; a constructor of a family
            // has no construction site that could leave one out by name. An
            // unindexed constructor's `Pos<A>` field is the one default
            // elsewhere: its fact is searched as a record field's is
            // (docs/positivity-evidence-design.md §13).
            if let Some(field) = c.fields.iter().find(|f| f.default.is_some())
                && (index.is_some() || !(d.is_record || is_pos_search(field)))
            {
                if is_pos_search(field) {
                    return err(
                        format!(
                            "a `Pos<A>` field is not supported on a constructor of the indexed \
                             family `{}`: write the carrier and a `0 < …` field, passed by \
                             position",
                            d.name
                        ),
                        field.span,
                    );
                }
                return err("only a record's fields take a default (`name: T := e`)", field.span);
            }
            ctors.push(Ctor {
                name: c.name.clone(),
                fields: c
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), f.ty.clone()))
                    .collect(),
                kind,
                res,
                rec_at,
                res_expr,
                defaults: c.fields.iter().map(|f| f.default.as_deref().cloned()).collect(),
            });
        }
        // *Any* child-contributing field, not just a plain one: a constructor
        // whose only recursive field is a container has `arity() == 0` and is
        // still tier 1 (docs/container-fields.md §3.1). Getting this wrong
        // classifies `Rose` as non-recursive and silently drops its children —
        // which is the hazard class, not a rejection, so
        // `container_fields::a_container_is_not_dropped` is the observer.
        let any_child = ctors.iter().any(|c| c.kind.iter().any(|k| k.is_child()));
        // Tier 2 (docs/inductive-tier2-w-lowering.md §1): a recursive function
        // field anywhere puts the whole declaration on `W`, and `recursive`
        // keeps meaning "lowered onto `Wf`".
        let infinitary = ctors.iter().any(|c| c.kind.contains(&FieldKind::FnChild));
        let recursive = any_child && !infinitary;
        if infinitary {
            for (c, cd) in ctors.iter().zip(&d.ctors) {
                if c.container().is_some() {
                    return err(
                        format!(
                            "`{}` has a container field, and `{}` is infinitary (it has a \
                             recursive function field): the two child kinds do not mix this \
                             round (docs/inductive-tier2-w-lowering.md §1)",
                            c.name, d.name
                        ),
                        cd.span,
                    );
                }
                if c.kind.iter().filter(|k| k.is_child()).count() > 1 {
                    return err(
                        format!(
                            "`{}` has more than one recursive field, and `{}` is infinitary \
                             (it has a recursive function field): its children would be one \
                             function out of a sum, which a `match` cannot rebuild without \
                             funext. Split the constructor, or keep `{}` finitary \
                             (docs/inductive-tier2-w-lowering.md §2.2)",
                            c.name, d.name, d.name
                        ),
                        cd.span,
                    );
                }
            }
        }
        // A `record` is tier 0 by construction (docs/surface-records.md §2):
        // a recursive one is an `inductive`, and saying so is more useful than
        // silently lowering it onto `Wf` where the field names would still
        // project but the declaration would no longer be a record.
        if d.is_record && any_child {
            return err(
                format!(
                    "`{}` is a `record` but mentions itself: a recursive declaration is \
                     an `inductive` (docs/surface-records.md §2)",
                    d.name
                ),
                d.span,
            );
        }
        if d.is_record {
            let fields = &ctors[0].fields;
            for (i, (n, _)) in fields.iter().enumerate() {
                // Field names are *accessors* on a record, so a duplicate is
                // ambiguous rather than merely positional as it is on an
                // `inductive` (docs/surface-records.md §2.2).
                if fields[..i].iter().any(|(m, _)| m == n) {
                    return err(
                        format!(
                            "duplicate field `{}` in record `{}`",
                            n.as_deref().unwrap_or("_"),
                            d.name
                        ),
                        d.ctors[0].fields[i].span,
                    );
                }
            }
        }
        // Route 2b's skeleton (`docs/inductive-fording-lowering.md` §4): the
        // declaration with its indices erased, registered as an ordinary
        // declaration so that the *unindexed* tiers lower it verbatim — which
        // is §4.1's single most consequential sentence, mechanized.
        let first_tag =
            if self.names.module() == crate::PRELUDE_MODULE && d.name == "CollectionLiteral" {
                crate::types::COLLECTION_LITERAL_TAG
            } else {
                self.types.next_tag()
            };
        let skel = match &route {
            Some(IdxRoute::Forded(_)) => Some(Rc::new(skeleton_of(
                d,
                &ctors,
                first_tag,
                Rc::new(self.names.scope().clone()),
            ))),
            _ => None,
        };
        let ind = Rc::new(Inductive {
            name: d.name.clone(),
            scope: Rc::new(self.names.scope().clone()),
            tag: first_tag + u32::from(skel.is_some()),
            params: d.params.clone(),
            valparams: d
                .valparams
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect(),
            op_symbols: d
                .valparams
                .iter()
                .filter_map(|p| p.symbol.clone().map(|s| (s, p.name.clone())))
                .collect(),
            ctors,
            recursive,
            is_record: d.is_record,
            index,
            index_ty,
            skel,
        });
        // A tier-2 declaration's lowering can fail on what the declaration
        // *says* — a function domain with no code, domains at two levels
        // (docs/inductive-tier2-w-lowering.md §1.5) — so an unparameterized
        // one is lowered once here, where that is a declaration error rather
        // than a surprise at its first use.
        if ind.infinitary() && ind.params.is_empty() && ind.valparams.is_empty() {
            self.lower_instance(&Cx::empty(), &ind, &[], &[], d.span)?;
        }
        // From here on registration is infallible. The type registry installs
        // all nominal views together; the ambiguity index then exposes the
        // same declarations to surface resolution.
        let module = self.names.module().to_string();
        self.semantic_commit_inductive(module, Rc::clone(&ind));
        if let Some(skeleton) = &ind.skel {
            self.add_name(&skeleton.name, NameKind::Inductive);
        }
        for ctor in &ind.ctors {
            self.add_name(&ctor.name, NameKind::Ctor);
        }
        self.add_name(&d.name, NameKind::Inductive);
        // The generator's own artifacts become Ψ definitions here — once, at
        // declaration time, never edited afterwards (§14.6's discipline, the
        // same one the skeleton above follows). Everything the declaration
        // emits later references them; see `gendefs.rs`.
        //
        // Tier 2 names its leaf predicate and nothing else
        // (docs/inductive-tier2-w-lowering.md §13): its lowering is spelled
        // with that definition, and the rest stays inline.
        if ind.infinitary() {
            self.register_w_canon(&ind, d.span);
        } else {
            self.register_gen_defs(&ind, d.span);
        }
        Ok(())
    }

    /// The index telescope's domain (docs/inductive-indexed-lowering.md §2,
    /// §8.2): `Nat`, or a previously declared inductive that can carry a
    /// family. Each rejection below is a *shape* the scheme has no branch for,
    /// not a policy — a parameterized index would need its arguments at every
    /// use, an indexed index would need a two-level family, and a
    /// single-constructor index has one closed value and so indexes nothing.
    fn index_type(&self, dom: &Ty, name: &str) -> R<IdxTy> {
        if matches!(dom.kind, TyKind::Nat) {
            return Ok(IdxTy::Nat);
        }
        let TyKind::Named { name: iname, args } = &dom.kind else {
            return err(
                "an index is a `Nat` or a previously declared inductive \
                 (docs/inductive-indexed-lowering.md §8.2)",
                dom.span,
            );
        };
        if !args.is_empty() {
            return err(
                format!(
                    "`{iname}` is applied to type arguments; an index type is used \
                     un-parameterized, since the family's branches are built once per \
                     index constructor"
                ),
                dom.span,
            );
        }
        let Some(ind) = self.lookup_inductive(iname) else {
            return Err(self.name_miss(iname, format!("unknown index type `{iname}`"), dom.span));
        };
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return err(
                format!(
                    "`{iname}` takes parameters and cannot be an index type this round \
                     (docs/inductive-indexed-lowering.md §8.3)"
                ),
                dom.span,
            );
        }
        if ind.index.is_some() {
            return err(
                format!(
                    "`{iname}` is itself an indexed family; indexing `{name}` by it would \
                     need a family over a family, which is not this scheme \
                     (docs/inductive-indexed-lowering.md §8.3)"
                ),
                dom.span,
            );
        }
        if ind.ctors.iter().any(|c| c.container().is_some()) {
            return err(
                format!(
                    "`{iname}` has a container field (`[{iname}; n]`), so its recursive \
                     arguments are not a fixed list; an index type's constructors must \
                     have a literal arity (docs/container-fields.md §3.1)"
                ),
                dom.span,
            );
        }
        if ind.infinitary() {
            return err(
                format!(
                    "`{iname}` has a recursive function field, so its recursive \
                     arguments are not a fixed list; an index type's constructors must \
                     have a literal arity (docs/inductive-tier2-w-lowering.md §1)"
                ),
                dom.span,
            );
        }
        if ind.ctors.len() < 2 {
            return err(
                format!(
                    "`{iname}` has fewer than two constructors, so it has nothing for \
                     `{name}` to be indexed *by* — the family would have one branch"
                ),
                dom.span,
            );
        }
        Ok(IdxTy::Decl(Rc::clone(ind)))
    }

    // -- the type (§3) ------------------------------------------------------

    /// `⟦D<args>⟧` for a named type: a type parameter in scope, or a declared
    /// inductive applied to its arguments.
    pub(crate) fn lower_named(
        &self,
        cx: &Cx,
        name: &str,
        args: &[Ty],
        span: Span,
    ) -> R<(Type, Level)> {
        if let Some(p) = cx.tyvars.iter().rev().find(|p| p.name == name) {
            if !args.is_empty() {
                return err(format!("type parameter `{name}` takes no arguments"), span);
            }
            // Weaken across the binders the field spine has pushed since the
            // instantiation was lowered — the nominal tag, then each earlier
            // field (§3.1). A closed instantiation makes this a no-op, which
            // is why its absence went unnoticed
            // (issues/tyvar-scoping-in-lowered-fields.md).
            let by = (cx.names.len() - p.depth) as u32;
            return Ok((p.ty.shift_local(by), p.level.clone()));
        }
        // `True` — the kernel's `Unit^0`, the one proposition with a canonical
        // inhabitant and *judgmental* uniqueness of it: `Unit`'s η is proof
        // irrelevance (`crates/kernel/src/conv.rs`), so any two proofs of
        // `True` are convertible and no `SProp`/`Prop` distinction has to be
        // decided (`issues/true-prop-trivial-hypotheses.md`, 2026-08-16).
        //
        // Level 0 **unconditionally**, like `Fin`: the surface has one `True`,
        // and the positions that want it — a `datarepr`'s `inv`, which is
        // `(r: R) -> Type` — are level-0 positions
        // (`docs/datarepr-design.md` §1.4 note 6). `Unit^l` at other levels is
        // a kernel former with no surface spelling, exactly as before.
        //
        // Claimed only when no declaration answers, so a file that declares
        // its own `True` keeps it; `Bool`'s `True` *constructor* is untouched
        // because a constructor is not a type name and never reached here.
        // `Pos<A>` where no binder sugar claimed it (the parser expands it on
        // a parameter, a function result and a record field). Unless a
        // declaration by that name takes one argument, say what it is.
        if name == "Pos"
            && args.len() == 1
            && self.lookup_inductive(name).is_none_or(|i| i.params.len() != 1)
        {
            return err(
                "`Pos<A>` is binder sugar, not a type: it is written as a parameter's type \
                 (`x: Pos<Nat>`), a function's result (`fn f(…) → Pos<Nat>`) or a named \
                 record or constructor field (`den: Pos<Nat>`), and stands for the carrier \
                 beside a searched `0 < x` \
                 (docs/positivity-evidence-design.md §6 B). Here, write the carrier and the \
                 hypothesis; a positive type for function domains and containers is \
                 issues/positive-refinement-type.md"
                    .to_string(),
                span,
            );
        }
        let Some(ind) = self.lookup_inductive(name) else {
            if name == "True" && args.is_empty() {
                return Ok((Type::Unit { level: Level::Zero }, Level::Zero));
            }
            // A type-valued `let` is a term alias at a universe. Decode its
            // resolved value, with the ordinary weakening and local/alias
            // shadowing rules. Type parameters and declared types retain
            // their existing precedence, including in declaration fields
            // lowered over a use site's context.
            if cx.aliases.iter().any(|alias| alias.name == name) {
                if !args.is_empty() {
                    return err(format!("type alias `{name}` takes no type arguments"), span);
                }
                let expression = Expr { kind: ExprKind::Var(name.to_string()), span };
                return self.expr_elab().lower_expression_type(self, cx, &expression, span);
            }
            return Err(self.name_miss(name, format!("unknown type `{name}`"), span));
        };
        if args.len() != ind.params.len() {
            return err(
                format!(
                    "`{name}` takes {} type argument(s), found {}",
                    ind.params.len(),
                    args.len()
                ),
                span,
            );
        }
        // `Converges` bare, where `Converges(p, env, ir, vs)` was meant. The
        // value arguments are only reachable through the *applied* spelling,
        // which arrives as `TyKind::OfExpr` and is caught upstream by
        // [`Self::try_valparam_ty`]; getting here means none were written.
        if !ind.valparams.is_empty() {
            return err(
                format!(
                    "`{name}` takes {} value argument(s): write `{name}{}({})`",
                    ind.valparams.len(),
                    if ind.params.is_empty() {
                        String::new()
                    } else {
                        "<…>".into()
                    },
                    ind.valparams
                        .iter()
                        .map(|(n, _)| n.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                span,
            );
        }
        // A declaration from a finished module, named bare, lowers to the same
        // type at every use, up to weakening past the globals committed since
        // (Ψ is de Bruijn): its field types are read in its own scope
        // (`lower_ctor`'s `use_inductive_scope`) with no type or value
        // arguments and the use site's binders and aliases hidden, so only
        // what else a use site's context carries could reach them — class
        // dictionaries, a quotation or meta environment, which keep the type
        // out of the memo. So it is lowered once per elaborator,
        // not at every mention: naming
        // `StructuredCode` in a signature cost ~5 ms of re-lowering
        // `Instruction` and everything under it, on every one of a generated
        // certificate's thousands of declarations
        // (issues/named-type-lowering-per-mention.md). The current module's
        // own declarations are left out, since a later declaration there can
        // still change what their field names resolve to; the `Rc` is held so
        // its address cannot be reused by another declaration.
        let memo = args.is_empty()
            && cx.dicts.is_empty()
            && cx.meta.is_none()
            && !cx.quoted
            && ind.scope.module != self.names.module();
        let key = (Rc::as_ptr(ind) as usize, self.in_generated());
        let psi = self.psi.bindings.len();
        if memo {
            let hit = self.named_type_memo.borrow().get(&key).map(|(_, at, hit)| (*at, hit.clone()));
            if let Some((at, (ty, level))) = hit.filter(|(at, _)| *at <= psi) {
                let out = (if at == psi { ty } else { ty.shift_global((psi - at) as u32) }, level);
                if at != psi {
                    self.named_type_memo.borrow_mut().insert(key, (Rc::clone(ind), psi, out.clone()));
                }
                return Ok(out);
            }
        }
        let ind = Rc::clone(ind);
        let mut lowered = Vec::with_capacity(args.len());
        for a in args {
            lowered.push(self.elab_ty(cx, a)?);
        }
        let out = self.lower_instance(cx, &ind, &lowered, &[], span)?;
        // Kept only when closed over the locals, so a hit is the same type at
        // any depth. Hiding the use site's binders should make every bare
        // lowering closed; this is the backstop, paid once per miss.
        if memo && out.0.shift_local(1) == out.0 {
            self.named_type_memo.borrow_mut().insert(key, (ind, psi, out.clone()));
        }
        Ok(out)
    }

    /// `D<ā>(v̄)` written in **type position**: a record applied to its value
    /// parameters (docs/surface-value-parameters.md §3), which is what makes it
    /// a predicate. The parser's applied-type-is-never-called backtracking
    /// delivers it as a [`TyKind::OfExpr`], the same road
    /// [`Self::try_indexed_ty`] travels; this recognizes the record case before
    /// `OfExpr`'s generic infer-and-decode path would try to *call* `D`.
    ///
    /// `None` — not an error — for anything that is not a declared record with
    /// value parameters, so every existing spelling reaches its old handler.
    pub(crate) fn try_valparam_ty(
        &self,
        cx: &Cx,
        e: &Expr,
        span: Span,
    ) -> R<Option<(Type, Level)>> {
        let ExprKind::App { head, args, .. } = &e.kind else {
            return Ok(None);
        };
        let Some((name, targs)) = named_head(head) else {
            return Ok(None);
        };
        let Some(ind) = self.lookup_inductive(name).cloned() else {
            return Ok(None);
        };
        if ind.valparams.is_empty() {
            return Ok(None);
        }
        // Written type arguments win. Omitted entirely, they may be recovered
        // from the value arguments' own types
        // (issues/exists-type-arg-not-inferred.md) — the case `Exists<A>(P: A
        // -> Type)` made real, where the predicate's binder already says what
        // `A` is. A *partial* list is still an arity error: filling some and
        // inferring the rest is a different feature and nothing asks for it.
        let lowered = if targs.is_empty() && !ind.params.is_empty() {
            self.valparam_targs(cx, &ind, args, span)?
        } else {
            if targs.len() != ind.params.len() {
                return err(
                    format!(
                        "`{name}` takes {} type argument(s), found {}",
                        ind.params.len(),
                        targs.len()
                    ),
                    span,
                );
            }
            let mut lowered = Vec::with_capacity(targs.len());
            for a in targs {
                lowered.push(self.elab_ty(cx, a)?);
            }
            lowered
        };
        let vargs = self.valparam_args(cx, &ind, &lowered, args, span)?;
        self.lower_instance(cx, &ind, &lowered, &vargs, span)
            .map(Some)
    }

    /// A declared type former **partially applied**, checked against an
    /// expected function type whose ultimate codomain is a universe
    /// (`docs/record-type-partial-application.md` §2). This is
    /// [`Self::build_ctor_value`]'s η-expansion pointed at the *type* reading:
    ///
    /// ```text
    /// D<ā>(v₁ … v_j)  ⇐  Π(x_{j+1} : A_{j+1}). … Π(x_m : A_m). Ty l
    ///     ⇝  λ x_{j+1} … λ x_m. ⌜D<ā>(v₁ … v_j, x_{j+1} … x_m)⌝
    /// ```
    ///
    /// `None` — not an error — for every shape that is not this one, so every
    /// reading the constructor arms have today is untouched. The disambiguator
    /// is `docs/record-type-values.md` §2.1's, one arrow further in: no
    /// constructor inhabits a universe, and no record type is a `Π`, so an
    /// expected Π-spine that ends in `Ty l` can only want the type former.
    /// Committing on exactly that shape is what lets an arity mismatch be
    /// diagnosed against the **value-parameter** telescope here rather than
    /// reported as the constructor's field count.
    pub(crate) fn check_type_former_value(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        span: Span,
    ) -> R<Option<Term>> {
        let (head, args) = match &e.kind {
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if named.is_empty() => (&**head, args.as_slice()),
            _ => (e, &[][..]),
        };
        let Some((name, _)) = named_head(head) else {
            return Ok(None);
        };
        // Registry first, `shadowed` second: this guard sits on the checking
        // path of every application that reached the constructor arms, and a
        // miss in the name table is a hash lookup where the shadowing test is
        // a walk of the context.
        let Some(ind) = self.lookup_inductive(name).cloned() else {
            return Ok(None);
        };
        // Saturated (or over-applied) is somebody else's case: the type
        // position already handles it, and there is nothing to abstract.
        let Some(missing) = ind
            .valparams
            .len()
            .checked_sub(args.len())
            .filter(|&m| m > 0)
        else {
            return Ok(None);
        };
        if self.shadowed(cx, name) {
            return Ok(None);
        }
        // Walk the expected Π-spine to its ultimate codomain, binder by
        // binder — a *dependent* domain (`Cursor<T>(source)`, which is the
        // shape the showcase's relation slots have) is only readable under
        // the ones before it. Nothing is committed during the walk: a spine
        // that does not end in a universe belongs to another reading.
        let mut pcx = cx.clone();
        let mut ty = expected.clone();
        let mut peeled: Vec<(String, Level, Level, Rc<Type>)> = Vec::new();
        let want = loop {
            match self.whnf(&pcx, &ty, span)? {
                Type::Pi {
                    dom_level,
                    cod_level,
                    dom,
                    cod,
                } => {
                    // `#` marks an elaborator-introduced binder: unspellable,
                    // so it captures nothing the user wrote.
                    let binder = format!("#ta{}", peeled.len());
                    pcx.push(binder.clone(), (*dom).clone(), dom_level.clone());
                    ty = (*cod).clone();
                    peeled.push((binder, dom_level, cod_level, dom));
                }
                Type::Ty(want) => break want,
                _ => return Ok(None),
            }
        };
        if peeled.len() != missing {
            return err(
                format!(
                    "`{name}` needs {missing} more value argument(s) to be a type, but \
                     the expected function type provides {} before its `Type`",
                    peeled.len()
                ),
                span,
            );
        }
        // The extra arguments are *surface* variables, so the saturated
        // spelling is lowered by `try_valparam_ty` exactly as a written
        // `D(v̄, x̄)` in type position is — no second copy of the instance
        // lowering (`docs/record-type-values.md` §2).
        let mut vargs = args.to_vec();
        vargs.extend(peeled.iter().map(|(binder, ..)| Expr {
            kind: ExprKind::Var(binder.clone()),
            span,
        }));
        let sat = Expr {
            kind: ExprKind::App {
                head: Box::new(head.clone()),
                args: vargs,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let (lowered, level) = self
            .try_valparam_ty(&pcx, &sat, span)?
            .expect("a declared type former with value parameters lowers here");
        let mut t =
            crate::expr::ExprElab::quote_type_at(self, &pcx, &lowered, &level, &want, span)?;
        for (_, dom_level, cod_level, dom) in peeled.into_iter().rev() {
            t = Term::Lam {
                dom_level,
                cod_level,
                dom,
                body: Rc::new(t),
            };
        }
        Ok(Some(t))
    }

    /// The type arguments of `D(v̄)`, recovered from the value arguments'
    /// own types (issues/exists-type-arg-not-inferred.md).
    ///
    /// Each value argument is **inferred**, and its type matched against the
    /// declared surface type of the parameter it fills; wherever the declared
    /// side is exactly a type parameter, the kernel side opposite is that
    /// parameter's solution. For `Exists<A>(P: A -> Type)` applied to
    /// `λ (k: Nat) => …`, the inferred `Π(Nat). Ty 0` meets the declared
    /// `A -> Type` and `A := Nat` falls out of the domains.
    ///
    /// **Deliberately first-order and one-sided**, on the doctrine
    /// [`Elaborator::infer_ctor`] already states for constructors: the
    /// declared side is a *skeleton* with the parameter names as holes, the
    /// actual side is inspected only where the skeleton has structure, and
    /// anything deeper is unification
    /// (issues/elab-unifier-completeness.md). An argument that fails to infer
    /// is not an error here — it simply solves nothing, and the unsolved
    /// parameter reports below.
    fn valparam_targs(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[Expr],
        span: Span,
    ) -> R<Vec<(Type, Level)>> {
        let mut sols: Vec<Option<(Type, Level)>> = vec![None; ind.params.len()];
        for ((_, decl), arg) in ind.valparams.iter().zip(args) {
            let Ok((_, ty, lvl)) = self.elab_infer(cx, arg) else {
                continue;
            };
            match_targs(decl, &ty, &lvl, &ind.params, &mut sols);
        }
        let mut out = Vec::with_capacity(sols.len());
        for (p, sol) in ind.params.iter().zip(sols) {
            let Some(sol) = sol else {
                return err(
                    format!(
                        "cannot infer the type argument `{p}` of `{}` here — no value \
                         argument's type determines it. Write it: `{}<…>({})`",
                        ind.name,
                        ind.name,
                        ind.valparams
                            .iter()
                            .map(|(n, _)| n.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    span,
                );
            };
            out.push(sol);
        }
        Ok(out)
    }

    /// Check a use site's value arguments against the declared telescope
    /// (docs/surface-value-parameters.md §2). Parameter `j`'s declared type may
    /// mention parameters `0..j`, so it is elaborated in a context carrying the
    /// earlier arguments as aliases — all bound at the *ambient* depth, so no
    /// shifting happens here. The shifting that matters happens later, in
    /// [`Self::lower_ctor`], where the field spine pushes binders on top.
    ///
    /// The declared type may also mention the declaration's **type**
    /// parameters — `class Monoid<A>(op: A -> A -> A)` is the case that made
    /// this true (docs/operation-indexed-classes-design.md §3) — so they are
    /// bound here at the instantiation, exactly as [`Self::lower_ctor`] binds
    /// them for the field types. `record R(p: Prog, env: Val)`, whose value
    /// parameters' types are closed, is unaffected.
    pub(crate) fn valparam_args(
        &self,
        cx: &Cx,
        ind: &Inductive,
        targs: &[(Type, Level)],
        args: &[Expr],
        span: Span,
    ) -> R<Vec<(Term, Type, Level)>> {
        if args.len() != ind.valparams.len() {
            return err(
                format!(
                    "`{}` takes {} value argument(s), found {}",
                    ind.name,
                    ind.valparams.len(),
                    args.len()
                ),
                span,
            );
        }
        let mut tcx = cx.clone();
        let depth = cx.names.len();
        tcx.tyvars.extend(
            ind.params
                .iter()
                .zip(targs)
                .map(|(name, (ty, level))| TyVar {
                    name: name.clone(),
                    ty: ty.clone(),
                    level: level.clone(),
                    depth,
                }),
        );
        // The declared types are the declaration's own source, so they are read
        // under the declaration's own body spellings and never the use site's:
        // a `∙` in this telescope is the head's `as`, or nothing
        // (issues/binder-symbol-as-notation.md). Installed as the telescope is
        // walked, which is what makes the scope "the rest of the telescope".
        tcx.op_locals.clear();
        let mut out = Vec::with_capacity(args.len());
        for ((pname, pty), arg) in ind.valparams.iter().zip(args) {
            let (ty, level) = {
                let _scope = self.use_inductive_scope(ind);
                self.elab_ty(&tcx, pty)?
            };
            let tm = self.elab_check(cx, arg, &ty, &level)?;
            tcx.aliases.push(Rc::new(Alias {
                skel: None,
                name: pname.clone(),
                depth,
                term: Rc::new(tm.clone()),
                ty: ty.clone(),
                level: level.clone(),
            }));
            if let Some((sym, _)) = ind.op_symbols.iter().find(|(_, n)| n == pname) {
                tcx.op_locals.push((sym.clone(), pname.clone()));
            }
            out.push((tm, ty, level));
        }
        Ok(out)
    }

    /// `⟦D<ā>⟧`: the tag spine at tier 0, and the `Wf` over it at tier 1
    /// (`docs/inductive-tier1-wf-lowering.md` §4). Every other lowering in
    /// this crate goes through here, so the two tiers cannot disagree about
    /// what a declaration's kernel type is.
    pub(crate) fn lower_instance(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        if ind.index.is_some() {
            return err(
                format!(
                    "`{}` is an indexed family and needs its index: write `{}{}(i)`",
                    ind.name,
                    ind.name,
                    if ind.params.is_empty() { "" } else { "<…>" }
                ),
                span,
            );
        }
        // Tier 2 (docs/inductive-tier2-w-lowering.md §5): the shape is this
        // same sum-of-Σs, wrapped in `W` and the leaf predicate.
        if ind.infinitary() {
            return self.lower_instance_w(cx, ind, args, vargs, span);
        }
        let (shape, level) = self.lower_shape(cx, ind, args, vargs, span)?;
        if !ind.recursive {
            return Ok((shape, level));
        }
        // The arity is a `Nat` term with `x : S` free, so it is built in the
        // context extended by that binder (§3).
        let mut xcx = cx.clone();
        xcx.push("#shape".into(), shape.clone(), level.clone());
        let arity = self.lower_arity(&xcx, ind, &shape, &level, span)?;
        Ok((
            Type::Wf {
                level: level.clone(),
                shape: Rc::new(shape),
                arity: Rc::new(arity),
            },
            level,
        ))
    }

    /// The tag spine (§3.2): `S = ⟦c₁⟧ + (⟦c₂⟧ + …)`, right-nested;
    /// `Empty` with no constructors, and no `+` at all with one. At tier 1
    /// this is the `Wf`'s *shape*, so the recursive fields are already gone
    /// by construction — [`Self::lower_ctor`] skips them.
    pub(crate) fn lower_shape(
        &self,
        cx: &Cx,
        ind: &Inductive,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        let mut parts = Vec::with_capacity(ind.ctors.len());
        for i in 0..ind.ctors.len() {
            parts.push(self.lower_ctor(cx, ind, i, args, vargs, span)?);
        }
        let Some((last, last_lvl)) = parts.pop() else {
            // A declaration with no constructors lowers to `Empty` (§3.3).
            //
            // **This is where the level-0 assumption enters.** `Unit`/`Empty`
            // are level-indexed (docs/unit-empty-level-indexing.md), but tier
            // 0 monomorphises type parameters, so every encoding this module
            // builds lives at level 0 and there is no `l` here to derive one
            // from — `parts` is empty. A polymorphic declaration would take
            // its level from the declaration head, and this is the site that
            // changes first.
            return Ok((Type::Empty { level: Level::Zero }, Level::Zero));
        };
        let mut acc = last;
        let mut acc_lvl = last_lvl;
        for (ty, lvl) in parts.into_iter().rev() {
            acc = Type::Sum {
                lhs_level: lvl.clone(),
                rhs_level: acc_lvl.clone(),
                lhs: Rc::new(ty),
                rhs: Rc::new(acc),
            };
            // Canonical, not the raw `Max` tree: each summand's level embeds
            // the accumulated one, so an uncanonicalized join grows a level
            // *tree* quadratic in the constructor count, mirrored into every
            // `Sum` node's level slots — measured at ~2/3 of a large lowered
            // type's remaining node mass (issues/wf-field-conversion-cost.md,
            // 2026-08-13). `canonical` is `equiv`-preserving by construction,
            // so this is a spelling change only.
            acc_lvl = Level::max(lvl, acc_lvl).normalize().canonical();
        }
        Ok((acc, acc_lvl))
    }

    /// The arity `n` over `(Γ, x : S)` (tier 1 §3): a case on the tag
    /// returning each constructor's literal recursive-field count. This is
    /// §6.1's constant-motive case tree at the motive `Nat` — the same code,
    /// so the shape's structure and the constructor list cannot disagree.
    fn lower_arity(
        &self,
        xcx: &Cx,
        ind: &Inductive,
        shape: &Type,
        level: &Level,
        span: Span,
    ) -> R<Term> {
        let spine = self.spine(shape, level, ind.ctors.len(), span)?;
        let counts: Vec<(usize, Option<usize>)> = ind
            .ctors
            .iter()
            .map(|c| (c.arity(), c.container().map(|(_, len)| len)))
            .collect();
        self.const_case_tree(
            xcx,
            &spine,
            ind.ctors.len(),
            &Type::Nat,
            &Level::Zero,
            Rc::new(Term::Var(LocalVar(0))),
            &ConstBody::Arity(counts),
            0,
            // The spine is scoped in `Γ`; one binder (`x`) has been pushed
            // since.
            1,
            span,
        )
    }

    /// One constructor's field spine (§3.1 + §3.3): the nominal tag, then the
    /// **payload** fields, Unit-terminated. Built outside-in as a list of
    /// entries and folded from the end, which is exactly why no shifting is
    /// needed: entry `j`'s type is already scoped in `Γ` plus entries `0..j`.
    ///
    /// Recursive fields are skipped and *not* pushed into scope: they are
    /// children in the `Vec`, not components of the shape, so a later field
    /// type cannot depend on one (tier 1 §2, where the restriction is stated
    /// and costed).
    pub(crate) fn lower_ctor(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level)> {
        self.lower_ctor_with_domain(cx, ind, i, args, vargs, span)
            .map(|(t, l, _)| (t, l))
    }

    /// [`Self::lower_ctor`], also returning the **domain** of the
    /// constructor's recursive function field, if it has one
    /// (docs/inductive-tier2-w-lowering.md §4): `(A, its level, j)` with `A`
    /// lowered by this same walk at the point the field sits, so scoped over
    /// `(Γ, #tag, p₀, …, p_{j-1})` — the tag and the `j` payload fields
    /// declared before it. One walk for both, so the domain sees exactly the
    /// field context the shape's own field types see.
    pub(crate) fn lower_ctor_with_domain(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[(Type, Level)],
        vargs: &[(Term, Type, Level)],
        span: Span,
    ) -> R<(Type, Level, Option<(Type, Level, usize)>)> {
        let _scope = self.use_inductive_scope(ind);
        // Field types see the type parameters and the earlier *named* fields;
        // nothing else from the ambient declaration. The arguments are scoped
        // in `cx`, so that is the depth every use of one is weakened from.
        let mut fcx = cx.clone();
        fcx.selfref = None;
        fcx.guard = None;
        // The class head's `as` spellings, and *only* those: the field types
        // are this declaration's own source, so a symbol in one means what the
        // head said it means, never what the use site's binders say
        // (issues/binder-symbol-as-notation.md — the symbol is scoped to the
        // binder's scope, and for a class head that scope is the class body).
        // Empty for every declaration whose head writes no `as`.
        fcx.op_locals = ind.op_symbols.clone();
        // The use site's binders and `let` aliases stay in Γ, where the
        // arguments are scoped, but out of reach by name: a field spelling
        // `y()` means the declaration's `y`, not a parameter `y` of whatever
        // function names the type (issues/named-type-lowering-per-mention.md).
        for name in &mut fcx.names {
            *name = "#use-site".into();
        }
        fcx.aliases.clear();
        let depth = cx.names.len();
        fcx.tyvars = ind
            .params
            .iter()
            .zip(args)
            .map(|(name, (ty, level))| TyVar {
                name: name.clone(),
                ty: ty.clone(),
                level: level.clone(),
                depth,
            })
            .collect();
        // Value parameters, bound to the terms the use site supplied
        // (docs/surface-value-parameters.md §2). An `Alias` is exactly the
        // right carrier: it is not a kernel binder, it is inlined at each use,
        // and its `depth` is what a use gets weakened by — which is the whole
        // correctness obligation here. The field spine pushes the tag and then
        // each earlier field on top of `cx`, so a use of a parameter in field
        // `j` sits `1 + j` binders deeper than the argument it denotes.
        //
        // Getting this shift wrong does **not** produce a kernel rejection: an
        // un-shifted parameter under the Σ binder captures the field above it
        // and writes a well-formed but *different* — typically trivially
        // inhabited — type (`docs/surface-existential-investigation.md` §B.1
        // test 9, §H risk 3). The observers are therefore propositional, in
        // `crates/elab/tests/value_parameters.rs`, not merely structural.
        for ((name, _), (tm, ty, level)) in ind.valparams.iter().zip(vargs) {
            fcx.aliases.push(Rc::new(Alias {
                skel: None,
                name: name.clone(),
                depth,
                term: Rc::new(tm.clone()),
                ty: ty.clone(),
                level: level.clone(),
            }));
        }
        // Entry 0 is the tag; the surface has no name for it and no way to
        // bind it in a pattern.
        let mut entries = vec![(tag_type(ind.tag), Level::Zero)];
        fcx.push("#tag".into(), tag_type(ind.tag), Level::Zero);
        let mut domain = None;
        let ctor = &ind.ctors[i];
        for (k, (name, ty)) in ctor.fields.iter().enumerate() {
            if ctor.kind[k] == FieldKind::FnChild {
                // Lowered where it sits, and *not* pushed: a recursive field
                // is not in scope in later field types (tier 1 §2).
                let TyKind::Fn { dom, .. } = &ty.kind else {
                    return err("internal: a recursive function field is not a `->`", ty.span);
                };
                let (t, l) = self.elab_ty(&fcx, dom)?;
                domain = Some((t, l, entries.len() - 1));
                continue;
            }
            if ctor.kind[k] != FieldKind::Payload {
                continue;
            }
            let (t, l) = self.elab_ty(&fcx, ty)?;
            entries.push((t.clone(), l.clone()));
            let fname = name.clone().unwrap_or_else(|| "#field".into());
            fcx.push(fname.clone(), t.clone(), l);
            // A field *at a universe* — `record Mon { carrier: Type, unit:
            // carrier, … }` — is a type name for the fields after it, by the
            // same rule as a `Type`-valued parameter: a type name is any
            // binder whose type is `Type<n>` (docs/surface-universe.md §2).
            // This is what makes the **bundled** record writable, the case
            // docs/surface-records.md §3 named as waiting on this round.
            if let Type::Ty(level) = t {
                fcx.tyvars.push(TyVar {
                    name: fname,
                    ty: Type::El {
                        level: level.clone(),
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    },
                    level,
                    depth: fcx.names.len(),
                });
            }
        }
        let _ = span;
        let mut acc = Type::Unit { level: Level::Zero };
        let mut acc_lvl = Level::Zero;
        for (ty, lvl) in entries.into_iter().rev() {
            acc = Type::Sigma {
                fst_level: lvl.clone(),
                snd_level: acc_lvl.clone(),
                fst: Rc::new(ty),
                snd: Rc::new(acc),
            };
            // Canonical join — [`Self::lower_shape`]'s note: the raw `Max`
            // tree compounds per field and is copied into every Σ level slot.
            acc_lvl = Level::max(lvl, acc_lvl).normalize().canonical();
        }
        Ok((acc, acc_lvl, domain))
    }

    // -- reading a lowered type back ----------------------------------------

    /// Split a lowered `⟦D⟧` into its `n` constructor summands (§3.2). `n`
    /// comes from the declaration, never from the shape, so a constructor
    /// whose own encoding is a `+` could not confuse it.
    ///
    /// A tier-1 `⟦D⟧` is `Wf^l(x : S). n`, and the summands are `S`'s: the
    /// unwrapping happens here, once, so no caller has to know which tier it
    /// is holding. A summand is always a `Σ`, never itself a `Wf`, so this
    /// cannot strip too much.
    pub(crate) fn spine(&self, ty: &Type, lvl: &Level, n: usize, span: Span) -> R<Spine> {
        let mut ctors = Vec::with_capacity(n);
        let mut tails = Vec::with_capacity(n.saturating_sub(1));
        let (cur, cur_lvl) = match &*decoded(ty) {
            // `Wf`'s shape lives at the `Wf`'s own level (kernel formation
            // rule), so there is no second level to read off.
            Type::Wf { shape, level, .. } => (Rc::clone(shape), level.clone()),
            // Tier 2: `Σ(t : W(x : S). P). El(canon t)`, and the summands are
            // `S`'s at the `W`'s shape level
            // (docs/inductive-tier2-w-lowering.md §5).
            other => match crate::infinitary::w_of(other) {
                Some((shape, shape_level)) => (shape, shape_level),
                None => (Rc::new(other.clone()), lvl.clone()),
            },
        };
        let mut cur = cur;
        let mut cur_lvl = cur_lvl;
        for _ in 0..n.saturating_sub(1) {
            // The inner scope ends `decoded`'s borrow of `cur` before `cur`
            // is rebound.
            let step = {
                let d = decoded(&cur);
                let Type::Sum {
                    lhs_level,
                    rhs_level,
                    lhs,
                    rhs,
                } = &*d
                else {
                    return err(
                        "internal: malformed inductive encoding (expected a `+`)",
                        span,
                    );
                };
                ctors.push((Rc::clone(lhs), lhs_level.clone()));
                tails.push((Rc::clone(rhs), rhs_level.clone()));
                (Rc::clone(rhs), rhs_level.clone())
            };
            cur = step.0;
            cur_lvl = step.1;
        }
        ctors.push((cur, cur_lvl));
        Ok(Spine { ctors, tails })
    }

    /// The spine with every component's registered sub-lowerings respelled as
    /// references, for **emission** (`inject`'s annotations at a constructor
    /// value). Components that respell nothing keep their `Rc` identity, so
    /// a small-field declaration pays two pointer walks and no allocation.
    ///
    /// A **flat** declaration with spine codes registered
    /// (`issues/inductive-spelling-codes-nonrecursive.md`) takes them by
    /// position first — `El (D#payloadₖ^δ)` for `ctors[k]`, `El (D#suffixₖ^δ)`
    /// for `tails[k]` — under the same structural guard as every other
    /// reference; a component the guard declines (a monomorphized or
    /// otherwise re-spelled copy) falls back to the deep respell as before.
    pub(crate) fn respell_spine(&self, cx: &Cx, spine: &Spine) -> Spine {
        let by_position = spine
            .ctors
            .first()
            .and_then(|(c, _)| self.tag_of(c))
            .and_then(|ind| self.spine_refs_by_position(cx, ind.tag, spine));
        let (ctor_refs, tail_refs) = match by_position {
            Some((c, t)) => (c, t),
            None => (vec![None; spine.ctors.len()], vec![None; spine.tails.len()]),
        };
        let re = |v: &Vec<(Rc<Type>, Level)>, refs: Vec<Option<Type>>| {
            v.iter()
                .zip(refs)
                .map(|((t, l), r)| match r.or_else(|| self.emit_ty(cx, t, 0)) {
                    Some(r) => (Rc::new(r), l.clone()),
                    None => (Rc::clone(t), l.clone()),
                })
                .collect()
        };
        Spine {
            ctors: re(&spine.ctors, ctor_refs),
            tails: re(&spine.tails, tail_refs),
        }
    }

    /// Which declaration a lowered type belongs to, by its nominal tag: walk
    /// to the leftmost constructor and read its tag field (§3.3). `None` for
    /// anything that is not an inductive encoding.
    pub(crate) fn tag_of(&self, ty: &Type) -> Option<Rc<Inductive>> {
        match &*decoded(ty) {
            // Tier 1: the tag is in the `Wf`'s shape (tier 1 §4).
            Type::Wf { shape, .. } => self.tag_of(shape),
            Type::Sum { lhs, .. } => self.tag_of(lhs),
            // Tier 2: through the `Σ` and the `W` to the shape
            // (docs/inductive-tier2-w-lowering.md §5).
            Type::Sigma { .. } if crate::infinitary::w_of(ty).is_some() => {
                self.tag_of(&crate::infinitary::w_of(ty)?.0)
            }
            Type::Sigma { fst, .. } => self.types.by_tag(read_tag(fst)?).cloned(),
            _ => None,
        }
    }

    /// The inline constructor shape of a type on the display path. Recursive
    /// values and types may carry `D#shape` rather than the shape itself; no
    /// ordinary structural reader unfolds generated globals, so display uses
    /// the registry's exact inverse lookup and nothing more.
    ///
    /// A flat declaration's emitted annotations carry `El (D#payload^δ)` /
    /// `El (D#suffix^δ)` — as a whole (`inl`/`inr` slots) or as the two
    /// components of a sum (the decode of its whole-type code) — and the same
    /// exact inverse lookup restores those
    /// (`issues/inductive-spelling-codes-nonrecursive.md`).
    fn display_shape(&self, ty: &Type) -> Type {
        // A whole-type reference first — since
        // `docs/per-instantiation-type-codes-design.md` a *parameterized*
        // instantiation has one too, and the constructor spine display reads
        // lives behind it (`List<A>` rather than `List<…>`).
        let inline = self.unspell_here(ty);
        let ty = inline.as_ref().unwrap_or(ty);
        // …and the kernel's lazy *decode* of one, which is what a type
        // reduced outside `Elaborator::whnf` arrives as: `Wf(El ⌜S⌝). n`,
        // `docs/wf-shape-code-design.md` §1.4's look-alike.
        let decoded = decode_deep(ty);
        let ty = decoded.as_ref().unwrap_or(ty);
        let shape = match ty {
            Type::Wf { shape, .. } => &**shape,
            _ => ty,
        };
        self.unspell_shape_here(shape)
            .or_else(|| self.unspell_here(shape))
            .or_else(|| self.unspell_sum_components(shape))
            .unwrap_or_else(|| shape.clone())
    }

    /// The declaration at the head of a displayable inductive type, including
    /// a recursive `Wf` whose shape has been respelled as a generated global.
    pub(crate) fn display_tag_of(&self, ty: &Type) -> Option<Rc<Inductive>> {
        self.tag_of(&self.display_shape(ty))
    }

    /// Recover a monomorphized inductive instance's type arguments for
    /// diagnostics. A candidate comes only from a payload field whose written
    /// type is exactly one declaration parameter. It is strengthened out of
    /// the tag/field telescope, then the complete candidate list is verified
    /// by re-lowering the declaration and comparing the resulting shape.
    /// Anything uncertain declines to the existing `<…>` spelling.
    /// `under` is the number of binders the display walk has descended
    /// through since `cx`, so `ty` — and every field type read out of its
    /// lowering below — is scoped in `cx.gamma` plus that many entries rather
    /// than in `cx.gamma` alone. It is load-bearing twice over: a recovered
    /// argument has to be strengthened past those binders *as well as* the Σ
    /// spine's, or `apply_local` is handed a variable that addresses nothing
    /// and the kernel aborts the whole process rather than the diagnostic
    /// (issues/pi-codomain-record-mismatch-panics-kernel.md); and the result
    /// is handed back to a walk that is still under them, so it is shifted
    /// back up before it is returned.
    pub(crate) fn display_targs(
        &self,
        cx: &Cx,
        ty: &Type,
        ind: &Inductive,
        under: u32,
    ) -> Option<Vec<(Type, Level)>> {
        if ind.params.is_empty() {
            return Some(Vec::new());
        }
        // Value arguments and indices are not recoverable from the ordinary
        // constructor shape alone. They keep the honest ellipsis until their
        // own display designs exist.
        if !ind.valparams.is_empty() || ind.index.is_some() {
            return None;
        }
        // Re-lowering is the soundness check and its cost is proportional to
        // the declaration. Keep a fixed ceiling on that work in a diagnostic.
        const MAX_RECOVERY_FIELDS: usize = 64;
        let size = ind.ctors.len()
            + ind
                .ctors
                .iter()
                .map(|ctor| ctor.fields.len())
                .sum::<usize>();
        if size > MAX_RECOVERY_FIELDS {
            return None;
        }

        let shape = self.display_shape(ty);
        let mut sols: Vec<Option<(Type, Level)>> = vec![None; ind.params.len()];
        let mut summand = Rc::new(shape.clone());
        for (i, ctor) in ind.ctors.iter().enumerate() {
            let ctor_ty = if i + 1 < ind.ctors.len() {
                let d = decoded(&summand);
                let Type::Sum { lhs, rhs, .. } = &*d else {
                    return None;
                };
                let out = Rc::clone(lhs);
                summand = Rc::clone(rhs);
                out
            } else {
                Rc::clone(&summand)
            };

            // Entry zero is the nominal tag. Every following Sigma entry is
            // one payload field; recursive children are absent from the shape.
            let d = decoded(&ctor_ty);
            let Type::Sigma { snd, .. } = &*d else {
                return None;
            };
            let mut fields = Rc::clone(snd);
            let mut crossed = 1u32;
            for (_, (_, written)) in ctor.payload() {
                let d = decoded(&fields);
                let Type::Sigma {
                    fst_level,
                    fst,
                    snd,
                    ..
                } = &*d
                else {
                    return None;
                };
                if let TyKind::Named { name, args } = &written.kind
                    && args.is_empty()
                    && let Some(p) = ind.params.iter().position(|param| param == name)
                    && sols[p].is_none()
                    && let Some(candidate) =
                        crate::strengthen_ty(&cx.gamma, fst, crossed + under)
                {
                    sols[p] = Some((candidate, fst_level.clone()));
                }
                fields = Rc::clone(snd);
                crossed += 1;
            }
        }
        let args: Vec<(Type, Level)> = sols.into_iter().collect::<Option<_>>()?;
        // The arguments strengthened all the way back to `cx`, which is where
        // `lower_shape` scopes them, so the re-lowering is the same soundness
        // check it always was; `shape` is `under` binders further in, so the
        // comparison meets it there.
        let (rebuilt, _) = self
            .lower_shape(cx, ind, &args, &[], Span { start: 0, end: 0 })
            .ok()?;
        if rebuilt.shift_local(under) != shape {
            return None;
        }
        // Back out to where the caller is standing.
        Some(args.into_iter().map(|(t, l)| (t.shift_local(under), l)).collect())
    }

    /// The surface field types of a constructor, for the narrow type-argument
    /// inference in [`Elaborator::infer_ctor`].
    pub(crate) fn ctor_fields(&self, ind: &Inductive, i: usize) -> Vec<Ty> {
        ind.ctors[i].fields.iter().map(|(_, t)| t.clone()).collect()
    }

    pub(crate) fn ctor_of(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        self.lookup_ctor(name)
    }

    // -- constructors (§4) --------------------------------------------------

    /// A constructor in checking position, saturated **or not**
    /// (`docs/constructor-function-values.md` §2). With every field supplied
    /// this is [`Self::build_ctor`]; with fields missing and a `Π` expected it
    /// is the η-expansion
    ///
    /// ```text
    /// C(a₁ … a_j) ⇐ Π(x_{j+1} : A_{j+1}). … Π(x_m : A_m). D
    ///     ⇝ λ x_{j+1} … λ x_m. ⟦C(a₁ … a_j, x_{j+1} … x_m)⟧ at D
    /// ```
    ///
    /// The missing arguments are *surface* variables at unspellable `#`-names,
    /// so the saturated builder runs unchanged and every tier distinction
    /// (`sup_f`, the children tuple, the container tail) stays inside it. The
    /// built term's type is the expected one by construction; a peeled domain
    /// that disagrees with the field it fills is a kernel rejection, not a
    /// mis-lowering (§2.2).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_ctor_value<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[A],
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        let missing = ctor.fields.len().saturating_sub(args.len());
        if missing == 0 {
            return self.build_ctor(cx, ind, i, args, expected, expected_lvl, span);
        }
        let mut cx = cx.clone();
        let missing_args: Vec<Expr> = (0..missing).map(|k| Expr {
            kind: ExprKind::Var(format!("#arg{k}")), span,
        }).collect();
        let mut args: Vec<&Expr> = args.iter().map(|a| a.borrow()).collect();
        let mut peeled = Vec::with_capacity(missing);
        let mut ty = expected.clone();
        let mut lvl = expected_lvl.clone();
        for k in 0..missing {
            let head = self.whnf(&cx, &ty, span)?;
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = head
            else {
                // Not enough arrows to absorb the missing fields. Diagnosed
                // here rather than left to `build_ctor`'s arity message, which
                // would count the arguments the user wrote and not the ones
                // the expected type would have supplied (§3).
                if k == 0 {
                    return self.build_ctor(&cx, ind, i, &args, &ty, &lvl, span);
                }
                return err(
                    format!(
                        "`{}` needs {missing} more argument(s), but the expected function \
                         type provides only {k}",
                        ctor.name
                    ),
                    span,
                );
            };
            // `#` marks an elaborator-introduced binder: unspellable, so it
            // cannot capture anything the user wrote, and filtered out of the
            // goal listing.
            let name = format!("#arg{k}");
            cx.push(name.clone(), (*dom).clone(), dom_level.clone());
            args.push(&missing_args[k]);
            // The codomain is scoped under the binder just pushed, which is
            // what makes a *dependent* expected type work.
            ty = (*cod).clone();
            lvl = cod_level.clone();
            peeled.push((dom_level, cod_level, dom));
        }
        let mut t = self.build_ctor(&cx, ind, i, &args, &ty, &lvl, span)?;
        for (dom_level, cod_level, dom) in peeled.into_iter().rev() {
            t = Term::Lam {
                dom_level,
                cod_level,
                dom,
                body: Rc::new(t),
            };
        }
        Ok(t)
    }

    /// Build `⟦c_i(a⃗)⟧` at a known type: the injection path, then the field
    /// tuple. Every annotation comes from `expected`, so this is total on a
    /// well-formed encoding and produces a kernel-rejected term otherwise.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_ctor<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Inductive,
        i: usize,
        args: &[A],
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let ctor = &ind.ctors[i];
        if args.len() != ctor.fields.len() {
            return err(
                format!(
                    "`{}` takes {} argument(s), found {}",
                    ctor.name,
                    ctor.fields.len(),
                    args.len()
                ),
                span,
            );
        }
        if ind.index.is_some() {
            // An indexed constructor reads the *family form* of the expected
            // type, not its whnf (docs/inductive-indexed-lowering.md §5;
            // docs/inductive-fording-lowering.md §6.3 for route 2b's).
            if ind.skel.is_some() {
                return self.build_forded_ctor(cx, ind, i, args, expected, expected_lvl, span);
            }
            return self.build_indexed_ctor(cx, ind, i, args, expected, expected_lvl, span);
        }
        let args: Vec<&Expr> = args.iter().map(|a| a.borrow()).collect();
        if ind.infinitary() {
            // Tier 2 (docs/inductive-tier2-w-lowering.md §6).
            return self.build_ctor_w(cx, ind, i, &args, expected, span);
        }
        let prepared = self.prepare_ctor(cx, ind, i, &args, expected, expected_lvl, span)?;
        if !ind.recursive { return Ok(prepared.term); }
        let child_ty = self.whnf(cx, expected, span)?;
        let Type::Wf { level: child_lvl, .. } = &child_ty else { unreachable!() };
        let iterative = !args.iter().any(|arg| crate::surface::has_free_slots(arg));
        let mut frames = vec![self.ctor_work_frame(cx, prepared, &child_ty, span)?];
        loop {
            let frame = frames.last_mut().expect("the root is returned, not popped empty");
            if let Some(child) = frame.prepared.children.pop() {
                // Plain recursive fields have exactly this family's type and
                // context. Other expressions retain the ordinary checker.
                let call = if iterative {
                    self.recursive_ctor_call(cx, child, ind, &child_ty)?
                } else { None };
                if let Some((i, args)) = call {
                    let prepared = self.prepare_ctor(
                        cx, ind, i, &args, &child_ty, child_lvl, child.span,
                    )?;
                    frames.push(self.ctor_work_frame(cx, prepared, &child_ty, child.span)?);
                    continue;
                }
                let term = self.elab_check(cx, child, &child_ty, child_lvl)?;
                self.add_ctor_child(cx, frame, &child_ty, term);
                continue;
            }
            let frame = frames.pop().expect("just inspected");
            let mut term = frame.prepared.term;
            if let Term::Supf { children, .. } = &mut term {
                *children = Rc::new(frame.children);
            }
            match frames.last_mut() {
                Some(parent) => self.add_ctor_child(cx, parent, &child_ty, term),
                None => return Ok(term),
            }
        }
    }

    fn ctor_work_frame<'a>(
        &self, cx: &Cx, prepared: PreparedCtor<'a>, expected: &Type, span: Span,
    ) -> R<CtorWorkFrame<'a>> {
        let (children, tail_len) = match &prepared.term {
            Term::Supf { level, .. } => self.constructor_children_tail(
                cx, expected, level,
                prepared.container.as_ref().map(|(a, len)| (*a, Rc::clone(len))), span,
            )?,
            _ => (Term::Triv { level: Level::Zero }, Term::Zero),
        };
        Ok(CtorWorkFrame { prepared, children, tail_len })
    }

    fn add_ctor_child(&self, cx: &Cx, frame: &mut CtorWorkFrame<'_>, expected: &Type, child: Term) {
        let Term::Supf { level, .. } = &frame.prepared.term else { unreachable!() };
        let children = std::mem::replace(&mut frame.children, Term::Zero);
        frame.children = self.prepend_constructor_child(
            cx, expected, level, child, children, &frame.tail_len,
        );
        frame.tail_len = Term::Succ(Rc::new(std::mem::replace(&mut frame.tail_len, Term::Zero)));
    }

    /// Prepare the label and emission slots using the same structural reads
    /// as the recursive builder. The work stack only changes child descent.
    #[allow(clippy::too_many_arguments)]
    fn prepare_ctor<'a>(
        &self, cx: &Cx, ind: &Inductive, i: usize, args: &[&'a Expr],
        expected: &Type, expected_lvl: &Level, span: Span,
    ) -> R<PreparedCtor<'a>> {
        let ctor = &ind.ctors[i];
        let pre_whnf = expected;
        let expected = self.whnf(cx, expected, span)?;
        match self.tag_of(&expected) {
            Some(found) if found.tag == ind.tag => {}
            _ => {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, which is not the expected type here",
                        ctor.name, ind.name
                    ),
                    span,
                );
            }
        }
        let spine = self.spine(&expected, expected_lvl, ind.ctors.len(), span)?;
        // Tier 1 (§5): the payload arguments build the *label*, the recursive
        // ones build the children tuple. Both keep declaration order.
        let payload: Vec<&Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| !k.is_child())
            .map(|(a, _)| *a)
            .collect();
        // The *plain* children, in order; the container argument, if any, is
        // the tuple's tail rather than an element (container-fields §3.4).
        let children: Vec<&Expr> = args
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| **k == FieldKind::Plain)
            .map(|(a, _)| *a)
            .collect();
        let container: Option<&Expr> = ctor.container().map(|(k, _)| args[k]);
        // The payload fields' skeletons, from their stored surface types —
        // filtered exactly as `payload` was, so the two stay aligned.
        let payload_skels: Vec<Option<Rc<crate::Skel>>> = ctor
            .fields
            .iter()
            .zip(&ctor.kind)
            .filter(|(_, k)| !k.is_child())
            .map(|((_, ty), _)| crate::skel_of_ty(ty))
            .collect();
        let fields =
            self.build_fields_skel(cx, &spine.ctors[i].0, &payload, true, &payload_skels, span)?;
        // A container's length, read *out of the label just built* rather than
        // re-elaborated from the argument: the arity term projects the same
        // field with the same function (`ConstBody::Arity`), so the two agree
        // by construction instead of by two elaborations happening to match
        // (docs/container-fields.md §3.4).
        let container = match (ctor.container(), &container) {
            (Some((_, p)), Some(arg)) => {
                // The projection's receiver must infer, and the tuple was
                // written for a checking position (§2.1): its root takes the
                // component type it was checked at.
                let receiver = match &fields {
                    Term::PairAt { ty: None, fst, snd } => Term::PairAt {
                        ty: Some(Rc::clone(&spine.ctors[i].0)),
                        fst: Rc::clone(fst),
                        snd: Rc::clone(snd),
                    },
                    other => other.clone(),
                };
                let (len, _, _) =
                    self.projection(cx, &spine.ctors[i].0, &Rc::new(receiver), p, span)?;
                Some((*arg, len))
            }
            _ => None,
        };
        // …then the injection path — over an **emission** copy of the spine
        // (`docs/annotation-component-respell-design.md` §2.3): the `Inl`/
        // `Inr` annotations of a constructor value carry `⟦c_j⟧` and the sum
        // tails verbatim, and their mass is the embedded field types — a
        // value of an `⟦Ir⟧`-field declaration writes `⟦Ir⟧` once per payload
        // *per injection step*. For a **flat** declaration the components
        // and the tails themselves are named (`D#payloadₖ`/`D#suffixₖ`,
        // `issues/inductive-spelling-codes-nonrecursive.md`); for a
        // recursive one the tails stay inline and only their embedded
        // field types respell. The structural spine above — `build_fields`'
        // checking, the container projection — is untouched.
        let spine_e = self.respell_spine(cx, &spine);
        // The `sup_f` slots, computed here rather than below because the
        // checked spelling of a **recursive** declaration's label injection
        // needs the same `shape` the slot takes: the label's type is the
        // `Wf`'s shape, not `pre_whnf`, and the two annotations agreeing is
        // what keeps the kernel's `Sum`-against-`Sum` query a `==`.
        let wf_slots = match &expected {
            Type::Wf { shape, arity, .. } if ind.recursive => {
                let depth = cx.gamma.entries.len();
                let known = self
                    .attempt
                    .wf_slot_annotations
                    .borrow()
                    .iter()
                    .find(|(ty, d, _)| *d == depth && *ty == expected)
                    .map(|(_, _, pair)| pair.clone());
                Some(match known {
                    Some(pair) => pair,
                    None => match self.wf_slot_refs(cx, shape, arity) {
                        Some((s, a)) => (Rc::new(s), Rc::new(a)),
                        None => self
                            .emit_wf_slots(cx, shape, arity, 0)
                            .unwrap_or_else(|| (Rc::clone(shape), Rc::clone(arity))),
                    },
                })
            }
            _ => None,
        };
        // …and the outermost injection's annotation (§4.1): the un-reduced
        // expected type for a flat declaration, the emitted shape for a
        // recursive one. A recursive declaration whose `expected` is not a
        // `Wf` is the error below; it takes no `@` and falls through to it.
        let at = if !self.emits_at_forms(cx) {
            None
        } else if ind.recursive {
            wf_slots.as_ref().map(|(s, _)| Rc::clone(s))
        } else {
            Some(match self.emit_ty(cx, pre_whnf, 0) {
                Some(r) => Rc::new(r),
                None => Rc::new(pre_whnf.clone()),
            })
        };
        let val = inject_at(&spine_e, i, ind.ctors.len(), fields, 0, at);
        if !ind.recursive {
            return Ok(PreparedCtor { term: val, children: Vec::new(), container: None });
        }
        // `val` is the label `ℓᵢ : S`; wrap it in `sup_f` with the children
        // (§5). Shape and arity are read off the type being built, never
        // rebuilt — the same discipline as the injections just above.
        let Type::Wf {
            level,
            shape,
            arity,
        } = &expected
        else {
            return err(
                "internal: a recursive declaration did not lower to a `Wf`",
                span,
            );
        };
        // …and the `sup_f`'s own two slots take their **references**
        // (`docs/wf-shape-code-design.md` §3.1). This is the value site the
        // measurement put first: a constructor value carries one whole shape
        // and one whole arity term, which for a large declaration is most of
        // what the value costs. The slots are the former's components rather
        // than annotations, so the kernel rebuilds `Wf(shape). arity` from
        // them and hands the agreement to conversion — a spelling choice like
        // every other one here. Child checking keeps reading the
        // *inline* `expected`, per §4's line.
        //
        // A **monomorphized** `Wf` (`List<Node>`) has no slots to name; its
        // two slots then take the same component respell the label's
        // `Inl`/`Inr` annotations just took (`respell_spine`), or neither
        // does — `respell_ty_deep`'s `Wf` arm respells shape and arity
        // together. Left inline, the kernel checked the label's respelled
        // annotations against the inline shape at every constructor value
        // (`Sum` vs `Sum`, 312 queries of the five-node FunctionIR/x86
        // module, 2026-09-06; issues/emission-site-respell-audit.md).
        let (shape_e, arity_e) = match wf_slots {
            Some(pair) => pair,
            None => match self.wf_slot_refs(cx, shape, arity) {
                Some((s, a)) => (Rc::new(s), Rc::new(a)),
                None => self
                    .emit_wf_slots(cx, shape, arity, 0)
                    .unwrap_or_else(|| (Rc::clone(shape), Rc::clone(arity))),
            },
        };
        // Shared across the declaration, like the children's annotation
        // (`wf.rs`'s `children_annotation`): the kernel's memo is keyed by
        // allocation identity.
        let (shape_e, arity_e) = {
            let depth = cx.gamma.entries.len();
            let mut seen = self.attempt.wf_slot_annotations.borrow_mut();
            match seen.iter().find(|(ty, d, _)| *d == depth && *ty == expected) {
                Some((_, _, (s, a))) => (Rc::clone(s), Rc::clone(a)),
                None => {
                    seen.push((expected.clone(), depth, (Rc::clone(&shape_e), Rc::clone(&arity_e))));
                    (shape_e, arity_e)
                }
            }
        };
        Ok(PreparedCtor {
            term: Term::Supf {
                level: level.clone(), shape: shape_e, arity: arity_e,
                label: Rc::new(val), children: Rc::new(Term::Triv { level: level.clone() }),
            },
            children, container,
        })
    }

    /// The field tuple: `pair(tag_refl, pair(a₁, … pair(a_k, ⟨⟩)))`, walking
    /// the Σ spine of `⟦c_i⟧` and checking each argument against the component
    /// the spine says it must have. `tag` marks the first component, which is
    /// the nominal tag rather than a field.
    pub(crate) fn build_fields<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        args: &[A],
        tag: bool,
        span: Span,
    ) -> R<Term> {
        self.build_fields_skel(cx, ctor_ty, args, tag, &[], span)
    }

    /// [`Self::build_fields`] plus, aligned positionally with `args`, each
    /// field's implicitness skeleton derived from its *stored surface* type
    /// (docs/implicit-binders-design.md §6.1's third site) — what lets a
    /// record literal's field be an implicit lambda. Empty for every caller
    /// that has no surface fields at hand.
    pub(crate) fn build_fields_skel<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        args: &[A],
        tag: bool,
        skels: &[Option<Rc<crate::Skel>>],
        span: Span,
    ) -> R<Term> {
        let head = self.whnf(cx, ctor_ty, span)?;
        let Type::Sigma {
            fst_level,
            snd_level,
            fst,
            snd,
        } = head
        else {
            // The Unit terminator (§3.1): every field consumed. `Unit` is
            // level-indexed (docs/unit-empty-level-indexing.md), so match at
            // *any* level and take the inhabitant's level from the type —
            // matching on `Unit^0` would silently stop terminating records
            // once a declaration lives above level 0.
            if let Type::Unit { level } = &head
                && args.is_empty()
            {
                return Ok(Term::Triv {
                    level: level.clone(),
                });
            }
            return err("internal: malformed constructor encoding", span);
        };
        // The tag's inhabitant is `srefl`, with the annotations read off the
        // encoding's own `sEq` rather than rebuilt.
        let (value, rest, skels_rest) = if tag {
            (tag_value(&fst), args, skels)
        } else {
            let (arg, rest) = args.split_first().ok_or(crate::ElabError::Elab {
                msg: "too few arguments".into(),
                span,
            })?;
            let skel = skels.first().and_then(|s| s.as_deref());
            (
                self.elab_check_skel(cx, arg.borrow(), &fst, &fst_level, None, skel)?,
                rest,
                skels.get(1..).unwrap_or(&[]),
            )
        };
        let value = Rc::new(value);
        let tail = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&value)));
        let tail_tm = self.build_fields_skel(cx, &tail, rest, false, skels_rest, span)?;
        // The emitted `Pair`'s annotations are the elimination-side projection
        // chain's dual and take the same reference spelling
        // (`docs/annotation-component-respell-design.md` §2.3): a constructor
        // *value* of an `⟦Ir⟧`-field declaration otherwise carries the field
        // type verbatim in its label tuple. The field arguments themselves
        // were checked against the inline components above, per the line.
        // …and the inline spelling of a component the decode handed back as
        // a code literal (`decode_deep`), so a tuple built at an `El ⌜Σ…⌝`
        // record type spells each link as the next link's own type does.
        // …unless the checked spellings are emitted, where the tuple carries
        // **no** type (`docs/intro-by-type-design.md` §2.1, §4.1): every layer
        // is a field of the injection or of the layer above it, a checking
        // position, and the kernel checks it against a description of the
        // component. `fst`/`snd` are the components of `ctor_ty`'s whnf —
        // the object the round exists to stop writing down — and they are
        // still what the fields were checked against above; they are just
        // not written.
        if self.emits_at_forms(cx) {
            return Ok(Term::PairAt {
                ty: None,
                fst: value,
                snd: Rc::new(tail_tm),
            });
        }
        let fst_e = match self.emit_ty(cx, &fst, 0) {
            Some(r) => Rc::new(r),
            None => fst,
        };
        let snd_e = match self.emit_ty(cx, &snd, 1) {
            Some(r) => Rc::new(r),
            None => snd,
        };
        Ok(Term::Pair {
            fst_level,
            snd_level,
            fst_ty: fst_e,
            snd_ty: snd_e,
            fst: value,
            snd: Rc::new(tail_tm),
        })
    }

    // -- match (§5) ---------------------------------------------------------

    /// `match` on a tier-0 inductive: nested `Case`, with the motive composed
    /// with the injection at each depth (§5.2).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_match_data(
        &self,
        cx: &Cx,
        form: MatchForm,
        ind: &Inductive,
        arms: &[Arm],
        scrut: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        if ind.index.is_some() {
            // Reachable only when a scrutinee's type arrived pre-reduced (the
            // family form is gone, and with it the index). Diagnosed rather
            // than mis-matched (docs/inductive-indexed-lowering.md §6).
            return err(
                format!(
                    "cannot `match` here: `{}` is an indexed family, but the \
                     scrutinee's type is not in the `{}(i)` family form",
                    ind.name, ind.name
                ),
                span,
            );
        }
        let n = ind.ctors.len();
        // Arms are permuted into declaration order; completeness, duplication
        // and arity are surface obligations, resolved before any lowering.
        let mut ordered: Vec<Option<&Arm>> = vec![None; n];
        for a in arms {
            let Some(i) = arm_ctor_index(ind, &a.ctor) else {
                return err(
                    format!("`{}` is not a constructor of `{}`", a.ctor, ind.name),
                    a.span,
                );
            };
            if ordered[i].replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
            if a.binders.len() != ind.ctors[i].fields.len() {
                return err(
                    format!(
                        "`{}` binds {} field(s), found {}",
                        a.ctor,
                        ind.ctors[i].fields.len(),
                        a.binders.len()
                    ),
                    a.span,
                );
            }
        }
        if n == 0 {
            // No constructors: the scrutinee is `Empty`, and the `match` is
            // absurdity elimination — the absurd-pattern case (§5.2).
            if !arms.is_empty() {
                return err(format!("`{}` has no constructors", ind.name), span);
            }
            return Ok(Term::ElimEmpty {
                level: mlvl,
                // The scrutinee's `Empty` is the one `lower_data` built, so
                // its level is the declaration's — read it off the scrutinee
                // rather than repeating the constant.
                scrut_level: scrut_lvl.clone(),
                motive: Rc::new(motive),
                scrut: Rc::new(scrut),
            });
        }
        let missing: Vec<&str> = ordered
            .iter()
            .enumerate()
            .filter(|(_, a)| a.is_none())
            .map(|(i, _)| ind.ctors[i].name.as_str())
            .collect();
        if !missing.is_empty() {
            return err(
                format!(
                    "`{}` is missing an arm for `{}`",
                    form.keyword(),
                    missing.join("`, `")
                ),
                span,
            );
        }
        let arms: Vec<&Arm> = ordered
            .into_iter()
            .map(|a| a.expect("checked above"))
            .collect();
        if ind.recursive {
            // Tier 1: one `elim_Wf`, not a case tree over the scrutinee
            // (docs/inductive-tier1-wf-lowering.md §6). Everything above is
            // surface bookkeeping and is shared.
            return self.elab_match_wf(cx, ind, &arms, scrut, scrut_ty, motive, mlvl, span);
        }
        if ind.infinitary() {
            // Tier 2: one `elim_W` over the tree, applied to its leaf proof
            // (docs/inductive-tier2-w-lowering.md §7).
            return self.elab_match_w(cx, ind, &arms, scrut, scrut_ty, motive, mlvl, span);
        }
        let spine = self.spine(scrut_ty, scrut_lvl, n, span)?;
        // The tier-0 twin of `wf.rs`'s motive respell
        // (`docs/family-type-code-defs-design.md`, 2026-08-12 extension). The
        // motive is written into every `Case` node of the tag tree and
        // substituted into every arm's obligation, so it is this lowering's
        // one Θ(arms)-copied whole type; the scrutinee's own `⟦D⟧` never
        // appears here at all (the spine's components do, and they stay
        // inline for `spine`/`tag_of` to read). The depth is 1, the motive's
        // own `z` binder: it is scoped over `(Γ, z : ⟦D⟧)` and a reference
        // minted for it is stamped one past `Γ`'s length. Passed as a depth
        // rather than shifted afterwards, because the instance route mints an
        // *open* reference whose arguments are already scoped there
        // (`docs/per-instantiation-type-codes-design.md` §4.1).
        let motive = self.respell_ty_at(cx, &motive, 1, 0).unwrap_or(motive);
        // The emission copy of the spine, beside the structural one — the same
        // split the tier-1 lowering takes (`docs/wf-shape-code-design.md`
        // §3.4). A tier-0 `match` writes the constructor payload types into
        // every `Case` and every injection, and a payload type embeds its
        // fields' lowerings verbatim.
        let spine_e = self.respell_spine(cx, &spine);
        self.case_tree(
            cx,
            ind,
            &arms,
            &spine,
            &spine_e,
            0,
            motive,
            &mlvl,
            Rc::new(scrut),
        )
    }

    /// The nested-`Case` recursion of §5.2. At depth `j` the context is `cx` —
    /// `Γ` plus the `j` `case_r` binders already pushed — `motive` is `M_j`
    /// over `cx, z : R_j`, and `scrut` is the `R_j`-typed scrutinee.
    ///
    /// `spine`'s components are scoped in the *original* `Γ`, so every use of
    /// one at depth `j` is weakened by `j` (and by `j+1` under a freshly pushed
    /// binder). The motive needs no such treatment: it is re-scoped by the
    /// substitution that composes it with the injection.
    #[allow(clippy::too_many_arguments)]
    fn case_tree(
        &self,
        cx: &Cx,
        ind: &Inductive,
        arms: &[&Arm],
        spine: &Spine,
        spine_e: &Spine,
        j: usize,
        motive: Type,
        mlvl: &Level,
        scrut: Rc<Term>,
    ) -> R<Term> {
        let n = arms.len();
        let d = j as u32;
        if j + 1 == n {
            // Last constructor: no `Case` — the arm body itself, checked at
            // `M_j[scrut/z]`. At `j = 0` that is the whole `match`.
            let expected =
                motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut)));
            let ctor_ty = spine.ctors[j].0.shift_local(d);
            let skels = arm_field_skels(ind, j);
            return self.elab_arm(cx, arms[j], &ctor_ty, &scrut, &expected, mlvl, &skels);
        }
        let ctor_lvl = spine.ctors[j].1.clone();
        let tail_lvl = spine.tails[j].1.clone();
        // Emitted: this `Case`'s two component types and the injections below.
        // The binder types pushed into the elaborator's own context, and every
        // type `elab_arm` reads a field out of, stay inline (§4's line).
        let ctor_ty = Rc::new(spine_e.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(spine_e.tails[j].0.shift_local(d));
        // case_l: binder `x : ⟦c_j⟧` over Γ_j, body at `M_j[inl x/z]`.
        let mut lcx = cx.clone();
        lcx.push(
            "#scrut".into(),
            spine.ctors[j].0.shift_local(d),
            ctor_lvl.clone(),
        );
        // The injection's own summand annotations are scoped in the *original*
        // `\u{393}`, so they carry the shift of whatever context the injection
        // is being placed in — which is **not** always `d + 1`. `l_expected`
        // lands in `lcx` (one binder past `cx`, so `d + 1`); `inner_motive`
        // lands in `rcx, z` (two, so `d + 2`), which is what
        // `embed(\u{2026}, 2)` on the same line says. Getting this wrong is
        // invisible at a closed payload type *and* at \u{2264} 2 constructors,
        // and it is axis 6 of docs/testing-generated-terms.md, whose
        // 2026-08-04 round fixed the same shift in `wf_case_tree` /
        // `idx_case_tree` / `indexed_case_tree` and missed this one: at a
        // *non-dependent* motive `z` never occurs, so the bad annotations are
        // substituted away before the kernel sees them.
        let injected = |val: Term, inl: bool, sh: u32| {
            let (lhs, rhs) = (
                spine_e.ctors[j].0.shift_local(sh),
                spine_e.tails[j].0.shift_local(sh),
            );
            let (lhs, rhs) = (Rc::new(lhs), Rc::new(rhs));
            let (lhs_level, rhs_level) = (ctor_lvl.clone(), tail_lvl.clone());
            let val = Rc::new(val);
            if inl {
                Term::Inl {
                    lhs_level,
                    rhs_level,
                    lhs,
                    rhs,
                    val,
                }
            } else {
                Term::Inr {
                    lhs_level,
                    rhs_level,
                    lhs,
                    rhs,
                    val,
                }
            }
        };
        let l_expected = motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(injected(
            Term::Var(LocalVar(0)),
            true,
            d + 1,
        ))));
        let l_skels = arm_field_skels(ind, j);
        let case_l = self.elab_arm(
            &lcx,
            arms[j],
            &spine.ctors[j].0.shift_local(d + 1),
            &Rc::new(Term::Var(LocalVar(0))),
            &l_expected,
            mlvl,
            &l_skels,
        )?;
        // case_r: binder `y : R_{j+1}` over Γ_j; inside it, the next `Case` on
        // `y`, whose motive is `M_j` composed with `inr` and weakened past `y`.
        let mut rcx = cx.clone();
        rcx.push(
            "#rest".into(),
            spine.tails[j].0.shift_local(d),
            tail_lvl.clone(),
        );
        let inner_motive = motive.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(injected(
            Term::Var(LocalVar(0)),
            false,
            d + 2,
        ))));
        let case_r = self.case_tree(
            &rcx,
            ind,
            arms,
            spine,
            spine_e,
            j + 1,
            inner_motive,
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
        )?;
        Ok(Term::Case {
            lhs_level: ctor_lvl,
            rhs_level: tail_lvl,
            motive_level: mlvl.clone(),
            lhs: ctor_ty,
            rhs: tail_ty,
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    /// One arm body, with its field binders bound to projections of the
    /// constructor value (§5.1). The binders are *aliases*, not kernel
    /// binders: the kernel has no `let`, so each use is the projection term.
    /// `ctor_ty` is `⟦c_i⟧` scoped in `cx`.
    #[allow(clippy::too_many_arguments)]
    fn elab_arm(
        &self,
        cx: &Cx,
        arm: &Arm,
        ctor_ty: &Type,
        value: &Rc<Term>,
        expected: &Type,
        mlvl: &Level,
        // Aligned with the binders: each field's implicitness skeleton from
        // its stored surface type (docs/implicit-binders-design.md §3.1), so
        // a matched-out function field inserts at its uses in the arm body.
        // Empty when the caller cannot align them (a ctor with children —
        // the Σ order is payload-then-children, not declaration order).
        skels: &[Option<Rc<crate::Skel>>],
    ) -> R<Term> {
        let mut acx = cx.clone();
        // Walk the Σ spine of the constructor, skipping the tag (entry 0), and
        // alias each surface binder to `fst(snd^j value)`.
        let mut cur = ctor_ty.clone();
        let mut pair = Rc::clone(value);
        let mut binders = arm.binders.iter().map(|p| p.name().to_string());
        let mut skels = skels.iter();
        let mut first = true;
        loop {
            let head = self.whnf(&acx, &cur, arm.span)?;
            let Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } = head
            else {
                break;
            };
            // The annotations in the emission spelling: the whnf's components
            // are the inline lowering of every field type, and each met the
            // named spelling the value was built with — a whole-type walk per
            // alias (`issues/emission-walker-residual-sites.md`, item 2). Not
            // the unannotated `@` projections `project_field` writes: the
            // elaborator's own reducts substitute a constructor literal for
            // the scrutinee, and a projection of an unannotated tuple does not
            // infer. `cur` stays the structural copy.
            let fst_e = match self.emit_ty(&acx, &fst, 0) {
                Some(t) => Rc::new(t),
                None => Rc::clone(&fst),
            };
            let snd_e = match self.emit_ty(&acx, &snd, 1) {
                Some(t) => Rc::new(t),
                None => Rc::clone(&snd),
            };
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst_e),
                snd_ty: Rc::clone(&snd_e),
                pair: Rc::clone(&pair),
            });
            let rest = Rc::new(Term::Snd {
                fst_level: fst_level.clone(),
                snd_level,
                fst_ty: fst_e,
                snd_ty: snd_e,
                pair: Rc::clone(&pair),
            });
            cur = snd.apply_local(&LocalSubst::id(&acx.gamma).extended(Rc::clone(&proj)));
            pair = rest;
            if first {
                // The nominal tag: no surface name, not bindable.
                first = false;
                continue;
            }
            let Some(name) = binders.next() else { break };
            acx.aliases.push(Rc::new(Alias {
                skel: skels.next().and_then(|s| s.clone()),
                name: name.clone(),
                depth: acx.names.len(),
                term: proj,
                ty: (*fst).clone(),
                level: fst_level,
            }));
        }
        self.elab_check(&acx, &arm.body, expected, mlvl)
    }

    /// Project field `idx` out of a record value (docs/surface-records.md
    /// §4.3). This is [`Self::elab_arm`]'s walk with the aliasing removed:
    /// step down the Σ spine, skipping the nominal tag, and stop at the
    /// wanted field. `π_j = fst(snd^j(value))`, with the *j*-th `snd` carrying
    /// the earlier projections substituted into the tail — which is what makes
    /// a dependent field's type come out right (`m.unit_l` mentions `m.op` and
    /// `m.unit`) with no special handling.
    ///
    /// Since the annotations are read off the type being projected, the result
    /// synthesizes: nothing here introduces a checking obligation.
    pub(crate) fn project_field(
        &self,
        cx: &Cx,
        ind: &Inductive,
        record_ty: &Type,
        value: Rc<Term>,
        idx: usize,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        // The named projection, where the declaration registered one
        // (`gendefs.rs`, `issues/theorem-field-projection-oom.md`, and
        // `docs/per-instantiation-type-codes-design.md` §13 for the
        // telescoped case). It is the walk below with its exponent removed
        // *and* with no `Σ` ever reconstituted against the receiver's own
        // reference, so it comes first; the walk stays as the fallback for
        // the records whose registration declined.
        //
        // A telescoped record's definition is applied to the instantiation's
        // arguments first, and those come off the receiver's type — its own
        // reference spine, or §4.1's hole-match of the inline copy. The
        // definition's domain at those arguments *is* the receiver's type,
        // which is the whole difference: the kernel's `App` rule matches it
        // syntactically where the `Fst`/`Snd` rule below would reconstitute
        // `Σ(fst). snd` and convert the reference against it.
        // The closed device fires whatever the receiver is: there the
        // definitions exist to remove the walk's *exponent*, and a literal
        // receiver is exactly the case that blows up without them. The
        // telescoped one asks first, because there the definitions buy a
        // syntactic comparison and charge δ + β for a computation — and only
        // at receiver shapes that survive substitution, which is what
        // `receiver_admits_reference` is for.
        let telescoped = !ind.params.is_empty() || !ind.valparams.is_empty();
        // The receiver gate first and the recovery only behind it, as before:
        // asking `instance_args` for a receiver the reference cannot stand at
        // would be the match's whole cost for nothing. Both answers are kept
        // so that the listing below can tell the three declines apart without
        // asking either question twice.
        //
        // The **dependent** telescoped device (`docs/telescoped-record-
        // projections-design.md` §4) is exempt at every receiver, exactly as
        // the closed device is and for its reason. The gate is a real trade
        // only where the alternative is linear: a reference is cheap to
        // compare and dear to compute through, δ + β per read per level, which
        // is what `caller_native_memory_same_27/28` could not afford. On a
        // dependent spine the alternative is the *exponent*, so a literal
        // receiver is the case that needs the name most. The payers are on the
        // other side of the same predicate — `MachineState<M>`,
        // `StackAccess<M>`, `And<P, Q>` and `reused_callee`'s twenty-eight
        // state chain all have non-dependent spines and keep the gate
        // verbatim — and every read the parser library makes (`op.end`,
        // `inner.end`, `close.forward`) is off a **bare** binder, which is
        // precisely what the gate declines.
        let admits = !telescoped
            || self.rec_projs_are_dependent(ind.tag)
            || receiver_admits_reference(&value);
        let args = admits
            .then(|| self.instance_args(cx, ind, record_ty))
            .flatten();
        if let Some(args) = args.as_ref()
            && let Some(t) = self.rec_proj_ref_at(cx, ind.tag, idx, args, &value)
        {
            crate::stats::count(crate::stats::Counter::ProjectionNamed);
            return Ok(t);
        }
        decline!(
            "project_field",
            &ind.name,
            "{}-{idx}",
            if !admits {
                "receiver-gate"
            } else if args.is_none() {
                "instance-args"
            } else {
                "no-projection-def"
            }
        );
        // Checked projections carry no component annotations. Their inferred
        // field type is a structural read too: keep it inline until a caller
        // actually writes an annotation. Emitting a selected conjunction here
        // recursively matches every remaining instance again at every dot.
        if self.emits_at_forms(cx) {
            crate::stats::count(crate::stats::Counter::ProjectionStructural);
            let mut cur = record_ty.clone();
            let mut pair = value;
            for step in 0..=idx + 1 {
                let Type::Sigma { fst_level, fst, snd, .. } = self.whnf(cx, &cur, span)? else {
                    return err(
                        format!("internal: `{}` has no field spine entry {step} (malformed record encoding)", ind.name),
                        span,
                    );
                };
                let proj = Rc::new(Term::FstAt { pair: Rc::clone(&pair) });
                if step == idx + 1 {
                    return Ok(((*proj).clone(), (*fst).clone(), fst_level));
                }
                cur = crate::stats::timed(crate::stats::Timer::ProjectionSubst,
                    || snd.apply_local(&LocalSubst::id(&cx.gamma).extended(proj)));
                pair = Rc::new(Term::SndAt { pair });
            }
            unreachable!("the loop returns at step idx + 1");
        }
        let mut cur = record_ty.clone();
        // Compute the declaration-binder spelling once, then walk it beside
        // the inline structural copy. Most fallback records have nothing to
        // respell and keep this as `None`, so their old path stays allocation-
        // free; a parameterized law record such as `IrPassLaws(R, alg)` gets
        // the exact component spelling its closed Π binder received.
        let mut cur_emit = crate::stats::timed(crate::stats::Timer::ProjectionEmit, || match self.emit_ty(cx, record_ty, 0) {
            Some(emitted) => Some(emitted),
            // The type may **already** be the emission spelling: since
            // `docs/per-instantiation-type-codes-design.md` a parameterized
            // record's instantiation has a name, so a receiver's inferred
            // type arrives as `El (app(D#tycode_fn^δ; ā))` — and `emit_ty` is
            // idempotent, so "nothing left to change" and "nothing to name"
            // look alike here. Without this the walk fell to the inline
            // branch and every `Fst`/`Snd` annotation of the chain met the
            // reference the value's own type carries (`Sigma`/`El(?)`, the
            // largest row of the x86 certificates before this line).
            None => self.unspell_here(record_ty).map(|_| record_ty.clone()),
        });
        let mut pair = value;
        // Entry 0 is the tag (§3.3), so field `idx` is spine entry `idx + 1`.
        for step in 0..=idx + 1 {
            let head = self.whnf(cx, &cur, span)?;
            let Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } = head
            else {
                return err(
                    format!(
                        "internal: `{}` has no field spine entry {step} \
                         (malformed record encoding)",
                        ind.name
                    ),
                    span,
                );
            };
            // `cur` remains the structural copy. Only annotations come from
            // the parallel emission walk, mirroring constructor/match
            // lowering's established split.
            let (fst_e, snd_e) = match &cur_emit {
                Some(emitted) => {
                    // Did this entry come from *behind* something — a whole-type
                    // reference, a code — or is the emission copy already the
                    // `Σ` it hands back? Only the first case has components in
                    // a spelling this walk did not choose, and only it may
                    // pay a respell. The second is every entry after the
                    // first, where the tail is the previous entry's *already
                    // emitted* `snd` with the previous projection substituted
                    // in — and that substitution is the walk's own exponent
                    // (`issues/theorem-field-projection-oom.md`), so calling
                    // `emit_ty` on it per entry re-walks and re-materializes
                    // an exponentially large type once per field. That is a
                    // 4 GiB abort on the eleven-field cross-referencing record
                    // of `crates/elab/tests/record_projection_size.rs`
                    // (§13.10 of `docs/per-instantiation-type-codes-design.md`,
                    // and §13.8 is the same sentence at the registration side:
                    // the field type is respelled, the tail never).
                    let behind_a_name = !matches!(emitted, Type::Sigma { .. });
                    let Type::Sigma { fst, snd, .. } = self.whnf(cx, emitted, span)? else {
                        return err("internal: respelling changed a record spine's shape", span);
                    };
                    if !behind_a_name {
                        (fst, snd)
                    } else {
                        // The emitted copy of an unparameterized record is its
                        // `El (D#tycode^δ)` reference, and what `whnf` hands
                        // back from behind it is the registry's *inline*
                        // lowering — `Vec(⟦Bool⟧; 64)` where every other site,
                        // the constructor tuple (`build_fields_skel`) first
                        // among them, spells `Vec(El (Bool#tycode^δ); 64)`. A
                        // record with no named projections (a non-dependent
                        // spine, `register_rec_projs`) reaches this walk for
                        // its parameters' fields inside a record *definition*,
                        // and the chain's annotations then met the tuple's at
                        // every instance of the defined record: the
                        // `Sigma`/`Sigma` bucket of the x86 fetch certificates
                        // (issues/unnameable-annotation-occurrences.md,
                        // 2026-09-10). Respell the components, as the tuple
                        // does; idempotent when nothing is left to respell.
                        (
                            self.emit_ty(cx, &fst, 0).map_or(fst, Rc::new),
                            self.emit_ty(cx, &snd, 1).map_or(snd, Rc::new),
                        )
                    }
                }
                // A record type that arrived as a code literal (`El ⌜Σ…⌝`,
                // a `→ Type` body's quote) whnf's one level at a time, and
                // the components it hands back are the *un*decoded tails;
                // the annotations take their inline spelling so each link
                // agrees with the next (`decode_deep`).
                None => (
                    decode_deep(&fst).map_or_else(|| Rc::clone(&fst), Rc::new),
                    decode_deep(&snd).map_or_else(|| Rc::clone(&snd), Rc::new),
                ),
            };
            // Component projections (inside quotes) still carry annotations,
            // so their links need the parallel emission spelling above.
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst_e),
                snd_ty: Rc::clone(&snd_e),
                pair: Rc::clone(&pair),
            });
            if step == idx + 1 {
                return Ok(((*proj).clone(), (*fst_e).clone(), fst_level));
            }
            let rest = Rc::new(Term::Snd {
                fst_level,
                snd_level,
                fst_ty: Rc::clone(&fst_e),
                snd_ty: Rc::clone(&snd_e),
                pair: Rc::clone(&pair),
            });
            cur = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&proj)));
            if cur_emit.is_some() {
                cur_emit = Some(snd_e.apply_local(&LocalSubst::id(&cx.gamma).extended(proj)));
            }
            pair = rest;
        }
        unreachable!("the loop returns at step idx + 1")
    }

    /// The record declaration a lowered type belongs to, if it is one. A
    /// non-record inductive gives `None`: its field names are positional, not
    /// accessors (docs/surface-records.md §2).
    pub(crate) fn record_of(&self, ty: &Type) -> Option<Rc<Inductive>> {
        self.tag_of(ty).filter(|i| i.is_record)
    }

    /// [`Self::record_of`] with a reduction step behind it, for a receiver
    /// whose type arrived through a **`Val -> Type` value** rather than through
    /// a type annotation: `dom(env)` with `dom := λ e => NatEnv(e)` is `El` of
    /// a β-redex, and [`decoded`] is deliberately context-free — it strips `El`
    /// off *canonical* codes only, because unfolding anything else is
    /// conversion's job (docs/types-as-expressions.md §4). So the structural
    /// read is tried first and unchanged, and `whnf` is paid only when it
    /// fails, which is exactly the new shape.
    pub(crate) fn record_of_at(&self, cx: &Cx, ty: &Type, span: Span) -> Option<Rc<Inductive>> {
        if let Some(ind) = self.record_of(ty) {
            return Some(ind);
        }
        let head = self.whnf(cx, ty, span).ok()?;
        // …and through a **name**, which is the one new shape this round adds
        // at this reader (`docs/name-per-value-design.md` §4's audit). The
        // readback keeps a glued encoding folded on purpose — that is what
        // every structural reader anchors on — so a receiver whose type came
        // out of a named `build_ctor` reduct arrives as `El (D#tycode_fn^δ ā)`
        // where the rewriter's reduct was the inline lowering, and `tag_of`
        // reads a *shape*. `unspell_here` is the registry's own exact inverse
        // and is what restores it.
        self.record_of(&head)
            .or_else(|| self.record_of(&self.unspell_here(&head)?))
    }
}

/// Is this field a recursive occurrence of the declaration being read
/// (`docs/inductive-tier1-wf-lowering.md` §1)? Three outcomes, and the third
/// is why this returns a `Result` rather than a `bool`:
///
/// - `false` — the field does not mention `name` at all.
/// - `true` — the field *is* `name<p̄>` applied to the declaration's own
///   parameters in order: the uniform, direct occurrence, which becomes a
///   child in the `Vec`.
/// - an error — `name` occurs, but nested under another type constructor or
///   at different arguments. Both are lowerable in principle and neither is
///   lowered here; a rejection with its own message is the whole point of
///   classifying rather than scanning.
/// Classify every field of one constructor (`docs/container-fields.md` §3.1),
/// which has to be one pass rather than one call per field: a container
/// field's length names an *earlier* field, and the position restrictions
/// ("at most one container, last among the children") are properties of the
/// sequence.
fn classify_fields(
    c: &CtorDecl,
    name: &str,
    params: &[String],
    vparams: &[String],
) -> R<Vec<FieldKind>> {
    let mut kinds: Vec<FieldKind> = Vec::with_capacity(c.fields.len());
    let mut payload_k = 0usize;
    // (payload index, span) of each `Nat` field seen so far, by name — the
    // only things a container length may refer to.
    let mut nat_fields: Vec<(String, usize)> = Vec::new();
    for f in &c.fields {
        // `[D; len]` — a container field.
        if let TyKind::Vec { elem, len } = &f.ty.kind
            && classify_field(elem.as_ref(), name, params, vparams, &c.name)?
        {
            if let Some((prev, _)) = kinds
                .iter()
                .enumerate()
                .find(|(_, k)| matches!(k, FieldKind::Container { .. }))
            {
                let _ = prev;
                return err(
                    format!(
                        "`{}` has more than one container field: the children are one \
                         tuple, and splitting it at a computed length is not an operation \
                         it has (docs/container-fields.md §3.1)",
                        c.name
                    ),
                    f.ty.span,
                );
            }
            // Phase 1: the length must be a bare payload field name (§3.1).
            let ExprKind::Var(lname) = &len.kind else {
                return err(
                    format!(
                        "a container field's length must be the name of a `Nat` field \
                         declared before it (docs/container-fields.md §3.1)"
                    ),
                    len.span,
                );
            };
            let Some((_, idx)) = nat_fields.iter().find(|(n, _)| n == lname) else {
                return err(
                    format!(
                        "`{lname}` is not a `Nat` field of `{}` declared before this one; \
                         a container field's length is evaluated inside the shape, so it \
                         can only name an earlier payload field \
                         (docs/container-fields.md §3.1)",
                        c.name
                    ),
                    len.span,
                );
            };
            kinds.push(FieldKind::Container { len_payload: *idx });
            continue;
        }
        // `(y: A) -> D` — a recursive function field (tier 2 §1). Only the
        // exact shape reaches here: `reject_function_fields` has already
        // refused every other function type that mentions `D`.
        if let TyKind::Fn { dom, cod, .. } = &f.ty.kind
            && occurs(dom, name).is_none()
            && classify_field(cod, name, params, vparams, &c.name)?
        {
            kinds.push(FieldKind::FnChild);
            continue;
        }
        if classify_field(&f.ty, name, params, vparams, &c.name)? {
            if kinds
                .iter()
                .any(|k| matches!(k, FieldKind::Container { .. }))
            {
                return err(
                    format!(
                        "a recursive field of `{}` may not follow a container field: \
                         reaching it would mean skipping the container's children \
                         (docs/container-fields.md §3.1)",
                        c.name
                    ),
                    f.ty.span,
                );
            }
            kinds.push(FieldKind::Plain);
            continue;
        }
        if matches!(f.ty.kind, TyKind::Nat)
            && let Some(n) = &f.name
        {
            nat_fields.push((n.clone(), payload_k));
        }
        kinds.push(FieldKind::Payload);
        payload_k += 1;
    }
    Ok(kinds)
}

/// Decompose a constructor's result annotation `D<params>(pattern)` into an
/// [`IdxPat`] (docs/inductive-indexed-lowering.md §2–§3): the type must be
/// the declaration at its own parameters, and the index a depth-one, linear,
/// constructor-headed pattern over the constructor's own fields. Everything
/// else is a rejection with the route that *does* cover it named (§8.1).
fn parse_result_index<'a>(
    c: &CtorDecl,
    r: &'a Expr,
    name: &str,
    params: &[String],
    ctors: &[CtorDecl],
    ity: &IdxTy,
) -> R<IdxPat> {
    let idx = parse_result_head(c, r, name, params)?;
    // A declared index's constructors are looked up by name first, so a
    // *nullary* one (`Bal(SLeaf)`) is a pattern and not the bare-variable
    // (fording) case below.
    let icts = ity.ctors();
    let head_of = |e: &'a Expr| -> Option<(usize, &'a [Expr])> {
        match &e.kind {
            ExprKind::Var(v) => icts.iter().position(|k| k.name == *v).map(|i| (i, &[][..])),
            ExprKind::App { head, args, .. } => match &head.kind {
                ExprKind::Var(v) => icts
                    .iter()
                    .position(|k| k.name == *v)
                    .map(|i| (i, args.as_slice())),
                _ => None,
            },
            _ => None,
        }
    };
    if !matches!(ity, IdxTy::Nat)
        && let Some((k, iargs)) = head_of(idx)
    {
        return decl_index_pattern(c, idx, ity, k, iargs);
    }
    match &idx.kind {
        ExprKind::Num(n) if n.is_zero() && matches!(ity, IdxTy::Nat) => Ok(IdxPat {
            ctor: 0,
            vars: vec![],
        }),
        ExprKind::Var(v) if v == "Zero" && matches!(ity, IdxTy::Nat) => Ok(IdxPat {
            ctor: 0,
            vars: vec![],
        }),
        ExprKind::App { head, args, .. }
            if matches!(ity, IdxTy::Nat)
                && matches!(&head.kind, ExprKind::Var(s) if s == "Succ") =>
        {
            let [arg] = args.as_slice() else {
                return err("`Succ` takes one argument", idx.span);
            };
            let ExprKind::Var(v) = &arg.kind else {
                return err(
                    format!(
                        "`{}`'s result index is deeper than one constructor: only \
                         `Succ(x)` with `x` a field is index-recursive; a deeper or \
                         computed index fords over `sEq` \
                         (issues/indexed-families.md routes 2b/3), not yet generated",
                        c.name
                    ),
                    idx.span,
                );
            };
            let Some(field) = c
                .fields
                .iter()
                .position(|f| f.name.as_deref() == Some(v.as_str()))
            else {
                return err(
                    format!(
                        "the pattern variable `{v}` must be a field of `{}` — every \
                         result-index variable is a (named) constructor field",
                        c.name
                    ),
                    arg.span,
                );
            };
            if !matches!(c.fields[field].ty.kind, TyKind::Nat) {
                return err(
                    format!("the pattern variable `{v}` must be a `Nat` field"),
                    arg.span,
                );
            }
            Ok(IdxPat {
                ctor: 1,
                vars: vec![field],
            })
        }
        ExprKind::Num(_) if matches!(ity, IdxTy::Nat) => err(
            format!(
                "`{}`'s result index is a numeral above `0`, which is a pattern deeper \
                 than one constructor — not index-recursive \
                 (docs/inductive-indexed-lowering.md §8.1)",
                c.name
            ),
            idx.span,
        ),
        // A bare-variable result index. Two very different situations wear this
        // spelling, and sending both toward fording is what
        // `docs/surface-existential-investigation.md` §C.7 asked this round to
        // correct:
        //
        // - *uniform* — every constructor's index is a bare variable. Then it
        //   is not an index at all, it is a **parameter**: it does not vary per
        //   constructor result, and it lowers by substitution with none of
        //   route 2b's machinery (no fording, no stored equation, no `Wf`
        //   skeleton, no UIP, no `Id`-transport). Say so, and name the grammar
        //   that now exists.
        // - *non-uniform* — some other constructor pins the index. Then it
        //   genuinely is the general case, and route 2b generates it (§3.4's
        //   non-uniform bare-variable row).
        ExprKind::Var(v) if matches!(ity, IdxTy::Nat) && all_bare_var_indices(ctors, ity) => err(
            format!(
                "`{}`'s result index `{v}` is a bare variable in *every* constructor of \
                 `{name}`, which makes it a **parameter**, not an index — it does not \
                 vary per constructor result. Write it as one: \
                 `inductive {name}({v}: Nat) {{ … }}`, or `record {name}({v}: Nat) {{ … }}` \
                 if `{name}` has a single constructor \
                 (docs/surface-value-parameters.md §1, §6). A genuinely varying index is the \
                 fording case (issues/indexed-families.md route 2b), and this is not it.",
                c.name
            ),
            idx.span,
        ),
        ExprKind::Var(v) => err(
            format!(
                "`{}`'s result index `{v}` is not constructor-headed: a bare-variable \
                 index means the constructor targets *every* index, which is the general \
                 (fording) case — docs/inductive-fording-lowering.md",
                c.name
            ),
            idx.span,
        ),
        _ => err(
            format!(
                "`{}`'s result index is computed, not constructor-headed: a computed \
                 index fords over `sEq` (docs/inductive-fording-lowering.md)",
                c.name
            ),
            idx.span,
        ),
    }
}

/// The `D<params>(index)` head of a result annotation, shared by both routes:
/// the type must be the declaration at its own parameters, and what comes back
/// is the single index expression. Route 1 then insists it is a pattern; route
/// 2b does not constrain it at all (fording doc §2).
fn parse_result_head<'a>(c: &CtorDecl, r: &'a Expr, name: &str, params: &[String]) -> R<&'a Expr> {
    let ExprKind::App { head, args, .. } = &r.kind else {
        return err(
            format!(
                "`{}`'s result annotation must be `{name}<…>(index)` — an applied \
                 occurrence of the declaration itself",
                c.name
            ),
            r.span,
        );
    };
    let (rname, targs): (&str, &[Ty]) = match &head.kind {
        ExprKind::Var(n) => (n, &[]),
        ExprKind::TyApp { head, args } => match &head.kind {
            ExprKind::Var(n) => (n, args),
            _ => return err("malformed result annotation", r.span),
        },
        _ => return err("malformed result annotation", r.span),
    };
    if rname != name {
        return err(
            format!(
                "`{}` is a constructor of `{name}`, so its result must be `{name}`",
                c.name
            ),
            r.span,
        );
    }
    let uniform = targs.len() == params.len()
        && targs.iter().zip(params).all(|(a, p)| {
            matches!(&a.kind, TyKind::Named { name: an, args } if an == p && args.is_empty())
        });
    if !uniform {
        return err(
            format!(
                "`{}`'s result must use `{name}`'s own parameters in order (`{}`); \
                 parameters are uniform, only the index varies per constructor",
                c.name,
                params.join(", ")
            ),
            r.span,
        );
    }
    let [idx] = args.as_slice() else {
        return err(
            format!("`{name}` takes exactly one index this round"),
            r.span,
        );
    };
    Ok(idx)
}

/// `D(I_k(x₁ … x_r))` at a **declared** index (§8.2): the index constructor is
/// `k`, and each of its arguments must be filled by a distinct named field of
/// this constructor. Depth one and linear, exactly as at `Nat` — the pattern
/// grammar is the same, only the constructor list it draws from changed.
fn decl_index_pattern(
    c: &CtorDecl,
    idx: &Expr,
    ity: &IdxTy,
    k: usize,
    iargs: &[Expr],
) -> R<IdxPat> {
    let icts = ity.ctors();
    let ict = &icts[k];
    let iname = ity.name();
    if iargs.len() != ict.rec.len() {
        return err(
            format!(
                "`{}`'s result index applies `{}` to {} argument(s), but it takes {}",
                c.name,
                ict.name,
                iargs.len(),
                ict.rec.len()
            ),
            idx.span,
        );
    }
    let mut vars = Vec::with_capacity(iargs.len());
    let nested = |e: &Expr| match &e.kind {
        ExprKind::Var(v) => icts.iter().any(|c| c.name == *v),
        ExprKind::App { head, .. } => {
            matches!(&head.kind, ExprKind::Var(v) if icts.iter().any(|c| c.name == *v))
        }
        _ => false,
    };
    for (a, arg) in iargs.iter().enumerate() {
        // A nested index constructor is the depth-two case, not a missing
        // field: name it as such rather than as a scope error.
        if nested(arg) {
            return err(
                format!(
                    "`{}`'s result index is deeper than one constructor: `{}`'s argument \
                     is itself constructor-headed, which needs simultaneous recursion — \
                     a real extension, deferred (docs/inductive-indexed-lowering.md §8.1)",
                    c.name, ict.name
                ),
                arg.span,
            );
        }
        let ExprKind::Var(v) = &arg.kind else {
            return err(
                format!(
                    "`{}`'s result index is deeper than one constructor: an argument of \
                     `{}` must be a field of `{}`, not a term; a deeper or computed \
                     index fords over `sEq` (issues/indexed-families.md routes 2b/3), \
                     not yet generated",
                    c.name, ict.name, c.name
                ),
                arg.span,
            );
        };
        let Some(field) = c
            .fields
            .iter()
            .position(|f| f.name.as_deref() == Some(v.as_str()))
        else {
            return err(
                format!(
                    "the pattern variable `{v}` must be a field of `{}` — every \
                     result-index variable is a (named) constructor field",
                    c.name
                ),
                arg.span,
            );
        };
        if vars.contains(&field) {
            return err(
                format!(
                    "`{}`'s result index repeats the pattern variable `{v}`: a pattern \
                     is linear, and an equation between two of its arguments is the \
                     fording case (issues/indexed-families.md route 2b)",
                    c.name
                ),
                arg.span,
            );
        }
        // Only a *recursive* argument's variable has a type this can check
        // without elaborating: it is the index type itself. A payload
        // argument's is checked where the index term is built (§5).
        if ict.rec[a]
            && !matches!(&c.fields[field].ty.kind,
                         TyKind::Named { name: n, args } if n == iname && args.is_empty())
        {
            return err(
                format!(
                    "the pattern variable `{v}` fills a recursive argument of `{}`, so \
                     it must be a `{iname}` field of `{}`",
                    ict.name, c.name
                ),
                arg.span,
            );
        }
        vars.push(field);
    }
    Ok(IdxPat { ctor: k, vars })
}

/// Classify an indexed constructor's fields
/// (docs/inductive-indexed-lowering.md §3, generalized by §8.2): a pattern
/// variable is [`FieldKind::IndexVar`], a recursive occurrence `D<params>(x)`
/// at a pattern variable that is a **recursive argument of the index
/// constructor** is a [`FieldKind::Plain`] child-in-the-spine, and any other
/// self-occurrence rejects with its own message. The second return is
/// [`Ctor::rec_at`]: which index-constructor argument each recursive field
/// draws its `rec` from.
fn classify_fields_indexed(
    c: &CtorDecl,
    name: &str,
    params: &[String],
    pat: &IdxPat,
    ity: &IdxTy,
) -> R<(Vec<FieldKind>, Vec<Option<usize>>)> {
    let icts = ity.ctors();
    let ict = &icts[pat.ctor];
    // Pattern-variable field position → the index-constructor argument it
    // fills. The inverse of `pat.vars`, which is the direction every lookup
    // below wants.
    let arg_of = |k: usize| pat.vars.iter().position(|&f| f == k);
    let mut kinds = Vec::with_capacity(c.fields.len());
    let mut rec_at: Vec<Option<usize>> = Vec::with_capacity(c.fields.len());
    for (k, f) in c.fields.iter().enumerate() {
        if arg_of(k).is_some() {
            kinds.push(FieldKind::IndexVar);
            rec_at.push(None);
            continue;
        }
        // `D<params>(e)` — parsed as an expression in type position, so it
        // arrives as `OfExpr` (parser.rs `ty_atom`: an applied type is never
        // called, so the call is the index application).
        if let TyKind::OfExpr(e) = &f.ty.kind
            && let ExprKind::App { head, args, .. } = &e.kind
            && let Some((rname, targs)) = named_head(head)
            && rname == name
        {
            let uniform = targs.len() == params.len()
                && targs.iter().zip(params).all(|(a, p)| {
                    matches!(&a.kind, TyKind::Named { name: an, args } if an == p
                             && args.is_empty())
                });
            if !uniform {
                return err(
                    format!(
                        "field of `{}` uses `{name}` at arguments other than its own \
                         parameters; parameters are monomorphized, so a recursive \
                         occurrence must be uniform",
                        c.name
                    ),
                    f.ty.span,
                );
            }
            // Which pattern variable this field sits at, if any.
            let at = match args.as_slice() {
                [
                    Expr {
                        kind: ExprKind::Var(v),
                        ..
                    },
                ] => c
                    .fields
                    .iter()
                    .position(|g| g.name.as_deref() == Some(v.as_str()))
                    .and_then(arg_of),
                _ => None,
            };
            let Some(a) = at else {
                return err(
                    format!(
                        "a recursive field of `{}` must sit at the result index's \
                         pattern variable — `rec` is the immediate subindex and nothing \
                         else exists during the recursion \
                         (docs/inductive-indexed-lowering.md §8.1; the general case is \
                         issues/indexed-families.md route 2b)",
                        c.name
                    ),
                    f.ty.span,
                );
            };
            // §8.2's generalization of condition 2: the `rec` a recursive
            // field reads is the index constructor's *own* recursion, so the
            // pattern variable has to fill a recursive argument of it. At an
            // enum index no argument is, and recursion is therefore not
            // expressible rather than merely rejected — say that by shape.
            if !ict.rec[a] {
                let what = if ict.rec.iter().any(|r| *r) {
                    format!("argument {} of `{}` is not recursive", a + 1, ict.name)
                } else {
                    format!(
                        "`{}` has no recursive argument, so at the index `{}` there is \
                         no smaller index to recurse to",
                        ict.name,
                        ity.name()
                    )
                };
                return err(
                    format!(
                        "a recursive field of `{}` sits at a pattern variable that is \
                         not a recursive argument of its result index's constructor: \
                         {what} (docs/inductive-indexed-lowering.md §8.2)",
                        c.name
                    ),
                    f.ty.span,
                );
            }
            kinds.push(FieldKind::Plain);
            rec_at.push(Some(a));
            continue;
        }
        // A bare `D` / `D<params>` with no index cannot inhabit anything.
        if occurs(&f.ty, name).is_some() {
            return err(
                format!(
                    "field of `{}` mentions `{name}` without supplying its index (or \
                     nested inside another type): an indexed occurrence is \
                     `{name}<…>(x)` at the pattern variable \
                     (docs/inductive-indexed-lowering.md §3)",
                    c.name
                ),
                f.ty.span,
            );
        }
        kinds.push(FieldKind::Payload);
        rec_at.push(None);
    }
    Ok((kinds, rec_at))
}

/// Which indexed fragment a declaration is in
/// (`docs/inductive-fording-lowering.md` §3). One value per declaration, not
/// per constructor: route 3 (fording one branch of a route-1 family) was
/// measured to fail on 2026-07-28, so a declaration with one non-route-1
/// constructor fords **whole**.
pub(crate) enum IdxRoute {
    /// Route 1 (`docs/inductive-indexed-lowering.md`): per constructor, the
    /// result-index pattern, the field kinds, and each child's index-constructor
    /// argument.
    One(Vec<(IdxPat, Vec<FieldKind>, Vec<Option<usize>>)>),
    /// Route 2b (`docs/inductive-fording-lowering.md`): per constructor, the
    /// written result index, the field kinds, and each child's *index variable*
    /// field.
    Forded(Vec<(Expr, Vec<FieldKind>, Vec<Option<usize>>)>),
}

/// §3's classifier, read in order: route 1 if every constructor is
/// route-1-eligible, route 2b if every constructor is 2b-eligible, otherwise a
/// rejection naming what failed where.
fn classify_indexed_route(d: &InductiveDecl, ity: &IdxTy) -> R<IdxRoute> {
    for c in &d.ctors {
        if c.result.is_none() {
            return err(
                format!(
                    "`{}` needs a result annotation: every constructor of an \
                     indexed declaration states its index (`{} : {}<…>(…)`)",
                    c.name, c.name, d.name
                ),
                c.span,
            );
        }
    }
    // Route 1 first: a declaration that qualifies keeps lowering by recursion
    // on the index, which is strictly better (§3.1 — no stored equation, no
    // measure, no cast anywhere).
    let mut rows = Vec::with_capacity(d.ctors.len());
    let mut r1_fail = None;
    for c in &d.ctors {
        let r = c.result.as_ref().expect("checked just above");
        let attempt = parse_result_index(c, r, &d.name, &d.params, &d.ctors, ity).and_then(|pat| {
            classify_fields_indexed(c, &d.name, &d.params, &pat, ity).map(|(k, ra)| (pat, k, ra))
        });
        match attempt {
            Ok(v) => rows.push(v),
            Err(e) => {
                r1_fail = Some((c.name.clone(), e));
                break;
            }
        }
    }
    let Some((c1, e1)) = r1_fail else {
        return Ok(IdxRoute::One(rows));
    };
    // §3.3 row 1: a *uniform* bare-variable index is a parameter wearing an
    // index's spelling. Route 2b would happily generate it, so the route-1
    // message has to win here rather than be tried after.
    if all_bare_var_indices(&d.ctors, ity) {
        return Err(e1);
    }
    let mut frows = Vec::with_capacity(d.ctors.len());
    for c in &d.ctors {
        match classify_forded(c, &d.name, &d.params, ity) {
            Ok(v) => frows.push(v),
            Err(e2) => {
                // §3.3's mixed row: the declaration is in neither fragment, and
                // saying only one reason is what sends a user in a circle. Both
                // are named whether one constructor failed both routes or two
                // constructors failed one each.
                let (
                    crate::ElabError::Elab { msg: m1, .. },
                    crate::ElabError::Elab { msg: m2, span },
                ) = (&e1, &e2)
                else {
                    return Err(e2);
                };
                let msg = if c.name == c1 {
                    format!(
                        "`{}` is in neither indexed fragment: `{c1}` is not \
                         route-1-eligible ({m1}), and it is not route-2b-eligible \
                         either ({m2}) (docs/inductive-fording-lowering.md §3.3)",
                        d.name
                    )
                } else {
                    format!(
                        "`{}` is in neither indexed fragment: `{c1}` is not \
                         route-1-eligible ({m1}), and `{}` is not route-2b-eligible \
                         ({m2}) (docs/inductive-fording-lowering.md §3.3)",
                        d.name, c.name
                    )
                };
                return err(msg, *span);
            }
        }
    }
    Ok(IdxRoute::Forded(frows))
}

/// Route-2b eligibility for one constructor
/// (`docs/inductive-fording-lowering.md` §3.2), with F1–F3's own diagnostics
/// (§3.3). What is **absent** is the point: no condition on the shape of the
/// result index, no bound on branching, no bound on pattern depth.
fn classify_forded(
    c: &CtorDecl,
    name: &str,
    params: &[String],
    ity: &IdxTy,
) -> R<(Expr, Vec<FieldKind>, Vec<Option<usize>>)> {
    let r = c.result.as_ref().expect("checked by the caller");
    let idx = parse_result_head(c, r, name, params)?;
    let iname = ity.name();
    let is_index_ty = |t: &Ty| match ity {
        IdxTy::Nat => matches!(t.kind, TyKind::Nat),
        IdxTy::Decl(_) => {
            matches!(&t.kind, TyKind::Named { name: n, args } if n == iname && args.is_empty())
        }
    };
    let fname = |k: usize| c.fields[k].name.clone().unwrap_or_else(|| "_".into());
    let mut kinds = vec![FieldKind::Payload; c.fields.len()];
    let mut rec_at: Vec<Option<usize>> = vec![None; c.fields.len()];
    for (k, f) in c.fields.iter().enumerate() {
        // A child: `D<params>(e)`, which the parser delivers as an expression
        // in type position.
        if let TyKind::OfExpr(e) = &f.ty.kind
            && let ExprKind::App { head, args, .. } = &e.kind
            && let Some((rname, targs)) = named_head(head)
            && rname == name
        {
            let uniform = targs.len() == params.len()
                && targs.iter().zip(params).all(|(a, p)| {
                    matches!(&a.kind, TyKind::Named { name: an, args } if an == p
                             && args.is_empty())
                });
            if !uniform {
                return err(
                    format!(
                        "field of `{}` uses `{name}` at arguments other than its own \
                         parameters; parameters are monomorphized, so a recursive \
                         occurrence must be uniform",
                        c.name
                    ),
                    f.ty.span,
                );
            }
            // (F1) a child's index is a bare variable naming a field.
            let bare = match args.as_slice() {
                [
                    Expr {
                        kind: ExprKind::Var(v),
                        ..
                    },
                ] => Some(v.clone()),
                _ => None,
            };
            let Some(v) = bare else {
                return err(
                    format!(
                        "`{}`'s index {} is not a variable: fording recomputes a child's \
                         index from the child, so a constructor may only pin it by \
                         *naming* it. Constraining it needs the coherence predicate of \
                         `docs/acc-via-w.md` (docs/inductive-fording-lowering.md §10.3), \
                         which is not generated.",
                        fname(k),
                        index_spelling(&args[0])
                    ),
                    f.ty.span,
                );
            };
            let Some(fk) = c
                .fields
                .iter()
                .position(|g| g.name.as_deref() == Some(v.as_str()))
            else {
                return err(
                    format!(
                        "`{}`'s index `{v}` must be a field of `{}` — a child's index \
                         names the field `μ` recomputes \
                         (docs/inductive-fording-lowering.md §3.2, F1)",
                        fname(k),
                        c.name
                    ),
                    f.ty.span,
                );
            };
            if !is_index_ty(&c.fields[fk].ty) {
                return err(
                    format!(
                        "`{v}` indexes a child of `{}`, so it must be a `{iname}` field",
                        c.name
                    ),
                    c.fields[fk].ty.span,
                );
            }
            // (F2) child indices are linear.
            if let Some(prev) = rec_at.iter().position(|a| *a == Some(fk)) {
                return err(
                    format!(
                        "`{}` and `{}` share the index variable `{v}`; the skeleton \
                         cannot record that they agree — a label cannot mention its \
                         children (`docs/inductive-tier1-wf-lowering.md` §2) — so the \
                         constraint would need the coherence predicate \
                         (docs/inductive-fording-lowering.md §10.3). Give the children \
                         separate indices, or state the family so it is \
                         route-1-eligible.",
                        fname(prev),
                        fname(k)
                    ),
                    f.ty.span,
                );
            }
            kinds[k] = FieldKind::Plain;
            rec_at[k] = Some(fk);
            continue;
        }
        if occurs(&f.ty, name).is_some() {
            return err(
                format!(
                    "field of `{}` mentions `{name}` without supplying its index (or \
                     nested inside another type): an indexed occurrence is \
                     `{name}<…>(x)` at a field naming the child's index \
                     (docs/inductive-fording-lowering.md §3.2)",
                    c.name
                ),
                f.ty.span,
            );
        }
    }
    // The child-index fields: named as some child's index, therefore **not
    // stored** (§4.2).
    for k in 0..c.fields.len() {
        if !rec_at.contains(&Some(k)) {
            continue;
        }
        if kinds[k] == FieldKind::Plain {
            return err(
                format!(
                    "`{}` is both a child of `{}` and another child's index; a child's \
                     index is a field of the index type, not a recursive occurrence",
                    fname(k),
                    c.name
                ),
                c.fields[k].ty.span,
            );
        }
        kinds[k] = FieldKind::IndexVar;
    }
    // (F3) no stored field's type mentions a child index.
    for (k, f) in c.fields.iter().enumerate() {
        if kinds[k] != FieldKind::Payload {
            continue;
        }
        for j in 0..c.fields.len() {
            if kinds[j] != FieldKind::IndexVar {
                continue;
            }
            let Some(v) = &c.fields[j].name else { continue };
            if !ty_mentions(&f.ty, v) {
                continue;
            }
            let child = rec_at
                .iter()
                .position(|a| *a == Some(j))
                .map(fname)
                .unwrap_or_else(|| "the child".into());
            return err(
                format!(
                    "`{}`'s type mentions `{v}`, which fords away: `{v}` is recomputed \
                     from `{child}`, and a child is not in scope in a payload field's \
                     type (`docs/inductive-tier1-wf-lowering.md` §2). This declaration \
                     *is* route-1-eligible if every result index is a pattern — see \
                     docs/inductive-indexed-lowering.md §3.",
                    fname(k)
                ),
                f.ty.span,
            );
        }
    }
    check_index_expr(c, idx, ity)?;
    Ok((idx.clone(), kinds, rec_at))
}

/// F4 is "the result index elaborates" (§3.2), and elaboration happens at each
/// *use*, so a malformed index would otherwise be diagnosed far from where it
/// was written. This is the part that can be checked at declaration time
/// without an instantiation: wherever the index applies a constructor of the
/// index type, its arity must match, and a bare-variable argument at a
/// *recursive* position must be a field of the index type. Everything else —
/// `plus(n, m)`, a payload read, an arbitrary call — is left to elaboration,
/// where the type checker owns it.
fn check_index_expr(c: &CtorDecl, e: &Expr, ity: &IdxTy) -> R<()> {
    let icts = ity.ctors();
    let iname = ity.name();
    let arity_of = |v: &str| icts.iter().position(|k| k.name == v);
    let (head, args): (Option<&str>, &[Expr]) = match &e.kind {
        ExprKind::Var(v) => (Some(v.as_str()), &[]),
        ExprKind::App { head, args, .. } => match &head.kind {
            ExprKind::Var(v) => (Some(v.as_str()), args.as_slice()),
            _ => (None, args.as_slice()),
        },
        _ => (None, &[]),
    };
    if let Some(h) = head
        && let Some(k) = arity_of(h)
    {
        let ict = &icts[k];
        if args.len() != ict.rec.len() {
            return err(
                format!(
                    "`{}`'s result index applies `{}` to {} argument(s), but it takes {}",
                    c.name,
                    ict.name,
                    args.len(),
                    ict.rec.len()
                ),
                e.span,
            );
        }
        for (a, arg) in args.iter().enumerate() {
            if !ict.rec[a] {
                continue;
            }
            let ExprKind::Var(v) = &arg.kind else {
                continue;
            };
            let Some(f) = c
                .fields
                .iter()
                .position(|g| g.name.as_deref() == Some(v.as_str()))
            else {
                continue;
            };
            let ok = match ity {
                IdxTy::Nat => matches!(c.fields[f].ty.kind, TyKind::Nat),
                IdxTy::Decl(_) => matches!(&c.fields[f].ty.kind,
                    TyKind::Named { name: n, args } if n == iname && args.is_empty()),
            };
            if !ok {
                return err(
                    format!(
                        "`{v}` fills a recursive argument of `{}`, so it must be a \
                         `{iname}` field of `{}`",
                        ict.name, c.name
                    ),
                    arg.span,
                );
            }
        }
    }
    for a in args {
        check_index_expr(c, a, ity)?;
    }
    Ok(())
}

/// A child's written index, for F1's message. Only the spellings a user would
/// plausibly write are rendered; anything else is described rather than
/// echoed, which is better than echoing it wrong.
fn index_spelling(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Num(n) => format!("`{n}`"),
        ExprKind::Var(v) => format!("`{v}`"),
        ExprKind::App { head, .. } => match &head.kind {
            ExprKind::Var(v) => format!("`{v}(…)`"),
            _ => "expression".into(),
        },
        _ => "expression".into(),
    }
}

/// Does a surface type mention the *term* variable `v`? [`occurs`] answers
/// this for everything except a written equation, whose endpoints are terms
/// it deliberately does not scan (it is looking for type occurrences).
fn ty_mentions(t: &Ty, v: &str) -> bool {
    match &t.kind {
        TyKind::Eq(a, b) => expr_mentions(a, v) || expr_mentions(b, v),
        _ => occurs(t, v).is_some(),
    }
}

/// The **skeleton** (`docs/inductive-fording-lowering.md` §4): the declaration
/// with every index erased — child-index fields deleted (§4.2), children's
/// types erased to the skeleton itself, result annotations dropped. What
/// remains is an ordinary declaration, and it takes the ordinary shape test:
/// some constructor has a child ⇒ `Wf`, otherwise tier 0's sum-of-Σs (§4.1).
///
/// Built **from** the declaration, once, and never edited afterwards — which
/// is what keeps the two from drifting (§14.6).
fn skeleton_of(d: &InductiveDecl, ctors: &[Ctor], tag: u32, scope: Rc<Scope>) -> Inductive {
    let sname = format!("{}#skel", d.name);
    let self_ty = Ty {
        kind: TyKind::Named {
            name: sname.clone(),
            args: d
                .params
                .iter()
                .map(|p| Ty {
                    kind: TyKind::Named {
                        name: p.clone(),
                        args: vec![],
                    },
                    span: d.span,
                })
                .collect(),
        },
        span: d.span,
    };
    let sctors: Vec<Ctor> = ctors
        .iter()
        .map(|c| {
            let mut fields = Vec::new();
            let mut kind = Vec::new();
            for (k, (n, t)) in c.fields.iter().enumerate() {
                match c.kind[k] {
                    // §4.2: a child-index field is not stored. `n` **is**
                    // `μ(child)`, definitionally.
                    FieldKind::IndexVar => {}
                    FieldKind::Plain => {
                        fields.push((n.clone(), self_ty.clone()));
                        kind.push(FieldKind::Plain);
                    }
                    _ => {
                        fields.push((n.clone(), t.clone()));
                        kind.push(FieldKind::Payload);
                    }
                }
            }
            let rec_at = vec![None; kind.len()];
            let defaults = vec![None; kind.len()];
            Ctor {
                name: format!("{}#skel", c.name),
                fields,
                kind,
                res: None,
                rec_at,
                res_expr: None,
                defaults,
            }
        })
        .collect();
    let recursive = sctors.iter().any(|c| c.kind.iter().any(|k| k.is_child()));
    Inductive {
        name: sname,
        scope,
        tag,
        params: d.params.clone(),
        valparams: vec![],
        op_symbols: vec![],
        ctors: sctors,
        recursive,
        is_record: false,
        index: None,
        index_ty: None,
        skel: None,
    }
}

/// The constructor an arm names, **through the scrutinee's type**
/// (docs/modules-design.md §8, the free win): a `match` arm never consults the
/// global constructor table, because the scrutinee's declaration already says
/// which constructors exist. An arm name is therefore unambiguous by
/// construction even when two visible modules declare a `Cons`, and all
/// qualification adds here is a spelling — `Option::None` is accepted exactly
/// when the scrutinee *is* an `Option`.
pub(crate) fn arm_ctor_index(ind: &Inductive, written: &str) -> Option<usize> {
    let base = match written.split_once("::") {
        Some((ty, c)) if ty == ind.name => c,
        Some(_) => return None,
        None => written,
    };
    ind.ctors.iter().position(|c| c.name == base)
}

/// Is *every* constructor's result index a bare variable? Then the declaration
/// has a parameter wearing an index's spelling — see the message at
/// [`parse_result_index`]'s `Var` arm. One constructor that pins its index
/// makes the family genuinely indexed, and this is `false`.
///
/// A **nullary index constructor** wears the same spelling as a variable
/// (`Tw(SLeaf)` parses as `App(Tw, [Var("SLeaf")])`), and it pins its index as
/// firmly as `SNode(l, r)` does — so the index type's own constructor names are
/// excluded here. Without that, an enum-indexed family with one bare-variable
/// constructor (§3.4's non-uniform row, at a declared index) was rejected with
/// the *parameter* message instead of fording (found 2026-08-04).
fn all_bare_var_indices(ctors: &[CtorDecl], ity: &IdxTy) -> bool {
    let icts = ity.ctors();
    ctors.iter().all(|c| {
        let Some(Expr {
            kind: ExprKind::App { args, .. },
            ..
        }) = &c.result
        else {
            return false;
        };
        let [
            Expr {
                kind: ExprKind::Var(v),
                ..
            },
        ] = args.as_slice()
        else {
            return false;
        };
        !icts.iter().any(|ic| ic.name == *v)
    })
}

/// The `(name, type args)` of `Var` / `TyApp(Var, …)` expression heads.
pub(crate) fn named_head(e: &Expr) -> Option<(&str, &[Ty])> {
    match &e.kind {
        ExprKind::Var(n) => Some((n, &[])),
        ExprKind::TyApp { head, args } => match &head.kind {
            ExprKind::Var(n) => Some((n, args)),
            _ => None,
        },
        _ => None,
    }
}

/// `t` *is* the declaration applied to something — `D<ā>` (a
/// [`TyKind::Named`]) or `D<ā>(ē)`, which reaches a field type as a
/// [`TyKind::OfExpr`] application (docs/surface-value-parameters.md §3) —
/// read as its type arguments and, for the applied spelling, its value
/// arguments. `None` for every other type, including one that mentions `D`
/// only further in.
fn self_head<'a>(t: &'a Ty, name: &str) -> Option<(&'a [Ty], Option<&'a [Expr]>)> {
    match &t.kind {
        TyKind::Named { name: n, args } if n == name => Some((args, None)),
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, args, .. } => match named_head(head) {
                Some((n, targs)) if n == name => Some((targs, Some(args))),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// Is `t` the **uniform** recursive occurrence — the declaration at its own
/// type parameters and its own value parameters, each bare and in order
/// (tier 1 §1's rule, extended by docs/surface-value-parameters.md §6)? Only
/// that occurrence is a child: it is the one whose type is the instance being
/// declared, so lowering it as the `Wf`/`W` itself substitutes nothing. A
/// value argument that differs (`ITree<R>(F)`, `D(Succ(n))`) would be an
/// *index*, and lowering it as a child would silently drop the difference.
fn uniform_occurrence(t: &Ty, name: &str, params: &[String], vparams: &[String]) -> Option<bool> {
    let (targs, vargs) = self_head(t, name)?;
    let targs_uniform = targs.len() == params.len()
        && targs.iter().zip(params).all(|(a, p)| {
            matches!(&a.kind, TyKind::Named { name: an, args } if an == p && args.is_empty())
        });
    let vargs_uniform = match (vargs, &t.kind) {
        (None, _) => vparams.is_empty(),
        (Some(vargs), TyKind::OfExpr(e)) => {
            !vparams.is_empty()
                && matches!(&e.kind, ExprKind::App { named, explicit: false, goal_oriented: false, .. }
                    if named.is_empty())
                && vargs.len() == vparams.len()
                && vargs
                    .iter()
                    .zip(vparams)
                    .all(|(a, v)| matches!(&a.kind, ExprKind::Var(an) if an == v))
        }
        (Some(_), _) => false,
    };
    Some(targs_uniform && vargs_uniform)
}

fn classify_field(
    t: &Ty,
    name: &str,
    params: &[String],
    vparams: &[String],
    ctor: &str,
) -> R<bool> {
    if let Some(uniform) = uniform_occurrence(t, name, params, vparams) {
        if uniform {
            return Ok(true);
        }
        let own = format!(
            "{name}{}{}",
            if params.is_empty() {
                String::new()
            } else {
                format!("<{}>", params.join(", "))
            },
            if vparams.is_empty() {
                String::new()
            } else {
                format!("({})", vparams.join(", "))
            }
        );
        if vparams.is_empty() && self_head(t, name).is_some_and(|(_, v)| v.is_some()) {
            return err(
                format!(
                    "field of `{ctor}` applies `{name}` to value arguments, but `{name}` \
                     declares no value parameters: the recursive occurrence is `{own}`. An \
                     argument that is the same in every occurrence is a value parameter \
                     (`inductive {name}(m: Nat) {{ … }}`); one that varies is an index \
                     (docs/surface-value-parameters.md §6)"
                ),
                t.span,
            );
        }
        if !vparams.is_empty() {
            return err(
                format!(
                    "field of `{ctor}` uses `{name}` at arguments other than its own \
                     parameters: a recursive occurrence must be `{own}` exactly — its type \
                     parameters and then its value parameters, each bare and in order. A \
                     value argument that varies is an index, not a parameter \
                     (docs/surface-value-parameters.md §6)"
                ),
                t.span,
            );
        }
        return err(
            format!(
                "field of `{ctor}` uses `{name}` at arguments other than its own parameters \
                 (`{}`); parameters are monomorphized, so a recursive occurrence must be \
                 uniform (docs/inductive-tier1-wf-lowering.md §1)",
                params.join(", ")
            ),
            t.span,
        );
    }
    if let Some(sp) = occurs(t, name) {
        return err(
            format!(
                "field of `{ctor}` mentions `{name}` nested inside another type: nested \
                 recursion (`Rose {{ Node(A, List Rose) }}`) is not lowered yet \
                 (docs/inductive-tier1-wf-lowering.md §8)"
            ),
            sp,
        );
    }
    Ok(false)
}

/// Where `name` occurs in a surface type, if it does. Only *occurrence*, not
/// polarity — and the reason that is still sound changed on 2026-07-27.
///
/// It used to be that no field could have a function type at all, so a
/// negative occurrence could not be written. Now one can
/// (docs/surface-records.md §11.1), and what keeps polarity out of reach here
/// is that [`reject_function_fields`] runs **first** and rejects a `Π` field
/// mentioning the declaration in *either* position. So every occurrence that
/// reaches this function is still under type constructors only, where it is
/// necessarily positive. The strict-positivity refinement is what lifts that
/// rejection, not what replaces this check.
/// Does `name` appear anywhere in an expression? Used only to keep
/// [`occurs`] conservative over [`TyKind::OfExpr`]; a false positive costs a
/// rejection, a false negative would cost positivity, so every compound form
/// recurses and only genuine leaves answer `false`.
pub(crate) fn expr_mentions(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Var(n) => n == name,
        // An operator symbol is a name in its own namespace, never a
        // declaration's (docs/operators-onto-classes-design.md §4).
        ExprKind::OpSymbol { .. }
        | ExprKind::Num(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::ArgSlot(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_)
        | ExprKind::Univ { .. } => false,
        ExprKind::App {
            head, args, named, ..
        } => {
            expr_mentions(head, name)
                || args.iter().any(|a| expr_mentions(a, name))
                || named.iter().any(|a| expr_mentions(&a.expr, name))
        }
        ExprKind::TyApp { head, args } => {
            expr_mentions(head, name) || args.iter().any(|t| occurs(t, name).is_some())
        }
        ExprKind::Lam { body, binders } => {
            expr_mentions(body, name)
                || binders
                    .iter()
                    .any(|b| b.ty.as_ref().is_some_and(|t| occurs(t, name).is_some()))
        }
        ExprKind::Eq(a, b) => expr_mentions(a, name) || expr_mentions(b, name),
        // A motive body in type syntax: read it as the type it is.
        ExprKind::TyLit(t) => occurs(t, name).is_some(),
        ExprKind::CollectionLit(es) => es.iter().any(|x| expr_mentions(x, name)),
        ExprKind::Index { recv, idx } => expr_mentions(recv, name) || expr_mentions(idx, name),
        ExprKind::RecordUpdate { base, fields } => expr_mentions(base, name) || fields.iter().any(|f| expr_mentions(&f.expr, name)),
        ExprKind::Dot {
            recv, tyargs, args, named, ..
        } => {
            expr_mentions(recv, name)
                || tyargs.iter().any(|t| occurs(t, name).is_some())
                || args.iter().flatten().any(|a| expr_mentions(a, name))
                || named.iter().any(|a| expr_mentions(&a.expr, name))
        }
        ExprKind::RecordLit {
            name: n,
            tyargs,
            fields,
        } => {
            n == name
                || tyargs.iter().any(|t| occurs(t, name).is_some())
                || fields.iter().any(|f| expr_mentions(&f.expr, name))
        }
        // Binder-carrying forms: conservative, since their motives and arms
        // are where a self-reference would hide.
        ExprKind::Match { .. } | ExprKind::MatchCode { .. } | ExprKind::J { .. } => true,
        // A block: conservative for the same reason, since its statements are
        // where a self-reference would hide (docs/let-and-blocks-design.md
        // §4.4). A false positive costs a rejection; a false negative would
        // cost positivity.
        ExprKind::Block(_) => true,
        // Quotation: recurse — a mention inside a quote or splice is still a
        // mention (and the modal forms are rejected in field types anyway).
        ExprKind::Quote(e) | ExprKind::Splice(e) => expr_mentions(e, name),
    }
}

/// Is this field the fact a `Pos<A>` field adds, defaulted to the parser's
/// positivity search?
fn is_pos_search(f: &heather_syntax::FieldDecl) -> bool {
    matches!(f.default.as_deref(), Some(Expr { kind: ExprKind::Var(v), .. }) if v == heather_syntax::POS_SEARCH)
}

fn occurs(t: &Ty, name: &str) -> Option<Span> {
    match &t.kind {
        TyKind::Nat | TyKind::Univ { .. } => None,
        // A decoded expression (`m.carrier`). Scanned by *name*, conservatively:
        // a mention anywhere counts as an occurrence, since there is no type
        // structure here to read polarity off (docs/surface-universe.md §4).
        TyKind::OfExpr(e) => expr_mentions(e, name).then_some(t.span),
        TyKind::Eq(..) => None,
        TyKind::Named { name: n, args } => {
            if n == name {
                return Some(t.span);
            }
            args.iter().find_map(|a| occurs(a, name))
        }
        // A function field is what makes a declaration *infinitary*; it is
        // rejected outright before this runs (`reject_function_fields`), so
        // an occurrence inside one cannot reach the lowering.
        TyKind::Fn { dom, cod, .. } => occurs(dom, name).or_else(|| occurs(cod, name)),
        // `[D; n]` is a *container* field, classified before this is reached
        // (§3.1); an occurrence deeper inside the element type is nested and
        // still rejected.
        TyKind::Vec { elem, .. } => occurs(elem, name),
        // `Fin(n)` has no element type — only a length, which is a *term*. A
        // mention of the declaration there could not be well-typed, but this
        // walk is conservative by design (see the doc comment): scanning it
        // costs at worst a rejection, and skipping it would cost positivity.
        TyKind::Fin(len) => expr_mentions(len, name).then_some(t.span),
        TyKind::Squash(inner) => occurs(inner, name),
        // Modal types (layer m) cannot be field types — they are rejected at
        // elaboration; conservative answers here keep the walkers total.
        TyKind::Ctx | TyKind::TyCode { .. } => None,
        TyKind::Code { ty, .. } => occurs(ty, name),
        TyKind::Splice { name: n } => (n == name).then_some(t.span),
    }
}

/// A `Π` field whose domain or codomain mentions the declaration puts it in
/// the **infinitary** tier. Exactly one shape of it is lowered
/// (docs/inductive-tier2-w-lowering.md §1): a *top-level* field
/// `(y: A) -> D<p̄>` of an unindexed declaration, with `A` free of `D` — a
/// strictly positive occurrence, `D` as the codomain and nowhere else. That
/// field is classified [`FieldKind::FnChild`] by `classify_fields`, and the
/// declaration lowers onto `W` (`infinitary.rs`).
///
/// Every other `Π` that mentions the declaration is diagnosed rather than
/// mis-lowered — the hazard class `docs/inductive-tier0-lowering.md` opens by
/// naming (docs/surface-function-types.md §8): `D` in a domain (not strictly
/// positive), a curried field (`A -> B -> D`, one arrow this round), a
/// function field nested under another type, or one on an indexed family.
///
/// A function field that does **not** mention the declaration is an ordinary
/// **payload** and is accepted (corrected 2026-07-27, docs/surface-records.md
/// §11). Nothing about it is infinitary: it is one `Type::Pi` component of the
/// Σ spine, and every downstream scheme treats it like any other payload. The
/// original check keyed on the *shape* of the field type rather than on a
/// self-occurrence, which was strictly too coarse — and it is what would
/// otherwise reject `record Monoid<A> { op: A -> A -> A }`, i.e. the entire
/// point of a record of functions.
pub(crate) fn reject_function_fields(d: &InductiveDecl) -> Result<(), crate::ElabError> {
    fn recursive_fn(t: &Ty, name: &str) -> Option<Span> {
        match &t.kind {
            TyKind::Fn { dom, cod, .. } => {
                if occurs(dom, name).is_some() || occurs(cod, name).is_some() {
                    return Some(t.span);
                }
                None
            }
            TyKind::Named { args, .. } => args.iter().find_map(|a| recursive_fn(a, name)),
            TyKind::Vec { elem, .. } => recursive_fn(elem, name),
            TyKind::Squash(inner) => recursive_fn(inner, name),
            // Not a `Π` by shape, so not what this check is looking for; a
            // self-occurrence inside it is `occurs`' business.
            TyKind::OfExpr(..) => None,
            // `Fin(n)` is not a `Π` by shape and its length is a term, so
            // there is no function field to find here.
            TyKind::Nat | TyKind::Eq(..) | TyKind::Univ { .. } | TyKind::Fin(_) => None,
            // Modal types are rejected as field types at elaboration; none of
            // them is a `Π` by shape.
            TyKind::Ctx | TyKind::TyCode { .. } | TyKind::Splice { .. } => None,
            TyKind::Code { ty, .. } => recursive_fn(ty, name),
        }
    }
    let fail = |msg: String, span: Span| Err(crate::ElabError::Elab { msg, span });
    for c in &d.ctors {
        for f in &c.fields {
            // The one lowered shape (tier 2 §1), at the top of a field.
            if let TyKind::Fn {
                dom, cod, implicit, ..
            } = &f.ty.kind
                && (occurs(dom, &d.name).is_some() || occurs(cod, &d.name).is_some())
            {
                if occurs(dom, &d.name).is_some() {
                    return fail(
                        format!(
                            "field of `{}` mentions `{}` in the domain of a function type: \
                             that occurrence is not strictly positive, and only `A -> {}` with \
                             `A` free of `{}` is lowered (docs/inductive-tier2-w-lowering.md §1)",
                            c.name, d.name, d.name, d.name
                        ),
                        f.ty.span,
                    );
                }
                if matches!(cod.kind, TyKind::Fn { .. }) {
                    return fail(
                        format!(
                            "field of `{}` is a curried function into `{}`: a recursive \
                             function field takes one argument this round — take a pair, or \
                             a record of the arguments (docs/inductive-tier2-w-lowering.md §1)",
                            c.name, d.name
                        ),
                        f.ty.span,
                    );
                }
                if *implicit {
                    return fail(crate::IMPLICIT_MARK_REFUSED.to_string(), f.ty.span);
                }
                if d.index.is_some() {
                    return fail(
                        format!(
                            "field of `{}` is a function into `{}`, and `{}` is an indexed \
                             family: the infinitary tier lowers unindexed declarations only \
                             this round (docs/inductive-tier2-w-lowering.md §1)",
                            c.name, d.name, d.name
                        ),
                        f.ty.span,
                    );
                }
                // `A -> D<…>` itself: classified by `classify_fields`, which
                // also checks that the occurrence is the uniform one.
                if self_head(cod, &d.name).is_some() {
                    continue;
                }
                return fail(
                    format!(
                        "field of `{}` is a function whose result mentions `{}` under \
                         another type: only `A -> {}` itself is lowered \
                         (docs/inductive-tier2-w-lowering.md §1)",
                        c.name, d.name, d.name
                    ),
                    f.ty.span,
                );
            }
            if let Some(sp) = recursive_fn(&f.ty, &d.name) {
                return fail(
                    format!(
                        "field of `{}` nests a function type mentioning `{}` inside another \
                         type: only a field that *is* `A -> {}` is lowered \
                         (docs/inductive-tier2-w-lowering.md §1)",
                        c.name, d.name, d.name
                    ),
                    sp,
                );
            }
        }
    }
    Ok(())
}

// -- no-confusion (§6) ------------------------------------------------------

/// Which branch body a constant-motive case tree puts at each constructor.
pub(crate) enum ConstBody {
    /// Tier 1 §3 / container-fields §3.3: constructor `j`'s arity. The motive
    /// is `Nat`, and the resulting tree *is* the `Wf`'s arity. Each entry is
    /// `(plain children, optional payload index of a container's length)`,
    /// giving `Succ^{plain}(len)` — with the tier-1 literal being the
    /// `len`-absent instance `Succ^{plain}(Zero)` of the same formula, so the
    /// two cannot diverge.
    Arity(Vec<(usize, Option<usize>)>),
    /// §6.1: the code of `Unit` at constructor `i`, of `Empty` elsewhere. The
    /// motive is `Ty 0` — this is the large elimination, and it is what makes
    /// two distinct constructors provably distinct.
    TagCode(usize),
    /// §6.2: the `k`-th *payload* field projection at constructor `i`, and a
    /// default term (the left-hand side's own field value) elsewhere, so that
    /// the projection is total on `⟦D⟧`.
    Field {
        i: usize,
        k: usize,
        default: Rc<Term>,
    },
}

impl Elaborator {
    /// A case tree with a *constant* motive. Simpler than §5.2's: with the
    /// motive independent of the scrutinee there is no injection to compose
    /// with, only the weakening that each pushed binder demands.
    ///
    /// `motive` and `spine` are scoped in the context the caller built them in;
    /// `d` counts the binders pushed since, so a spine component used here is
    /// weakened by `d` (or `d+1` under a branch binder). `j` is the constructor
    /// index — *not* the same counter as `d`, since these trees are built
    /// several binders deep (inside a `J` motive, `d` starts at 2).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn const_case_tree(
        &self,
        cx: &Cx,
        spine: &Spine,
        n: usize,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &ConstBody,
        j: usize,
        d: u32,
        span: Span,
    ) -> R<Term> {
        if j + 1 == n {
            // The last constructor: no `Case`, so the branch body is scoped in
            // `cx` itself with the scrutinee standing in for the binder.
            return self.const_body(cx, spine, j, &scrut, body, d, span);
        }
        let ctor_lvl = spine.ctors[j].1.clone();
        let tail_lvl = spine.tails[j].1.clone();
        let ctor_ty = Rc::new(spine.ctors[j].0.shift_local(d));
        let tail_ty = Rc::new(spine.tails[j].0.shift_local(d));
        let mut bcx = cx.clone();
        bcx.push("#c".into(), (*ctor_ty).clone(), ctor_lvl.clone());
        let case_l = self.const_body(
            &bcx,
            spine,
            j,
            &Rc::new(Term::Var(LocalVar(0))),
            body,
            d + 1,
            span,
        )?;
        let mut rcx = cx.clone();
        rcx.push("#r".into(), (*tail_ty).clone(), tail_lvl.clone());
        let case_r = self.const_case_tree(
            &rcx,
            spine,
            n,
            &motive.shift_local(1),
            mlvl,
            Rc::new(Term::Var(LocalVar(0))),
            body,
            j + 1,
            d + 1,
            span,
        )?;
        Ok(Term::Case {
            lhs_level: ctor_lvl,
            rhs_level: tail_lvl,
            motive_level: mlvl.clone(),
            lhs: ctor_ty,
            rhs: tail_ty,
            // The motive binds `z`, which a constant motive simply ignores.
            motive: Rc::new(motive.shift_local(1)),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut,
        })
    }

    /// One branch of [`Self::const_case_tree`], for constructor `j`, with
    /// `value : ⟦c_j⟧` scoped in `cx`.
    #[allow(clippy::too_many_arguments)]
    fn const_body(
        &self,
        cx: &Cx,
        spine: &Spine,
        j: usize,
        value: &Rc<Term>,
        body: &ConstBody,
        d: u32,
        span: Span,
    ) -> R<Term> {
        match body {
            ConstBody::Arity(counts) => {
                let (plain, len_payload) = counts[j];
                let mut acc = match len_payload {
                    // A container: the arity is data — the length field
                    // projected straight out of the shape (§3.3). This is the
                    // same projection `ConstBody::Field` builds, deliberately.
                    Some(p) => {
                        let ctor_ty = spine.ctors[j].0.shift_local(d);
                        let (proj, _, _) = self.projection(cx, &ctor_ty, value, p, span)?;
                        (*proj).clone()
                    }
                    None => Term::Zero,
                };
                // `Succ`-headed exactly `plain` times, which is what lets
                // `Vec` unfold that many steps and leave the container as the
                // tail (§3.3).
                for _ in 0..plain {
                    acc = Term::Succ(Rc::new(acc));
                }
                Ok(acc)
            }
            ConstBody::TagCode(i) => Ok(if j == *i {
                Term::TmUnit { level: Level::Zero }
            } else {
                Term::TmEmpty { level: Level::Zero }
            }),
            ConstBody::Field { i, k, default } => {
                if j != *i {
                    return Ok(default.shift_local(d));
                }
                let ctor_ty = spine.ctors[j].0.shift_local(d);
                let (proj, _, _) = self.projection(cx, &ctor_ty, value, *k, span)?;
                Ok((*proj).clone())
            }
        }
    }

    /// The `k`-th field projection `fst(snd^{k+1} value)` and its type (§5.1;
    /// the `+1` is the nominal tag). `ctor_ty` is `⟦c_i⟧` scoped in `cx`.
    pub(crate) fn projection(
        &self,
        cx: &Cx,
        ctor_ty: &Type,
        value: &Rc<Term>,
        k: usize,
        span: Span,
    ) -> R<(Rc<Term>, Type, Level)> {
        let mut cur = ctor_ty.clone();
        let mut pair = Rc::clone(value);
        // Component 0 is the tag, so field `k` is component `k+1`.
        for step in 0..=k + 1 {
            let head = self.whnf(cx, &cur, span)?;
            let Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } = head
            else {
                return err("internal: constructor encoding is too short", span);
            };
            // The **emitted** `Fst`/`Snd` annotations take the reference
            // spelling where their components are registered lowerings
            // (`docs/annotation-component-respell-design.md` §2.2): a field
            // of type `⟦Ir⟧` otherwise writes 1,712 nodes into `fst_ty` *and*
            // into every preceding step's `snd_ty`, per use of the binder the
            // chain aliases. The loop's own `cur` and the **returned** field
            // type stay inline — the return becomes a `match` binder's alias
            // type, a structural-read position (family-code design §10.3).
            let fst_e = match self.emit_ty(cx, &fst, 0) {
                Some(r) => Rc::new(r),
                None => Rc::clone(&fst),
            };
            // `snd` binds the Σ's first component, hence depth 1.
            let snd_e = match self.emit_ty(cx, &snd, 1) {
                Some(r) => Rc::new(r),
                None => Rc::clone(&snd),
            };
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst_e),
                snd_ty: Rc::clone(&snd_e),
                pair: Rc::clone(&pair),
            });
            if step == k + 1 {
                return Ok((proj, (*fst).clone(), fst_level));
            }
            pair = Rc::new(Term::Snd {
                fst_level,
                snd_level,
                fst_ty: fst_e,
                snd_ty: snd_e,
                pair: Rc::clone(&pair),
            });
            cur = snd.apply_local(&LocalSubst::id(&cx.gamma).extended(proj));
        }
        err("internal: projection walked off the end", span)
    }

    /// Read a constructor term back: its index and its field values. Besides a
    /// canonical constructor, accept the injected neutral that a `match` arm's
    /// motive is instantiated at (issues/absurd-on-branch-scrutinee.md). The
    /// injection determines the constructor; its payload fields are the
    /// ordinary Σ projections of the neutral summand value.
    ///
    /// A bare neutral at a multi-constructor inductive is deliberately still
    /// `None`: `x : D` identifies no summand, so `x = C(…)` is not yet a
    /// constructor equation. `spine` is scoped in `cx`, as are `t` and the
    /// projections returned here. `read_fields` is false for disjointness,
    /// whose tag predicate deliberately ignores every field and child.
    pub(crate) fn read_ctor(
        &self,
        cx: &Cx,
        ind: &Inductive,
        spine: &Spine,
        t: &Term,
        read_fields: bool,
        span: Span,
    ) -> R<Option<(usize, Vec<Rc<Term>>)>> {
        // Tier 1: the injections are in the *label*, and the fields are split
        // between the label's Σ spine and the children tuple (tier 1 §7).
        let (label, children) = match t {
            Term::Supf {
                label, children, ..
            } => (&**label, Some(&**children)),
            _ => (t, None),
        };
        // Tier 2: `⟨sup(ℓ; f), q⟩`, and the label is inside the `sup`
        // (docs/inductive-tier2-w-lowering.md §9). The children are a function,
        // not a tuple, and nothing reads them back: `inj` at a recursive field
        // of a tier-2 type is refused before it would look (§9), so each child
        // field gets the whole value as a stand-in, only to keep the field
        // list aligned with the declaration.
        let tier2 = ind.infinitary();
        let label = match (tier2, crate::spelling::pair_of(t)) {
            (true, Some((fst, _))) => match &**fst {
                Term::Sup { label, .. } => &**label,
                _ => return Ok(None),
            },
            (true, None) => return Ok(None),
            (false, _) => label,
        };
        let n = ind.ctors.len();
        let mut i = 0usize;
        let mut cur = label;
        let mut injected = false;
        loop {
            // Either injection spelling (`crate::spelling`): this walk reads
            // the *path*, never an annotation, so `inr@` is an `inr`.
            match crate::spelling::inj_of(cur) {
                Some((false, val)) if i + 1 < n => {
                    injected = true;
                    i += 1;
                    cur = val;
                }
                Some((true, val)) => {
                    injected = true;
                    cur = val;
                    break;
                }
                _ => break,
            }
        }
        if i >= n {
            return Ok(None);
        }
        let ctor = &ind.ctors[i];
        let canonical = crate::spelling::is_pair(cur);
        if !canonical && !injected && n > 1 {
            return Ok(None);
        }
        // Disjointness depends only on the injection path. In particular, a
        // recursive arm may carry a neutral children vector, which need not
        // be decoded merely to prove that `Cons` and `Nil` are distinct.
        if !read_fields {
            return Ok(Some((i, Vec::new())));
        }
        // Skip the nominal tag, then collect one value per *payload* field.
        let mut payload = Vec::new();
        if let Some((_, snd)) = crate::spelling::pair_of(cur) {
            let mut p = snd;
            // Not `fields.len() - arity()`: a container field is neither
            // payload nor a *plain* child, so the two no longer partition the
            // fields (docs/container-fields.md §3.1).
            for _ in 0..ctor.payload().count() {
                let Some((fst, snd)) = crate::spelling::pair_of(p) else {
                    return Ok(None);
                };
                payload.push(Rc::clone(fst));
                p = snd;
            }
        } else {
            // Every surface constructor of a sum is injected. Seeing that
            // injection is what distinguishes an arm's neutral summand value
            // from an arbitrary neutral of the whole inductive. With one
            // constructor the whole type is the summand, so no injection is
            // needed.
            let value = Rc::new(cur.clone());
            for k in 0..ctor.payload().count() {
                let (field, _, _) = self.projection(cx, &spine.ctors[i].0, &value, k, span)?;
                payload.push(field);
            }
        }
        // …one per plain child, out of the tuple…
        let mut kids = Vec::new();
        if let Some(children) = children {
            let mut c = children;
            for _ in 0..ctor.arity() {
                let Some((fst, snd)) = crate::spelling::pair_of(c) else {
                    return Ok(None);
                };
                kids.push(Rc::clone(fst));
                c = snd;
            }
            // …and the container, if there is one, is what remains: the
            // tuple's tail *is* the children vector
            // (docs/container-fields.md §3.4), so it reads back as one field
            // value like any other.
            if ctor.container().is_some() {
                kids.push(Rc::new(c.clone()));
            }
        } else if ctor.container().is_some() {
            return Ok(None);
        } else if tier2 {
            for _ in ctor.kind.iter().filter(|k| k.is_child()) {
                kids.push(Rc::new(t.clone()));
            }
        }
        // Re-interleave into declaration order, which is the order `inj`'s
        // field index and every surface message speak in.
        let (mut a, mut b) = (0usize, 0usize);
        let fields = (0..ctor.fields.len())
            .map(|k| {
                if ctor.kind[k].is_child() {
                    b += 1;
                    Rc::clone(&kids[b - 1])
                } else {
                    a += 1;
                    Rc::clone(&payload[a - 1])
                }
            })
            .collect();
        Ok(Some((i, fields)))
    }

    /// The equation an `absurd`/`inj` argument must prove, reduced far enough
    /// to expose its carrier and endpoints. Constructor-specific readers sit
    /// on top of this because `Nat` is a kernel type rather than a declared
    /// inductive (issues/absurd-at-nat-numerals.md).
    fn equation(&self, cx: &Cx, e: &Expr, who: &str) -> R<Equation> {
        let (proof, proof_ty, _) = self.elab_infer(cx, e)?;
        let Type::Id {
            level,
            ty,
            lhs,
            rhs,
        } = self.whnf(cx, &proof_ty, e.span)?
        else {
            return err(
                format!("`{who}` needs a proof of an `=` between constructors"),
                e.span,
            );
        };
        let sty = self.whnf(cx, &ty, e.span)?;
        // A constructor equation may be reached by computation. No-confusion
        // is about the reduced endpoints rather than their source spelling.
        let (lhs, rhs) = (
            self.whnf_tm(cx, &lhs, e.span)?,
            self.whnf_tm(cx, &rhs, e.span)?,
        );
        Ok((proof, sty, level, lhs, rhs))
    }

    /// A declared-inductive equation with both sides read as constructors.
    fn declared_equation(
        &self,
        cx: &Cx,
        equation: Equation,
        who: &str,
        read_fields: bool,
        span: Span,
    ) -> R<CtorEquation> {
        let (proof, sty, level, lhs, rhs) = equation;
        let Some(ind) = self.tag_of(&sty) else {
            return err(
                format!("`{who}` needs an equation at a declared inductive type"),
                span,
            );
        };
        let spine = self.spine(&sty, &level, ind.ctors.len(), span)?;
        let (Some(l), Some(r)) = (
            self.read_ctor(cx, &ind, &spine, &lhs, read_fields, span)?,
            self.read_ctor(cx, &ind, &spine, &rhs, read_fields, span)?,
        ) else {
            return err(
                format!("`{who}` needs both sides of the equation to be constructor applications"),
                span,
            );
        };
        Ok((proof, ind, sty, level, lhs, rhs, l, r))
    }

    fn nat_pred(n: Term) -> Term {
        Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Zero),
            step: Rc::new(Term::Var(LocalVar(1))),
            scrut: Rc::new(n),
        }
    }

    /// Apply constructor injectivity once, internally, to peel a matching
    /// `Succ` layer. This is `cong pred proof`, emitted directly so `absurd`
    /// does not depend on the optional `std/nat` module.
    fn nat_succ_inj(proof: Term, lhs: Rc<Term>, rhs: Rc<Term>) -> Term {
        let pred_lhs = Rc::new(Self::nat_pred((*lhs).clone()));
        Term::J {
            ty_level: Level::Zero,
            motive_level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::clone(&lhs),
            motive: Rc::new(Type::Id {
                level: Level::Zero,
                ty: Rc::new(Type::Nat),
                lhs: Rc::new(Self::nat_pred(lhs.shift_local(2))),
                rhs: Rc::new(Self::nat_pred(Term::Var(LocalVar(1)))),
            }),
            case: Rc::new(Term::Refl {
                level: Level::Zero,
                ty: Rc::new(Type::Nat),
                tm: pred_lhs,
            }),
            rhs,
            proof: Rc::new(proof),
        }
    }

    /// `⌜Unit⌝` at one Nat constructor and `⌜Empty⌝` at the other.
    fn nat_tag(n: Term, unit_at_zero: bool) -> Term {
        let unit = Term::TmUnit { level: Level::Zero };
        let empty = Term::TmEmpty { level: Level::Zero };
        let (base, step) = if unit_at_zero {
            (unit, empty)
        } else {
            (empty, unit)
        };
        Term::ElimNat {
            level: Level::succ(Level::Zero),
            motive: Rc::new(Type::Ty(Level::Zero)),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::new(n),
        }
    }

    fn build_nat_absurd(
        &self,
        cx: &Cx,
        mut proof: Term,
        mut lhs: Rc<Term>,
        mut rhs: Rc<Term>,
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let unit_at_zero = loop {
            match (nat_head(&lhs), nat_head(&rhs)) {
                (NatHead::Zero, NatHead::Succ(_)) => break true,
                (NatHead::Succ(_), NatHead::Zero) => break false,
                (NatHead::Zero, NatHead::Zero) => {
                    return err(
                        "both sides of this equation are `Zero`, so it is not absurd",
                        span,
                    );
                }
                (NatHead::Succ(a), NatHead::Succ(b)) => {
                    let (a, b) = (self.whnf_tm(cx, &a, span)?, self.whnf_tm(cx, &b, span)?);
                    if matches!(nat_head(&a), NatHead::Neutral)
                        || matches!(nat_head(&b), NatHead::Neutral)
                    {
                        return err(
                            "both sides of this equation are `Succ`, so it is not absurd \
                             (use `inj` to get the predecessor equation)",
                            span,
                        );
                    }
                    proof = Self::nat_succ_inj(proof, Rc::clone(&lhs), Rc::clone(&rhs));
                    lhs = a;
                    rhs = b;
                }
                (NatHead::Neutral, _) | (_, NatHead::Neutral) => {
                    return err(
                        "`absurd` needs both sides of the equation to reduce to Nat constructors",
                        span,
                    );
                }
            }
        };

        // Transport `trivial` from the left constructor's tag to the right
        // one. At the exposed Zero/Succ mismatch the result reduces to Empty.
        let empty = Term::J {
            ty_level: Level::Zero,
            motive_level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::clone(&lhs),
            motive: Rc::new(Type::El {
                level: Level::Zero,
                tm: Rc::new(Self::nat_tag(Term::Var(LocalVar(1)), unit_at_zero)),
            }),
            case: Rc::new(Term::Triv { level: Level::Zero }),
            rhs,
            proof: Rc::new(proof),
        };
        Ok(Term::ElimEmpty {
            level: expected_lvl.clone(),
            scrut_level: Level::Zero,
            motive: Rc::new(expected.shift_local(1)),
            scrut: Rc::new(empty),
        })
    }

    /// A total, constant-motive function of `⟦D⟧` built inside a `J` motive —
    /// which is what both halves of no-confusion need, and the one place the
    /// two tiers differ in *how* they eliminate. Tier 0 cases on the
    /// scrutinee directly; tier 1 cases on the tag inside an `elim_Wf`
    /// (docs/inductive-tier1-wf-lowering.md §7).
    ///
    /// `d_ty`, `spine` and `body`'s payloads are scoped in the caller's base
    /// context; `motive` and `scrut` in `mcx`, which is that context plus the
    /// `J` motive's two binders — hence the fixed `2` below.
    #[allow(clippy::too_many_arguments)]
    fn const_predicate(
        &self,
        mcx: &Cx,
        ind: &Inductive,
        d_ty: &Type,
        spine: &Spine,
        motive: &Type,
        mlvl: &Level,
        scrut: Rc<Term>,
        body: &ConstBody,
        span: Span,
    ) -> R<Term> {
        if ind.recursive {
            return self.const_elim_wf(mcx, ind, d_ty, spine, motive, mlvl, scrut, body, 2, span);
        }
        if ind.infinitary() {
            return self.const_elim_w(mcx, ind, d_ty, spine, motive, mlvl, scrut, body, span);
        }
        self.const_case_tree(
            mcx,
            spine,
            ind.ctors.len(),
            motive,
            mlvl,
            scrut,
            body,
            0,
            2,
            span,
        )
    }

    /// §6.1, disjointness: from an equation between *different* constructors,
    /// anything. The tag predicate ignores the fields, so it lands in `Ty 0`
    /// whatever the field levels are, and both `El` reductions are
    /// definitional — which is why the transported case is just `⟨⟩`.
    pub(crate) fn build_absurd(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        expected_lvl: &Level,
        span: Span,
    ) -> R<Term> {
        let equation = self.equation(cx, arg, "absurd")?;
        if matches!(equation.1, Type::Nat) {
            let (proof, _, _, lhs, rhs) = equation;
            return self.build_nat_absurd(cx, proof, lhs, rhs, expected, expected_lvl, span);
        }
        let (proof, ind, sty, slvl, lhs, rhs, (i, _), (j, _)) =
            self.declared_equation(cx, equation, "absurd", false, arg.span)?;
        if i == j {
            return err(
                format!(
                    "both sides of this equation are `{}`, so it is not absurd \
                     (use `inj` to get the field equations)",
                    ind.ctors[i].name
                ),
                span,
            );
        }
        // The J motive, over `y : ⟦D⟧` and `p : lhs = y`: `El⁰ (tag_i y)`.
        let mut mcx = cx.clone();
        mcx.push("#y".into(), sty.clone(), slvl.clone());
        mcx.push(
            "#p".into(),
            Type::Id {
                level: slvl.clone(),
                ty: Rc::new(sty.shift_local(1)),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(Term::Var(LocalVar(0))),
            },
            slvl.clone(),
        );
        let spine = self.spine(&sty, &slvl, ind.ctors.len(), span)?;
        let pred = self.const_predicate(
            &mcx,
            &ind,
            &sty,
            &spine,
            &Type::Ty(Level::Zero),
            &Level::succ(Level::Zero),
            Rc::new(Term::Var(LocalVar(1))),
            &ConstBody::TagCode(i),
            span,
        )?;
        let motive = Type::El {
            level: Level::Zero,
            tm: Rc::new(pred),
        };
        let absurd = Term::J {
            ty_level: slvl.clone(),
            motive_level: Level::Zero,
            ty: Rc::new(sty),
            lhs,
            motive: Rc::new(motive),
            // `El⁰ (tag_i lhs) ⇝ El ⌜Unit⌝ ⇝ Unit`, definitionally.
            case: Rc::new(Term::Triv { level: Level::Zero }),
            rhs,
            proof: Rc::new(proof),
        };
        // …and `El⁰ (tag_i rhs) ⇝ Empty^0`, so this eliminates into anything.
        // The scrutinee's level is the `El`'s, which is 0 just above.
        Ok(Term::ElimEmpty {
            level: expected_lvl.clone(),
            scrut_level: Level::Zero,
            motive: Rc::new(expected.shift_local(1)),
            scrut: Rc::new(absurd),
        })
    }

    /// §6.2, injectivity: from an equation between the *same* constructor, the
    /// equation between its `k`-th fields, by congruence of a total projection.
    ///
    /// The projection needs a value at the other constructors; this takes the
    /// left-hand side's own field, which is in scope and of exactly the right
    /// type. That keeps the motive constant — no code-valued family, and so
    /// none of the level restriction the document's first version carried.
    /// The price: the field's type must not depend on the constructor's
    /// earlier fields, which is checked (by conversion) rather than assumed.
    pub(crate) fn build_inj(
        &self,
        cx: &Cx,
        k: usize,
        arg: &Expr,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let equation = self.equation(cx, arg, "inj")?;
        let (proof, ind, sty, slvl, lhs, rhs, (i, la), (j, rb)) =
            self.declared_equation(cx, equation, "inj", true, arg.span)?;
        if i != j {
            return err(
                format!(
                    "this equation is between `{}` and `{}`, which are different constructors \
                     (use `absurd`)",
                    ind.ctors[i].name, ind.ctors[j].name
                ),
                span,
            );
        }
        let arity = ind.ctors[i].fields.len();
        if k >= arity {
            return err(
                format!(
                    "`{}` has {arity} field(s), so there is no field {k}",
                    ind.ctors[i].name
                ),
                span,
            );
        }
        let spine = self.spine(&sty, &slvl, ind.ctors.len(), span)?;
        // Which body the projection's case tree gets, and at what type. A
        // recursive field is a child rather than a component of the shape, so
        // its type is `⟦D⟧` itself and there is nothing for it to depend on
        // (tier 1 §2/§7.2); a payload field is tier 0's projection, at its
        // index *among the payload*.
        // Injectivity at a *container* field is not phase 1
        // (docs/container-fields.md §6). It is not a missing case so much as
        // a dependent one: the field's type is `[D; len]`, which depends on
        // an earlier field, so a constant motive would need both sides'
        // lengths to be definitionally equal. That is tier 0's
        // dependent-field restriction, and it wants the same treatment rather
        // than a special case here.
        if matches!(ind.ctors[i].kind[k], FieldKind::Container { .. }) {
            return err(
                format!(
                    "`inj` at the container field of `{}` is not supported yet: its type \
                     `[{}; …]` depends on the length field before it, so the two sides' \
                     lengths would have to be definitionally equal \
                     (docs/container-fields.md §6)",
                    ind.ctors[i].name, ind.name
                ),
                span,
            );
        }
        if ind.infinitary() && ind.ctors[i].kind[k].is_child() {
            return err(
                format!(
                    "`inj` at the recursive field of `{}` is not supported: `{}` has a \
                     recursive function field, and a child's injectivity there would need \
                     funext (docs/inductive-tier2-w-lowering.md §9)",
                    ind.ctors[i].name, ind.name
                ),
                span,
            );
        }
        let (body, lty, llvl) = if ind.ctors[i].kind[k].is_child() {
            // A child, not a component of the shape: `None` routes the
            // projection through `child_projection` below.
            (None, sty.clone(), slvl.clone())
        } else {
            let p = ind.ctors[i].kind[..k]
                .iter()
                .filter(|f| !f.is_child())
                .count();
            // The field type at each side. They differ exactly when the
            // field's type depends on an earlier field of the same
            // constructor.
            let (_, lty, llvl) = self.projection(cx, &spine.ctors[i].0, &lhs, p, span)?;
            let (_, rty, _) = self.projection(cx, &spine.ctors[i].0, &rhs, p, span)?;
            // Layer p: conversion is only defined at computing layers, and
            // this comparison is the elaborator's own, not part of an emitted
            // term.
            if self
                .committed_oracle()
                .convert_type(&cx.gamma, Layer::Prog, &lty, &rty, &llvl)
                .is_err()
            {
                return err(
                    format!(
                        "field {k} of `{}` has a type that depends on an earlier field, so its \
                         injectivity is not derivable this way yet \
                         (docs/inductive-tier0-lowering.md §6.2)",
                        ind.ctors[i].name
                    ),
                    span,
                );
            }
            (
                Some(ConstBody::Field {
                    i,
                    k: p,
                    default: Rc::clone(&la[k]),
                }),
                lty,
                llvl,
            )
        };
        // The J motive, over `y` and `p : lhs = y`: `a_k = proj y`.
        let mut mcx = cx.clone();
        mcx.push("#y".into(), sty.clone(), slvl.clone());
        mcx.push(
            "#p".into(),
            Type::Id {
                level: slvl.clone(),
                ty: Rc::new(sty.shift_local(1)),
                lhs: Rc::new(lhs.shift_local(1)),
                rhs: Rc::new(Term::Var(LocalVar(0))),
            },
            slvl.clone(),
        );
        let proj = match &body {
            Some(body) => self.const_predicate(
                &mcx,
                &ind,
                &sty,
                &spine,
                &lty.shift_local(2),
                &llvl,
                Rc::new(Term::Var(LocalVar(1))),
                body,
                span,
            )?,
            // The recursive half (tier 1 §7.2). It cannot go through
            // `const_predicate`: reading a child out of `cs` needs `cs` at
            // the *literal* arity, and outside a tag branch that arity is
            // stuck on a variable — so this one generalizes `cs` in the case
            // motive exactly as `match` does, and shares the code that does.
            None => {
                let t = ind.ctors[i].kind[..k]
                    .iter()
                    .filter(|f| **f == FieldKind::Plain)
                    .count();
                self.child_projection(
                    &mcx,
                    &ind,
                    &sty.shift_local(2),
                    &slvl,
                    i,
                    t,
                    Rc::new(la[k].shift_local(2)),
                    Term::Var(LocalVar(1)),
                    span,
                )?
            }
        };
        let motive = Type::Id {
            level: llvl.clone(),
            ty: Rc::new(lty.shift_local(2)),
            lhs: Rc::new(la[k].shift_local(2)),
            rhs: Rc::new(proj),
        };
        let term = Term::J {
            ty_level: slvl,
            motive_level: llvl.clone(),
            ty: Rc::new(sty),
            lhs,
            motive: Rc::new(motive),
            // At `y := lhs` the projection computes back to `a_k`.
            case: Rc::new(Term::Refl {
                level: llvl.clone(),
                ty: Rc::new(lty.clone()),
                tm: Rc::clone(&la[k]),
            }),
            rhs,
            proof: Rc::new(proof),
        };
        // The J term's type mentions the projection; report the type the user
        // means, which it reduces to.
        let result = Type::Id {
            level: llvl.clone(),
            ty: Rc::new(lty),
            lhs: Rc::clone(&la[k]),
            rhs: Rc::clone(&rb[k]),
        };
        Ok((term, result, llvl))
    }
}

/// Match a declared surface type against an inferred kernel type, solving the
/// declaration's type parameters where the surface side names one.
///
/// Structural, first-order, and **domain-only** through an arrow: a solution
/// read out of a codomain would have been extracted from under the binder,
/// where it may mention the bound variable and could not be lifted out
/// soundly. `A -> Type` is the shape that motivated this and it solves from
/// the domain, so the restriction costs nothing today and cannot be wrong
/// later (issues/exists-type-arg-not-inferred.md).
fn match_targs(
    decl: &Ty,
    actual: &Type,
    lvl: &Level,
    params: &[String],
    sols: &mut [Option<(Type, Level)>],
) {
    match &decl.kind {
        TyKind::Named { name, args } if args.is_empty() => {
            if let Some(i) = params.iter().position(|p| p == name)
                && sols[i].is_none()
            {
                sols[i] = Some((actual.clone(), lvl.clone()));
            }
        }
        TyKind::Fn { dom, .. } => {
            if let Type::Pi {
                dom_level,
                dom: adom,
                ..
            } = actual
            {
                match_targs(dom, adom, dom_level, params, sols);
            }
        }
        _ => {}
    }
}

/// May a field read off this receiver take the *reference*
/// (`docs/per-instantiation-type-codes-design.md` §13.6, and
/// `docs/x86-scaling-rail-out-of-fuel-design.md` §2.5, which narrowed it)?
///
/// Two conditions, and the second is the one the x86 scaling rail added.
///
/// 1. The receiver must bottom out in a **local** ([`receiver_is_neutral`]).
///    A reference is cheap to *compare* and dear to **compute through** — δ +
///    β where the inline `fst(sndʲ v)` is one elimination the evaluator fires
///    on the receiver's own value — and a certificate that chains twenty-eight
///    machine states through `state.memory` pays that once per read per level:
///    `reused_callee`'s `caller_native_memory_same_28` is refused `OutOfFuel`
///    with the reference and checks inside the default budget without.
///
/// 2. The receiver must not be the **bare local itself**. A reference minted
///    at a binder does not stay at a binder: a record's field type is
///    instantiated at every use, and `BlockArtifact`'s `after.memory` becomes
///    a reference over a *computed* state the moment the constructor
///    substitutes one — where condition 1 declines, so the record's field type
///    and every statement written against the same state disagree, the
///    shortcut cannot fire, and the kernel converts a 22-instruction symbolic
///    execution instead (the 20-node rail, `OutOfFuel` since the device
///    landed). A *chain* (`Sndᵏ`, an applied local) is §13.1's measured payer
///    and keeps the reference; a bare binder's read is one `fst(sndʲ v)` node,
///    which is what the walk costs anyway.
///
/// Together: the spelling of a field read is decided by shapes that survive
/// substitution, so the two sides of a conversion agree.
pub(crate) fn receiver_admits_reference(value: &Term) -> bool {
    !matches!(value, Term::Var(_)) && receiver_is_neutral(value)
}

/// Does this receiver bottom out in a **local** — so that a field read off it
/// is something the kernel compares, not something it computes?
fn receiver_is_neutral(value: &Term) -> bool {
    match value {
        Term::Var(_) => true,
        Term::Fst { pair, .. }
        | Term::Snd { pair, .. }
        | Term::FstAt { pair, .. }
        | Term::SndAt { pair, .. } => receiver_is_neutral(pair),
        Term::App { fun, .. } | Term::AppAt { fun, .. } => receiver_is_neutral(fun),
        _ => false,
    }
}
