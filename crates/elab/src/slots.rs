//! Elaboration **slots**: the seam between a `meta fn` template and the use
//! site it elaborates (docs/meta-def-registration-design.md).
//!
//! A slot is an elaboration site the elaborator is willing to hand over —
//! `vec.map`, `vec.fold`, … — one per Rust schema that can have an in-language
//! mirror. A template *declares* its slot (`meta fn map_code(g: Ctx) for
//! vec.map -> …`), and registration checks that it has the slot's type; a use
//! site names its slot and hands over a **bag of named ingredients**, never an
//! argument vector in the template's Π order.
//!
//! That split is the whole point (design doc §3): the Π order lives in the
//! template's own signature and nowhere else, because it is not free — it is
//! forced by the ingredients' dependencies (`tabulate`'s `f : Fin(k) -> B`
//! puts `k` before `f` in *every* well-formed spelling, and a call site that
//! hard-coded an order would be asserting a fact about a program it did not
//! write).
//!
//! Registration is **not a soundness gate**: it fixes a template's type, never
//! its body (a constant fold has `fold_code`'s type exactly), and the kernel
//! re-checks every emitted term regardless. It decides *which* functions get
//! the in-language path — nothing more.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::SlotPath;

/// The vocabulary. Closed by decision (design doc §2): a slot exists because a
/// Rust schema exists to state its type and to serve the instances a template
/// declines. User-declared slots are deferred (§10) — they need a story for
/// what the contract is when there is no Rust type to check against.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Slot {
    VecMap,
    VecFold,
    VecTabulate,
    VecNth,
    /// An **analyzer** slot (§ANALYZERS): the certifying generator's
    /// fragment transcriber.
    CertgenTranscribe,
    /// The certifying generator's fragment *signature* checker
    /// (docs/fn-signature-reflection-design.md §2): consumes a fn's type as
    /// code — the pull reflection API's first datum — and answers with the
    /// fragment arity, or declines.
    CertgenCheckSig,
}

/// What kind of thing a use site hands over for one ingredient, and hence how
/// the hook materializes it. Derived from the ingredient's *type* rather than
/// written twice: a universe binder takes a type, everything else a term.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IngredientKind {
    /// A `(A: Type<0>)` binder: the use site names a [`Type`], and the hook
    /// passes its Tarski code — or **declines** if it has none, or is not at
    /// level 0 (design doc §5).
    Type,
    /// An ordinary payload argument: the use site names a [`Term`].
    Term,
}

/// One ingredient a use site can supply, as the hook receives it.
pub(crate) enum Ingredient<'a> {
    Type { level: &'a Level, ty: &'a Type },
    Term(Term),
}

/// The type of one ingredient, in the little language a slot spec is written
/// in. Deliberately not raw [`Type`]s: an ingredient's type refers to *earlier
/// ingredients by name*, and the de Bruijn index that becomes depends on the
/// order the template declared — which is exactly what a slot must not fix.
/// Resolving names at build time is what lets a legally permuted template
/// (design doc §4.3) be accepted with no per-permutation Rust.
enum ITy {
    /// `Type<0>` — the binder that makes an ingredient a [`IngredientKind::Type`].
    Univ,
    Nat,
    /// `El a` — the element type an earlier `Univ` ingredient names.
    Elem(&'static str),
    /// `Fin(k)` for an earlier `Nat` ingredient `k`.
    Fin(&'static str),
    /// `s -> t`, non-dependent.
    Arrow(&'static ITy, &'static ITy),
    /// `[a; k]`.
    Vec {
        elem: &'static str,
        len: &'static str,
    },
}

impl ITy {
    fn kind(&self) -> IngredientKind {
        match self {
            ITy::Univ => IngredientKind::Type,
            _ => IngredientKind::Term,
        }
    }
}

pub(crate) struct Ingr {
    pub(crate) name: &'static str,
    ty: ITy,
}

impl Ingr {
    pub(crate) fn kind(&self) -> IngredientKind {
        self.ty.kind()
    }
}

pub(crate) struct SlotSpec {
    pub(crate) slot: Slot,
    /// `("vec", "map")` — how the `for` clause spells it.
    pub(crate) path: (&'static str, &'static str),
    /// The ingredient vocabulary. The order here is documentation and
    /// diagnostics only; the *template* fixes the Π order.
    pub(crate) ingredients: &'static [Ingr],
    /// What the payload returns once every ingredient is applied.
    result: ITy,
}

// The ingredient types, as consts so they can be referenced from the table.
const EL_A: ITy = ITy::Elem("A");
const EL_B: ITy = ITy::Elem("B");
const FIN_K: ITy = ITy::Fin("k");
const B_TO_B: ITy = ITy::Arrow(&EL_B, &EL_B);

/// The vocabulary, one entry per Rust schema in `crates/elab/src/vec.rs` (and
/// `nth`, whose schema is kernel-side, `term.rs`'s `nth`). All four slots now
/// have templates in `lib/lang/vec_code.hthr`; `vec.tabulate` and `vec.nth` waited
/// on a surface spelling for `Fin` and its index constructors
/// (`issues/surface-fin-indexing.md`), and their specs living here ahead of
/// that round is what let it add a template and not a third dispatch pattern.
static SLOTS: &[SlotSpec] = &[
    SlotSpec {
        slot: Slot::VecMap,
        path: ("vec", "map"),
        ingredients: &[
            Ingr {
                name: "A",
                ty: ITy::Univ,
            },
            Ingr {
                name: "B",
                ty: ITy::Univ,
            },
            Ingr {
                name: "f",
                ty: ITy::Arrow(&EL_A, &EL_B),
            },
            Ingr {
                name: "k",
                ty: ITy::Nat,
            },
            Ingr {
                name: "v",
                ty: ITy::Vec {
                    elem: "A",
                    len: "k",
                },
            },
        ],
        result: ITy::Vec {
            elem: "B",
            len: "k",
        },
    },
    SlotSpec {
        slot: Slot::VecFold,
        path: ("vec", "fold"),
        ingredients: &[
            Ingr {
                name: "A",
                ty: ITy::Univ,
            },
            Ingr {
                name: "B",
                ty: ITy::Univ,
            },
            Ingr {
                name: "z",
                ty: ITy::Elem("B"),
            },
            Ingr {
                name: "f",
                ty: ITy::Arrow(&EL_A, &B_TO_B),
            },
            Ingr {
                name: "k",
                ty: ITy::Nat,
            },
            Ingr {
                name: "v",
                ty: ITy::Vec {
                    elem: "A",
                    len: "k",
                },
            },
        ],
        result: ITy::Elem("B"),
    },
    SlotSpec {
        slot: Slot::VecTabulate,
        path: ("vec", "tabulate"),
        ingredients: &[
            Ingr {
                name: "B",
                ty: ITy::Univ,
            },
            Ingr {
                name: "k",
                ty: ITy::Nat,
            },
            Ingr {
                name: "f",
                ty: ITy::Arrow(&FIN_K, &EL_B),
            },
        ],
        result: ITy::Vec {
            elem: "B",
            len: "k",
        },
    },
    SlotSpec {
        slot: Slot::VecNth,
        path: ("vec", "nth"),
        ingredients: &[
            Ingr {
                name: "A",
                ty: ITy::Univ,
            },
            Ingr {
                name: "k",
                ty: ITy::Nat,
            },
            Ingr {
                name: "v",
                ty: ITy::Vec {
                    elem: "A",
                    len: "k",
                },
            },
            Ingr {
                name: "i",
                ty: ITy::Fin("k"),
            },
        ],
        result: ITy::Elem("A"),
    },
];

/// An **analyzer** slot: a `meta fn` that consumes code and returns a *value*
/// (docs/archive/certgen-transcriber-in-language-design.md §9.1, and
/// docs/meta-def-registration-design.md's dated extension section).
///
/// The difference from a template slot is what "having the slot's type" can
/// mean. A template is applied to the use site's context and then to the
/// slot's ingredients down its *payload's* Π spine, so the payload spine is
/// where the order lives and `ITy` is the little language that states it. An
/// analyzer has no payload: its arguments are its own Π binders, so whole-
/// signature convertibility fixes the order outright, and the invoking Rust
/// builds the application spine in the slot's canonical order. Same `for`
/// clause, same closed vocabulary, same declaration-time loudness, same
/// not-a-soundness-gate stance.
///
/// The expected signature is written **in Heather** and elaborated in the
/// declaring file's scope, which is what lets it name library types (`TOut`)
/// that are not Ψ globals at all — an inductive is inlined, so there is no
/// global for a Rust-built type to reference.
pub(crate) struct AnalyzerSpec {
    pub(crate) slot: Slot,
    pub(crate) path: (&'static str, &'static str),
    /// A `meta fn` declaration whose *signature* is the contract; its name and
    /// body are ignored.
    pub(crate) signature: &'static str,
}

/// One slot per client (the round's scoping). User-declared analyzer slots
/// are deferred with user-declared slots generally
/// (docs/meta-def-registration-design.md §10).
///
/// A `TyCode(g)` parameter in an expected signature is where a slot's **pull**
/// is visible (docs/fn-signature-reflection-design.md §1): the invoking Rust
/// fills it from `Elaborator::fn_type_code`, the reflection primitive, in the
/// slot's canonical order.
static ANALYZERS: &[AnalyzerSpec] = &[
    AnalyzerSpec {
        slot: Slot::CertgenTranscribe,
        path: ("certgen", "transcribe"),
        signature: "meta fn _sig(g: Ctx, arity: Nat, body: Code(g |- Nat)) -> TOut { TNo }",
    },
    AnalyzerSpec {
        slot: Slot::CertgenCheckSig,
        path: ("certgen", "check_sig"),
        signature: "meta fn _sig(g: Ctx, sig: TyCode(g)) -> SigOut { SigNo }",
    },
];

/// The analyzer slot a `for family.name` clause names, if it is one.
pub(crate) fn lookup_analyzer(path: &SlotPath) -> Option<&'static AnalyzerSpec> {
    ANALYZERS
        .iter()
        .find(|s| s.path == (path.family.as_str(), path.name.as_str()))
}

impl AnalyzerSpec {
    pub(crate) fn path_str(&self) -> String {
        format!("{}.{}", self.path.0, self.path.1)
    }
}

/// The slot a `for family.name` clause names, if it is one.
pub(crate) fn lookup(path: &SlotPath) -> Option<&'static SlotSpec> {
    SLOTS
        .iter()
        .find(|s| s.path == (path.family.as_str(), path.name.as_str()))
}

pub(crate) fn spec(slot: Slot) -> &'static SlotSpec {
    SLOTS
        .iter()
        .find(|s| s.slot == slot)
        .expect("every slot has a spec")
}

/// Every slot's path, for the unknown-slot diagnostic.
pub(crate) fn known_paths() -> String {
    SLOTS
        .iter()
        .map(|s| format!("`{}.{}`", s.path.0, s.path.1))
        .chain(
            ANALYZERS
                .iter()
                .map(|s| format!("`{}.{}`", s.path.0, s.path.1)),
        )
        .collect::<Vec<_>>()
        .join(", ")
}

impl SlotSpec {
    pub(crate) fn path_str(&self) -> String {
        format!("{}.{}", self.path.0, self.path.1)
    }

    /// The names, in the order this spec lists them — for diagnostics that
    /// have to say what a template was supposed to bind.
    pub(crate) fn ingredient_names(&self) -> String {
        self.ingredients
            .iter()
            .map(|i| format!("`{}`", i.name))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// The generic template type this slot's payload must have, spelled in the
    /// order `order` (positions into [`Self::ingredients`], as the template
    /// declared them) — design doc §2.2 step 3, the thing registration checks
    /// the declared statement against by **conversion**.
    ///
    /// Everything here is level 0 but the universe binders, which live at 1;
    /// the payload type's own level is the join, so a two-parameter template
    /// genuinely lives at level 1 (design doc §3's note on `map_code`).
    pub(crate) fn expected_payload_ty(&self, order: &[usize]) -> (Type, Level) {
        self.chain(order, 0)
    }

    fn chain(&self, order: &[usize], i: usize) -> (Type, Level) {
        let Some(&pos) = order.get(i) else {
            return self.build(&self.result, order, i);
        };
        let (dom, dom_level) = self.build(&self.ingredients[pos].ty, order, i);
        let (cod, cod_level) = self.chain(order, i + 1);
        (
            Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(cod),
            },
            Level::max(dom_level, cod_level),
        )
    }

    /// One ingredient type at `depth` binders in scope. An ingredient declared
    /// at position `p` of `order` is `Var(depth - 1 - p)` — which is why the
    /// spec names ingredients and the *order* supplies the arithmetic.
    fn build(&self, ity: &ITy, order: &[usize], depth: usize) -> (Type, Level) {
        let var = |name: &str| {
            let p = order
                .iter()
                .position(|&pos| self.ingredients[pos].name == name)
                .expect("an ingredient type names an ingredient of its own slot");
            debug_assert!(p < depth, "`{name}` is used before it is bound");
            Rc::new(Term::Var(LocalVar((depth - 1 - p) as u32)))
        };
        match ity {
            ITy::Univ => (Type::Ty(Level::Zero), Level::succ(Level::Zero)),
            ITy::Nat => (Type::Nat, Level::Zero),
            ITy::Elem(name) => (
                Type::El {
                    level: Level::Zero,
                    tm: var(name),
                },
                Level::Zero,
            ),
            ITy::Fin(name) => (Type::Fin { len: var(name) }, Level::Zero),
            ITy::Arrow(dom, cod) => {
                let (dom_t, dom_level) = self.build(dom, order, depth);
                let (cod_t, cod_level) = self.build(cod, order, depth + 1);
                (
                    Type::Pi {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::new(dom_t),
                        cod: Rc::new(cod_t),
                    },
                    Level::max(dom_level, cod_level),
                )
            }
            ITy::Vec { elem, len } => (
                Type::Vec {
                    level: Level::Zero,
                    elem: Rc::new(Type::El {
                        level: Level::Zero,
                        tm: var(elem),
                    }),
                    len: var(len),
                },
                Level::Zero,
            ),
        }
    }
}
