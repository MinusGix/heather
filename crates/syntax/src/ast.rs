//! The surface AST. Names, not de Bruijn; nothing here is trusted.
pub use heather_numeral::Numeral;

/// Byte range into the source, for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// Parser-internal call heads used to carry expected-type-directed constructor
/// notation through the ordinary expression AST. `#` is not an identifier
/// character, so source text can never name or shadow these sentinels.
pub const ANON_CTOR_ONLY: &str = "#anonymous-constructor";
pub const ANON_CTOR_LEFT: &str = "#anonymous-left-constructor";
pub const ANON_CTOR_RIGHT: &str = "#anonymous-right-constructor";

impl Span {
    pub fn join(self, other: Span) -> Span {
        Span { start: self.start.min(other.start), end: self.end.max(other.end) }
    }
}

/// A source file: a sequence of items.
#[derive(Debug, Clone)]
pub struct File {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub enum Item {
    Decl(Decl),
    Inductive(InductiveDecl),
    /// `class C<A> extends P<A> { f: T, … }` — a parameterized record plus a
    /// class-registry entry (docs/traits-layer1-design.md §2).
    Class(ClassDecl),
    /// `instance C<T> { … }` — a namespace of ordinary declarations plus an
    /// assembled record value (docs/traits-layer1-design.md §4).
    Instance(InstanceDecl),
    /// `designation + at Nat := add` — what an operator symbol means at a
    /// carrier (docs/operators-onto-classes-design.md §3).
    Designation(DesignationDecl),
    /// `datarepr N for S { … }` / `datarepr N for S := repr::naive();` — a
    /// runtime representation of a spec inductive, linked by certified
    /// refinement (docs/datarepr-design.md §1.4).
    Datarepr(DatareprDecl),
    /// `impl f for Rp { body := …, refines := … }` — one entry of the
    /// **cost basis**, the open per-operation registry (§1.2).
    Impl(ImplDecl),
    /// `import nat;` / `import option::{Option, map};`
    /// (docs/modules-design.md §3.1). Allowed only before the first
    /// declaration, so the import DAG is readable without elaborating
    /// anything.
    Import(ImportItem),
}

/// `designation<A> ++ at List<A> := append`
/// (docs/operators-onto-classes-design.md §3.1).
///
/// Shaped like `instance` on purpose: the generic binder list is in
/// `instance<A> Monoid<List<A>>(append)`'s position and does the same job — it
/// exists to *spell* the carrier, whose **head** is the half of the key that
/// is kept — and the right-hand side is `:=` plus a name, which is what an
/// instance's literal field is.
#[derive(Debug, Clone)]
pub struct DesignationDecl {
    /// `designation<A> …` — bound only so that `List<A>` parses. The key is
    /// the carrier's head, so these never reach it.
    pub tyvars: Vec<String>,
    /// Prefix and infix operators occupy distinct designation slots. Existing
    /// declarations omit the keyword and are infix; prefix declarations write
    /// it explicitly (`designation prefix - at Int := neg`).
    pub fixity: OpFixity,
    /// The operator, as written: `+`, `++`, `*`, `^`, `&&`, `||`, `<=`, `<`,
    /// `-`, `!`, `⁻¹`.
    pub symbol: String,
    pub carrier: Ty,
    /// The designated operation. A **bare global name** (§3.2): it is emitted
    /// bare at each use site and instantiated there by ordinary implicit
    /// inference, which is why a written type application would be wrong
    /// rather than merely unsupported.
    pub op: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpFixity {
    Prefix,
    Infix,
    /// `x⁻¹`, the only postfix symbol (docs/inverse-power-notation-design.md
    /// §2), declared `designation postfix ⁻¹ at Rat := Rat::inv`.
    Postfix,
}

impl OpFixity {
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Prefix => "prefix",
            Self::Infix => "infix",
            Self::Postfix => "postfix",
        }
    }
}

/// One `import` item. The listed names are a *standing disambiguation*, not a
/// different mode: `import m::{…}` imports all of `m` exactly as `import m;`
/// does, and additionally says which `m` the listed names mean when something
/// else in scope declares them too (docs/modules-design.md §4).
#[derive(Debug, Clone)]
pub struct ImportItem {
    /// Explicit selected reexport (`export m::{x};`); ordinary imports stay private.
    pub reexport: bool,
    pub module: String,
    pub module_span: Span,
    pub listed: Vec<(String, Span)>,
    pub span: Span,
}

impl Item {
    /// The `fn`/`theorem` declaration, panicking otherwise. For tests and
    /// callers that have just constructed the item.
    pub fn into_decl(self) -> Decl {
        match self {
            Item::Decl(d) => d,
            Item::Inductive(i) => panic!("expected a declaration, found `inductive {}`", i.name),
            Item::Import(i) => panic!("expected a declaration, found `import {}`", i.module),
            Item::Class(c) => panic!("expected a declaration, found `class {}`", c.name),
            Item::Instance(i) => {
                panic!("expected a declaration, found `instance {}`", i.class.name)
            }
            Item::Designation(d) => {
                panic!("expected a declaration, found `designation {}`", d.symbol)
            }
            Item::Datarepr(d) => {
                panic!("expected a declaration, found `datarepr {}`", d.name)
            }
            Item::Impl(i) => {
                panic!("expected a declaration, found `impl {}`", i.op)
            }
        }
    }
}

/// `datarepr VecList for List<Tok> { R := VecT, … }`
/// (docs/datarepr-design.md §1.4).
///
/// A dedicated form rather than an `instance`, for a structural reason: the
/// record's field list is computed from the spec inductive's constructor list,
/// and an instance instantiates a *fixed* class shape.
#[derive(Debug, Clone)]
pub struct DatareprDecl {
    /// The repr's name. Also the minting site for a parameterized
    /// instantiation's monomorph name (§1.4 item 2), which is why it is
    /// written rather than derived.
    pub name: String,
    /// The spec type this represents: `List<Tok>`, `Nat`.
    pub spec: Ty,
    pub body: DatareprBody,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum DatareprBody {
    /// `{ R := …, mk Cons := …, … }`.
    Fields(Vec<DatareprField>),
    /// `:= repr::naive()` and, later, other repr-producing meta-programs. The
    /// expression is kept as written; which ones are understood is the
    /// elaborator's rule, not the grammar's.
    Mint(Expr),
}

/// `impl length for VecList { body := …, refines := … }`
/// (docs/datarepr-design.md §1.2). The operation is an *index*, so the
/// registry is open by construction — there is no closed field list to amend.
#[derive(Debug, Clone)]
pub struct ImplDecl {
    /// The spec function this implements.
    pub op: String,
    /// The repr it implements it at — a `datarepr`'s name.
    pub repr: String,
    /// Reuses a `datarepr`'s body node, and for the same two reasons: the
    /// clause shapes are the same `f := e` (with `mk` simply never set here),
    /// and the `:= <route>` form is the same one token of lookahead —
    /// `impl length for ListTok := derive();`
    /// (docs/obligation-records-design.md §4.1, §4.3).
    pub body: DatareprBody,
    pub span: Span,
}

/// One clause of an explicit `datarepr` body. `:=` rather than `:` for the
/// reason an instance's literal field uses it: a `:` here would read as a
/// field's type ascription.
#[derive(Debug, Clone)]
pub struct DatareprField {
    /// `mk Cons := vec_prepend` — this clause is a *constructor image*, and
    /// `name` is the spec constructor's name rather than a record field's.
    /// The elaborator checks the clause list against `S`'s declaration.
    pub is_mk: bool,
    pub name: String,
    pub expr: Expr,
    pub span: Span,
}

/// `class C<A, …> extends P<A>, Q<A> { f: T, … }`
/// (docs/traits-layer1-design.md §2). The lowering is a `record`'s: the
/// elaborator concatenates the ancestors' fields in front of `fields` and
/// hands the result to the tier-0 generator. What the keyword buys is the
/// registry entry and the `extends` discipline, not a second encoding.
#[derive(Debug, Clone)]
pub struct ClassDecl {
    pub name: String,
    pub params: Vec<String>,
    /// `class Monoid<A>(op: A -> A -> A)` — the class's **value indices**
    /// (docs/operation-indexed-classes-design.md §3). The same
    /// [`InductiveDecl::valparams`] a `record` head takes, and lowered by the
    /// same path: what the keyword adds is that the index joins the registry
    /// key and the constraint binder's desugaring. Empty for an unindexed
    /// class, which is every class written before this grammar existed.
    pub valparams: Vec<Param>,
    pub extends: Vec<ClassRef>,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

/// `Monoid<A>` in an `extends` list or an `instance` head — a class applied to
/// its arguments. Angle brackets and no `for`: the carrier is a *parameter*,
/// and privileging one of several would break at `Coe<A, B>`
/// (docs/traits-design.md §3).
#[derive(Debug, Clone)]
pub struct ClassRef {
    pub name: String,
    pub args: Vec<Ty>,
    /// `Monoid<A>(op)` — the **index arguments**
    /// (docs/operation-indexed-classes-design.md §3, §4.1). Empty at an
    /// unindexed class, and empty at an indexed one whose slot is left for the
    /// binder desugaring to fill (§4.1's EMPTY referent).
    pub index: Vec<Expr>,
    /// `extends Monoid<A>(op) as additive` — a named parent dictionary path.
    /// Empty on ordinary class references and untagged parents. During class
    /// elaboration, transitive ancestors prepend the path through which their
    /// dictionary is reached, so this also serves as committed class metadata.
    pub path: Vec<String>,
    pub span: Span,
}

/// `instance<A, B> C<T> requires m: D<A> { … }`
/// (docs/traits-layer1-design.md §4).
#[derive(Debug, Clone)]
pub struct InstanceDecl {
    /// `instance<A, B> …` — the generic instance's type parameters. They
    /// become leading implicit parameters of every member and of the assembled
    /// value, exactly as a `fn`'s do.
    pub tyvars: Vec<TyParam>,
    /// `instance(n, m: Nat) Decide<Le(n, m)>` — the instance's **value
    /// binders** (docs/value-generic-instances-design.md §2). Written after the
    /// type parameters and in the same production a `record` head takes, they
    /// are what lets an instance be generic over a *value* rather than only
    /// over a type or fixed at one index.
    ///
    /// Every one is `implicit: true` by the time it leaves the parser: a use
    /// site never writes them, because resolution recovers them by unifying the
    /// instance head against the goal — the same route `instance<A>`'s type
    /// parameters already take. Empty for every instance written before this
    /// grammar existed.
    pub valparams: Vec<Param>,
    pub class: ClassRef,
    /// `requires ma: Monoid<A>, …` — **solver parameters**
    /// (docs/traits-layer2-design.md §1): implicit at every use site and
    /// filled by resolution, passed by hand only under `@`. Layer 1 had them
    /// as ordinary explicit parameters; layer 2 is what changed the use site.
    pub requires: Vec<Param>,
    pub body: InstanceBody,
    pub span: Span,
}

/// The two spellings of an instance body (docs/traits-design.md §3), told
/// apart by one token: a body that starts with `fn`/`theorem`/`meta` is a
/// block, anything else is a literal. There is no mixed form.
#[derive(Debug, Clone)]
pub enum InstanceBody {
    /// Each member elaborates, in order, to a real top-level global under the
    /// instance's namespace; the value is assembled from them at the end.
    Block(Vec<Decl>),
    /// `op := Rat::add` — assembled from previously declared globals.
    Literal(Vec<InstanceField>),
}

/// One `f := e` of an instance's literal body. `:=` rather than `:` because a
/// `:` inside instance braces would read as both a record-literal field and a
/// class field's type ascription.
#[derive(Debug, Clone)]
pub struct InstanceField {
    pub name: String,
    pub expr: Expr,
    pub span: Span,
}

/// `inductive D<p, …> { c(f: T, …), … }` — a datatype declaration. Tier 0
/// (non-recursive) compiles to sums-of-Σs; see docs/inductive-tier0-lowering.md.
/// Type parameters are monomorphized: `D<Nat>` and `D<Bool>` are unrelated
/// kernel types.
#[derive(Debug, Clone)]
pub struct InductiveDecl {
    pub name: String,
    /// Type-parameter names, in order.
    pub params: Vec<String>,
    /// `record R(p: Prog, env: Val)` — **value** parameters, in order, written
    /// after the type parameters (docs/surface-value-parameters.md §1). A value
    /// parameter is a *term* the use site supplies, substituted into the field
    /// types at lowering exactly as a type parameter's instantiation is; it is
    /// what makes a record usable as a **predicate** over the values it is
    /// applied to (`Converges(p, env, ir, vs)`).
    ///
    /// Reuses [`Param`] rather than a new node so `{implicit}` and `self` stay
    /// available if they are ever wanted here; both are rejected for now.
    /// Empty for every declaration written before this grammar existed.
    pub valparams: Vec<Param>,
    pub ctors: Vec<CtorDecl>,
    /// Written `record D<…> { f: T, … }` — one constructor, named after the
    /// declaration, every field named (docs/surface-records.md §2). The
    /// *lowering* is the ordinary tier-0 one; this flag is what earns the
    /// extra surface checks (non-recursive, distinct field names) and the
    /// accessor table.
    pub is_record: bool,
    /// Written `codata D<…> { … }` — a **coinductive** declaration
    /// (docs/codata-elaborator-design.md): the same constructor grammar,
    /// lowered onto the kernel's negative `M` former instead of an inductive
    /// one, so a value may be infinitely deep and is observed only by `match`.
    pub is_codata: bool,
    /// `inductive Vec<A> : (n: Nat) -> Type { … }` — the index telescope of an
    /// indexed family (docs/inductive-indexed-lowering.md §2). Parsed as an
    /// ordinary [`TyKind::Fn`] and validated by the elaborator: this round it
    /// must be one `Nat` binder into bare `Type`. `None` for every unindexed
    /// declaration, whose grammar is unchanged.
    pub index: Option<Ty>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CtorDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    /// `Nil : Vec<A>(0)` — the result annotation of an indexed declaration's
    /// constructor, as the expression `D<params>(pattern)`
    /// (docs/inductive-indexed-lowering.md §2). Mandatory when the declaration
    /// has an index telescope, an error when it does not; the elaborator
    /// decomposes and validates it.
    pub result: Option<Expr>,
    pub span: Span,
}

/// One constructor field. A *named* field (`Some(n: Nat, p: n = n)`) is in
/// scope in the types of the fields after it — that dependency is the reason
/// the encoding's field spine is a Σ and not a product.
#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: Option<String>,
    pub ty: Ty,
    /// `name: T := e` — what fills the field when a construction leaves it
    /// out (docs/named-arguments-design.md §9): checked at the field's type
    /// as the construction instantiates it, in the declaration's scope.
    pub default: Option<Box<Expr>>,
    pub span: Span,
}

/// `fn name(params) -> T { body }` (computing definition),
/// `theorem name(params): T { proof }` (opaque), or
/// `axiom name(params): T;` (an explicit, bodiless assumption).
#[derive(Debug, Clone)]
pub struct Decl {
    pub kind: DeclKind,
    /// `meta fn` — a layer-m declaration (docs/in-language-map-design.md §3).
    /// Its parameters may be `Ctx`/`TyCode`/`Code` binders, its body is
    /// quotation, and it is registered elaborator-side rather than in Ψ.
    /// Only `fn` may carry it; `meta theorem` is rejected in the parser.
    pub is_meta: bool,
    /// `evidence theorem` — an **evidence rule**: a theorem `:= infer` may
    /// apply to a proposition goal, backchaining through its own `:= infer`
    /// premises (docs/positivity-evidence-design.md §6 A). Only a theorem may
    /// carry it, and the elaborator refuses one with a parameter search could
    /// not fill.
    pub is_evidence: bool,
    /// `meta fn map_code(g: Ctx) for vec.map -> …` — the elaboration **slot**
    /// this template fills (docs/meta-def-registration-design.md §2.1). A
    /// `meta fn` without one is registered but never dispatched: the clause,
    /// not the declaration's name, is what routes a use site. Only a `meta fn`
    /// may carry it.
    pub elaborates: Option<SlotPath>,
    pub name: String,
    /// `fn map<A, B>(…)` — type parameters, in order. Each becomes a
    /// **leading implicit parameter at `Type<n>`**, usable as a type inside
    /// this declaration and nowhere else (docs/surface-polymorphism.md §2,
    /// docs/surface-universe.md §2). Unlike an `InductiveDecl`'s parameters
    /// these are not monomorphized: they are real kernel binders, and a use of
    /// one is `El A`.
    pub tyvars: Vec<TyParam>,
    pub params: Vec<Param>,
    /// Return type of a `fn`, statement of a `theorem`.
    pub result: Ty,
    /// `decreases e` — a `Nat` measure justifying recursion the structural
    /// checker declines (docs/termination-measures-design.md). The body is
    /// then elaborated as strong induction on a bound for `e`, and every
    /// recursive call owes `e[args] < e`, a goal hole named `decN`.
    pub decreases: Option<Expr>,
    pub body: Block,
    pub span: Span,
}

/// `vec.map` — the dotted name of an elaboration slot. Two segments: the
/// family and the slot within it. The vocabulary is the elaborator's
/// ([`crates/elab/src/slots.rs`]), so the parser only shapes it — an unknown
/// path is a *registration* diagnostic, where the known ones can be listed.
#[derive(Debug, Clone)]
pub struct SlotPath {
    pub family: String,
    pub name: String,
    pub span: Span,
}

/// One type parameter: `A`, or `A: Type<1>`.
///
/// The level is the *universe the parameter ranges over*, defaulting to 0 —
/// `<A>` is `<A: Type<0>>`, which is what every declaration written before
/// docs/surface-universe.md meant. It is a numeral for the same reason
/// [`TyKind::Univ`]'s is: a level variable is `UPi`, layer m
/// (issues/implicit-level-polymorphism.md is the deferred alternative, where
/// an unannotated `<A>` would instead be generic in its level).
#[derive(Debug, Clone)]
pub struct TyParam {
    pub name: String,
    pub level: u64,
    pub span: Span,
}

/// A block: local bindings, the result expression, then the `on` discharges
/// of any goals raised inside it (issues/goal-holes.md). Blocks exist only as
/// declaration bodies for now, so "end of block" and "end of declaration"
/// coincide — that is also the scope of a goal.
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub result: Box<Expr>,
    /// Order-free: an `on` may discharge a goal raised anywhere in the block.
    pub ons: Vec<OnStmt>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    /// `let x = e;` or `let x: T = e;`. The annotation is what puts the
    /// right-hand side in *checking* position, so `let p: a = b = ?g;` is how
    /// a hole gets bound to a name.
    ///
    /// `opaque` is `have x = e;` (docs/have-design.md): the rest of the block
    /// sees `x : T` and not its value, and elaboration binds it by a β-redex
    /// instead of an alias. One variant, not two, so that every walker that
    /// only cares what a statement binds treats the two alike.
    Let { name: String, ty: Option<Ty>, expr: Expr, span: Span, opaque: bool },
    /// `let { unit := u, op } = m;` — record destructuring
    /// (docs/named-patterns-by-field-design.md §2). Each right-hand binder is
    /// aliased to the selected projection, so this remains sugar over
    /// [`ExprKind::Dot`]. Partial patterns and `_` are allowed. No annotation:
    /// the receiver must infer, since it is what names the fields.
    LetRecord { fields: Vec<RecordPatField>, expr: Expr, span: Span },
    /// `let code x = e;` — the surface letbox (surface-v0 §4, adopted
    /// verdict (c)). Binds `x` as *code*: a later `$x` inside a quote hoists
    /// a `LetBoxTm` for it. Meta-layer blocks only.
    LetCode { name: String, expr: Expr, span: Span },
}

/// One named slot of a record destructuring pattern:
/// `let { witness := x, proof := hx } = h;`. The field name selects the
/// projection; the pattern names (or ignores) the projected value.
#[derive(Debug, Clone)]
pub struct RecordPatField {
    pub name: String,
    pub pat: Pat,
    pub span: Span,
}

/// `on ?name := expr;` / `on _: P := expr;` — discharge of a goal.
#[derive(Debug, Clone)]
pub struct OnStmt {
    pub target: OnTarget,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum OnTarget {
    /// By name — the site name `?first`, or a checker-assigned default
    /// (`?bound`, `?bound.1`, …).
    Name(String),
    /// By statement: discharges *every* goal whose statement is `P`.
    Stmt(Ty),
    /// `on Ctor(x, y) := e;` — a **`split` arm**, not a goal discharge
    /// (docs/match-equation-split-design.md §5). Told apart from the two above
    /// by one token: a discharge head is `?name` or `_`, an arm head is an
    /// ordinary identifier, which was a parse error before this existed.
    ///
    /// Never reaches the elaborator: `split_result` consumes these into
    /// [`Arm`]s, and an arm head in a block with no `split` is a parse error.
    Ctor { ctor: String, binders: Vec<Pat>, default: bool },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Fn,
    Theorem,
    Axiom,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    /// Written `{name: T}` — filled by unification at call sites unless the
    /// call is `@`-marked (fully explicit). See issues/elab-stage2-metas.md.
    pub implicit: bool,
    /// Written `self name: T` — this is the parameter a method call's
    /// *receiver* fills, so `x.f(a)` is `f(a, x)` when the second parameter
    /// is marked and `f(x, a)` when the first is. Unmarked declarations
    /// default to their first explicit parameter, so the flag is only ever
    /// written where the subject is *not* first (`cong`). A marker on a
    /// normally-named parameter rather than a name, because a proof wants to
    /// be called `p`; `self: T` names it `self` as well, for record methods.
    /// See issues/method-receiver-position.md.
    pub is_self: bool,
    /// A **solver default** (docs/traits-layer2-design.md §1): the argument is
    /// produced by a solver run in the caller's context when the caller omits
    /// it. Written `hx: P := infer`, or as a `requires` binder — the two
    /// spellings desugar here, and a solver parameter is always `implicit`
    /// (it has no positional slot; `@f(…)` is how one is passed by hand).
    pub solver: Option<Solver>,
    /// A **parameter default** (docs/named-arguments-design.md §9): written
    /// `b: T := e` with any expression but `infer`. Like a solver parameter
    /// it has no positional slot and is always `implicit`; a call that leaves
    /// it out gets `e` checked at the parameter's instantiated type, with
    /// names resolved where the declaration was written, and a named argument
    /// (`b := …`) overrides it.
    pub default: Option<Box<Expr>>,
    /// Where this parameter entered the written telescope. Assumption groups
    /// are parser sugar over ordinary solver parameters, but the distinction
    /// remains observable to the advisory unused-assumption lint.
    pub origin: ParamOrigin,
    /// `op as ∙: A -> A -> A` — the **body spelling** this binder installs
    /// (issues/binder-symbol-as-notation.md). The identifier stays the binder's
    /// *interface* spelling: constraint slots, call sites, the registry and
    /// every diagnostic go on saying `op`, and the symbol is local notation for
    /// the binder's own scope (the rest of the telescope, the result type, and
    /// the body — for a class head, the class body).
    ///
    /// Set only where a binder is **declared**: a class head's index parameter
    /// and a `fn`/`theorem` value parameter. Never on a reference — a linked
    /// constraint slot mentions a parameter declared elsewhere, and notation
    /// belongs where the name is born — so the three constraint slots (empty /
    /// linked / symbol) keep exactly the grammar the operators round left them.
    ///
    /// `None` for every parameter written before this grammar existed.
    pub symbol: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamOrigin {
    /// A parameter or named `requires` binder written on this declaration.
    Written,
    /// An anonymous dictionary synthesized from an inline type constraint.
    InlineConstraint,
    /// A solver parameter prepended by an enclosing `assuming` item group.
    Assuming,
}

/// The solvers a parameter default may name. One this round
/// (docs/traits-design.md §8 enumerates the others, layer 3's).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Solver {
    /// Search the caller's scope, then the instance registry, for a value of
    /// the parameter's type.
    Infer,
}

/// Surface types. `a = b` is the identity type at the (synthesized) type
/// of `a` (Heather merges binding and equality onto one `=`, ML-style;
/// issues/surface-syntax.md).
#[derive(Debug, Clone)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TyKind {
    Nat,
    Eq(Box<Expr>, Box<Expr>),
    /// `Type<n>`, and `Type` for `Type<0>` — the kernel's `Type::Ty(n)`, a
    /// type at level `n + 1` (docs/surface-universe.md §2).
    ///
    /// The level is a **numeral**, never a name or an expression: quantifying
    /// over a level is `UPi`, which is layer m by construction
    /// (issues/surface-universe.md §7), and joins are computed by the
    /// elaborator rather than written.
    Univ { level: u64 },
    /// An arbitrary expression in type position, decoded: `m.carrier`,
    /// `f(x)`. Elaborated by inferring the expression and requiring its type
    /// to be a universe, then wrapping in `El` — the dual of the `Expr`/`Ty`
    /// bridge (docs/surface-universe.md §4), and what makes a **bundled**
    /// record's carrier usable as a type.
    ///
    /// Only reached as `ty_atom`'s last resort, so a bare name is still
    /// [`TyKind::Named`] and nothing that used to parse as a type changes
    /// shape.
    OfExpr(Box<Expr>),
    /// A declared inductive, applied to its type arguments (`Bool`,
    /// `Option<Nat>`), or a type parameter in scope inside an `inductive`.
    Named { name: String, args: Vec<Ty> },
    /// `[T; n]` — a length-indexed vector, the kernel's `Type::Vec`. A
    /// *primitive* indexed type, not a user declaration: there is no fording
    /// and no encoding (docs/container-fields.md §2.1). The length is an
    /// expression checked at `Nat`.
    Vec { elem: Box<Ty>, len: Box<Expr> },
    /// `Fin(n)` — the kernel's `Type::Fin`, the type of indices below `n`. A
    /// *primitive* indexed type for the same reason [`TyKind::Vec`] is: a
    /// kernel former rather than a user declaration, so it gets a node rather
    /// than an encoding (docs/surface-fin-indexing-design.md §2.1). The length
    /// is an expression checked at `Nat`.
    ///
    /// No parser rule of its own: `Fin(n)` reaches this through `expr_as_ty`,
    /// which claims the *name* `Fin` exactly as it claims `Nat` — so `Fin` is
    /// a reserved type-former name in type position (§2.2).
    Fin(Box<Expr>),
    /// Propositional truncation, written `∥A∥` or `Squash<A>`.
    Squash(Box<Ty>),
    /// `(x: A) -> B` (dependent) or `A -> B` (`binder: None`).
    /// Right-associative; one binder per parenthesis group, so `(x: A) (y: B)
    /// -> C` is written `(x: A) -> (y: B) -> C`
    /// (docs/surface-function-types.md §1.1).
    ///
    /// `implicit` marks a `{x: A} -> B` binder. The flag never reaches the
    /// kernel — `Type::Pi` has no slot for it — it is read off the surface
    /// type into the elaborator's positional implicitness *skeleton*
    /// (docs/implicit-binders-design.md §2), which governs insertion at uses
    /// and is erased at the kernel boundary
    /// (issues/implicit-binders-in-function-types.md).
    Fn { binder: Option<String>, implicit: bool, dom: Box<Ty>, cod: Box<Ty> },
    /// `Ctx` — the kind of a context binder in a `meta fn` signature
    /// (docs/in-language-map-design.md §3). Layer m only; a diagnostic
    /// anywhere else.
    Ctx,
    /// `TyCode(g)` — code of a type in context `g`, the kernel's
    /// `□(g ⊢ Ty 0)`. The binder becomes a global (`TyLam`), so its splices
    /// need no letbox. Level fixed at 0 for the slice.
    TyCode { ctx: String },
    /// `Code(g |- T)` — code of a term of type `T` in context `g`, the
    /// kernel's `□(g ⊢ T)`. `T` is elaborated at `Layer::Code` in `g`.
    Code { ctx: String, ty: Box<Ty> },
    /// `$a` in type position — a `TyCode` binder used as a type inside a
    /// quote payload (a `GlobalTy` reference after elaboration).
    Splice { name: String },
}

/// One field of a record literal: `unit: 0`. The span is the whole
/// `name: expr`, so a duplicate or unknown field is reported at the field
/// rather than at the literal.
#[derive(Debug, Clone)]
pub struct RecordLitField {
    pub name: String,
    pub expr: Expr,
    pub span: Span,
}

/// One **named argument** at a call site: `xs := ys`
/// (docs/named-arguments-design.md §3). The span covers the whole
/// `name := expr`; `name_span` covers the identifier alone, so a refusal
/// about the *name* points at the name and not at its value.
///
/// `:=` rather than `:` or `=`: `:` introduces a *type* in every binding
/// position in this grammar and a type is an expression (§3.1), and `=` is
/// the identity-type former, so `f(a = x)` is already a legal one-argument
/// call (§3.2). `:=` is this language's operator for filling a named slot —
/// `on ?g := e`, an instance's `op := e`, a binder's `:= infer` — and a
/// named argument is that slot filled from the other side.
#[derive(Debug, Clone)]
pub struct NamedArg {
    /// Written parameter name, or private `#decreasing:label` call metadata.
    /// The latter is consumed by measure lowering, never passed to a callee.
    pub name: String,
    pub name_span: Span,
    pub expr: Expr,
    pub span: Span,
}

/// One lambda binder: `x`, `(x: A)`, `{x}` or `{x: A}`. An unannotated
/// binder is only usable in checking position, where the expected Π supplies
/// the domain. `implicit` marks the brace spelling; like [`TyKind::Fn`]'s
/// flag it is surface-only — the emitted `Term::Lam` is byte-identical to
/// the explicit spelling's (docs/implicit-binders-design.md §7.2).
#[derive(Debug, Clone)]
pub struct LamBinder {
    pub name: String,
    pub ty: Option<Ty>,
    pub implicit: bool,
    pub span: Span,
}

/// One field position of a `match` arm: a binder, or a **deep pattern** —
/// a constructor applied to more patterns
/// (docs/nested-match-patterns-design.md §3.1).
///
/// A deep pattern never survives elaboration's preprocessing: the pattern
/// matrix compiles it into a nested single-level `match` on a generated
/// binder, so every lowering below sees only [`Pat::Var`].
///
/// A bare identifier is a [`Pat::Ctor`] with no arguments **iff it names a
/// constructor** — the rule expression position already uses, where `resolve`
/// falls through to `ctor_of`. The parser cannot tell the two apart (it has no
/// constructor table), so it always produces [`Pat::Var`] and the elaborator
/// reclassifies (§3.5). `_` is always a binder.
#[derive(Debug, Clone)]
pub enum Pat {
    Var { name: String, span: Span },
    Ctor { name: String, args: Vec<Pat>, span: Span },
    /// `field := pattern` inside a constructor pattern. This wrapper is
    /// surface-only: elaboration restores declaration order and fills omitted
    /// slots with `_` before the existing pattern matrix sees it.
    Named { field: String, pat: Box<Pat>, span: Span },
}

impl Pat {
    pub fn span(&self) -> Span {
        match self {
            Pat::Var { span, .. } | Pat::Ctor { span, .. } | Pat::Named { span, .. } => *span,
        }
    }

    /// The binder name, for the lowerings — which only ever run on patterns
    /// the preprocessing has already flattened. A `Ctor` here is a bug in the
    /// preprocessing, not a user error, so it reads as an unspellable name
    /// rather than panicking in a library.
    pub fn name(&self) -> &str {
        match self {
            Pat::Var { name, .. } => name,
            Pat::Ctor { .. } => "#deep",
            Pat::Named { .. } => "#named",
        }
    }

    /// Is this pattern, or anything under it, a constructor application?
    pub fn is_deep(&self) -> bool {
        match self {
            Pat::Var { .. } => false,
            Pat::Ctor { .. } => true,
            Pat::Named { pat, .. } => pat.is_deep(),
        }
    }

    pub fn has_named(&self) -> bool {
        match self {
            Pat::Var { .. } => false,
            Pat::Ctor { args, .. } => args.iter().any(Pat::has_named),
            Pat::Named { .. } => true,
        }
    }
}

/// One `match` arm: `C(x, y) => body`, or the default `_ => body`. The
/// binders are the constructor's fields, positionally. `Succ(k, ih)` on `Nat`
/// is the one place a second binder is *not* a field: it is the explicit
/// induction hypothesis, kept as a low-level fallback
/// (issues/match-recursion.md).
#[derive(Debug, Clone)]
pub struct Arm {
    /// The constructor's name, or `"_"` when [`Arm::default`] is set. The
    /// sentinel is deliberate: a default arm is expanded away before any
    /// lowering runs, so if one ever leaked it dies at "`_` is not a
    /// constructor of `X`" rather than silently
    /// (docs/nested-match-patterns-design.md §3.1).
    pub ctor: String,
    /// `_ => body` — expands to the constructors with no arm of their own
    /// (docs/nested-match-patterns-design.md §4). Binds nothing, appears last,
    /// at most once.
    pub default: bool,
    pub binders: Vec<Pat>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// Parser-generated head for `split_all; all_goals { ... }`. A NUL cannot be
/// written by the surface lexer, so ordinary declarations and locals can
/// never collide with this checking-form marker.
pub const SPLIT_ALL_GOALS: &str = "\0split-all-goals";

impl Expr {
    /// `f(a, b)` with a *name* at the head — the shape every name-keyed
    /// special form wants (`absurd`, `inj`, constructors, `Succ`, a self-call,
    /// and implicit-argument insertion, which is name-directed). Returns
    /// `None` for an application of anything else.
    pub fn as_named(&self) -> Option<(&str, &[Expr], bool)> {
        match &self.kind {
            ExprKind::App { head, args, explicit, .. } => match &head.kind {
                ExprKind::Var(name) => Some((name.as_str(), args.as_slice(), *explicit)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The call's **named** arguments, or `&[]` for anything that is not a
    /// call (docs/named-arguments-design.md §8.2).
    ///
    /// Every consumer of [`Self::as_named`] hands the positional slice to a
    /// name-keyed special form — a builtin arm, a fragment recognizer — and
    /// those have no parameter table to be called by, so a named argument at
    /// one must be *refused* rather than dropped. This is the accessor that
    /// lets them notice.
    pub fn named_args(&self) -> &[NamedArg] {
        match &self.kind {
            ExprKind::App { named, .. } => named.as_slice(),
            ExprKind::Dot { named, .. } => named.as_slice(),
            _ => &[],
        }
    }
}

/// Which surface spelling built an [`ExprKind::Match`]: the expression form,
/// or the statement-position `split e; on C(…) := …;`
/// (docs/match-equation-split-design.md §6).
///
/// Both spellings build one node and one elimination — that is §6's whole
/// point, and it stays true because this is consulted **only** where a
/// diagnostic has to name the form the user typed
/// (issues/diagnostics-name-the-written-form.md).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchForm {
    /// `match e { … }`
    Match,
    /// `split e; on C(x⃗) := b;`
    Split,
    /// `if P { yes } else { no }`, lowered through `decide<P>()` to the
    /// ordinary `Or` constructors. Like `Split`, this survives only so
    /// diagnostics name the spelling the writer used.
    If,
    /// `if let P = e { yes } else { no }`, lowered to a one-row pattern
    /// matrix followed by a default arm. This is diagnostic provenance only;
    /// pattern compilation and elimination are the ordinary match path.
    IfLet,
}

impl MatchForm {
    /// The keyword the user wrote, for a message that names the form.
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Match => "match",
            Self::Split => "split",
            Self::If => "if",
            Self::IfLet => "if let",
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A name: parameter, `fn`, or `theorem`.
    Var(String),
    /// An **operator symbol** — `+`, `++`, `*`, `&&`, `||`, `<=`, `<`, `-`, `!`
    /// (docs/operators-onto-classes-design.md §4). A name in a namespace of
    /// its own: `a + b` is this node *applied*
    /// (`App { head: OpSymbol { symbol: "+", fixity: Infix }, … }`) and a lone symbol between delimiters
    /// — `Monoid(+)`, `A::CommMonoid(+)` — is it unapplied, which is the
    /// designation reference §7 of the operation-indexed design specified.
    ///
    /// Never reaches a kernel term: the elaborator resolves it to a name at
    /// the top of `elab_infer_at`/`elab_check_skel` and everything downstream
    /// is the ordinary application path. Its last resolution rung is the
    /// fixed name the parser used to desugar to, which is why every operator
    /// expression that elaborated before this node existed still elaborates
    /// to the same term.
    OpSymbol { symbol: String, fixity: OpFixity },
    /// `Type<n>` where a *term* is expected — the code `TmTy(n) : Ty (n+1)`.
    /// A universe is a type, so it is spellable in both positions; this is the
    /// expression one, and it infers rather than needing the `Expr`/`Ty`
    /// bridge (docs/surface-universe.md §4).
    Univ { level: u64 },
    /// Numeral literal (desugars to `Zero`/`Succ`).
    Num(Numeral),
    /// `'x'` — a character literal, carrying the scalar value the lexer read
    /// (docs/string-char-design.md §3). At `Char` it elaborates to
    /// `char::ofNat(code, decide)`; at another carrier it resolves
    /// `CharLiteral` the way a numeral resolves `Numeral`.
    Char(char),
    /// `"…"` — a string literal, carrying the decoded scalar values. At
    /// `String` it is the record over the list literal of its characters,
    /// reusing the collection-literal lowering; at another carrier it
    /// resolves `StringLiteral`.
    Str(String),
    /// `·` / `·₀` / `·₁₂` — an anonymous argument slot
    /// (issues/argument-slot-sections.md). `None` is an unindexed slot;
    /// `Some(n)` is the explicitly zero-based slot `n`. Checking-position
    /// elaboration replaces every slot at one abstraction boundary with an
    /// ordinary local and wraps the expression in ordinary lambdas. This node
    /// must therefore never reach a kernel term.
    ArgSlot(Option<u64>),
    /// `f(a, b, …)`, `@f(a, b, …)`, or an application of any expression —
    /// `g(a)(b)`, `(λ x => x)(3)`. Kept **n-ary rather than curried** so that
    /// implicit-argument insertion, which needs the whole argument list at
    /// once, keeps working unchanged (docs/surface-function-types.md §2.2).
    ///
    /// `explicit` (the `@` prefix) suppresses implicit-argument insertion, so
    /// every parameter — including `{}`-implicits — must be given positionally.
    /// It is only ever set on a `Var` head: implicit insertion is
    /// name-directed, so there is nothing for `@` to suppress elsewhere.
    /// `named` holds the `x := e` arguments (docs/named-arguments-design.md).
    /// A **separate list**, not an optional name per element of `args`, and
    /// that is load-bearing three times over: it makes the grammar's
    /// positional-then-named rule (§4.2) *unrepresentable* otherwise, so no
    /// elaborator path has to decide what an interleaving would mean; it
    /// leaves `args.len()` meaning the positional arity that every fragment
    /// recognizer keys on, so a call carrying names simply fails to match a
    /// shape expecting `n` positional arguments (the safe direction); and it
    /// cannot desync, which a parallel `Vec<Option<String>>` could.
    ///
    /// `goal_oriented` records the `apply f; …` spelling. It does not change
    /// ordinary application semantics: the parser lowers the argument bodies
    /// to this same n-ary node so expected-type and cross-argument inference
    /// remain shared. Keeping the bit is what lets later elaboration and
    /// diagnostics distinguish an inference failure at the originating
    /// `apply` from the same failure at an ordinary call.
    ///
    /// `named` is empty for every call written before named arguments existed,
    /// and the elaborator's resolution pass is a no-op when it is empty — a
    /// call with no named argument takes the path it took before, byte for
    /// byte.
    App {
        head: Box<Expr>,
        args: Vec<Expr>,
        named: Vec<NamedArg>,
        explicit: bool,
        goal_oriented: bool,
    },
    /// `f<A, B>` — explicit type application, filling a declaration's leading
    /// type parameters positionally (docs/surface-polymorphism.md §1). Kept
    /// **separate** from `App` rather than a field on it: every existing
    /// construction site of `App` stays untouched, and a type argument is a
    /// `Ty`, not an `Expr`, so it could not share the argument list anyway.
    ///
    /// Also the one form that can spell an *applied* type where an expression
    /// is expected — `@map(List<Nat>, …)` — since a `Ty 0` argument position
    /// reads its expression as a type (§5).
    TyApp { head: Box<Expr>, args: Vec<Ty> },
    /// `λ (x: A) (y: B) => e`, or `fun` for the ASCII spelling. Multiple
    /// binders are sugar for nesting.
    Lam { binders: Vec<LamBinder>, body: Box<Expr> },
    /// `[a, b, c]` — an expected-type-directed collection literal.
    /// Checking-only, like `refl`: `List<T>` lowers it through `Cons`/`Nil`,
    /// while `[T; k]` lowers it to the primitive vector representation.
    CollectionLit(Vec<Expr>),
    /// `a = b` — the identity type, as an **expression**. A type is an
    /// expression whose type is a universe, so with `Type<n>` writable there
    /// is no reason for the equality former to live only in `TyKind`
    /// (docs/surface-universe.md §13). This is what lets a motive be an
    /// ordinary [`ExprKind::Lam`]: `λ z => acc + z = n`.
    ///
    /// Non-associative and loosest-binding, and **suppressed** in the two
    /// contexts that use `=` as punctuation — `calc` steps and, once it has
    /// parsed its left endpoint, `ty_atom`.
    Eq(Box<Expr>, Box<Expr>),
    /// A **type written in type syntax** where an expression node is needed.
    ///
    /// Produced in two ways.
    ///
    /// 1. A motive body (`match … as λ z => T`, `j(p, λ y q => T, …)`), whose
    ///    body is a type by construction — `motive_lam` in the elaborator reads
    ///    it back out.
    /// 2. A **function type in expression position** — `Parser::expr`'s arrow
    ///    fall-through (`docs/types-as-expressions.md`). `(x: A) -> B` and
    ///    `A -> B` are expressions whose type is a universe, which is what
    ///    makes a type-valued `fn` an ordinary `fn`.
    ///
    /// Reading (2) is why (1) can be stated at all: a motive body may be a
    /// *function* type, e.g. the IH-generalizing `λ z => (env: Val) -> … ->
    /// P(z)` (`issues/ih-generalization.md`).
    TyLit(Box<Ty>),
    /// `refl` — checking-only.
    Refl,
    /// The result the parser puts in an **empty** proof block, `{}`
    /// (issues/auto-refl-empty-block.md). Not writable: it exists so that a
    /// `Block` still has a result and every consumer of one is unchanged.
    ///
    /// Checking-only, and deliberately one node wide: in checking position it
    /// gets ONE speculative `refl` attempt, kept iff the kernel accepts the
    /// two endpoints as convertible, and otherwise it raises the same goal a
    /// `?` would. `refl` itself is untouched — the empty block is the whole
    /// trigger, which is [[surface-proof-automation]]'s conservative reading.
    AutoRefl,
    /// `?name` or `?` — a goal: a deferred obligation, discharged by an `on`
    /// statement later in the same block. Checking-only, like `refl`: a hole
    /// with no expected type has no statement to list.
    Hole(Option<String>),
    /// `match (h :)? scrut (as λ bind => motive)? { C(x, …) => body, … }` — one
    /// arm per constructor of the scrutinee's type, in any order. On `Nat` the
    /// arms are `Zero` and `Succ(k)` (or the low-level `Succ(k, ih)`); on a
    /// declared inductive they are its constructors.
    ///
    /// Also the node a `split e; on C(x⃗) := b;` block desugars to — `split` is
    /// a *statement-position spelling* of this expression and not a second
    /// elimination mechanism, so the parser builds one of these and nothing
    /// downstream can tell (docs/match-equation-split-design.md §6).
    Match {
        /// Which spelling this node was written as
        /// (issues/diagnostics-name-the-written-form.md). Read by
        /// **diagnostics only** — every message that has to name a form asks
        /// this instead of saying `match`.
        ///
        /// This does not weaken §6's tautology. What that section buys is that
        /// `split` lowers to the same *elimination*, and the elimination is
        /// built from `scrut`/`eqbind`/`motive`/`arms`; nothing that computes
        /// a term may consult this field, which is why it carries a keyword
        /// and not a variant of behaviour.
        form: MatchForm,
        /// Whether the **pattern compiler** built this node rather than a
        /// writer (`docs/nested-match-patterns-design.md` §3.3): a level that
        /// stands for a pattern *column*, with machine binders and possibly a
        /// `_` arm the compiler itself supplied.
        ///
        /// Read by **diagnostics only**, and for one reason
        /// (`docs/diagnostic-warnings-design.md` §7.1): a warning about an
        /// unreachable arm is a statement about what somebody *wrote*, and a
        /// generated level's arms were written by us. Reachability for the
        /// written arms is complete without it — one compilation's census
        /// spans every level it emits — so this only ever silences a report
        /// about our own arms, never suppresses one about the user's.
        generated: bool,
        scrut: Box<Expr>,
        /// `match h : e { … }` — the convoy, written by the elaborator: the
        /// motive gains `Id(S, e, z) ->` and each arm gains a binder
        /// `h : e = pat` (docs/match-equation-split-design.md §3). Direction is
        /// **scrutinee = pattern**, which is the direction the one live
        /// consumer wants (§3.2). Refused on an indexed family, where it would
        /// be heterogeneous (§4).
        eqbind: Option<String>,
        /// Explicit dependent motive, as a **lambda**: `as λ z => T`. A motive
        /// is a function from the scrutinee to a type, so with `Type<n>`
        /// writable it can simply *be* one, and the surface keeps a single
        /// binder form (docs/surface-universe.md §13). Retired with this: the
        /// bespoke `as z -> T`, which overloaded `->`.
        motive: Option<Box<Expr>>,
        arms: Vec<Arm>,
    },
    /// `match code e as T { zero => …, succ(t) => …, _ => … }` — intensional
    /// analysis of code by the kernel's code recursor
    /// (docs/certgen-transcriber-in-language-design.md §3).
    ///
    /// Three things distinguish it from [`ExprKind::Match`], and all three are
    /// what make a 65-branch elimination writable at all:
    ///
    /// - the motive is a **constant type**, not a lambda: a motive that
    ///   mentioned the scrutinee, its context or its level would give the
    ///   branches 56 different expected types and would put the recursive
    ///   results of the `lam`/`elim_nat` branches at *extended* contexts,
    ///   where nothing can bring them back down;
    /// - an arm binds only the branch's recursive-call results, positionally;
    /// - the arms are keyed to `heather_kernel::rec::BRANCH_NAMES`, and the
    ///   mandatory default arm stands for every branch not written.
    MatchCode { scrut: Box<Expr>, motive: Box<Ty>, arms: Vec<Arm> },
    /// `p.f` (`args: None`), `p.f(a, b)` (`args: Some`), or
    /// `p.f<T, …>(a, b)` (`tyargs` non-empty)
    /// (docs/surface-records.md §4).
    ///
    /// **Resolved in the elaborator, not here.** Until records existed, `.`
    /// was a parser desugaring — `p.f(a)` became `f(a, p)`, a call to a
    /// *global* with the receiver last — which is backwards for a record of
    /// functions, where `m.op(x)` must mean `(m.op)(x)`. Deciding between the
    /// two needs the receiver's type, so it cannot happen here. The old
    /// desugaring survives as the fallback for every non-field name, which is
    /// what keeps `p.sym()`, `p.inj(1)` and `xs.map(f)` working unchanged.
    Dot {
        recv: Box<Expr>,
        name: String,
        tyargs: Vec<Ty>,
        args: Option<Vec<Expr>>,
        named: Vec<NamedArg>,
    },
    /// `xs[i]` — indexing a vector at a `Fin` index
    /// (docs/surface-fin-indexing-design.md §5). A **postfix** form, produced
    /// in `postfix`'s loop beside `Dot` and the call `(`, so `[1,2,3][0]` and
    /// `xs[i].foo` chain in the order written. Both prefix readings of `[` —
    /// `[T; n]` in type position, a collection literal in expression position —
    /// are unaffected: `[` is disambiguated by position, never by lookahead.
    Index { recv: Box<Expr>, idx: Box<Expr> },
    /// `D { f: e, … }` or `D<T, …> { f: e, … }` — a record literal
    /// (docs/surface-records.md §6). Fields may be written in any order; they
    /// are permuted into declaration order in front of the ordinary tier-0
    /// constructor path, which is what actually elaborates.
    RecordLit { name: String, tyargs: Vec<Ty>, fields: Vec<RecordLitField> },
    /// `base with { f = e, … }` — functional record update
    /// (issues/record-update-syntax.md): the record's constructor over
    /// `base`'s projections, with the written fields replaced. The elaborator
    /// knows the declaration, so it reports an unknown or repeated field, and
    /// refuses a dependent record whose kept field's type mentions a replaced
    /// one.
    RecordUpdate { base: Box<Expr>, fields: Vec<RecordLitField> },
    /// `{ let x = e; … result }` — a **block in expression position**
    /// (docs/let-and-blocks-design.md §4).
    ///
    /// Disambiguated from the record literal `D { … }` **by position, never by
    /// lookahead**, exactly as [`ExprKind::Index`]'s `[` is: a record literal
    /// is *postfix* on a name head and is constructed only after an expression
    /// has been parsed, while a prefix `{` in expression position was a parse
    /// error in every production before this node existed. A `{` where a
    /// *statement* is expected is a declaration body or an arm list and is
    /// reached by `block()`/`match_expr` directly, never through `atom`.
    ///
    /// Reuses [`Block`] rather than minting a second node, so the parser
    /// shares `block_body` verbatim and the elaborator shares the alias loop —
    /// a declaration body and a block expression cannot drift in what a `let`
    /// means. The `ons` field is **parsed and then rejected**
    /// (`InductiveDecl::valparams` is the same house style): an arm-level `on`
    /// would mint a nested goal scope, and `goal_base`/`frozen`/
    /// `strengthen_global` are all declaration-scoped
    /// (issues/nested-goal-discharge.md). When that issue lands, the field is
    /// already here and only the elaborator changes.
    Block(Box<crate::ast::Block>),
    /// `code { e }` — a quotation (docs/in-language-map-design.md §3).
    /// Checking-only, mirroring the kernel's `BoxTm` (`NotInferable` by
    /// design): the expected `Code(g |- T)` supplies the payload's context
    /// and type. Splices inside hoist letboxes at this boundary.
    Quote(Box<Expr>),
    /// `$x` / `${e}` — a splice inside a quote payload: meta-level code,
    /// used at its unboxing. `$x` for a `Code`-typed name and `${e}` for a
    /// compound are one node; the distinction is elaboration bookkeeping,
    /// not meaning (surface-v0 §4).
    Splice(Box<Expr>),
    /// `j(proof, λ y p => M, case)` — based path induction. `proof`'s type
    /// fixes the endpoint and family; `M` is scoped over `y` (right endpoint)
    /// and `p` (the path).
    J {
        proof: Box<Expr>,
        /// The motive as a **two-binder lambda**: `λ y q => T`, over the
        /// endpoint and the path. Same move as [`ExprKind::Match`]'s
        /// (docs/surface-universe.md §13); retires `(y, q) -> T`.
        motive: Box<Expr>,
        case: Box<Expr>,
    },
}
