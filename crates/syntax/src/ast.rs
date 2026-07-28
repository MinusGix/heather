//! The surface AST. Names, not de Bruijn; nothing here is trusted.

/// Byte range into the source, for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

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
}

impl Item {
    /// The `fn`/`theorem` declaration, panicking otherwise. For tests and
    /// callers that have just constructed the item.
    pub fn into_decl(self) -> Decl {
        match self {
            Item::Decl(d) => d,
            Item::Inductive(i) => panic!("expected a declaration, found `inductive {}`", i.name),
        }
    }
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
    pub ctors: Vec<CtorDecl>,
    /// Written `record D<…> { f: T, … }` — one constructor, named after the
    /// declaration, every field named (docs/surface-records.md §2). The
    /// *lowering* is the ordinary tier-0 one; this flag is what earns the
    /// extra surface checks (non-recursive, distinct field names) and the
    /// accessor table.
    pub is_record: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CtorDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

/// One constructor field. A *named* field (`Some(n: Nat, p: n = n)`) is in
/// scope in the types of the fields after it — that dependency is the reason
/// the encoding's field spine is a Σ and not a product.
#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: Option<String>,
    pub ty: Ty,
    pub span: Span,
}

/// `fn name(params) -> T { body }` (computing definition, inlined) or
/// `theorem name(params): T { proof }` (opaque, becomes a Ψ-global).
#[derive(Debug, Clone)]
pub struct Decl {
    pub kind: DeclKind,
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
    pub body: Block,
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
    Let { name: String, ty: Option<Ty>, expr: Expr, span: Span },
    /// `let { unit, op } = m;` — record destructuring
    /// (docs/surface-records.md §5). Each name is bound to its projection, so
    /// this is sugar over [`ExprKind::Dot`] and shares its code. Partial
    /// patterns are allowed: an unmentioned field is simply not bound. No
    /// annotation — the receiver must infer, since it is what names the
    /// fields.
    LetRecord { fields: Vec<(String, Span)>, expr: Expr, span: Span },
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Fn,
    Theorem,
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
    pub span: Span,
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
    /// `(x: A) -> B` (dependent) or `A -> B` (`binder: None`).
    /// Right-associative; one binder per parenthesis group, so `(x: A) (y: B)
    /// -> C` is written `(x: A) -> (y: B) -> C`
    /// (docs/surface-function-types.md §1.1).
    ///
    /// Binders are always *explicit*: implicitness lives in the elaborator's
    /// per-declaration `ParamMeta`, not in the kernel's `Type::Pi`, so there
    /// is nowhere in a function type to record it
    /// (issues/implicit-binders-in-function-types.md).
    Fn { binder: Option<String>, dom: Box<Ty>, cod: Box<Ty> },
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

/// One lambda binder: `x` or `(x: A)`. An unannotated binder is only usable
/// in checking position, where the expected Π supplies the domain.
#[derive(Debug, Clone)]
pub struct LamBinder {
    pub name: String,
    pub ty: Option<Ty>,
    pub span: Span,
}

/// One `match` arm: `C(x, y) => body`. The binders are the constructor's
/// fields, positionally. `Succ(k, ih)` on `Nat` is the one place a second
/// binder is *not* a field: it is the explicit induction hypothesis, kept as
/// a low-level fallback (issues/match-recursion.md).
#[derive(Debug, Clone)]
pub struct Arm {
    pub ctor: String,
    pub binders: Vec<String>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    /// `f(a, b)` with a *name* at the head — the shape every name-keyed
    /// special form wants (`absurd`, `inj`, constructors, `Succ`, a self-call,
    /// and implicit-argument insertion, which is name-directed). Returns
    /// `None` for an application of anything else.
    pub fn as_named(&self) -> Option<(&str, &[Expr], bool)> {
        match &self.kind {
            ExprKind::App { head, args, explicit } => match &head.kind {
                ExprKind::Var(name) => Some((name.as_str(), args.as_slice(), *explicit)),
                _ => None,
            },
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A name: parameter, `fn`, or `theorem`.
    Var(String),
    /// `Type<n>` where a *term* is expected — the code `TmTy(n) : Ty (n+1)`.
    /// A universe is a type, so it is spellable in both positions; this is the
    /// expression one, and it infers rather than needing the `Expr`/`Ty`
    /// bridge (docs/surface-universe.md §4).
    Univ { level: u64 },
    /// Numeral literal (desugars to `Zero`/`Succ`).
    Num(u64),
    /// `f(a, b, …)`, `@f(a, b, …)`, or an application of any expression —
    /// `g(a)(b)`, `(λ x => x)(3)`. Kept **n-ary rather than curried** so that
    /// implicit-argument insertion, which needs the whole argument list at
    /// once, keeps working unchanged (docs/surface-function-types.md §2.2).
    ///
    /// `explicit` (the `@` prefix) suppresses implicit-argument insertion, so
    /// every parameter — including `{}`-implicits — must be given positionally.
    /// It is only ever set on a `Var` head: implicit insertion is
    /// name-directed, so there is nothing for `@` to suppress elsewhere.
    App { head: Box<Expr>, args: Vec<Expr>, explicit: bool },
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
    /// `[a, b, c]` — a vector literal. Checking-only, like `refl`: the
    /// expected `[T; k]` supplies both the element type and the length, and
    /// the length must be a literal (docs/container-fields.md §2.2).
    VecLit(Vec<Expr>),
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
    /// `refl` — checking-only.
    Refl,
    /// `?name` or `?` — a goal: a deferred obligation, discharged by an `on`
    /// statement later in the same block. Checking-only, like `refl`: a hole
    /// with no expected type has no statement to list.
    Hole(Option<String>),
    /// `match scrut (as λ bind => motive)? { C(x, …) => body, … }` — one arm per
    /// constructor of the scrutinee's type, in any order. On `Nat` the arms
    /// are `Zero` and `Succ(k)` (or the low-level `Succ(k, ih)`); on a
    /// declared inductive they are its constructors.
    Match {
        scrut: Box<Expr>,
        /// Explicit dependent motive, as a **lambda**: `as λ z => T`. A motive
        /// is a function from the scrutinee to a type, so with `Type<n>`
        /// writable it can simply *be* one, and the surface keeps a single
        /// binder form (docs/surface-universe.md §13). Retired with this: the
        /// bespoke `as z -> T`, which overloaded `->`.
        motive: Option<Box<Expr>>,
        arms: Vec<Arm>,
    },
    /// `p.f` (`args: None`) or `p.f(a, b)` (`args: Some`)
    /// (docs/surface-records.md §4).
    ///
    /// **Resolved in the elaborator, not here.** Until records existed, `.`
    /// was a parser desugaring — `p.f(a)` became `f(a, p)`, a call to a
    /// *global* with the receiver last — which is backwards for a record of
    /// functions, where `m.op(x)` must mean `(m.op)(x)`. Deciding between the
    /// two needs the receiver's type, so it cannot happen here. The old
    /// desugaring survives as the fallback for every non-field name, which is
    /// what keeps `p.sym()`, `p.inj(1)` and `xs.map(f)` working unchanged.
    Dot { recv: Box<Expr>, name: String, args: Option<Vec<Expr>> },
    /// `D { f: e, … }` or `D<T, …> { f: e, … }` — a record literal
    /// (docs/surface-records.md §6). Fields may be written in any order; they
    /// are permuted into declaration order in front of the ordinary tier-0
    /// constructor path, which is what actually elaborates.
    RecordLit { name: String, tyargs: Vec<Ty>, fields: Vec<RecordLitField> },
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
