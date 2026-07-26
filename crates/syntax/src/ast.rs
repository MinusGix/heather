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
    pub params: Vec<Param>,
    /// Return type of a `fn`, statement of a `theorem`.
    pub result: Ty,
    pub body: Block,
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
    /// A declared inductive, applied to its type arguments (`Bool`,
    /// `Option<Nat>`), or a type parameter in scope inside an `inductive`.
    Named { name: String, args: Vec<Ty> },
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
    /// `λ (x: A) (y: B) => e`, or `fun` for the ASCII spelling. Multiple
    /// binders are sugar for nesting.
    Lam { binders: Vec<LamBinder>, body: Box<Expr> },
    /// `refl` — checking-only.
    Refl,
    /// `?name` or `?` — a goal: a deferred obligation, discharged by an `on`
    /// statement later in the same block. Checking-only, like `refl`: a hole
    /// with no expected type has no statement to list.
    Hole(Option<String>),
    /// `match scrut (as bind -> motive)? { C(x, …) => body, … }` — one arm per
    /// constructor of the scrutinee's type, in any order. On `Nat` the arms
    /// are `Zero` and `Succ(k)` (or the low-level `Succ(k, ih)`); on a
    /// declared inductive they are its constructors.
    Match {
        scrut: Box<Expr>,
        /// Explicit dependent motive: `(binder name, motive type)`.
        motive: Option<(String, Box<Ty>)>,
        arms: Vec<Arm>,
    },
    /// `j(proof, (y, p) -> M, case)` — based path induction. `proof`'s type
    /// fixes the endpoint and family; `M` is scoped over `y` (right endpoint)
    /// and `p` (the path).
    J {
        proof: Box<Expr>,
        y: String,
        p: String,
        motive: Box<Ty>,
        case: Box<Expr>,
    },
}
