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

/// A source file: a sequence of declarations.
#[derive(Debug, Clone)]
pub struct File {
    pub decls: Vec<Decl>,
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
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A name: parameter, `fn`, or `theorem`.
    Var(String),
    /// Numeral literal (desugars to `Zero`/`Succ`).
    Num(u64),
    /// `f(a, b, …)` or `@f(a, b, …)`; the head is a name (stage 1).
    /// `explicit` (the `@` prefix) suppresses implicit-argument insertion, so
    /// every parameter — including `{}`-implicits — must be given positionally.
    Call { name: String, args: Vec<Expr>, explicit: bool },
    /// `refl` — checking-only.
    Refl,
    /// `?name` or `?` — a goal: a deferred obligation, discharged by an `on`
    /// statement later in the same block. Checking-only, like `refl`: a hole
    /// with no expected type has no statement to list.
    Hole(Option<String>),
    /// `match scrut (as bind -> motive)? { Zero => zero, Succ(k) => succ }`,
    /// or with the low-level explicit-ih arm `Succ(k, ih) => succ`.
    Match {
        scrut: Box<Expr>,
        /// Explicit dependent motive: `(binder name, motive type)`.
        motive: Option<(String, Box<Ty>)>,
        zero: Box<Expr>,
        /// `(predecessor name, ih name, arm body)`. The ih name is `None` in
        /// the unified form `Succ(k)`, where the induction hypothesis is
        /// reached by a structurally guarded *self-call* instead of a binder
        /// (issues/match-recursion.md).
        succ: (String, Option<String>, Box<Expr>),
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
