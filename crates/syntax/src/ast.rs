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
    pub body: Expr,
    pub span: Span,
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
    pub span: Span,
}

/// Surface types. `a == b` is the identity type at the (synthesized) type
/// of `a`.
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
    /// `Succ(e)` — builtin constructor (also reachable as `Call`).
    /// `f(a, b, …)`; the head is a name (stage 1).
    Call(String, Vec<Expr>),
    /// `refl` — checking-only.
    Refl,
    /// `match scrut (as bind -> motive)? { Zero => zero, Succ(k, ih) => succ }`
    Match {
        scrut: Box<Expr>,
        /// Explicit dependent motive: `(binder name, motive type)`.
        motive: Option<(String, Box<Ty>)>,
        zero: Box<Expr>,
        /// `(predecessor name, ih name, arm body)`.
        succ: (String, String, Box<Expr>),
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
