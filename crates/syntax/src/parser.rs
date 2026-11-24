//! Recursive-descent parser for the stage-1 grammar.
//!
//! ```text
//! file    := item*
//! item    := decl | inductive | record | class | instance | assuming | section
//! assuming := "assuming" requirement ("," requirement)* "{" item* "}"
//! section := "section" typarams? requires? params? "{" (fn | theorem | section)* "}"
//! requirement := (name ":")? type
//! decl    := "fn" name tyvars? "(" params? ")" "->" type block
//!          | "theorem" name tyvars? "(" params? ")" ":" type block
//! tyvars  := "<" tyvar ("," tyvar)* ">"
//! tyvar   := name (":" annot)?                       -- default `Type<0>`
//! annot   := univ ("+" constr)* | constr ("+" constr)*
//! constr  := name ("<" type ("," type)* ">")?  -- `A: C<X>` is `C<A, X>`
//! univ    := "Type" ("<" numeral ">")?
//! induct  := "inductive" name tyvars? "{" ctors? "}"
//! codata  := "codata" name tyvars? vparams? "{" ctors? "}"
//!                                     -- a coinductive declaration
//!                                     (docs/inductives/codata-elaborator-design.md)
//! record  := "record" name tyvars? "{" rfield ("," rfield)* ","? "}"
//! rfield  := name ":" type            -- a record field is always named
//! class   := "class" name tyvars? ("extends" cref ("as" name)? ("," cref ("as" name)?)*)?
//!            "{" rfield ("," rfield)* ","? "}"
//! cref    := name "<" type ("," type)* ">"
//! inst    := "instance" tyvars? vparams? cref
//!            ("requires" ibind ("," ibind)*)?
//!                                     -- vparams: the instance's VALUE binders
//!                                     (docs/language/classes/value-generic-instances-design.md)
//! impl    := "impl" name "for" name "{" dclause ("," dclause)* ","? "}"
//!                                     -- one entry of the cost basis (§1.2)
//! drepr   := "datarepr" name "for" type
//!            ( ":=" expr ";"? | "{" dclause ("," dclause)* ","? "}" )
//!                                     -- a certified runtime representation
//!                                     (docs/native/datarepr-design.md §1.4)
//! dclause := "mk"? name ":=" expr     -- `mk C := …` is C's image
//! desig   := "designation" "prefix"? tyvars? OP "at" type ":=" expr
//!                                     -- what a symbol means at a carrier
//!                                     (docs/language/classes/operators-onto-classes-design.md)
//! decl    := ("fn"|"theorem") name tyvars? ("requires" ibind ("," ibind)*)?
//!            "(" param* ")" …          -- param := … (":=" ("infer" | expr))?
//!            "{" (decl* | ifield ("," ifield)* ","?) "}"
//! ibind   := name ":" type
//! ifield  := name ":=" expr
//! ctors   := ctor ("," ctor)* ","?
//! ctor    := name ("(" field ("," field)* ","? ")")?
//! field   := (name ":")? type
//! params  := param ("," param)* ","?
//! param   := names ":" type | "{" names ":" type "}" -- implicit
//! names   := name ("," name)*   -- a run shares ONE annotation; a modifier
//!                                  (`self x`) still prefixes a single name
//! type    := "(" bgroup ("," bgroup)* ")" "->" type  -- dependent function,
//!                                     a telescope: a later binder's type may
//!                                     mention an earlier binder
//!          | "{" bgroup ("," bgroup)* "}" "->" type  -- implicit binders
//!          | tyatom "->" type                        -- right-associative
//!          | tyatom
//! bgroup  := names ":" type   -- `(x, y: A, z: B)` is three binders, and
//!                                desugars to the curried chain (`curry`)
//! tyatom  := univ                                    -- Type, Type<n>
//!          | "[" type ";" expr "]"                   -- length-indexed vector
//!          | name ("<" type ("," type)* ">")         -- applied inductive
//!          | cmp                    -- bare `Nat`/`Bool` is that type
//!          | "(" type ")"
//! cmp     := expr (("=" | "<=" | "<") expr)?   -- ONE non-associative rung:
//!                                      `=` is propositional equality (`==`
//!                                      rejected), `<=` is `Le(a, b)`, `<` is
//!                                      `lt(a, b)`; none of them chain
//! block   := "{" stmt* ((expr | split) on_stmt* | goal_combinators) "}"
//! stmt    := "let" name (":" type)? "=" expr ";"
//!          | "let" "{" name ("," name)* ","? "}" "=" expr ";"   -- destructure
//! split   := "split" (name ":")? expr ("as" expr)? ";"   -- IS the result
//! goal_combinators := "split_all" ";" "all_goals" block
//! on_stmt := "on" ("?" name ("." numeral)? | "_" ":" type) ":=" expr ";"
//!          | "on" name ("(" name ("," name)* ")")? ":=" expr ";"  -- split arm
//! expr    := "match" (name ":")? expr ("as" expr)? "{" arms "}"
//!          | "if" (name ":")? expr "{" block-body "}"
//!                 "else" "{" block-body "}"
//!          | "if" "let" (name ":")? pat-head "=" expr
//!                 "{" block-body "}" "else" "{" block-body "}"
//!          | "refl" | "?" name?
//!          | "j" "(" expr "," "(" name "," name ")" "->" type "," expr ")"
//!          | ("λ"|"fun") binder+ "=>" expr
//!          | "@" name ("<" type ("," type)* ">")? "(" args ")"
//!          | atom ("<" type ("," type)* ">")?     -- explicit type application
//!                 ("{" (name ":" expr)* "}")?     -- record literal
//!                 (("." name ("(" args ")")?) | "(" args ")")*   -- postfix
//!          | "[" (expr ("," expr)*)? "]"           -- collection literal
//!          | "{" stmt* expr "}"                    -- block, PREFIX `{` only
//!          | name | numeral | "(" expr ")"
//! binder  := name | "(" name ":" type ")"
//! arms    := arm ("," arm)* ","?    -- one per constructor, any order
//! arm     := name ("(" name ("," name)* ")")? "=>" expr
//! ```
//!
//! `on` discharges are trailing: order-free among themselves, but after the
//! result expression (issues/goal-holes.md). `let`/`on` are contextual
//! keywords like every other keyword here — an expression can never be
//! *continued* by a bare identifier, so a statement head is unambiguous.
//!
//! `split` is the one statement head that sits where a *result expression*
//! could start, so it cannot be bought back by lookahead (nothing fixed
//! follows it) and is instead rejected as a binding name, like `match`/`fun`/
//! `if`/`Type` — rule 3 of docs/language/let-and-blocks-design.md §5.2. A block that splits
//! has no result expression: the arms are the result, and the `on Ctor(…)`
//! heads after it are those arms rather than goal discharges
//! (docs/language/matching/match-equation-split-design.md §5). Both `split` and `match` take the
//! optional `h :` equation binder (§3), which is exact on two tokens because
//! `:` never continues an expression.

use crate::ast::*;
use crate::lexer::{lex, lex_while, Tok, TokKind};

#[derive(Debug, Clone)]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
}

/// A class reference *as a type*. Unindexed it is the ordinary applied name;
/// indexed it is the applied spelling a value-parameterized record already has
/// (`docs/language/surface-value-parameters.md` §3) — `Monoid<A>(op)` reaching the
/// elaborator as [`TyKind::OfExpr`], the same road `Converges(p, env, …)`
/// travels. There is no second encoding, which is
/// `docs/language/classes/operation-indexed-classes-design.md` §2.1 in one function.
pub fn class_ty(name: String, args: Vec<Ty>, index: Vec<Expr>, span: Span) -> Ty {
    if index.is_empty() {
        return Ty { kind: TyKind::Named { name, args }, span };
    }
    let head = Expr { kind: ExprKind::Var(name), span };
    let head = if args.is_empty() {
        head
    } else {
        Expr { kind: ExprKind::TyApp { head: Box::new(head), args }, span }
    };
    let applied = Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args: index,
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    };
    Ty { kind: TyKind::OfExpr(Box::new(applied)), span }
}

pub fn parse_file(src: &str) -> Result<File, ParseError> {
    let toks = lex(src).map_err(|e| ParseError { msg: e.msg, span: e.span })?;
    let mut p = Parser::over(toks);
    let mut items = Vec::new();
    // Imports come first, all of them (docs/language/modules-design.md §3.1). The
    // position rule is enforced here rather than in the elaborator because it
    // is what lets a tool read a file's import DAG without parsing bodies.
    let mut seen_decl = false;
    while !p.at_eof() {
        for item in p.items()? {
            match &item {
                Item::Import(i) if seen_decl => {
                    return Err(ParseError {
                        msg: format!("`{}` must come before the first declaration", if i.reexport { "export" } else { "import" }),
                        span: i.span,
                    })
                }
                Item::Import(_) => {}
                _ => seen_decl = true,
            }
            items.push(item);
        }
    }
    Ok(File { items, section_typarams: p.section_typarams })
}

/// The imports a source opens with, read without lexing or parsing anything
/// after them. Imports come first (the rule [`parse_file`] enforces), so in a
/// source that parses these are all of its imports: the import DAG of a
/// closure is read at the cost of its import lines, not of its bodies.
///
/// The reading ends at the first item that is not an import, and at an import
/// that does not lex or parse; whatever is wrong there or later is
/// `parse_file`'s to report. A source that does not parse therefore still has the imports it
/// opens with.
pub fn leading_imports(src: &str) -> Vec<ImportItem> {
    // An import holds one `;`, its last token, so until the first other item
    // a token opens an item exactly when it is the first or follows a `;`.
    let mut opens_item = true;
    let toks = lex_while(src, |tok| {
        let goes_on = !opens_item || matches!(&tok.kind, TokKind::Ident(k) if k == "import" || k == "export");
        opens_item = matches!(tok.kind, TokKind::Semi);
        goes_on
    });
    let mut p = Parser::over(toks);
    let mut imports = Vec::new();
    while p.at_kw("import") || p.at_kw("export") {
        let Ok(import) = p.import() else { break };
        imports.push(import);
    }
    imports
}

/// The first segments of the paths a source writes, `m` of `m::x`: the
/// lower-case first segment of every qualified name (the lexer reads
/// `m::T::x` as one identifier) that no `.` or `::` precedes, in order of
/// first appearance. A module named so is loaded for the source without an
/// import, visible qualified only (docs/language/modules-design.md §3.8); a
/// name that is no module (a function's `f::rec`, a local's) is the caller's
/// to drop. Read from the tokens, so a comment or a string never names one,
/// and a source that does not lex names the paths before the point it stops.
pub fn written_paths(src: &str) -> Vec<String> {
    let toks = crate::lexer::lex_while(src, |_| true);
    let mut out: Vec<String> = Vec::new();
    for (i, tok) in toks.iter().enumerate() {
        let TokKind::Ident(text) = &tok.kind else { continue };
        let Some((head, _)) = text.split_once("::") else { continue };
        if i > 0 && matches!(toks[i - 1].kind, TokKind::ColonColon | TokKind::Dot) {
            continue;
        }
        if !head.starts_with(|c: char| c.is_ascii_lowercase()) || out.iter().any(|m| m == head) {
            continue;
        }
        out.push(head.to_string());
    }
    out
}

/// One `section`'s head, split as [`Parser::splice_sections`] splices it.
struct SectionHead {
    tyvars: Vec<TyParam>,
    solver: Vec<Param>,
    written: Vec<Param>,
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    /// The heads of the `section`s enclosing the current position, outermost
    /// first ([`Parser::section_items`]).
    sections: Vec<SectionHead>,
    /// [`File::section_typarams`], as each section head is parsed.
    section_typarams: Vec<(Span, Span, Span)>,
    /// The evidence rules a record's `Pos<A>` fields declare, emitted as the
    /// items after the record ([`Parser::record`]).
    record_facts: Vec<Decl>,
    /// Avoid a lowering walk for declarations and lambdas without postfix `?`.
    propagation_count: usize,
    /// Ordinary function/lambda bodies admit propagation; signatures do not.
    propagation_depth: usize,
    /// The expression being parsed heads a block statement, so an `if` there
    /// may omit its `else` (docs/language/sequencing-surface-design.md §4). Taken by
    /// the `if` it reaches first, so nothing nested inherits it.
    elseless_if: bool,
    /// The names the `on` discharges at the head of the declaration body
    /// being read mention: an `if h: P` whose branches never name `h` binds
    /// its evidence anyway when one of them does, since the obligation it
    /// discharges is raised inside the branch (`if h: 0 < n { f(n - 1) }`
    /// with `on ?dec1 := { … h … }`).
    body_on_names: Vec<String>,
    /// `mut x: T` and `mut self x: T` parameters of the parameter list just
    /// read, by name, with whether each is the receiver
    /// (docs/language/sequencing-surface-design.md §8.2). Taken by [`Parser::decl`].
    mut_params: Vec<(String, bool)>,
    /// The `mut` parameters the next block opened is the body of: it binds
    /// each as a `let mut` local, and a `mut self` one is returned beside the
    /// result. Taken by the first [`Parser::block_body`].
    pending_mut: Option<Vec<(String, bool)>>,
    /// The next block is a function's body, where `return` may stand outside
    /// any loop (docs/language/sequencing-surface-design.md §5.5).
    fn_body: bool,
    /// The method whose body is being read, by its base name, when it is a
    /// `mut self` one: a call of that name on the receiver that ends the
    /// body is the method's own ([`Parser::receiver_end`]).
    own_method: Option<String>,
    /// The next block opened is the body of a `while` with no measure
    /// (docs/language/sequencing-surface-design.md §18): its binds stay as markers
    /// until the loop is lowered, because they run inside the loop's step,
    /// after the locals it threads are known. Taken by the first
    /// [`Parser::block_body`].
    defer_binds: bool,
    /// The `let mut` locals and `mut` parameters lexically in scope, innermost
    /// last: a method call on one of them may update it, so the parser marks
    /// it a candidate ([`crate::imperative::MUTCALL`]) for the scope that
    /// declared the local to claim.
    mutables: Vec<String>,
    /// Parsing a `for` header, where `a..b` is a range (§5.2).
    range_header: bool,
    /// Inside a `record`'s value-parameter list, where `self t: T` marks the
    /// receiver (issues/record-in-type-namespace.md).
    record_self: bool,
    /// Suppress the record literal `D { … }` (docs/language/surface-records.md §6.1).
    ///
    /// `{` after an expression is ambiguous exactly where a *block* follows
    /// one: `match m { … }` would otherwise read `m { … }` as a literal. Rust
    /// has the same problem and the same fix — the restriction is set for the
    /// scrutinee and the block-preceding types, and **lifted inside any
    /// bracket**, so `match f(D { x: 1 }) { … }` is fine and a literal that
    /// really is wanted in scrutinee position is parenthesised.
    no_record_lit: bool,
    /// Suppress the whole **comparison level** — `a = b`, `a <= b`, `a < b` —
    /// as an *expression* (docs/language/surface-universe.md §13).
    ///
    /// `=` is loosest-binding and non-associative, which is right everywhere
    /// except the contexts that use it as punctuation: a `calc` step
    /// (`e0 = e1 := p`) reads its endpoints with `=` as the separator,
    /// [`Parser::ty_atom`] must not re-consume the `=` it is about to inspect,
    /// and an annotated `let`'s type must stop before the binder `=`
    /// (docs/language/let-and-blocks-design.md §3). Same shape as `no_record_lit`: set
    /// in the punctuation contexts, and **lifted inside any bracket**, so the
    /// escape hatch is a parenthesis — `let p: (a = b) = pf;`, `a = (b = c)`.
    no_eq: bool,
    /// Inside a binding's annotation (`let`, `have`, `def`): the comparison
    /// rung is suppressed **only at `=`**, so `let k: a <= b = h;` reads its
    /// annotation as `a <= b` (issues/annotated-let-relation-needs-parentheses.md).
    /// Only `=` is ambiguous there — after an annotation the statement wants
    /// its binder `=` (or `<-`), so `<=`, `<`, `≈` and `≠` can only be the
    /// type's own. Meaningful only while [`Parser::no_eq`] is set, and
    /// cleared by every [`Parser::with_eq`], so a comparison's right operand,
    /// a bracket, or any other context that sets `no_eq` for itself is
    /// unaffected.
    annotation_rel: bool,
    /// `P ↔ Q` suppressed, exactly as [`Parser::no_eq`] suppresses `a = b`.
    /// Set while a function type's **codomain** is read, which is what makes
    /// `↔` looser than `->`: without it the codomain's own `ty()` reaches
    /// `expr()` and takes the `↔` for itself, so `P -> Q ↔ Q -> P` parses as
    /// `P -> (Q ↔ (Q -> P))` — right-associativity of the arrow beating a
    /// rung that is supposed to be looser than it.
    ///
    /// Same shape as `no_eq` in the other half too, and that half was missing:
    /// the restriction is **lifted inside any bracket**, so a parenthesis is
    /// the escape hatch — `(a: A) -> (P(a) ↔ Q(a))`, `P -> Or<Q ↔ R, S>`. It
    /// has to be, because the restriction exists only to stop the *codomain's
    /// own spine* from eating the outer `↔`, and a `↔` inside a delimiter is
    /// never that one. Lifted in exactly two places — [`Parser::expr`], for
    /// every expression-side bracket, and [`Parser::ty_atom`], for the
    /// type-side ones (issues/iff-in-type-valued-body.md).
    no_iff: bool,
    /// The next lambda body parsed is a **motive** body, so it is a type and
    /// is parsed with [`Parser::ty`] rather than [`Parser::expr`].
    ///
    /// One-shot: [`Parser::lambda`] takes the flag, so only the motive's own
    /// lambda is affected and a lambda *inside* the motive body is an
    /// ordinary expression lambda. Needed because a motive body may be a
    /// function type — an IH-generalizing motive is
    /// `λ z => (env: Val) -> … -> P(z)` — and `->` is not in the expression
    /// grammar (`issues/ih-generalization.md`). Every type the old grammar
    /// accepted here still parses: [`Parser::ty`] falls through to
    /// [`Parser::expr`] for `a = b`, names and applications.
    motive_body: bool,
    /// File-local supply for names the source language cannot spell. Item
    /// groups flatten, so a per-group index would collide across nested
    /// anonymous `assuming` telescopes.
    next_hygienic: usize,
    /// Positions where a type-argument speculation has already been tried and
    /// **failed** — the memo that keeps speculation linear.
    ///
    /// Two sites speculate on a `<`: [`Parser::try_tyargs`] in the expression
    /// grammar, and the `D<A, B>` branch of [`Parser::ty`]. Each falls back by
    /// rewinding and re-parsing the same tokens the other way, so once *both*
    /// recover they re-enter each other and a failing `A<A<A<…<Nat` re-parses
    /// every prefix at every depth. That is **exponential**: measured at 4× per
    /// two levels, 7 ms at depth 10 and 4.7 s at depth 20.
    /// `docs/language/surface-polymorphism.md` §1 called backtracking "free here", and
    /// it was — but only because the *type* side failed hard and cut the
    /// recursion. Making that side recover (the `Lt` round) removed the cut.
    ///
    /// A failed speculation is a pure function of (position, site, flags), so
    /// remembering it is sound, and it collapses the re-entry to one attempt
    /// per key — packrat memoization over the one nonterminal that needs it.
    /// **Failures only**: a success consumes its tokens and is never retried,
    /// so there is nothing to memo on that side.
    ///
    /// The flags are part of the key because `ty()` reaches the expression
    /// grammar, where all five of them change what parses.
    spec_failed: std::collections::HashSet<(usize, u8)>,
}

type R<T> = Result<T, ParseError>;

/// The two speculating sites on a `<`, as the `site` half of a
/// [`Parser::spec_failed`] key. They must not share: the expression site
/// additionally requires a `(` or a `>` where the type site does not, so the
/// same position can fail for one and succeed for the other.
const SITE_EXPR_TYARGS: u8 = 1 << 4;
const SITE_TY_NAMED: u8 = 1 << 5;
/// The `[T; n]` branch of [`Parser::ty`]: a `[` whose element does not parse
/// as a type followed by `;` is a list literal, read by the expression grammar.
const SITE_TY_VEC: u8 = 1 << 6;

/// A calc step's relation, ordered by strength: composing two steps yields
/// the stronger (`=` < `≈` < `<=` < `<`), which is what the mixed lemmas
/// prove (`<` absorbs `<=`, either order absorbs `≈`, `=` transports).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum CalcRel {
    Eq,
    Same,
    Le,
    Lt,
}

impl CalcRel {
    fn symbol(self) -> &'static str {
        match self {
            CalcRel::Eq => "=",
            CalcRel::Same => "≈",
            CalcRel::Le => "<=",
            CalcRel::Lt => "<",
        }
    }
}

/// `trans(p, q, a := …, b := …, c := …)` — one `calc` step
/// (docs/language/named-arguments-design.md). Separate from [`named_call`] because the
/// endpoints are named rather than positional; see `calc_expr` for why.
fn trans_call(args: Vec<Expr>, named: Vec<(&str, Expr)>, span: Span) -> Expr {
    let head = Expr { kind: ExprKind::Var("trans".to_string()), span };
    let named = named
        .into_iter()
        .map(|(name, expr)| NamedArg {
            name: name.to_string(),
            name_span: span,
            span,
            expr,
        })
        .collect();
    Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args,
            named,
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

/// The owner half of a `<owner>::<member>` path, rendered as it is *printed*
/// (docs/native/repr-access-spellings-design.md §4): `Impl(add, BinNat)`. Only an
/// application of a name to names qualifies, which is v1's one applied owner
/// and is what keeps the rendering total — there is no expression printer
/// here and none is wanted.
fn render_owner(e: &Expr) -> Option<String> {
    let ExprKind::App { head, args, named, explicit: false, .. } = &e.kind else { return None };
    if !named.is_empty() {
        // An owner path is `Impl(add, BinNat)`, a name applied to names. A
        // named argument is not a name, so it does not render — and rendering
        // it as if it were would mint a path string that no `::` lookup and no
        // `heather obligations` line could ever match.
        return None;
    }
    let ExprKind::Var(h) = &head.kind else { return None };
    let mut parts = Vec::with_capacity(args.len());
    for a in args {
        match &a.kind {
            ExprKind::Var(n) => parts.push(n.clone()),
            _ => return None,
        }
    }
    Some(format!("{h}({})", parts.join(", ")))
}

/// `a + b` as an application of the **symbol**
/// (docs/language/classes/operators-onto-classes-design.md §4). The symbol is a name in a
/// namespace of its own, so an operator expression is the ordinary
/// [`ExprKind::App`] it has always been — only its head survives as what was
/// written instead of as what it used to desugar to.
/// A braced block that ends in a statement: the body of a statement form
/// (docs/language/sequencing-surface-design.md §4).
fn is_statement_body(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Block(b) if matches!(&b.result.kind, ExprKind::Var(n) if n == crate::imperative::UNIT)
        || crate::imperative::ends_in_method_call(b))
}

/// `{}`, which elsewhere is an empty proof block (`ExprKind::AutoRefl`).
fn is_empty_body(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Block(b) if b.stmts.is_empty() && matches!(b.result.kind, ExprKind::AutoRefl))
}

/// An `if`/`match` whose bodies are statement bodies: a statement. `{}` is
/// a statement body beside one, so `None => {}` assigns nothing; an
/// `if`/`match` of `{}` alone stays the proof it was.
fn is_statement_form(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Match { arms, .. }
        if arms.iter().any(|a| is_statement_body(&a.body))
            && arms.iter().all(|a| is_statement_body(&a.body) || is_empty_body(&a.body)))
}

/// A statement after which a block may end with no result: an assignment
/// or a statement form.
fn is_imperative_statement(s: &Stmt) -> bool {
    // `break`/`continue` are zero-argument markers; the rest carry one.
    matches!(s, Stmt::Let { expr, .. } if matches!(&expr.kind, ExprKind::App { head, args, .. }
        if matches!(&head.kind, ExprKind::Var(n)
            if (!args.is_empty() && (n == crate::imperative::ASSIGN || n == crate::imperative::STMT
                || n == crate::imperative::FOR || n == crate::imperative::RETURN
                || (n == crate::imperative::MUTCALL && matches!(s, Stmt::Let { name, .. } if name.starts_with("#seq")))))
                || (args.is_empty() && (n == crate::imperative::BREAK || n == crate::imperative::CONTINUE)))))
}

/// The binding power just above `&&` and `||`: an operand read at it holds
/// neither.
const BOOL_CHAIN_BP: u8 = 5;

/// An operand of `&&`/`||` as a `Bool`: a relation (`a < b`, `a ≠ b`) is
/// its decision `decide_bit<a < b>()`; anything else is as written.
fn decided(e: Expr) -> Expr {
    let relation = match &e.kind {
        ExprKind::App { head, args, .. } => match &head.kind {
            ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix } => args.len() == 2 && matches!(symbol.as_str(), "<" | "<=" | "≈"),
            ExprKind::Var(n) => n == "Not" && args.len() == 1 && matches!(args[0].kind, ExprKind::Eq(..)),
            _ => false,
        },
        _ => false,
    };
    if !relation {
        return e;
    }
    let span = e.span;
    Expr {
        kind: ExprKind::App {
            head: Box::new(Expr {
                kind: ExprKind::TyApp { head: Box::new(Expr { kind: ExprKind::Var("decide_bit".into()), span }), args: vec![expr_as_ty(&e)] },
                span,
            }),
            args: vec![],
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

fn op_call(sym: &str, fixity: OpFixity, args: Vec<Expr>, span: Span) -> Expr {
    let head = Expr { kind: ExprKind::OpSymbol { symbol: sym.to_string(), fixity }, span };
    Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args,
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

/// Where an operator symbol sits in the expression grammar: the parser's own
/// precedence, for a printer that spells a resolved operation back as the
/// symbol (issues/diagnostic-operator-resugaring.md) and has to parenthesize
/// what it prints exactly as this parser would read it — by this table, not a
/// second one (issues/notation-extensibility.md).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperatorForm {
    /// An infix rung, as its left and right binding powers
    /// (`Parser::infix_op`): `a op b` folds `op` while its left power is at
    /// least the minimum, and parses the right operand at the right power.
    Infix(u8, u8),
    /// The comparison level, `<=`, `<` and `≈` beside `=`: below every infix
    /// rung, non-associative (`Parser::comparison`).
    Comparison,
    /// `^`: the base a postfix expression, the exponent a prefix one, so it
    /// is right-associative and binds tighter than a prefix operator
    /// (`Parser::power`).
    Power,
    /// `-x`, `!b`, `↑n`: the operand a prefix expression (`Parser::prefix`).
    Prefix,
    /// `x⁻¹`: the operand a postfix expression (`Parser::postfix`).
    Postfix,
}

/// The [`OperatorForm`] of `sym` at `fixity`, or `None` for a symbol the
/// grammar does not read at that fixity.
pub fn operator_form(sym: &str, fixity: OpFixity) -> Option<OperatorForm> {
    match fixity {
        OpFixity::Infix => match sym {
            "<=" | "<" | "≈" => Some(OperatorForm::Comparison),
            "^" => Some(OperatorForm::Power),
            _ => Parser::infix_binding(sym).map(|(l, r)| OperatorForm::Infix(l, r)),
        },
        OpFixity::Prefix => matches!(sym, "-" | "!" | "~" | "↑").then_some(OperatorForm::Prefix),
        OpFixity::Postfix => (sym == "⁻¹").then_some(OperatorForm::Postfix),
    }
}

/// The carrier of `Pos<A>` written as a binder's type: the sugar
/// (docs/library/positivity-evidence-design.md §6 B) is recognised by name, as
/// `Squash<A>` is, so `Pos` with one type argument is reserved there.
pub fn pos_carrier(ty: &Ty) -> Option<&Ty> {
    match &ty.kind {
        TyKind::Named { name, args } if name == "Pos" && args.len() == 1 => Some(&args[0]),
        _ => None,
    }
}

/// The searched fact a `Pos<A>` binder named `name` stands beside: `0 < name`.
pub fn positivity_ty(name: &str, span: Span) -> Ty {
    let zero = Expr { kind: ExprKind::Num(Numeral::ZERO), span };
    let var = Expr { kind: ExprKind::Var(name.to_string()), span };
    let lt = op_call("<", OpFixity::Infix, vec![zero, var], span);
    Ty { kind: TyKind::OfExpr(Box::new(lt)), span }
}

/// The search a `fn f(…) → Pos<A>` body's positivity is proved by:
/// `positivity`, with a failure that says how to prove it by hand
/// (`on ?pos := …;`). Reserved like omega's own `__` branch markers.
/// The prelude record a `mut self` method returns: its receiver after the
/// call, and the call's value (docs/language/sequencing-surface-design.md §8.2).
pub const MUTATED_RECORD: &str = "Mutated";

pub const POS_RESULT: &str = "__pos_result";

/// What fills a `Pos<A>` record field's fact when a construction leaves it
/// out: the search a `:= infer` parameter runs (locals, computation, evidence
/// rules; no omega), over the constructing scope.
pub const POS_SEARCH: &str = "__pos_search";

/// The call head `by t` parses to (docs/metaprogramming/host-elaboration-interface-design.md
/// §7): the elaborator runs `t` as a tactic against the expected type. Not a
/// name a user can write, like [`POS_SEARCH`].
pub const BY_TACTIC: &str = "__by";

/// The name of that fact: `x_pos` beside `x`.
pub fn positivity_name(name: &str) -> String {
    format!("{name}_pos")
}

/// `x_pos: 0 < x := infer`, the parameter a `Pos<A>` binder adds after `x`.
fn positivity_param(name: &str, span: Span) -> Param {
    Param {
        name: positivity_name(name),
        ty: positivity_ty(name, span),
        implicit: true,
        is_self: false,
        solver: Some(Solver::Infer),
        default: None,
        origin: ParamOrigin::Written,
        symbol: None,
        span,
    }
}

/// A binary connective: `P ∧ Q` is `And<P, Q>`, the declared record applied to
/// its two **type** arguments (`lib/std/core/logic.hthr`).
///
/// The target name is fixed here rather than emitted as a symbol for
/// resolution to place, which is the opposite of what `+` does — and the test
/// is [`Parser::op_symbol`]'s own: a connective is a *type former*, like `=`,
/// not an operation a carrier can have. There is nothing for a designation to
/// say about `∧` at a carrier, because its operands are propositions and not
/// values of one.
///
/// [`ExprKind::TyApp`] rather than a [`ExprKind::TyLit`] wrapper: `expr_as_ty`
/// already reads `TyApp` on a name back as [`TyKind::Named`], so the desugared
/// node in *type* position is byte-for-byte the `And<P, Q>` a writer could
/// have typed, and in expression position it is the same node `List<Nat>`
/// produces.
fn connective(name: &str, lhs: Expr, rhs: Expr, span: Span) -> Expr {
    let head = Expr { kind: ExprKind::Var(name.to_string()), span };
    let args = vec![expr_as_ty(&lhs), expr_as_ty(&rhs)];
    Expr { kind: ExprKind::TyApp { head: Box::new(head), args }, span }
}

/// Read an already-parsed expression **as a type**, syntactically and totally.
///
/// The one place the grammar decides what an expression means in type
/// position, shared by `ty_atom`'s fall-through and by `expr`'s arrow
/// domain, so the two cannot drift. Nothing here is a judgement about whether
/// the thing *is* a type: a bare name becomes `TyKind::Named` whether or not a
/// type by that name exists, and everything unrecognised becomes
/// `TyKind::OfExpr`, a *decoded* type the elaborator checks sits at a universe
/// (docs/language/surface-universe.md §4).
fn expr_as_ty(e: &Expr) -> Ty {
    let span = e.span;
    let kind = match &e.kind {
        // `a = b` is an *expression* former, so it arrives already built; a
        // type position simply names it (docs/language/surface-universe.md §13).
        ExprKind::Eq(a, b) => TyKind::Eq(a.clone(), b.clone()),
        // A type that was written in type syntax in the first place — a
        // function type, or a motive body. Unwrap rather than re-wrap, so
        // `Nat -> Nat` in type position is the same `TyKind::Fn` it always was
        // and not an `El` of its own code.
        ExprKind::TyLit(t) => return (**t).clone(),
        // A bare name in type position is `Nat` or a declared type; whether
        // the name is in fact a type is the elaborator's call.
        ExprKind::Var(s) if s == "Nat" => TyKind::Nat,
        ExprKind::Var(s) => TyKind::Named { name: s.clone(), args: vec![] },
        // `Fin(n)` — the kernel's `Type::Fin`, claimed by *name* exactly as
        // `Nat` is, and so reserved in type position
        // (docs/language/surface-fin-indexing-design.md §2.2). It arrives here as an
        // ordinary application because `ty_atom`'s `D<A>` rule declines a `(`
        // and the fall-through parses an expression. Any other arity falls
        // through to `OfExpr`, where the elaborator's own `Fin` arm says what
        // the arity is.
        // `named.is_empty()` because this arm reads the arity off `args`
        // alone: `Fin(1, n := 2)` has one positional argument and would
        // otherwise be read as `Fin(1)` with the name silently dropped
        // (docs/language/named-arguments-design.md §8.2).
        ExprKind::App { head, args, named, explicit: false, .. }
            if matches!(&head.kind, ExprKind::Var(s) if s == "Fin")
                && args.len() == 1
                && named.is_empty() =>
        {
            TyKind::Fin(Box::new(args[0].clone()))
        }
        // `Type<n>` and `List<Nat>` — the two forms `atom` already parses with
        // type syntax inside them, so reading them back costs nothing.
        ExprKind::Univ { level } => TyKind::Univ { level: *level },
        ExprKind::TyApp { head, args } => match &head.kind {
            ExprKind::Var(name) => TyKind::Named { name: name.clone(), args: args.clone() },
            _ => TyKind::OfExpr(Box::new(e.clone())),
        },
        // Any other expression: a decoded type. `m.carrier` is why this
        // exists. Deliberately last, so every shape that already parsed as a
        // type still does.
        _ => TyKind::OfExpr(Box::new(e.clone())),
    };
    Ty { kind, span }
}

/// Fold a binder group's telescope into the curried Π chain it abbreviates:
/// `(x: A, y: B) -> C` **is** `(x: A) -> (y: B) -> C`, and nothing downstream
/// can tell which was written (issues/multi-binder-function-types.md). The
/// sugar is discharged here, in the parser, for that reason — a second
/// representation of the same type would be a second thing for the elaborator,
/// the printer and every test to agree about.
fn curry(binders: Vec<(String, Ty)>, cod: Ty, implicit: bool, span: Span) -> Ty {
    let mut out = cod;
    for (name, dom) in binders.into_iter().rev() {
        let sp = dom.span.join(out.span);
        out = Ty {
            kind: TyKind::Fn {
                binder: Some(name),
                implicit,
                dom: Box::new(dom),
                cod: Box::new(out),
            },
            span: sp,
        };
    }
    // The whole group's span, so a one-binder list is byte-for-byte the node
    // the single-binder rule used to build.
    Ty { kind: out.kind, span }
}

impl Parser {
    fn over(toks: Vec<Tok>) -> Parser {
        Parser {
            toks,
            pos: 0,
            sections: Vec::new(),
            section_typarams: Vec::new(),
            no_record_lit: false,
            no_eq: false,
            annotation_rel: false,
            no_iff: false,
            motive_body: false,
            spec_failed: std::collections::HashSet::new(),
            next_hygienic: 0,
            body_on_names: Vec::new(),
            record_facts: Vec::new(),
            propagation_count: 0,
            propagation_depth: 0,
            elseless_if: false,
            mut_params: Vec::new(),
            pending_mut: None,
            fn_body: false,
            own_method: None,
            defer_binds: false,
            mutables: Vec::new(),
            range_header: false,
            record_self: false,
        }
    }

    /// Whether an identifier token `name` was read since token `from`: a
    /// conservative "the source names it" (a shadowing binder counts too).
    fn names_from(&self, from: usize, name: Option<&str>) -> bool {
        let Some(name) = name else { return false };
        self.toks[from..self.pos].iter().any(|t| matches!(&t.kind, TokKind::Ident(n) if n == name))
            || self.body_on_names.iter().any(|n| n == name)
    }

    /// The identifiers of the `on` clauses at the head of the block that
    /// opens here (`{ … on ?dec1 := …; }`), read ahead of it: `on` at the
    /// block's own depth, up to the `;` that ends the clause.
    fn on_names_ahead(&self) -> Vec<String> {
        let mut out = Vec::new();
        if !matches!(self.peek(), TokKind::LBrace) {
            return out;
        }
        let mut depth = 0usize;
        let mut in_on = false;
        for tok in &self.toks[self.pos..] {
            match &tok.kind {
                TokKind::LBrace => depth += 1,
                TokKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                TokKind::Semi if depth == 1 => in_on = false,
                TokKind::Ident(n) if depth == 1 && n == "on" => in_on = true,
                TokKind::Ident(n) if in_on => out.push(n.clone()),
                _ => {}
            }
        }
        out
    }

    /// Whether an `on` discharge of a block enclosing this point names
    /// `name`: those blocks' goals are raised inside the branches being
    /// parsed, so their proofs see what the branches bind. Read ahead over
    /// the tokens: an `on` counts when it sits at the shallowest bracket
    /// depth reached so far, which is an enclosing block's own level (a
    /// later sibling's or a later item's `on`s are deeper). Conservative
    /// like [`Self::names_from`].
    fn names_in_enclosing_ons(&self, name: Option<&str>) -> bool {
        let Some(name) = name else { return false };
        let (mut depth, mut floor) = (0i64, 0i64);
        let mut j = self.pos;
        while j < self.toks.len() {
            match &self.toks[j].kind {
                TokKind::LBrace | TokKind::LParen | TokKind::LBracket => depth += 1,
                TokKind::RBrace | TokKind::RParen | TokKind::RBracket => {
                    depth -= 1;
                    floor = floor.min(depth);
                }
                TokKind::Ident(word) if word == "on" && depth == floor => {
                    // The discharge runs to its `;` at this level.
                    let mut inner = 0i64;
                    j += 1;
                    while j < self.toks.len() {
                        match &self.toks[j].kind {
                            TokKind::LBrace | TokKind::LParen | TokKind::LBracket => inner += 1,
                            TokKind::RBrace | TokKind::RParen | TokKind::RBracket => {
                                if inner == 0 { break }
                                inner -= 1;
                            }
                            TokKind::Semi if inner == 0 => break,
                            TokKind::Ident(n) if n == name => return true,
                            _ => {}
                        }
                        j += 1;
                    }
                    continue;
                }
                TokKind::Eof => break,
                _ => {}
            }
            j += 1;
        }
        false
    }

    fn hygienic(&mut self, kind: &str) -> String {
        let id = self.next_hygienic;
        self.next_hygienic += 1;
        format!("#{kind}{id}")
    }

    /// The token `k` positions ahead (`nth(0)` is [`Self::peek`]). Clamped to
    /// `Eof`, which the token stream always ends with.
    fn nth(&self, k: usize) -> &TokKind {
        let i = (self.pos + k).min(self.toks.len() - 1);
        &self.toks[i].kind
    }

    /// Is the parenthesised group at the current position a **type** rather
    /// than the start of an expression?
    ///
    /// In type position a leading `(` is ambiguous: `(A -> B) -> C` groups a
    /// type, while `(a + b) + c = d` opens the *expression* that is an
    /// equality's left endpoint. `->` is the discriminator, because it is not
    /// an expression operator — so the group is a type exactly when it
    /// contains a top-level `->` of its own, or is immediately followed by
    /// one. One scan, no backtracking.
    fn group_is_type(&self) -> bool {
        let mut depth = 0usize;
        let mut i = self.pos;
        while i < self.toks.len() {
            match self.toks[i].kind {
                TokKind::LParen => depth += 1,
                TokKind::Arrow if depth == 1 => return true,
                TokKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.nth(i + 1 - self.pos), TokKind::Arrow);
                    }
                }
                TokKind::Eof => break,
                _ => {}
            }
            i += 1;
        }
        false
    }

    /// Run `f` with the record-literal restriction set to `no`, restoring it
    /// after. Every bracketed context clears it; the three block-preceding
    /// contexts set it (see [`Parser::no_record_lit`]).
    fn with_record_lit<T>(&mut self, no: bool, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.no_record_lit, no);
        let r = f(self);
        self.no_record_lit = saved;
        r
    }

    fn peek(&self) -> &TokKind {
        &self.toks[self.pos].kind
    }

    fn peek_span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek(), TokKind::Eof)
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    fn err<T>(&self, msg: impl Into<String>) -> R<T> {
        Err(ParseError { msg: msg.into(), span: self.peek_span() })
    }

    fn expect(&mut self, kind: &TokKind, what: &str) -> R<Span> {
        if self.peek() == kind {
            return Ok(self.bump().span);
        }
        // A stray `>` has exactly one cause worth naming. `>` is not an
        // operator anywhere in the language (lexer.rs:40) — it only ever
        // closes a type-argument list — so meeting one where something else
        // was due means an opening `<` was read as a comparison instead of a
        // bracket. Under the one-directional whitespace rule ([`Self::tight`])
        // that is almost always a space the writer did not mean: `List <Nat>`.
        //
        // Cheap and precise: no scanning, no guessing which `<`, just the
        // reading that a stray `>` can have.
        if matches!(self.peek(), TokKind::Gt)
            && !matches!(kind, TokKind::Gt)
            && matches!(self.nth(1), TokKind::Gt)
            && self.tight(self.pos + 1)
        {
            return self.err(format!(
                "expected {what}, found `>>` written tight against what precedes it, which \
                 reads as two closers of type-argument lists. A right shift is written with \
                 a space before it: `a >> b`, not `a>>b`"
            ));
        }
        if matches!(self.peek(), TokKind::Gt) && !matches!(kind, TokKind::Gt) {
            return self.err(format!(
                "expected {what}, found `>` — `>` is not an operator and only ever closes a \
                 type-argument list, so its `<` was read as a comparison. A `<` with a space \
                 before it always is one: write `List<Nat>`, not `List <Nat>`"
            ));
        }
        self.err(format!("expected {what}, found {:?}", self.peek()))
    }

    /// Accept an identifier token; keywords are contextual, so any ident
    /// works where a name is demanded.
    fn ident(&mut self, what: &str) -> R<(String, Span)> {
        let (s, sp) = self.qual_ident(what)?;
        // A qualified name is a *reference*; nothing is ever declared or bound
        // under one (docs/language/modules-design.md §4). Caught here so the message
        // names the rule rather than surfacing as an elaborator mystery three
        // phases later.
        if s.contains("::") {
            return Err(ParseError {
                msg: format!(
                    "`{s}` is a qualified name, which can only refer to something \
                     declared elsewhere — it cannot be {what}"
                ),
                span: sp,
            });
        }
        Ok((s, sp))
    }

    /// [`Self::ident`] at a **reference** position, where `m::n` is a name:
    /// a module-qualified global (`nat::Nat::le_add`) or a type-qualified
    /// constructor (`Option::None`). Which one it is needs the name tables,
    /// so the parser keeps the two halves in one string and the elaborator
    /// splits it (docs/language/modules-design.md §4).
    fn qual_ident(&mut self, what: &str) -> R<(String, Span)> {
        match self.peek() {
            TokKind::Ident(s) => {
                let s = s.clone();
                let sp = self.bump().span;
                Ok((s, sp))
            }
            _ => self.err(format!("expected {what}, found {:?}", self.peek())),
        }
    }

    /// [`Self::ident`] at a **binding** position: the same read, plus rule 3.
    ///
    /// **Rule 3** (docs/language/let-and-blocks-design.md §5.2): a keyword-headed form
    /// that is neither saturated by a fixed token (rule 1's `j`, `calc`,
    /// `code`) nor nullary (rule 2's `refl`) is a true keyword, and a binder by
    /// its name is rejected *at the binding site* with a message naming the
    /// collision. `match` cannot take rule 1 because what follows it is an
    /// arbitrary expression; `Type` cannot take rule 2 because `Type` and
    /// `Type<0>` produce the same node, so there is no name left in the tree to
    /// check. Two of these were **silent** before this: `let refl = n; refl`
    /// died at "`refl` needs an `=` expected type" and `let Type = n; Type`
    /// reached the kernel as `Type<0>` and died at `LevelMismatch`.
    ///
    /// Permanent, unlike rules 1 and 2: `match`, `fun`, `if` and `Type` are keywords
    /// of the grammar, not elaborator conveniences, so
    /// `issues/special-forms-as-declarations.md` will never make them
    /// ordinary declarations (§5.4).
    fn binder_ident(&mut self, what: &str) -> R<(String, Span)> {
        let (name, span) = self.ident(what)?;
        let reason = match name.as_str() {
            "match" => "`match` is the eliminator keyword, so a use of it would parse \
                        as `match scrut { … }`",
            "fun" => "`fun` is the lambda keyword, so a use of it would parse as \
                      `fun x => …`",
            "Type" => "`Type` is the universe keyword, so a use of it would parse as \
                       `Type<0>` — silently, all the way to the kernel",
            "split" => "`split` is the case-split statement keyword, so a use of it at \
                        the head of a block's result would parse as `split e;` \
                        (docs/language/matching/match-equation-split-design.md §5)",
            "if" => "`if` is the decidable-branching keyword, so a use of it would parse \
                     as `if P { … } else { … }`",
            _ => return Ok((name, span)),
        };
        Err(ParseError {
            msg: format!("{reason}; it cannot be a binding name here. Pick another name"),
            span,
        })
    }

    /// Is the next token the identifier `kw`?
    fn at_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), TokKind::Ident(s) if s == kw)
    }

    /// `induct f(…)`: the word followed by a name, so `induct` stays an
    /// ordinary identifier everywhere else (`induct(x)`, `let induct = …`).
    fn at_induct(&self) -> bool {
        self.at_kw("induct") && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Ident(_)))
    }

    /// `cases h;` or `cases h as …;`: the word followed by a name and then
    /// `;` or `as`, so `cases` stays an ordinary identifier elsewhere
    /// (`cases(e, g)` in the tactic library).
    fn at_cases(&self) -> bool {
        self.at_kw("cases")
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Ident(_)))
            && matches!(self.toks.get(self.pos + 2).map(|t| &t.kind), Some(TokKind::Semi) | Some(TokKind::Ident(_)))
            && match self.toks.get(self.pos + 2).map(|t| &t.kind) {
                Some(TokKind::Ident(word)) => word == "as",
                _ => true,
            }
    }

    /// `op as ∙` — the **body spelling** a declaring binder installs
    /// (issues/binder-symbol-as-notation.md). Read directly after the binder's
    /// name, before its `:`.
    ///
    /// `as` can only install a symbol that **already lexes**, which is what
    /// bounds the device's blast radius: the curated table
    /// (issues/notation-extensibility.md) is the same one everything else is
    /// bounded by, so this grammar adds a *position* for a symbol and never a
    /// symbol. A name here — `op as mul` — is refused with the table, since it
    /// would otherwise read as the beginning of an unrelated parse error.
    fn binder_symbol(&mut self, name: &str) -> R<Option<String>> {
        if !self.at_kw("as") {
            return Ok(None);
        }
        let asp = self.bump().span;
        let Some(sym) = Self::op_symbol(self.peek()) else {
            return Err(ParseError {
                msg: format!(
                    "`{name} as …` installs an operator SYMBOL as this binder's body \
                     spelling, and `as` can only install one that already lexes: the \
                     curated table is `+`, `-`, `++`, `*`, `/`, `%`, `^`, `&`, `|`, `<<`, \
                     `>>`, `&&`, `||`, `∙`, `⊔`, `⊓`, `≈`, `<=`, `<` \
                     (issues/notation-extensibility.md owns the lexicon)"
                ),
                span: asp.join(self.peek_span()),
            });
        };
        self.bump();
        Ok(Some(sym.to_string()))
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    // -- declarations -------------------------------------------------------

    /// Parse one item position. An `assuming` group is surface-only: it
    /// flattens to its declarations after prepending one ordinary solver
    /// telescope to each. The elaborator consequently sees exactly the same
    /// `Param` representation as a written `:= infer` or `requires` binder.
    fn items(&mut self) -> R<Vec<Item>> {
        if self.at_kw("assuming") {
            self.assuming_items()
        } else if self.at_kw("section") {
            self.section_items()
        } else if self.at_kw("partial")
            && (matches!(self.nth(1), TokKind::LParen)
                || matches!(self.nth(1), TokKind::Ident(k) if DECL_WORDS.contains(&k.as_str())))
        {
            Ok(vec![Item::Decl(self.partial_decl()?)])
        } else {
            match self.item()? {
                Item::Decl(mut d) => {
                    let fact = self.result_fact(&mut d)?;
                    Ok(std::iter::once(Item::Decl(d)).chain(fact.map(Item::Decl)).collect())
                }
                item => {
                    let facts = std::mem::take(&mut self.record_facts);
                    Ok(std::iter::once(item).chain(facts.into_iter().map(Item::Decl)).collect())
                }
            }
        }
    }

    /// `fn f(…) → Pos<A>` — the result half of the `Pos<A>` binder sugar
    /// (docs/library/positivity-evidence-design.md §6 B). The function returns an
    /// `A`, and the declaration after it is the fact, owned by the function:
    ///
    /// ```text
    /// evidence theorem f::pos({…f's parameters…}): 0 < f(…) { … }
    /// ```
    ///
    /// A member function's fact is named under it: `fn T::f(…) → Pos<A>`
    /// declares `T::f::pos`, attached to `T` as an instance's
    /// `Le::Judge::verdict` is (the elaborator splits at the first `::`).
    ///
    /// Every parameter of `f` that is not a solver parameter becomes a `{}`
    /// implicit, which the rule's conclusion fixes by unification; solver
    /// parameters (a `Pos<A>` parameter's `x_pos` among them) stay premises
    /// `:= infer`. So the fact is an evidence rule, and `0 < f(…)` is found
    /// by `:= infer` at every caller. An `assuming` group reaches both
    /// declarations, as it does every item in it.
    ///
    /// The proof is the obligation the result type states. Written
    /// `on ?pos := e;` in `f`'s body, `e` proves the statement itself, which
    /// is the route for a recursive `f` (its proof is an induction). Otherwise
    /// the body is restated at `0 < (result)` and `positivity` searches it:
    /// the statement unfolds `f` once, by conversion, to meet it.
    fn result_fact(&mut self, d: &mut Decl) -> R<Option<Decl>> {
        let Some(carrier) = pos_carrier(&d.result).cloned() else { return Ok(None) };
        let span = d.result.span;
        let refuse = |msg: String| Err(ParseError { msg, span });
        if d.kind != DeclKind::Fn || d.is_meta {
            return refuse(format!(
                "`Pos<A>` as a result is a function's: `fn f(…) → Pos<A>` returns an `A` \
                 and declares `f::pos` (docs/library/positivity-evidence-design.md §6 B). A \
                 {} states `0 < …` instead",
                if d.is_meta { "`meta fn`" } else { "theorem" }
            ));
        }
        let mut written = None;
        d.body.ons.retain(|o| match &o.target {
            OnTarget::Name(n) if n == "pos" && written.is_none() => {
                written = Some(o.expr.clone());
                false
            }
            _ => true,
        });
        if written.is_none() && d.decreases.is_some() {
            return refuse(format!(
                "`{}` recurses on a measure, so restating its body proves nothing about \
                 the recursive calls: prove its positivity in the body, \
                 `on ?pos := …;`, at `0 < {}(…)`",
                d.name, d.name
            ));
        }
        d.result = carrier;
        let var = |name: &str| Expr { kind: ExprKind::Var(name.to_string()), span };
        let mut args = Vec::new();
        let mut named = Vec::new();
        let mut params = Vec::new();
        for p in &d.params {
            let mut q = p.clone();
            if p.solver.is_none() {
                if p.implicit {
                    named.push(NamedArg {
                        name: p.name.clone(),
                        name_span: span,
                        expr: var(&p.name),
                        span,
                    });
                } else {
                    args.push(var(&p.name));
                }
                q.implicit = true;
                q.default = None;
                q.is_self = false;
            }
            q.span = span;
            params.push(q);
        }
        let call = Expr {
            kind: ExprKind::App {
                head: Box::new(var(&d.name)),
                args,
                named,
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let positive = |e: Expr| {
            let zero = Expr { kind: ExprKind::Num(Numeral::ZERO), span };
            Ty { kind: TyKind::OfExpr(Box::new(op_call("<", OpFixity::Infix, vec![zero, e], span))), span }
        };
        let body = match written {
            Some(e) => Block { stmts: Vec::new(), result: Box::new(e), ons: Vec::new(), span },
            None => {
                let h = self.hygienic("pos");
                let mut stmts = d.body.stmts.clone();
                stmts.push(Stmt::Let {
                    name: h.clone(),
                    ty: Some(positive((*d.body.result).clone())),
                    expr: var(POS_RESULT),
                    span,
                    opaque: false,
                });
                Block { stmts, result: Box::new(var(&h)), ons: d.body.ons.clone(), span }
            }
        };
        Ok(Some(Decl {
            kind: DeclKind::Theorem,
            is_meta: false,
            is_evidence: true,
            is_interface: false, partial: None,
            value: false,
            elaborates: None,
            name: format!("{}::pos", d.name),
            tyvars: d.tyvars.clone(),
            params,
            result: positive(call),
            decreases: None,
            depth: None,
            unfolding: Vec::new(),
            body,
            span,
        }))
    }

    /// `section<A: C>(x: A, …) { fn … theorem … }` — a head written once for
    /// a run of declarations (docs/language/sections-design.md §5). Surface-only, like
    /// `assuming`: the head is pushed for the group's extent and
    /// [`Parser::splice_sections`] prepends it to each member's own head as
    /// the member is read, so the elaborator sees ordinary declarations.
    fn section_items(&mut self) -> R<Vec<Item>> {
        let start = self.bump().span; // `section`
        let (tyvars, constraints) = self.typaram_list()?;
        let mut solver = constraints;
        solver.extend(self.requires_list()?);
        let written =
            if matches!(self.peek(), TokKind::LParen) { self.param_list(Vec::new())? } else { Vec::new() };
        let head = start.join(self.toks[self.pos.saturating_sub(1)].span);
        if tyvars.is_empty() && solver.is_empty() && written.is_empty() {
            return Err(ParseError {
                msg: "a section's head is what it writes once for its members: give it \
                      type parameters `section<A> { … }`, parameters `section(x: A) { … }`, \
                      or both (docs/language/sections-design.md §5.1)"
                    .into(),
                span: head,
            });
        }
        if let Some(p) = written.iter().find(|p| p.is_self)
            && let Some(outer) = self.sections.iter().flat_map(|s| &s.written).find(|q| q.is_self)
        {
            return Err(ParseError {
                msg: format!(
                    "a declaration has at most one `self`, and the enclosing section's `{}` \
                     is already it",
                    outer.name
                ),
                span: p.span,
            });
        }
        self.check_section_names(
            tyvars.iter().map(|t| (t.name.as_str(), t.span)).chain(
                solver.iter().chain(&written).map(|p| (p.name.as_str(), p.span)),
            ),
            "an enclosing section",
        )?;
        if let (Some(first), Some(last)) = (tyvars.first(), tyvars.last()) {
            self.section_typarams.push((head, first.span, last.span));
        }
        self.sections.push(SectionHead { tyvars, solver, written });
        self.expect(&TokKind::LBrace, "`{` to open the section's declarations")?;
        let mut items = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            if self.at_eof() {
                return Err(ParseError {
                    msg: "expected `}` to close the section".into(),
                    span: start.join(self.peek_span()),
                });
            }
            for item in self.items()? {
                let refuse = |what: &str, span: Span| {
                    Err(ParseError {
                        msg: format!(
                            "{what} cannot be in a section: a section's head is spliced into \
                             the head of each `fn` and `theorem` in it, and nothing else has \
                             a head to splice into (docs/language/sections-design.md §5.2)"
                        ),
                        span,
                    })
                };
                match &item {
                    Item::Decl(d) if d.is_meta => return refuse("a `meta fn`", d.span),
                    Item::Decl(d) if d.kind == DeclKind::Axiom => return refuse("an `axiom`", d.span),
                    Item::Decl(_) => {}
                    Item::Import(i) => return refuse("an `import`", i.span),
                    Item::Inductive(i) => return refuse("an `inductive` or `record`", i.span),
                    Item::Class(c) => return refuse("a `class`", c.span),
                    Item::Instance(i) => return refuse("an `instance`", i.span),
                    Item::Designation(d) => return refuse("a `designation`", d.span),
                    Item::Datarepr(d) => return refuse("a `datarepr`", d.span),
                    Item::Impl(i) => return refuse("an `impl`", i.span),
                    Item::Generate(g) => {
                        return Err(ParseError {
                            msg: "a `generate` cannot be in a section yet: its generator runs at \
                                  the module's empty context, and running it under the section's \
                                  head is open (docs/metaprogramming/host-elaboration-interface-design.md §19)"
                                .into(),
                            span: g.span,
                        })
                    }
                    Item::Prefixed(PrefixedItem { span, .. }) | Item::PrefixedRecord(PrefixedRecordItem { span, .. }) => {
                        return Err(ParseError {
                            msg: "a prefixed declaration cannot be in a section yet: its \
                                  generator runs at the module's empty context, as a \
                                  `generate` does (docs/metaprogramming/value-definitions-design.md §3)"
                                .into(),
                            span: *span,
                        })
                    }
                }
                items.push(item);
            }
        }
        self.bump(); // `}`
        self.sections.pop();
        Ok(items)
    }

    /// Refuse a binder that rebinds a name an enclosing section's head binds.
    /// A repeated value parameter otherwise shadows the earlier one silently,
    /// which inside a section would hide the head's binder from the member.
    fn check_section_names<'a>(
        &self,
        names: impl Iterator<Item = (&'a str, Span)>,
        whose: &str,
    ) -> R<()> {
        for (name, span) in names {
            if name.starts_with('#') {
                continue;
            }
            let bound = self.sections.iter().any(|s| {
                s.tyvars.iter().any(|t| t.name == name)
                    || s.solver.iter().chain(&s.written).any(|p| p.name == name)
            });
            if bound {
                return Err(ParseError {
                    msg: format!(
                        "`{name}` is already bound by {whose}'s head: a section's binders \
                         are every member's, so a member cannot rebind one (move the \
                         declaration out of the section, or rename)"
                    ),
                    span,
                });
            }
        }
        Ok(())
    }

    /// Prepend the enclosing sections' heads to a declaration's own
    /// (docs/language/sections-design.md §5.2), outermost first: type parameters before
    /// the member's, solver parameters before its solver parameters (the first
    /// `leading` of `params`), written parameters before its written ones. The
    /// result is the head the member would have if written out by hand.
    ///
    /// A section type parameter or `{}` implicit that nothing in the spliced
    /// head determines is refused: no call could infer it. "Determines" is
    /// read off the tokens of the head: a name written in an explicit
    /// parameter's type or the result type, or in the type of a binder so
    /// determined. That over-approximates (a name bound inside a type also
    /// counts), so the check can miss a case, which then fails at the call as
    /// it would without a section; it never refuses a member that could be
    /// called.
    fn splice_sections(
        &self,
        member: &str,
        member_span: Span,
        tyvars: Vec<TyParam>,
        params: Vec<Param>,
        leading: usize,
        result: &Ty,
    ) -> R<(Vec<TyParam>, Vec<Param>)> {
        if self.sections.is_empty() {
            return Ok((tyvars, params));
        }
        self.check_section_names(
            tyvars.iter().map(|t| (t.name.as_str(), t.span)).chain(params.iter().map(|p| (p.name.as_str(), p.span))),
            "the enclosing section",
        )?;
        if let Some(p) = params.iter().find(|p| p.is_self)
            && let Some(outer) = self.sections.iter().flat_map(|s| &s.written).find(|q| q.is_self)
        {
            return Err(ParseError {
                msg: format!(
                    "a declaration has at most one `self`, and the enclosing section's `{}` \
                     is already it",
                    outer.name
                ),
                span: p.span,
            });
        }
        let mut all_tyvars: Vec<TyParam> = self.sections.iter().flat_map(|s| s.tyvars.clone()).collect();
        all_tyvars.extend(tyvars);
        let mut own = params;
        let own_written = own.split_off(leading.min(own.len()));
        let mut all: Vec<Param> = self.sections.iter().flat_map(|s| s.solver.clone()).collect();
        all.extend(own);
        all.extend(self.sections.iter().flat_map(|s| s.written.clone()));
        all.extend(own_written);

        let mut determined = std::collections::HashSet::new();
        self.idents_in(result.span, &mut determined);
        for p in all.iter().filter(|p| !p.implicit) {
            self.idents_in(p.ty.span, &mut determined);
        }
        let unification = |p: &Param| p.implicit && p.solver.is_none() && p.default.is_none();
        loop {
            let before = determined.len();
            let reached: Vec<Span> = all
                .iter()
                .filter(|p| unification(p) && determined.contains(&p.name))
                .map(|p| p.ty.span)
                .collect();
            for span in reached {
                self.idents_in(span, &mut determined);
            }
            if determined.len() == before {
                break;
            }
        }
        let section_binder = |name: &str| {
            self.sections.iter().any(|s| {
                s.tyvars.iter().any(|t| t.name == name) || s.written.iter().any(|p| p.name == name && unification(p))
            })
        };
        let undetermined = all_tyvars
            .iter()
            .map(|t| t.name.as_str())
            .chain(all.iter().filter(|p| unification(p)).map(|p| p.name.as_str()))
            .find(|n| section_binder(n) && !determined.contains(*n));
        if let Some(n) = undetermined {
            return Err(ParseError {
                msg: format!(
                    "`{member}` does not determine the section's `{n}`: nothing in its head \
                     mentions it, so no call could infer it. Move `{member}` out of the \
                     section, or mention `{n}` in its parameters or result \
                     (docs/language/sections-design.md §4.1)"
                ),
                span: member_span,
            });
        }
        Ok((all_tyvars, all))
    }

    /// Every identifier token inside `span` (the tokens are sorted by
    /// position, so this is a binary search and a slice).
    fn idents_in(&self, span: Span, out: &mut std::collections::HashSet<String>) {
        let first = self.toks.partition_point(|t| t.span.start < span.start);
        for t in self.toks[first..].iter().take_while(|t| t.span.end <= span.end) {
            if let TokKind::Ident(n) = &t.kind {
                out.insert(n.clone());
            }
        }
    }

    fn assuming_items(&mut self) -> R<Vec<Item>> {
        let start = self.bump().span; // `assuming`
        let mut assumptions = Vec::new();
        loop {
            let named = matches!(self.peek(), TokKind::Ident(_))
                && matches!(self.nth(1), TokKind::Colon);
            let (name, nsp) = if named {
                let (name, span) = self.binder_ident("an `assuming` binder name")?;
                self.bump(); // `:`
                (name, span)
            } else {
                (self.hygienic("assuming"), self.peek_span())
            };
            // The following `{` opens the item group, never a record literal
            // continuing the assumption type — the same boundary as a
            // declaration result immediately followed by its body.
            let ty = self.with_record_lit(true, |p| p.ty())?;
            let span = nsp.join(ty.span);
            assumptions.push(Param {
                name,
                ty,
                implicit: true,
                is_self: false,
                solver: Some(Solver::Infer),
                default: None,
                origin: ParamOrigin::Assuming,
                symbol: None,
                span,
            });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::LBrace, "`{` to open the `assuming` item group")?;
        let mut items = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            if self.at_eof() {
                return Err(ParseError {
                    msg: "expected `}` to close the `assuming` item group".into(),
                    span: start.join(self.peek_span()),
                });
            }
            for item in self.items()? {
                if let Item::Import(i) = &item {
                    return Err(ParseError {
                        msg: "an `import` cannot appear inside an `assuming` group; imports \
                              belong at the start of the file"
                            .into(),
                        span: i.span,
                    });
                }
                items.push(self.apply_assumptions(item, &assumptions)?);
            }
        }
        self.bump(); // `}`
        Ok(items)
    }

    fn apply_assumptions(&self, item: Item, assumptions: &[Param]) -> R<Item> {
        match item {
            Item::Decl(mut d) => {
                let mut params = assumptions.to_vec();
                params.append(&mut d.params);
                d.params = params;
                Ok(Item::Decl(d))
            }
            Item::Inductive(i) => Err(ParseError {
                msg: "`inductive` inside `assuming` is not implemented yet: the first \
                      slice generalizes `fn`, `theorem`, `axiom`, and `meta fn` declarations"
                    .into(),
                span: i.span,
            }),
            Item::Class(c) => Err(ParseError {
                msg: "`class` inside `assuming` is not implemented yet: the first slice \
                      generalizes ordinary declarations"
                    .into(),
                span: c.span,
            }),
            Item::Instance(mut i) => {
                // An instance already carries its conditional evidence in
                // `requires`; inherited assumptions are exactly more of that
                // telescope. Value binders must remain first because written
                // instance requirements may depend on them, so prepend within
                // `requires`, not before the instance's type/value binders.
                let mut requires = assumptions.to_vec();
                requires.append(&mut i.requires);
                i.requires = requires;
                Ok(Item::Instance(i))
            }
            Item::Designation(d) => Err(ParseError {
                msg: "`designation` cannot yet inherit an `assuming` telescope".into(),
                span: d.span,
            }),
            Item::Datarepr(d) => Err(ParseError {
                msg: "`datarepr` cannot yet inherit an `assuming` telescope".into(),
                span: d.span,
            }),
            Item::Impl(i) => Err(ParseError {
                msg: "`impl` cannot yet inherit an `assuming` telescope".into(),
                span: i.span,
            }),
            Item::Import(i) => Err(ParseError {
                msg: "an `import` cannot appear inside an `assuming` group".into(),
                span: i.span,
            }),
            Item::Generate(g) => Err(ParseError {
                msg: "a `generate` cannot yet inherit an `assuming` telescope".into(),
                span: g.span,
            }),
            Item::Prefixed(PrefixedItem { span, .. }) | Item::PrefixedRecord(PrefixedRecordItem { span, .. }) => Err(ParseError {
                msg: "a prefixed declaration cannot yet inherit an `assuming` telescope".into(),
                span,
            }),
        }
    }

    fn item(&mut self) -> R<Item> {
        // `import` is contextual like every other keyword here: a declaration
        // named `import` is impossible anyway (`import` would have to be
        // followed by `fn`/`theorem`), and the `;`/`::` shape below is what a
        // real import always has.
        if self.at_kw("import") || self.at_kw("export") {
            return Ok(Item::Import(self.import()?));
        }
        if self.at_kw("inductive") || self.at_kw("codata") {
            return Ok(Item::Inductive(self.inductive()?));
        }
        if self.at_kw("record") {
            return Ok(Item::Inductive(self.record()?));
        }
        // `class`/`instance` are contextual like every keyword here: a
        // declaration cannot begin with either (a `fn` named `class` is
        // `fn class(…)`, and the keyword is only recognized at the head of an
        // item, where `class C<…>` and `instance C<…>` are the only readings).
        if self.at_kw("class") {
            return Ok(Item::Class(self.class_decl()?));
        }
        if self.at_kw("instance") {
            return Ok(Item::Instance(self.instance_decl()?));
        }
        if self.at_kw("designation") {
            return Ok(Item::Designation(self.designation_decl()?));
        }
        if self.at_kw("datarepr") {
            return Ok(Item::Datarepr(self.datarepr_decl()?));
        }
        if self.at_kw("impl") {
            return Ok(Item::Impl(self.impl_decl()?));
        }
        // `generate g(args);` runs a generator and publishes what it builds
        // (docs/metaprogramming/host-elaboration-interface-design.md §19). Contextual like
        // `by`: only when a name follows.
        if self.at_kw("generate") && matches!(self.nth(1), TokKind::Ident(_)) {
            let start = self.bump().span;
            let generator = self.postfix()?;
            let end = self.expect(&TokKind::Semi, "`;` to end the `generate`")?;
            return Ok(Item::Generate(GenerateItem { generator, span: start.join(end) }));
        }
        // `given` section variables and `context` constraint bundles are the
        // two other ways round 2 sketched of writing a constraint ONCE for many
        // declarations. Neither is decided (issues/requires-placement-syntax.md;
        // `section` heads are docs/language/sections-design.md), and both are words a
        // reader who met `<A: Monoid>` will reach for, so they are refused by
        // name rather than by "expected `fn`".
        if self.at_kw("given") || self.at_kw("context") {
            let TokKind::Ident(w) = self.peek() else { unreachable!() };
            let w = w.clone();
            return self.err(&format!(
                "`{w}` is not implemented: a constraint is written on the declaration \
                 that needs it, inline as `<A: Monoid>` or as a `requires` binder, or \
                 once for a run of declarations in a `section<A: Monoid> {{ … }}` head. \
                 Section variables and named bundles are open design \
                 (issues/requires-placement-syntax.md)"
            ));
        }
        // `runtime fn f(…)`, `runtime(owned) fn f(…)`, `regex def x = "…";` —
        // a declaration under a prefix generator
        // (docs/metaprogramming/value-definitions-design.md §3). A name before a declaration
        // keyword, or a name applied, is not otherwise an item, so this reads
        // nothing that used to parse. The modifier keywords are matched first.
        // `laid record T { … }`: a `record` takes a prefix too (§3.5).
        if let TokKind::Ident(w) = self.peek()
            && !matches!(w.as_str(), "fn" | "theorem" | "axiom" | "def" | "meta" | "evidence" | "interface")
            && (matches!(self.nth(1), TokKind::LParen)
                || matches!(self.nth(1), TokKind::Ident(k) if DECL_WORDS.contains(&k.as_str()) || PREFIXED_TYPE_WORDS.contains(&k.as_str()))
                // `a b fn f`: two prefixes, read as one so it is refused as such.
                || (matches!(self.nth(1), TokKind::Ident(_))
                    && matches!(self.nth(2), TokKind::Ident(k) if DECL_WORDS.contains(&k.as_str()) || PREFIXED_TYPE_WORDS.contains(&k.as_str()))))
        {
            return self.prefixed();
        }
        Ok(Item::Decl(self.decl()?))
    }

    /// `partial fn f(…) → B { … }` or `partial(E) fn …` ([`Decl::partial`],
    /// docs/language/partial-functions-design.md §4). Contextual: `partial` is a word
    /// only before `fn` or `(`, at an item's head.
    fn partial_decl(&mut self) -> R<Decl> {
        let start = self.bump().span;
        let mut events = None;
        if matches!(self.peek(), TokKind::LParen) {
            self.bump();
            events = Some(self.expr()?);
            self.expect(&TokKind::RParen, "`)` to close `partial(E)`")?;
        }
        if !self.at_kw("fn") {
            return self.err(
                "`partial` marks a `fn`: a function that may not return. A theorem, a value \
                 or an axiom has no run to diverge",
            );
        }
        let mut d = self.decl()?;
        if d.decreases.is_some() {
            return Err(ParseError {
                msg: "a `partial fn` has no measure: it may not return, which is what `partial` says. \
                      Drop `partial` to prove it terminates with `decreases`"
                    .into(),
                span: d.span,
            });
        }
        d.partial = Some(PartialSpec { events, span: start });
        d.span = start.join(d.span);
        Ok(d)
    }

    /// `P decl` or `P(args) decl` ([`Item::Prefixed`]). One prefix: a second
    /// name before the declaration is refused, since composing generators is
    /// open (issues/scoped-declaration-generators.md). The declaration under
    /// it is a `fn`, a `theorem` or a `def`, or a `record`
    /// ([`Item::PrefixedRecord`]).
    fn prefixed(&mut self) -> R<Item> {
        let start = self.peek_span();
        let (name, name_span) = self.ident("a generator's name")?;
        let mut generator = Expr { kind: ExprKind::Var(name.clone()), span: name_span };
        if matches!(self.peek(), TokKind::LParen) {
            self.bump();
            let (args, named, close) = self.call_args()?;
            generator = Expr {
                kind: ExprKind::App { head: Box::new(generator), args, named, explicit: false, goal_oriented: false },
                span: name_span.join(close),
            };
        }
        if self.at_kw("record") {
            let record = self.record()?;
            let span = start.join(record.span);
            return Ok(Item::PrefixedRecord(PrefixedRecordItem { generator, record, span }));
        }
        if let TokKind::Ident(w) = self.peek()
            && matches!(w.as_str(), "inductive" | "codata" | "class" | "instance")
        {
            let w = w.clone();
            return self.err(&format!(
                "a generator prefixes a `fn`, a `theorem`, a `def` or a `record`, not \
                 {} `{w}` (docs/metaprogramming/value-definitions-design.md §3)",
                if w == "inductive" || w == "instance" { "an" } else { "a" }
            ));
        }
        if let TokKind::Ident(w) = self.peek()
            && !matches!(w.as_str(), "fn" | "theorem" | "axiom" | "def" | "meta" | "evidence" | "interface")
        {
            let w = w.clone();
            return self.err(&format!(
                "one generator prefixes a declaration: `{name} {w} …` stacks two, and how \
                 generators compose is open (issues/scoped-declaration-generators.md)"
            ));
        }
        let decl = self.decl()?;
        if decl.is_meta || decl.is_evidence || decl.kind == DeclKind::Axiom {
            let what = if decl.is_meta {
                "a `meta fn`"
            } else if decl.is_evidence {
                "an `evidence theorem`"
            } else {
                "an `axiom`"
            };
            return Err(ParseError {
                msg: format!(
                    "a generator prefixes a `fn`, a `theorem` or a `def`, not {what} \
                     (docs/metaprogramming/value-definitions-design.md §3)"
                ),
                span: start.join(decl.span),
            });
        }
        let span = start.join(decl.span);
        Ok(Item::Prefixed(PrefixedItem { generator, decl, span }))
    }

    /// `class C<A> extends P<A>, Q<A> { f: T, … }`
    /// (docs/language/classes/traits-layer1-design.md §1). The body is a `record`'s field list,
    /// verbatim — a class *is* a parameterized record, and the parse says so.
    fn class_decl(&mut self) -> R<ClassDecl> {
        let start = self.peek_span();
        self.bump(); // `class`
        let (name, _) = self.ident("class name")?;
        let (params, kinds) = self.class_tyvar_list()?;
        // `class Monoid<A>(op: A -> A -> A)` — the index list, in the position
        // and with the grammar a `record` head already has
        // (docs/language/classes/operation-indexed-classes-design.md §2.1: there is no second
        // class form, only a per-class choice about the parameter list).
        let valparams = self.valparam_list(true, false)?;
        let mut extends = Vec::new();
        if self.eat_kw("extends") {
            loop {
                let mut parent = self.class_ref("a parent class (`extends Monoid<A>`)")?;
                if self.eat_kw("as") {
                    let (tag, tag_span) = self.ident("parent dictionary tag after `as`")?;
                    parent.path.push(tag);
                    parent.span = parent.span.join(tag_span);
                }
                extends.push(parent);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&TokKind::LBrace, "`{` (field list)")?;
        let mut fields = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let f = self.field()?;
            if f.name.is_none() {
                return Err(ParseError {
                    msg: "a class field needs a name (`unit: A`): the name is what an \
                          instance fills and what `m.unit` projects by"
                        .into(),
                    span: f.span,
                });
            }
            fields.push(f);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}` (field list)")?;
        Ok(ClassDecl { name, params, kinds, valparams, extends, fields, span: start.join(end) })
    }

    /// A class head's `<A, M: Type → Type>`: [`Self::tyvar_list`] plus an
    /// optional **kind** per parameter (issues/higher-kinded-classes.md). A
    /// kind is any type — what makes it a type constructor is the
    /// elaborator's check — so the grammar is a parameter's own
    /// `name: T`, and an unannotated name keeps meaning a type.
    fn class_tyvar_list(&mut self) -> R<(Vec<String>, Vec<Option<Ty>>)> {
        let mut params = Vec::new();
        let mut kinds = Vec::new();
        if matches!(self.peek(), TokKind::Lt) {
            self.bump();
            loop {
                params.push(self.binder_ident("type parameter name")?.0);
                kinds.push(if matches!(self.peek(), TokKind::Colon) {
                    self.bump();
                    Some(self.ty()?)
                } else {
                    None
                });
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::Gt, "`>` to close the type parameters")?;
        }
        Ok((params, kinds))
    }

    /// `Monoid<A>` — a class applied to its arguments. The brackets are
    /// mandatory: a class with no parameters has no carrier, so it is a
    /// `record` and should be written as one.
    fn class_ref(&mut self, what: &str) -> R<ClassRef> {
        let (name, nsp) = self.qual_ident(what)?;
        if !matches!(self.peek(), TokKind::Lt) {
            return Err(ParseError {
                msg: format!(
                    "`{name}` needs its arguments here (`{name}<A>`): a class is a record \
                     parameterized by its carrier, so the carrier is written"
                ),
                span: nsp,
            });
        }
        self.bump();
        let mut args = Vec::new();
        loop {
            args.push(self.with_record_lit(true, |p| p.ty())?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let mut end = self.expect(&TokKind::Gt, "`>` to close the class arguments")?;
        // `Monoid<A>(op)` — the index arguments
        // (docs/language/classes/operation-indexed-classes-design.md §3). An index is an
        // ordinary expression here; which shapes an *instance head* admits is
        // the elaborator's spellability rule (§3.1), stated where the key is
        // computed rather than in the grammar.
        //
        // The `(` is the index list only when it does not open a *binder* list:
        // `requires m: Monoid<A> (xs: List<A>)` puts the declaration's own
        // parameters directly after the class reference, and `name :` is the
        // one shape an index argument can never have.
        let mut index = Vec::new();
        // An empty `()` is a binder list too: an index list with nothing in it
        // says nothing, and `requires m: Mag<A> () -> Nat` is the shape that
        // has to keep parsing.
        let binder_list = matches!(self.peek(), TokKind::LParen)
            && (matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::RParen))
                || (matches!(
                    self.toks.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokKind::Ident(_))
                ) && matches!(
                    self.toks.get(self.pos + 2).map(|t| &t.kind),
                    Some(TokKind::Colon)
                )));
        if matches!(self.peek(), TokKind::LParen) && !binder_list {
            self.bump();
            while !matches!(self.peek(), TokKind::RParen) {
                match self.op_symbol_arg() {
                    Some(e) => index.push(e),
                    None => index.push(self.expr()?),
                }
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            end = self.expect(&TokKind::RParen, "`)` to close the class's index arguments")?;
        }
        Ok(ClassRef { name, args, index, path: Vec::new(), span: nsp.join(end) })
    }

    /// `designation<A> ++ at List<A> := append`
    /// (docs/language/classes/operators-onto-classes-design.md §3.1).
    ///
    /// Contextual exactly as `class` and `instance` are, and for a stronger
    /// reason than either: the token after the keyword is an *operator*, which
    /// no declaration's name can be.
    fn designation_decl(&mut self) -> R<DesignationDecl> {
        let start = self.peek_span();
        self.bump(); // `designation`
        let fixity = if self.eat_kw("prefix") {
            OpFixity::Prefix
        } else if self.eat_kw("postfix") {
            OpFixity::Postfix
        } else {
            OpFixity::Infix
        };
        // `<` opens the optional type-parameter list everywhere else, but in
        // `designation < at Int := Lt` it is the operator itself. `at` cannot
        // begin a type parameter, so this two-token lookahead is exact and
        // leaves `designation<A> < at List<A> := …` on the generic path.
        let less_operator = matches!(self.peek(), TokKind::Lt)
            && matches!(self.nth(1), TokKind::Ident(word) if word == "at");
        let tyvars = if less_operator {
            Vec::new()
        } else {
            self.tyvar_list()?
        };
        let sym = match fixity {
            OpFixity::Prefix if matches!(self.peek(), TokKind::Minus) => Some("-"),
            OpFixity::Prefix if matches!(self.peek(), TokKind::Bang) => Some("!"),
            OpFixity::Prefix if matches!(self.peek(), TokKind::Tilde) => Some("~"),
            OpFixity::Prefix => None,
            OpFixity::Postfix if matches!(self.peek(), TokKind::SupInverse) => Some("⁻¹"),
            OpFixity::Postfix => None,
            OpFixity::Infix => Self::op_symbol(self.peek()),
        };
        let Some(sym) = sym else {
            return self.err(
                "a designation names an operator (`designation + at Nat := add`, \
                 `designation prefix - at Int := neg`, `designation postfix ⁻¹ at Rat := \
                 Rat::inv`). A designation for an ordinary name \
                 is not a form — that is a default instance wearing a smaller hat \
                 (docs/language/classes/operation-indexed-classes-design.md §9.2)",
            );
        };
        let symbol = sym.to_string();
        self.bump();
        if !self.eat_kw("at") {
            return self.err(&format!(
                "`at` and then the carrier (`designation {symbol} at Nat := …`): a \
                 designation says what `{symbol}` means at a type, so the type is written"
            ));
        }
        let carrier = self.with_record_lit(true, |p| p.ty())?;
        self.expect(
            &TokKind::ColonEq,
            "`:=` and the designated operation (`designation + at Nat := add`)",
        )?;
        let op = self.expr()?;
        let span = start.join(op.span);
        Ok(DesignationDecl { tyvars, fixity, symbol, carrier, op, span })
    }

    /// `datarepr N for S { R := …, mk Cons := …, … }` and
    /// `datarepr N for S := repr::naive();` (docs/native/datarepr-design.md §1.4).
    ///
    /// Contextual like every keyword here. The two bodies are told apart by
    /// one token after the spec type, as an instance's two bodies are.
    fn datarepr_decl(&mut self) -> R<DatareprDecl> {
        let start = self.peek_span();
        self.bump(); // `datarepr`
        let (name, _) = self.ident("the repr's name")?;
        if !self.eat_kw("for") {
            return self.err(&format!(
                "`for` and then the spec type (`datarepr {name} for List<Tok> := \
                 repr::naive();`): a repr is a representation *of* something, so the \
                 something is written"
            ));
        }
        let spec = self.with_record_lit(true, |p| p.ty())?;
        if matches!(self.peek(), TokKind::ColonEq) {
            self.bump();
            let e = self.expr()?;
            let mut end = e.span;
            if matches!(self.peek(), TokKind::Semi) {
                end = self.peek_span();
                self.bump();
            }
            return Ok(DatareprDecl {
                name,
                spec,
                body: DatareprBody::Mint(e),
                span: start.join(end),
            });
        }
        self.expect(&TokKind::LBrace, "`{` (the repr's clauses) or `:=` (a minted repr)")?;
        let fields = self.datarepr_clauses()?;
        let end = self.expect(&TokKind::RBrace, "`}` (the repr's clauses)")?;
        Ok(DatareprDecl {
            name,
            spec,
            body: DatareprBody::Fields(fields),
            span: start.join(end),
        })
    }

    /// The `name := expr` / `mk C := expr` clause list shared by `datarepr`
    /// and `impl`. The caller owns the braces.
    fn datarepr_clauses(&mut self) -> R<Vec<DatareprField>> {
        let mut fields = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let fstart = self.peek_span();
            // `mk Cons := …`. `mk` is contextual here too, and unambiguous:
            // a record field named `mk` would be `mk := …`, with `:=` where
            // the constructor's name stands.
            let is_mk = self.at_kw("mk")
                && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Ident(_)));
            if is_mk {
                self.bump();
            }
            let (fname, _) = self.ident(if is_mk {
                "the spec constructor this image is for"
            } else {
                "a clause name (`abs := …`)"
            })?;
            self.expect(&TokKind::ColonEq, "`:=` (a repr clause)")?;
            let expr = self.expr()?;
            let span = fstart.join(expr.span);
            fields.push(DatareprField { is_mk, name: fname, expr, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        Ok(fields)
    }

    /// `impl f for Rp { body := …, refines := … }`
    /// (docs/native/datarepr-design.md §1.2).
    fn impl_decl(&mut self) -> R<ImplDecl> {
        let start = self.peek_span();
        self.bump(); // `impl`
        let (op, _) = self.ident("the spec function this implements")?;
        if !self.eat_kw("for") {
            return self.err(&format!(
                "`for` and then the repr (`impl {op} for BinNat {{ … }}`): an \
                 implementation is an implementation *at* a representation"
            ));
        }
        let (repr, _) = self.ident("the repr's name")?;
        // `:= derive();` — a route, told from the clause list by one token,
        // exactly as a minted `datarepr` is.
        if matches!(self.peek(), TokKind::ColonEq) {
            self.bump();
            let e = self.expr()?;
            let mut end = e.span;
            if matches!(self.peek(), TokKind::Semi) {
                end = self.peek_span();
                self.bump();
            }
            return Ok(ImplDecl {
                op,
                repr,
                body: DatareprBody::Mint(e),
                span: start.join(end),
            });
        }
        self.expect(&TokKind::LBrace, "`{` (the implementation's clauses) or `:=` (a route)")?;
        let fields = self.datarepr_clauses()?;
        let end = self.expect(&TokKind::RBrace, "`}` (the implementation's clauses)")?;
        Ok(ImplDecl { op, repr, body: DatareprBody::Fields(fields), span: start.join(end) })
    }

    /// `instance<A, B> C<T> requires m: D<A> { … }`
    /// (docs/language/classes/traits-layer1-design.md §1, §4).
    fn instance_decl(&mut self) -> R<InstanceDecl> {
        let start = self.peek_span();
        self.bump(); // `instance`
        let (tyvars, constraints) = self.typaram_list()?;
        // `instance(n, m: Nat) Decide<Le(n, m)>` — the **value binders**
        // (docs/language/classes/value-generic-instances-design.md §2). A parameter list rather
        // than a trailing `forall`, because `(` after `instance` begins nothing
        // else: the head is a class reference and a class reference starts with
        // an identifier. That is the parse constraint `requires n: Nat` fails
        // (docs/language/surface-value-parameters.md §1) and this position does not.
        //
        // Marked implicit here, at the one place both spellings of an instance
        // pass through: a use site never writes them, since resolution recovers
        // them by unifying the head against the goal.
        let valparams: Vec<Param> = self
            .valparam_list(false, false)?
            .into_iter()
            .map(|p| Param { implicit: true, ..p })
            .collect();
        let class = self.class_ref("the class this instance is of")?;
        // `requires ma: Monoid<A>, mb: Monoid<B>` — no parentheses, because the
        // list is not an argument list: at layer 1 these are ordinary explicit
        // parameters of every member and of the assembled value.
        //
        // `instance<A: Mag> …` is the same list written at the binder: the
        // constraints lead, then the written `requires` binders, one order for
        // both spellings.
        let mut requires = constraints;
        requires.extend(self.requires_list()?);
        let open = self.expect(&TokKind::LBrace, "`{` (the instance body)")?;
        // One token decides the body form (docs/language/classes/traits-layer1-design.md §1):
        // a member is a declaration, a literal field is an assignment, and one
        // brace never holds both.
        let is_block =
            self.at_kw("fn") || self.at_kw("theorem") || self.at_kw("meta");
        let body = if is_block {
            let mut members = Vec::new();
            while !matches!(self.peek(), TokKind::RBrace) {
                if !(self.at_kw("fn") || self.at_kw("theorem") || self.at_kw("meta")) {
                    return self.err(
                        "an instance body is either a block of `fn`/`theorem` members or a \
                         list of `field := expr`, never both \
                         (docs/language/classes/traits-layer1-design.md §1)",
                    );
                }
                members.push(self.decl()?);
            }
            InstanceBody::Block(members)
        } else {
            let mut fields = Vec::new();
            while !matches!(self.peek(), TokKind::RBrace) {
                let (fname, fsp) = self.ident("a field name (`op := Rat::add`)")?;
                self.expect(
                    &TokKind::ColonEq,
                    "`:=` (an instance's literal field is `op := e`; `:` is the record \
                     literal's spelling and would be ambiguous here)",
                )?;
                let expr = self.expr()?;
                let span = fsp.join(expr.span);
                fields.push(InstanceField { name: fname, expr, span });
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            InstanceBody::Literal(fields)
        };
        let end = self.expect(&TokKind::RBrace, "`}` to close the instance body")?;
        let _ = open;
        Ok(InstanceDecl { tyvars, valparams, class, requires, body, span: start.join(end) })
    }

    /// `requires ma: Monoid<A>, Monoid<B>`, or nothing — the class
    /// spelling of a **solver parameter** (docs/language/classes/traits-layer2-design.md §1).
    /// No parentheses, because the list is not an argument list; every binder
    /// desugars to a leading implicit parameter with `Solver::Infer`, which is
    /// the one representation both spellings and both declaration forms share.
    fn requires_list(&mut self) -> R<Vec<Param>> {
        let mut requires = Vec::new();
        if !self.eat_kw("requires") {
            return Ok(requires);
        }
        loop {
            // `requires C<A>` is the anonymous form. A colon immediately
            // after the first identifier selects the named form; every class
            // reference otherwise consumes its own complete `<…>` and
            // optional index list before the comma or value-parameter list.
            let named = matches!(self.peek(), TokKind::Ident(_))
                && matches!(self.nth(1), TokKind::Colon);
            let (pname, psp) = if named {
                let (name, span) = self.binder_ident("a `requires` binder name")?;
                self.bump(); // `:`
                (name, span)
            } else {
                (self.hygienic("requires"), self.peek_span())
            };
            // A **class reference**, not a general type: `requires` is the
            // class spelling of a solver parameter, and the general one is
            // `p: T := infer`. The restriction is also what keeps the list
            // parseable in front of a parameter list — `Mag<A> (x: A)` would
            // otherwise read as a value-parameter application
            // (docs/language/surface-value-parameters.md §1).
            let cref = self.class_ref("the class a `requires` binder is of")?;
            let ty = class_ty(cref.name, cref.args, cref.index, cref.span);
            let span = psp.join(ty.span);
            requires.push(Param {
                name: pname,
                ty,
                implicit: true,
                is_self: false,
                solver: Some(Solver::Infer),
                default: None,
                origin: if named { ParamOrigin::Written } else { ParamOrigin::InlineConstraint },
                symbol: None,
                span,
            });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        Ok(requires)
    }

    /// `<A, B: Type<1>, C: Monoid + Cmp>` after `instance` or a declaration
    /// name, or nothing — the one production every type-parameter bracket uses.
    ///
    /// Two nouns share the colon (issues/requires-placement-syntax.md §R2-A):
    /// `A: Type<n>` says **where** `A` lives, `A: Monoid` says **what** it
    /// carries, and the head word tells them apart — `Type` is the universe
    /// noun, every other name is a class. They stack with `+`, so
    /// `<A: Type<1> + Monoid>` says both.
    ///
    /// A constraint is not a new elaborator concept: `A: C` desugars, here, to
    /// the parameter `requires _: C<A>` would have produced — implicit,
    /// `Solver::Infer`, at the front of the value-parameter list — with a
    /// compiler-generated `#`-prefixed name, which is unspellable, because the
    /// inline form deliberately offers no way to project the dictionary. The
    /// body that needs a name writes `requires`; both may appear on one
    /// declaration, and the constraints come first.
    fn typaram_list(&mut self) -> R<(Vec<TyParam>, Vec<Param>)> {
        let mut tyvars = Vec::new();
        let mut constraints = Vec::new();
        if !matches!(self.peek(), TokKind::Lt) {
            return Ok((tyvars, constraints));
        }
        self.bump();
        loop {
            let (tv, tvsp) = self.binder_ident("type parameter name")?;
            if tv == "self" {
                // Type arguments are never passed at a call site
                // (issues/at-and-type-arguments.md), so there is no slot here
                // for a receiver either.
                return Err(ParseError {
                    msg: "a type parameter cannot be `self`: type arguments are never \
                          passed at a call site, so there is nothing for a receiver to \
                          fill"
                        .into(),
                    span: tvsp,
                });
            }
            let mut level = 0;
            if matches!(self.peek(), TokKind::Colon) {
                self.bump();
                // `Type` first, if it is there at all: the universe annotation
                // is one entry in the `+` list and, being a statement about
                // where `A` lives rather than about what it carries, it can
                // only be the leading one.
                let mut classes = true;
                if self.at_kw("Type") {
                    let Some((n, _)) = self.univ()? else { unreachable!() };
                    level = n;
                    classes = matches!(self.peek(), TokKind::Plus);
                    if classes {
                        self.bump(); // `+`
                    }
                }
                while classes {
                    let n = constraints.len();
                    constraints.push(self.constraint(&tv, tvsp, n)?);
                    classes = matches!(self.peek(), TokKind::Plus);
                    if classes {
                        self.bump();
                    }
                }
            }
            tyvars.push(TyParam { name: tv, level, span: tvsp });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::Gt, "`>` to close the type parameters")?;
        Ok((tyvars, constraints))
    }

    /// One entry of a `<A: C1 + C2>` list: a class name, optionally with the
    /// arguments that follow its carrier. `A: C` is `C<A>` and `A: C<X>` is
    /// `C<A, X>` — the annotated binder is always the class's FIRST argument,
    /// which is what makes the inline form a *hoist* of the sentence `A: C`
    /// rather than a second feature.
    fn constraint(&mut self, tyvar: &str, tyvar_span: Span, ix: usize) -> R<Param> {
        if !matches!(self.peek(), TokKind::Ident(_)) {
            return self.err(&format!(
                "a type parameter's annotation is either a universe — \
                 `<{tyvar}: Type<n>>`, or `<{tyvar}>` for `Type<0>` — or a class \
                 constraint, `<{tyvar}: Monoid>`, stacked with `+`"
            ));
        }
        if self.at_kw("Type") {
            return self.err(&format!(
                "`Type` is the universe annotation and can only lead the list: write \
                 `<{tyvar}: Type<n> + C>`, not `<{tyvar}: C + Type<n>>`"
            ));
        }
        let (name, nsp) = self.qual_ident("a class name (`<A: Monoid>`)")?;
        let mut args = vec![Ty {
            kind: TyKind::Named { name: tyvar.to_string(), args: Vec::new() },
            span: tyvar_span,
        }];
        let mut end = nsp;
        if matches!(self.peek(), TokKind::Lt) {
            self.bump();
            loop {
                let a = self.with_record_lit(true, |p| p.ty())?;
                // `A: Coe<_, B>` — the carrier moved to a slot other than the
                // first. Deliberately NOT decided
                // (issues/requires-placement-syntax.md, log 2026-08-07), so it
                // is refused by name rather than parsed into something else.
                let wild = matches!(&a.kind, TyKind::Named { name, args }
                    if name == "_" && args.is_empty());
                if wild {
                    return Err(ParseError {
                        msg: "`_` in a constraint's arguments is not implemented: the \
                              inline form always puts the annotated parameter in the \
                              class's FIRST slot (`A: C<X>` is `C<A, X>`). A \
                              multi-parameter class whose carrier sits elsewhere is \
                              written `requires m: C<X, A>`"
                            .into(),
                        span: a.span,
                    });
                }
                args.push(a);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            end = self.expect(&TokKind::Gt, "`>` to close the class arguments")?;
        }
        // `<A: Monoid(op)>` — the index slot's NAME referent
        // (docs/language/classes/operation-indexed-classes-design.md §4.1): the index is linked
        // to an explicit parameter of this same declaration, forward reference
        // allowed. An empty slot is the absence of this list, and
        // `<A: Monoid(+)>` is the SYMBOL referent, the designation the binder
        // names (docs/language/classes/operators-onto-classes-design.md §5).
        let mut index = Vec::new();
        if matches!(self.peek(), TokKind::LParen) {
            self.bump();
            while !matches!(self.peek(), TokKind::RParen) {
                match self.op_symbol_arg() {
                    Some(e) => index.push(e),
                    None => index.push(self.expr()?),
                }
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            end = self.expect(&TokKind::RParen, "`)` to close the constraint's index")?;
        }
        if self.at_kw("as") {
            return self.err(
                "naming a constraint (`<A: Monoid as m>`) is not implemented: an inline \
                 constraint is always anonymous. A declaration whose body projects the \
                 dictionary writes `requires m: Monoid<A>`, which may sit on the same \
                 declaration as inline constraints",
            );
        }
        let span = tyvar_span.join(end);
        Ok(Param {
            // Unspellable by construction: `#` never begins an identifier, so
            // nothing in a body can reach this dictionary by name.
            name: format!("#constraint{ix}"),
            ty: class_ty(name, args, index, span),
            implicit: true,
            is_self: false,
            solver: Some(Solver::Infer),
            default: None,
            origin: ParamOrigin::InlineConstraint,
            symbol: None,
            span,
        })
    }

    /// `import nat;` or `import option::{Option, map};`
    /// (docs/language/modules-design.md §3.1). Single-segment module names only: there
    /// is no `std::nat` in v1, and no glob form — plain `import m;` already
    /// brings all of `m` into scope unqualified, so a glob would be a second
    /// spelling of it.
    fn import(&mut self) -> R<ImportItem> {
        let reexport = self.at_kw("export");
        let start = self.bump().span; // `import` or `export`
        // `export import m;`, the whole-module reexport.
        let whole = reexport && self.at_kw("import");
        if whole {
            self.bump();
        }
        let (module, module_span) = self.qual_ident("module name after `import`")?;
        if module.contains("::") {
            return Err(ParseError {
                msg: format!(
                    "`import {module};` imports nothing: a single name is written as a \
                     list, `import {}::{{{}}};`, and module names have one segment",
                    module.split("::").next().unwrap_or(""),
                    module.split("::").nth(1).unwrap_or("")
                ),
                span: module_span,
            });
        }
        let mut listed = Vec::new();
        if matches!(self.peek(), TokKind::ColonColon) {
            self.bump();
            self.expect(&TokKind::LBrace, "`{` (an import list is `m::{a, b}`)")?;
            while !matches!(self.peek(), TokKind::RBrace) {
                if matches!(self.peek(), TokKind::Star) {
                    return self.err(
                        "there is no glob import: `import m;` already brings all of \
                         `m` into scope unqualified (docs/language/modules-design.md §3.1)",
                    );
                }
                listed.push(if reexport { self.qual_ident("a name in the export list")? }
                    else { self.ident("a name in the import list")? });
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::RBrace, "`}` to close the import list")?;
        }
        if whole && !listed.is_empty() {
            return self.err("`export import m;` reexports all of `m`: a list is `export m::{Name};`");
        }
        if reexport && !whole && listed.is_empty() {
            return self.err("an export needs an explicit nonempty list, `export m::{Name};`, \
                             or is the whole module, `export import m;`");
        }
        let end = self.expect(&TokKind::Semi, "`;` to end the import")?;
        Ok(ImportItem { reexport, whole, module, module_span, listed, span: start.join(end) })
    }

    /// A field written `x: Pos<A>`, expanded: `x: A`, then `x_pos: 0 < x`,
    /// filled at a construction that leaves it out by the search `:= infer`
    /// runs, over the constructing scope (docs/library/positivity-evidence-design.md
    /// §6 B). Any other field comes back as it was. A record's and a
    /// constructor's field expand alike; only the record also gets a rule.
    fn pos_field(&self, f: FieldDecl) -> R<Vec<FieldDecl>> {
        let Some(carrier) = pos_carrier(&f.ty).cloned() else { return Ok(vec![f]) };
        let refuse = |msg: &str| Err(ParseError { msg: msg.to_string(), span: f.span });
        // Only a constructor's field can be unnamed; a record refused it
        // already.
        let Some(fname) = f.name.clone() else {
            return refuse(
                "a `Pos<A>` field needs a name (`n: Pos<Nat>`): its fact is `n_pos`, \
                 named after it",
            );
        };
        if f.default.is_some() {
            return refuse(
                "a `Pos<A>` field takes no default: its positivity is searched at \
                 each construction, and the value is the constructor's to pass",
            );
        }
        let ty_span = f.ty.span;
        Ok(vec![
            FieldDecl { name: f.name, ty: carrier, default: None, span: f.span },
            FieldDecl {
                name: Some(positivity_name(&fname)),
                ty: positivity_ty(&fname, ty_span),
                default: Some(Box::new(Expr { kind: ExprKind::Var(POS_SEARCH.into()), span: ty_span })),
                span: ty_span,
            },
        ])
    }

    /// `record D<p, …>(v: T, …) { f: T, … }` — desugared here into the
    /// one-constructor `InductiveDecl` the tier-0 generator already handles
    /// (docs/language/surface-records.md §2.1), with the constructor named after the
    /// record. What makes it a distinct *surface* form is the checks the flag
    /// earns downstream, not a distinct lowering.
    ///
    /// Every field must be named: `record D { Nat }` has nothing to project.
    fn record(&mut self) -> R<InductiveDecl> {
        let start = self.peek_span();
        self.bump(); // `record`
        // `record Target::Held(self t: Target, …) { … }`: a record may be
        // declared in a type's namespace, as a `fn Target::m` is, and is then
        // applied as `t.Held(…)` (issues/record-in-type-namespace.md,
        // docs/language/modules-design.md §4). As at a declaration head, the
        // parser lets one qualifier through and the elaborator checks that it
        // names a type.
        let (name, name_span) = self.qual_ident("record name")?;
        if name.matches("::").count() > 1 {
            return Err(ParseError {
                msg: format!(
                    "`{name}` has more than one qualifier: a record is declared in \
                     exactly one type's namespace, `Type::Name`"
                ),
                span: name_span,
            });
        }
        // `record R<A: Type<1>, X>`: a parameter declared at a universe is a
        // type the record's own type parameters (which live at `Type<0>`)
        // cannot hold, so it becomes a leading value parameter at that
        // universe, the way a class carrier declared at one does. A use site
        // still writes it in the angle brackets (`R<Omega, Nat>(…)`): the
        // elaborator reads angle arguments past the type parameters as these
        // leading values (issues/record-universe-parameters.md).
        let (named, kinds) = self.class_tyvar_list()?;
        let mut params = Vec::new();
        let mut valparams = Vec::new();
        for (p, kind) in named.into_iter().zip(kinds) {
            match kind {
                None => params.push(p),
                Some(ty) if matches!(ty.kind, TyKind::Univ { .. }) => {
                    if !params.is_empty() {
                        return Err(ParseError {
                            msg: format!(
                                "a record's parameters at a universe lead its type parameters: \
                                 write `{p}` before `{}`",
                                params[0]
                            ),
                            span: ty.span,
                        });
                    }
                    valparams.push(Param {
                        name: p,
                        span: ty.span,
                        ty,
                        implicit: false,
                        is_self: false,
                        solver: None,
                        default: None,
                        origin: ParamOrigin::Written,
                        symbol: None,
                    });
                }
                Some(ty) => {
                    return Err(ParseError {
                        msg: format!(
                            "a record's type parameter is annotated only with a universe \
                             (`<{p}: Type<1>>`); a type-constructor parameter is a class's"
                        ),
                        span: ty.span,
                    });
                }
            }
        }
        self.record_self = true;
        let written = self.valparam_list(false, true);
        self.record_self = false;
        let written = written?;
        // A method call puts its receiver in the first positional argument
        // of a record's type, so `self` is that one: what a `fn` reads off
        // its parameter metadata, a record's type former does not keep.
        if let Some(p) = written.iter().skip(1).find(|p| p.is_self) {
            return Err(ParseError {
                msg: format!(
                    "a record's `self` is its first value parameter, which is where a \
                     method call puts the receiver: write `self {}` first",
                    p.name
                ),
                span: p.span,
            });
        }
        valparams.extend(written);
        let varies = self.varies_clause()?;
        self.expect(&TokKind::LBrace, "`{` (field list)")?;
        let mut fields = Vec::new();
        let mut facts = Vec::new();
        // Where each field's tokens begin and end, for the parameter check below.
        let mut field_toks = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let from = self.pos;
            let f = self.field()?;
            field_toks.push(from..self.pos);
            if f.name.is_none() {
                return Err(ParseError {
                    msg: "a record field needs a name (`unit: Nat`): the name is what \
                          `m.unit` projects by"
                        .into(),
                    span: f.span,
                });
            }
            // `den: Pos<A>` — the field half of the binder sugar
            // (docs/library/positivity-evidence-design.md §6 B), with a rule about
            // the projection declared after the record.
            if pos_carrier(&f.ty).is_some() {
                let fname = f.name.clone().unwrap_or_default();
                let ty_span = f.ty.span;
                fields.extend(self.pos_field(f)?);
                facts.push((fname.clone(), positivity_name(&fname), ty_span));
            } else {
                fields.push(f);
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}` (field list)")?;
        let span = start.join(end);
        // The rule below finds the record's parameters by unifying its type,
        // and a parameter no field mentions leaves nothing to unify: `R(3)`
        // and `R(5)` lower to one type (docs/language/surface-value-parameters.md §6).
        // Read off the tokens, conservatively: any mention counts, the
        // field's own name included.
        if let Some((_, _, fspan)) = facts.first() {
            let mentioned = |p: &str| {
                field_toks.iter().flat_map(|r| &self.toks[r.clone()])
                    .any(|t| matches!(&t.kind, TokKind::Ident(n) if n == p))
            };
            let all = params.iter().cloned().chain(valparams.iter().map(|v| v.name.clone()));
            if let Some(p) = all.into_iter().find(|p| !mentioned(p)) {
                return Err(ParseError {
                    msg: format!(
                        "a `Pos<A>` field needs every parameter of `{name}` to appear in a \
                         field's type, and `{p}` appears in none: its rule `0 < r.field` \
                         finds the parameters by unifying the record's type, and with `{p}` \
                         unused every instantiation of `{name}` is one type"
                    ),
                    span: *fspan,
                });
            }
        }
        // One rule per positive field, `0 < r.den` from `r.den_pos`: a
        // projection of a local is not itself in scope, so without it the
        // search could not read the field's fact. On a parameterised record
        // the rule is generic in its type parameters and takes its value
        // parameters as `{}` implicits ahead of the record:
        // `<A>({k: Nat}, {r: R<A>(k)}): 0 < r.den`. All of them are solved by
        // unifying the record's type, checked above.
        for (field, fact, fspan) in facts {
            let var = |n: &str| Expr { kind: ExprKind::Var(n.to_string()), span: fspan };
            let recv = self.hygienic("record");
            let tyargs: Vec<Ty> = params
                .iter()
                .map(|p| Ty { kind: TyKind::Named { name: p.clone(), args: Vec::new() }, span: fspan })
                .collect();
            let recv_ty = if valparams.is_empty() {
                Ty { kind: TyKind::Named { name: name.clone(), args: tyargs }, span: fspan }
            } else {
                let head = if tyargs.is_empty() {
                    var(&name)
                } else {
                    Expr { kind: ExprKind::TyApp { head: Box::new(var(&name)), args: tyargs }, span: fspan }
                };
                let applied = Expr {
                    kind: ExprKind::App {
                        head: Box::new(head),
                        args: valparams.iter().map(|v| var(&v.name)).collect(),
                        named: Vec::new(),
                        explicit: false,
                        goal_oriented: false,
                    },
                    span: fspan,
                };
                Ty { kind: TyKind::OfExpr(Box::new(applied)), span: fspan }
            };
            let mut rparams: Vec<Param> = valparams
                .iter()
                .map(|v| Param {
                    implicit: true,
                    is_self: false,
                    solver: None,
                    default: None,
                    origin: ParamOrigin::Written,
                    symbol: None,
                    span: fspan,
                    ..v.clone()
                })
                .collect();
            rparams.push(Param {
                name: recv.clone(),
                ty: recv_ty,
                implicit: true,
                is_self: false,
                solver: None,
                default: None,
                origin: ParamOrigin::Written,
                symbol: None,
                span: fspan,
            });
            let project = |n: &str| Expr {
                kind: ExprKind::Dot {
                    recv: Box::new(var(&recv)),
                    name: n.to_string(),
                    tyargs: Vec::new(),
                    args: None,
                    named: Vec::new(),
                },
                span: fspan,
            };
            let zero = Expr { kind: ExprKind::Num(Numeral::ZERO), span: fspan };
            let stmt = op_call("<", OpFixity::Infix, vec![zero, project(&field)], fspan);
            self.record_facts.push(Decl {
                kind: DeclKind::Theorem,
                is_meta: false,
                is_evidence: true,
                is_interface: false, partial: None,
            value: false,
                elaborates: None,
                name: format!("{name}::{field}_positive"),
                tyvars: params.iter().map(|p| TyParam { name: p.clone(), level: 0, span: fspan }).collect(),
                params: rparams,
                result: Ty { kind: TyKind::OfExpr(Box::new(stmt)), span: fspan },
                decreases: None,
                depth: None,
                unfolding: Vec::new(),
                body: Block { stmts: Vec::new(), result: Box::new(project(&fact)), ons: Vec::new(), span: fspan },
                span: fspan,
            });
        }
        let ctor = CtorDecl { name: name.clone(), fields, result: None, span };
        Ok(InductiveDecl {
            name,
            params,
            valparams,
            varies,
            ctors: vec![ctor],
            is_record: true,
            is_codata: false,
            index: None,
            span,
        })
    }

    /// `(p: T, …)` after a declaration name (and after its `<…>`), or nothing —
    /// the **value** parameter list (docs/language/surface-value-parameters.md §1).
    ///
    /// The position is free and unambiguous: before this grammar existed, a `(`
    /// here was `parse error: expected `{``, and `fn`/`theorem` share no
    /// grammar with `record`/`inductive` (they have their own inline binder
    /// loop). Every parameter must be named — a value parameter is referred to
    /// by name inside the field types, which is the whole point of it.
    ///
    /// `symbols` says whether a parameter here may carry `as ∙`
    /// (issues/binder-symbol-as-notation.md). True only at a **class** head,
    /// whose index parameter is a declaring binder with a body — the class's
    /// own field types — to install a spelling for. A `record`/`inductive`
    /// value parameter is refused by name rather than parsed and dropped:
    /// there is no customer for it, and silence would be the wrong answer.
    /// `defaults`: a `record`'s list, where a parameter may end `:= e`
    /// (issues/constraint-indices-from-carrier-designations.md): an **index
    /// default**, what fills the slot when a type application stops before
    /// it. Unlike a `fn` parameter's default it keeps its positional slot,
    /// and only a trailing run of parameters may have one, so an application
    /// omits a suffix and never a slot in the middle.
    fn valparam_list(&mut self, symbols: bool, defaults: bool) -> R<Vec<Param>> {
        let mut params = Vec::new();
        if !matches!(self.peek(), TokKind::LParen) {
            return Ok(params);
        }
        self.bump();
        while !matches!(self.peek(), TokKind::RParen) {
            // `(n, m: Nat)` — a run of names sharing one annotation, exactly as
            // a `fn`'s parameter list reads it (the run stops at the `:`, which
            // is why the same comma goes on separating binders after the type).
            // A name followed by `,` was a parse error here before, so the form
            // is strictly additive; it is shared because a reader who has
            // written `fn f(n, m: Nat)` has no way to know this list is a
            // different production.
            let mut names: Vec<(String, Span, Option<String>, bool)> = Vec::new();
            loop {
                // `self t: Target`: a record's value parameter a method call's
                // receiver fills, as at a `fn` (issues/record-in-type-namespace.md).
                // Only a record's list reads it; elsewhere `self` stays a name.
                let is_self = self.record_self
                    && self.at_kw("self")
                    && matches!(self.nth(1), TokKind::Ident(_));
                let self_sp = self.peek_span();
                if is_self {
                    self.bump();
                }
                let (n, span) = self.binder_ident("value parameter name")?;
                if is_self
                    && let Some(prev) = params.iter().find(|p: &&Param| p.is_self).map(|p| p.name.clone())
                        .or_else(|| names.iter().find(|(.., s)| *s).map(|(n, ..)| n.clone()))
                {
                    return Err(ParseError {
                        msg: format!("a record has at most one `self`, and `{prev}` is already it"),
                        span: self_sp.join(span),
                    });
                }
                let asp = self.peek_span();
                let symbol = self.binder_symbol(&n)?;
                if symbol.is_some() && !symbols {
                    return Err(ParseError {
                        msg: format!(
                            "`{n} as …` is a class head's device: it installs a body spelling \
                             for the declaration's own body, and a `record`'s value parameter \
                             is a term its *fields* mention rather than a binder with a body \
                             to spell (issues/binder-symbol-as-notation.md)"
                        ),
                        span: asp.join(self.peek_span()),
                    });
                }
                names.push((n, span, symbol, is_self));
                if !(matches!(self.peek(), TokKind::Comma)
                    && matches!(self.nth(1), TokKind::Ident(_)))
                {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::Colon, "`:` (a value parameter is `name: T`)")?;
            let ty = self.ty()?;
            let mut default = None;
            if matches!(self.peek(), TokKind::ColonEq) {
                let eq = self.bump().span;
                // A lone operator symbol before `,` or `)` is a designation
                // reference here as in an argument list: `same_a: A → A → Type := ≈`.
                let e = match self.op_symbol_arg() {
                    Some(sym) => sym,
                    None => self.expr()?,
                };
                if !defaults {
                    return Err(ParseError {
                        msg: "only a `record`'s value parameter takes a default (an index \
                              default, what fills the slot when a type application stops \
                              before it)"
                            .into(),
                        span: eq.join(e.span),
                    });
                }
                default = Some(Box::new(e));
            } else if defaults && params.iter().any(|p: &Param| p.default.is_some()) {
                return Err(ParseError {
                    msg: format!(
                        "`{}` follows a defaulted value parameter, so it needs a default \
                         too: an application omits a trailing run of indices, never one \
                         in the middle",
                        names[0].0
                    ),
                    span: names[0].1.join(ty.span),
                });
            }
            for (n, nsp, symbol, is_self) in names {
                params.push(Param {
                    name: n,
                    ty: ty.clone(),
                    implicit: false,
                    is_self,
                    solver: None,
                    default: default.clone(),
                    origin: ParamOrigin::Written,
                    symbol,
                    span: nsp.join(ty.span),
                });
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::RParen, "`)` to close the value parameters")?;
        Ok(params)
    }

    /// `varies A` after a declaration's parameter lists, or nothing
    /// (docs/language/classes/lambda-carrier-instances-design.md §7.1). `varies` is contextual:
    /// it is read only here, so it stays an ordinary identifier everywhere else.
    fn varies_clause(&mut self) -> R<Option<(String, Span)>> {
        if !self.at_kw("varies") {
            return Ok(None);
        }
        self.bump();
        let (name, span) = self.ident("the varying parameter's name after `varies`")?;
        Ok(Some((name, span)))
    }

    /// `<A, B>` after a declaration name, or nothing.
    fn tyvar_list(&mut self) -> R<Vec<String>> {
        let mut params = Vec::new();
        if matches!(self.peek(), TokKind::Lt) {
            self.bump();
            loop {
                params.push(self.binder_ident("type parameter name")?.0);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::Gt, "`>` to close the type parameters")?;
        }
        Ok(params)
    }

    /// `inductive D<p, …> { c(f: T, …), … }`. Zero constructors is legal (the
    /// empty type); so is a constructor with no field list.
    fn inductive(&mut self) -> R<InductiveDecl> {
        let start = self.peek_span();
        // `codata` shares the whole grammar: the constructors are written the
        // same way, and what they mean is the elaborator's
        // (docs/inductives/codata-elaborator-design.md §1).
        let is_codata = self.at_kw("codata");
        self.bump(); // `inductive` / `codata`
        let (name, _) = self.ident("inductive name")?;
        let params = self.tyvar_list()?;
        // Parsed, then rejected by the elaborator: value parameters are a
        // `record` form this round (docs/language/surface-value-parameters.md §6), and a
        // named rejection beats `expected `{`, found LParen`.
        let valparams = self.valparam_list(false, false)?;
        let varies = self.varies_clause()?;
        // `: (n: Nat) -> Type` — an index telescope
        // (docs/inductives/inductive-indexed-lowering.md §2). Parsed with the ordinary
        // type grammar; its shape is the elaborator's to validate.
        let index = if matches!(self.peek(), TokKind::Colon) {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        self.expect(&TokKind::LBrace, "`{` (constructor list)")?;
        let mut ctors = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let (cname, cspan) = self.binder_ident("constructor name")?;
            let mut fields = Vec::new();
            let mut span = cspan;
            if matches!(self.peek(), TokKind::LParen) {
                self.bump();
                while !matches!(self.peek(), TokKind::RParen) {
                    // `Some(n: Pos<Nat>)` — the record expansion, with no rule:
                    // a constructor's fields are reached by a pattern, which
                    // binds the fact as a local the search reads.
                    let f = self.field()?;
                    fields.extend(self.pos_field(f)?);
                    if !matches!(self.peek(), TokKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                span = span.join(self.expect(&TokKind::RParen, "`)` (field list)")?);
            }
            // `Nil : Vec<A>(0)` — a constructor's result annotation, an
            // expression by the same backtracking rule that makes `Vec<A>(0)`
            // an expression in type position (`ty_atom`): an applied type is
            // never called, so the call *is* the index application.
            let result = if matches!(self.peek(), TokKind::Colon) {
                self.bump();
                let r = self.expr()?;
                span = span.join(r.span);
                Some(r)
            } else {
                None
            };
            ctors.push(CtorDecl { name: cname, fields, result, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RBrace, "`}` (constructor list)")?;
        Ok(InductiveDecl {
            name,
            params,
            valparams,
            varies,
            ctors,
            is_record: false,
            is_codata,
            index,
            span: start.join(end),
        })
    }

    /// A constructor field: `name: T` or a bare `T`. Named fields are in scope
    /// in the later fields' types.
    fn field(&mut self) -> R<FieldDecl> {
        let start = self.peek_span();
        // `name :` — but only when the `:` really follows, since a bare type
        // is also an identifier (`Nat`).
        let named = matches!(self.peek(), TokKind::Ident(_))
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Colon));
        let name = if named {
            let (n, _) = self.binder_ident("field name")?;
            self.bump(); // `:`
            Some(n)
        } else {
            None
        };
        let ty = self.ty()?;
        // `:= e`: the field's default. Unambiguous here, as at a parameter:
        // nothing else follows a field's type with `:=`.
        let default = if name.is_some() && matches!(self.peek(), TokKind::ColonEq) {
            self.bump();
            Some(Box::new(self.expr()?))
        } else { None };
        let span = start.join(default.as_ref().map_or(ty.span, |e| e.span));
        Ok(FieldDecl { name, ty, default, span })
    }

    /// `(x: A, {n: Nat}, self s: S, h: P := infer, …)` — a declaration's
    /// value-parameter list, appended to `params` (its solver parameters, which
    /// lead). A section head reads the same list (docs/language/sections-design.md §5).
    fn param_list(&mut self, mut params: Vec<Param>) -> R<Vec<Param>> {
        self.expect(&TokKind::LParen, "`(`")?;
        while !matches!(self.peek(), TokKind::RParen) {
            // `{name: T}` marks an implicit parameter (filled by unification);
            // `name: T` is explicit.
            let implicit = matches!(self.peek(), TokKind::LBrace);
            if implicit {
                self.bump();
            }
            // `fn f(x, y: A)` — a run of names sharing one annotation, the
            // parameter-list half of issues/multi-binder-function-types.md.
            // A name followed by `,` was a parse error before this (every
            // parameter is annotated), so the form is strictly additive; and
            // the run stops at the `:`, which is why the same comma can go on
            // separating parameters after the type.
            //
            // A modifier prefixes exactly one name — the one it is written on
            // — so both modifiers are read per *entry*, inside the run
            // (issues/modifiers-in-shared-binder-runs.md). `self x, y: A`
            // marks `x` and leaves `y` an ordinary parameter of the same type,
            // and `g as ∙, h: A -> A -> A` gives the symbol to `g` alone. The
            // annotation is the only thing the run shares.
            let mut names: Vec<(String, Span, bool, Option<String>)> = Vec::new();
            loop {
                // `self p: T` marks the parameter a method receiver fills
                // (issues/method-receiver-position.md). `self: T` marks *and*
                // names it, so a record method reads the Rust way; there is no
                // third reading, which is what keeps a parameter merely named
                // `self` from silently not being the subject.
                // `mut x: T`, `mut self x: T` (docs/language/sequencing-surface-design.md
                // §8.2): the body may reassign `x`, and a `mut self`
                // receiver comes back out beside the result. Contextual: a
                // parameter named `mut` is still `mut: T`.
                let is_mut = self.at_kw("mut") && matches!(self.nth(1), TokKind::Ident(_));
                let mut_sp = self.peek_span();
                if is_mut {
                    if implicit {
                        return Err(ParseError {
                            msg: "an implicit parameter cannot be `mut`: it has no argument slot \
                                  to update".into(),
                            span: mut_sp,
                        });
                    }
                    self.bump();
                }
                let is_self = self.at_kw("self");
                let self_sp = self.peek_span();
                if is_self {
                    self.bump();
                }
                let (pname, psp) = if is_self && matches!(self.peek(), TokKind::Colon) {
                    ("self".to_string(), self_sp)
                } else {
                    self.binder_ident("parameter name")?
                };
                if is_self && implicit {
                    return Err(ParseError {
                        msg: "`self` cannot be implicit: an implicit parameter has no \
                              argument slot for the receiver to fill"
                            .into(),
                        span: self_sp.join(psp),
                    });
                }
                // At most one `self` per declaration — and the run itself has
                // to be scanned too, since its names are not pushed onto
                // `params` until the shared annotation is read.
                if is_self
                    && let Some(prev) = params
                        .iter()
                        .find(|p: &&Param| p.is_self)
                        .map(|p| p.name.clone())
                        .or_else(|| {
                            names.iter().find(|(_, _, s, _)| *s).map(|(n, ..)| n.clone())
                        })
                {
                    return Err(ParseError {
                        msg: format!(
                            "a declaration has at most one `self`, and `{prev}` is already it"
                        ),
                        span: self_sp.join(psp),
                    });
                }
                // `op as ∙: A -> A -> A` — the binder's body spelling
                // (issues/binder-symbol-as-notation.md). Read here, between
                // the name and the annotation (or the run's comma), because it
                // is a property of the *name*: the identifier stays the
                // interface (the constraint slot, every call site, every
                // diagnostic) and the symbol is local notation for the rest of
                // the telescope, the result type, and the body. Two names in
                // one run may each carry one; that two of them cannot be the
                // *same* symbol is the ordinary uniqueness rule, which the
                // elaborator runs per spelling.
                let symbol = self.binder_symbol(&pname)?;
                if is_mut {
                    self.mut_params.push((pname.clone(), is_self));
                }
                names.push((pname, psp, is_self, symbol));
                if !(matches!(self.peek(), TokKind::Comma)
                    && matches!(self.nth(1), TokKind::Ident(_)))
                {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::Colon, "`:`")?;
            let ty = self.ty()?;
            let mut span = names[0].1.join(ty.span);
            // `hx: P := infer` — a solver default
            // (docs/language/classes/traits-layer2-design.md §1) — or, with any other
            // expression after the `:=`, a parameter default
            // (docs/language/named-arguments-design.md §9.1). Unambiguous here: nothing
            // else follows a parameter's type with `:=`. `infer` stays the
            // solver keyword, so it is not a default naming something else.
            let mut solver = None;
            let mut default = None;
            if matches!(self.peek(), TokKind::ColonEq) {
                let eq = self.bump().span;
                let solver_kw = matches!(self.peek(), TokKind::Ident(n) if n == "infer")
                    && matches!(self.nth(1), TokKind::Comma | TokKind::RParen | TokKind::RBrace);
                let filled = if solver_kw {
                    let ssp = self.bump().span;
                    solver = Some(Solver::Infer);
                    ssp
                } else {
                    let e = self.expr()?;
                    let esp = e.span;
                    default = Some(Box::new(e));
                    esp
                };
                if implicit {
                    return Err(ParseError {
                        msg: if solver.is_some() {
                            "an implicit parameter is already filled by unification: \
                             `:= infer` is the other filling discipline, and a \
                             parameter has one"
                                .into()
                        } else {
                            "an implicit parameter is already filled by unification: \
                             a default is another filling discipline, and a parameter \
                             has one. Drop the braces: a defaulted parameter has no \
                             positional slot either (docs/language/named-arguments-design.md §9.2)"
                                .into()
                        },
                        span: eq.join(filled),
                    });
                }
                if names.iter().any(|(_, _, s, _)| *s) {
                    return Err(ParseError {
                        msg: format!(
                            "`self` cannot have {}: its argument is the receiver, which \
                             is never omitted",
                            if solver.is_some() { "a solver default" } else { "a default" }
                        ),
                        span: eq.join(filled),
                    });
                }
                span = span.join(filled);
            }
            if implicit {
                span = span.join(self.expect(&TokKind::RBrace, "`}` to close implicit parameter")?);
            }
            // A solver parameter has no positional slot: it is implicit, and
            // `@f(…)` is how it is passed by hand (§1). A defaulted one is
            // the same (docs/language/named-arguments-design.md §9.2).
            let implicit = implicit || solver.is_some() || default.is_some();
            // `x: Pos<A>` — binder sugar, not a type
            // (docs/library/positivity-evidence-design.md §6 B): the parameter is an
            // `A`, followed by `x_pos: 0 < x := infer`. Nothing is wrapped, so
            // a caller passes a plain `A` and the search finds its positivity;
            // `x_pos := …` names it by hand.
            let positive = pos_carrier(&ty).cloned();
            if positive.is_some() && (solver.is_some() || default.is_some()) {
                return Err(ParseError {
                    msg: "a `Pos<A>` parameter takes no default: its positivity is \
                          searched at each call, and the value is the caller's to pass"
                        .into(),
                    span,
                });
            }
            for (name, nsp, is_self, symbol) in names {
                let fact = positive.as_ref().map(|_| positivity_param(&name, ty.span));
                params.push(Param {
                    name,
                    ty: positive.clone().unwrap_or_else(|| ty.clone()),
                    implicit,
                    is_self,
                    solver,
                    default: default.clone(),
                    origin: ParamOrigin::Written,
                    symbol,
                    span: nsp.join(span),
                });
                params.extend(fact);
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::RParen, "`)`")?;
        Ok(params)
    }

    fn decl(&mut self) -> R<Decl> {
        let propagation_start = self.propagation_count;
        let start = self.peek_span();
        // `meta fn` — a layer-m declaration (docs/metaprogramming/in-language-map-design.md
        // §3). Only `fn`: a theorem is an opaque Ψ-global, and meta
        // definitions never reach Ψ, so `meta theorem` has no meaning.
        let is_meta = self.eat_kw("meta");
        // `evidence theorem` — contextual, like every keyword here: only the
        // word directly before `theorem` is the modifier, so a field or
        // binder named `evidence` elsewhere is untouched.
        let is_evidence = !is_meta
            && self.at_kw("evidence")
            && matches!(self.nth(1), TokKind::Ident(s) if s == "theorem");
        if is_evidence {
            self.bump();
        } else if self.at_kw("evidence")
            && matches!(self.nth(1), TokKind::Ident(s) if s == "fn" || s == "axiom" || s == "meta" || s == "def")
        {
            return self.err(
                "`evidence` marks a `theorem`: a rule is a proof `:= infer` applies \
                 (docs/library/positivity-evidence-design.md §6 A)",
            );
        }
        // `interface fn` — an interface definition
        // (docs/language/interface-definitions-design.md §1). Contextual: only the word
        // directly before a declaration keyword is the modifier.
        let is_interface = !is_meta
            && !is_evidence
            && self.at_kw("interface")
            && matches!(self.nth(1), TokKind::Ident(s) if s == "fn");
        if is_interface {
            self.bump();
        } else if !is_meta
            && !is_evidence
            && self.at_kw("interface")
            && matches!(self.nth(1), TokKind::Ident(s) if s == "theorem" || s == "def" || s == "axiom" || s == "meta")
        {
            return self.err(
                "`interface` marks a `fn`: a theorem is already opaque to its clients, and a \
                 `def` or `axiom` has no arguments a call could leave open \
                 (docs/language/interface-definitions-design.md §1)",
            );
        }
        // `def name: T = e;` — a value definition
        // (docs/metaprogramming/value-definitions-design.md §2). Contextual like every
        // keyword here: only `def` followed by a name, at an item's head.
        if self.at_kw("def") && matches!(self.nth(1), TokKind::Ident(_)) {
            if is_meta {
                return self.err("`meta` marks a `fn`: a `def` is an ordinary value");
            }
            return self.value_decl(start, propagation_start);
        }
        let kind = if self.eat_kw("fn") {
            DeclKind::Fn
        } else if !is_meta && self.eat_kw("theorem") {
            DeclKind::Theorem
        } else if !is_meta && self.eat_kw("axiom") {
            DeclKind::Axiom
        } else if is_meta {
            return self.err("`meta` marks a `fn`: write `meta fn name(…)`");
        } else {
            return self.err("expected `fn`, `theorem`, `def`, `axiom`, or `inductive`");
        };
        // A declaration head is the one *binding* position where a qualified
        // name is legal: `fn List::nth(…)` attaches the declaration to a
        // type's namespace (issues/type-owned-members-receiver-slice.md).
        // Whether the qualifier really names a type is the elaborator's to
        // check — the parser has no name tables — so all that happens here is
        // that the `::` is let through, with the arity of the path fixed at
        // one segment of qualifier.
        let (name, name_span) = self.qual_ident("declaration name")?;
        if name.matches("::").count() > 1 {
            return Err(ParseError {
                msg: format!(
                    "`{name}` has more than one qualifier: a member is attached to \
                     exactly one type, `Type::member`"
                ),
                span: name_span,
            });
        }
        // `fn map<A, B>(…)` — type parameters (docs/language/surface-polymorphism.md
        // §1). Unambiguous here: a declaration's name is always followed by
        // `(` or `<`, and neither is an expression continuation. `<A: Type<1>>`
        // annotates the universe the parameter ranges over
        // (docs/language/surface-universe.md §2); `<A: Monoid>` constrains what it
        // carries — one production, shared with the `instance` head.
        let (tyvars, constraints) = self.typaram_list()?;
        // `fn sum<A> requires m: Monoid<A> (xs: List<A>) -> A` — solver
        // parameters, the class spelling (docs/language/classes/traits-layer2-design.md §1).
        // They are moved to the front of the parameter list, because they are
        // what the later parameters' types mention; the same production the
        // `instance` head uses, and the same desugaring. Inline constraints are
        // those same parameters, and lead: `<A: Monoid> requires c: Cmp<A>`
        // binds the monoid first.
        let mut requires = constraints;
        requires.extend(self.requires_list()?);
        let leading = requires.len();
        self.mut_params.clear();
        let params = self.param_list(requires)?;
        let mut_params = std::mem::take(&mut self.mut_params);
        // `for vec.map` — the elaboration slot this template fills
        // (docs/metaprogramming/meta-def-registration-design.md §2.1). The parse point is
        // unambiguous: what follows a parameter list is `->` or `:`, never an
        // identifier, so the contextual keyword cannot be read as anything
        // else. The path's *vocabulary* is the elaborator's, so an unknown
        // slot is a registration diagnostic, not a parse error.
        let elaborates = if self.at_kw("for") {
            let start = self.bump().span;
            let (family, _) = self.ident("a slot family (`for vec.map`)")?;
            self.expect(&TokKind::Dot, "`.` (a slot is written `family.name`)")?;
            let (sname, nsp) = self.ident("a slot name (`for vec.map`)")?;
            let span = start.join(nsp);
            if !is_meta {
                return Err(ParseError {
                    msg: "`for` marks a `meta fn` as an elaboration template: an \
                          ordinary declaration elaborates nothing but itself"
                        .into(),
                    span,
                });
            }
            Some(SlotPath { family, name: sname, span })
        } else {
            None
        };
        match kind {
            DeclKind::Fn => {
                self.expect(&TokKind::Arrow, "`->`")?;
            }
            DeclKind::Theorem | DeclKind::Axiom => {
                self.expect(&TokKind::Colon, "`:`")?;
            }
        }
        // The declaration's body block follows immediately, so a `{` here
        // opens it, not a record literal in the last endpoint of a
        // `theorem t: a = D { … }` (docs/language/surface-records.md §6.1).
        let mut result = self.with_record_lit(true, |p| p.ty())?;
        // A `mut self` method returns its receiver beside its result
        // (docs/language/sequencing-surface-design.md §8.2): `fn Io::read(mut self io:
        // Io, …) → R` has kernel type `Io → … → Mutated<Io, R>`.
        let mut_self = mut_params.iter().find(|(_, s)| *s).map(|(n, _)| n.clone());
        if !mut_params.is_empty() && kind != DeclKind::Fn {
            return Err(ParseError {
                msg: "only a `fn` takes `mut` parameters: a theorem's parameters are not updated".into(),
                span: result.span,
            });
        }
        if let Some(receiver) = &mut_self {
            let receiver_ty = params.iter().find(|p| &p.name == receiver).map(|p| p.ty.clone())
                .expect("a `mut self` parameter is in the list");
            let span = result.span;
            result = Ty { kind: TyKind::Named { name: MUTATED_RECORD.into(), args: vec![receiver_ty, result] }, span };
        }
        // `decreases e` — a termination measure, before the body. Contextual,
        // like `requires`: an identifier can never follow a complete result
        // type, so the word is unambiguous here. The body's `{` must not be
        // swallowed as a record literal of the measure.
        let decreases = if self.eat_kw("decreases") {
            Some(self.with_record_lit(true, |p| p.expr())?)
        } else {
            None
        };
        // `depth ν` — a bound on how deep the recursion nests, beside its
        // measure (docs/native/runtime-fn-recursion-design.md §3.3).
        // Contextual, like `decreases`.
        let depth = if self.eat_kw("depth") {
            if decreases.is_none() {
                return self.err(
                    "a `depth` bound sits beside a `decreases` measure: `decreases μ depth ν`, \
                     each recursive call owing `ν(y) < ν(x)` as it owes `μ(y) < μ(x)`",
                );
            }
            Some(self.with_record_lit(true, |p| p.expr())?)
        } else {
            None
        };
        // `unfolding f, g` — see through these interface definitions in this
        // declaration (docs/language/interface-definitions-design.md §4). Contextual,
        // like `decreases`.
        let mut unfolding = Vec::new();
        if self.eat_kw("unfolding") {
            loop {
                let (name, _) = self.qual_ident("an interface definition's name")?;
                unfolding.push(name);
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
        }
        // The `given` clause — the constraint sentence written where its
        // subject is not a binder (`given List<A>: Monoid`) — is deliberately
        // NOT decided (issues/requires-placement-syntax.md, log 2026-08-07).
        // It is refused by name because this is exactly where a reader who
        // learned `<A: Monoid>` will try to write it.
        if self.at_kw("given") {
            return self.err(
                "a `given` clause is not implemented: the inline form `<A: Monoid>` \
                 constrains a type PARAMETER, and a constraint on anything else \
                 (`List<A>: Monoid`) is written `requires m: Monoid<List<A>>` before \
                 the parameter list (issues/requires-placement-syntax.md)",
            );
        }
        let body = if kind == DeclKind::Axiom {
            let end = self.expect(&TokKind::Semi, "`;` (an axiom has no proof body)")?;
            // `Decl` predates bodiless declarations and several syntax tools
            // deliberately operate on its always-present block.  Keep that
            // invariant with an unreachable sentinel; the elaborator and
            // lints branch on `kind` and never inspect it.
            Block {
                stmts: Vec::new(),
                result: Box::new(Expr {
                    kind: ExprKind::Var("#axiom".into()),
                    span: end,
                }),
                ons: Vec::new(),
                span: end,
            }
        } else {
            let saved = self.propagation_depth;
            self.propagation_depth = usize::from(!is_meta && kind == DeclKind::Fn);
            self.pending_mut = (!mut_params.is_empty()).then(|| mut_params.clone());
            self.own_method = mut_self.is_some().then(|| name.rsplit("::").next().unwrap_or(&name).to_string());
            let ahead = self.on_names_ahead();
            let on_names = std::mem::replace(&mut self.body_on_names, ahead);
            self.fn_body = true;
            let body = self.block();
            self.fn_body = false;
            self.body_on_names = on_names;
            self.pending_mut = None;
            self.own_method = None;
            self.propagation_depth = saved;
            body?
        };
        let body = if self.propagation_count != propagation_start {
            crate::try_lower::reject_type(&result)?;
            for p in &params { crate::try_lower::reject_type(&p.ty)?; }
            crate::try_lower::block(body, &mut self.next_hygienic)?
        } else { body };
        crate::try_lower::validate_decrease_labels(&body, decreases.is_some())?;
        crate::try_lower::reject_bind_in_type(&result)?;
        for p in &params { crate::try_lower::reject_bind_in_type(&p.ty)?; }
        let mut body = crate::imperative::lower_returns(body);
        // A `mut self` method's `return e` leaves with its receiver as it
        // stands there, `Mutated(x, e)`, as the body's own end does (§8.2).
        if let Some(receiver) = &mut_self {
            crate::imperative::return_receiver(&mut body, receiver, MUTATED_RECORD);
        }
        crate::imperative::reject_residue(&body)?;
        let (tyvars, params) = self.splice_sections(&name, name_span, tyvars, params, leading, &result)?;
        let span = start.join(body.span);
        Ok(Decl { kind, is_meta, is_evidence, is_interface, partial: None, value: false, elaborates, name, tyvars, params, result, decreases, depth, unfolding, body, span })
    }

    /// `def name<A>: T = e;`, `def name = e;` (docs/metaprogramming/value-definitions-design.md
    /// §2). A value is a [`DeclKind::Fn`] with no written parameters and the
    /// [`Decl::value`] flag; its body is the block `{ e }`. Without `: T` the
    /// result is [`TyKind::TypeOf`] the value. Type parameters and inline
    /// constraints are allowed (they are implicit, so the value is still used
    /// bare); a written parameter list is refused with the two spellings it
    /// could have meant.
    fn value_decl(&mut self, start: Span, propagation_start: usize) -> R<Decl> {
        self.bump(); // `def`
        let (name, name_span) = self.qual_ident("definition name")?;
        if name.matches("::").count() > 1 {
            return Err(ParseError {
                msg: format!(
                    "`{name}` has more than one qualifier: a member is attached to \
                     exactly one type, `Type::member`"
                ),
                span: name_span,
            });
        }
        let (tyvars, constraints) = self.typaram_list()?;
        if matches!(self.peek(), TokKind::LParen) {
            return self.err(&format!(
                "a `def` names a value and takes no parameters: write a function as \
                 `fn {name}(…) -> T {{ … }}`, or a function-typed value as \
                 `def {name}: A -> B = λ x => …;`"
            ));
        }
        if self.at_kw("requires") {
            return self.err(
                "a `def` takes no `requires` list: constrain its type parameters inline \
                 (`def unit<A: Monoid>: A = …;`)",
            );
        }
        let leading = constraints.len();
        let params = constraints;
        // The annotation, and only the annotation, with a top-level `=`
        // suppressed: `let`'s rule, so `def x: Nat = 5;` reads its value and
        // an equation type is written in parentheses.
        let annotated = if matches!(self.peek(), TokKind::Colon) {
            self.bump();
            Some(self.with_record_lit(true, |p| p.annotation())?)
        } else {
            None
        };
        if matches!(self.peek(), TokKind::LBrace) {
            return self.err("a `def`'s value follows `=`: `def name: T = e;`");
        }
        self.expect_eq("`def` value")?;
        let saved = self.propagation_depth;
        self.propagation_depth = 1;
        let value = self.expr();
        self.propagation_depth = saved;
        let value = value?;
        let end = self.expect(&TokKind::Semi, "`;` to end the `def`")?;
        let result = match annotated {
            Some(t) => t,
            None => Ty { kind: TyKind::TypeOf(Box::new(value.clone())), span: value.span },
        };
        let vspan = value.span;
        let body = Block { stmts: Vec::new(), result: Box::new(value), ons: Vec::new(), span: vspan };
        let body = if self.propagation_count != propagation_start {
            crate::try_lower::reject_type(&result)?;
            crate::try_lower::block(body, &mut self.next_hygienic)?
        } else { body };
        let (tyvars, params) = self.splice_sections(&name, name_span, tyvars, params, leading, &result)?;
        Ok(Decl {
            kind: DeclKind::Fn,
            is_meta: false,
            is_evidence: false,
            is_interface: false, partial: None,
            value: true,
            elaborates: None,
            name,
            tyvars,
            params,
            result,
            decreases: None,
            depth: None,
            unfolding: Vec::new(),
            body,
            span: start.join(end),
        })
    }

    // -- blocks and statements ----------------------------------------------

    fn block(&mut self) -> R<Block> {
        let open = self.expect(&TokKind::LBrace, "`{`")?;
        // Inside the braces nothing is waiting for a block, so a literal is
        // unambiguous again.
        let saved = std::mem::replace(&mut self.no_record_lit, false);
        let r = self.block_body(open);
        self.no_record_lit = saved;
        r
    }

    fn block_body(&mut self, open: Span) -> R<Block> {
        let pending = self.pending_mut.take();
        let fn_body = std::mem::take(&mut self.fn_body);
        let defer = std::mem::take(&mut self.defer_binds);
        let saved = self.mutables.len();
        let receiver = pending.as_ref().and_then(|ps| ps.iter().find(|(_, s)| *s)).map(|(n, _)| n.clone());
        if let Some(ps) = &pending {
            self.mutables.extend(ps.iter().map(|(n, _)| n.clone()));
        }
        let block = self.block_body_in(open, pending);
        self.mutables.truncate(saved);
        let block = if fn_body {
            // `return e` outside a loop ends the body (§5.5); in a `mut
            // self` method it leaves with the receiver as it stands there,
            // as the body's own end does (§8.2).
            let ret = |value: Expr| match &receiver {
                Some(x) => {
                    let span = value.span;
                    Expr {
                        kind: ExprKind::App {
                            head: Box::new(Expr { kind: ExprKind::Var(MUTATED_RECORD.into()), span }),
                            args: vec![Expr { kind: ExprKind::Var(x.clone()), span }, value],
                            named: vec![], explicit: false, goal_oriented: false,
                        },
                        span,
                    }
                }
                None => value,
            };
            crate::imperative::lower_body(block?, &ret, &mut self.next_hygienic)?
        } else {
            crate::imperative::lower_block(block?, &mut self.next_hygienic)?
        };
        if defer {
            return Ok(block);
        }
        crate::try_lower::binds_in_block(block, &mut self.next_hygienic)
    }

    /// Is `e` a method call on a `let mut` local or `mut` parameter in
    /// scope: one that may update its receiver (§8.2)?
    fn mut_receiver(&self, e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::Dot { recv, args: Some(_), .. }
            if crate::imperative::place_root(recv).is_some_and(|x| self.mutables.iter().any(|m| m == x)))
    }

    /// [`Self::block_body`] before its layer-2 statements and binds are
    /// lowered: the statements, and a `mut` parameter list's bindings when
    /// this is a function's body.
    fn block_body_in(&mut self, open: Span, pending: Option<Vec<(String, bool)>>) -> R<Block> {
        let mut stmts = Vec::new();
        // `{}` — an empty proof block, whose result is the elaborator's one
        // speculative `refl` (issues/auto-refl-empty-block.md). Read here,
        // before the statements, so that the trigger is *exactly* empty
        // braces: `{ let x = 1; }` is still the missing-result parse error it
        // was, since a block with work in it that closes a goal by computation
        // is not the case this feature is about.
        if matches!(self.peek(), TokKind::RBrace) {
            let close = self.expect(&TokKind::RBrace, "`}`")?;
            let span = open.join(close);
            return Ok(Block {
                stmts,
                result: Box::new(Expr { kind: ExprKind::AutoRefl, span }),
                ons: Vec::new(),
                span,
            });
        }
        let parsed = self.block_statements(&mut stmts)?;
        let mut block = self.block_tail(open, stmts, parsed)?;
        // A result that updates its receiver is bound first, so the local
        // is updated before the block ends (§8.2).
        if self.mut_receiver(&block.result) {
            let span = block.result.span;
            let name = self.hygienic("tail");
            let call = std::mem::replace(&mut *block.result, Expr { kind: ExprKind::Var(name.clone()), span });
            block.stmts.push(Stmt::Let {
                name, ty: None, expr: crate::imperative::marked(crate::imperative::MUTCALL, call, span), span, opaque: false,
            });
        }
        if let Some(ps) = pending {
            // `mut x` is `let mut x = x;` at the body's head; a `mut self`
            // receiver is returned beside the body's value,
            // `Mutated(x, value)`.
            let mut head: Vec<Stmt> = ps.iter().map(|(n, _)| {
                let x = Expr { kind: ExprKind::Var(n.clone()), span: open };
                Stmt::Let { name: n.clone(), ty: None, expr: crate::imperative::marked(crate::imperative::MUT, x, open), span: open, opaque: false }
            }).collect();
            head.append(&mut block.stmts);
            block.stmts = head;
            if let Some((receiver, _)) = ps.iter().find(|(_, s)| *s) {
                self.receiver_end(&mut block, receiver);
            }
        }
        Ok(block)
    }

    /// The end of a `mut self` body, where the receiver `x` goes back out
    /// beside the body's value: `Mutated(x, value)`, the value bound first
    /// (§8.2).
    ///
    /// A body that ends in a branch one of whose arms updates the receiver
    /// returns it at the end of each arm instead (§19.2), since the
    /// receiver after the branch is a different one per arm: each arm ends
    /// as a body does, and [`crate::imperative::lower_block`] gives its
    /// statements the body's mutable locals. The method's own call on the
    /// receiver, where it ends the body or such an arm, is the whole result
    /// ([`crate::imperative::MUTATED_WHOLE`]), so the recursion is a tail
    /// call.
    fn receiver_end(&mut self, block: &mut Block, receiver: &str) {
        if let ExprKind::Match { motive: None, arms, eqbind, .. } = &mut block.result.kind
            && crate::imperative::tail_updates(arms, eqbind.as_deref(), receiver)
        {
            for arm in arms.iter_mut() {
                let span = arm.body.span;
                let mut body = match std::mem::replace(&mut arm.body.kind, ExprKind::AutoRefl) {
                    ExprKind::Block(b) => *b,
                    kind => {
                        // An arm that is a bare call on the receiver: bound
                        // first, as a block's result is (§8.2).
                        let call = Expr { kind, span };
                        if crate::imperative::receiver_call(&call, receiver) {
                            let name = self.hygienic("tail");
                            let bound = Stmt::Let {
                                name: name.clone(), ty: None,
                                expr: crate::imperative::marked(crate::imperative::MUTCALL, call, span), span, opaque: false,
                            };
                            Block { stmts: vec![bound], result: Box::new(Expr { kind: ExprKind::Var(name), span }), ons: Vec::new(), span }
                        } else {
                            Block { stmts: Vec::new(), result: Box::new(call), ons: Vec::new(), span }
                        }
                    }
                };
                self.receiver_end(&mut body, receiver);
                arm.body.kind = ExprKind::Block(Box::new(body));
            }
            return;
        }
        if let Some(method) = self.own_method.clone()
            && let Some(call) = crate::imperative::take_own_call(block, receiver, &method)
        {
            let span = call.span;
            block.result = Box::new(crate::imperative::marked(crate::imperative::MUTATED_WHOLE, call, span));
            return;
        }
        // The value stands in the record, where it is checked at the
        // method's result type: a numeral there is one of that type.
        let span = block.result.span;
        let value = if crate::imperative::is_unit_result(&block.result) {
            Expr { kind: ExprKind::Var("trivial".into()), span }
        } else {
            std::mem::replace(&mut *block.result, Expr { kind: ExprKind::Var("trivial".into()), span })
        };
        let var = |n: &str| Expr { kind: ExprKind::Var(n.into()), span };
        block.result = Box::new(Expr {
            kind: ExprKind::App { head: Box::new(var(MUTATED_RECORD)), args: vec![var(receiver), value], named: vec![], explicit: false, goal_oriented: false },
            span,
        });
    }

    /// [`Self::block_body`] after its statements: the result (`parsed` when
    /// [`Self::block_statements`] already read it), its `on`s, and the `}`.
    fn block_tail(&mut self, open: Span, stmts: Vec<Stmt>, parsed: Option<Expr>) -> R<Block> {
        // A statement body ends in a statement and has no result
        // (docs/language/sequencing-surface-design.md §4): `{ x := e }`, or `{}`.
        if parsed.is_none()
            && matches!(self.peek(), TokKind::RBrace)
            && stmts.last().is_none_or(is_imperative_statement)
        {
            let close = self.expect(&TokKind::RBrace, "`}`")?;
            return Ok(Block { stmts, result: Box::new(crate::imperative::unit(close)), ons: Vec::new(), span: open.join(close) });
        }
        if let Some(result) = parsed {
            let ons = self.block_ons(Vec::new())?;
            let close = self.expect(&TokKind::RBrace, "`}`")?;
            return Ok(Block { stmts, result: Box::new(result), ons, span: open.join(close) });
        }
        // `induct f(x̄); all_goals { … }` and `induct f(x̄) { C => e, … }`:
        // induction along `f`'s own recursion at the goal, every case with
        // the same block or each with its own arm. Packaged like `split_all`,
        // since the cases are only known once `f::induct` is resolved.
        if self.at_induct() {
            let start = self.bump().span;
            let call = self.with_record_lit(true, |p| p.expr())?;
            let result = if matches!(self.peek(), TokKind::Semi) {
                self.bump();
                if !self.eat_kw("all_goals") {
                    return self.err("`induct f(…);` must be followed by `all_goals { ... }`");
                }
                let goals = self.block()?;
                if !goals.ons.is_empty() {
                    return Err(ParseError {
                        msg: "an `all_goals` block cannot contain declaration-scoped `on` discharges".into(),
                        span: goals.span,
                    });
                }
                let span = start.join(goals.span);
                Expr {
                    kind: ExprKind::App {
                        head: Box::new(Expr { kind: ExprKind::Var(INDUCT_ALL_GOALS.into()), span: start }),
                        args: vec![call, Expr { kind: ExprKind::Block(Box::new(goals)), span }],
                        named: Vec::new(),
                        explicit: false,
                        goal_oriented: false,
                    },
                    span,
                }
            } else {
                let open_cases = self.expect(&TokKind::LBrace, "`{` with one arm per case, or `; all_goals { … }`, after `induct f(…)`")?;
                let arms = self.match_arms()?;
                let close_cases = self.expect(&TokKind::RBrace, "`}` after the cases")?;
                let span = start.join(close_cases);
                let cases = Expr {
                    kind: ExprKind::Match {
                        form: MatchForm::Match,
                        generated: false,
                        scrut: Box::new(call),
                        eqbind: None,
                        motive: None,
                        arms,
                        test: None,
                    },
                    span: open_cases.join(close_cases),
                };
                Expr {
                    kind: ExprKind::App {
                        head: Box::new(Expr { kind: ExprKind::Var(INDUCT_CASES.into()), span: start }),
                        args: vec![cases],
                        named: Vec::new(),
                        explicit: false,
                        goal_oriented: false,
                    },
                    span,
                }
            };
            let close = self.expect(&TokKind::RBrace, "`}` after `induct`")?;
            return Ok(Block { stmts, result: Box::new(result), ons: Vec::new(), span: open.join(close) });
        }
        // Goal combinators are statement-shaped: `split_all` replaces the
        // current goal by one goal per finite branch, then `all_goals` checks
        // the same block in every resulting branch. The parser packages the
        // pair into one unspellable checking form; branch construction needs
        // elaborated local types and therefore remains in the elaborator.
        if self.at_kw("split_all") {
            let start = self.bump().span;
            self.expect(&TokKind::Semi, "`;` after `split_all`")?;
            if !self.eat_kw("all_goals") {
                return self.err("`split_all` must be followed by `all_goals { ... }`");
            }
            let goals = self.block()?;
            if !goals.ons.is_empty() {
                return Err(ParseError {
                    msg: "an `all_goals` block cannot contain declaration-scoped `on` discharges"
                        .into(),
                    span: goals.span,
                });
            }
            let close = self.expect(&TokKind::RBrace, "`}` after `all_goals`")?;
            let span = start.join(close);
            let result = Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr {
                        kind: ExprKind::Var(SPLIT_ALL_GOALS.into()),
                        span: start,
                    }),
                    args: vec![Expr {
                        kind: ExprKind::Block(Box::new(goals)),
                        span,
                    }],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            };
            return Ok(Block {
                stmts,
                result: Box::new(result),
                ons: Vec::new(),
                span: open.join(close),
            });
        }
        // `cases h;` / `cases h as e1, e2(x, y);`: take the hypothesis `h`
        // apart along the tests the call it states is stuck on, the rest of
        // the block being every case that survives
        // (issues/cases-on-hypothesis-tactic.md). Packaged like `split_all`,
        // since the tests are only known from `h`'s elaborated type.
        if self.at_cases() {
            let start = self.bump().span;
            let (hypothesis, _) = self.ident("the hypothesis `cases` takes apart")?;
            let mut names = Vec::new();
            if self.eat_kw("as") {
                loop {
                    let (name, _) = self.ident("a name for the split's equation")?;
                    let mut fields = Vec::new();
                    if matches!(self.peek(), TokKind::LParen) {
                        self.bump();
                        loop {
                            fields.push(self.ident("a field name")?.0);
                            if !matches!(self.peek(), TokKind::Comma) {
                                break;
                            }
                            self.bump();
                        }
                        self.expect(&TokKind::RParen, "`)` after the case's field names")?;
                    }
                    names.push(CasesName { equation: name, fields });
                    if !matches!(self.peek(), TokKind::Comma) {
                        break;
                    }
                    self.bump();
                }
            }
            let semi = self.expect(&TokKind::Semi, "`;` after `cases h`")?;
            let mut body_stmts = Vec::new();
            let parsed = self.block_statements(&mut body_stmts)?;
            let (body_result, ons) = match parsed {
                Some(result) => (result, self.block_ons(Vec::new())?),
                None => self.block_result_and_ons()?,
            };
            let close = self.expect(&TokKind::RBrace, "`}`")?;
            let body = if body_stmts.is_empty() {
                body_result
            } else {
                Expr {
                    kind: ExprKind::Block(Box::new(Block { stmts: body_stmts, result: Box::new(body_result), ons: Vec::new(), span: semi.join(close) })),
                    span: semi.join(close),
                }
            };
            let result = Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr { kind: ExprKind::Var(cases_head(&names, !names.is_empty(), None)), span: start }),
                    args: vec![Expr { kind: ExprKind::Var(hypothesis), span: start }, body],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span: start.join(close),
            };
            return Ok(Block { stmts, result: Box::new(result), ons, span: open.join(close) });
        }
        // `x ⊢ ...` at a block's result scopes over the REST of that block,
        // including its `let`s. This is the long-proof face of the sequent
        // expression: `{ x ⊢ let y = e; body }` lowers to
        // `λ x => { let y = e; body }`, without requiring a second pair of
        // braces merely to delimit the lambda body
        // (issues/sequent-binder-expression.md).
        if self.at_sequent_binders() {
            let (binders, start, turnstile) = self.sequent_binders()?;
            let mut body_stmts = Vec::new();
            let parsed = self.block_statements(&mut body_stmts)?;
            let (body_result, ons) = match parsed {
                Some(result) => (result, self.block_ons(Vec::new())?),
                None => self.block_result_and_ons()?,
            };
            let close = self.expect(&TokKind::RBrace, "`}`")?;
            let body = if body_stmts.is_empty() {
                body_result
            } else {
                let inner = crate::try_lower::binds_in_block(
                    Block {
                        stmts: body_stmts,
                        result: Box::new(body_result),
                        // Goal discharges retain declaration-block scope and
                        // are therefore hoisted to the outer block below.
                        ons: Vec::new(),
                        span: turnstile.join(close),
                    },
                    &mut self.next_hygienic,
                )?;
                Expr { kind: ExprKind::Block(Box::new(inner)), span: turnstile.join(close) }
            };
            let result = Expr {
                kind: ExprKind::Lam { binders, body: Box::new(body) },
                span: start.join(close),
            };
            return Ok(Block { stmts, result: Box::new(result), ons, span: open.join(close) });
        }
        let (result, ons) = self.block_result_and_ons()?;
        let close = self.expect(&TokKind::RBrace, "`}`")?;
        Ok(Block { stmts, result: Box::new(result), ons, span: open.join(close) })
    }

    /// Parse the result expression (or terminal `split`) and the declaration-
    /// scoped goal discharges that follow it. Kept separate from
    /// [`Self::block_body`] because a sequent block header wraps this whole
    /// suffix in a lambda while hoisting its `on`s back to the declaration.
    fn block_result_and_ons(&mut self) -> R<(Expr, Vec<OnStmt>)> {
        if self.at_kw("on") {
            return self
                .err("a block's `on` discharges come after its result expression");
        }
        // `split e;` — the statement-position case split. It *is* the block's
        // result, so the statement list ends here and the `on Ctor(…)` arms
        // that follow are its arms (docs/language/matching/match-equation-split-design.md §5).
        let (result, ons) = if self.at_kw("split") {
            self.split_result()?
        } else {
            let result = self.expr()?;
            (result, Vec::new())
        };
        let ons = self.block_ons(ons)?;
        Ok((result, ons))
    }

    /// The `on` goal discharges after a block's result, appended to `ons`.
    fn block_ons(&mut self, mut ons: Vec<OnStmt>) -> R<Vec<OnStmt>> {
        while self.at_kw("on") {
            let on = self.on_stmt()?;
            if let OnTarget::Ctor { ctor, .. } = &on.target {
                return Err(ParseError {
                    msg: format!(
                        "`on {ctor}(…)` is a `split` arm, and this block has no `split`. \
                         A goal discharge is `on ?name := …` or `on _: P := …`"
                    ),
                    span: on.span,
                });
            }
            ons.push(on);
        }
        Ok(ons)
    }

    /// `split (h :)? e; on C(x⃗) := b; …` — parsed here and **desugared here**,
    /// onto the very `ExprKind::Match` a hand-written case analysis builds
    /// (docs/language/matching/match-equation-split-design.md §6). Nothing downstream learns that
    /// `split` exists, which is what makes "it lowers to the same elimination"
    /// a tautology rather than an obligation.
    ///
    /// Returns the synthesized result expression and any *goal* discharges
    /// found among the trailing `on`s: arms and discharges share the one `on`
    /// loop and are told apart by a single token, so arms stay order-free.
    fn split_result(&mut self) -> R<(Expr, Vec<OnStmt>)> {
        let start = self.bump().span; // `split`
        let eqbind = self.eq_binder()?;
        let scrut = self.with_record_lit(true, |p| p.expr())?;
        let motive = if self.eat_kw("as") {
            Some(Box::new(self.with_motive(|p| p.with_record_lit(true, |p| p.expr()))?))
        } else {
            None
        };
        let mut end = self.expect(&TokKind::Semi, "`;` to end the `split`")?;
        if self.at_stmt() {
            return self.err(
                "a `split` is the last statement of its block: its arms are the \
                 block's result, so nothing follows them but `on`",
            );
        }
        let mut arms: Vec<Arm> = Vec::new();
        let mut ons: Vec<OnStmt> = Vec::new();
        while self.at_kw("on") {
            let on = self.on_stmt()?;
            end = on.span;
            match on.target {
                OnTarget::Ctor { ctor, binders, default } => {
                    arms.push(Arm { ctor, default, binders, body: on.expr, span: on.span })
                }
                _ => ons.push(on),
            }
        }
        if arms.is_empty() {
            return Err(ParseError {
                msg: "a `split` needs at least one `on Ctor(…) := …;` arm — its arms \
                      are the block's result"
                    .to_string(),
                span: start,
            });
        }
        let span = start.join(end);
        Ok((
            Expr {
                kind: ExprKind::Match {
                    form: MatchForm::Split,
                    generated: false,
                    scrut: Box::new(scrut),
                    eqbind,
                    motive,
                    arms,
                    test: None,
                },
                span,
            },
            ons,
        ))
    }

    /// `let x = e;` / `let x: T = e;`. The `=` here is the same `=` as the
    /// equality type former ([`Self::expect_eq`]).
    ///
    /// The annotation is read with [`Parser::no_eq`] set, so the binder `=` is
    /// never eaten by the comparison rung and `let x: T = e;` is writable at
    /// **every** `T` (docs/language/let-and-blocks-design.md §3). An annotation that is
    /// itself an equation is parenthesised — `let p: (a = b) = pf;` — which is
    /// the escape hatch `no_eq`'s doc comment promises and `atom`'s `(` arm
    /// now delivers. Every other relation is unambiguous there and reads bare:
    /// `let k: a <= b = h;` ([`Parser::annotation_rel`]).
    fn let_stmt(&mut self) -> R<Stmt> {
        if self.at_kw("have") {
            return self.have_stmt();
        }
        let start = self.bump().span; // `let`
        // `let { unit := u, op } = m;` — record destructuring
        // (docs/language/matching/named-patterns-by-field-design.md §2). Unambiguous against
        // `let x = …`: a binding name cannot start with `{`.
        if matches!(self.peek(), TokKind::LBrace) {
            self.bump();
            let mut fields = Vec::new();
            while !matches!(self.peek(), TokKind::RBrace) {
                let (n, sp) = self.binder_ident("field name in a `let` pattern")?;
                let pat = if matches!(self.peek(), TokKind::ColonEq) {
                    self.bump();
                    self.pat()?
                } else {
                    Pat::Var { name: n.clone(), span: sp }
                };
                let span = sp.join(pat.span());
                fields.push(RecordPatField { name: n, pat, span });
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect(&TokKind::RBrace, "`}` (`let` pattern)")?;
            let bound = self.eat_bind_arrow();
            if !bound {
                self.expect_eq("`let` pattern")?;
            }
            let expr = self.expr()?;
            let expr = if bound { let span = expr.span; crate::try_lower::bind_marker(expr, span) } else { expr };
            let end = self.expect(&TokKind::Semi, "`;` to end the `let`")?;
            return Ok(Stmt::LetRecord { fields, expr, span: start.join(end) });
        }
        // `let code x = e;` — the surface letbox (surface-v0 §4). Unambiguous
        // against `let code = …`: two names in a row were never a parse.
        if self.at_kw("code") && matches!(self.nth(1), TokKind::Ident(_)) {
            self.bump(); // `code`
            let (name, _) = self.binder_ident("`let code` binding name")?;
            self.expect_eq("`let code` binding")?;
            let expr = self.expr()?;
            let end = self.expect(&TokKind::Semi, "`;` to end the `let code`")?;
            return Ok(Stmt::LetCode { name, expr, span: start.join(end) });
        }
        // `let mut x = e;` — a local `:=` may reassign (§4). `mut` is
        // contextual: `let mut = e;` still binds a name `mut`.
        let mutable = self.at_kw("mut") && matches!(self.nth(1), TokKind::Ident(_));
        if mutable {
            self.bump();
        }
        let (mut name, _) = self.binder_ident("`let` binding name")?;
        let ty = if matches!(self.peek(), TokKind::Colon) {
            self.bump();
            // The annotation, and only the annotation: the value is parsed
            // below with the flag restored, so `let x: Type<0> = a = b;` still
            // binds the *proposition*.
            Some(self.annotation()?)
        } else {
            None
        };
        // `let x <- e;` — a binding statement (docs/language/sequencing-surface-design.md
        // §3.1): the nested bind at the `let`'s right side, `let x = (<- e);`.
        if self.eat_bind_arrow() {
            let expr = self.expr()?;
            let end = self.expect(&TokKind::Semi, "`;` to end the `let`")?;
            if name == "_" {
                name = self.hygienic("seq");
            }
            let span = expr.span;
            let expr = crate::try_lower::bind_marker(expr, span);
            let expr = if mutable { crate::imperative::marked(crate::imperative::MUT, expr, span) } else { expr };
            return Ok(Stmt::Let { name, ty, expr, span: start.join(end), opaque: false });
        }
        self.expect_eq("`let` binding")?;
        let expr = self.expr()?;
        let end = self.expect(&TokKind::Semi, "`;` to end the `let`")?;
        let expr = if mutable {
            let span = expr.span;
            crate::imperative::marked(crate::imperative::MUT, expr, span)
        } else if self.mut_receiver(&expr) {
            // `let p = x.m(a);` on a mutable `x` (§8.2), annotated or not.
            let span = expr.span;
            crate::imperative::marked(crate::imperative::MUTCALL, expr, span)
        } else {
            expr
        };
        if mutable {
            self.mutables.push(name.clone());
        }
        Ok(Stmt::Let { name, ty, expr, span: start.join(end), opaque: false })
    }

    /// `<-` or `←` after a `let` binder: the statement binds.
    fn eat_bind_arrow(&mut self) -> bool {
        if matches!(self.peek(), TokKind::LArrow) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// A block's statements, up to its result. `let`/`have` statements, and
    /// expression statements `e;` (docs/language/sequencing-surface-design.md §3.1,
    /// §4): an expression followed by `;` discards its result in the
    /// block's carrier, so it is the binding statement `let _ <- e;` at a
    /// private name. An expression followed by anything else is the block's
    /// result, returned here already parsed. No block written before this
    /// had an expression followed by `;`, so nothing that parsed changes
    /// meaning. The forms the result position reads by its first token
    /// (`split`, `split_all`, a sequent header, `on`, `}`) end the loop
    /// unparsed.
    /// `for x in e { body }` (docs/language/sequencing-surface-design.md §5.2): the
    /// marker `\0for(e, λ x => body)` at a private name, for
    /// [`crate::imperative`] to thread the `let mut` locals the body assigns
    /// and the elaborator to lift into a named step over a fold.
    fn for_stmt(&mut self) -> R<Stmt> {
        let start = self.bump().span;
        let (x, xspan) = self.binder_ident("`for` binder")?;
        self.bump(); // `in`
        let saved = std::mem::replace(&mut self.range_header, true);
        let iter = self.with_record_lit(true, |p| p.expr());
        self.range_header = saved;
        let mut iter = iter?;
        // `for i in a..b`: the range is `List::range_from(a, b - a)`, and
        // `0..n` is `List::range(n)` (§5.2), written only here, so no
        // `Range` type is needed yet.
        if matches!(self.peek(), TokKind::Dot) && matches!(self.nth(1), TokKind::Dot) {
            self.bump();
            self.bump();
            let hi = self.with_record_lit(true, |p| p.expr())?;
            let span = iter.span.join(hi.span);
            let app = |head: &str, args: Vec<Expr>| Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr { kind: ExprKind::Var(head.into()), span }),
                    args,
                    named: vec![],
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            };
            iter = if matches!(&iter.kind, ExprKind::Num(n) if *n == Numeral::ZERO) {
                app("List::range", vec![hi])
            } else {
                let len = op_call("-", OpFixity::Infix, vec![hi, iter.clone()], span);
                app("List::range_from", vec![iter, len])
            };
        }
        if !matches!(self.peek(), TokKind::LBrace) {
            return self.err("a `for` body is a braced block of statements: `for x in xs { … }`");
        }
        self.loop_stmt(start, iter, x, xspan, "for")
    }

    /// `while c [invariant p] decreases m { body }` (docs/language/sequencing-surface-design.md
    /// §5.3, §22.5): the `for` marker over the header `\0while(decide_bit<c>(),
    /// m)` and a private binder, so [`crate::imperative`] threads its state
    /// as a `for`'s, and the elaborator lifts it into a recursive `f::run`
    /// instead of a step over a fold.
    ///
    /// With no `decreases`, `while c { body }` is a loop in a block over a
    /// carrier that iterates (§18): the header is `\0while(decide_bit<c>())`
    /// alone, and the body's binds wait for the loop's lowering.
    fn while_stmt(&mut self) -> R<Stmt> {
        let start = self.bump().span;
        let condition = self.with_record_lit(true, |p| p.expr())?;
        let cspan = condition.span;
        // `invariant P`: a fact the loop keeps, proved where it starts and
        // at each round's end, and assumed in the body (§22.5).
        let invariant = if self.eat_kw("invariant") {
            Some(self.with_record_lit(true, |p| p.expr())?)
        } else {
            None
        };
        let measure = if self.eat_kw("decreases") {
            Some(self.with_record_lit(true, |p| p.expr())?)
        } else {
            None
        };
        if !matches!(self.peek(), TokKind::LBrace) {
            return self.err(if measure.is_some() {
                "a `while` body is a braced block of statements: `while c decreases m { … }`"
            } else {
                "a `while` body is a braced block of statements: `while c { … }` (in a block over a \
                 carrier that iterates) or `while c decreases m { … }`"
            });
        }
        // The condition as a plain `if` decides it, so the step sees the
        // same `decide_bit` match the measure obligation reads (§5.3).
        let scrut = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::TyApp {
                        head: Box::new(Expr { kind: ExprKind::Var("decide_bit".into()), span: cspan }),
                        args: vec![expr_as_ty(&condition)],
                    },
                    span: cspan,
                }),
                args: vec![],
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span: cspan,
        };
        if let Some(p) = &invariant
            && measure.is_none()
        {
            return Err(ParseError {
                msg: "a `while` with an `invariant` states its measure too: `while c invariant p decreases m { … }`"
                    .into(),
                span: p.span,
            });
        }
        let mut header_args = vec![scrut];
        header_args.extend(measure.clone());
        // The invariant rides third, read as the proposition it states.
        header_args.extend(invariant.map(|p| Expr { span: p.span, kind: ExprKind::TyLit(Box::new(expr_as_ty(&p))) }));
        let header = crate::imperative::call_marker(crate::imperative::WHILE, header_args, start.join(cspan));
        let x = self.hygienic("while");
        self.defer_binds = measure.is_none();
        self.loop_stmt(start, header, x, start, "while")
    }

    /// The braced body of a `for` or `while`, and its marker.
    fn loop_stmt(&mut self, start: Span, iter: Expr, x: String, xspan: Span, kw: &str) -> R<Stmt> {
        let body = self.block()?;
        if !matches!(&body.result.kind, ExprKind::Var(n) if n == crate::imperative::UNIT)
            && !(body.stmts.is_empty() && matches!(body.result.kind, ExprKind::AutoRefl))
        {
            return Err(ParseError {
                msg: format!("a `{kw}` body ends in a statement, not a value: it reassigns `let mut` locals, \
                      so it has no result"),
                span: body.result.span,
            });
        }
        if matches!(self.peek(), TokKind::Semi) {
            self.bump();
        }
        let span = start.join(body.span);
        let body = Expr { span: body.span, kind: ExprKind::Block(Box::new(body)) };
        let lam = Expr {
            kind: ExprKind::Lam {
                binders: vec![LamBinder { name: x, ty: None, implicit: false, span: xspan }],
                body: Box::new(body),
            },
            span,
        };
        let marked = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr { kind: ExprKind::Var(crate::imperative::FOR.into()), span }),
                args: vec![iter, lam],
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let name = self.hygienic("for");
        Ok(Stmt::Let { name, ty: None, expr: marked, span, opaque: false })
    }

    fn block_statements(&mut self, stmts: &mut Vec<Stmt>) -> R<Option<Expr>> {
        loop {
            if self.at_stmt() {
                stmts.push(self.let_stmt()?);
                continue;
            }
            if matches!(self.peek(), TokKind::RBrace | TokKind::Eof)
                || self.at_kw("split")
                || self.at_kw("split_all")
                || self.at_induct()
                || self.at_cases()
                || self.at_kw("on")
                || self.at_sequent_binders()
            {
                return Ok(None);
            }
            // `break;`, `continue;`, `return e;` (§4): statements of a
            // loop body, lowered by the loop ([`crate::imperative`]).
            if (self.at_kw("break") || self.at_kw("continue"))
                && matches!(self.nth(1), TokKind::Semi | TokKind::RBrace)
            {
                let word = if self.at_kw("break") { crate::imperative::BREAK } else { crate::imperative::CONTINUE };
                let span = self.bump().span;
                if matches!(self.peek(), TokKind::Semi) { self.bump(); }
                let name = self.hygienic("exit");
                stmts.push(Stmt::Let {
                    name,
                    ty: None,
                    expr: Expr {
                        kind: ExprKind::App {
                            head: Box::new(Expr { kind: ExprKind::Var(word.into()), span }),
                            args: vec![], named: vec![], explicit: false, goal_oriented: false,
                        },
                        span,
                    },
                    span,
                    opaque: false,
                });
                continue;
            }
            if self.at_kw("return") && !matches!(self.nth(1), TokKind::Semi | TokKind::RBrace) {
                let start = self.bump().span;
                let value = self.expr()?;
                let end = if matches!(self.peek(), TokKind::RBrace) { value.span } else { self.expect(&TokKind::Semi, "`;` to end the `return`")? };
                let span = start.join(end);
                let name = self.hygienic("exit");
                let vspan = value.span;
                stmts.push(Stmt::Let {
                    name,
                    ty: None,
                    expr: crate::imperative::marked(crate::imperative::RETURN, value, vspan),
                    span,
                    opaque: false,
                });
                continue;
            }
            // `for x in e { body }` (§5.2): a statement, needing no `;`.
            if self.at_kw("for")
                && matches!(self.nth(1), TokKind::Ident(_))
                && matches!(self.nth(2), TokKind::Ident(w) if w == "in")
            {
                stmts.push(self.for_stmt()?);
                continue;
            }
            // `while c decreases m { body }` (§5.3), a statement too.
            if self.at_kw("while") && !matches!(self.nth(1), TokKind::Semi | TokKind::RBrace) {
                stmts.push(self.while_stmt()?);
                continue;
            }
            // A statement `if` may omit its `else` (§4): only here, at the
            // head of a statement.
            self.elseless_if = self.at_kw("if");
            let expr = self.expr();
            self.elseless_if = false;
            let expr = expr?;
            // `x := e` — reassign a `let mut` local (§4, §5.1). The `;` may
            // be left off before the block's `}`, as a statement body's last
            // assignment usually is.
            if matches!(self.peek(), TokKind::ColonEq) {
                if crate::imperative::place_root(&expr).is_none() {
                    return Err(ParseError {
                        msg: "only a place is assigned: a local, `x := e`, a field path of one, \
                              `x.f := e`, or an element of one, `x.f[i] := e` \
                              (docs/language/sequencing-surface-design.md §20, §21)".into(),
                        span: expr.span,
                    });
                }
                self.bump();
                let value = self.expr()?;
                // `x.f := e` assigns `x` the record with that field replaced
                // (§20): `x := x with { f = e }`.
                let (name, value) = crate::imperative::place_update(&expr, value).expect("a place");
                let end = if matches!(self.peek(), TokKind::RBrace) {
                    value.span
                } else {
                    self.expect(&TokKind::Semi, "`;` to end the assignment")?
                };
                let span = expr.span.join(end);
                let marked = value.span;
                stmts.push(Stmt::Let {
                    name,
                    ty: None,
                    expr: crate::imperative::marked(crate::imperative::ASSIGN, value, marked),
                    span,
                    opaque: false,
                });
                continue;
            }
            // A statement `if`/`match`: a block-like form whose bodies are
            // statements. It needs no `;`.
            if is_statement_form(&expr) {
                if matches!(self.peek(), TokKind::Semi) {
                    self.bump();
                }
                let span = expr.span;
                let name = self.hygienic("stmt");
                stmts.push(Stmt::Let {
                    name,
                    ty: None,
                    expr: crate::imperative::marked(crate::imperative::STMT, expr, span),
                    span,
                    opaque: false,
                });
                continue;
            }
            if !matches!(self.peek(), TokKind::Semi) {
                return Ok(Some(expr));
            }
            let end = self.bump().span;
            let span = expr.span.join(end);
            let marked = expr.span;
            let name = self.hygienic("seq");
            // `x.m(a);` on a mutable `x` updates it (§8.2); any other
            // expression statement is a bind.
            let expr = if self.mut_receiver(&expr) {
                crate::imperative::marked(crate::imperative::MUTCALL, expr, marked)
            } else {
                crate::try_lower::bind_marker(expr, marked)
            };
            stmts.push(Stmt::Let {
                name,
                ty: None,
                expr,
                span,
                opaque: false,
            });
        }
    }

    /// A block statement starts here: `let`, or `have` followed by a name.
    /// `have` is contextual the way `let code x` is (docs/language/have-design.md §2):
    /// `have x` was never an expression, so a value named `have` keeps
    /// working everywhere, the head of a block's result included.
    fn at_stmt(&self) -> bool {
        self.at_kw("let") || (self.at_kw("have") && matches!(self.nth(1), TokKind::Ident(_)))
    }

    /// `have x = e;` / `have x: T = e;` — [`Self::let_stmt`]'s single-name
    /// form, binding opaquely (docs/language/have-design.md). The annotation is read
    /// under `no_eq` for the same reason as a `let`'s.
    fn have_stmt(&mut self) -> R<Stmt> {
        let start = self.bump().span; // `have`
        let (name, _) = self.binder_ident("`have` binding name")?;
        let ty = if matches!(self.peek(), TokKind::Colon) {
            self.bump();
            Some(self.annotation()?)
        } else {
            None
        };
        self.expect_eq("`have` binding")?;
        let expr = self.expr()?;
        let end = self.expect(&TokKind::Semi, "`;` to end the `have`")?;
        Ok(Stmt::Let { name, ty, expr, span: start.join(end), opaque: true })
    }

    fn on_stmt(&mut self) -> R<OnStmt> {
        let start = self.bump().span; // `on`
        let target = match self.peek().clone() {
            _ if self.at_kw("decreasing") => {
                self.bump();
                let (name, _) = self.ident("decrease label")?;
                OnTarget::Name(format!("#decreasing:{name}"))
            }
            TokKind::Hole(Some(name)) => {
                self.bump();
                // `?bound.1` — the checker's ordinal suffix for a deduplicated
                // default name. Only a numeral follows; `.f(…)` is a method
                // call, which a goal name never carries.
                let mut name = name;
                if matches!(self.peek(), TokKind::Dot)
                    && let Some(TokKind::Num(n)) = self.toks.get(self.pos + 1).map(|t| &t.kind)
                {
                    name = format!("{name}.{n}");
                    self.bump();
                    self.bump();
                }
                OnTarget::Name(name)
            }
            TokKind::Hole(None) => {
                return self.err(
                    "`on ?` needs a goal name; write `on _: P := …` to discharge by statement",
                )
            }
            // `on _: P := …` is a discharge by statement; `on _ := …` is a
            // **default arm** of the enclosing `split`
            // (docs/language/matching/nested-match-patterns-design.md §8). One token apart, and
            // the token is already read here.
            _ if self.at_kw("_") && matches!(self.nth(1), TokKind::Colon) => {
                self.bump();
                self.bump(); // `:`
                OnTarget::Stmt(self.ty()?)
            }
            _ if self.at_kw("_") => {
                self.bump();
                OnTarget::Ctor { ctor: "_".to_string(), binders: vec![], default: true }
            }
            // `on Ctor(x, y) := …` — a `split` arm. An identifier head was a
            // parse error before this, so the form is strictly additive
            // (docs/language/matching/match-equation-split-design.md §5).
            TokKind::Ident(_) => {
                let (ctor, cspan) = self.qual_ident("constructor name in an `on` arm")?;
                let binders = self.pat_args(&ctor, cspan)?;
                OnTarget::Ctor { ctor, binders, default: false }
            }
            _ => return self.err("expected `?name`, `_: P`, or `Ctor(…)` after `on`"),
        };
        self.expect(&TokKind::ColonEq, "`:=` (goal discharge)")?;
        let expr = self.expr()?;
        let end = self.expect(&TokKind::Semi, "`;` to end the `on`")?;
        Ok(OnStmt { target, expr, span: start.join(end) })
    }

    // -- types --------------------------------------------------------------

    /// Consume the equality operator `=`. Heather merges binding and equality
    /// onto one `=` (ML-style, disambiguated by `let`; issues/surface-syntax.md);
    /// `==` is lexed but not part of the grammar, so it gets a targeted hint
    /// where equality is expected (`a = b`, calc steps) — catching C/Rust habit.
    fn expect_eq(&mut self, what: &str) -> R<()> {
        if matches!(self.peek(), TokKind::EqEq) {
            return self.err(format!("`==` is not used in Heather; write `=` ({what})"));
        }
        self.expect(&TokKind::Eq, "`=`")?;
        Ok(())
    }

    /// Types, arrow-aware. `->` is right-associative, and a *binder-headed*
    /// group `(x: A) -> B` makes it dependent
    /// (docs/language/surface-function-types.md §3.1).
    ///
    /// The arrow check has to live above [`Self::ty_atom`] rather than inside
    /// it: `ty_atom`'s `D<A>` case returns early, so folding the arrow into it
    /// would silently drop the `-> B` of `D<A> -> B`.
    fn ty(&mut self) -> R<Ty> {
        // `(x: A) -> B`. Three-token lookahead; `:` is not in the expression
        // grammar, so a binder-headed group cannot be anything else.
        if self.at_binder_group() {
            let start = self.bump().span; // `(`
            let binders = self.binder_list(false)?;
            self.expect(&TokKind::RParen, "`)` to close the binder")?;
            self.expect(&TokKind::Arrow, "`->` after a function-type binder")?;
            let cod = self.cod(|p| p.ty())?;
            let span = start.join(cod.span);
            return self.iff_after_fn_type(curry(binders, cod, false, span));
        }
        // `{x: A} -> B` — an *implicit* binder
        // (docs/language/implicit-binders-design.md §8). The same three-token
        // lookahead the old diagnostic used: type position has no other
        // brace form, so `{ Ident :` is unambiguous. One binder per brace
        // group, mirroring the paren rule; inside the braces the type parses
        // exactly as inside `(…: …)` (an equality domain is `{p: (a = b)}`).
        if matches!(self.peek(), TokKind::LBrace)
            && matches!(self.nth(1), TokKind::Ident(_))
            && matches!(self.nth(2), TokKind::Colon | TokKind::Comma)
        {
            let start = self.bump().span; // `{`
            let binders = self.binder_list(true)?;
            self.expect(&TokKind::RBrace, "`}` to close the implicit binder")?;
            self.expect(&TokKind::Arrow, "`->` after a function-type binder")?;
            let cod = self.cod(|p| p.ty())?;
            let span = start.join(cod.span);
            return self.iff_after_fn_type(curry(binders, cod, true, span));
        }
        let lhs = self.ty_atom()?;
        if matches!(self.peek(), TokKind::Arrow) {
            self.bump();
            let cod = self.cod(|p| p.ty())?; // right-associative
            let span = lhs.span.join(cod.span);
            return Ok(Ty {
                kind: TyKind::Fn {
                    binder: None,
                    implicit: false,
                    dom: Box::new(lhs),
                    cod: Box::new(cod),
                },
                span,
            });
        }
        Ok(lhs)
    }

    /// The inside of a function type's binder group: `x: A`, `x, y: A`,
    /// `x: A, y: B`, and every mix of the two
    /// (issues/multi-binder-function-types.md). The result is a **telescope** —
    /// a later binder's type may mention an earlier binder — which is exactly
    /// what falls out of parsing the domains left to right and currying at the
    /// end, so nothing here has to enforce it.
    ///
    /// The two commas are one comma and the parse is still deterministic: a
    /// *name* is only ever followed by `,` (another name in the same run) or
    /// `:` (the run's shared annotation), and a group is only ever ended by a
    /// *type*, so the comma after a type starts the next group. No lookahead,
    /// no backtracking.
    fn binder_list(&mut self, implicit: bool) -> R<Vec<(String, Ty)>> {
        let (open, close) = if implicit { ("{", "}") } else { ("(", ")") };
        let mut out: Vec<(String, Ty)> = Vec::new();
        loop {
            let mut names = vec![self.ident("binder name")?];
            while matches!(self.peek(), TokKind::Comma) {
                self.bump();
                names.push(self.ident("binder name")?);
            }
            if !matches!(self.peek(), TokKind::Colon) {
                let span = names[0].1.join(names[names.len() - 1].1);
                let written =
                    names.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(", ");
                return Err(ParseError {
                    msg: format!(
                        "this binder group has no type: write `{open}{written}: A{close} -> B`. \
                         A comma-separated run of names shares ONE annotation, and the \
                         annotation is what makes them binders rather than a grouped \
                         expression"
                    ),
                    span,
                });
            }
            self.bump(); // `:`
            let dom = self.ty()?;
            for (name, _) in names {
                out.push((name, dom.clone()));
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        Ok(out)
    }

    /// A type with no top-level arrow.
    /// `Type` / `Type<n>` in either position. Shared by [`Self::ty_atom`] and
    /// [`Self::atom`] so the two spellings cannot drift, and tried *before*
    /// the applied-inductive rule, which parses its arguments with
    /// [`Self::ty`] and would reject the numeral in `Type<0>`
    /// (docs/language/surface-universe.md §3).
    fn univ(&mut self) -> R<Option<(u64, Span)>> {
        if !self.at_kw("Type") {
            return Ok(None);
        }
        let start = self.bump().span;
        if !matches!(self.peek(), TokKind::Lt) {
            return Ok(Some((0, start)));
        }
        self.bump(); // `<`
        let TokKind::Num(n) = self.peek() else {
            return self.err(
                "a universe level must be a numeral: levels cannot be quantified over \
                 at the surface (universe polymorphism is layer m) and joins are \
                 computed rather than written",
            );
        };
        let Some(n) = n.as_u64() else {
            return self.err("a universe level must fit in 64 bits");
        };
        self.bump();
        let end = self.expect(&TokKind::Gt, "`>` to close a universe level")?;
        Ok(Some((n, start.join(end))))
    }

    fn ty_atom(&mut self) -> R<Ty> {
        // Every rule below but the two expression fallthroughs opens a
        // bracket, and a bracket lifts the codomain's `↔` restriction
        // ([`Self::expr`]). Lifting it once here covers the type-side
        // brackets — the parenthesised group, the type arguments of `D<A, B>`,
        // `[T; n]`, `Squash`, `Code` — and the fallthroughs put it back, since
        // those *are* the codomain's spine (issues/iff-in-type-valued-body.md).
        let restricted = std::mem::replace(&mut self.no_iff, false);
        let out = self.ty_atom_rules(restricted);
        self.no_iff = restricted;
        out
    }

    /// [`Self::ty_atom`]'s rules, with the codomain restriction lifted for the
    /// bracketed ones. `restricted` is restored around the two fallthroughs to
    /// [`Self::expr`], which continue the codomain rather than descending into
    /// a bracket.
    fn ty_atom_rules(&mut self, restricted: bool) -> R<Ty> {
        if matches!(self.peek(), TokKind::NormBar) {
            let start = self.bump().span;
            let inner = self.ty()?;
            let end = self.expect(&TokKind::NormBar, "`∥` to close a squash type")?;
            return Ok(Ty { kind: TyKind::Squash(Box::new(inner)), span: start.join(end) });
        }
        if self.at_kw("Squash") && matches!(self.nth(1), TokKind::Lt) {
            let start = self.bump().span;
            self.bump(); // `<`
            let inner = self.ty()?;
            let end = self.expect(&TokKind::Gt, "`>` to close `Squash<A>`")?;
            return Ok(Ty { kind: TyKind::Squash(Box::new(inner)), span: start.join(end) });
        }
        // `Type` / `Type<n>`. Before the applied-inductive rule below, which
        // would try to parse `0` as a type.
        if let Some((level, span)) = self.univ()? {
            return Ok(Ty { kind: TyKind::Univ { level }, span });
        }
        // `( ty )` — needed so `(A -> B) -> C` groups. Guarded by
        // `group_is_type`, because in type position a leading `(` far more
        // often opens an *expression*: `(a + b) + c = a + (b + c)` is a type,
        // but every parenthesis in it is an arithmetic one.
        if matches!(self.peek(), TokKind::LParen) && self.group_is_type() {
            let save = self.pos;
            let start = self.bump().span;
            // Inside the bracket the comparison rung is available again, the
            // same escape hatch `atom`'s `(` arm opens.
            let inner = self.with_eq(false, |p| p.ty())?;
            let end = self.expect(&TokKind::RParen, "`)`")?;
            // …unless a connective follows, in which case this group is that
            // connective's left OPERAND and the whole type is built by the
            // rung that lives in the expression grammar — the same rewind the
            // `D<A>` rule below makes, and for the same reason
            // (issues/std-logic-module.md).
            if !self.at_connective() {
                return Ok(Ty { kind: inner.kind, span: start.join(end) });
            }
            self.pos = save;
        }
        // The modal slice (docs/metaprogramming/in-language-map-design.md §3): `Ctx`,
        // `TyCode(g)`, `Code(g |- T)`, and `$a` for a `TyCode` binder used as
        // a type. Keyword-shaped, so they are tried before the general rules;
        // a user type named `Ctx`/`TyCode`/`Code` was possible before and is
        // shadowed now, the usual cost of a keyword.
        if self.at_kw("Ctx") && !matches!(self.nth(1), TokKind::Lt | TokKind::LParen) {
            let span = self.bump().span;
            return Ok(Ty { kind: TyKind::Ctx, span });
        }
        if self.at_kw("TyCode") && matches!(self.nth(1), TokKind::LParen) {
            let start = self.bump().span;
            self.bump(); // `(`
            let (ctx, _) = self.ident("context name in `TyCode(g)`")?;
            let end = self.expect(&TokKind::RParen, "`)` to close `TyCode(g)`")?;
            return Ok(Ty { kind: TyKind::TyCode { ctx }, span: start.join(end) });
        }
        if self.at_kw("Code") && matches!(self.nth(1), TokKind::LParen) {
            let start = self.bump().span;
            self.bump(); // `(`
            let (ctx, _) = self.ident("context name in `Code(g |- T)`")?;
            self.expect(&TokKind::Turnstile, "`|-` (a code type is `Code(g |- T)`)")?;
            let ty = self.ty()?;
            let end = self.expect(&TokKind::RParen, "`)` to close `Code(g |- T)`")?;
            return Ok(Ty { kind: TyKind::Code { ctx, ty: Box::new(ty) }, span: start.join(end) });
        }
        if matches!(self.peek(), TokKind::Dollar) {
            let start = self.bump().span;
            let (name, nsp) = self.ident("name after `$` in type position")?;
            return Ok(Ty { kind: TyKind::Splice { name }, span: start.join(nsp) });
        }
        // `[T; n]` — a length-indexed vector (docs/language/container-fields.md §2.1).
        // A leading `[` in type position is also the list literal that opens
        // an equality's left endpoint — `[1] ++ [2] = [1, 2]` is a statement
        // — so the vector reading is speculative, like `D<A, B>` below: the
        // element parses as a type, and only a `;` after it commits. Anything
        // else rewinds to the expression grammar, whose `[` arm tells the two
        // apart by the same first separator
        // (issues/statement-leading-list-literal-parse.md).
        if matches!(self.peek(), TokKind::LBracket) && !self.spec_seen_failing(self.pos, SITE_TY_VEC) {
            let save = self.pos;
            let start = self.bump().span;
            let elem = match self.ty() {
                Ok(elem) if matches!(self.peek(), TokKind::Semi) => elem,
                _ => {
                    self.spec_note_failure(save, SITE_TY_VEC);
                    let lhs = self.with_iff(restricted, |p| p.expr())?;
                    return Ok(expr_as_ty(&lhs));
                }
            };
            self.bump(); // `;`
            let len = self.expr()?;
            let end = self.expect(&TokKind::RBracket, "`]` (a vector type is `[T; n]`)")?;
            return Ok(Ty {
                kind: TyKind::Vec { elem: Box::new(elem), len: Box::new(len) },
                span: start.join(end),
            });
        }
        // `D<A, B>` — an applied inductive. This was once annotated
        // "unambiguous: `<` is the `lt` operator only in *expression*
        // position, and no expression is a type". **That premise died with
        // the propositional order** (issues/nat-order-kit.md, 2026-08-16):
        // `n < m` is `Lt(n, m)`, a proposition, so it is a type, and it is
        // written exactly where a hypothesis is — `h: i < len(xs)`. The two
        // readings are genuinely ambiguous at the `<` and are told apart the
        // only way they can be: try the type arguments, and if that parse does
        // not *complete*, it was the operator.
        //
        // Speculative parsing rather than lookahead, because no bounded
        // lookahead decides it — `D<A, B>` and `a < b` agree for arbitrarily
        // many tokens (`f(x) < g(y)` against `Vec<Pair<A, B>>`). The rewind
        // below already existed for two other discriminators; this adds the
        // third and largest, and it is the same `save`.
        if matches!(self.peek(), TokKind::Ident(_))
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind), Some(TokKind::Lt))
            && self.tight(self.pos + 1)
            && !self.spec_seen_failing(self.pos, SITE_TY_NAMED)
        {
            let save = self.pos;
            let (name, start) = self.qual_ident("type name")?;
            self.bump(); // `<`
            let mut args = Vec::new();
            let mut ok = true;
            loop {
                match self.ty() {
                    Ok(t) => args.push(t),
                    Err(_) => {
                        ok = false;
                        break;
                    }
                }
                if !matches!(self.peek(), TokKind::Comma) {
                    break;
                }
                self.bump();
            }
            // A failed argument, or no `>` where one was due, means this was
            // never a type application. Rewind and let the expression grammar
            // have it; if THAT fails too the error the user sees is the
            // expression's, which is the right one — an unterminated `D<A, B`
            // reports at the `<` as "unbound name / expected …" rather than
            // pretending to know which reading was intended.
            if !ok || !matches!(self.peek(), TokKind::Gt) {
                self.spec_note_failure(save, SITE_TY_NAMED);
                let lhs = self.with_iff(restricted, |p| p.expr())?;
                return Ok(expr_as_ty(&lhs));
            }
            let end = self.expect(&TokKind::Gt, "`>` to close the type arguments")?;
            // …unless a call follows, in which case this was an *expression*
            // with explicit type arguments opening an equality type —
            // `theorem t(): id<Nat>(3) = 3`. `(` is the discriminator for the
            // same reason `->` is in `group_is_type`: an applied type is
            // never called (docs/language/surface-polymorphism.md §1).
            //
            // A connective follows for the same reason and gets the same
            // answer: `Or<P, Q> ∧ R` is a *type* built by the connective
            // rung, which lives in the expression grammar, so this applied
            // type is its left operand and not the whole type. Without the
            // rewind the `∧` would dangle here and be reported at whatever
            // the caller expected next (issues/std-logic-module.md).
            if matches!(self.peek(), TokKind::LParen) || self.at_connective() {
                self.pos = save;
            } else {
                return Ok(Ty { kind: TyKind::Named { name, args }, span: start.join(end) });
            }
        }
        let lhs = self.with_iff(restricted, |p| p.expr())?;
        Ok(expr_as_ty(&lhs))
    }

    // -- expressions --------------------------------------------------------

    /// Expressions, with infix operators. Precedence, loosest to tightest: the
    /// **comparison level** ([`Self::comparison`] — `=`, `<=`, `<`), then
    /// `||`, `&&`, `+`/`++`, `*`, then postfix `.method(args)` / calls, then atoms.
    ///
    /// An operator application is an ordinary [`ExprKind::App`] whose head is
    /// the [`ExprKind::OpSymbol`] that was **written**. It used to be the head
    /// `Var("add")` that `+` desugared to, on a fixed name table here; that
    /// table is now the last rung of the elaborator's symbol resolution
    /// (docs/language/classes/operators-onto-classes-design.md §4), so `+` can mean a different
    /// operation at a different carrier without the parse depending on
    /// anything — which is `issues/notation-extensibility.md`'s standing
    /// boundary, *parsing is context-free; only resolution consults scope*.
    ///
    /// **Function types are expressions** (`docs/language/types-as-expressions.md`): a
    /// leading binder group `(x: A) -> …` and a trailing `->` both hand off to
    /// [`Self::ty`] and come back as an [`ExprKind::TyLit`]. Neither spelling
    /// was previously a parse — `->` after an expression was always an error,
    /// and `:` is not in the expression grammar — so this is a pure extension
    /// with no backtracking. `=` binds tighter than `->`, exactly as in
    /// [`Self::ty`], where the arrow's sides are `ty_atom`s and `ty_atom`
    /// falls through to this function.
    fn expr(&mut self) -> R<Expr> {
        // `<- e` — a nested bind (docs/language/sequencing-surface-design.md §3.2): at
        // the head of an expression, so `f(<- e, y)`, `(<- e)` and
        // `match <- e { … }` all read it. It takes the whole expression after
        // it. The enclosing block or λ lowers it when it closes
        // ([`crate::try_lower::binds_in_block`]).
        if matches!(self.peek(), TokKind::LArrow) {
            let start = self.bump().span;
            let input = self.expr()?;
            let span = start.join(input.span);
            return Ok(crate::try_lower::bind_marker(input, span));
        }
        // The codomain restriction is a rule about **this rung**, not about
        // everything below it: once the parse descends into a bracket, a `↔`
        // there cannot be the enclosing arrow's, so the restriction has
        // nothing left to protect. Lift it for the operands and put it back
        // before the `↔` decision — the same bracket escape hatch
        // [`Parser::no_eq`] documents, which `no_iff` claimed to mirror and
        // did not (issues/iff-in-type-valued-body.md).
        let restricted = std::mem::replace(&mut self.no_iff, false);
        let out = self.expr_rung(restricted);
        self.no_iff = restricted;
        out
    }

    /// [`Self::expr`]'s rung, with the codomain restriction already lifted for
    /// the operands. `restricted` is the value it was lifted from — the one
    /// bit the `↔` decision itself still needs.
    fn expr_rung(&mut self, restricted: bool) -> R<Expr> {
        // The turnstile is the loosest expression form and extends rightward
        // exactly like a lambda body. It is recognized before parsing its
        // identifier-headed left side; without the complete binder-prefix
        // lookahead, an ordinary variable would be consumed before we learned
        // whether a `⊢` followed (issues/sequent-binder-expression.md).
        if self.at_sequent_binders() {
            return self.sequent_expr();
        }
        // `apply f; give a; b` is ordinary n-ary application with its
        // argument bodies written in goal order. `apply` remains contextual:
        // `apply(x)` is still a call to a function named `apply`, and a bare
        // `apply` is still a variable. The top-level semicolon is the exact
        // discriminator for the new form.
        if self.starts_apply_expr() {
            return self.apply_expr();
        }
        let lhs = self.expr_no_iff()?;
        if restricted {
            return Ok(lhs);
        }
        self.iff_rung(lhs)
    }

    /// The `↔` rung, given its left operand.
    ///
    /// `↔` is the loosest rung of all — looser than `->`, so `P -> Q ↔ R` is
    /// `(P -> Q) ↔ R` — and **non-associative**, for the reason the comparison
    /// rung is: `P ↔ Q ↔ R` has two readings and no reason to prefer either,
    /// and a bi-implication between bi-implications is not what anyone writing
    /// it meant.
    ///
    /// Split out of [`Self::expr_rung`] because it has a second caller:
    /// [`Self::ty`]'s binder-headed paths build their Π and return it, so
    /// without this they sit *below* the loosest rung and
    /// `(a: A) -> P(a) ↔ R` is a parse error rather than the reading
    /// `P -> Q ↔ R` already gets
    /// (issues/binder-headed-arrow-as-connective-operand.md).
    fn iff_rung(&mut self, lhs: Expr) -> R<Expr> {
        if !matches!(self.peek(), TokKind::Iff) {
            return Ok(lhs);
        }
        self.bump();
        let rhs = self.expr_no_iff()?;
        let span = lhs.span.join(rhs.span);
        if matches!(self.peek(), TokKind::Iff) {
            return self.err(
                "`↔` does not chain: it is one non-associative level, so `P ↔ Q ↔ R` \
                 has no reading. Parenthesise the one that is meant to be an operand",
            );
        }
        Ok(connective("Iff", lhs, rhs, span))
    }

    /// Offer a binder-headed function type to the `↔` rung, which is looser
    /// than the arrow it was just built from.
    ///
    /// The Π is complete — binders *and* codomain — before the `↔` is applied,
    /// so the binder's scope is unchanged and the unparenthesised
    /// `(a: A) -> P(a) ↔ Q(a)` still leaves the right-hand `a` unbound. That
    /// is the reading [`issues/iff-in-type-valued-body.md`] asked be left
    /// alone; what changes here is only that it is a *reading* rather than a
    /// parse error.
    ///
    /// Declines while a codomain is being read, exactly as [`Self::expr_rung`]
    /// does: there the outer arrow's own `↔` is still to come.
    fn iff_after_fn_type(&mut self, pi: Ty) -> R<Ty> {
        if self.no_iff || !matches!(self.peek(), TokKind::Iff) {
            return Ok(pi);
        }
        let span = pi.span;
        let lhs = Expr { kind: ExprKind::TyLit(Box::new(pi)), span };
        let out = self.iff_rung(lhs)?;
        Ok(expr_as_ty(&out))
    }

    /// Does the cursor begin the contextual `apply <callee>;` form?
    ///
    /// Scan only to the end of this expression and ignore delimiters inside
    /// the callee. This keeps both `apply(x)` and a bare function value named
    /// `apply` source-compatible without reserving a lexer keyword.
    fn starts_apply_expr(&self) -> bool {
        if !self.at_kw("apply") || matches!(self.nth(1), TokKind::LParen) {
            return false;
        }
        let mut paren = 0usize;
        let mut bracket = 0usize;
        let mut semantic = 0usize;
        let mut brace = 0usize;
        for tok in self.toks.iter().skip(self.pos + 1) {
            match tok.kind {
                TokKind::LParen => paren += 1,
                TokKind::RParen if paren > 0 => paren -= 1,
                TokKind::LBracket => bracket += 1,
                TokKind::RBracket if bracket > 0 => bracket -= 1,
                TokKind::LSemantic => semantic += 1,
                TokKind::RSemantic if semantic > 0 => semantic -= 1,
                TokKind::LBrace => brace += 1,
                TokKind::RBrace if brace > 0 => brace -= 1,
                TokKind::Semi
                    if paren == 0 && bracket == 0 && semantic == 0 && brace == 0 =>
                {
                    return true;
                }
                TokKind::Comma
                | TokKind::RParen
                | TokKind::RBracket
                | TokKind::RSemantic
                | TokKind::RBrace
                    if paren == 0 && bracket == 0 && semantic == 0 && brace == 0 =>
                {
                    return false;
                }
                TokKind::Eof => return false,
                _ => {}
            }
        }
        false
    }

    /// `apply f; give a; b` → the same n-ary call as `f(a, b)`.
    ///
    /// Every `give` completes one non-final parameter; the last expression
    /// completes the last parameter without ceremony. Recursing through
    /// [`Self::expr`] makes chains read naturally:
    /// `apply f; apply g; x` is `f(g(x))`.
    fn apply_expr(&mut self) -> R<Expr> {
        let start = self.bump().span; // `apply`
        let callee = self.expr()?;
        self.expect(&TokKind::Semi, "`;` after the callee in `apply f; body`")?;

        let mut bodies = Vec::new();
        while self.eat_kw("give") {
            if matches!(self.peek(), TokKind::Semi | TokKind::RBrace | TokKind::Eof) {
                return self.err("an expression after `give`");
            }
            bodies.push(self.expr()?);
            self.expect(&TokKind::Semi, "`;` after a non-final `give` body")?;
        }
        if matches!(self.peek(), TokKind::RBrace | TokKind::Eof) {
            return self.err(
                "a final argument body after `apply`; use `give body;` only for non-final arguments",
            );
        }
        let last = self.expr()?;
        let span = start.join(last.span);
        bodies.push(last);

        // Named values on the apply line are parameter selections, not an
        // already-executed partial call: `apply trans(b := m); give p; q`
        // lowers to `trans(p, q, b := m)`. A positional call remains a
        // callable expression, so `apply make(x); y` means `make(x)(y)`.
        let (head, mut args, named, explicit) = match callee.kind {
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                goal_oriented: false,
            } if args.is_empty() && !named.is_empty() => (head, args, named, explicit),
            kind => (Box::new(Expr { kind, span: callee.span }), Vec::new(), Vec::new(), false),
        };
        args.extend(bodies);
        Ok(Expr {
            kind: ExprKind::App { head, args, named, explicit, goal_oriented: true },
            span,
        })
    }

    /// Does the cursor begin one or more sequent binders followed by `⊢`?
    ///
    /// Bare binders are identifiers. Annotated binders are one-per-group,
    /// `(x: A)`, exactly as for lambdas; their types may contain arbitrarily
    /// nested parentheses, so the lookahead balances rather than attempting to
    /// recognize the type grammar. This is only a discriminator: the real
    /// parser below still owns every diagnostic.
    fn at_sequent_binders(&self) -> bool {
        let mut i = self.pos;
        loop {
            match self.toks.get(i).map(|t| &t.kind) {
                Some(TokKind::Ident(_)) => {
                    i += 1;
                }
                Some(TokKind::LParen)
                    if matches!(self.toks.get(i + 1).map(|t| &t.kind), Some(TokKind::Ident(_)))
                        && matches!(self.toks.get(i + 2).map(|t| &t.kind), Some(TokKind::Colon)) =>
                {
                    let mut depth = 0usize;
                    loop {
                        match self.toks.get(i).map(|t| &t.kind) {
                            Some(TokKind::LParen) => depth += 1,
                            Some(TokKind::RParen) => {
                                depth -= 1;
                                if depth == 0 {
                                    i += 1;
                                    break;
                                }
                            }
                            Some(TokKind::Eof) | None => return false,
                            _ => {}
                        }
                        i += 1;
                    }
                }
                _ => break,
            }
            if matches!(self.toks.get(i).map(|t| &t.kind), Some(TokKind::Turnstile)) {
                return true;
            }
        }
        false
    }

    /// Parse the binder prefix shared by a one-expression sequent and a
    /// sequent-headed block. The latter needs the turnstile span to delimit
    /// the transparent block synthesized for a long body.
    fn sequent_binders(&mut self) -> R<(Vec<LamBinder>, Span, Span)> {
        let start = self.peek_span();
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                TokKind::Ident(_) => {
                    let (name, span) = self.binder_ident("sequent binder")?;
                    binders.push(LamBinder { name, ty: None, implicit: false, span });
                }
                TokKind::LParen => {
                    let open = self.bump().span;
                    let (name, _) = self.binder_ident("sequent binder")?;
                    self.expect(&TokKind::Colon, "`:` (annotated sequent binder)")?;
                    let ty = self.ty()?;
                    let close = self.expect(&TokKind::RParen, "`)`")?;
                    binders.push(LamBinder {
                        name,
                        ty: Some(ty),
                        implicit: false,
                        span: open.join(close),
                    });
                }
                _ => break,
            }
            if matches!(self.peek(), TokKind::Turnstile) {
                break;
            }
        }
        let turnstile =
            self.expect(&TokKind::Turnstile, "`⊢` (a sequent binder is `x ⊢ body`)")?;
        Ok((binders, start, turnstile))
    }

    /// `x y ⊢ body` / `(x: A) ⊢ body`: a checking-position spelling of
    /// the ordinary lambda `λ x y => body`. Parser lowering is intentional;
    /// dependent checking and every diagnostic after the spelling disappears
    /// are exactly the existing lambda path's behavior.
    fn sequent_expr(&mut self) -> R<Expr> {
        let propagation_start = self.propagation_count;
        let (binders, start, _) = self.sequent_binders()?;
        let body = if std::mem::take(&mut self.motive_body) {
            let ty = self.ty()?;
            let span = ty.span;
            Expr { kind: ExprKind::TyLit(Box::new(ty)), span }
        } else {
            self.propagation_depth += 1;
            let body = self.expr();
            self.propagation_depth -= 1;
            body?
        };
        let span = start.join(body.span);
        let body = if self.propagation_count != propagation_start {
            for binder in &binders { if let Some(t) = &binder.ty { crate::try_lower::reject_type(t)?; } }
            crate::try_lower::expression(body, &mut self.next_hygienic)?
        } else { body };
        let body = crate::try_lower::binds_in_expression(body, &mut self.next_hygienic)?;
        Ok(Expr { kind: ExprKind::Lam { binders, body: Box::new(body) }, span })
    }

    /// [`Self::expr`] without its `↔` rung — the level `↔`'s two operands are
    /// read at, and the whole of the expression grammar otherwise.
    fn expr_no_iff(&mut self) -> R<Expr> {
        // `∀ x: A, P` and `∃ x: A, P`. Binder forms, so they come first and
        // their bodies run to the right as far as they can, exactly like `λ`.
        if matches!(self.peek(), TokKind::Forall | TokKind::Exists) {
            return self.quantifier();
        }
        // `(x: A) -> B`. The same three-token lookahead `ty()` uses; `:` is
        // not in the expression grammar, so a binder-headed group cannot be
        // anything else.
        if self.at_binder_group() {
            let ty = self.ty()?;
            let span = ty.span;
            return Ok(Expr { kind: ExprKind::TyLit(Box::new(ty)), span });
        }
        let lhs = self.connectives()?;
        if !matches!(self.peek(), TokKind::Arrow) {
            return Ok(lhs);
        }
        // `A -> B`: read what we have as the domain and let `ty()` take the
        // (right-associative) codomain, so the two spellings share one parse.
        self.bump();
        let dom = expr_as_ty(&lhs);
        let cod = self.cod(|p| p.ty())?;
        let span = lhs.span.join(cod.span);
        let kind = TyKind::Fn {
            binder: None,
            implicit: false,
            dom: Box::new(dom),
            cod: Box::new(cod),
        };
        Ok(Expr { kind: ExprKind::TyLit(Box::new(Ty { kind, span })), span })
    }

    /// The **comparison level**: one non-associative rung, loosest of all, sitting
    /// above the arithmetic table (`a + b <= c` is `Le(add(a, b), c)`).
    ///
    /// Four spellings share it, because they are one notion — a relation
    /// between two arithmetic expressions — and because sharing a rung is what
    /// makes chaining impossible:
    ///
    /// - `a = b`, the identity-type former (an [`ExprKind::Eq`], not a call —
    ///   the elaborator never sees `=` as a `Call`);
    /// - `a ≠ b`, direct notation for `¬(a = b)`, desugared here to the
    ///   same `Not` application and equality node as that longer spelling;
    /// - `a <= b`, which falls back to `Le(a, b)`, the *proposition* from
    ///   lib/certgen/ir_v1.hthr, never the boolean `leb`; a computational position
    ///   calls `leb` by name (issues/comparison-operators.md);
    /// - `a < b`, whose fallback `lt` has no lib target yet — it stays here so
    ///   `<` cannot chain either, and so the speculative type-argument parse
    ///   keeps its documented fallback (docs/language/surface-polymorphism.md §1).
    ///
    /// The two relational rungs emit their symbol like the arithmetic ones do;
    /// the library designates neither, so both are the fallback name and
    /// nothing about them changed.
    ///
    /// Non-associativity is structural first: the right operand is read with
    /// [`Parser::no_eq`] set, so it is an *arithmetic* expression and cannot
    /// grow a second comparison of its own. What is left over is then a
    /// dangling operator, which would surface as whatever error the caller
    /// happens to raise next — so a trailing `<=`/`=`/`==` gets a targeted
    /// message instead. A trailing `=` was exempt while an annotated `let`'s
    /// binder could land exactly there; the annotation position now suppresses
    /// this whole rung (docs/language/let-and-blocks-design.md §3), so a `=` after a
    /// completed comparison is *always* a chain and can say so.
    fn comparison(&mut self, lhs: Expr) -> R<Expr> {
        let out = match self.peek() {
            TokKind::Eq | TokKind::EqEq => {
                self.expect_eq("equality type `a = b`")?;
                let rhs = self.with_eq(true, |p| p.expr_bp(0))?;
                let span = lhs.span.join(rhs.span);
                Expr { kind: ExprKind::Eq(Box::new(lhs), Box::new(rhs)), span }
            }
            TokKind::Ne => {
                let op = self.bump().span;
                let rhs = self.with_eq(true, |p| p.expr_bp(BOOL_CHAIN_BP))?;
                let eq_span = lhs.span.join(rhs.span);
                let eq = Expr { kind: ExprKind::Eq(Box::new(lhs), Box::new(rhs)), span: eq_span };
                let head = Expr { kind: ExprKind::Var("Not".to_string()), span: op };
                Expr {
                    kind: ExprKind::App {
                        head: Box::new(head),
                        args: vec![eq],
                        named: Vec::new(),
                        explicit: false,
                        goal_oriented: false,
                    },
                    span: eq_span,
                }
            }
            TokKind::LtEq | TokKind::Lt | TokKind::Approx => {
                let sym = match self.peek() {
                    TokKind::LtEq => "<=",
                    TokKind::Approx => "≈",
                    _ => "<",
                };
                self.bump();
                let rhs = self.with_eq(true, |p| p.expr_bp(BOOL_CHAIN_BP))?;
                let span = lhs.span.join(rhs.span);
                op_call(sym, OpFixity::Infix, vec![lhs, rhs], span)
            }
            _ => return Ok(lhs),
        };
        const CHAIN: &str = "comparisons do not chain: `=`, `≠`, `≈`, `<=` and `<` share one \
             non-associative level, so `a <= b <= c` has no reading. Write the two \
             comparisons separately, or parenthesise the one that is meant to be an \
             operand";
        match self.peek() {
            // An annotation's relation ends at the binding's own `=`.
            TokKind::Eq if self.annotation_rel => Ok(out),
            TokKind::LtEq | TokKind::Lt | TokKind::Approx | TokKind::Eq | TokKind::Ne => self.err(CHAIN),
            TokKind::EqEq => {
                self.err(format!("{CHAIN} (and `==` is not used in Heather: equality is `=`)"))
            }
            _ => Ok(out),
        }
    }

    /// The **connective level**: `∧` and `∨`, sitting between the comparison
    /// rung below and `->` above.
    ///
    /// Looser than comparison, which is what makes `n <= m ∧ m <= k` the
    /// conjunction of two comparisons rather than a comparison against a
    /// conjunction — and the opposite of where `&&`/`||` sit, deliberately.
    /// The Boolean doubles are *arithmetic*: they combine `Bool` values, and
    /// `x && True = x` wants to be `(x && True) = x`. These combine
    /// propositions, and a proposition is what a comparison produces.
    ///
    /// Both are **right-associative** (`left_bp > right_bp`, the convention
    /// `++` set), and for the same proof-relevant reason: `P ∧ (Q ∧ R)` is the
    /// nesting `And(p, And(q, r))` builds and projects, so the fixity that
    /// matches the term shape is the one that saves a re-association.
    fn connectives(&mut self) -> R<Expr> {
        self.connectives_bp(0)
    }

    /// At a binary connective — the token set `ty_atom`'s two early-returning
    /// atom rules have to decline, since an atom before one of these is an
    /// operand rather than a whole type. `¬` is absent on purpose: it is
    /// prefix, so it can never follow an atom.
    fn at_connective(&self) -> bool {
        matches!(self.peek(), TokKind::Wedge | TokKind::Vee | TokKind::Iff)
    }

    fn connectives_bp(&mut self, min_bp: u8) -> R<Expr> {
        let mut lhs = self.logic_operand()?;
        loop {
            let (name, l_bp, r_bp) = match self.peek() {
                TokKind::Wedge => ("And", 4, 3),
                TokKind::Vee => ("Or", 2, 1),
                _ => break,
            };
            if l_bp < min_bp {
                break;
            }
            self.bump();
            let rhs = self.connectives_bp(r_bp)?;
            let span = lhs.span.join(rhs.span);
            lhs = connective(name, lhs, rhs, span);
        }
        Ok(lhs)
    }

    /// One operand of the connective level: a comparison, optionally negated.
    ///
    /// `¬` is prefix and binds **tighter than `∧`** but **looser than the
    /// comparison rung**, so `¬P ∧ Q` is `(¬P) ∧ Q` and `¬ a = b` is
    /// `¬(a = b)` — the second being the reading everyone writing it wants,
    /// and the one Lean's precedence gives too. It recurses on itself, so
    /// `¬¬P` is a double negation and not a parse error.
    ///
    /// `Not` is a `fn` taking a `Type`, so this is an ordinary call and not a
    /// [`connective`]: unlike `∧`/`∨`/`↔` it has no type parameters to fill.
    fn logic_operand(&mut self) -> R<Expr> {
        if matches!(self.peek(), TokKind::Neg) {
            let start = self.bump().span;
            let inner = self.logic_operand()?;
            let span = start.join(inner.span);
            let head = Expr { kind: ExprKind::Var("Not".to_string()), span: start };
            return Ok(Expr {
                kind: ExprKind::App {
                    head: Box::new(head),
                    args: vec![inner],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            });
        }
        if self.no_eq {
            let lhs = self.expr_bp(0)?;
            let relation = matches!(self.peek(), TokKind::LtEq | TokKind::Lt | TokKind::Approx | TokKind::Ne);
            return if self.annotation_rel && relation { self.comparison(lhs) } else { Ok(lhs) };
        }
        // `&&` and `||` sit between the relations and `=`: `0 < j && key < b`
        // is the conjunction of two tests, as in Rust, while `x && True = x`
        // is still `(x && True) = x`.
        let lhs = self.bool_chain(0)?;
        self.comparison(lhs)
    }

    /// `r₁ && r₂ || …` over relation operands ([`Self::relation_operand`]),
    /// `&&` binding tighter than `||`, both left-associative. A relation
    /// among the operands is read as its decision, `decide_bit<r>()`, since
    /// `&&` combines `Bool`s.
    fn bool_chain(&mut self, min_bp: u8) -> R<Expr> {
        let mut lhs = self.relation_operand()?;
        loop {
            let (sym, l_bp, r_bp) = match self.peek() {
                TokKind::PipePipe => ("||", 1, 2),
                TokKind::AmpAmp => ("&&", 3, 4),
                _ => break,
            };
            if l_bp < min_bp {
                break;
            }
            self.bump();
            let rhs = self.bool_chain(r_bp)?;
            let span = lhs.span.join(rhs.span);
            lhs = op_call(sym, OpFixity::Infix, vec![decided(lhs), decided(rhs)], span);
        }
        Ok(lhs)
    }

    /// An operand of `&&`/`||`: an arithmetic expression, or a relation
    /// (`<`, `<=`, `≈`, `≠`) between two (the `=` rung is looser, read by
    /// [`Self::comparison`] after the chain).
    fn relation_operand(&mut self) -> R<Expr> {
        let lhs = self.expr_bp(BOOL_CHAIN_BP)?;
        if matches!(self.peek(), TokKind::LtEq | TokKind::Lt | TokKind::Approx | TokKind::Ne) {
            return self.comparison(lhs);
        }
        Ok(lhs)
    }

    /// `∀ x: A, P` and `∃ x: A, P` — one binder group, then the body, which
    /// runs to the right as far as it can exactly as a `λ`'s does.
    ///
    /// `∀` is a **synonym**, not a new form: it desugars to the `(x: A) -> P`
    /// the surface already had, so nothing downstream learns a second
    /// spelling of the dependent function type. `∃` is a call to
    /// `logic::Exists` with the type argument supplied *from the binder's own
    /// annotation* — which is what makes the sugar worth having, since the
    /// bare record spelling cannot infer it
    /// (issues/exists-type-arg-not-inferred.md).
    ///
    /// **One binder group per quantifier**, names sharing one annotation:
    /// `∀ x, y: A, P` writes, `∀ x: A, y: B, P` does not. The restriction is
    /// forced rather than chosen — after the annotation, a comma may begin
    /// either another group or the body, and the body may itself be a bare
    /// name, so the two readings are genuinely ambiguous. Nest instead:
    /// `∀ x: A, ∀ y: B, P`.
    fn quantifier(&mut self) -> R<Expr> {
        let exists = matches!(self.peek(), TokKind::Exists);
        let kw = if exists { "∃" } else { "∀" };
        let start = self.bump().span;
        let mut names = vec![self.ident("binder name after a quantifier")?];
        while matches!(self.peek(), TokKind::Comma) {
            self.bump();
            names.push(self.ident("binder name after a quantifier")?);
        }
        if !matches!(self.peek(), TokKind::Colon) {
            return self.err(format!(
                "this quantifier's binder has no type: write `{kw} x: A, P`. One binder \
                 group per quantifier — a comma-separated run of names shares ONE \
                 annotation, and a second group is written by nesting \
                 (`{kw} x: A, {kw} y: B, P`), because after the annotation a comma \
                 could begin either a group or the body"
            ));
        }
        self.bump(); // `:`
        let dom = self.ty()?;
        self.expect(&TokKind::Comma, "`,` between a quantifier's binder and its body")?;
        // A second binder group, written flat. `:` is not in the expression
        // grammar, so `ident :` here cannot be the body and the mistake is
        // unambiguous — worth catching, because the parse otherwise ends at
        // the name and the error surfaces as whatever the *declaration*
        // expected next, a span away from the cause.
        if matches!(self.peek(), TokKind::Ident(_)) && matches!(self.nth(1), TokKind::Colon) {
            return self.err(format!(
                "one binder group per quantifier: write `{kw} x: A, {kw} y: B, P` rather \
                 than `{kw} x: A, y: B, P`. A comma-separated run of names may share ONE \
                 annotation (`{kw} x, y: A, P`), but after the annotation a comma could \
                 begin either a second group or the body, so only nesting is read"
            ));
        }
        let body = self.expr()?;
        let span = start.join(body.span);
        if !exists {
            let binders = names.iter().map(|(n, _)| (n.clone(), dom.clone())).collect();
            let ty = curry(binders, expr_as_ty(&body), false, span);
            return Ok(Expr { kind: ExprKind::TyLit(Box::new(ty)), span });
        }
        let mut out = body;
        for (name, nsp) in names.into_iter().rev() {
            let lam = Expr {
                kind: ExprKind::Lam {
                    binders: vec![LamBinder {
                        name,
                        ty: Some(dom.clone()),
                        implicit: false,
                        span: nsp,
                    }],
                    body: Box::new(out),
                },
                span,
            };
            let head = Expr { kind: ExprKind::Var("Exists".to_string()), span: start };
            let head = Expr {
                kind: ExprKind::TyApp { head: Box::new(head), args: vec![dom.clone()] },
                span: start,
            };
            out = Expr {
                kind: ExprKind::App {
                    head: Box::new(head),
                    args: vec![lam],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            };
        }
        Ok(out)
    }

    /// `( ident :` — the start of a dependent function type's binder group;
    /// or `( ident ,`, the multi-binder form (issues/multi-binder-function-types.md).
    ///
    /// The comma form needs more than three tokens to recognise, because
    /// `(a, b)` on its own is not a binder list and must stay whatever it was
    /// (nothing, today — but the parenthesis rule is load-bearing enough that
    /// the lookahead pays for itself). The discriminator is the same one
    /// [`Self::group_is_type`] uses one level down: a `:` at the group's own
    /// depth, which the expression grammar has nowhere to put, or a `->`
    /// straight after the group, which no expression can be followed by. The
    /// second disjunct is what lets `(x, y) -> C` reach the binder-list parser
    /// and get told what it is missing, instead of failing at the comma with
    /// `expected )`.
    fn at_binder_group(&self) -> bool {
        matches!(self.peek(), TokKind::LParen)
            && matches!(self.nth(1), TokKind::Ident(_))
            && match self.nth(2) {
                // `(x: A)` with no arrow after it is an ascription.
                TokKind::Colon => self.group_then_arrow(),
                TokKind::Comma => self.group_binds(),
                _ => false,
            }
    }

    /// Does the parenthesised group at the cursor stand immediately before a
    /// `->`? What tells a binder `(x: A) -> B` from an ascription `(x: A)`.
    fn group_then_arrow(&self) -> bool {
        let mut depth = 0usize;
        let mut i = self.pos;
        while i < self.toks.len() {
            match self.toks[i].kind {
                TokKind::LParen => depth += 1,
                TokKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.nth(i + 1 - self.pos), TokKind::Arrow);
                    }
                }
                TokKind::Eof => break,
                _ => {}
            }
            i += 1;
        }
        false
    }

    /// Does the parenthesised group at the cursor either carry an annotation
    /// of its own (a `:` at the group's depth, outside any nested brace or
    /// bracket — a record literal's `a: 1` is not this) or stand immediately
    /// before a `->`? Either answer means a binder list is intended.
    fn group_binds(&self) -> bool {
        let mut depth = 0usize;
        let mut inner = 0usize; // braces and brackets nested inside the group
        let mut i = self.pos;
        while i < self.toks.len() {
            match self.toks[i].kind {
                TokKind::LParen => depth += 1,
                TokKind::LBrace | TokKind::LBracket | TokKind::LSemantic if depth == 1 => inner += 1,
                TokKind::RBrace | TokKind::RBracket | TokKind::RSemantic
                    if depth == 1 && inner > 0 =>
                {
                    inner -= 1;
                }
                TokKind::Colon if depth == 1 && inner == 0 => return true,
                TokKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.nth(i + 1 - self.pos), TokKind::Arrow);
                    }
                }
                TokKind::Eof => break,
                _ => {}
            }
            i += 1;
        }
        false
    }

    /// Run `f` with the next lambda body flagged as a motive body. Restores
    /// the flag afterwards, so a motive that is not a lambda at all (the
    /// elaborator's diagnostic, not the grammar's) leaves nothing set.
    fn with_motive<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.motive_body, true);
        let r = f(self);
        self.motive_body = saved;
        r
    }

    /// Run `f` with `a = b` suppressed (or restored). Mirrors
    /// [`Parser::with_record_lit`].
    fn with_eq<T>(&mut self, no: bool, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.no_eq, no);
        let saved_rel = std::mem::replace(&mut self.annotation_rel, false);
        let r = f(self);
        self.no_eq = saved;
        self.annotation_rel = saved_rel;
        r
    }

    /// Read a binding's annotation: [`Self::ty`] with `=` suppressed but the
    /// other relations kept ([`Parser::annotation_rel`]), so the binder `=`
    /// ends it and `let k: a <= b = h;` needs no parentheses.
    fn annotation(&mut self) -> R<Ty> {
        self.with_eq(true, |p| {
            p.annotation_rel = true;
            p.ty()
        })
    }

    /// Run `f` with `P ↔ Q` suppressed. The codomain rule; see
    /// [`Parser::no_iff`].
    fn cod<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.with_iff(true, f)
    }

    /// Run `f` with the `↔` restriction set to `no` (or restored). Mirrors
    /// [`Parser::with_eq`]; [`Self::cod`] is the setter and
    /// [`Self::expr`]/[`Self::ty_atom`] are the bracket lifts.
    fn with_iff<T>(&mut self, no: bool, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = std::mem::replace(&mut self.no_iff, no);
        let r = f(self);
        self.no_iff = saved;
        r
    }

    /// Binding powers for the infix operators. `(symbol, left_bp, right_bp)`;
    /// `right_bp > left_bp` makes every operator left-associative.
    ///
    /// The first element used to be the *name* the operator desugared to
    /// (`add`, `mul`), which made `+` mean one global everywhere. It is now the
    /// symbol as written, and what it means is resolution's business
    /// (docs/language/classes/operators-onto-classes-design.md §2.1) — the fixed name survives
    /// as that resolver's last rung, so nothing that parsed before this change
    /// elaborates differently.
    /// `&&` and `||` sit *below* `+`/`*` and *above* the comparison rung —
    /// deliberately unlike C, where `&&` is looser than `<=`. The comparison
    /// level here is propositional (`=` is the identity type, `<=` falls back
    /// to `Le`), so a Boolean operand never wants to contain one, and theorem
    /// statements want the arithmetic reading: `x && True = x` is
    /// `(x && True) = x`, exactly as `x + A.unit = x` already relies on
    /// (issues/bool-operator-designations.md).
    ///
    /// The bitwise and shift rungs (issues/integer-operator-symbols.md) sit
    /// between `&&` and `+` in Rust's order: `|` loosest, then `⊕` (Rust's
    /// `^`, issues/bitvec-xor-complement-symbols.md), then `&`, then
    /// `<<`/`>>`, so `a & b << 1` is `a & (b << 1)`, `a ⊕ b & c` is
    /// `a ⊕ (b & c)` and `x + y << 2` is
    /// `(x + y) << 2`. Rust's C-inherited trap does not exist here, since the
    /// comparison rung is below all of them: `a & m = 0` is `(a & m) = 0`.
    /// `/` and `%` share `*`'s rung, left-associative.
    fn infix_op(tok: &TokKind) -> Option<(&'static str, u8, u8)> {
        let sym = Self::op_symbol(tok)?;
        let (l, r) = Self::infix_binding(sym)?;
        Some((sym, l, r))
    }

    /// [`Self::infix_op`]'s binding powers, by the symbol a token spells: the
    /// one table, read by the parser and by [`operator_form`].
    fn infix_binding(sym: &str) -> Option<(u8, u8)> {
        match sym {
            "||" => Some((1, 2)),
            "&&" => Some((3, 4)),
            "|" => Some((5, 6)),
            "⊕" => Some((7, 8)),
            "&" => Some((9, 10)),
            "<<" => Some((11, 12)),
            ">>" => Some((11, 12)),
            "+" => Some((13, 14)),
            "-" => Some((13, 14)),
            "⊔" => Some((13, 14)),
            // `++` is RIGHT-associative (`left_bp > right_bp`), unlike its
            // rung-mates: fixity is proof-relevant here. `a ++ (b ++ c)` is
            // the shape `append`'s recursion unfolds against and the shape
            // every append lemma is stated in; the left-nested reading walks
            // `a` twice and meets no lemma head-on. `::`-style list notation,
            // when it lands, is right-associative by necessity, so the list
            // family reads uniformly (docs/showcase/README.md, friction 2).
            "++" => Some((14, 13)),
            "*" => Some((15, 16)),
            "/" => Some((15, 16)),
            "%" => Some((15, 16)),
            // `∙` sits on the multiplicative rung, which is where
            // issues/notation-extensibility.md's precedence-by-class scheme
            // puts a dot-shaped operator (`× ⊗ ∘ ∩`). Nothing in the library
            // mixes it with `+` — it is the *generic* operation, so a file that
            // writes it has one — but a rung had to be chosen and this is the
            // one its shape asks for.
            "∙" => Some((15, 16)),
            // `⊓` binds tighter than `⊔`, as `*` does `+`: the lattice's
            // two operations read like the semiring's.
            "⊓" => Some((15, 16)),
            _ => None,
        }
    }

    /// The operator symbol a token spells, for every infix token in the
    /// grammar — the arithmetic rung and the comparison rung alike. `=` is
    /// **not** here: equality is a core form with a typing rule
    /// ([`ExprKind::Eq`] → the kernel's `Id`), not a notation, which is the
    /// test `issues/notation-extensibility.md` states for the distinction.
    fn op_symbol(tok: &TokKind) -> Option<&'static str> {
        match tok {
            TokKind::Plus => Some("+"),
            TokKind::Minus => Some("-"),
            TokKind::PlusPlus => Some("++"),
            TokKind::Star => Some("*"),
            TokKind::Slash => Some("/"),
            TokKind::Percent => Some("%"),
            TokKind::Amp => Some("&"),
            TokKind::Pipe => Some("|"),
            TokKind::OPlus => Some("⊕"),
            TokKind::Shl => Some("<<"),
            TokKind::Shr => Some(">>"),
            TokKind::Caret => Some("^"),
            TokKind::AmpAmp => Some("&&"),
            TokKind::PipePipe => Some("||"),
            TokKind::Bullet => Some("∙"),
            TokKind::Join => Some("⊔"),
            TokKind::Meet => Some("⊓"),
            TokKind::Approx => Some("≈"),
            TokKind::LtEq => Some("<="),
            TokKind::Lt => Some("<"),
            _ => None,
        }
    }

    /// A **designation reference** in argument-initial position — `Monoid(+)`,
    /// `Semiring(+, *)`, `A::CommMonoid(+)`
    /// (docs/language/classes/operation-indexed-classes-design.md §7, decided there).
    ///
    /// An infix operator token can never *begin* an expression, so directly
    /// after `(` or `,` it has exactly one reading and this needs no
    /// backtracking. The rule reserved with it: a lone operator token between
    /// delimiters is *always* the designation reference, which is what keeps
    /// the position free for a future prefix operator — so the symbol must be
    /// followed by `,` or `)` to be read as one.
    fn op_symbol_arg(&mut self) -> Option<Expr> {
        let sym = Self::op_symbol(self.peek())?;
        if !matches!(self.nth(1), TokKind::Comma | TokKind::RParen) {
            return None;
        }
        let span = self.bump().span;
        Some(Expr {
            kind: ExprKind::OpSymbol { symbol: sym.to_string(), fixity: OpFixity::Infix },
            span,
        })
    }

    /// Precedence-climbing loop: parse a postfix expression, then fold in
    /// infix operators whose left binding power is at least `min_bp`.
    fn expr_bp(&mut self, min_bp: u8) -> R<Expr> {
        let mut lhs = self.prefix()?;
        while let Some((sym, l_bp, r_bp)) = Self::infix_op(self.peek()) {
            if l_bp < min_bp {
                break;
            }
            // `⟨a |⟩`: a `|` against the closing `⟩` marks the left
            // injection ([`Self::anonymous_constructor_expr`]), and is no
            // bitwise or with a missing operand.
            if matches!(self.peek(), TokKind::Pipe) && matches!(self.nth(1), TokKind::RAngle) {
                break;
            }
            self.bump();
            let rhs = self.expr_bp(r_bp)?;
            let span = lhs.span.join(rhs.span);
            lhs = op_call(sym, OpFixity::Infix, vec![lhs, rhs], span);
        }
        Ok(lhs)
    }

    /// Value-level prefix operators. Unary `-` is an operator symbol rather
    /// than a literal sign: `-3` has exactly the AST of `-(3)`. Boolean `!`
    /// follows the same carrier-directed path. They bind more tightly than
    /// every infix rung, include postfix applications in their operands, and
    /// recurse so `--a` and `!!b` are nested applications.
    ///
    /// The one exception is `^`, which binds tighter than a prefix operator
    /// (`-x ^ 2` is `-(x ^ 2)`, as in mathematics and Lean): a prefix
    /// operator's operand is a [`Self::power`], not a bare postfix.
    fn prefix(&mut self) -> R<Expr> {
        let symbol = match self.peek() {
            TokKind::Minus => "-",
            TokKind::Bang => "!",
            TokKind::Tilde => "~",
            // A cast, at `-`'s precedence (docs/language/casting-design.md §5.2):
            // `↑n - 1` subtracts at the target, `↑(n - 1)` casts the
            // difference.
            TokKind::UpArrow => "↑",
            TokKind::BigSum | TokKind::BigProd => return self.big_operator(),
            _ => return self.power(),
        };
        let start = self.bump().span;
        let inner = self.prefix()?;
        let span = start.join(inner.span);
        Ok(op_call(symbol, OpFixity::Prefix, vec![inner], span))
    }

    /// `∑ k < n, e` and `∏ k < n, e` — the big-operator binder
    /// (issues/notation-extensibility.md; docs/library/analysis-foundations-design.md
    /// §4). A **synonym**, as `∀` is: it desugars to the range sum
    /// `MonoidRel::range(+, n, λ (k: Nat) => e)` (`*` for `∏`) of
    /// std/big_operator, so a sum is that call and every law about range sums
    /// applies to it unchanged. The operator is the bare symbol, so it means
    /// whatever `+` or `*` means at the body's carrier, a constraint binder's
    /// operation included.
    ///
    /// It sits at the **prefix** level, so it is an operand: `x + ∑ k < n, e`
    /// and `x ≈ ∑ k < n, e` read as written. The body is an *arithmetic*
    /// expression and runs right as far as one can, so `∑ k < n, f(k) + 1`
    /// sums `f(k) + 1` (the mathematical reading; narrowing needs
    /// parentheses) and `∑ k < n, f(k) ≈ s` compares the whole sum with `s`.
    /// The bound is arithmetic too, and the index is a `Nat` below it.
    fn big_operator(&mut self) -> R<Expr> {
        let (glyph, symbol) = match self.peek() {
            TokKind::BigProd => ("∏", "*"),
            _ => ("∑", "+"),
        };
        let start = self.bump().span;
        let (name, nsp) = self.ident("index name after a big operator")?;
        if !matches!(self.peek(), TokKind::Lt) {
            return self.err(format!(
                "a big operator ranges below a bound: write `{glyph} {name} < n, e`, \
                 which reads the indices `0, 1, …, n - 1`"
            ));
        }
        self.bump();
        let bound = self.expr_bp(0)?;
        self.expect(&TokKind::Comma, "`,` between a big operator's bound and its body")?;
        let body = self.expr_bp(0)?;
        let span = start.join(body.span);
        let lam = Expr {
            kind: ExprKind::Lam {
                binders: vec![LamBinder {
                    name,
                    ty: Some(Ty { kind: TyKind::Nat, span: nsp }),
                    implicit: false,
                    span: nsp,
                }],
                body: Box::new(body),
            },
            span,
        };
        let op = Expr { kind: ExprKind::OpSymbol { symbol: symbol.to_string(), fixity: OpFixity::Infix }, span: start };
        let head = Expr { kind: ExprKind::Var("MonoidRel::range".to_string()), span: start };
        Ok(Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args: vec![op, bound, lam],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        })
    }

    /// `base ^ exponent` (docs/library/inverse-power-notation-design.md §2): above
    /// every infix rung and above the prefix operators, below postfix forms
    /// (`x⁻¹ ^ 2` is `(x⁻¹) ^ 2`, `x.f ^ 2` is `(x.f) ^ 2`). Right-associative,
    /// and the exponent is a whole [`Self::prefix`], so `a ^ b ^ c` is
    /// `a ^ (b ^ c)` and `x ^ -1` needs no parentheses.
    fn power(&mut self) -> R<Expr> {
        let base = self.postfix()?;
        if !matches!(self.peek(), TokKind::Caret) {
            return Ok(base);
        }
        self.bump();
        let exponent = self.prefix()?;
        let span = base.span.join(exponent.span);
        Ok(op_call("^", OpFixity::Infix, vec![base, exponent], span))
    }

    /// An atom followed by zero or more field accesses `.f`, method calls
    /// `.f(args)` / `.f<T, …>(args)`, a record literal `D { … }`, and zero or
    /// more applications `(args)` — so the head of a call can be any
    /// expression: `g(a)(b)`, `(λ x => x)(3)`
    /// (docs/language/surface-function-types.md §1.3).
    ///
    /// `.f` is **not** desugared here any more. It used to become
    /// `f(args…, receiver)` — a call to a global with the receiver last;
    /// where the receiver goes is now the callee's business, decided by its
    /// `self` parameter (issues/method-receiver-position.md). That reading is
    /// wrong anyway for a record of functions, where
    /// `m.op(x)` must be `(m.op)(x)`, and choosing between the two needs the
    /// receiver's *type*. So the parser emits [`ExprKind::Dot`] and the
    /// elaborator decides, keeping the old desugaring as the fallback
    /// (docs/language/surface-records.md §4.2).
    fn postfix(&mut self) -> R<Expr> {
        let mut e = self.atom()?;
        if let Some((args, end)) = self.try_tyargs() {
            let span = e.span.join(end);
            e = Expr { kind: ExprKind::TyApp { head: Box::new(e), args }, span };
        }
        // `D { … }` / `D<T> { … }` — a record literal. Only on a *name* head,
        // and only where a block cannot follow (see `no_record_lit`).
        if matches!(self.peek(), TokKind::LBrace) && !self.no_record_lit {
            let (name, tyargs) = match &e.kind {
                ExprKind::Var(n) => (Some(n.clone()), Vec::new()),
                ExprKind::TyApp { head, args } => match &head.kind {
                    ExprKind::Var(n) => (Some(n.clone()), args.clone()),
                    _ => (None, Vec::new()),
                },
                _ => (None, Vec::new()),
            };
            if let Some(name) = name {
                e = self.record_lit(name, tyargs, e.span)?;
            }
        }
        loop {
            match self.peek() {
                // `e with { f = v, … }` — functional record update
                // (issues/record-update-syntax.md). `with` is a word only
                // here, before a `{`, so it names nothing else.
                _ if self.at_kw("with") && matches!(self.nth(1), TokKind::LBrace) => {
                    self.bump();
                    e = self.record_update(e)?;
                }
                _ if self.at_kw("decreasing") => {
                    let start = self.bump().span;
                    let (label, end) = self.ident("decrease label")?;
                    let ExprKind::App { named, .. } = &mut e.kind else {
                        return self.err("`decreasing` labels a recursive call: write `f(args) decreasing label`");
                    };
                    named.push(NamedArg { name: format!("#decreasing:{label}"), name_span: end,
                        expr: Expr { kind: ExprKind::Num(Numeral::ZERO), span: end }, span: start.join(end) });
                    e.span = e.span.join(end);
                }
                // `x⁻¹` — the postfix inverse, binding as tightly as `.f`
                // (docs/library/inverse-power-notation-design.md §2).
                TokKind::SupInverse => {
                    let end = self.bump().span;
                    let span = e.span.join(end);
                    e = op_call("⁻¹", OpFixity::Postfix, vec![e], span);
                }
                TokKind::Hole(None) if self.tight(self.pos) => {
                    if self.propagation_depth == 0 {
                        return self.err("postfix `?` needs an enclosing function or lambda body");
                    }
                    self.propagation_count += 1;
                    let end = self.bump().span;
                    let span = e.span.join(end);
                    e = Expr { kind: ExprKind::App {
                        head: Box::new(Expr { kind: ExprKind::Var(crate::try_lower::TRY.into()), span: end }),
                        args: vec![e], named: Vec::new(), explicit: false, goal_oriented: false,
                    }, span };
                }
                // `a..b`: a range's `..` (a `for` header, §5.2), never a
                // member access.
                TokKind::Dot if matches!(self.nth(1), TokKind::Dot) => {
                    if self.range_header { break; }
                    return self.err(
                        "`a..b` is a range only in a `for` header (`for i in a..b { … }`); elsewhere write \
                         `List::range_from(a, b - a)`",
                    );
                }
                TokKind::Dot => {
                    self.bump();
                    let (field, fsp) = self.ident("field or method name")?;
                    let (tyargs, member_end) = self
                        .try_tyargs()
                        .map_or_else(|| (Vec::new(), fsp), |(args, end)| (args, end));
                    let (args, named, end) = if matches!(self.peek(), TokKind::LParen) {
                        self.bump();
                        let (args, named, end) = self.call_args()?;
                        (Some(args), named, end)
                    } else {
                        (None, Vec::new(), member_end)
                    };
                    let span = e.span.join(end);
                    e = Expr {
                        kind: ExprKind::Dot {
                            recv: Box::new(e),
                            name: field,
                            tyargs,
                            args,
                            named,
                        },
                        span,
                    };
                }
                // `Impl(add, BinNat)::refines` — a member of an *applied*
                // owner's namespace (docs/native/repr-access-spellings-design.md §4).
                // An unapplied owner never reaches here: `A::b` is one lexer
                // token, so the standalone `::` only appears after something
                // the lexer could not join, and that was a parse error in
                // every expression position before this arm.
                //
                // What it builds is a `Var` whose name is the path as it is
                // *printed* — the owner rendered structurally, so the
                // referenceable string and the string `heather obligations`
                // prints are the same string by construction — rather than a
                // new `ExprKind` every AST walk would have to learn.
                TokKind::ColonColon => {
                    self.bump();
                    let (member, msp) = self.ident("a member name after `::`")?;
                    let Some(owner) = render_owner(&e) else {
                        return Err(ParseError {
                            msg: format!(
                                "`::` here needs an owner of the form `<name>(<name>, …)`: \
                                 an obligation path is `Impl(<op>, <repr>)::{member}`"
                            ),
                            span: e.span,
                        });
                    };
                    let span = e.span.join(msp);
                    e = Expr { kind: ExprKind::Var(format!("{owner}::{member}")), span };
                }
                TokKind::LParen => {
                    self.bump();
                    let (args, named, end) = self.call_args()?;
                    let span = e.span.join(end);
                    e = Expr {
                        kind: ExprKind::App {
                            head: Box::new(e),
                            args,
                            named,
                            explicit: false,
                            goal_oriented: false,
                        },
                        span,
                    };
                }
                // `xs[i]` — indexing (docs/language/surface-fin-indexing-design.md §5.1).
                // A pure extension: `[` opens a type (`[T; n]`) or a vector
                // literal only in *prefix* position, and it is in the follow
                // set of no expression production (statements end with `;`,
                // blocks with `}`, elements and arms with `,`), so an
                // expression followed by `[` was a parse error everywhere
                // before this arm. No lookahead, no backtracking.
                TokKind::LBracket => {
                    self.bump();
                    let idx = self.with_record_lit(false, |p| p.expr())?;
                    let end = self.expect(&TokKind::RBracket, "`]` (an index)")?;
                    let span = e.span.join(end);
                    e = Expr {
                        kind: ExprKind::Index { recv: Box::new(e), idx: Box::new(idx) },
                        span,
                    };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    /// `< T, … >` after an expression — explicit type application
    /// (docs/language/surface-polymorphism.md §1). `<` is *also* the `lt` operator
    /// ([`Self::comparison`]), so this is **speculative**: save the position, try, and
    /// restore on any failure. Backtracking is free (the parser is a token
    /// vector plus an index) and total, so unlike a lookahead heuristic it
    /// cannot be wrong about a program: `a < b` fails at the missing `>` and
    /// falls back to `lt`, `f<A>(x)` succeeds.
    ///
    /// The closing `>` alone is the discriminator — no `(` is required, so a
    /// bare `nil<Nat>` is a value. That is safe because `>` is not an
    /// expression operator (lexer.rs:28), so no `lt` expression can be
    /// followed by one.
    fn try_tyargs(&mut self) -> Option<(Vec<Ty>, Span)> {
        if !matches!(self.peek(), TokKind::Lt) {
            return None;
        }
        // A spaced `<` is a comparison, full stop — see [`Self::tight`].
        if !self.tight(self.pos) {
            return None;
        }
        if self.spec_seen_failing(self.pos, SITE_EXPR_TYARGS) {
            return None;
        }
        let save = self.pos;
        self.bump();
        let mut args = Vec::new();
        loop {
            match self.ty() {
                Ok(t) => args.push(t),
                Err(_) => return self.spec_fail(save, SITE_EXPR_TYARGS),
            }
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        if !matches!(self.peek(), TokKind::Gt) {
            return self.spec_fail(save, SITE_EXPR_TYARGS);
        }
        Some((args, self.bump().span))
    }

    /// Is the token at `idx` **tight** against the one before it — no
    /// whitespace, no comment, nothing between them?
    ///
    /// Read off the spans, which are byte offsets, so the lexer needs to know
    /// nothing about this. `a<b` is tight; `a < b`, `a\n<b` and `a /*c*/< b`
    /// are not.
    ///
    /// This is the whole of the **one-directional whitespace rule**
    /// (docs/language/type-argument-disambiguation.md): a `<` with space before it
    /// never opens a type-argument list. One-directional is the load-bearing
    /// word — a *tight* `<` is not thereby a bracket, it is merely still
    /// speculated as one, so `a<b` remains a comparison by falling back
    /// exactly as it always did. Spacing can only ever *narrow* the ambiguity,
    /// never decide a program's meaning against what it already meant.
    ///
    /// It buys the one thing speculation provably cannot: nested comparisons.
    /// In `Or<n < m, m <= n>` the inner ` < ` is spaced, so it cannot open a
    /// list, so it cannot steal the outer's `>` — and the outer parse, which
    /// used to die on exactly that theft, completes
    /// (issues/comparison-inside-type-arguments.md).
    fn tight(&self, idx: usize) -> bool {
        match (idx.checked_sub(1).and_then(|i| self.toks.get(i)), self.toks.get(idx)) {
            (Some(prev), Some(here)) => prev.span.end == here.span.start,
            // Nothing before it: a `<` cannot open type arguments anyway,
            // since there is no head for them to apply to.
            _ => false,
        }
    }

    /// The bit-packed flag set that, with a position and a site, keys
    /// [`Self::spec_failed`]. Every flag that can change what the expression
    /// grammar accepts has to be here, or the memo would answer a question it
    /// was not asked.
    fn spec_flags(&self, site: u8) -> u8 {
        site | (self.no_record_lit as u8)
            | ((self.no_eq as u8) << 1)
            | ((self.no_iff as u8) << 2)
            | ((self.motive_body as u8) << 3)
            | ((self.annotation_rel as u8) << 7)
    }

    /// Has this exact speculation already been tried here and failed?
    fn spec_seen_failing(&self, at: usize, site: u8) -> bool {
        self.spec_failed.contains(&(at, self.spec_flags(site)))
    }

    /// Record a failed speculation, rewind, and answer "not this reading".
    /// Typed to return `Option` so the two `try_tyargs` exits read as one line;
    /// [`Self::ty`]'s site calls [`Self::spec_note_failure`] directly, since it
    /// continues into the fallback rather than returning.
    fn spec_fail<T>(&mut self, save: usize, site: u8) -> Option<T> {
        self.spec_note_failure(save, site);
        None
    }

    fn spec_note_failure(&mut self, save: usize, site: u8) {
        let key = (save, self.spec_flags(site));
        self.spec_failed.insert(key);
        self.pos = save;
    }

    fn anonymous_constructor_expr(&mut self) -> R<Expr> {
        let open = self.expect(&TokKind::LAngle, "`⟨`")?;
        let (head_name, args) = if matches!(self.peek(), TokKind::Pipe) {
            self.bump();
            let arg = self.expr()?;
            (ANON_CTOR_RIGHT, vec![arg])
        } else if matches!(self.peek(), TokKind::RAngle) {
            (ANON_CTOR_ONLY, vec![])
        } else {
            let first = self.expr()?;
            if matches!(self.peek(), TokKind::Pipe) {
                self.bump();
                (ANON_CTOR_LEFT, vec![first])
            } else {
                let mut args = vec![first];
                while matches!(self.peek(), TokKind::Comma) {
                    self.bump();
                    if matches!(self.peek(), TokKind::RAngle) {
                        break;
                    }
                    args.push(self.expr()?);
                }
                (ANON_CTOR_ONLY, args)
            }
        };
        let close = self.expect(&TokKind::RAngle, "`⟩` to close the constructor")?;
        let span = open.join(close);
        let head = Expr { kind: ExprKind::Var(head_name.into()), span: open };
        Ok(Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        })
    }

    /// A primary expression: keyword forms (`match`/`refl`/`j`/`calc`), an
    /// `@`- or plain call, a variable, a numeral, or a parenthesised group.
    fn atom(&mut self) -> R<Expr> {
        let start = self.peek_span();
        // Expected-type-directed constructor notation. A comma tuple selects
        // the sole constructor; a bar against either edge selects a side of
        // a two-constructor sum. The synthetic call head cannot be written by
        // a user and lets every existing AST traversal treat the arguments as
        // ordinary subexpressions.
        if matches!(self.peek(), TokKind::LAngle) {
            return self.anonymous_constructor_expr();
        }
        // `⟦b⟧` reflects a Boolean into `Type`: exact surface sugar for
        // `Bool::IsTrue(b)`. The delimiters reopen the expression grammar just like
        // parentheses, so an enclosing comparison or record-literal context
        // cannot restrict the reflected expression.
        if matches!(self.peek(), TokKind::LSemantic) {
            let open = self.bump().span;
            let inner = self
                .with_eq(false, |p| p.with_record_lit(false, |p| p.expr()))?;
            let close = self.expect(&TokKind::RSemantic, "`⟧` to close Boolean reflection")?;
            let span = open.join(close);
            let head = Expr { kind: ExprKind::Var("Bool::IsTrue".to_string()), span: open };
            return Ok(Expr {
                kind: ExprKind::App {
                    head: Box::new(head),
                    args: vec![inner],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            });
        }
        // Squash is type syntax in expression position too, just like an
        // arrow type.  This matters in particular under `code { ... }`: the
        // quotation must retain the distinct `TmSquash` encoding rather than
        // resolving `Squash` as an ordinary term name.
        if matches!(self.peek(), TokKind::NormBar)
            || (self.at_kw("Squash") && matches!(self.nth(1), TokKind::Lt))
        {
            let ty = self.ty_atom()?;
            let span = ty.span;
            return Ok(Expr { kind: ExprKind::TyLit(Box::new(ty)), span });
        }
        // `Type<n>` where a term is expected. Before the operator loop sees
        // the `<`, which would otherwise read it as `lt`.
        if let Some((level, span)) = self.univ()? {
            return Ok(Expr { kind: ExprKind::Univ { level }, span });
        }
        if self.at_kw("match") {
            return self.match_expr();
        }
        if self.at_kw("if") {
            return self.if_expr();
        }
        // **Rule 1** (docs/language/let-and-blocks-design.md §5.2): a keyword-headed
        // form that is always introduced by a fixed token is recognized only
        // when that token follows, so the name is bought back everywhere else.
        // Exact, not heuristic: `calc_expr` and `j_expr` *require* the same
        // token one line later, so nothing that parses today parses
        // differently. This is the `code {` rule (below) and its pinned test,
        // applied to the two other forms that qualify.
        if self.at_kw("calc") && matches!(self.nth(1), TokKind::LBrace) {
            return self.calc_expr();
        }
        if self.at_kw("refl") {
            self.bump();
            return Ok(Expr { kind: ExprKind::Refl, span: start });
        }
        // `by t` runs the tactic `t` against the expected type. Rule 1: only
        // when a name follows, so a local called `by` (`by(a)`, `by + 1`)
        // still reads as itself.
        if self.at_kw("by") && matches!(self.nth(1), TokKind::Ident(_)) {
            self.bump();
            let tactic = self.postfix()?;
            let span = start.join(tactic.span);
            let head = Expr { kind: ExprKind::Var(BY_TACTIC.to_string()), span: start };
            return Ok(Expr {
                kind: ExprKind::App {
                    head: Box::new(head),
                    args: vec![tactic],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            });
        }
        if self.at_kw("j") && matches!(self.nth(1), TokKind::LParen) {
            return self.j_expr();
        }
        if self.at_kw("squash_ind") && matches!(self.nth(1), TokKind::LParen) {
            return self.squash_ind_expr();
        }
        if matches!(self.peek(), TokKind::Lambda) || self.at_kw("fun") {
            return self.lambda();
        }
        // `code { e }` — a quotation (docs/metaprogramming/in-language-map-design.md §3).
        // Before the general `Ident` case; the `{` lookahead is what keeps a
        // plain variable named `code` working everywhere else.
        //
        // "Everywhere else" includes the positions where the `{` is not the
        // payload's at all but the *enclosing form's* — a `match` scrutinee,
        // a motive, a block-preceding type — and that is exactly what
        // `no_record_lit` already marks, which is why the same flag decides
        // this (issues/match-scrutinee-named-code.md). Without it
        // `match code { … }` committed to a quotation and died inside the
        // first arm at ``expected `}` to close the quote``, since `match`'s
        // own guard had already, correctly, declined to read it as the
        // intensional form. The escape hatch is the one the flag documents:
        // a quotation that really is wanted there is parenthesised, and a
        // bracket lifts the restriction.
        if self.at_kw("code") && matches!(self.nth(1), TokKind::LBrace) && !self.no_record_lit {
            let start = self.bump().span; // `code`
            self.bump(); // `{`
            // Inside the braces nothing is waiting for a block (same reasoning
            // as `block`), and the payload is one expression — quotes have no
            // statements.
            let saved = std::mem::replace(&mut self.no_record_lit, false);
            let body = self.expr();
            self.no_record_lit = saved;
            let body = body?;
            // A block as the payload's top level is **declined**, not
            // supported: its `let`s would elaborate as aliases at
            // `Layer::Code`, which plausibly interacts with `scan_splices`'
            // letbox hoisting and with `box-synthesis-gap`'s meta-ANF
            // invariant in ways nobody has established. A wrong answer here is
            // a silently mis-hoisted splice, so it is filed rather than
            // guessed (docs/language/let-and-blocks-design.md §7.2).
            if matches!(body.kind, ExprKind::Block(_)) {
                return Err(ParseError {
                    msg: "a quote payload is one expression, not a block: `let` inside \
                          quotation is not in this slice \
                          (issues/let-inside-quotation.md)"
                        .into(),
                    span: body.span,
                });
            }
            let end = self.expect(&TokKind::RBrace, "`}` to close the quote")?;
            return Ok(Expr {
                kind: ExprKind::Quote(Box::new(body)),
                span: start.join(end),
            });
        }
        // `$x` / `${e}` — a splice (surface-v0 §4, verdict (c)).
        if matches!(self.peek(), TokKind::Dollar) {
            let start = self.bump().span;
            if matches!(self.peek(), TokKind::LBrace) {
                self.bump();
                let e = self.with_record_lit(false, |p| p.expr())?;
                let end = self.expect(&TokKind::RBrace, "`}` to close `${…}`")?;
                return Ok(Expr { kind: ExprKind::Splice(Box::new(e)), span: start.join(end) });
            }
            let (name, nsp) = self.ident("name after `$` (or `${expr}`)")?;
            let inner = Expr { kind: ExprKind::Var(name), span: nsp };
            return Ok(Expr { kind: ExprKind::Splice(Box::new(inner)), span: start.join(nsp) });
        }
        // `@f(args)` — a fully-explicit call (implicit params given
        // positionally). Stays an atom-level *named* form rather than a
        // prefix on any application: `@` suppresses implicit-argument
        // insertion, which is name-directed, so on a non-name there is
        // nothing to suppress (docs/language/surface-function-types.md §1.3).
        if matches!(self.peek(), TokKind::At) {
            let at = self.bump().span;
            let (name, nsp) = self.qual_ident("call head after `@`")?;
            // `@f<T, …>(…)` — the two knobs compose: `<…>` writes the type
            // arguments, `@` makes the *value* implicits positional
            // (issues/at-and-type-arguments.md). Not speculative here, unlike
            // `try_tyargs`: after `@` a name is always a callee, so `<` can
            // only open a type-argument list.
            let mut head = Expr { kind: ExprKind::Var(name), span: nsp };
            if matches!(self.peek(), TokKind::Lt) {
                self.bump();
                let mut targs = Vec::new();
                loop {
                    targs.push(self.ty()?);
                    if !matches!(self.peek(), TokKind::Comma) {
                        break;
                    }
                    self.bump();
                }
                let gt = self.expect(&TokKind::Gt, "`>` to close the type arguments")?;
                head = Expr {
                    kind: ExprKind::TyApp { head: Box::new(head), args: targs },
                    span: nsp.join(gt),
                };
            }
            self.expect(&TokKind::LParen, "`(` (`@` marks a call)")?;
            let (args, named, end) = self.call_args()?;
            return Ok(Expr {
                kind: ExprKind::App {
                    head: Box::new(head),
                    args,
                    named,
                    explicit: true,
                    goal_oriented: false,
                },
                span: at.join(end),
            });
        }
        // The first separator selects `[T; n]` (a type expression) or
        // `[a, b, c]` (an expected-type-directed collection literal). Parse
        // the head once and read it as a type only at `;`: no backtracking
        // or expected-universe retry can reinterpret a malformed literal.
        if matches!(self.peek(), TokKind::LBracket) {
            let open = self.bump().span;
            return self.with_record_lit(false, |p| {
                let mut elems = Vec::new();
                if !matches!(p.peek(), TokKind::RBracket) {
                    let first = p.expr()?;
                    if matches!(p.peek(), TokKind::Semi) {
                        p.bump();
                        let elem = expr_as_ty(&first);
                        let len = p.expr()?;
                        let close = p.expect(&TokKind::RBracket, "`]` (a vector type is `[T; n]`)")?;
                        let span = open.join(close);
                        let ty = Ty { kind: TyKind::Vec { elem: Box::new(elem), len: Box::new(len) }, span };
                        return Ok(Expr { kind: ExprKind::TyLit(Box::new(ty)), span });
                    }
                    elems.push(first);
                }
                while matches!(p.peek(), TokKind::Comma) {
                    p.bump();
                    if matches!(p.peek(), TokKind::RBracket) {
                        break;
                    }
                    // `[a, b, ..rest]`: a list that goes on as `rest`, the
                    // conses written out (`Cons(a, Cons(b, rest))`).
                    if p.at_list_rest() {
                        p.bump();
                        p.bump();
                        let rest = p.expr()?;
                        let close = p.expect(&TokKind::RBracket, "`]` after a list's `..rest`")?;
                        let span = open.join(close);
                        return Ok(elems.into_iter().rev().fold(rest, |tail, head| Expr {
                            kind: ExprKind::App {
                                head: Box::new(Expr { kind: ExprKind::Var("Cons".into()), span }),
                                args: vec![head, tail],
                                named: Vec::new(),
                                explicit: false,
                                goal_oriented: false,
                            },
                            span,
                        }));
                    }
                    elems.push(p.expr()?);
                }
                let close = p.expect(&TokKind::RBracket, "`]` (collection literal)")?;
                Ok(Expr { kind: ExprKind::CollectionLit(elems), span: open.join(close) })
            });
        }
        // `{ let x = e; … result }` — a block in expression position
        // (docs/language/let-and-blocks-design.md §4). **Prefix** `{` only: the record
        // literal is postfix on a name head (`postfix`), and a `{` where a
        // statement is expected is reached by `block()`/`match_expr` directly,
        // so this is a pure extension — a prefix `{` was "expected an
        // expression" in every production before it. No lookahead, no
        // backtracking, and independent of `no_record_lit`.
        if matches!(self.peek(), TokKind::LBrace) {
            let b = self.block()?;
            if let Some(on) = b.ons.first() {
                return Err(ParseError {
                    msg: "a block in expression position cannot discharge goals: an \
                          `on` belongs to the declaration's own block, because a goal's \
                          scope is the declaration (issues/nested-goal-discharge.md)"
                        .into(),
                    span: on.span,
                });
            }
            let span = b.span;
            return Ok(Expr { kind: ExprKind::Block(Box::new(b)), span });
        }
        match self.peek().clone() {
            TokKind::Hole(name) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Hole(name), span: sp })
            }
            TokKind::ArgSlot(index) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::ArgSlot(index), span: sp })
            }
            TokKind::Num(n) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Num(n), span: sp })
            }
            TokKind::SuffixedNum(value, suffix) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::SuffixedNum { value, suffix }, span: sp })
            }
            TokKind::Scaled(s) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Scaled(s), span: sp })
            }
            // One atom each, exactly as a numeral is one: the lexer has
            // already decided the payload, so there is no grammar here beyond
            // "a literal is an expression" (docs/library/string-char-design.md §3).
            TokKind::Char(c) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Char(c), span: sp })
            }
            TokKind::Str(s) => {
                let s = s.clone();
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Str(s), span: sp })
            }
            // `b"…"`, one token whose bytes the lexer has read
            // (docs/native/io-programs-design.md §5 D3).
            TokKind::ByteStr(bytes) => {
                let bytes = bytes.clone();
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::ByteStr(bytes), span: sp })
            }
            // `b'…'`, one byte.
            TokKind::ByteChar(byte) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::ByteChar(byte), span: sp })
            }
            TokKind::LParen => {
                let open = self.bump().span;
                // `(<=)`: an operator section, the bare symbol as a value
                // anywhere an expression stands (issues/parenthesized-operator-symbols.md).
                // It is the node `f(<=, x)` already gives a lone symbol between
                // delimiters, so it resolves by the same designation ladder:
                // `s.SortedPerm((<=), out)` at `BitVec(64)` is
                // `BitVec::unsigned_le`. An infix token cannot begin an
                // expression, so `(` symbol `)` has no other reading.
                if let Some(sym) = Self::op_symbol(self.peek())
                    && matches!(self.nth(1), TokKind::RParen)
                {
                    self.bump();
                    let close = self.bump().span;
                    let span = open.join(close);
                    return Ok(Expr { kind: ExprKind::OpSymbol { symbol: sym.to_string(), fixity: OpFixity::Infix }, span });
                }
                // Parenthesising is the escape hatch for a record literal in
                // scrutinee position **and for the comparison rung**, so both
                // restrictions must lift here. The `no_eq` half is what makes
                // `a = (b = c)` a parse (the `CHAIN` message's own advice) and
                // what makes an equality `let` annotation writable as
                // `let p: (a = b) = pf;`.
                let e = self
                    .with_eq(false, |p| p.with_record_lit(false, |p| p.expr()))?;
                // `(e: T)`: an ascription. A group `(x: A)` followed by an
                // arrow never gets here (`at_binder_group` took it).
                if matches!(self.peek(), TokKind::Colon) {
                    self.bump();
                    let ty = self.with_eq(false, |p| p.ty())?;
                    let close = self.expect(&TokKind::RParen, "`)` to close the ascription")?;
                    let span = open.join(close);
                    return Ok(Expr { kind: ExprKind::Ascribe { expr: Box::new(e), ty: Box::new(ty) }, span });
                }
                self.expect(&TokKind::RParen, "`)`")?;
                Ok(e)
            }
            // Application is postfix now, so a bare name is just a name;
            // `f(a)` is assembled by `postfix`.
            TokKind::Ident(name) => {
                let sp = self.bump().span;
                Ok(Expr { kind: ExprKind::Var(name), span: sp })
            }
            _ => self.err("expected an expression"),
        }
    }

    /// `λ (x: A) (y: B) => e`, or `fun` for the ASCII spelling. Multiple
    /// binders are sugar for nesting. The body is parsed at binding power 0,
    /// so it extends as far as it can and stops at `,` `)` `}` `;` — none of
    /// which are infix operators.
    fn lambda(&mut self) -> R<Expr> {
        let propagation_start = self.propagation_count;
        let start = self.bump().span; // `λ` or `fun`
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                TokKind::Ident(_) => {
                    let (name, sp) = self.binder_ident("lambda binder")?;
                    binders.push(LamBinder { name, ty: None, implicit: false, span: sp });
                }
                TokKind::LParen => {
                    let open = self.bump().span;
                    let (name, _) = self.binder_ident("lambda binder")?;
                    self.expect(&TokKind::Colon, "`:` (annotated lambda binder)")?;
                    let ty = self.ty()?;
                    let close = self.expect(&TokKind::RParen, "`)`")?;
                    binders.push(LamBinder {
                        name,
                        ty: Some(ty),
                        implicit: false,
                        span: open.join(close),
                    });
                }
                // `{x}` / `{x: A}` — an implicit lambda binder
                // (docs/language/implicit-binders-design.md §8). One binder per brace
                // group, mirroring the paren rule; the annotation is optional
                // exactly as for a bare binder (checking position supplies
                // the domain from the expected Π).
                TokKind::LBrace => {
                    let open = self.bump().span;
                    let (name, _) = self.binder_ident("lambda binder")?;
                    let ty = if matches!(self.peek(), TokKind::Colon) {
                        self.bump();
                        Some(self.ty()?)
                    } else {
                        None
                    };
                    let close =
                        self.expect(&TokKind::RBrace, "`}` (implicit lambda binder)")?;
                    binders.push(LamBinder {
                        name,
                        ty,
                        implicit: true,
                        span: open.join(close),
                    });
                }
                _ => break,
            }
        }
        if binders.is_empty() {
            return self.err("a lambda needs at least one binder");
        }
        self.expect(&TokKind::FatArrow, "`=>` (a lambda's body follows `=>`)")?;
        // A motive body is a *type* (docs/language/surface-universe.md §13), and may be
        // a function type; nothing else in expression position may be.
        let body = if std::mem::take(&mut self.motive_body) {
            let ty = self.ty()?;
            let span = ty.span;
            Expr { kind: ExprKind::TyLit(Box::new(ty)), span }
        } else {
            self.propagation_depth += 1;
            let body = self.expr();
            self.propagation_depth -= 1;
            body?
        };
        let span = start.join(body.span);
        let body = if self.propagation_count != propagation_start {
            for binder in &binders { if let Some(t) = &binder.ty { crate::try_lower::reject_type(t)?; } }
            crate::try_lower::expression(body, &mut self.next_hygienic)?
        } else { body };
        let body = crate::try_lower::binds_in_expression(body, &mut self.next_hygienic)?;
        Ok(Expr { kind: ExprKind::Lam { binders, body: Box::new(body) }, span })
    }

    /// Parse a comma-separated argument list up to and including the closing
    /// `)` (the opening `(` is already consumed). Returns the args and the
    /// span of the `)`.
    /// The argument list of every call — a plain one, an `@`-call, an
    /// `f<T>(…)` call, a method call and a constructor application all reach
    /// here. The `(` is already consumed.
    ///
    /// Positional arguments first, then **named** ones, `x := e`
    /// (docs/language/named-arguments-design.md §3.3). An argument is named iff the
    /// next two tokens are `IDENT` `:=`, which is two tokens of fixed
    /// lookahead with no speculation and no backtracking: `:=` occurs in no
    /// expression position anywhere in this grammar (§2.2), so `f(x := e)` was
    /// a parse error — at the `)` — before this existed, and nothing that
    /// parsed before parses differently now.
    fn call_args(&mut self) -> R<(Vec<Expr>, Vec<NamedArg>, Span)> {
        // Inside brackets a `{` cannot be a block, so the record-literal
        // restriction lifts here (and in every other bracketed context).
        self.with_record_lit(false, |p| {
            let mut args = Vec::new();
            let mut named: Vec<NamedArg> = Vec::new();
            while !matches!(p.peek(), TokKind::RParen) {
                if p.at_named_arg() {
                    let (name, name_span) = p.ident("a named argument's parameter name")?;
                    p.expect(&TokKind::ColonEq, "`:=` (a named argument)")?;
                    let expr = p.expr()?;
                    let span = name_span.join(expr.span);
                    named.push(NamedArg { name, name_span, expr, span });
                } else {
                    // Positional-then-named is the grammar, not an elaboration
                    // rule (§4.2): a positional argument means "the next
                    // parameter with no argument yet", and once free-order
                    // named arguments have claimed parameters that is a rule
                    // the writer has to compute rather than read. Refusing it
                    // here is what makes the interleaving unrepresentable in
                    // the AST, so no elaborator path has to define it.
                    if let Some(prev) = named.last() {
                        let msg = format!(
                            "a positional argument cannot follow a named one: `{}` names its \
                             parameter, so every argument after it must name its own. Write the \
                             positional arguments first, or give this one a name too",
                            prev.name
                        );
                        return Err(ParseError { msg, span: p.peek_span() });
                    }
                    // `A::CommMonoid(+)` — a designation reference, which is
                    // what an operator token in argument-initial position
                    // always is
                    // (docs/language/classes/operation-indexed-classes-design.md §7).
                    match p.op_symbol_arg() {
                        Some(e) => args.push(e),
                        None => args.push(p.expr()?),
                    }
                }
                if !matches!(p.peek(), TokKind::Comma) {
                    break;
                }
                p.bump();
            }
            let end = p.expect(&TokKind::RParen, "`)`")?;
            Ok((args, named, end))
        })
    }

    /// `x :=` at the head of an argument. Two tokens, no lookahead beyond
    /// them, and total — see [`Self::call_args`] for why that is enough.
    fn at_named_arg(&self) -> bool {
        matches!(self.peek(), TokKind::Ident(_)) && matches!(self.nth(1), TokKind::ColonEq)
    }

    /// `{ f: e, … }` after the record name, which the caller has consumed.
    /// Field order is free — it is normalized against the declaration in the
    /// elaborator (docs/language/surface-records.md §6), which is also where an unknown
    /// or missing field is reported, since only it knows the declaration.
    fn record_lit(&mut self, name: String, tyargs: Vec<Ty>, head: Span) -> R<Expr> {
        self.expect(&TokKind::LBrace, "`{` (record literal)")?;
        self.with_record_lit(false, |p| {
            let mut fields = Vec::new();
            while !matches!(p.peek(), TokKind::RBrace) {
                let (fname, fsp) = p.ident("record field name")?;
                p.expect(&TokKind::Colon, "`:` (record field)")?;
                let expr = p.expr()?;
                let span = fsp.join(expr.span);
                fields.push(RecordLitField { name: fname, expr, span });
                if !matches!(p.peek(), TokKind::Comma) {
                    break;
                }
                p.bump();
            }
            let end = p.expect(&TokKind::RBrace, "`}` (record literal)")?;
            Ok(Expr {
                kind: ExprKind::RecordLit { name, tyargs, fields },
                span: head.join(end),
            })
        })
    }

    /// `{ f = v, … }` after `base with`, which the caller has consumed. Which
    /// fields exist is the elaborator's to say, which knows the record.
    fn record_update(&mut self, base: Expr) -> R<Expr> {
        self.expect(&TokKind::LBrace, "`{` (record update)")?;
        self.with_record_lit(false, |p| {
            let mut fields = Vec::new();
            while !matches!(p.peek(), TokKind::RBrace) {
                let (fname, fsp) = p.ident("record field name")?;
                p.expect(&TokKind::Eq, "`=` (record update: `s with { f = v }`)")?;
                let expr = p.expr()?;
                let span = fsp.join(expr.span);
                fields.push(RecordLitField { name: fname, expr, span });
                if !matches!(p.peek(), TokKind::Comma) {
                    break;
                }
                p.bump();
            }
            let end = p.expect(&TokKind::RBrace, "`}` (record update)")?;
            if fields.is_empty() {
                return p.err("a record update replaces at least one field: `s with { f = v }`");
            }
            let span = base.span.join(end);
            Ok(Expr { kind: ExprKind::RecordUpdate { base: Box::new(base), fields }, span })
        })
    }

    fn match_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `match`
        // `match code e as T { … }` — intensional analysis. `code` is a
        // contextual keyword, so a scrutinee *named* `code` still parses:
        // only `match code` followed by a token that could **begin its
        // scrutinee** is the analysis form.
        //
        // Two tokens cannot, and both of them are how an ordinary `match` on a
        // variable named `code` continues (issues/match-scrutinee-named-code.md):
        // the arm block's `{`, and the motive's `as`. Declining on those costs
        // the analysis form nothing — there is no expression they could have
        // started — and it is the whole of what the variable needs here. A
        // follow token that *can* begin an expression (`match code (x) as T`)
        // still reads as the analysis form, deliberately: that one is a real
        // ambiguity rather than a gap, and it is the issue's residue.
        if self.at_kw("code")
            && !matches!(self.nth(1), TokKind::LBrace)
            && !matches!(self.nth(1), TokKind::Ident(s) if s == "as")
        {
            return self.match_code_expr(start);
        }
        // The scrutinee and the motive are both immediately followed by the
        // arm block, so a `{` here closes the `match` rather than opening a
        // record literal (docs/language/surface-records.md §6.1).
        let eqbind = self.eq_binder()?;
        let scrut = self.with_record_lit(true, |p| p.expr())?;
        let motive = if self.eat_kw("as") {
            // The retired spelling `as z -> T`, diagnosed rather than parsed:
            // `->` is the type arrow and nothing else now
            // (docs/language/surface-universe.md §13).
            if matches!(self.peek(), TokKind::Ident(_)) && matches!(self.nth(1), TokKind::Arrow) {
                return self.err(
                    "a motive is a lambda: write `as \u{3bb} z => T` (or `as fun z => T`) \
                     rather than `as z -> T`",
                );
            }
            Some(Box::new(self.with_motive(|p| p.with_record_lit(true, |p| p.expr()))?))
        } else {
            None
        };
        self.expect(&TokKind::LBrace, "`{`")?;
        let arms = self.match_arms()?;
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        Ok(Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(scrut),
                eqbind,
                motive,
                arms,
                test: None,
            },
            span: start.join(end),
        })
    }

    /// `if P { yes } else { no }` and `if h : P { yes } else { no }`.
    ///
    /// Both branch on the decision's bit (issues/native-frontend-decided-matches.md):
    ///
    /// ```text
    /// match decide_bit<P>() { True => yes, False => no }
    /// ```
    ///
    /// so a decision built from a comparison is a match on that comparison's
    /// bit, the way code branches on it. With a binder the match is convoyed,
    /// and each branch binds the evidence from the bit's equation through the
    /// instance's `reflects` (issues/runtime-fn-if-word-proposition.md):
    ///
    /// ```text
    /// match e: decide_bit<P>() {
    ///     True => { let h = decide_true<P>(e); yes },
    ///     False => { let h = decide_false<P>(e); no },
    /// }
    /// ```
    ///
    /// (a branch that never names `h` binds none, unless an enclosing
    /// block's `on` discharge names it: its goal is raised in the branch),
    /// so `h: P` and `h: ¬P` as
    /// before, and the `runtime fn` reflector, the
    /// measure obligations and `split_all` read the bit the code tests, never
    /// the `P ∨ ¬P` decision.
    ///
    /// `MatchForm::If` is diagnostic provenance only. Everything that types or
    /// computes sees the same ordinary match as the explicit spelling.
    fn if_expr(&mut self) -> R<Expr> {
        let start = self.bump().span; // `if`
        if self.eat_kw("let") {
            return self.if_let_expr(start);
        }
        let evidence = self.eq_binder()?;
        // The following `{` is the true branch, never a record literal on the
        // condition's final name.
        let condition = self.with_record_lit(true, |p| p.expr())?;
        // Reuse the language's one expression-to-type bridge. It preserves
        // built-in and declared proposition names (`True`, `P`, `Mystery`)
        // while relational expressions become decoded type expressions.
        let proposition = expr_as_ty(&condition);

        let elseless = std::mem::take(&mut self.elseless_if);
        let yes_from = self.pos;
        let yes = self.if_branch("the `if` branch")?;
        let yes_names = self.names_from(yes_from, evidence.as_deref());
        let no_from = self.pos;
        let no = if self.eat_kw("else") {
            if self.at_kw("if") {
                // `else if c { … }`: the nested `if` is the `else` branch, and
                // a statement's chain may end without an `else` too.
                self.elseless_if = elseless;
                let nested = self.if_expr();
                self.elseless_if = false;
                let nested = nested?;
                let span = nested.span;
                // Braced, as every branch is: a statement chain's tail is a
                // statement body holding the nested statement form.
                let block = if is_statement_form(&nested) {
                    let name = self.hygienic("stmt");
                    Block {
                        stmts: vec![Stmt::Let {
                            name,
                            ty: None,
                            expr: crate::imperative::marked(crate::imperative::STMT, nested, span),
                            span,
                            opaque: false,
                        }],
                        result: Box::new(crate::imperative::unit(Span { start: span.end, end: span.end })),
                        ons: Vec::new(),
                        span,
                    }
                } else {
                    Block { stmts: Vec::new(), result: Box::new(nested), ons: Vec::new(), span }
                };
                Expr { kind: ExprKind::Block(Box::new(block)), span }
            } else {
                self.if_branch("the `else` branch")?
            }
        } else if elseless && is_statement_body(&yes) {
            // A statement `if` with no `else` assigns nothing when `c` fails.
            let span = Span { start: yes.span.end, end: yes.span.end };
            Expr {
                kind: ExprKind::Block(Box::new(Block { stmts: Vec::new(), result: Box::new(crate::imperative::unit(span)), ons: Vec::new(), span })),
                span,
            }
        } else {
            return self.err("an `if` needs an `else { … }` branch");
        };

        // An enclosing block's `on ?decN := …` proves a goal raised inside
        // a branch, so a name it uses is bound in both.
        let in_ons = self.names_in_enclosing_ons(evidence.as_deref());
        let yes_names = yes_names || in_ons;
        let no_names = self.names_from(no_from, evidence.as_deref()) || in_ons;
        let ev_span = condition.span;
        // The condition's own span on every lowered call's head: it is what
        // marks the call as a lowered condition for the elaborator's
        // readings (`surface::lowered_condition`).
        let call = |head: &str, proposition: &Ty, args: Vec<Expr>| Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::TyApp {
                        head: Box::new(Expr { kind: ExprKind::Var(head.into()), span: ev_span }),
                        args: vec![proposition.clone()],
                    },
                    span: ev_span,
                }),
                args,
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span: ev_span,
        };
        let scrut = call("decide_bit", &proposition, vec![]);
        // With evidence the match is still on the bit, convoyed, and each
        // branch binds `h` from the instance's `reflects` at that equation:
        // `decide_true<P>(e): P`, `decide_false<P>(e): ¬P`.
        //
        // The equation's name is one a tactic's reading of the context
        // lists (`omega_cert::local_fact_entries` passes over `#` names)
        // where a branch does not bind `h` itself: `h` was written, so
        // the test is a fact of that branch, and a proof found there
        // (`omega`, `bv_omega`, a parameter's default) reads it as the
        // bit's equation, as it reads a `match h:`'s. The term is the same
        // either way.
        let eqbind = evidence.as_ref().map(|_| {
            let hidden = self.hygienic("if_bit");
            if yes_names && no_names { hidden } else { format!("__if_bit{}", &hidden["#if_bit".len()..]) }
        });
        // A branch that never names the evidence binds none: the function
        // is then a plain convoy, which a proof that cases the same test can
        // abstract (an evidence term is typed by the instance's bit, not by
        // the scrutinee the motive abstracts).
        let branch = |body: Expr, side: &str, names: bool| match (&evidence, &eqbind) {
            (Some(name), Some(e)) if names => {
                let bit = Expr { kind: ExprKind::Var(e.clone()), span: ev_span };
                let span = body.span;
                let evidence = Stmt::Let { name: name.clone(), ty: None, expr: call(side, &proposition, vec![bit]), span: ev_span, opaque: false };
                Expr { kind: ExprKind::Block(Box::new(Block { stmts: vec![evidence], result: Box::new(body), ons: Vec::new(), span })), span }
            }
            _ => body,
        };
        let (yes_span, no_span) = (yes.span, no.span);
        let arms = vec![
            Arm {
                ctor: "True".into(),
                default: false,
                binders: vec![],
                span: yes_span,
                body: branch(yes, "decide_true", yes_names),
            },
            Arm {
                ctor: "False".into(),
                default: false,
                binders: vec![],
                span: no_span,
                body: branch(no, "decide_false", no_names),
            },
        ];
        let span = start.join(no_span);
        Ok(Expr {
            kind: ExprKind::Match {
                form: MatchForm::If,
                generated: false,
                scrut: Box::new(scrut),
                eqbind,
                motive: None,
                arms,
                test: evidence,
            },
            span,
        })
    }

    /// `if let P = e { yes } else { no }`, with optional success evidence:
    /// `if let h : P = e { yes } else { no }`.
    ///
    /// The `=` is a pattern/scrutinee separator, not a displayed type. In the
    /// success branch `h` follows the equation-bearing-match convention and
    /// has type `e = P`. The convoy binder itself has an unspellable internal
    /// name; a synthetic success-local `let` exposes it as `h`. Consequently
    /// the default arm receives no source-visible negative or equation
    /// evidence, while both forms still lower to exactly one ordinary match.
    fn if_let_expr(&mut self, start: Span) -> R<Expr> {
        const EQUATION: &str = "#if_let_eq";

        let evidence = self.eq_binder()?;
        let (ctor, cspan) = self.qual_ident("constructor name in an `if let` pattern")?;
        if ctor == "_" {
            return Err(ParseError {
                msg: "an `if let` pattern must be refutable; `_` always matches".into(),
                span: cspan,
            });
        }
        let binders = self.pat_args(&ctor, cspan)?;
        self.expect_eq("`if let` pattern")?;
        // The following `{` starts the success block, never a record literal
        // attached to the scrutinee's final name.
        let scrut = self.with_record_lit(true, |p| p.expr())?;

        let mut yes = self.if_branch("the `if let` branch")?;
        if !self.eat_kw("else") {
            return self.err("an `if let` needs an `else { … }` branch");
        }
        let no = self.if_branch("the `else` branch")?;

        if let Some(name) = &evidence {
            let ExprKind::Block(block) = &mut yes.kind else {
                unreachable!("if_branch always constructs a block")
            };
            block.stmts.insert(
                0,
                Stmt::Let {
                    name: name.clone(),
                    ty: None,
                    expr: Expr {
                        kind: ExprKind::Var(EQUATION.into()),
                        span: cspan,
                    },
                    span: cspan,
                    opaque: false,
                },
            );
        }

        let arms = vec![
            Arm {
                ctor,
                default: false,
                binders,
                span: cspan.join(yes.span),
                body: yes,
            },
            Arm {
                ctor: "_".into(),
                default: true,
                binders: vec![],
                span: no.span,
                body: no,
            },
        ];
        let span = start.join(arms[1].body.span);
        Ok(Expr {
            kind: ExprKind::Match {
                form: MatchForm::IfLet,
                generated: false,
                scrut: Box::new(scrut),
                eqbind: evidence.map(|_| EQUATION.into()),
                motive: None,
                arms,
                test: None,
            },
            span,
        })
    }

    /// One braced `if` branch as an ordinary block expression. Branch-local
    /// `let`s are therefore the same aliases as everywhere else; nested goal
    /// discharges retain the existing expression-block refusal.
    fn if_branch(&mut self, what: &str) -> R<Expr> {
        if !matches!(self.peek(), TokKind::LBrace) {
            return self.err(format!("{what} must be a braced block"));
        }
        let b = self.block()?;
        if let Some(on) = b.ons.first() {
            return Err(ParseError {
                msg: "an `if` branch cannot discharge declaration-scoped goals".into(),
                span: on.span,
            });
        }
        let span = b.span;
        Ok(Expr { kind: ExprKind::Block(Box::new(b)), span })
    }

    /// Arms are `C(x, …) => body`, one per constructor. Which constructors
    /// exist — and so whether the arms are complete, duplicated, or of the
    /// wrong arity — is the elaborator's business: it knows the scrutinee's
    /// type, and the grammar does not. Shared with `match code`, whose arm
    /// names are branch names and whose binders are recursive results, because
    /// the *grammar* of an arm is the same either way.
    fn match_arms(&mut self) -> R<Vec<Arm>> {
        let mut arms: Vec<Arm> = Vec::new();
        while !matches!(self.peek(), TokKind::RBrace) {
            let (ctor, cspan, binders) = if matches!(self.peek(), TokKind::LAngle) {
                self.anonymous_constructor_pat()?
            } else if matches!(self.peek(), TokKind::LBracket) {
                match self.list_pat()? {
                    Pat::Ctor { name, args, span } => (name, span, args),
                    Pat::Var { name, span } => (name, span, Vec::new()),
                    Pat::Named { span, .. } => return Err(ParseError { msg: "a list pattern is not a field".into(), span }),
                }
            } else {
                let (ctor, cspan) = self.qual_ident("constructor name in a `match` arm")?;
                let binders = self.pat_args(&ctor, cspan)?;
                (ctor, cspan, binders)
            };
            // `_ =>` is the default arm. It parses here rather than needing a
            // token of its own because `_` already lexes as an identifier
            // (`on _: P` reads it that way), so the form steals nothing
            // (docs/language/matching/nested-match-patterns-design.md §2).
            let default = ctor == "_";
            self.expect(&TokKind::FatArrow, "`=>`")?;
            let body = self.expr()?;
            let span = cspan.join(body.span);
            arms.push(Arm { ctor, default, binders, body, span });
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        Ok(arms)
    }

    /// Pattern counterpart of [`Self::anonymous_constructor_expr`]. Keeping
    /// the same three unspellable constructor sentinels means the elaborator
    /// can resolve both introduction and elimination from the type in hand.
    fn anonymous_constructor_pat(&mut self) -> R<(String, Span, Vec<Pat>)> {
        let open = self.expect(&TokKind::LAngle, "`⟨`")?;
        let (name, args) = if matches!(self.peek(), TokKind::Pipe) {
            self.bump();
            (ANON_CTOR_RIGHT, vec![self.pat_arg()?])
        } else if matches!(self.peek(), TokKind::RAngle) {
            (ANON_CTOR_ONLY, vec![])
        } else {
            let first = self.pat_arg()?;
            if matches!(self.peek(), TokKind::Pipe) {
                self.bump();
                (ANON_CTOR_LEFT, vec![first])
            } else {
                let mut args = vec![first];
                while matches!(self.peek(), TokKind::Comma) {
                    self.bump();
                    if matches!(self.peek(), TokKind::RAngle) {
                        break;
                    }
                    args.push(self.pat_arg()?);
                }
                (ANON_CTOR_ONLY, args)
            }
        };
        let close = self.expect(&TokKind::RAngle, "`⟩` to close the constructor pattern")?;
        Ok((name.into(), open.join(close), args))
    }

    /// `match code e as T { branch(x, …) => …, _ => … }`
    /// (docs/archive/certgen-transcriber-in-language-design.md §3). `start` is the
    /// `match` keyword's span; the `code` keyword is still unconsumed.
    ///
    /// The motive is a **type**, not a lambda: a `match code` motive is
    /// constant by design, and spelling it as a type is what says so.
    fn match_code_expr(&mut self, start: Span) -> R<Expr> {
        self.bump(); // `code`
        let scrut = self.with_record_lit(true, |p| p.expr())?;
        if !self.eat_kw("as") {
            return self.err(
                "a `match code` needs its result type: write `match code e as T { … }` \
                 (the motive is constant — the arms all have the same type)",
            );
        }
        let motive = self.with_record_lit(true, |p| p.ty())?;
        self.expect(&TokKind::LBrace, "`{`")?;
        let arms = self.match_arms()?;
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        Ok(Expr {
            kind: ExprKind::MatchCode {
                scrut: Box::new(scrut),
                motive: Box::new(motive),
                arms,
            },
            span: start.join(end),
        })
    }

    /// The parenthesized argument list of a pattern — positional fields or
    /// `field := pattern` (docs/language/matching/named-patterns-by-field-design.md §3).
    /// Absent parentheses mean no fields, which is the nullary-constructor
    /// spelling `Zero => …`.
    ///
    /// `head`/`hspan` are the pattern's own head, needed only for the one
    /// error this can raise: a default arm binds nothing, so `_( … )` is
    /// refused here rather than surviving to the elaborator as a shape no
    /// expansion could use.
    fn pat_args(&mut self, head: &str, hspan: Span) -> R<Vec<Pat>> {
        let mut args = Vec::new();
        if !matches!(self.peek(), TokKind::LParen) {
            return Ok(args);
        }
        if head == "_" {
            return Err(ParseError {
                msg: "`_` binds no fields: it is the default arm, standing for every \
                      constructor that has no arm of its own"
                    .to_string(),
                span: hspan,
            });
        }
        self.bump();
        while !matches!(self.peek(), TokKind::RParen) {
            args.push(self.pat_arg()?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        self.expect(&TokKind::RParen, "`)` (pattern binders)")?;
        Ok(args)
    }

    /// One field position: a binder, or a **deep pattern**
    /// (docs/language/matching/nested-match-patterns-design.md §3.1).
    ///
    /// A bare identifier is read as [`Pat::Var`] unconditionally — whether it
    /// is really a nullary constructor is a question about the constructor
    /// table, which the parser does not have, and the elaborator reclassifies
    /// (§3.5). So the *only* thing that distinguishes a deep pattern here is a
    /// following `(`.
    fn pat(&mut self) -> R<Pat> {
        if matches!(self.peek(), TokKind::LBracket) {
            return self.list_pat();
        }
        if matches!(self.peek(), TokKind::LAngle) {
            let (name, span, args) = self.anonymous_constructor_pat()?;
            return Ok(Pat::Ctor { name, args, span });
        }
        let (name, span) = self.binder_ident("pattern binder")?;
        if !matches!(self.peek(), TokKind::LParen) {
            return Ok(Pat::Var { name, span });
        }
        if name == "_" {
            return Err(ParseError {
                msg: "`_` is a binder, so it takes no pattern arguments".to_string(),
                span,
            });
        }
        self.bump();
        let mut args = Vec::new();
        while !matches!(self.peek(), TokKind::RParen) {
            args.push(self.pat_arg()?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let end = self.expect(&TokKind::RParen, "`)` (pattern arguments)")?;
        Ok(Pat::Ctor { name, args, span: span.join(end) })
    }

    /// `..` inside a list's brackets: the rest of the list follows.
    fn at_list_rest(&self) -> bool {
        matches!(self.peek(), TokKind::Dot) && matches!(self.nth(1), TokKind::Dot)
    }

    /// A list pattern: `[]`, `[p, q]`, or `[p, q, ..rest]`, the conses
    /// written out (`Cons(p, Cons(q, rest))`; `Nil` where no rest is
    /// named), so the pattern matrix sees nothing new.
    fn list_pat(&mut self) -> R<Pat> {
        let open = self.expect(&TokKind::LBracket, "`[`")?;
        let mut elems = Vec::new();
        let mut rest = None;
        while !matches!(self.peek(), TokKind::RBracket) {
            if self.at_list_rest() {
                if elems.is_empty() {
                    return self.err("a list pattern names an element before `..rest`: `[x, ..rest]`; a whole list is a plain binder");
                }
                self.bump();
                self.bump();
                rest = Some(self.pat()?);
                break;
            }
            elems.push(self.pat()?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump();
        }
        let close = self.expect(&TokKind::RBracket, "`]` to close the list pattern")?;
        let span = open.join(close);
        let tail = rest.unwrap_or(Pat::Var { name: "Nil".into(), span });
        Ok(elems.into_iter().rev().fold(tail, |tail, head| Pat::Ctor { name: "Cons".into(), args: vec![head, tail], span }))
    }

    /// A constructor field pattern, positional or `field := pattern`.
    fn pat_arg(&mut self) -> R<Pat> {
        if self.at_named_arg() {
            let (field, fsp) = self.ident("a named pattern's field name")?;
            self.bump(); // `:=`
            let pat = self.pat()?;
            let span = fsp.join(pat.span());
            return Ok(Pat::Named { field, pat: Box::new(pat), span });
        }
        self.pat()
    }

    /// The optional `h :` prefix of a `match` scrutinee or a `split`
    /// (docs/language/matching/match-equation-split-design.md §3.1). Recognized on two tokens,
    /// which is exact: `:` never *continues* an expression in this grammar
    /// (every `Colon` is a binder annotation, a record-literal field after
    /// `{`, or a declaration header), and `::` is its own token, so
    /// `match A::b { … }` is untouched. Same shape as `code {`'s rule-1
    /// lookahead (docs/language/let-and-blocks-design.md §5.2).
    fn eq_binder(&mut self) -> R<Option<String>> {
        if matches!(self.peek(), TokKind::Ident(_)) && matches!(self.nth(1), TokKind::Colon) {
            let (name, _) = self.binder_ident("the equation binder")?;
            self.bump(); // `:`
            return Ok(Some(name));
        }
        Ok(None)
    }

    /// The residue rule 1 leaves standing (docs/language/let-and-blocks-design.md §5.3):
    /// after the lookahead, a binder named `j` is an ordinary name at every use
    /// *except* `j(x)` — a local of function type applied to arguments, which
    /// still enters this form and fails its arity check. Loud, and inside a
    /// form the error can name, so the arity messages say so; it dissolves
    /// entirely under `issues/special-forms-as-declarations.md`.
    const J_ARITY: &str = "`j` takes exactly three arguments — \
                           `j(proof, \u{3bb} y q => T, case)`. If `j` is a local name \
                           here, it cannot be *applied*: rename it, since a call \
                           `j(…)` is the eliminator (issues/j-binder-parse-trap.md)";

    fn j_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `j`
        // Unreachable in practice: rule 1's lookahead is what got us here.
        self.expect(&TokKind::LParen, "`(`")?;
        let proof = self.expr()?;
        self.expect(&TokKind::Comma, Self::J_ARITY)?;
        // The retired spelling `(y, q) -> T`.
        if matches!(self.peek(), TokKind::LParen)
            && matches!(self.nth(1), TokKind::Ident(_))
            && matches!(self.nth(2), TokKind::Comma)
        {
            return self.err(
                "a motive is a lambda: write `j(p, \u{3bb} y q => T, case)` rather than \
                 `j(p, (y, q) -> T, case)`",
            );
        }
        let motive = self.with_motive(|p| p.expr())?;
        self.expect(&TokKind::Comma, Self::J_ARITY)?;
        let case = self.expr()?;
        let end = self.expect(&TokKind::RParen, Self::J_ARITY)?;
        Ok(Expr {
            kind: ExprKind::J {
                proof: Box::new(proof),
                motive: Box::new(motive),
                case: Box::new(case),
            },
            span: start.join(end),
        })
    }

    fn squash_ind_expr(&mut self) -> R<Expr> {
        let start = self.bump().span;
        self.expect(&TokKind::LParen, "`(`")?;
        let scrut = self.expr()?;
        self.expect(&TokKind::Comma, "`,` after the squash scrutinee")?;
        let motive = self.with_motive(|p| p.expr())?;
        self.expect(&TokKind::Comma, "`,` after the squash motive")?;
        let case = self.expr()?;
        let end = self.expect(&TokKind::RParen, "`)` to close `squash_ind`")?;
        Ok(Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::Var("squash_ind".into()),
                    span: start,
                }),
                args: vec![scrut, motive, case],
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span: start.join(end),
        })
    }

    /// One calc step's relation token.
    fn calc_relation(&mut self) -> R<CalcRel> {
        let rel = match self.peek() {
            TokKind::Approx => CalcRel::Same,
            TokKind::LtEq => CalcRel::Le,
            TokKind::Lt => CalcRel::Lt,
            TokKind::EqEq => {
                self.expect_eq("calc step")?;
                unreachable!("`==` is refused by expect_eq")
            }
            TokKind::Eq => CalcRel::Eq,
            _ => {
                return self.err("a calc step relation: `=`, `≈`, `<=` or `<`".to_string());
            }
        };
        self.bump();
        Ok(rel)
    }

    /// `calc { e0 = e1 := p1 (, = e_i := p_i)* ,? }` — an equational chain
    /// (surface-v1 §1). Desugars to a right-nested `@trans` over the step
    /// proofs, carrying the step terms as the *explicit* endpoints so that
    /// `refl` steps still receive a checking type. Proves `e0 = e_last`;
    /// a single identity step is just its proof.
    ///
    /// A step may instead be written with `≈`, `<=` or `<`
    /// (issues/calc-over-order-relations.md). Such a chain is relational: it
    /// folds through the ordinary `relation_props` helpers with every
    /// endpoint passed explicitly, so each is checked, even in a single
    /// step. Adjacent steps compose by their pair: the same relation through
    /// `Transitive` (`relation_step`), an `=` beside anything by transport
    /// (`relation_eq_l`/`_r`, no class), and two different relations through
    /// a `Trans` instance (`relation_trans`) whose result is the stronger of
    /// the two in `≈` < `<=` < `<`. The parser names that result, so
    /// resolution only looks the pair up; a pair the carrier does not
    /// register is a missing instance, reported at the elaborator.
    fn calc_expr(&mut self) -> R<Expr> {
        let start = self.peek_span();
        self.bump(); // `calc`
        self.expect(&TokKind::LBrace, "`{`")?;
        // The chain: terms[i] are the endpoints, proofs[i] : terms[i] rels[i] terms[i+1].
        // The first step carries both endpoints (`e0 = e1 := p1`); later steps
        // reuse the previous right endpoint (`= e_{i+1} := p_{i+1}`).
        // Endpoints are read with the comparison rung suppressed: here `=`,
        // `≈`, `<=` and `<` are step separators, not the comparison types
        // (docs/language/surface-universe.md §13).
        let mut terms = vec![self.with_eq(true, |p| p.expr())?];
        let mut proofs = Vec::new();
        let mut rels = vec![self.calc_relation()?];
        loop {
            terms.push(self.with_eq(true, |p| p.expr())?);
            self.expect(&TokKind::ColonEq, "`:=` (calc step proof)")?;
            proofs.push(self.expr()?);
            if !matches!(self.peek(), TokKind::Comma) {
                break;
            }
            self.bump(); // `,`
            if matches!(self.peek(), TokKind::RBrace) {
                break; // trailing comma
            }
            rels.push(self.calc_relation()?);
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?;
        let span = start.join(end);
        // Fold right: acc proves terms[i+1] acc_rel e_last; prepend step i.
        let m = proofs.len();
        if rels.iter().any(|r| *r != CalcRel::Eq) {
            let relation = |r: CalcRel| Expr {
                kind: ExprKind::OpSymbol {
                    symbol: r.symbol().to_string(),
                    fixity: OpFixity::Infix,
                },
                span,
            };
            let call = |name: &str, args: Vec<Expr>| Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr {
                        kind: ExprKind::Var(name.into()),
                        span,
                    }),
                    args,
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            };
            let last = &terms[m];
            let mut acc_rel = rels[m - 1];
            let mut acc = if acc_rel == CalcRel::Eq {
                proofs[m - 1].clone()
            } else {
                call(
                    "relation_props::relation_exact",
                    vec![
                        relation(acc_rel),
                        terms[m - 1].clone(),
                        last.clone(),
                        proofs[m - 1].clone(),
                    ],
                )
            };
            for i in (0..m - 1).rev() {
                let (a, b, c) = (terms[i].clone(), terms[i + 1].clone(), last.clone());
                let step = rels[i];
                let p = proofs[i].clone();
                acc = match (step, acc_rel) {
                    (CalcRel::Eq, CalcRel::Eq) => {
                        trans_call(vec![p, acc], vec![("a", a), ("b", b), ("c", c)], span)
                    }
                    (CalcRel::Eq, r) => call(
                        "relation_props::relation_eq_l",
                        vec![relation(r), a, b, c, p, acc],
                    ),
                    (r, CalcRel::Eq) => call(
                        "relation_props::relation_eq_r",
                        vec![relation(r), a, b, c, p, acc],
                    ),
                    (r, s) if r == s => call(
                        "relation_props::relation_step",
                        vec![relation(r), a, b, c, p, acc],
                    ),
                    (r, s) => call(
                        "relation_props::relation_trans",
                        vec![relation(r), relation(s), relation(r.max(s)), a, b, c, p, acc],
                    ),
                };
                acc_rel = acc_rel.max(step);
            }
            return Ok(acc);
        }
        let last = &terms[m];
        let mut acc = proofs[m - 1].clone();
        for i in (0..m - 1).rev() {
            // The endpoints are pinned **by name**, not by a fully explicit
            // `@trans` (docs/language/named-arguments-design.md; the issue calls this
            // desugaring out as having been fragile twice). `@` forced every
            // value implicit positionally, so the emitted call depended on how
            // many implicits `trans` has and in what order — a property of a
            // *library* declaration that a *parser* desugaring should not
            // encode. Naming them depends only on what they are called, which
            // `ParamMeta` already treats as API.
            acc = trans_call(
                vec![proofs[i].clone(), acc],
                vec![
                    ("a", terms[i].clone()),
                    ("b", terms[i + 1].clone()),
                    ("c", last.clone()),
                ],
                span,
            );
        }
        acc.span = span;
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn written_paths_are_first_segments_outside_comments_and_strings() {
        let src = "fn f(x: bitvec::BitVec(8)) -> Nat { rat::Rat::ofInt(x.y::z) + Nat::succ(0) }\n\
                   // fs::read\nfn g() -> Str { \"io::write\" }\nfn h() -> Nat { rat::one }";
        assert_eq!(written_paths(src), ["bitvec", "rat"]);
    }

    /// The file's single `fn`/`theorem` declaration.
    fn only_decl(f: &File) -> &Decl {
        match &f.items[0] {
            Item::Decl(d) => d,
            other => panic!("expected a declaration, got {other:?}"),
        }
    }

    /// What [`leading_imports`] reads of a source, as text.
    fn opens_with(src: &str) -> Vec<String> {
        leading_imports(src)
            .iter()
            .map(|i| format!("{}{}::{{{}}}@{}..{}", if i.reexport { "export " } else { "" }, i.module,
                i.listed.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(","), i.span.start, i.span.end))
            .collect()
    }

    /// The imports of a source that parses, as `opens_with` spells them.
    fn parsed_imports(src: &str) -> Vec<String> {
        parse_file(src)
            .unwrap_or_else(|e| panic!("{src}: {}", e.msg))
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Import(i) => Some(format!("{}{}::{{{}}}@{}..{}", if i.reexport { "export " } else { "" }, i.module,
                    i.listed.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(","), i.span.start, i.span.end)),
                _ => None,
            })
            .collect()
    }

    // The loader and the session read a module's imports with
    // `leading_imports`, and the elaborator reads them from the parsed file:
    // the two readings are the same imports, at the same spans, wherever the
    // file parses.
    #[test]
    fn the_leading_imports_are_the_parsed_files_imports() {
        for src in [
            "",
            "fn f() -> Nat { 0 }",
            "import nat;",
            "import nat; import list::{map, fold};\nfn f() -> Nat { 0 }",
            "// a header\nimport nat; // why\n// and\nimport option::{\n  Option, // the type; with a `;` in the comment\n  map,\n};\nexport list::{list::Nil};\ntheorem t(a: Nat): a = a { refl }",
            "import a;\nfn import_like(import_x: Nat) -> Nat { import_x }",
            "import a;\nfn f(s: String) -> String { \"import b; export c::{d};\" }",
            "import a;\nsection<A> { fn f(x: A) -> A { x } }",
        ] {
            assert_eq!(opens_with(src), parsed_imports(src), "{src}");
        }
        assert_eq!(opens_with("import nat; import list::{map};").len(), 2);
    }

    // Nothing past the imports is read: a source whose bodies do not lex or
    // parse still opens with its imports, and the full parse reports the rest.
    #[test]
    fn the_leading_imports_do_not_read_the_bodies() {
        for body in ["fn f( -> Nat { 0 }", "fn f() -> Nat { \"unterminated }", "fn f() -> Nat { 0 }\nimport late;", "§"] {
            let src = format!("import a;\nimport b::{{c}};\n{body}");
            assert!(parse_file(&src).is_err(), "{src}: the control is a source that does not parse");
            assert_eq!(opens_with(&src), ["a::{}@0..9", "b::{c}@10..24"], "{src}");
        }
    }

    // An import that does not parse ends the reading where it stands, and a
    // name that only starts like the keyword is not one.
    #[test]
    fn the_leading_imports_end_at_what_is_not_an_import() {
        assert_eq!(opens_with("import a; import b c; import d;"), ["a::{}@0..9"]);
        assert_eq!(opens_with("import a; import b::*; import d;"), ["a::{}@0..9"]);
        assert_eq!(opens_with("import a; import::gen fn f() -> Nat { 0 } import d;"), ["a::{}@0..9"]);
        assert_eq!(opens_with("imports a; import b;"), [] as [&str; 0]);
        assert_eq!(opens_with("import a"), [] as [&str; 0]);
        assert_eq!(opens_with("import a; import §; import d;"), ["a::{}@0..9"]);
    }

    #[test]
    fn implicit_and_explicit_params() {
        let f = parse_file("theorem t({a: Nat}, b: Nat, p: a = b): b = a { refl }").unwrap();
        let ps = &only_decl(&f).params;
        assert_eq!(ps.len(), 3);
        assert!(ps[0].implicit, "`{{a}}` is implicit");
        assert!(!ps[1].implicit, "`b` is explicit");
        assert!(!ps[2].implicit, "`p` is explicit");
    }

    // Successors of the two implicit-binder diagnostics (retired
    // 2026-08-06): `{x: A} -> B` and `λ {x: A} => e` are parses now
    // (docs/language/implicit-binders-design.md §8), with the mark on the node.
    #[test]
    fn implicit_function_type_binders_parse() {
        let f = parse_file("fn f(g: {n: Nat} -> Nat -> Nat) -> Nat { 0 }").unwrap();
        let TyKind::Fn { binder, implicit, cod, .. } = &only_decl(&f).params[0].ty.kind
        else {
            panic!("expected a function type")
        };
        assert_eq!(binder.as_deref(), Some("n"));
        assert!(*implicit, "`{{n: Nat}}` is implicit");
        // The spine continues explicit past the brace group.
        assert!(matches!(&cod.kind, TyKind::Fn { implicit: false, .. }));
    }

    #[test]
    fn implicit_lambda_binders_parse() {
        let f =
            parse_file("fn f() -> Nat { g(λ {A: Type<0>} {x} (y: Nat) => y) }").unwrap();
        let ExprKind::App { args, .. } = &only_decl(&f).body.result.kind else {
            panic!("expected a call")
        };
        let ExprKind::Lam { binders, .. } = &args[0].kind else { panic!("expected a lambda") };
        assert_eq!(binders.len(), 3);
        assert!(binders[0].implicit && binders[0].ty.is_some());
        assert!(binders[1].implicit && binders[1].ty.is_none(), "`{{x}}` is unannotated");
        assert!(!binders[2].implicit);
    }

    // §8.2's residual case: a motive that *ends* in an implicit binder type
    // parses greedily and correctly — the arms brace cannot match the
    // `{ Ident :` lookahead (`Pat =>` / `Pat(` follows the brace instead).
    #[test]
    fn a_motive_ending_in_an_implicit_binder_type_leaves_the_arms_brace() {
        parse_file(
            "fn f(t: Nat) -> Nat { match t as λ z => {p: Nat} -> Nat { Zero => 0, Succ(k) => k } }",
        )
        .unwrap();
    }

    #[test]
    fn at_marks_a_fully_explicit_call() {
        let f = parse_file("fn f(n: Nat) -> Nat { @g(a, b, p) }").unwrap();
        match &only_decl(&f).body.result.kind {
            ExprKind::App { head, args, explicit, .. } => {
                assert!(matches!(&head.kind, ExprKind::Var(n) if n == "g"));
                assert_eq!(args.len(), 3);
                assert!(*explicit);
            }
            other => panic!("expected an explicit call, got {other:?}"),
        }
    }

    #[test]
    fn plain_call_is_not_explicit() {
        let f = parse_file("fn f(n: Nat) -> Nat { g(a) }").unwrap();
        match &only_decl(&f).body.result.kind {
            ExprKind::App { explicit, .. } => assert!(!*explicit),
            other => panic!("expected a call, got {other:?}"),
        }
    }

    /// Named arguments land in their own list, so the grammar's
    /// positional-then-named rule is a property of the AST rather than a rule
    /// every reader has to re-check (docs/language/named-arguments-design.md §8.1).
    #[test]
    fn a_named_argument_parses_into_its_own_list() {
        let f = parse_file("fn f(n: Nat) -> Nat { g(a, x := b, y := c) }").unwrap();
        match &only_decl(&f).body.result.kind {
            ExprKind::App { args, named, .. } => {
                assert_eq!(args.len(), 1, "one positional");
                assert_eq!(named.len(), 2);
                assert_eq!(named[0].name, "x");
                assert_eq!(named[1].name, "y");
            }
            other => panic!("expected a call, got {other:?}"),
        }
    }

    /// §4.2 is a *parse* rule, so the interleaving never reaches the AST.
    #[test]
    fn a_positional_argument_after_a_named_one_does_not_parse() {
        let e = parse_file("fn f(n: Nat) -> Nat { g(x := b, c) }").unwrap_err();
        assert!(e.msg.contains("positional argument cannot follow a named one"), "{}", e.msg);
    }

    /// The lookahead is two tokens and total: `:=` occurs in no expression
    /// position, so nothing that parsed before parses differently now. `a : b`
    /// inside call parentheses is still the error it always was — it is not
    /// quietly read as a named argument.
    #[test]
    fn a_colon_in_an_argument_is_still_not_a_named_argument() {
        assert!(parse_file("fn f(n: Nat) -> Nat { g(x: b) }").is_err());
    }

    /// Named arguments reach every call spelling, because they are all one
    /// function (`call_args`).
    #[test]
    fn every_call_spelling_takes_named_arguments() {
        for src in [
            "fn f(n: Nat) -> Nat { @g(a, x := b) }",
            "fn f(n: Nat) -> Nat { g<Nat>(a, x := b) }",
            "fn f(n: Nat) -> Nat { n.g(x := b) }",
            "fn f(n: Nat) -> Nat { C(x := b) }",
        ] {
            parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
        }
    }

    #[test]
    fn unclosed_implicit_param_errors() {
        assert!(parse_file("theorem t({a: Nat, b: Nat): a = b { refl }").is_err());
    }

    // Parse a single-declaration `fn f(n: Nat) -> Nat { <body> }` and return
    // the body kind, for exercising expression desugaring.
    fn body(src_body: &str) -> ExprKind {
        let src = format!("fn f(n: Nat) -> Nat {{ {src_body} }}");
        parse_file(&src).unwrap().items.remove(0).into_decl().body.result.kind
    }

    // A byte string is the token `b"…"`, its bytes ASCII characters and
    // escapes; `b` with a space before a string, or `b` alone, is the name it
    // always was, and a character that is not ASCII is refused where it
    // stands (docs/native/io-programs-design.md §5 D3).
    #[test]
    fn byte_strings_are_b_against_a_string() {
        assert!(matches!(body(r#"b"hi\n""#), ExprKind::ByteStr(b) if b == b"hi\n"), "{:?}", body(r#"b"hi\n""#));
        assert!(matches!(body(r#"b"""#), ExprKind::ByteStr(b) if b.is_empty()));
        assert!(matches!(body(r#"b"\x7f\0\xFF""#), ExprKind::ByteStr(b) if b == [0x7f, 0, 0xff]));
        assert!(matches!(body("b"), ExprKind::Var(name) if name == "b"));
        let call = body(r#"g(b"x", b)"#);
        let (head, args, _) = as_call(&call);
        assert_eq!(head, "g");
        assert!(matches!(&args[0].kind, ExprKind::ByteStr(b) if b == b"x"));
        assert!(matches!(&args[1].kind, ExprKind::Var(name) if name == "b"));
        assert!(parse_file(r#"fn f() -> X { b "x" }"#).is_err());
        assert!(parse_file(r#"fn f() -> X { bb"x" }"#).is_err());
        // A byte character, `b'…'`, is one byte the same way.
        assert!(matches!(body(r"b'\n'"), ExprKind::ByteChar(b'\n')));
        assert!(matches!(body(r"b'\xff'"), ExprKind::ByteChar(0xff)));
        let call = body("g(b'x', b)");
        let (_, args, _) = as_call(&call);
        assert!(matches!(&args[0].kind, ExprKind::ByteChar(b'x')));
        assert!(matches!(&args[1].kind, ExprKind::Var(name) if name == "b"));
        let refused = parse_file(r#"fn f() -> X { b"aé" }"#).unwrap_err();
        assert!(refused.msg.contains("a byte string holds ASCII characters"), "{}", refused.msg);
        assert!(refused.msg.contains(r"`\xC3\xA9`"), "{}", refused.msg);
        assert_eq!(refused.span.start, r#"fn f() -> X { b"a"#.len());
    }

    /// The head of an application, as a string — a name or an operator
    /// **symbol**. The symbol is what the parser now emits for `+`/`*`/`<=`,
    /// and what it *means* is the resolver's
    /// (docs/language/classes/operators-onto-classes-design.md §2.1): the fixed names these
    /// tests used to assert survive as that resolver's last rung, which is
    /// where the assertion on them moved (`crates/elab/tests/operators.rs`,
    /// the growth-invariant pins).
    fn as_call(k: &ExprKind) -> (&str, &[Expr], bool) {
        match k {
            ExprKind::App { head, args, explicit, .. } => match &head.kind {
                ExprKind::Var(name) => (name.as_str(), args.as_slice(), *explicit),
                ExprKind::OpSymbol { symbol, .. } => {
                    (symbol.as_str(), args.as_slice(), *explicit)
                }
                other => panic!("expected a named call, got {other:?}"),
            },
            other => panic!("expected a call, got {other:?}"),
        }
    }

    #[test]
    fn apply_lowers_to_one_goal_oriented_nary_call() {
        let k = body("apply trans; give p; q");
        let ExprKind::App { head, args, named, explicit, goal_oriented } = k else {
            panic!("expected an application")
        };
        assert!(matches!(head.kind, ExprKind::Var(ref name) if name == "trans"));
        assert_eq!(args.len(), 2);
        assert!(matches!(args[0].kind, ExprKind::Var(ref name) if name == "p"));
        assert!(matches!(args[1].kind, ExprKind::Var(ref name) if name == "q"));
        assert!(named.is_empty());
        assert!(!explicit);
        assert!(goal_oriented);
    }

    #[test]
    fn apply_chains_by_nesting_the_final_body() {
        let k = body("apply f; apply g; n");
        let ExprKind::App { head, args, goal_oriented: true, .. } = k else {
            panic!("expected outer apply")
        };
        assert!(matches!(head.kind, ExprKind::Var(ref name) if name == "f"));
        assert_eq!(args.len(), 1);
        let ExprKind::App { head, args, goal_oriented: true, .. } = &args[0].kind else {
            panic!("expected nested apply")
        };
        assert!(matches!(head.kind, ExprKind::Var(ref name) if name == "g"));
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn apply_line_accepts_named_implicit_values() {
        let k = body("apply trans(b := n); give p; q");
        let ExprKind::App { head, args, named, goal_oriented: true, .. } = k else {
            panic!("expected an apply call")
        };
        assert!(matches!(head.kind, ExprKind::Var(ref name) if name == "trans"));
        assert_eq!(args.len(), 2);
        assert_eq!(named.len(), 1);
        assert_eq!(named[0].name, "b");
    }

    #[test]
    fn apply_identifier_calls_and_values_remain_ordinary() {
        let ExprKind::App { goal_oriented, .. } = body("apply(n)") else {
            panic!("expected an ordinary call")
        };
        assert!(!goal_oriented);
        assert!(matches!(body("apply"), ExprKind::Var(ref name) if name == "apply"));
    }

    #[test]
    fn apply_requires_a_final_body() {
        let e = parse_file("fn f(n: Nat) -> Nat { apply g; give n; }").unwrap_err();
        assert!(e.msg.contains("final argument body"), "{}", e.msg);
    }

    #[test]
    fn operators_desugar_with_precedence() {
        // `a + b * c` ⇒ `+`(a, `*`(b, c)); `*` binds tighter than `+`.
        let k = body("a + b * c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "+");
        assert_eq!(args.len(), 2);
        let (inner, iargs, _) = as_call(&args[1].kind);
        assert_eq!(inner, "*");
        assert!(matches!(&iargs[0].kind, ExprKind::Var(v) if v == "b"));
    }

    #[test]
    fn addition_is_left_associative() {
        // `a + b + c` ⇒ `+`(`+`(a, b), c).
        let k = body("a + b + c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "+");
        assert_eq!(as_call(&args[0].kind).0, "+");
        assert!(matches!(&args[1].kind, ExprKind::Var(v) if v == "c"));
    }

    #[test]
    fn subtraction_is_left_associative_at_additive_precedence() {
        // `a - b - c * d` ⇒ `-`(`-`(a, b), `*`(c, d)).
        let k = body("a - b - c * d");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "-");
        let ExprKind::App { head, .. } = &k else { unreachable!() };
        assert!(matches!(
            head.kind,
            ExprKind::OpSymbol { fixity: OpFixity::Infix, .. }
        ));
        assert_eq!(as_call(&args[0].kind).0, "-");
        assert_eq!(as_call(&args[1].kind).0, "*");
    }

    #[test]
    fn unary_minus_is_a_prefix_symbol_applied_to_an_expression() {
        let k = body("-3");
        let ExprKind::App { head, args, .. } = k else { panic!("expected prefix call") };
        assert!(matches!(
            head.kind,
            ExprKind::OpSymbol { symbol, fixity: OpFixity::Prefix } if symbol == "-"
        ));
        assert!(matches!(args.as_slice(), [Expr { kind: ExprKind::Num(__n), .. }] if __n.as_u64() == Some(3)));
    }

    #[test]
    fn unary_minus_binds_tighter_than_infix_and_nests() {
        let k = body("--a * b");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "*");
        let (outer, outer_args, _) = as_call(&args[0].kind);
        assert_eq!(outer, "-");
        assert_eq!(as_call(&outer_args[0].kind).0, "-");
    }

    #[test]
    fn vector_types_are_expressions_without_reinterpreting_collection_literals() {
        for src in ["[A; n]", "[[A; n]; m]", "[A -> B; n]", "[List<A>; n]"] {
            let ExprKind::TyLit(ty) = body(src) else { panic!("{src}: expected a type") };
            assert!(matches!(ty.kind, TyKind::Vec { .. }), "{src}");
        }
        let ExprKind::TyLit(ty) = body("[A; n] -> [A; m]") else { panic!("expected an arrow") };
        let TyKind::Fn { dom, cod, .. } = ty.kind else { panic!("expected a function type") };
        assert!(matches!(dom.kind, TyKind::Vec { .. }));
        assert!(matches!(cod.kind, TyKind::Vec { .. }));
        for (src, len) in [("[]", 0), ("[x]", 1), ("[x, y]", 2), ("[x,]", 1)] {
            let ExprKind::CollectionLit(elems) = body(src) else { panic!("{src}: expected a literal") };
            assert_eq!(elems.len(), len, "{src}");
        }
    }

    /// A statement (a declared type) may open with a list literal: the `[`
    /// is the vector type `[T; n]` only when a `;` follows its element
    /// (issues/statement-leading-list-literal-parse.md).
    #[test]
    fn statements_may_start_with_a_list_literal() {
        for (stmt, lhs_len) in [
            ("[1] ++ [2] = [1, 2]", None),
            ("[] = xs", Some(0)),
            ("[x] = xs", Some(1)),
            ("[x, y,] = xs", Some(2)),
            ("[[1]] = [[1]]", Some(1)),
            ("[[Nat; 3]] = xs", Some(1)),
        ] {
            let src = format!("theorem t(xs: List<Nat>, h: {stmt}): {stmt} {{ h }}");
            let f = parse_file(&src).unwrap_or_else(|e| panic!("{stmt}: {}", e.msg));
            let d = only_decl(&f);
            for ty in [&d.params[1].ty, &d.result] {
                let TyKind::Eq(lhs, _) = &ty.kind else { panic!("{stmt}: expected an equality") };
                match (lhs_len, &lhs.kind) {
                    (Some(n), ExprKind::CollectionLit(elems)) => assert_eq!(elems.len(), n, "{stmt}"),
                    (None, ExprKind::App { args, .. }) => {
                        assert!(args.iter().all(|a| matches!(a.kind, ExprKind::CollectionLit(_))), "{stmt}")
                    }
                    (_, other) => panic!("{stmt}: unexpected left endpoint {other:?}"),
                }
            }
        }
        // `[T; n]` keeps its reading in the same positions.
        for ty in ["[Nat; 3]", "[[A; n]; m]", "[A -> B; n]", "[List<A>; n]", "[Nat; 3] -> [Nat; 3]"] {
            let src = format!("fn f(v: {ty}) -> {ty} {{ v }}");
            let f = parse_file(&src).unwrap_or_else(|e| panic!("{ty}: {}", e.msg));
            let d = only_decl(&f);
            for t in [&d.params[0].ty, &d.result] {
                let vec = match &t.kind {
                    TyKind::Fn { dom, .. } => &dom.kind,
                    k => k,
                };
                assert!(matches!(vec, TyKind::Vec { .. }), "{ty}");
            }
        }
        // A malformed vector type past its `;` still reports as one, and a
        // deep nest of literals is one attempt per bracket.
        for (ty, token) in [("[A; n, m]", ","), ("[A; n; m]", ";")] {
            let src = format!("fn f() -> {ty} {{ v }}");
            let err = parse_file(&src).unwrap_err();
            assert!(err.msg.contains("a vector type is `[T; n]`"), "{ty}: {}", err.msg);
            assert_eq!(&src[err.span.start..err.span.end], token, "{ty}");
        }
        let deep = format!("{}1{} = x", "[".repeat(200), "]".repeat(200));
        parse_file(&format!("theorem t(): {deep} {{ refl }}")).unwrap();
    }

    #[test]
    fn malformed_vector_expressions_report_the_relevant_delimiter() {
        for (body, message, token) in [
            ("[A; n, m]", "a vector type is `[T; n]`", ","),
            ("[A; n; m]", "a vector type is `[T; n]`", ";"),
            ("[x, y; n]", "collection literal", ";"),
            ("[x,; n]", "expected an expression", ";"),
            ("[; n]", "expected an expression", ";"),
            ("[A;]", "expected an expression", "]"),
        ] {
            let src = format!("fn f() -> Type {{ {body} }}");
            let err = parse_file(&src).unwrap_err();
            assert!(err.msg.contains(message), "{body}: {}", err.msg);
            assert_eq!(&src[err.span.start..err.span.end], token, "{body}");
        }
    }

    /// Operator structure as an s-expression: `(^ x 2)`, with the fixity of a
    /// unary symbol marked (`(- …)` prefix, `(⁻¹ …)` postfix both print as
    /// `(sym …)`, so the fixity is asserted separately where it matters).
    fn shape(k: &ExprKind) -> String {
        match k {
            ExprKind::App { head, args, .. } if matches!(head.kind, ExprKind::OpSymbol { .. }) => {
                let ExprKind::OpSymbol { symbol, .. } = &head.kind else { unreachable!() };
                let inner: Vec<String> = args.iter().map(|a| shape(&a.kind)).collect();
                format!("({symbol} {})", inner.join(" "))
            }
            ExprKind::Var(n) => n.clone(),
            ExprKind::Num(n) => format!("{}", n.as_u64().unwrap()),
            ExprKind::Dot { recv, name, .. } => format!("{}.{name}", shape(&recv.kind)),
            other => panic!("unexpected {other:?}"),
        }
    }

    /// `^` sits above `*` and above prefix `-`, is right-associative, and
    /// takes a whole prefix expression as its exponent; `⁻¹` binds as tightly
    /// as `.f` (docs/library/inverse-power-notation-design.md §2).
    #[test]
    fn power_and_inverse_precedence() {
        for (src, want) in [
            ("x ^ 2", "(^ x 2)"),
            ("-x ^ 2", "(- (^ x 2))"),
            ("a * b ^ 2", "(* a (^ b 2))"),
            ("a ^ b * c", "(* (^ a b) c)"),
            ("a ^ b ^ c", "(^ a (^ b c))"),
            ("x ^ -1", "(^ x (- 1))"),
            ("x⁻¹", "(⁻¹ x)"),
            ("x⁻¹⁻¹", "(⁻¹ (⁻¹ x))"),
            ("-x⁻¹", "(- (⁻¹ x))"),
            ("x⁻¹ ^ 2", "(^ (⁻¹ x) 2)"),
            ("x ^ 2⁻¹", "(^ x (⁻¹ 2))"),
            ("x⁻¹.f", "(⁻¹ x).f"),
            ("a + b⁻¹ * c", "(+ a (* (⁻¹ b) c))"),
        ] {
            assert_eq!(shape(&body(src)), want, "{src}");
        }
        let ExprKind::App { head, .. } = body("x⁻¹") else { panic!("expected a call") };
        assert!(matches!(head.kind, ExprKind::OpSymbol { fixity: OpFixity::Postfix, .. }));
        let ExprKind::App { head, .. } = body("x ^ 2") else { panic!("expected a call") };
        assert!(matches!(head.kind, ExprKind::OpSymbol { fixity: OpFixity::Infix, .. }));
    }

    #[test]
    fn postfix_and_power_designations_parse() {
        let file = parse_file("designation postfix ⁻¹ at Rat := inv\ndesignation ^ at Rat := pow\n").unwrap();
        let [Item::Designation(inv), Item::Designation(pow)] = file.items.as_slice() else {
            panic!("expected two designations")
        };
        assert_eq!((inv.fixity, inv.symbol.as_str()), (OpFixity::Postfix, "⁻¹"));
        assert_eq!((pow.fixity, pow.symbol.as_str()), (OpFixity::Infix, "^"));
        let err = parse_file("designation postfix - at Int := neg\n").unwrap_err();
        assert!(err.msg.contains("designation postfix ⁻¹"), "{}", err.msg);
    }

    #[test]
    fn boolean_not_is_a_prefix_symbol_and_nests() {
        let k = body("!!a && b");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "&&");
        let (outer, outer_args, _) = as_call(&args[0].kind);
        assert_eq!(outer, "!");
        let ExprKind::App { head, .. } = &args[0].kind else { unreachable!() };
        assert!(matches!(
            head.kind,
            ExprKind::OpSymbol { fixity: OpFixity::Prefix, .. }
        ));
        assert_eq!(as_call(&outer_args[0].kind).0, "!");
    }

    /// `↑` binds as tightly as the other prefixes: `↑n - 1` casts `n`, and
    /// the subtraction happens at the target (docs/language/casting-design.md §14).
    #[test]
    fn a_cast_is_a_prefix_symbol_binding_tighter_than_infix() {
        let k = body("↑n - 1");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "-");
        let (cast, cast_args, _) = as_call(&args[0].kind);
        assert_eq!(cast, "↑");
        assert_eq!(cast_args.len(), 1);
        let ExprKind::App { head, .. } = &args[0].kind else { unreachable!() };
        assert!(matches!(
            head.kind,
            ExprKind::OpSymbol { fixity: OpFixity::Prefix, .. }
        ));
    }

    #[test]
    fn semantic_brackets_desugar_to_is_true() {
        let k = body("⟦!b⟧");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "Bool::IsTrue");
        assert_eq!(args.len(), 1);
        assert_eq!(as_call(&args[0].kind).0, "!");

        let err = parse_file("fn f(b: Bool) -> Type { ⟦b }").unwrap_err();
        assert!(err.msg.contains("⟧` to close Boolean reflection"), "{}", err.msg);
    }

    #[test]
    fn prefix_designation_records_a_distinct_fixity() {
        let f = parse_file("fn neg(a: Nat) -> Nat { a } designation prefix - at Nat := neg")
            .expect("prefix designation");
        let Item::Designation(d) = &f.items[1] else { panic!("expected designation") };
        assert_eq!(d.symbol, "-");
        assert_eq!(d.fixity, OpFixity::Prefix);
    }

    #[test]
    fn boolean_not_designation_is_prefix() {
        let f = parse_file("fn not(a: Nat) -> Nat { a } designation prefix ! at Nat := not")
            .expect("prefix designation");
        let Item::Designation(d) = &f.items[1] else { panic!("expected designation") };
        assert_eq!(d.symbol, "!");
        assert_eq!(d.fixity, OpFixity::Prefix);
    }

    #[test]
    fn infix_minus_designation_is_distinct_from_prefix_minus() {
        let f = parse_file(
            "fn neg(a: Nat) -> Nat { a }
             fn sub(a: Nat, b: Nat) -> Nat { a }
             designation prefix - at Nat := neg
             designation - at Nat := sub",
        )
        .expect("prefix and infix minus designations");
        let Item::Designation(prefix) = &f.items[2] else { panic!("expected designation") };
        let Item::Designation(infix) = &f.items[3] else { panic!("expected designation") };
        assert_eq!((prefix.symbol.as_str(), prefix.fixity), ("-", OpFixity::Prefix));
        assert_eq!((infix.symbol.as_str(), infix.fixity), ("-", OpFixity::Infix));
    }

    #[test]
    fn relational_notation_precedence_and_non_chaining() {
        let k = body("a⊔b⊔c≈d⊔e");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "≈");
        let (join, left, _) = as_call(&args[0].kind);
        assert_eq!(join, "⊔");
        assert_eq!(as_call(&left[0].kind).0, "⊔");
        assert_eq!(as_call(&args[1].kind).0, "⊔");
        let k = body("a⊔b*c");
        let (_, args, _) = as_call(&k);
        assert_eq!(as_call(&args[1].kind).0, "*");
        for expression in ["a≈b≈c", "a≈b=c", "a=b≈c"] {
            let error = parse_file(&format!("fn f() -> Type {{ {expression} }}")).unwrap_err();
            assert!(error.msg.contains("comparisons do not chain"), "{}", error.msg);
        }
        let k = body("f(≈, ⊔)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::OpSymbol { symbol, .. } if symbol == "≈"));
        assert!(matches!(&args[1].kind, ExprKind::OpSymbol { symbol, .. } if symbol == "⊔"));
    }

    #[test]
    fn meet_binds_tighter_than_join() {
        // `a ⊔ b ⊓ c ≈ d` is `(a ⊔ (b ⊓ c)) ≈ d`, and `⊓` is left-associative.
        let k = body("a⊔b⊓c≈d");
        let (_, args, _) = as_call(&k);
        let (join, operands, _) = as_call(&args[0].kind);
        assert_eq!(join, "⊔");
        assert_eq!(as_call(&operands[1].kind).0, "⊓");
        let k = body("a⊓b⊓c");
        let (meet, operands, _) = as_call(&k);
        assert_eq!(meet, "⊓");
        assert_eq!(as_call(&operands[0].kind).0, "⊓");
        let k = body("f(⊓)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::OpSymbol { symbol, .. } if symbol == "⊓"));
    }

    // -- integer operator symbols (issues/integer-operator-symbols.md) ----

    #[test]
    fn integer_operators_take_rusts_rungs() {
        // `/` and `%` share `*`'s rung, left-associative.
        let k = body("a / b % c * d");
        let (mul, operands, _) = as_call(&k);
        assert_eq!(mul, "*");
        let (rem, operands, _) = as_call(&operands[0].kind);
        assert_eq!(rem, "%");
        assert_eq!(as_call(&operands[0].kind).0, "/");
        // `|` below `&` below the shifts below `+`, all above `&&`.
        let k = body("a | b & c << d + e && f");
        let (and, operands, _) = as_call(&k);
        assert_eq!(and, "&&");
        let (or, operands, _) = as_call(&operands[0].kind);
        assert_eq!(or, "|");
        let (band, operands, _) = as_call(&operands[1].kind);
        assert_eq!(band, "&");
        let (shl, operands, _) = as_call(&operands[1].kind);
        assert_eq!(shl, "<<");
        assert_eq!(as_call(&operands[1].kind).0, "+");
        // And above the comparison rung: `a & m = 0` is `(a & m) = 0`.
        let ExprKind::Eq(lhs, _) = body("a & m = 0") else { panic!("not an equation") };
        assert_eq!(as_call(&lhs.kind).0, "&");
    }

    #[test]
    fn exclusive_or_sits_between_or_and_and() {
        // issues/bitvec-xor-complement-symbols.md: Rust's order, `|` below
        // `⊕` below `&`, and `⊕` left-associative.
        let k = body("a | b ⊕ c & d");
        let (or, operands, _) = as_call(&k);
        assert_eq!(or, "|");
        let (xor, operands, _) = as_call(&operands[1].kind);
        assert_eq!(xor, "⊕");
        assert_eq!(as_call(&operands[1].kind).0, "&");
        let k = body("a ⊕ b ⊕ c");
        let (xor, operands, _) = as_call(&k);
        assert_eq!(xor, "⊕");
        assert_eq!(as_call(&operands[0].kind).0, "⊕");
        // A designation reference, as every infix symbol has.
        let k = body("f(⊕)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::OpSymbol { symbol, .. } if symbol == "⊕"));
        assert_eq!(operator_form("⊕", OpFixity::Infix), Some(OperatorForm::Infix(7, 8)));
    }

    #[test]
    fn complement_is_a_prefix_operator() {
        // `~` binds as `-` and `!` do: tighter than every infix rung, looser
        // than a postfix application, and it nests.
        let k = body("~a ⊕ b");
        let (xor, operands, _) = as_call(&k);
        assert_eq!(xor, "⊕");
        let ExprKind::App { head, .. } = &operands[0].kind else { panic!("not a call") };
        assert!(matches!(&head.kind, ExprKind::OpSymbol { symbol, fixity: OpFixity::Prefix } if symbol == "~"));
        let (_, inner, _) = as_call(&operands[0].kind);
        assert!(matches!(&inner[0].kind, ExprKind::Var(a) if a == "a"));
        let k = body("~~x.f()");
        let (not, inner, _) = as_call(&k);
        assert_eq!(not, "~");
        assert_eq!(as_call(&inner[0].kind).0, "~");
        assert_eq!(operator_form("~", OpFixity::Prefix), Some(OperatorForm::Prefix));
        let file = parse_file("designation prefix ~ at BitVec(n) := BitVec::complement").unwrap();
        let Item::Designation(d) = &file.items[0] else { panic!("not a designation") };
        assert_eq!((d.symbol.as_str(), d.fixity), ("~", OpFixity::Prefix));
    }

    #[test]
    fn a_suffixed_numeral_is_one_atom() {
        // issues/integer-literal-width-suffix.md.
        let k = body("0x80u8");
        let ExprKind::SuffixedNum { value, suffix } = &k else { panic!("not a suffixed numeral: {k:?}") };
        assert_eq!((value.as_u64(), suffix.as_str()), (Some(0x80), "u8"));
        let k = body("i + 1u64");
        let (plus, operands, _) = as_call(&k);
        assert_eq!(plus, "+");
        assert!(matches!(&operands[1].kind, ExprKind::SuffixedNum { suffix, .. } if suffix == "u64"));
    }

    #[test]
    fn a_spaced_double_gt_shifts_and_a_tight_one_closes_two_lists() {
        let k = body("a >> b >> c");
        let (shr, operands, _) = as_call(&k);
        assert_eq!(shr, ">>");
        assert_eq!(as_call(&operands[0].kind).0, ">>");
        // Nested type arguments are unchanged.
        let src = "fn f(x: List<List<Nat>>) -> List<List<Nat>> { id<List<List<Nat>>>(x) }";
        parse_file(src).unwrap();
        // `a>>b` is two closers, and the refusal says how to write the shift.
        let src = "fn f(n: Nat) -> Nat { n>>1 }";
        let e = parse_file(src).unwrap_err();
        assert!(e.msg.contains("`a >> b`"), "{}", e.msg);
        // After `(` or `,` the bare symbol is a designation reference.
        let k = body("f(>>, <<)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::OpSymbol { symbol, .. } if symbol == ">>"));
        assert!(matches!(&args[1].kind, ExprKind::OpSymbol { symbol, .. } if symbol == "<<"));
    }

    #[test]
    fn integer_operators_designate_and_keep_their_neighbours() {
        let src = "designation >> at SInt(n) := SInt::shift_right\n\
                   designation << at SInt(n) := SInt::shift_left\n\
                   designation / at Nat := Nat::div\n\
                   designation | at Nat := Nat::bor\n";
        let file = parse_file(src).unwrap();
        let symbols: Vec<_> = file
            .items
            .iter()
            .map(|it| match it {
                Item::Designation(d) => d.symbol.as_str(),
                _ => panic!("not a designation"),
            })
            .collect();
        assert_eq!(symbols, [">>", "<<", "/", "|"]);
        // `//` is still a comment, and `⟨a |⟩` still the left injection.
        assert!(matches!(body("a // b\n"), ExprKind::Var(ref n) if n == "a"));
        let ExprKind::App { head, args, .. } = body("⟨a | b |⟩") else { panic!("not a call") };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == ANON_CTOR_LEFT));
        assert_eq!(as_call(&args[0].kind).0, "|");
    }

    // -- binder symbols (issues/binder-symbol-as-notation.md) --------------

    #[test]
    fn the_generic_symbol_is_a_three_byte_infix_at_multiplicative_precedence() {
        // Three bytes, so the two-byte window cannot see it; no whitespace
        // here, to say the lexer claims it on adjacency like every other
        // symbol. It shares `*`'s left-associative rung, which is where
        // issues/notation-extensibility.md's precedence-by-class scheme puts a
        // dot-shaped operator.
        let k = body("a∙b * c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "*");
        assert_eq!(as_call(&args[0].kind).0, "∙");
        let k = body("a + b ∙ c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "+");
        assert_eq!(as_call(&args[1].kind).0, "∙");
        // And between delimiters it is the bare designation reference, the
        // same rule `Monoid(+)` reserved — which is what lets a constraint
        // slot name it, and so what makes the duplicate control writable.
        let k = body("f(∙, x)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(
            &args[0].kind,
            ExprKind::OpSymbol { symbol: s, fixity: OpFixity::Infix } if s == "∙"
        ));
    }

    #[test]
    fn as_attaches_a_body_spelling_to_a_declaring_binder() {
        // A class head's index parameter, and a `fn`'s value parameter. In
        // both the *name* is untouched — that is the whole design: the
        // identifier is the interface spelling and the symbol is the body's.
        let f = parse_file(
            "class Sem<A>(op as ∙: A -> A -> A) { assoc: (x: A) -> x ∙ x = x }
             fn fold<A: Sem(op)>(op as ∙: A -> A -> A, x: A) -> A { x ∙ x }",
        )
        .unwrap();
        let Item::Class(c) = &f.items[0] else { panic!("expected a class") };
        assert_eq!(c.valparams[0].name, "op");
        assert_eq!(c.valparams[0].symbol.as_deref(), Some("∙"));
        let Item::Decl(d) = &f.items[1] else { panic!("expected a declaration") };
        // The constraint slot is untouched: it is a *reference*, and its
        // grammar is exactly what the operators round left it.
        let op = d.params.iter().find(|p| p.name == "op").expect("`op` is still the name");
        assert_eq!(op.symbol.as_deref(), Some("∙"));
        assert!(d.params.iter().all(|p| p.name != "∙"));
    }

    #[test]
    fn as_marks_the_name_it_is_written_on_inside_a_run() {
        // The `self` sentence, applied to the other modifier
        // (issues/modifiers-in-shared-binder-runs.md): the symbol goes to the
        // ONE name it prefixes, and the run shares only the annotation. So
        // `g as ∙, h: A -> A -> A` is `g` carrying `∙` and `h` carrying
        // nothing, both at the same type.
        let f =
            parse_file("fn f<A>(g as ∙, h: A -> A -> A, x: A) -> A { g(x, h(x, x)) }").unwrap();
        let Item::Decl(d) = &f.items[0] else { panic!("expected a declaration") };
        assert_eq!(d.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), [
            "g", "h", "x"
        ]);
        assert_eq!(d.params[0].symbol.as_deref(), Some("∙"));
        assert_eq!(d.params[1].symbol, None, "the symbol does not reach the rest of the run");
        // A run's later name may carry its own, and the two are distinct
        // spellings at one annotation.
        let f = parse_file("fn f<A>(g as ∙, h as +: A -> A -> A, x: A) -> A { x ∙ x }").unwrap();
        let Item::Decl(d) = &f.items[0] else { panic!("expected a declaration") };
        assert_eq!(d.params[0].symbol.as_deref(), Some("∙"));
        assert_eq!(d.params[1].symbol.as_deref(), Some("+"));
        // The group *after* an `as` binder is untouched, as it always was: the
        // mark ends at its own name, and `x, y: A` is an ordinary shared run.
        parse_file("fn f<A>(g as ∙: A -> A -> A, x, y: A) -> A { x ∙ y }").unwrap();
    }

    #[test]
    fn as_can_only_install_a_symbol_that_already_lexes() {
        // The curated table is what bounds the device: `as` adds a *position*
        // for a symbol and never a symbol (issues/notation-extensibility.md).
        let e = parse_file("fn f<A>(g as mul: A -> A -> A, x: A) -> A { x }").unwrap_err();
        assert!(e.msg.contains("can only install one that already lexes"), "{}", e.msg);
        assert!(e.msg.contains("`∙`"), "{}", e.msg);
    }

    #[test]
    fn a_record_value_parameter_takes_no_body_spelling() {
        // `as` is a declaring binder's device where the declaration has a body
        // to spell. A `record`'s value parameter is a term its fields mention;
        // refused by name rather than parsed and silently dropped.
        let e = parse_file("record R(p as ∙: Nat) { q: Nat }").unwrap_err();
        assert!(e.msg.contains("class head's device"), "{}", e.msg);
    }

    // -- list append (issues/list-append-symbol.md) ------------------------

    #[test]
    fn append_symbol_is_a_two_byte_infix_at_additive_precedence() {
        // No whitespace: the lexer must claim `++` before either `+` can be
        // emitted. It sits on `+`'s rung but is RIGHT-associative (the fixity
        // table says why: fixity is proof-relevant, and append lemmas are
        // stated right-nested), so in the mixed spelling `++` takes the whole
        // `+`-expression as its tail. Mixing the two is type-nonsense either
        // way; what this pins is that `++` lexed at all and where it binds.
        let k = body("a++b + c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "++");
        assert_eq!(as_call(&args[1].kind).0, "+");
    }

    #[test]
    fn append_symbol_chains_right_associatively() {
        // `a ++ b ++ c` is `a ++ (b ++ c)`: the shape `append`'s recursion
        // unfolds against and the shape every append lemma is stated in
        // (docs/showcase/README.md, friction 2).
        let k = body("a ++ b ++ c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "++");
        let (inner, inner_args, _) = as_call(&args[1].kind);
        assert_eq!(inner, "++");
        assert_eq!(inner_args.len(), 2);
    }

    #[test]
    fn append_symbol_parses_in_designations_binders_and_arguments() {
        let f = parse_file(
            "class Mon<A>(op: A -> A -> A) { unit: A }
             designation<A> ++ at List<A> := append
             fn fold<A: Mon(++)>(xs: List<A>) -> A { use(++, xs) }",
        )
        .unwrap();
        assert_eq!(f.items.len(), 3);
        let Item::Designation(d) = &f.items[1] else { panic!("expected designation") };
        assert_eq!(d.symbol, "++");
        let Item::Decl(d) = &f.items[2] else { panic!("expected declaration") };
        let ExprKind::App { args, .. } = &d.body.result.kind else { panic!("expected call") };
        assert!(matches!(
            &args[0].kind,
            ExprKind::OpSymbol { symbol: s, fixity: OpFixity::Infix } if s == "++"
        ));
    }

    #[test]
    fn less_than_parses_as_a_designation_symbol_before_at() {
        let f = parse_file(
            "designation < at Nat := Lt
             designation<A> < at List<A> := before",
        )
        .unwrap();
        let Item::Designation(plain) = &f.items[0] else { panic!("expected designation") };
        assert_eq!(plain.symbol, "<");
        assert!(plain.tyvars.is_empty());
        let Item::Designation(generic) = &f.items[1] else { panic!("expected designation") };
        assert_eq!(generic.symbol, "<");
        assert_eq!(generic.tyvars, ["A"]);
    }

    // -- the logical connectives (issues/std-logic-module.md) ---------------
    //
    // What the elaborator's `logic.rs` cannot see: the lexer windows, and the
    // desugared node shapes. Meaning is tested there, spelling here.

    /// `<->` is three ASCII bytes and is matched in the three-byte window,
    /// which the two-byte `<=` would otherwise take a `<` off — the one place
    /// the new tokens could have broken an old one.
    #[test]
    fn the_ascii_iff_does_not_disturb_the_comparison_tokens() {
        use crate::lexer::{lex, TokKind};
        let kinds = |s: &str| {
            lex(s).unwrap().into_iter().map(|t| t.kind).collect::<Vec<_>>()
        };
        assert_eq!(kinds("a <-> b")[1], TokKind::Iff);
        assert_eq!(kinds("a <= b")[1], TokKind::LtEq);
        assert_eq!(kinds("a < b")[1], TokKind::Lt);
        assert_eq!(kinds("a ≠ b")[1], TokKind::Ne);
        // `↔` and `<->` are one token, so nothing downstream can tell them
        // apart — the property the library's casual spelling rests on.
        assert_eq!(kinds("a ↔ b"), kinds("a <-> b"));
    }

    #[test]
    fn the_unicode_arrow_is_the_same_token_as_ascii() {
        use crate::lexer::lex;
        let kinds = |s: &str| {
            lex(s).unwrap().into_iter().map(|t| t.kind).collect::<Vec<_>>()
        };
        assert_eq!(kinds("A → B"), kinds("A -> B"));
        parse_file("theorem id<A>(): A → A { λ x => x }").unwrap();
    }

    /// `¬` is two bytes and `∧`/`∨`/`∃`/`∀` are three, so they are matched in
    /// different windows; a window that lands mid-codepoint must mean "not a
    /// token of this width" rather than panic.
    #[test]
    fn the_connective_glyphs_lex_at_their_own_widths() {
        use crate::lexer::{lex, TokKind};
        let kinds =
            |s: &str| lex(s).unwrap().into_iter().map(|t| t.kind).collect::<Vec<_>>();
        assert_eq!(kinds("¬a")[0], TokKind::Neg);
        assert_eq!(kinds("a ∧ b")[1], TokKind::Wedge);
        assert_eq!(kinds("a ∨ b")[1], TokKind::Vee);
        assert_eq!(kinds("∃ k")[0], TokKind::Exists);
        assert_eq!(kinds("∑ k")[0], TokKind::BigSum);
        assert_eq!(kinds("∏ k")[0], TokKind::BigProd);
        assert_eq!(kinds("↑n")[0], TokKind::UpArrow);
        assert_eq!(kinds("∀ k")[0], TokKind::Forall);
        // `λ`, the other two-byte glyph, is unmoved.
        assert_eq!(kinds("λ x")[0], TokKind::Lambda);
    }

    /// `P ∧ Q` desugars to the *type application* `And<P, Q>` — the spelling a
    /// writer could have typed — and not to an operator symbol for the
    /// resolver to place. A connective is a type former, like `=`.
    #[test]
    fn a_connective_desugars_to_its_declared_type() {
        let ExprKind::TyApp { head, args } = body("p ∧ q") else {
            panic!("expected a type application")
        };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == "And"));
        assert_eq!(args.len(), 2);
        let ExprKind::TyApp { head, .. } = body("p ∨ q") else { panic!("expected TyApp") };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == "Or"));
        let ExprKind::TyApp { head, .. } = body("p ↔ q") else { panic!("expected TyApp") };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == "Iff"));
        // `¬` is an ordinary call: `Not` takes a `Type` and has no type
        // parameters to fill.
        assert_eq!(as_call(&body("¬p")).0, "Not");
    }

    /// A bracket lifts the codomain's `↔` restriction, so the parentheses that
    /// group a connective inside a codomain are readable rather than a parse
    /// error (issues/iff-in-type-valued-body.md). The spelling assertion is
    /// here; that the two spellings mean one type is
    /// `crates/elab/tests/logic.rs`.
    #[test]
    fn a_bracket_lifts_the_codomain_iff_restriction() {
        // Bracketed: the `↔` is the codomain, so the type is a `Fn` whose
        // codomain is the `Iff`.
        let ExprKind::TyLit(ty) = body("P -> (Q ↔ R)") else { panic!("expected a type") };
        let TyKind::Fn { cod, .. } = &ty.kind else { panic!("expected a Pi, got {ty:?}") };
        assert!(matches!(&cod.kind, TyKind::Named { name, args } if name == "Iff" && args.len() == 2));
        // Bare: the `↔` is the loosest rung, so it is the root and the arrow
        // is its left operand. The restriction still does its job.
        let ExprKind::TyApp { head, args } = body("P -> Q ↔ R") else {
            panic!("expected the `↔` at the root")
        };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == "Iff"));
        assert!(matches!(&args[0].kind, TyKind::Fn { .. }));
        // Every other bracket, same rule: a type-argument list, a call's
        // arguments, and a group whose own top level is an arrow (which is
        // read by `ty_atom`'s parenthesis rule rather than `atom`'s).
        for src in ["P -> Or<Q ↔ R, P>", "P -> ¬(Q ↔ R)", "P -> (Q -> R ↔ P)"] {
            let ExprKind::TyLit(ty) = body(src) else { panic!("{src}: expected a type") };
            assert!(matches!(&ty.kind, TyKind::Fn { .. }), "{src}: {ty:?}");
        }
    }

    /// A binder-headed function type is offered to the `↔` rung too, which
    /// `Parser::ty`'s early `return` used to skip
    /// (issues/binder-headed-arrow-as-connective-operand.md). The Π is
    /// complete before the `↔` applies, so it is the *whole* arrow that
    /// becomes the left operand — the binder does not reach the right one.
    #[test]
    fn a_binder_headed_function_type_reaches_the_iff_rung() {
        let ExprKind::TyLit(ty) = body("(a: A) -> P(a) ↔ R") else {
            panic!("expected a type")
        };
        let TyKind::Named { name, args } = &ty.kind else {
            panic!("expected the `↔` at the root, got {ty:?}")
        };
        assert_eq!(name, "Iff");
        assert!(matches!(&args[0].kind, TyKind::Fn { binder, .. } if binder.as_deref() == Some("a")));
        // A codomain still declines, so the `↔` after a binder-headed
        // codomain belongs to the outer arrow: `(P -> (a: A) -> Q(a)) ↔ R`.
        let ExprKind::TyApp { head, args } = body("P -> (a: A) -> Q(a) ↔ R") else {
            panic!("expected the `↔` at the root")
        };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == "Iff"));
        assert!(matches!(&args[0].kind, TyKind::Fn { binder, .. } if binder.is_none()));
    }

    #[test]
    fn term_introduction_type_connectives_and_boolean_operators_are_distinct() {
        let ExprKind::App { head, args, .. } = body("⟨p, q⟩") else {
            panic!("expected anonymous constructor application")
        };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == ANON_CTOR_ONLY));
        assert_eq!(args.len(), 2);

        assert!(matches!(body("P ∧ Q"), ExprKind::TyApp { .. }));
        let boolean = body("a && b");
        let (name, _, _) = as_call(&boolean);
        assert_eq!(name, "&&");
    }

    /// `∀` is a **synonym**: it produces the same `TyKind::Fn` the arrow form
    /// does, so nothing downstream learns a second spelling.
    #[test]
    fn forall_desugars_to_the_dependent_function_type() {
        let ExprKind::TyLit(ty) = body("∀ k: Nat, k = k") else { panic!("expected a type") };
        let TyKind::Fn { binder, implicit, .. } = &ty.kind else { panic!("expected a Pi") };
        assert_eq!(binder.as_deref(), Some("k"));
        assert!(!implicit);
        // Two names share one annotation and curry, exactly as a binder group
        // does.
        let ExprKind::TyLit(ty) = body("∀ k, l: Nat, k = l") else { panic!("expected a type") };
        let TyKind::Fn { cod, .. } = &ty.kind else { panic!("expected a Pi") };
        assert!(matches!(&cod.kind, TyKind::Fn { .. }));
    }

    /// `∃` supplies the type argument from its own binder, which is what the
    /// bare record spelling cannot do
    /// (issues/exists-type-arg-not-inferred.md).
    #[test]
    fn exists_desugars_to_a_type_applied_record() {
        let ExprKind::App { head, args, .. } = body("∃ k: Nat, k = k") else {
            panic!("expected a call")
        };
        let ExprKind::TyApp { head, args: targs } = &head.kind else {
            panic!("expected the type argument to be supplied")
        };
        assert!(matches!(&head.kind, ExprKind::Var(n) if n == "Exists"));
        assert!(matches!(&targs[0].kind, TyKind::Nat));
        assert!(matches!(&args[0].kind, ExprKind::Lam { .. }));
    }

    /// `∑ k < n, e` is the range sum `MonoidRel::range(+, n, λ (k: Nat) => e)`
    /// and `∏` the same at `*`: a synonym, as `∃` is.
    #[test]
    fn big_operators_desugar_to_the_range_sum() {
        for (src, sym) in [("∑ k < n, f(k)", "+"), ("∏ k < n, f(k)", "*")] {
            let k = body(src);
            let (name, args, _) = as_call(&k);
            assert_eq!(name, "MonoidRel::range");
            assert!(matches!(&args[0].kind, ExprKind::OpSymbol { symbol, .. } if symbol == sym));
            assert!(matches!(&args[1].kind, ExprKind::Var(n) if n == "n"));
            let ExprKind::Lam { binders, body } = &args[2].kind else { panic!("expected the body's λ") };
            assert_eq!(binders[0].name, "k");
            assert!(matches!(binders[0].ty.as_ref().map(|t| &t.kind), Some(TyKind::Nat)));
            assert_eq!(as_call(&body.kind).0, "f");
        }
    }

    /// The big operator is an operand, its body an arithmetic expression that
    /// runs right as far as one can: `x + ∑ …` adds a sum, `∑ k < n, f(k) + 1`
    /// sums `f(k) + 1`, and a comparison after the body compares the sum.
    #[test]
    fn big_operator_body_stops_at_a_relation() {
        let k = body("x + ∑ k < n, f(k)");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "+");
        assert_eq!(as_call(&args[1].kind).0, "MonoidRel::range");
        let k = body("∑ k < n, f(k) + 1");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "MonoidRel::range");
        let ExprKind::Lam { body: summand, .. } = &args[2].kind else { panic!("expected the body's λ") };
        assert_eq!(as_call(&summand.kind).0, "+");
        let k = body("∑ k < n + 1, f(k) ≈ s");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "≈");
        let (name, args, _) = as_call(&args[0].kind);
        assert_eq!(name, "MonoidRel::range");
        assert_eq!(as_call(&args[1].kind).0, "+");
        let k = body("∑ i < m, ∑ j < n, f(i, j)");
        let (_, args, _) = as_call(&k);
        let ExprKind::Lam { body: summand, .. } = &args[2].kind else { panic!("expected the body's λ") };
        assert_eq!(as_call(&summand.kind).0, "MonoidRel::range");
    }

    #[test]
    fn big_operator_needs_a_bound() {
        let e = parse_file("fn f(n: Nat) -> Nat { ∑ k <= n, k }").unwrap_err();
        assert!(e.msg.contains("ranges below a bound"), "{}", e.msg);
        let e = parse_file("fn f(n: Nat) -> Nat { ∑ k < n k }").unwrap_err();
        assert!(e.msg.contains("between a big operator's bound and its body"), "{}", e.msg);
    }

    // -- the Boolean operators (issues/bool-operator-designations.md) -------

    #[test]
    fn boolean_operators_desugar_with_precedence() {
        // `a || b && c` ⇒ `||`(a, `&&`(b, c)); `&&` binds tighter than `||`,
        // and both sit below the arithmetic pair: `a || b + c` keeps the sum
        // whole.
        let k = body("a || b && c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "||");
        assert_eq!(as_call(&args[1].kind).0, "&&");
        let k = body("a && b || c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "||");
        assert_eq!(as_call(&args[0].kind).0, "&&");
        let k = body("a || b + c");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "||");
        assert_eq!(as_call(&args[1].kind).0, "+");
    }

    #[test]
    fn boolean_operators_bind_tighter_than_equality() {
        // Unlike C, where `&&` is looser than the comparisons: the comparison
        // rung here is propositional, and a theorem statement wants the
        // Boolean reading whole — `x && True = x` is `(x && True) = x`,
        // exactly as `x + A.unit = x` relies on for `+`.
        let k = body("x && y = z");
        let ExprKind::Eq(lhs, rhs) = &k else { panic!("expected `=`, got {k:?}") };
        assert_eq!(as_call(&lhs.kind).0, "&&");
        assert!(matches!(&rhs.kind, ExprKind::Var(v) if v == "z"));
    }

    #[test]
    fn boolean_symbols_are_designation_references_between_delimiters() {
        // `f(||, x)` — the lone symbol after `(` is the unapplied
        // [`ExprKind::OpSymbol`], the same rule `Monoid(+)` reserved.
        let k = body("f(||, x)");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "f");
        assert!(matches!(
            &args[0].kind,
            ExprKind::OpSymbol { symbol: s, fixity: OpFixity::Infix } if s == "||"
        ));
    }

    #[test]
    fn a_parenthesised_symbol_is_the_bare_symbol_anywhere() {
        // `(<=)` is the node `f(<=, x)` gives the lone symbol, in any
        // expression position: a call's argument, a receiver call's.
        let k = body("f(x, (<=))");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[1].kind, ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix } if symbol == "<="));
        let k = body("xs.SortedPerm((<=), ys)");
        let ExprKind::Dot { args: Some(args), .. } = &k else { panic!("expected a receiver call, got {k:?}") };
        assert!(matches!(&args[0].kind, ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix } if symbol == "<="));
        // Every infix symbol reads this way, `-` as subtraction.
        for sym in ["+", "-", "*", "<", "&&", "||", "++", "^", "≈"] {
            let k = body(&format!("({sym})"));
            assert!(
                matches!(&k, ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix } if symbol == sym),
                "({sym}) gave {k:?}"
            );
        }
        // A symbol with an operand is no section: `(-x)` is still negation.
        let k = body("(-x)");
        assert!(matches!(&k, ExprKind::App { head, .. } if matches!(head.kind, ExprKind::OpSymbol { fixity: OpFixity::Prefix, .. })));
    }

    #[test]
    fn a_list_pattern_with_only_a_rest_is_refused() {
        // `[..r]` is the whole list: a plain binder says that.
        let e = parse_file("fn f(xs: List<Nat>) -> Nat { match xs { [..r] => 0 } }").unwrap_err();
        assert!(e.msg.contains("names an element before `..rest`"), "{}", e.msg);
        assert!(parse_file("fn f(xs: List<Nat>) -> Nat { match xs { [a, ..r] => a, [] => 0 } }").is_ok());
    }

    #[test]
    fn a_bare_pipe_in_a_pattern_stays_unclaimed() {
        // `&` and `|` are the bitwise operators in an *expression*
        // (issues/integer-operator-symbols.md); in a pattern `|` is still
        // reserved against a future or-pattern, as Rust has both.
        let e = parse_file("fn f(n: Nat) -> Nat { match n { Zero | Succ(_) => 0 } }").unwrap_err();
        assert!(e.msg.contains("Pipe"), "{}", e.msg);
    }

    // -- the comparison level (issues/comparison-operators.md) --------------

    #[test]
    fn le_desugars_to_the_proposition_not_the_boolean() {
        // `a <= b` ⇒ `Le(a, b)`, the Type-valued proposition. `leb` is still
        // callable by name where a Bool is wanted; `<=` is not
        // context-sensitive.
        let k = body("a <= b");
        let (name, args, explicit) = as_call(&k);
        assert_eq!(name, "<=");
        assert!(!explicit);
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0].kind, ExprKind::Var(v) if v == "a"));
        assert!(matches!(&args[1].kind, ExprKind::Var(v) if v == "b"));
    }

    #[test]
    fn comparison_binds_looser_than_arithmetic() {
        // `a + b <= c * d` ⇒ Le(add(a, b), mul(c, d)) — the whole arithmetic
        // expression on each side, no parentheses needed.
        let k = body("a + b <= c * d");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "<=");
        assert_eq!(as_call(&args[0].kind).0, "+");
        assert_eq!(as_call(&args[1].kind).0, "*");
    }

    #[test]
    fn comparisons_do_not_chain() {
        // Non-associative at their shared level: `a <= b <= c` has no reading,
        // and says so rather than silently grouping.
        for src in [
            "a <= b <= c",
            "a <= b == c",
            "a = b <= c",
            "a < b <= c",
            "a ≠ b = c",
            "a = b ≠ c",
            "a ≠ b ≠ c",
        ] {
            let e = parse_file(&format!("fn f() -> Nat {{ {src} }}")).unwrap_err();
            assert!(e.msg.contains("do not chain"), "{src}: {}", e.msg);
        }
    }

    #[test]
    fn inequality_is_exact_negated_equality_sugar_with_logic_precedence() {
        let inequality = body("a ≠ b");
        let explicit = body("¬(a = b)");

        let inequality_call = as_call(&inequality);
        let explicit_call = as_call(&explicit);
        assert_eq!(inequality_call.0, "Not");
        assert_eq!(explicit_call.0, "Not");
        assert!(matches!(inequality_call.1[0].kind, ExprKind::Eq(..)));
        assert!(matches!(explicit_call.1[0].kind, ExprKind::Eq(..)));

        // Comparison is tighter than conjunction.
        let conjunction = body("a ≠ b ∧ P");
        let ExprKind::TyApp { head, args } = conjunction else {
            panic!("expected an And type application")
        };
        assert!(matches!(&head.kind, ExprKind::Var(name) if name == "And"));
        let TyKind::OfExpr(left) = &args[0].kind else {
            panic!("expected inequality as the left conjunct")
        };
        assert_eq!(as_call(&left.kind).0, "Not");

        // Prefix negation is looser than comparison, giving double negation.
        let outer = body("¬(a ≠ b)");
        let (_, args, _) = as_call(&outer);
        assert_eq!(as_call(&args[0].kind).0, "Not");

        let ascii = parse_file("fn f(a, b: Nat) -> Type { a != b }").unwrap_err();
        assert!(ascii.msg.contains("unexpected character"), "{}", ascii.msg);
    }

    #[test]
    fn a_comparison_still_parses_in_a_type() {
        // The statement position is where `<=` earns its keep:
        // `hle: n <= m` is the `Le(n, m)` hypothesis, and it composes with
        // `->` exactly as `Le(n, m)` did (`<=` binds tighter than the arrow).
        let f = parse_file("theorem t(n: Nat, m: Nat, h: n <= m): m <= m { h }").unwrap();
        let d = only_decl(&f);
        let TyKind::OfExpr(e) = &d.params[2].ty.kind else {
            panic!("expected a decoded type, got {:?}", d.params[2].ty.kind)
        };
        assert_eq!(as_call(&e.kind).0, "<=");
        let f = parse_file("theorem t(n: Nat): (m: Nat) -> n <= m -> n <= m { ?p }").unwrap();
        assert!(matches!(only_decl(&f).result.kind, TyKind::Fn { .. }));
    }

    #[test]
    fn a_type_argument_list_survives_the_two_char_token() {
        // `<=` is lexed greedily, and generics must not notice: a declaration
        // with type parameters, an applied inductive, and a `<=` all in one
        // file (issues/comparison-operators.md, the lexer worry).
        let f = parse_file(
            "record Boxed<A> { v: A }
             fn unbox<A>(b: Boxed<A>) -> A { b.v }
             theorem t(n: Nat, m: Nat, h: n <= m): n <= m { h }",
        )
        .unwrap();
        assert_eq!(f.items.len(), 3);
    }

    // `.f` is no longer desugared here: the parser emits `Dot` and the
    // elaborator decides between a record projection and the method call,
    // since only it knows the receiver's type (docs/language/surface-records.md §4.2).
    // What that desugaring *becomes* is pinned in the elaborator's tests; what
    // is pinned here is that the shape survives parsing intact.
    #[test]
    fn method_call_parses_as_dot_with_args() {
        let k = body("add_succ(n, k).sym()");
        let ExprKind::Dot { recv, name, args, .. } = &k else { panic!("expected a Dot, got {k:?}") };
        assert_eq!(name, "sym");
        assert_eq!(args.as_ref().expect("`()` means a call").len(), 0);
        assert_eq!(as_call(&recv.kind).0, "add_succ");
    }

    #[test]
    fn method_call_parses_explicit_type_arguments() {
        let k = body("x.fold<Nat, List<Nat>>(success, failure)");
        let ExprKind::Dot { recv, name, tyargs, args, .. } = &k else {
            panic!("expected a Dot, got {k:?}")
        };
        assert!(matches!(&recv.kind, ExprKind::Var(v) if v == "x"));
        assert_eq!(name, "fold");
        assert_eq!(tyargs.len(), 2);
        assert_eq!(args.as_ref().expect("a call").len(), 2);
    }

    #[test]
    fn tight_less_than_after_a_member_still_falls_back_to_comparison() {
        let k = body("x.value<limit");
        let (name, args, _) = as_call(&k);
        assert_eq!(name, "<");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0].kind, ExprKind::Dot { name, tyargs, .. }
            if name == "value" && tyargs.is_empty()));
    }

    #[test]
    fn field_access_parses_without_parens() {
        // `m.op` — a bare projection, which used to be a parse error.
        let k = body("m.op");
        let ExprKind::Dot { recv, name, args, .. } = &k else { panic!("expected a Dot, got {k:?}") };
        assert_eq!(name, "op");
        assert!(args.is_none(), "no `()` means no call");
        assert!(matches!(&recv.kind, ExprKind::Var(v) if v == "m"));
    }

    #[test]
    fn dot_chains_left_associatively() {
        // `m.a.b(c)` — `(m.a).b(c)`, so the receiver of `b` is `m.a`.
        let k = body("m.a.b(c)");
        let ExprKind::Dot { recv, name, args, .. } = &k else { panic!("expected a Dot, got {k:?}") };
        assert_eq!(name, "b");
        assert_eq!(args.as_ref().expect("a call").len(), 1);
        let ExprKind::Dot { name: inner, .. } = &recv.kind else { panic!("expected a Dot") };
        assert_eq!(inner, "a");
    }

    // `s with { f = v }` (issues/record-update-syntax.md): a postfix form on
    // any expression, chaining left to right; `with` is a word only before
    // `{`, and an update writes at least one field.
    #[test]
    fn record_update_parses_as_postfix() {
        let src = "fn f(s: P) -> P { s.inner with { x = 1, y = s.y } with { z = 2 } }";
        let d = parse_file(src).unwrap().items.remove(0).into_decl();
        let ExprKind::RecordUpdate { base, fields } = &d.body.result.kind else {
            panic!("expected a record update, got {:?}", d.body.result.kind)
        };
        assert_eq!(fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["z"]);
        let ExprKind::RecordUpdate { base, fields } = &base.kind else { panic!("updates chain left to right") };
        assert_eq!(fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["x", "y"]);
        assert!(matches!(base.kind, ExprKind::Dot { .. }));
        assert!(parse_file("fn f(with: Nat) -> Nat { with }").is_ok(), "`with` is still a name");
        assert!(parse_file("fn f(s: P) -> P { s with { } }").is_err());
        assert!(parse_file("fn f(s: P) -> P { s with { x: 1 } }").is_err(), "an update writes `=`");
    }

    #[test]
    fn record_literal_parses_with_free_field_order() {
        let src = "record P { x: Nat, y: Nat }
                   fn f() -> P { P { y: 1, x: 0 } }";
        let mut items = parse_file(src).unwrap().items;
        let d = items.remove(1).into_decl();
        let ExprKind::RecordLit { name, tyargs, fields } = &d.body.result.kind else {
            panic!("expected a record literal, got {:?}", d.body.result.kind)
        };
        assert_eq!(name, "P");
        assert!(tyargs.is_empty());
        // Written order is preserved here; the permutation into declaration
        // order happens in the elaborator, which is what knows the order.
        assert_eq!(fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["y", "x"]);
    }

    // The `match m { … }` ambiguity (docs/language/surface-records.md §6.1): a `{`
    // after the scrutinee closes the `match`, and parenthesising is the escape
    // hatch for a literal that really is the scrutinee.
    #[test]
    fn a_match_scrutinee_does_not_swallow_the_arm_block() {
        let src = "record P { x: Nat }
                   inductive B { T, F }
                   fn f(b: B, m: P) -> Nat { match b { T => m.x, F => 0 } }";
        parse_file(src).expect("the arm block is not a record literal");
    }

    #[test]
    fn a_parenthesised_literal_may_be_a_scrutinee() {
        let src = "record P { x: Nat }
                   inductive B { T, F }
                   fn f(b: B) -> Nat { match (P { x: 1 }).x { Zero => 0, Succ(k) => k } }";
        parse_file(src).expect("parens lift the restriction");
    }

    #[test]
    fn a_record_field_must_be_named() {
        let msg = parse_file("record P { Nat }").unwrap_err().msg;
        assert!(msg.contains("record field needs a name"), "{msg}");
    }

    #[test]
    fn let_destructuring_parses() {
        let src = "record P { x: Nat, y: Nat }
                   fn f(p: P) -> Nat { let { x, y } = p; x }";
        let mut items = parse_file(src).unwrap().items;
        let d = items.remove(1).into_decl();
        let Stmt::LetRecord { fields, .. } = &d.body.stmts[0] else {
            panic!("expected a destructuring let")
        };
        assert_eq!(fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["x", "y"]);
    }

    #[test]
    fn calc_single_step_is_the_bare_proof() {
        // `calc { a = b := p }` ⇒ p.
        let k = body("calc { a = b := p }");
        assert!(matches!(&k, ExprKind::Var(v) if v == "p"));
    }

    /// `calc { a = b := p1, = c := p2 }` ⇒ `trans(p1, p2, a := a, b := b,
    /// c := c)`. The assertion that this used to be `@trans(a, b, c, p1, p2)`
    /// was changed **deliberately** when named arguments landed: `@` made the
    /// desugaring depend on how many implicits `trans` has and in what order,
    /// which is a property of a library declaration rather than of the
    /// grammar, and is the fragility `issues/named-arguments.md` records.
    #[test]
    fn calc_multi_step_pins_the_endpoints_by_name() {
        let k = body("calc { a = b := p1, = c := p2 }");
        let (name, args, explicit) = as_call(&k);
        assert_eq!(name, "trans");
        assert!(!explicit, "the endpoints are named, so `@` is not needed");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0].kind, ExprKind::Var(v) if v == "p1"));
        assert!(matches!(&args[1].kind, ExprKind::Var(v) if v == "p2"));
        let ExprKind::App { named, .. } = &k else { panic!("expected a call") };
        let spelled: Vec<(&str, &str)> = named
            .iter()
            .map(|n| {
                let ExprKind::Var(v) = &n.expr.kind else { panic!("expected a var") };
                (n.name.as_str(), v.as_str())
            })
            .collect();
        assert_eq!(spelled, vec![("a", "a"), ("b", "b"), ("c", "c")]);
    }

    /// `calc { a=b:=p1, =c:=p2, =d:=p3 }` ⇒
    /// `trans(p1, trans(p2, p3, a:=b, b:=c, c:=d), a:=a, b:=b, c:=d)`.
    /// The right endpoint `d` is shared by every level, which is what the
    /// right fold is for; it is now read off the `c` **name** rather than off
    /// argument slot 2.
    #[test]
    fn calc_three_steps_fold_right() {
        let k = body("calc { a = b := p1, = c := p2, = d := p3 }");
        assert_eq!(calc_endpoint(&k, "c"), "d", "shared right endpoint");
        assert_eq!(calc_endpoint(&k, "a"), "a");
        let (_, args, _) = as_call(&k);
        let (inner, _, iexpl) = as_call(&args[1].kind);
        assert_eq!(inner, "trans");
        assert!(!iexpl);
        assert_eq!(calc_endpoint(&args[1].kind, "a"), "b");
        assert_eq!(calc_endpoint(&args[1].kind, "c"), "d");
    }

    /// The relation symbol an order calc passes as argument `i`.
    fn calc_relation_arg(args: &[Expr], i: usize) -> &str {
        let ExprKind::OpSymbol { symbol, .. } = &args[i].kind else {
            panic!("expected a relation symbol, got {:?}", args[i].kind)
        };
        symbol.as_str()
    }

    /// Two different relations meet at a `Trans` instance named by the pair
    /// and the stronger result; the same relation keeps `Transitive`.
    /// `calc { a <= b := p1, < c := p2, < d := p3 }` ⇒
    /// `relation_trans(<=, <, <, a, b, d, p1, relation_step(<, b, c, d, p2,
    /// relation_exact(<, c, d, p3)))`.
    #[test]
    fn calc_order_steps_compose_by_pair() {
        let k = body("calc { a <= b := p1, < c := p2, < d := p3 }");
        let (head, args, _) = as_call(&k);
        assert_eq!(head, "relation_props::relation_trans");
        assert_eq!(
            [0, 1, 2].map(|i| calc_relation_arg(args, i)),
            ["<=", "<", "<"],
            "the pair and the stronger result",
        );
        let ends: Vec<_> = args[3..6]
            .iter()
            .map(|e| match &e.kind {
                ExprKind::Var(v) => v.as_str(),
                other => panic!("expected an endpoint, got {other:?}"),
            })
            .collect();
        assert_eq!(ends, ["a", "b", "d"]);
        let (inner, iargs, _) = as_call(&args[7].kind);
        assert_eq!(inner, "relation_props::relation_step");
        assert_eq!(calc_relation_arg(iargs, 0), "<");
        let (last, _, _) = as_call(&iargs[5].kind);
        assert_eq!(last, "relation_props::relation_exact");
    }

    /// An `=` step beside a relation transports rather than asking for an
    /// instance, on either side; a single order step still checks its
    /// endpoints.
    #[test]
    fn calc_eq_steps_transport_in_an_order_chain() {
        let k = body("calc { a = b := p1, <= c := p2, = d := p3 }");
        let (head, args, _) = as_call(&k);
        assert_eq!(head, "relation_props::relation_eq_l");
        assert_eq!(calc_relation_arg(args, 0), "<=");
        let (inner, iargs, _) = as_call(&args[5].kind);
        assert_eq!(inner, "relation_props::relation_eq_r");
        assert_eq!(calc_relation_arg(iargs, 0), "<=");
        // The trailing `=` proof is passed bare, checked at `c = d`.
        assert!(matches!(&iargs[5].kind, ExprKind::Var(v) if v == "p3"));
        let single = body("calc { a < b := p }");
        let (one, oargs, _) = as_call(&single);
        assert_eq!(one, "relation_props::relation_exact");
        assert_eq!(calc_relation_arg(oargs, 0), "<");
    }

    #[test]
    fn calc_step_needs_a_relation() {
        let msg = parse_file("fn f(n: Nat) -> Nat { calc { a <= b := p, + c := q } }")
            .unwrap_err()
            .msg;
        assert!(msg.contains("calc step relation"), "{msg}");
    }

    /// The variable a `calc`-emitted `trans` pins at the named endpoint `which`.
    fn calc_endpoint<'a>(k: &'a ExprKind, which: &str) -> &'a str {
        let ExprKind::App { named, .. } = k else { panic!("expected a call, got {k:?}") };
        let na = named.iter().find(|n| n.name == which).expect("endpoint");
        let ExprKind::Var(v) = &na.expr.kind else { panic!("expected a var") };
        v.as_str()
    }

    #[test]
    fn single_eq_is_the_equality_type_former() {
        // `a = b` in type position is the identity type (not an expression
        // operator — the elaborator never sees `=` as a Call).
        let f = parse_file("theorem t(a: Nat, b: Nat): a = b { refl }").unwrap();
        assert!(matches!(only_decl(&f).result.kind, crate::ast::TyKind::Eq(..)));
    }

    #[test]
    fn double_eq_is_rejected_with_a_hint() {
        // `==` is lexed but not grammatical; equality is `=`. The parser
        // rejects it with a targeted message (C/Rust muscle memory).
        let err = parse_file("theorem t(a: Nat, b: Nat): a == b { refl }").unwrap_err();
        assert!(err.msg.contains("=="), "hint should mention `==`: {}", err.msg);
        assert!(err.msg.contains('='), "hint should point at `=`: {}", err.msg);
    }

    // -- goal holes (issues/goal-holes.md) ----------------------------------

    fn decl_of(src: &str) -> Decl {
        parse_file(src).unwrap().items.remove(0).into_decl()
    }

    #[test]
    fn named_and_anonymous_holes_parse() {
        // Adjacency decides: `?p` is named, `? ` is anonymous. Both are atoms,
        // so they nest inside calls like any other expression.
        let k = body("f(?p, ?)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Hole(Some(n)) if n == "p"), "{:?}", args[0]);
        assert!(matches!(args[1].kind, ExprKind::Hole(None)), "{:?}", args[1]);
    }

    #[test]
    fn on_discharges_by_name_and_by_statement() {
        let d = decl_of(
            "theorem t(a: Nat, b: Nat): a = b {
                 ?first
                 on ?first := p;
                 on ?bound.1 := q;
                 on _: a = b := r;
             }",
        );
        assert_eq!(d.body.ons.len(), 3);
        match &d.body.ons[0].target {
            OnTarget::Name(n) => assert_eq!(n, "first"),
            other => panic!("expected a name target, got {other:?}"),
        }
        // The checker's ordinal suffix is part of the name, not a method call.
        match &d.body.ons[1].target {
            OnTarget::Name(n) => assert_eq!(n, "bound.1"),
            other => panic!("expected a name target, got {other:?}"),
        }
        assert!(matches!(d.body.ons[2].target, OnTarget::Stmt(_)));
    }

    /// `by t` is the tactic form only before a name (Rule 1), so a local
    /// called `by` still reads as itself.
    #[test]
    fn by_runs_a_tactic_only_before_a_name() {
        let k = body("by assumption");
        let (head, args, _) = as_call(&k);
        assert_eq!(head, BY_TACTIC);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "assumption"));
        let k = body("by tactic::spin(3)");
        let (head, args, _) = as_call(&k);
        assert_eq!(head, BY_TACTIC);
        assert!(matches!(&args[0].kind, ExprKind::App { .. }));
        let k = body("by(1)");
        let (head, _, _) = as_call(&k);
        assert_eq!(head, "by");
        assert!(parse_file("fn f(by: Nat) -> Nat { by + 1 }").is_ok());
    }

    #[test]
    fn split_all_then_all_goals_is_one_checking_form() {
        let d = decl_of(
            "theorem t(a: Bool): a = a {
                 split_all;
                 all_goals { refl }
             }",
        );
        let Some((head, args, false)) = d.body.result.as_named() else {
            panic!("goal combinator call")
        };
        assert_eq!(head, SPLIT_ALL_GOALS);
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0].kind, ExprKind::Block(_)));
    }

    #[test]
    fn split_all_requires_an_all_goals_consumer() {
        let error = parse_file("theorem t(a: Bool): a = a { split_all; refl }").unwrap_err();
        assert!(error.msg.contains("all_goals"), "{}", error.msg);
    }

    #[test]
    fn let_binds_with_and_without_an_annotation() {
        let d = decl_of(
            "fn f(n: Nat) -> Nat {
                 let a = n;
                 let p: (n = n) = refl;
                 let q: Nat = 3;
                 let g: Nat -> Nat = fun x => x;
                 let r: (Nat) = 3;
                 a
             }",
        );
        assert_eq!(d.body.stmts.len(), 5);
        let Stmt::Let { name, ty, .. } = &d.body.stmts[0] else { panic!("plain let") };
        assert_eq!(name, "a");
        assert!(ty.is_none());
        // `let p: (n = n) = refl;` — the annotation is read with the
        // comparison rung suppressed, so an equation is parenthesised and the
        // binder `=` is the parser's (docs/language/let-and-blocks-design.md §3).
        let Stmt::Let { name, ty, expr, .. } = &d.body.stmts[1] else { panic!("plain let") };
        assert_eq!(name, "p");
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Eq(..))));
        assert!(matches!(expr.kind, ExprKind::Refl));
        // The three shapes that could never be written before: a bare type
        // name, a function type, and a parenthesised type.
        let Stmt::Let { name, ty, .. } = &d.body.stmts[2] else { panic!("plain let") };
        assert_eq!(name, "q");
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Nat)));
        let Stmt::Let { name, ty, .. } = &d.body.stmts[3] else { panic!("plain let") };
        assert_eq!(name, "g");
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Fn { .. })));
        let Stmt::Let { name, ty, .. } = &d.body.stmts[4] else { panic!("plain let") };
        assert_eq!(name, "r");
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Nat)));
    }

    /// The negative control for the annotation's `no_eq`: it is scoped to the
    /// annotation, so a `let`'s *value* may still be an equation
    /// (docs/language/let-and-blocks-design.md §8 item 4(b) — the `surface-universe`
    /// counterexample that killed the last-`=`-scan option).
    #[test]
    fn a_let_value_may_still_be_an_equation() {
        let d = decl_of("fn f(n: Nat) -> Nat { let x: Type<0> = a = b; n }");
        let Stmt::Let { name, ty, expr, .. } = &d.body.stmts[0] else { panic!("plain let") };
        assert_eq!(name, "x");
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Univ { level: 0 })));
        assert!(matches!(expr.kind, ExprKind::Eq(..)), "the value is the proposition");
    }

    /// A relation other than `=` needs no parenthesis in an annotation: only
    /// `=` collides with the binder, so `<=`, `<`, `≈` and `≠` read as the
    /// type's own (issues/annotated-let-relation-needs-parentheses.md), in a
    /// `let`, a `have` and a `def` alike. The binder `=` still ends the
    /// annotation, so a bare equation keeps its old split and a chain inside
    /// the annotation is still one.
    #[test]
    fn an_annotation_takes_a_relation_other_than_equality_bare() {
        for (src, sym) in [
            ("fn f(a: Nat, b: Nat, h: a <= b) -> Nat { let k: a <= b = h; 0 }", "<="),
            ("fn f(a: Nat, b: Nat, h: a < b) -> Nat { let k: a < b = h; 0 }", "<"),
            ("fn f(a: Nat, b: Nat, h: a <= b) -> Nat { have k: a <= b = h; 0 }", "<="),
            ("fn f(a: Nat, b: Nat, h: a <= b) -> Nat { let k: a <= b ∧ b <= b = h; 0 }", "And"),
        ] {
            let d = decl_of(src);
            let Stmt::Let { name, ty, expr, .. } = &d.body.stmts[0] else { panic!("{src}: a let") };
            assert_eq!(name, "k", "{src}");
            assert!(matches!(expr.kind, ExprKind::Var(ref v) if v == "h"), "{src}: the value is `h`");
            let shown = format!("{:?}", ty.as_ref().expect("annotated"));
            assert!(shown.contains(sym), "{src}: the annotation is the relation, got {shown}");
        }
        let d = decl_of("fn f(a: Nat, b: Nat, h: a ≠ b) -> Nat { let k: a ≠ b = h; 0 }");
        let Stmt::Let { ty, expr, .. } = &d.body.stmts[0] else { panic!("a let") };
        assert!(ty.is_some() && matches!(expr.kind, ExprKind::Var(ref v) if v == "h"));
        assert!(parse_file("def k: 1 <= 2 = p;").is_ok());
        // Negative controls: the binder `=` still ends the annotation, and a
        // second relation is still a chain.
        let d = decl_of("fn f(n: Nat) -> Nat { let x: Type<0> = a <= b; n }");
        let Stmt::Let { ty, expr, .. } = &d.body.stmts[0] else { panic!("a let") };
        assert!(matches!(ty.as_ref().map(|t| &t.kind), Some(TyKind::Univ { level: 0 })));
        assert!(!matches!(expr.kind, ExprKind::Var(_)), "the value is the relation");
        let e = parse_file("fn f(n: Nat) -> Nat { let k: a <= b <= c = h; n }").expect_err("a chain");
        assert!(e.msg.contains("comparisons do not chain"), "{}", e.msg);
    }

    /// The parenthesis escape hatch `no_eq`'s doc comment promised and did not
    /// have: with it, the `CHAIN` message's advice is true
    /// (docs/language/let-and-blocks-design.md §1.1(3)).
    #[test]
    fn a_parenthesis_reopens_the_comparison_rung() {
        assert!(parse_file("theorem t(): a = (b = c) { refl }").is_ok());
        assert!(parse_file("fn f(n: Nat) -> Nat { calc { (a = b) = c := p } }").is_ok());
    }

    /// A trailing `=` after a completed comparison is now always a chain: the
    /// annotation position no longer needs the exemption
    /// (docs/language/let-and-blocks-design.md §3.1).
    #[test]
    fn comparisons_still_do_not_chain() {
        for src in [
            "fn f(n: Nat) -> Nat { a = b = c }",
            "fn f(n: Nat) -> Nat { a <= b = c }",
            "fn f(n: Nat) -> Nat { a <= b <= c }",
        ] {
            let e = parse_file(src).expect_err("a chain has no reading");
            assert!(e.msg.contains("comparisons do not chain"), "{}: {}", src, e.msg);
        }
    }

    /// The block expression's disambiguation is **positional**
    /// (docs/language/let-and-blocks-design.md §4.1): a prefix `{` is a block, a
    /// postfix `{` on a name head is still a record literal, and a `{` where a
    /// statement is expected is still a declaration body or an arm list. Three
    /// collision checks, not one.
    #[test]
    fn a_prefix_brace_is_a_block_and_a_postfix_one_is_a_literal() {
        // Prefix, in an arm — the shape issues/match-arm-blocks.md was about.
        let d = decl_of(
            "fn f(n: Nat) -> Nat { match n { Zero => { let y = n; y }, Succ(k) => k } }",
        );
        let ExprKind::Match { arms, .. } = &d.body.result.kind else { panic!("match") };
        let ExprKind::Block(b) = &arms[0].body.kind else {
            panic!("expected a block, got {:?}", arms[0].body.kind)
        };
        assert_eq!(b.stmts.len(), 1);
        assert!(b.ons.is_empty());
        // Postfix on a name head, in the same position: still a literal.
        let d = decl_of("fn f(n: Nat) -> D { match n { Zero => D { x: 1 } } }");
        let ExprKind::Match { arms, .. } = &d.body.result.kind else { panic!("match") };
        assert!(matches!(arms[0].body.kind, ExprKind::RecordLit { .. }));
        // A block *as* a scrutinee is unambiguous: it consumes its own braces.
        let d = decl_of("fn f(n: Nat) -> Nat { match { let y = n; y } { Zero => 0 } }");
        let ExprKind::Match { scrut, .. } = &d.body.result.kind else { panic!("match") };
        assert!(matches!(scrut.kind, ExprKind::Block(_)));
        // A declaration body is still reached by `block()`, not through `atom`.
        let d = decl_of("fn f(n: Nat) -> Nat { let y = n; y }");
        assert_eq!(d.body.stmts.len(), 1);
        assert!(matches!(d.body.result.kind, ExprKind::Var(_)));
    }

    /// A block expression declines `on` discharges (§4.3), and its `let`s all
    /// precede the result (§4.5). The empty form is no longer refused: `{}`
    /// parses, with one synthetic `AutoRefl` result
    /// (issues/auto-refl-empty-block.md). A block that has *statements* and no
    /// result still is refused — `{}` is the whole trigger.
    #[test]
    fn a_block_expression_declines_on_and_a_missing_result() {
        let e = parse_file("theorem t(n: Nat): n = n { { ?g on ?g := refl; } }")
            .expect_err("an `on` inside a block expression");
        assert!(e.msg.contains("cannot discharge goals"), "{}", e.msg);
        let d = decl_of("fn f(n: Nat) -> Nat { { } }");
        let ExprKind::Block(b) = &d.body.result.kind else { panic!("block") };
        assert!(b.stmts.is_empty() && b.ons.is_empty());
        assert!(matches!(b.result.kind, ExprKind::AutoRefl), "an empty block is one `AutoRefl`");
        assert!(parse_file("fn f(n: Nat) -> Nat { { let y = n; } }").is_err(), "no result");
        assert!(parse_file("fn f(n: Nat) -> Nat { { n let y = n; } }").is_err(), "a trailing let");
    }

    #[test]
    fn statements_need_semicolons() {
        assert!(parse_file("fn f(n: Nat) -> Nat { let a = n a }").is_err());
        assert!(parse_file("theorem t(n: Nat): n = n { ?p on ?p := refl }").is_err());
    }

    #[test]
    fn on_before_the_result_expression_is_rejected() {
        let err = parse_file("theorem t(n: Nat): n = n { on ?p := refl; ?p }").unwrap_err();
        assert!(err.msg.contains("result expression"), "{}", err.msg);
    }

    #[test]
    fn on_and_let_are_still_usable_as_names() {
        // Contextual keywords: an expression is never continued by a bare
        // identifier, so a statement head is unambiguous and these still parse.
        let k = body("add(on, let)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "on"));
        assert!(matches!(&args[1].kind, ExprKind::Var(n) if n == "let"));
    }

    // -- the quotation slice (docs/metaprogramming/in-language-map-design.md §3) ------------

    #[test]
    fn meta_fn_with_modal_signature() {
        let f = parse_file(
            "meta fn map_code(g: Ctx, a: TyCode(g), f: Code(g |- $a -> Nat)) \
             -> Code(g |- Nat) { code { 0 } }",
        )
        .unwrap();
        let d = only_decl(&f);
        assert!(d.is_meta);
        assert!(matches!(d.params[0].ty.kind, TyKind::Ctx));
        assert!(matches!(&d.params[1].ty.kind, TyKind::TyCode { ctx } if ctx == "g"));
        let TyKind::Code { ctx, ty } = &d.params[2].ty.kind else {
            panic!("expected a Code type, got {:?}", d.params[2].ty.kind)
        };
        assert_eq!(ctx, "g");
        let TyKind::Fn { dom, .. } = &ty.kind else { panic!("expected `$a -> Nat`") };
        assert!(matches!(&dom.kind, TyKind::Splice { name } if name == "a"));
        assert!(matches!(&d.result.kind, TyKind::Code { .. }));
        assert!(matches!(&d.body.result.kind, ExprKind::Quote(_)));
    }

    /// The registration clause (docs/metaprogramming/meta-def-registration-design.md §2.1).
    /// The parser only shapes the path; whether `vec.map` names a slot is the
    /// elaborator's question, where the vocabulary can be listed.
    #[test]
    fn meta_fn_declares_its_slot() {
        let f =
            parse_file("meta fn map_code(g: Ctx) for vec.map -> Code(g |- Nat) { code { 0 } }")
                .unwrap();
        let d = only_decl(&f);
        let s = d.elaborates.as_ref().expect("a `for` clause");
        assert_eq!((s.family.as_str(), s.name.as_str()), ("vec", "map"));
        // …and a `meta fn` without one parses exactly as before.
        let g = parse_file("meta fn m(g: Ctx) -> Code(g |- Nat) { code { 0 } }").unwrap();
        assert!(only_decl(&g).elaborates.is_none());
    }

    #[test]
    fn a_for_clause_marks_a_meta_fn_only() {
        let err = parse_file("fn f(n: Nat) for vec.map -> Nat { n }").unwrap_err();
        assert!(err.msg.contains("meta fn"), "{}", err.msg);
    }

    #[test]
    fn meta_marks_a_fn_only() {
        let err = parse_file("meta theorem t(): Nat { 0 }").unwrap_err();
        assert!(err.msg.contains("meta"), "{}", err.msg);
    }

    #[test]
    fn quote_splices_and_let_code() {
        // `$x` and `${e}` are one node; `let code` is its own statement.
        let d = parse_file(
            "meta fn f(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) { \
             let code y = x; code { add($y, ${x}) } }",
        )
        .unwrap()
        .items
        .remove(0)
        .into_decl();
        assert!(matches!(&d.body.stmts[0], Stmt::LetCode { name, .. } if name == "y"));
        let ExprKind::Quote(payload) = &d.body.result.kind else { panic!("expected a quote") };
        let (_, args, _) = as_call(&payload.kind);
        assert!(matches!(&args[0].kind, ExprKind::Splice(_)));
        assert!(matches!(&args[1].kind, ExprKind::Splice(_)));
    }

    // -- the equation binder and `split` (docs/language/matching/match-equation-split-design.md)

    /// §3.1: the `h :` prefix is exact on two tokens, and it steals nothing.
    #[test]
    fn a_match_takes_an_equation_binder() {
        let d = decl_of("fn f(n: Nat) -> Nat { match h : n { Zero => 0, Succ(k) => k } }");
        let ExprKind::Match { eqbind, scrut, motive, .. } = &d.body.result.kind else {
            panic!("match")
        };
        assert_eq!(eqbind.as_deref(), Some("h"));
        assert!(matches!(&scrut.kind, ExprKind::Var(n) if n == "n"));
        assert!(motive.is_none(), "the binder is a prefix, the motive a suffix");
        // …and they compose.
        let d = decl_of(
            "fn f(n: Nat) -> Nat { match h : n as \u{3bb} z => Nat { Zero => 0, Succ(k) => k } }",
        );
        let ExprKind::Match { eqbind, motive, .. } = &d.body.result.kind else { panic!("match") };
        assert_eq!(eqbind.as_deref(), Some("h"));
        assert!(motive.is_some());
    }

    /// The collision checks §3.1 claims, done rather than asserted: a
    /// qualified scrutinee (`::` is its own token) and an ordinary one.
    #[test]
    fn the_equation_binder_steals_no_scrutinee() {
        let d = decl_of("fn f(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => k } }");
        let ExprKind::Match { eqbind, .. } = &d.body.result.kind else { panic!("match") };
        assert!(eqbind.is_none());
        assert!(parse_file(
            "fn f(n: Nat) -> Nat { match Mod::val { Zero => 0, Succ(k) => k } }"
        )
        .is_ok());
    }

    /// §5/§6: a `split`-terminated block is desugared here, onto the very node
    /// a hand-written `match` builds. The `on Ctor` heads become arms, so
    /// `Block::ons` keeps only real goal discharges.
    #[test]
    fn a_split_block_desugars_to_a_match() {
        let d = decl_of(
            "fn f(m: Nat, n: Nat) -> Nat { split m; on Zero := n; on Succ(k) := n; }",
        );
        assert!(d.body.stmts.is_empty(), "a `split` is not left in the statement list");
        assert!(d.body.ons.is_empty(), "its arms are arms, not discharges");
        let ExprKind::Match { arms, eqbind, motive, .. } = &d.body.result.kind else {
            panic!("expected a Match, got {:?}", d.body.result.kind)
        };
        assert!(eqbind.is_none() && motive.is_none());
        assert_eq!(arms.len(), 2);
        assert_eq!(arms[0].ctor, "Zero");
        assert_eq!(arms[1].binders.iter().map(|p| p.name()).collect::<Vec<_>>(), ["k"]);
        // A goal discharge in the same block stays a discharge, in any order.
        let d = decl_of(
            "fn f(m: Nat) -> Nat { split m; on ?g := 0; on Zero := ?g; on Succ(k) := k; }",
        );
        assert_eq!(d.body.ons.len(), 1);
        let ExprKind::Match { arms, .. } = &d.body.result.kind else { panic!("match") };
        assert_eq!(arms.len(), 2);
        // `split h : e;` — §7, the same field.
        let d = decl_of("fn f(m: Nat) -> Nat { split h : m; on Zero := 0; on Succ(k) := k; }");
        let ExprKind::Match { eqbind, .. } = &d.body.result.kind else { panic!("match") };
        assert_eq!(eqbind.as_deref(), Some("h"));
    }

    /// The grammar's negative controls (§8). Each is a rule the block form
    /// gains, so each gets a message rather than a fall-through.
    #[test]
    fn the_split_grammar_rejects_what_it_says_it_does() {
        for (src, want) in [
            (
                "fn f(m: Nat) -> Nat { split m; let x = 1; on Zero := 0; on Succ(k) := k; }",
                "last statement",
            ),
            ("fn f(m: Nat) -> Nat { split m; }", "at least one"),
            ("fn f(m: Nat) -> Nat { m on Zero := 0; }", "has no `split`"),
            ("fn f(n: Nat) -> Nat { let split = n; split }", "case-split statement keyword"),
            ("fn f(m: Nat) -> Nat { split m on Zero := 0; }", "`;` to end the `split`"),
        ] {
            let e = parse_file(src).expect_err(src);
            assert!(e.msg.contains(want), "{src}\n  got: {}", e.msg);
        }
    }

    #[test]
    fn code_is_still_an_ordinary_name() {
        // The `{` lookahead is what keeps `code` usable as a variable, and
        // `Code`/`Ctx` stay ordinary type names when their follow set says so.
        let k = body("add(code, 1)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "code"));
        // `Code<Nat>` — a user inductive named `Code` applied to arguments
        // still parses as a Named type (no `(` after the name).
        let f = parse_file("fn f(x: Code<Nat>) -> Nat { 0 }").unwrap();
        assert!(matches!(&only_decl(&f).params[0].ty.kind, TyKind::Named { name, .. } if name == "Code"));
    }

    /// **Rule 1** at the two forms that qualify, on the pattern
    /// `code_is_still_an_ordinary_name` set: the lookahead is what buys the
    /// name back, and the form is untouched because the same token was already
    /// required one line later (docs/language/let-and-blocks-design.md §5.2).
    #[test]
    fn j_and_calc_are_still_ordinary_names() {
        // `j` as an ordinary name at a use — the reported bug
        // (issues/j-binder-parse-trap.md), whose message named an eliminator
        // the user never wrote.
        let f = parse_file("fn f(n: Nat) -> Nat { let j = n; lookup(j, n) }");
        assert!(f.is_ok(), "{:?}", f.err().map(|e| e.msg));
        let k = body("add(j, 1)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "j"));
        // …and the J form is unchanged.
        assert!(parse_file(
            "theorem t(a: Nat, b: Nat, p: a = b): b = a \
             { j(p, \u{3bb} y q => y = a, refl) }"
        )
        .is_ok());
        // `calc` likewise: a name without a `{`, the form with one.
        let k = body("add(calc, 1)");
        let (_, args, _) = as_call(&k);
        assert!(matches!(&args[0].kind, ExprKind::Var(n) if n == "calc"));
        assert!(parse_file("fn f(n: Nat) -> Nat { calc { a = b := p } }").is_ok());
    }

    /// The residue rule 1 leaves (§5.3): `j(x)`, a *local* `j` applied, still
    /// enters the form — loudly, and the message now names the collision.
    #[test]
    fn an_applied_local_j_says_what_collided() {
        let e = parse_file("fn f(n: Nat) -> Nat { let j = n; j(n) }")
            .expect_err("an applied `j` is the eliminator");
        assert!(e.msg.contains("takes exactly three arguments"), "{}", e.msg);
        assert!(e.msg.contains("j-binder-parse-trap"), "{}", e.msg);
    }

    /// **Rule 3**: the four true keywords are rejected *at the binding site*,
    /// each with a message naming the form. One per form across three sites is
    /// the coverage §8 item 16 asks for; the point is that `match`/`fun`/`if`/`Type`
    /// are keywords of the grammar and stay so (§5.4).
    #[test]
    fn a_true_keyword_cannot_be_a_binding_name() {
        for form in ["match", "fun", "if", "Type"] {
            for src in [
                format!("fn f(n: Nat) -> Nat {{ let {form} = n; n }}"),
                format!("fn f(n: Nat) -> Nat {{ (\u{3bb} {form} => n)(n) }}"),
                format!("fn f(n: Nat) -> Nat {{ match n {{ Succ({form}) => 0, Zero => 0 }} }}"),
                format!("fn f({form}: Nat) -> Nat {{ 0 }}"),
            ] {
                let e = parse_file(&src)
                    .err()
                    .unwrap_or_else(|| panic!("`{form}` must not bind: {src}"));
                assert!(e.msg.contains(form), "{src}: {}", e.msg);
                assert!(e.msg.contains("cannot be a binding name"), "{src}: {}", e.msg);
            }
        }
        // The two that were **silent** before rule 3 (§5.1): `refl` and
        // `Type`. `refl` takes rule 2 instead and binds fine.
        assert!(parse_file("fn f(n: Nat) -> Nat { let refl = n; refl }").is_ok());
    }

    #[test]
    fn let_code_needs_a_name() {
        // `let code = e;` binds a plain variable named `code`, unchanged.
        let f = parse_file("fn f(n: Nat) -> Nat { let code = n; code }").unwrap();
        assert!(matches!(&only_decl(&f).body.stmts[0], Stmt::Let { name, .. } if name == "code"));
    }

    /// `match code { … }` on an ordinary variable named `code`
    /// (issues/match-scrutinee-named-code.md). The `{` lookahead buys the name
    /// back everywhere a `{` could be the quote's payload; where the `{`
    /// belongs to the *enclosing* form instead, `no_record_lit` already says
    /// so, and the quotation stands down.
    #[test]
    fn a_scrutinee_named_code_is_an_ordinary_variable() {
        let f = parse_file("fn f(code: Nat) -> Nat { match code { Zero => 0, Succ(k) => k } }")
            .unwrap();
        let ExprKind::Match { scrut, arms, .. } = &only_decl(&f).body.result.kind else {
            panic!("expected a match")
        };
        assert!(matches!(&scrut.kind, ExprKind::Var(n) if n == "code"), "the scrutinee is `code`");
        assert_eq!(arms.len(), 2);
        // The same brace in the same position, one form up: a motive's body
        // and the arm block are both the enclosing form's.
        parse_file("fn f(code: Nat) -> Nat { match code as λ z => Nat { Zero => 0, Succ(k) => k } }")
            .unwrap();
    }

    /// …and the quotation is untouched wherever the `{` really is its payload:
    /// a `let`, an argument, a block's result. These are the positions the
    /// flag is lifted in, so this is the control that says the fix took only
    /// the scrutinee.
    #[test]
    fn a_quotation_still_parses_where_the_brace_is_its_own() {
        for src in [
            "meta fn f(g: Ctx) -> Code(g |- Nat) { code { 0 } }",
            "meta fn f(g: Ctx) -> Code(g |- Nat) { let q = code { 0 }; q }",
            "meta fn f(g: Ctx, h: Code(g |- Nat) -> Code(g |- Nat)) -> Code(g |- Nat) \
             { h(code { 0 }) }",
        ] {
            parse_file(src).unwrap_or_else(|e| panic!("{src}\n  got: {}", e.msg));
        }
        // In scrutinee position the escape hatch is the one `no_record_lit`
        // documents for record literals, and for the same reason: a bracket
        // lifts the restriction.
        let f = parse_file(
            "meta fn f(g: Ctx, c: Code(g |- Nat)) -> Nat \
             { match (code { 0 }) { _ => 0 } }",
        )
        .unwrap();
        let ExprKind::Match { scrut, .. } = &only_decl(&f).body.result.kind else {
            panic!("expected a match")
        };
        assert!(matches!(&scrut.kind, ExprKind::Quote { .. }), "parens restore the quotation");
    }

    /// The negative control the fix must not disturb: `match code e as T { … }`
    /// is the intensional form, and it was never the ambiguous shape — its own
    /// guard reads `match code` followed by something *other* than the arm
    /// block, which is why the variable case reached the quotation at all.
    #[test]
    fn the_intensional_match_is_untouched() {
        parse_file(
            "meta fn f(g: Ctx, c: Code(g |- Nat)) -> Nat \
             { match code c as Nat { _ => 0 } }",
        )
        .unwrap();
        let e = parse_file(
            "meta fn f(g: Ctx, c: Code(g |- Nat)) -> Nat { match code c { _ => 0 } }",
        )
        .unwrap_err();
        assert!(e.msg.contains("needs its result type"), "{}", e.msg);
    }

    #[test]
    fn turnstile_is_required_in_code_types() {
        let err =
            parse_file("meta fn f(g: Ctx, x: Code(g, Nat)) -> Code(g |- Nat) { code { 0 } }")
                .unwrap_err();
        assert!(err.msg.contains("|-"), "{}", err.msg);
    }

    // -- multi-binder function types ---------------------------------------
    // issues/multi-binder-function-types.md. The sugar is discharged in the
    // parser, so every test here asserts on the *curried chain* — if the
    // desugaring were anything but the hand-written spelling, these would be
    // the wrong assertions to be able to write.

    /// The binder spine of a function type, outermost first: the name and the
    /// domain's leading identifier (enough to tell `Nat` from `Bool`), then
    /// the result type's leading identifier.
    fn head(t: &Ty) -> String {
        match &t.kind {
            TyKind::Named { name, .. } => name.clone(),
            TyKind::Univ { level } => format!("Type<{level}>"),
            TyKind::OfExpr(e) => match &e.kind {
                ExprKind::Var(n) => n.clone(),
                other => format!("{other:?}"),
            },
            other => format!("{other:?}"),
        }
    }

    fn spine(ty: &Ty) -> (Vec<(String, String)>, String) {
        let mut binders = Vec::new();
        let mut cur = ty;
        while let TyKind::Fn { binder: Some(name), dom, cod, .. } = &cur.kind {
            binders.push((name.clone(), head(dom)));
            cur = cod;
        }
        (binders, head(cur))
    }

    /// The type of `g`, the sole parameter of the file's one declaration.
    fn param_ty(src: &str) -> Ty {
        let f = parse_file(src).unwrap();
        only_decl(&f).params[0].ty.clone()
    }

    #[test]
    fn two_binders_in_one_arrow_group_curry() {
        let ty = param_ty("fn f(g: (x: Nat, y: Bool) -> Nat) -> Nat { 0 }");
        let (binders, res) = spine(&ty);
        assert_eq!(
            binders,
            vec![("x".into(), "Nat".into()), ("y".into(), "Bool".into())]
        );
        assert_eq!(res, "Nat");
        // …and the desugaring is the hand-curried spelling, not a lookalike.
        let hand = param_ty("fn f(g: (x: Nat) -> (y: Bool) -> Nat) -> Nat { 0 }");
        assert_eq!(spine(&ty), spine(&hand));
    }

    #[test]
    fn a_run_of_names_shares_one_annotation() {
        let ty = param_ty("fn f(g: (x, y, z: Nat) -> Bool) -> Nat { 0 }");
        let (binders, res) = spine(&ty);
        assert_eq!(
            binders,
            vec![
                ("x".into(), "Nat".into()),
                ("y".into(), "Nat".into()),
                ("z".into(), "Nat".into())
            ]
        );
        assert_eq!(res, "Bool");
    }

    #[test]
    fn runs_and_separate_groups_mix() {
        let ty = param_ty("fn f(g: (x, y: Nat, z: Bool) -> Nat) -> Nat { 0 }");
        let (binders, _) = spine(&ty);
        assert_eq!(
            binders,
            vec![
                ("x".into(), "Nat".into()),
                ("y".into(), "Nat".into()),
                ("z".into(), "Bool".into())
            ]
        );
    }

    /// It is a telescope: `A` is in scope in the next binder's type, which is
    /// automatic once the group curries left to right.
    #[test]
    fn a_later_binder_may_mention_an_earlier_one() {
        let ty = param_ty("fn f(g: (A: Type<0>, x: A) -> A) -> Nat { 0 }");
        let (binders, res) = spine(&ty);
        assert_eq!(
            binders,
            vec![("A".into(), "Type<0>".into()), ("x".into(), "A".into())]
        );
        assert_eq!(res, "A");
    }

    #[test]
    fn implicit_binder_groups_take_the_run_too() {
        let ty = param_ty("fn f(g: {A, B: Type<0>} -> Nat) -> Nat { 0 }");
        let TyKind::Fn { binder, implicit, cod, .. } = &ty.kind else { panic!("{ty:?}") };
        assert_eq!(binder.as_deref(), Some("A"));
        assert!(*implicit);
        assert!(matches!(&cod.kind, TyKind::Fn { implicit: true, .. }));
        assert_eq!(spine(&ty).0.len(), 2);
    }

    #[test]
    fn a_parameter_run_shares_one_annotation() {
        let f = parse_file("fn f(x, y: Nat, z: Bool) -> Nat { 0 }").unwrap();
        let ps = &only_decl(&f).params;
        assert_eq!(ps.len(), 3);
        assert_eq!(ps.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), ["x", "y", "z"]);
        assert!(ps.iter().all(|p| !p.implicit));
        assert_eq!(ps.iter().map(|p| head(&p.ty)).collect::<Vec<_>>(), ["Nat", "Nat", "Bool"]);
    }

    #[test]
    fn an_implicit_parameter_run_stays_implicit() {
        let f = parse_file("theorem t({a, b: Nat}, p: a = b): b = a { refl }").unwrap();
        let ps = &only_decl(&f).params;
        assert_eq!(ps.len(), 3);
        assert!(ps[0].implicit && ps[1].implicit, "both names in the brace are implicit");
        assert!(!ps[2].implicit);
    }

    /// A modifier prefixes ONE name — the property the comma form was chosen
    /// for (Lean's juxtaposition cannot state it) — and it is the name it is
    /// *written on*, inside the run as well as before it
    /// (issues/modifiers-in-shared-binder-runs.md). `self x: Nat, y: Nat` and
    /// `self x, y: Nat` are therefore the same two parameters: the mark
    /// reaches `x` and nothing else, and the annotation is the only thing the
    /// run shares.
    #[test]
    fn a_modifier_prefixes_a_single_name() {
        for src in ["fn r(self x: Nat, y: Nat) -> Nat { x }", "fn r(self x, y: Nat) -> Nat { x }"]
        {
            let f = parse_file(src).unwrap();
            let ps = &only_decl(&f).params;
            assert_eq!(ps.len(), 2, "{src}");
            assert_eq!(ps.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), ["x", "y"]);
            assert!(ps[0].is_self && !ps[1].is_self, "the mark is on `x` alone: {src}");
            assert_eq!(ps.iter().map(|p| head(&p.ty)).collect::<Vec<_>>(), ["Nat", "Nat"]);
        }
        // A run's *later* name may carry the mark just as well: the modifier
        // is read per entry, not once at the head of the group.
        let f = parse_file("fn r(x, self y: Nat) -> Nat { y }").unwrap();
        let ps = &only_decl(&f).params;
        assert!(!ps[0].is_self && ps[1].is_self);
    }

    /// The rule the per-name reading does NOT relax: one `self` per
    /// declaration. The scan has to see the run it is standing in, whose names
    /// are not pushed until the shared annotation is read.
    #[test]
    fn two_selfs_in_one_run_are_still_refused() {
        let e = parse_file("fn r(self x, self y: Nat) -> Nat { x }").unwrap_err();
        assert!(e.msg.contains("at most one `self`"), "{}", e.msg);
        assert!(e.msg.contains("`x` is already it"), "{}", e.msg);
        // …and across groups, which is the case that always worked.
        let e = parse_file("fn r(self x: Nat, self y: Nat) -> Nat { x }").unwrap_err();
        assert!(e.msg.contains("at most one `self`"), "{}", e.msg);
    }

    /// The negative control: names with no annotation are not binders, and the
    /// error says which form was almost written instead of failing at the
    /// comma with `expected )`.
    #[test]
    fn a_binder_group_without_an_annotation_is_named() {
        let e = parse_file("fn f(g: (x, y) -> Nat) -> Nat { 0 }").unwrap_err();
        assert!(e.msg.contains("has no type"), "{}", e.msg);
        assert!(e.msg.contains("(x, y: A)"), "{}", e.msg);
    }

    /// …and in expression position the same group is still not a tuple (there
    /// are none), but the message names the missing arrow rather than
    /// cascading.
    #[test]
    fn a_binder_group_in_expression_position_asks_for_the_arrow() {
        let e = parse_file("fn f(n: Nat) -> Nat { (x, y: Nat) }").unwrap_err();
        assert!(e.msg.contains("->"), "{}", e.msg);
    }

    /// The parenthesis rule is untouched: a leading `(` in type position that
    /// opens an *expression* still does (`(a + b) + c = …`), and a comma
    /// inside a call's argument list is still an argument separator.
    #[test]
    fn ordinary_parenthesised_expressions_still_parse() {
        parse_file("theorem t(a: Nat, b: Nat, c: Nat): (a + b) + c = a + (b + c) { refl }")
            .unwrap();
        parse_file("fn f(a: Nat, b: Nat) -> Nat { g(h(a, b), a) }").unwrap();
    }

    /// **Speculation stays linear** (`issues/type-argument-speculation-cost.md`).
    ///
    /// Two sites speculate on a `<` and each falls back by re-parsing the same
    /// tokens the other way, so once both recover they re-enter each other and
    /// a failing `A<A<A<…` costs 2^depth. It was measured at 4× per two
    /// levels — 7 ms at depth 10, 4.7 s at depth 20 — before
    /// [`Parser::spec_failed`] memoized the failures.
    ///
    /// This is a **cost** test, so it is written the only way a cost test is
    /// worth having: at a depth the exponential could not survive. Depth 200
    /// is 2^200 attempts unmemoized and one attempt per position memoized, so
    /// the assertion is simply that it *terminates* — no timing, no threshold,
    /// nothing machine-dependent. Both spellings are here because the two
    /// sites are separate keys and a memo on one alone still blows up.
    #[test]
    fn deep_failing_speculation_does_not_blow_up() {
        let ty_pos = format!("fn f(h: {}Nat) -> Nat {{ 0 }}", "A<".repeat(200));
        assert!(parse_file(&ty_pos).is_err(), "unterminated type arguments must still fail");
        let expr_pos = format!("fn g() -> Nat {{ {}b }}", "a<".repeat(200));
        assert!(parse_file(&expr_pos).is_err(), "an unterminated `<` chain must still fail");
    }

    /// The **one-directional whitespace rule**
    /// (`docs/language/type-argument-disambiguation.md`): a `<` with a space before it
    /// never opens type arguments, and a tight one is still only *speculated*
    /// as opening them.
    ///
    /// The first case is the point of the whole rule — it is the one thing
    /// speculation provably cannot do, because the inner `<` would otherwise
    /// eat the outer's `>`. The rest are the property that makes the rule
    /// safe: spacing narrows the ambiguity and never decides a meaning, so
    /// everything that parsed before still parses, `a<b` included.
    #[test]
    fn a_spaced_lt_never_opens_type_arguments() {
        // The residue, unparenthesized — this was a parse error until the rule.
        parse_file("fn d(n: Nat, m: Nat, h: Or<n < m, m <= n>) -> Nat { 0 }").unwrap();
        // …and every mixed nesting, which is what rules out "just turn inner
        // speculation off": one argument needs it on, the other needs it off.
        parse_file("fn e(n: Nat, h: Or<Option<Nat>, n < n>) -> Nat { 0 }").unwrap();
        parse_file("fn f(n: Nat, h: Or<n < n, Option<Nat>>) -> Nat { 0 }").unwrap();
        // One-directional: a TIGHT `<` is not thereby a bracket. `a<b` has no
        // closing `>`, so it falls back to the comparison it always was.
        parse_file("fn g(a: Nat, b: Nat) -> Type { a<b }").unwrap();
        // Newlines are whitespace too, deliberately: the rule is one sentence,
        // and wrapping works by breaking *inside* the brackets instead.
        assert!(parse_file("fn h(xs: List\n<Nat>) -> Nat { 0 }").is_err());
    }

    /// A stray `>` names its own cause. `>` is not an operator anywhere, so
    /// meeting one where something else was due means its `<` was read as a
    /// comparison — nearly always an unintended space.
    #[test]
    fn a_stray_gt_blames_the_space_before_its_lt() {
        let e = parse_file("fn f(xs: List <Nat>) -> Nat { 0 }").unwrap_err();
        assert!(e.msg.contains("space before it"), "{}", e.msg);
        assert!(e.msg.contains("List<Nat>"), "{}", e.msg);
    }

    /// The memo must not change *which* programs parse — it only skips work
    /// already known to be wasted. The shapes that exercise every rewind path:
    /// a comparison in type position (the `Lt` round's whole point), a real
    /// type application, the `(`-follows reinterpretation, and nesting of each.
    #[test]
    fn memoized_speculation_accepts_exactly_what_it_did_before() {
        parse_file("fn a(n: Nat, m: Nat, h: n < m) -> Nat { 0 }").unwrap();
        parse_file("fn b(xs: List<Option<Nat>>) -> List<Option<Nat>> { xs }").unwrap();
        parse_file("theorem c(): id<Nat>(3) = 3 { refl }").unwrap();
        parse_file("fn d(n: Nat, m: Nat, h: Or<(n < m), (m <= n)>) -> Nat { 0 }").unwrap();
        parse_file("fn e(a: Nat, b: Nat) -> Nat { a < b }").unwrap();
    }

    #[test]
    fn axioms_are_explicit_and_bodiless() {
        let d = parse_file("axiom funext<A>(f, g: A -> A): f = g;")
            .unwrap()
            .items
            .remove(0)
            .into_decl();
        assert_eq!(d.kind, DeclKind::Axiom);
        assert!(parse_file("axiom assumed(): Nat { 0 }").is_err());
        assert!(parse_file("theorem accidental(): Nat;").is_err());
        assert!(parse_file("postulate hidden(): Nat;").is_err());
    }

    // Index defaults (issues/constraint-indices-from-carrier-designations.md):
    // a record's trailing run only, a bare symbol is a designation reference,
    // and no other head takes one.
    #[test]
    fn record_index_defaults() {
        let ok = parse_file("record U<A>(op: A -> A -> A := +, e: A := 0) { f: Nat }").expect("parses");
        let Item::Inductive(d) = &ok.items[0] else { panic!("a record") };
        assert!(matches!(d.valparams[0].default.as_deref().map(|e| &e.kind), Some(ExprKind::OpSymbol { .. })));
        assert!(!d.valparams[0].implicit && d.valparams[1].default.is_some());
        let middle = parse_file("record U<A>(op: A -> A -> A := +, e: A) { f: Nat }").unwrap_err();
        assert!(middle.msg.contains("follows a defaulted value parameter"), "{}", middle.msg);
        let class = parse_file("class C<A>(op: A -> A -> A := +) { }").unwrap_err();
        assert!(class.msg.contains("only a `record`"), "{}", class.msg);
    }

    /// `record Target::Held(self t: Target, …)` (issues/record-in-type-namespace.md):
    /// one qualifier, and a `self` that is the first value parameter.
    #[test]
    fn record_in_a_type_namespace() {
        let ok = parse_file("record T::Held(self t: T, n: Nat) { f: Nat }").expect("parses");
        let Item::Inductive(d) = &ok.items[0] else { panic!("a record") };
        assert_eq!(d.name, "T::Held");
        assert!(d.valparams[0].is_self && !d.valparams[1].is_self);
        let late = parse_file("record T::Held(n: Nat, self t: T) { f: Nat }").unwrap_err();
        assert!(late.msg.contains("its first value parameter"), "{}", late.msg);
        let two = parse_file("record T::A::Held(self t: T) { f: Nat }").unwrap_err();
        assert!(two.msg.contains("more than one qualifier"), "{}", two.msg);
        // Elsewhere `self` is still an ordinary name.
        let named = parse_file("record R(self: Nat) { f: Nat }").expect("parses");
        let Item::Inductive(d) = &named.items[0] else { panic!("a record") };
        assert!(d.valparams[0].name == "self" && !d.valparams[0].is_self);
        let class = parse_file("class C<A>(self x: A) { }").unwrap_err();
        assert!(!class.msg.is_empty());
        // An inductive still declares no qualified name.
        let ind = parse_file("inductive T::D { A }").unwrap_err();
        assert!(ind.msg.contains("qualified name"), "{}", ind.msg);
    }

    #[test]
    fn anonymous_requires_mints_a_hygienic_solver_parameter() {
        let f = parse_file("fn f requires Monoid<Nat> () -> Nat { 0 }").unwrap();
        let p = &only_decl(&f).params[0];
        assert_eq!(p.name, "#requires0");
        assert!(p.implicit);
        assert_eq!(p.solver, Some(Solver::Infer));
        assert_eq!(p.origin, ParamOrigin::InlineConstraint);
    }

    #[test]
    fn assuming_flattens_a_comma_separated_telescope_over_every_declaration() {
        let f = parse_file(
            "assuming h: Nat, Nat { \
                 fn first(x: Nat) -> Nat { h } \
                 theorem second(): Nat { first(0) } \
             }",
        )
        .unwrap();
        assert_eq!(f.items.len(), 2);
        for item in &f.items {
            let Item::Decl(d) = item else { panic!("expected a declaration") };
            assert_eq!(d.params[0].name, "h");
            assert_eq!(d.params[1].name, "#assuming0");
            assert!(d.params[..2].iter().all(|p| {
                p.implicit
                    && p.solver == Some(Solver::Infer)
                    && p.origin == ParamOrigin::Assuming
            }));
        }
        let Item::Decl(first) = &f.items[0] else { unreachable!() };
        assert_eq!(first.params[2].name, "x", "written parameters follow the group telescope");
    }

    #[test]
    fn nested_assuming_groups_put_outer_requirements_first() {
        let f = parse_file(
            "assuming outer: Nat { assuming inner: Nat { \
                 theorem nested(): Nat { inner } \
             } }",
        )
        .unwrap();
        let params = &only_decl(&f).params;
        assert_eq!(params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), ["outer", "inner"]);
    }

    #[test]
    fn assuming_lowers_onto_an_instances_requires_telescope() {
        let f = parse_file(
            "assuming Nat { assuming Nat { \
                 instance Mag<Nat> requires written: Mag<Nat> { op := add } \
             } }",
        )
        .unwrap();
        let Item::Instance(instance) = &f.items[0] else { panic!("expected an instance") };
        assert_eq!(
            instance.requires.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(),
            ["#assuming0", "#assuming1", "written"]
        );
        assert!(instance.requires[..2].iter().all(|p| p.origin == ParamOrigin::Assuming));
        assert_eq!(instance.requires[2].origin, ParamOrigin::Written);
    }

    #[test]
    fn a_section_head_splices_in_the_order_a_hand_written_head_has() {
        // Type parameters, then solver parameters (the section's before the
        // member's), then written parameters (likewise): exactly the head the
        // member would have written out, `fn f<A: C, B: D>(x: A, y: B)`.
        let f = parse_file(
            "section<A: C>(x: A) { section(z: A) { fn f<B: D>(y: B) -> A { x } } }",
        )
        .unwrap();
        let [Item::Decl(d)] = &f.items[..] else { panic!("expected one declaration") };
        let tyvars: Vec<&str> = d.tyvars.iter().map(|t| t.name.as_str()).collect();
        assert_eq!(tyvars, ["A", "B"]);
        let origins: Vec<(bool, ParamOrigin)> =
            d.params.iter().map(|p| (p.solver.is_some(), p.origin)).collect();
        assert_eq!(
            origins,
            [
                (true, ParamOrigin::InlineConstraint),
                (true, ParamOrigin::InlineConstraint),
                (false, ParamOrigin::Written),
                (false, ParamOrigin::Written),
                (false, ParamOrigin::Written),
            ]
        );
        let written: Vec<&str> = d.params[2..].iter().map(|p| p.name.as_str()).collect();
        assert_eq!(written, ["x", "z", "y"]);
    }

    #[test]
    fn assuming_refuses_item_kinds_not_yet_generalized() {
        let e = parse_file("assuming Nat { inductive D { C } }").unwrap_err();
        assert!(e.msg.contains("inside `assuming` is not implemented yet"), "{}", e.msg);
    }

    // -- `Pos<A>` binder sugar (issues/pos-binder-sugar.md) -----------------

    #[test]
    fn a_pos_parameter_is_its_carrier_then_a_searched_fact() {
        let d = decl_of("fn f(a, b: Pos<Nat>, c: Nat) -> Nat { a }");
        let shape: Vec<_> = d
            .params
            .iter()
            .map(|p| (p.name.as_str(), p.implicit, p.solver == Some(Solver::Infer)))
            .collect();
        assert_eq!(
            shape,
            vec![
                ("a", false, false),
                ("a_pos", true, true),
                ("b", false, false),
                ("b_pos", true, true),
                ("c", false, false),
            ]
        );
        assert!(matches!(d.params[0].ty.kind, TyKind::Nat), "{:?}", d.params[0].ty);
    }

    #[test]
    fn a_pos_result_declares_the_functions_fact_after_it() {
        let items = parse_file("fn sq(n: Pos<Nat>, k: Nat) -> Pos<Nat> { n * n }").unwrap().items;
        assert_eq!(items.len(), 2);
        let mut items = items.into_iter();
        let f = items.next().unwrap().into_decl();
        assert!(matches!(f.result.kind, TyKind::Nat), "{:?}", f.result);
        let fact = items.next().unwrap().into_decl();
        assert_eq!(fact.name, "sq::pos");
        assert!(fact.is_evidence && fact.kind == DeclKind::Theorem);
        // Values become implicits the conclusion fixes; `n_pos` stays a premise.
        let shape: Vec<_> = fact.params.iter().map(|p| (p.name.as_str(), p.implicit, p.solver.is_some())).collect();
        assert_eq!(shape, vec![("n", true, false), ("n_pos", true, true), ("k", true, false)]);
    }

    #[test]
    fn a_pos_field_is_its_carrier_then_a_fact_and_a_rule() {
        let items = parse_file("record Frac { num: Nat, den: Pos<Nat> }").unwrap().items;
        let Item::Inductive(r) = &items[0] else { panic!("{:?}", items[0]) };
        let fields: Vec<_> = r.ctors[0]
            .fields
            .iter()
            .map(|f| (f.name.clone().unwrap(), f.default.is_some()))
            .collect();
        assert_eq!(fields, vec![("num".into(), false), ("den".into(), false), ("den_pos".into(), true)]);
        let Item::Decl(rule) = &items[1] else { panic!("{:?}", items[1]) };
        assert_eq!(rule.name, "Frac::den_positive");
        assert!(rule.is_evidence);
    }

    #[test]
    fn a_member_pos_result_declares_the_members_fact() {
        let items = parse_file("fn Nat::twice(self n: Nat) -> Pos<Nat> { n + n + 1 }").unwrap().items;
        let fact = items.into_iter().nth(1).unwrap().into_decl();
        assert_eq!(fact.name, "Nat::twice::pos");
        assert!(!fact.params[0].is_self && fact.params[0].implicit);
    }

    #[test]
    fn a_parameterised_records_rule_takes_its_parameters() {
        let items = parse_file("record Bounded<A>(k: Nat) { a: A, len: Pos<Nat>, ok: len <= k }")
            .unwrap()
            .items;
        let Item::Decl(rule) = &items[1] else { panic!("{:?}", items[1]) };
        assert_eq!(rule.name, "Bounded::len_positive");
        let tyvars: Vec<_> = rule.tyvars.iter().map(|t| t.name.as_str()).collect();
        assert_eq!(tyvars, vec!["A"]);
        // `{k: Nat}`, then the record at `Bounded<A>(k)`, both implicit.
        assert_eq!(rule.params.len(), 2);
        assert!(rule.params.iter().all(|p| p.implicit && p.solver.is_none()));
        assert_eq!(rule.params[0].name, "k");
        assert!(matches!(rule.params[1].ty.kind, TyKind::OfExpr(_)), "{:?}", rule.params[1].ty);
    }

    #[test]
    fn a_pos_constructor_field_expands_with_no_rule() {
        let items = parse_file("inductive Q { Mk(a: Nat, n: Pos<Nat>), Other }").unwrap().items;
        assert_eq!(items.len(), 1);
        let Item::Inductive(q) = &items[0] else { panic!("{:?}", items[0]) };
        let fields: Vec<_> = q.ctors[0]
            .fields
            .iter()
            .map(|f| (f.name.clone().unwrap(), f.default.is_some()))
            .collect();
        assert_eq!(fields, vec![("a".into(), false), ("n".into(), false), ("n_pos".into(), true)]);
        let e = parse_file("inductive Q { Mk(Pos<Nat>) }").unwrap_err();
        assert!(e.msg.contains("a `Pos<A>` field needs a name"), "{}", e.msg);
    }
}

/// The words a declaration (or its modifier) starts with: what may follow a
/// prefix generator's name ([`Parser::prefixed`]).
const DECL_WORDS: &[&str] = &["fn", "theorem", "def", "meta", "evidence", "axiom", "interface"];
/// The type declarations a name may stand before: `record` takes a prefix
/// generator, and the others are named so that one before them is refused
/// as a prefix and not as "expected `fn`".
const PREFIXED_TYPE_WORDS: &[&str] = &["record", "inductive", "codata", "class", "instance"];
