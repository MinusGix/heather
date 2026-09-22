//! Rust-side construction API for generated Heather source.
//!
//! This is an emission IR, not a second Heather frontend. It represents the
//! stable syntactic structure generators need—expressions, binders, blocks,
//! and declarations—then serializes once at the checker boundary. The emitted
//! module is still parsed, elaborated, and kernel-checked normally.

use std::fmt::Write;

const LINE_WIDTH: usize = 96;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ExprKind {
    Atom(String),
    Nat(u64),
    Call {
        callee: Box<Expr>,
        arguments: Vec<Argument>,
    },
    Projection {
        receiver: Box<Expr>,
        field: String,
    },
    Equal {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    List(Vec<Expr>),
    Lambda {
        parameters: Vec<String>,
        body: Box<Expr>,
    },
    /// A consciously unstructured leaf for syntax not yet represented by the
    /// emission IR. Callers cannot accidentally obtain one through `From`.
    Raw(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Argument {
    Positional(Expr),
    Named { name: String, value: Expr },
}

impl Expr {
    pub fn name(name: impl Into<String>) -> Self {
        Self {
            kind: ExprKind::Atom(name.into()),
        }
    }

    pub fn nat(value: u64) -> Self {
        Self {
            kind: ExprKind::Nat(value),
        }
    }

    pub fn call(callee: impl Into<Expr>, arguments: impl IntoIterator<Item = Expr>) -> Self {
        Self {
            kind: ExprKind::Call {
                callee: Box::new(callee.into()),
                arguments: arguments.into_iter().map(Argument::Positional).collect(),
            },
        }
    }

    /// `@callee(arguments)`: every parameter positional, implicits included —
    /// for emitters that know a width the callee declares implicit.
    pub fn explicit_call(callee: &str, arguments: impl IntoIterator<Item = Expr>) -> Self {
        Self::call(Self::name(format!("@{callee}")), arguments)
    }

    pub fn nullary(callee: impl Into<Expr>) -> Self {
        Self::call(callee, [])
    }

    pub fn named_call(
        callee: impl Into<Expr>,
        arguments: impl IntoIterator<Item = (impl Into<String>, Expr)>,
    ) -> Self {
        Self {
            kind: ExprKind::Call {
                callee: Box::new(callee.into()),
                arguments: arguments
                    .into_iter()
                    .map(|(name, value)| Argument::Named {
                        name: name.into(),
                        value,
                    })
                    .collect(),
            },
        }
    }

    pub fn with_argument(mut self, argument: Expr) -> Self {
        match &mut self.kind {
            ExprKind::Call { arguments, .. } => arguments.push(Argument::Positional(argument)),
            _ => panic!("arguments can only be appended to a call expression"),
        }
        self
    }

    pub fn with_named_argument(mut self, name: impl Into<String>, value: Expr) -> Self {
        match &mut self.kind {
            ExprKind::Call { arguments, .. } => {
                arguments.push(Argument::Named {
                    name: name.into(),
                    value,
                });
            }
            _ => panic!("named arguments can only be appended to a call expression"),
        }
        self
    }

    pub fn project(self, field: impl Into<String>) -> Self {
        Self {
            kind: ExprKind::Projection {
                receiver: Box::new(self),
                field: field.into(),
            },
        }
    }

    pub fn equal(left: Expr, right: Expr) -> Self {
        Self {
            kind: ExprKind::Equal {
                left: Box::new(left),
                right: Box::new(right),
            },
        }
    }

    pub fn list(elements: impl IntoIterator<Item = Expr>) -> Self {
        Self {
            kind: ExprKind::List(elements.into_iter().collect()),
        }
    }

    pub fn lambda(parameters: impl IntoIterator<Item = impl Into<String>>, body: Expr) -> Self {
        Self {
            kind: ExprKind::Lambda {
                parameters: parameters.into_iter().map(Into::into).collect(),
                body: Box::new(body),
            },
        }
    }

    pub fn raw(source: impl Into<String>) -> Self {
        Self {
            kind: ExprKind::Raw(source.into()),
        }
    }

    pub fn render(&self) -> String {
        self.render_at(0)
    }

    fn render_at(&self, indent: usize) -> String {
        let flat = self.render_flat();
        if indent + flat.chars().count() <= LINE_WIDTH || !self.can_break() {
            return flat;
        }
        match &self.kind {
            ExprKind::Call { callee, arguments } => {
                let mut out = format!("{}(\n", callee.render_at(indent));
                for (index, argument) in arguments.iter().enumerate() {
                    out.push_str(&" ".repeat(indent + 4));
                    match argument {
                        Argument::Positional(value) => out.push_str(&value.render_at(indent + 4)),
                        Argument::Named { name, value } => {
                            write!(out, "{name} := {}", value.render_at(indent + 4)).unwrap();
                        }
                    }
                    if index + 1 != arguments.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                out.push_str(&" ".repeat(indent));
                out.push(')');
                out
            }
            ExprKind::Equal { left, right } => format!(
                "{} =\n{}{}",
                left.render_at(indent),
                " ".repeat(indent + 4),
                right.render_at(indent + 4),
            ),
            ExprKind::List(elements) => {
                let mut out = "[\n".to_string();
                for (index, element) in elements.iter().enumerate() {
                    out.push_str(&" ".repeat(indent + 4));
                    out.push_str(&element.render_at(indent + 4));
                    if index + 1 != elements.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                out.push_str(&" ".repeat(indent));
                out.push(']');
                out
            }
            _ => flat,
        }
    }

    fn can_break(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::Call { .. } | ExprKind::Equal { .. } | ExprKind::List(_)
        )
    }

    fn render_flat(&self) -> String {
        match &self.kind {
            ExprKind::Atom(atom) => atom.clone(),
            ExprKind::Nat(value) => value.to_string(),
            ExprKind::Call { callee, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| match argument {
                        Argument::Positional(value) => value.render_flat(),
                        Argument::Named { name, value } => {
                            format!("{name} := {}", value.render_flat())
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({arguments})", callee.render_flat())
            }
            ExprKind::Projection { receiver, field } => {
                format!("{}.{field}", receiver.render_flat())
            }
            ExprKind::Equal { left, right } => {
                format!("{} = {}", left.render_flat(), right.render_flat())
            }
            ExprKind::List(elements) => format!(
                "[{}]",
                elements
                    .iter()
                    .map(Expr::render_flat)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ExprKind::Lambda { parameters, body } => {
                format!("λ {} => {}", parameters.join(" "), body.render_flat())
            }
            ExprKind::Raw(source) => source.clone(),
        }
    }
}

impl From<&str> for Expr {
    fn from(value: &str) -> Self {
        Self::name(value)
    }
}

impl From<String> for Expr {
    fn from(value: String) -> Self {
        Self::name(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parameter {
    name: String,
    ty: Expr,
}

impl Parameter {
    pub fn explicit(name: impl Into<String>, ty: Expr) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }

    fn render(&self, indent: usize) -> String {
        format!(
            "{}: {}",
            self.name,
            self.ty.render_at(indent + self.name.len() + 2)
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    Let { name: String, value: Expr },
    Expression(Expr),
}

impl Statement {
    pub fn let_value(name: impl Into<String>, value: Expr) -> Self {
        Self::Let {
            name: name.into(),
            value,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    statements: Vec<Statement>,
    result: Expr,
}

impl Block {
    pub fn expression(result: Expr) -> Self {
        Self {
            statements: Vec::new(),
            result,
        }
    }

    pub fn new(statements: impl IntoIterator<Item = Statement>, result: Expr) -> Self {
        Self {
            statements: statements.into_iter().collect(),
            result,
        }
    }

    fn render(&self, out: &mut String) {
        for statement in &self.statements {
            match statement {
                Statement::Let { name, value } => {
                    writeln!(
                        out,
                        "    let {name} = {};",
                        value.render_at(4 + name.len() + 7)
                    )
                    .unwrap();
                }
                Statement::Expression(expression) => {
                    writeln!(out, "    {};", expression.render_at(4)).unwrap();
                }
            }
        }
        for line in self.result.render_at(4).lines() {
            writeln!(out, "    {line}").unwrap();
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationKind {
    Function,
    Theorem,
}

impl DeclarationKind {
    fn keyword(self) -> &'static str {
        match self {
            Self::Function => "fn",
            Self::Theorem => "theorem",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    kind: DeclarationKind,
    name: String,
    generics: Vec<String>,
    parameters: Vec<Parameter>,
    result: Expr,
    body: Block,
}

impl Declaration {
    pub fn function(name: impl Into<String>, result: Expr, body: Block) -> Self {
        Self::new(DeclarationKind::Function, name, result, body)
    }

    pub fn theorem(name: impl Into<String>, result: Expr, body: Block) -> Self {
        Self::new(DeclarationKind::Theorem, name, result, body)
    }

    fn new(kind: DeclarationKind, name: impl Into<String>, result: Expr, body: Block) -> Self {
        Self {
            kind,
            name: name.into(),
            generics: Vec::new(),
            parameters: Vec::new(),
            result,
            body,
        }
    }

    pub fn generic(mut self, generic: impl Into<String>) -> Self {
        self.generics.push(generic.into());
        self
    }

    pub fn parameter(mut self, parameter: Parameter) -> Self {
        self.parameters.push(parameter);
        self
    }

    pub fn parameters(mut self, parameters: impl IntoIterator<Item = Parameter>) -> Self {
        self.parameters.extend(parameters);
        self
    }

    fn render(&self, out: &mut String) {
        write!(out, "{} {}", self.kind.keyword(), self.name).unwrap();
        if !self.generics.is_empty() {
            write!(out, "<{}>", self.generics.join(", ")).unwrap();
        }
        out.push('(');
        if !self.parameters.is_empty() {
            let rendered = self
                .parameters
                .iter()
                .map(|parameter| parameter.render(4))
                .collect::<Vec<_>>();
            out.push_str(&rendered.join(",\n    "));
        }
        out.push(')');
        match self.kind {
            DeclarationKind::Function => {
                write!(out, " → {}", self.result.render_at(4)).unwrap();
            }
            DeclarationKind::Theorem => {
                write!(out, ":\n    {}", self.result.render_at(4)).unwrap();
            }
        }
        out.push_str("\n{\n");
        self.body.render(out);
        out.push('}');
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Module {
    items: Vec<ModuleItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ModuleItem {
    Declaration(Declaration),
    Raw(String),
}

impl Module {
    /// Compose structured fragments without rendering either one to raw text.
    pub fn extend(&mut self, other: Module) {
        self.items.extend(other.items);
    }

    pub fn declaration(&mut self, declaration: Declaration) {
        self.items.push(ModuleItem::Declaration(declaration));
    }

    /// Preserve a legacy generated fragment while it is migrated. New code
    /// should construct declarations and expressions instead.
    pub fn raw(&mut self, text: impl Into<String>) {
        let text = text.into();
        if !text.trim().is_empty() {
            self.items.push(ModuleItem::Raw(text));
        }
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        for (index, item) in self.items.iter().enumerate() {
            if index > 0 {
                out.push_str("\n\n");
            }
            match item {
                ModuleItem::Declaration(declaration) => declaration.render(&mut out),
                ModuleItem::Raw(text) => out.push_str(text.trim()),
            }
        }
        out.push('\n');
        out
    }
}

#[cfg(test)]
mod tests {
    use super::{Block, Declaration, Expr, Module, Parameter, Statement};

    #[test]
    fn constructs_calls_projections_and_named_records() {
        let artifact = Expr::named_call(
            "Artifact",
            [
                ("after", Expr::name("prior").project("after")),
                (
                    "proof",
                    Expr::call("trans", [Expr::name("left"), Expr::name("right")]),
                ),
            ],
        );
        assert_eq!(
            artifact.render(),
            "Artifact(after := prior.after, proof := trans(left, right))",
        );
    }

    #[test]
    fn renders_structured_declarations_and_blocks() {
        let mut module = Module::default();
        module.declaration(Declaration::function(
            "answer",
            Expr::name("Nat"),
            Block::expression(Expr::nat(42)),
        ));
        let mut suffix = Module::default();
        suffix.declaration(
            Declaration::theorem(
                "answer_is_answer",
                Expr::equal(Expr::nullary("answer"), Expr::nullary("answer")),
                Block::new(
                    [Statement::let_value("proof", Expr::name("refl"))],
                    Expr::name("proof"),
                ),
            )
            .parameter(Parameter::explicit("unused", Expr::name("True"))),
        );
        module.extend(suffix);
        assert_eq!(
            module.render(),
            "fn answer() → Nat\n{\n    42\n}\n\n\
             theorem answer_is_answer(unused: True):\n    answer() = answer()\n{\n\
             \x20   let proof = refl;\n    proof\n}\n",
        );
    }

    #[test]
    fn long_calls_break_deterministically() {
        let expression = Expr::call(
            "long_function_name",
            (0..8).map(|index| Expr::name(format!("argument_with_a_long_name_{index}"))),
        );
        let rendered = expression.render();
        assert!(rendered.starts_with("long_function_name(\n    argument_with_a_long_name_0,"));
        assert!(rendered.ends_with("argument_with_a_long_name_7\n)"));
    }
}
