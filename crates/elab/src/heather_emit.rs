//! Rust-side construction API for generated Heather expressions.
//!
//! This is an emission IR, not a second Heather frontend. It represents the
//! stable syntactic structure of an expression, then serializes once at the
//! checker boundary; what is emitted is still parsed, elaborated, and
//! kernel-checked normally. The relational-context reports
//! (`relational_context`) spell their goals with it.

use std::fmt::Write;

const LINE_WIDTH: usize = 96;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ExprKind {
    Atom(String),
    Nat(heather_kernel::term::Numeral),
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

    pub fn nat(value: impl Into<heather_kernel::term::Numeral>) -> Self {
        Self {
            kind: ExprKind::Nat(value.into()),
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

#[cfg(test)]
mod tests {
    use super::Expr;

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
