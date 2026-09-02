//! A deliberately small document model for generated Heather modules.
//!
//! Generators still construct Heather expressions as text: duplicating the
//! parser's full expression grammar here would create a second frontend.  The
//! declaration structure, parameters, indentation, and module spacing are not
//! expressions, however, and keeping those in ad-hoc `format!` calls made the
//! FunctionIR backend hard to change safely.  This module owns that structure.

use std::fmt::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclarationKind {
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
pub(crate) struct Declaration {
    kind: DeclarationKind,
    name: String,
    generics: Vec<String>,
    parameters: Vec<String>,
    result: String,
    body: String,
}

impl Declaration {
    pub(crate) fn function(name: impl Into<String>, result: impl Into<String>) -> Self {
        Self::new(DeclarationKind::Function, name, result)
    }

    pub(crate) fn theorem(name: impl Into<String>, result: impl Into<String>) -> Self {
        Self::new(DeclarationKind::Theorem, name, result)
    }

    fn new(kind: DeclarationKind, name: impl Into<String>, result: impl Into<String>) -> Self {
        Self {
            kind,
            name: name.into(),
            generics: Vec::new(),
            parameters: Vec::new(),
            result: result.into(),
            body: String::new(),
        }
    }

    pub(crate) fn generic(mut self, generic: impl Into<String>) -> Self {
        self.generics.push(generic.into());
        self
    }

    pub(crate) fn parameter(mut self, parameter: impl Into<String>) -> Self {
        self.parameters.push(parameter.into());
        self
    }

    pub(crate) fn parameters(mut self, parameters: impl IntoIterator<Item = String>) -> Self {
        self.parameters.extend(parameters);
        self
    }

    pub(crate) fn body(mut self, body: impl Into<String>) -> Self {
        self.body = body.into();
        self
    }

    fn render(&self, out: &mut String) {
        write!(out, "{} {}", self.kind.keyword(), self.name).unwrap();
        if !self.generics.is_empty() {
            write!(out, "<{}>", self.generics.join(", ")).unwrap();
        }
        out.push('(');
        if !self.parameters.is_empty() {
            out.push_str(&self.parameters.join(",\n    "));
        }
        out.push(')');
        match self.kind {
            DeclarationKind::Function => write!(out, " → {}", self.result).unwrap(),
            DeclarationKind::Theorem => write!(out, ":\n    {}", self.result).unwrap(),
        }
        out.push_str("\n{\n");
        for line in self.body.lines() {
            if line.is_empty() {
                out.push('\n');
            } else {
                writeln!(out, "    {line}").unwrap();
            }
        }
        out.push('}');
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Module {
    items: Vec<ModuleItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ModuleItem {
    Declaration(Declaration),
    Raw(String),
}

impl Module {
    pub(crate) fn declaration(&mut self, declaration: Declaration) {
        self.items.push(ModuleItem::Declaration(declaration));
    }

    /// Preserve an already-generated module fragment while its declarations
    /// are migrated incrementally to this representation.
    pub(crate) fn raw(&mut self, text: impl Into<String>) {
        let text = text.into();
        if !text.trim().is_empty() {
            self.items.push(ModuleItem::Raw(text));
        }
    }

    pub(crate) fn render(&self) -> String {
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
    use super::{Declaration, Module};

    #[test]
    fn renders_structured_declarations() {
        let mut module = Module::default();
        module.declaration(Declaration::function("answer", "Nat").body("42"));
        module.declaration(
            Declaration::theorem("answer_is_answer", "answer() = answer()").body("refl"),
        );
        assert_eq!(
            module.render(),
            "fn answer() → Nat\n{\n    42\n}\n\n\
             theorem answer_is_answer():\n    answer() = answer()\n{\n    refl\n}\n",
        );
    }
}
