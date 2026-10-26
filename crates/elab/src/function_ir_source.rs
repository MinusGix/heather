//! Heather source reflected into FunctionIR for the verified lowering: a
//! word function and the word functions it calls become a FunctionIR program
//! (`program`), which `compile-x86` lowers through `lower_program` and
//! certifies with `compiled_returns`. The reflector is untrusted: the
//! certificate states that the program evaluates to the source function, and
//! the kernel checks it.

use std::collections::BTreeMap;

use heather_kernel::term::{LocalVar, Term, Type};

use crate::Elaborator;
use crate::function_ir_cert::{self as cert, Node, Port, Region};

mod program;
pub use program::{reflect_program, evaluate_numbers, evaluate_number, ids, ProgramFunction, ProgramRegion, Measured, ReflectedLoop, ReflectedProgram, Split};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceError {
    Unsupported(String),
}

impl std::fmt::Display for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for SourceError {}

fn unsupported<T>(message: &str) -> Result<T, SourceError> {
    Err(SourceError::Unsupported(message.to_string()))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceBinaryOperation {
    Add,
    Sub,
    BitAnd,
    BitOr,
    BitXor,
}

impl SourceBinaryOperation {
    fn node_at_width(self, width: u64, output: u64, left: u64, right: u64) -> Node {
        match self {
            Self::Add => Node::Add { width, output, left, right },
            Self::Sub => Node::Sub { width, output, left, right },
            Self::BitAnd => Node::BitAnd { width, output, left, right },
            Self::BitOr => Node::BitOr { width, output, left, right },
            Self::BitXor => Node::BitXor { width, output, left, right },
        }
    }

    fn semantic_name(self) -> &'static str {
        match self {
            Self::Add => "bitvec::BitVec::add",
            Self::Sub => "bitvec::BitVec::sub",
            Self::BitAnd => "bitvec::BitVec::band",
            Self::BitOr => "bitvec::BitVec::bor",
            Self::BitXor => "bitvec::BitVec::bxor",
        }
    }
}

struct OperationGlobals {
    operations: BTreeMap<usize, SourceBinaryOperation>,
    of_nat: usize,
}

impl OperationGlobals {
    fn resolve(elaborator: &Elaborator) -> Result<Self, SourceError> {
        let mut operations = BTreeMap::new();
        for (name, operation) in [
            ("bitvec::BitVec::add", SourceBinaryOperation::Add),
            ("bitvec::BitVec::sub", SourceBinaryOperation::Sub),
            ("bitvec::BitVec::band", SourceBinaryOperation::BitAnd),
            ("bitvec::BitVec::bor", SourceBinaryOperation::BitOr),
            ("bitvec::BitVec::bxor", SourceBinaryOperation::BitXor),
        ] {
            let abs = elaborator.global_abs(name).ok_or_else(|| {
                SourceError::Unsupported(format!("required operation `{name}` is not loaded"))
            })?;
            operations.insert(abs, operation);
        }
        let of_nat = elaborator.global_abs("bitvec::BitVec::ofNat").ok_or_else(|| {
            SourceError::Unsupported("required operation `bitvec::BitVec::ofNat` is not loaded".to_string())
        })?;
        Ok(Self { operations, of_nat })
    }
}

fn application_spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut head = term;
    let mut arguments = Vec::new();
    while let Some((fun, arg)) = crate::spelling::app_of(head) {
        arguments.push(&**arg);
        head = fun;
    }
    arguments.reverse();
    (head, arguments)
}

fn nat_literal(term: &Term) -> Option<u64> {
    match term {
        Term::Zero => Some(0),
        Term::NatLit(value) => value.as_u64(),
        Term::Succ(predecessor) => nat_literal(predecessor)?.checked_add(1),
        _ => None,
    }
}
