//! A word function and the word functions it calls, reflected into a
//! FunctionIR program for the verified lowering
//! (issues/function-ir-verified-lowering.md, round 4).
//!
//! Untrusted like every reflector: nothing here is believed. The certificate
//! states `program_eval(program, f, [a, …]) = source(a, …)` and the kernel
//! checks it by conversion, which the evaluator's shape makes possible
//! (`function_ir_compile`). What this produces is only what that equation
//! and `lower_program` then judge.
//!
//! The fragment: parameters and result `BitVec(64)`, at most six
//! parameters; bodies of literal constants, `add`/`sub`/`band`/`bor`/`bxor`,
//! calls to functions of the same fragment (each its own function in the
//! program, called by a `Call` node), and `match` on a comparison
//! (`unsigned_lt_bit`, `signed_lt_bit`, `eq_bit`) in tail position.
use super::*;

/// A structured region of the verified lowering's FunctionIR, with calls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramRegion {
    Dataflow(Region),
    Compose(Box<ProgramRegion>, Box<ProgramRegion>),
    Conditional { inputs: Vec<Port>, condition: u64, arguments: Vec<Port>, outputs: Vec<Port>,
        when_true: Box<ProgramRegion>, when_false: Box<ProgramRegion> },
    Call { callee: usize, arguments: Vec<u64>, result: u64 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramFunction {
    pub source_name: String,
    pub arity: usize,
    pub body: ProgramRegion,
    pub result: u64,
}

/// Function `k` is `functions[k]`, and calls only functions below it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedProgram {
    pub functions: Vec<ProgramFunction>,
    pub root: usize,
}

impl ReflectedProgram {
    /// The program as `function_ir` lists it: last first.
    pub fn render(&self) -> String {
        let items: Vec<String> = self.functions.iter().rev().map(ProgramFunction::render).collect();
        format!("[\n    {}\n]", items.join(",\n    "))
    }
}

impl ProgramFunction {
    fn render(&self) -> String {
        let parameters: Vec<String> = (0..self.arity).map(|id| id.to_string()).collect();
        format!("Function(parameters := [{}], body := {}, result := {})", parameters.join(", "), self.body.render(), self.result)
    }
}

fn ports(ports: &[Port]) -> String {
    let items: Vec<String> = ports.iter().map(|port| format!("Port(id := {}, width := {})", port.id, port.width)).collect();
    format!("Ports([{}])", items.join(", "))
}

impl ProgramRegion {
    pub fn render(&self) -> String {
        match self {
            Self::Dataflow(region) => {
                let nodes: Vec<String> = region.nodes.iter().map(|node| cert::render_node(*node)).collect();
                format!("Dataflow(Region(inputs := {}, nodes := [{}], outputs := {}))", ports(&region.inputs), nodes.join(", "), ports(&region.outputs))
            }
            Self::Compose(prefix, continuation) => format!("Compose({}, {})", prefix.render(), continuation.render()),
            Self::Conditional { inputs, condition, arguments, outputs, when_true, when_false } => format!("Conditional({}, {condition}, {}, {}, {}, {})",
                ports(inputs), ports(arguments), ports(outputs), when_true.render(), when_false.render()),
            Self::Call { callee, arguments, result } => {
                let arguments: Vec<String> = arguments.iter().map(u64::to_string).collect();
                format!("Call({callee}, [{}], {result})", arguments.join(", "))
            }
        }
    }
}

/// The function `source_name` and every function it reaches, as a program
/// whose last function is it.
pub fn reflect_program(elaborator: &Elaborator, source_name: &str) -> Result<ReflectedProgram, SourceError> {
    let root = elaborator.global_abs(source_name).ok_or_else(|| SourceError::Unsupported(format!("unknown source function `{source_name}`")))?;
    let globals = Globals::resolve(elaborator)?;
    let mut program = Program { elaborator, globals, functions: Vec::new(), index: BTreeMap::new(), stack: Vec::new() };
    let root = program.function(root)?;
    Ok(ReflectedProgram { functions: program.functions, root })
}

struct Globals {
    operations: OperationGlobals,
    unsigned_less: usize,
    signed_less: usize,
    equal: usize,
    word: usize,
}

impl Globals {
    fn resolve(elaborator: &Elaborator) -> Result<Self, SourceError> {
        let abs = |name: &str| elaborator.global_abs(name).ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not loaded")));
        let word = elaborator.lookup_inductive("bitvec::BitVec").map(|ind| ind.tag)
            .ok_or_else(|| SourceError::Unsupported("`bitvec::BitVec` is not loaded".into()))?;
        Ok(Self { operations: OperationGlobals::resolve(elaborator)?, unsigned_less: abs("bitvec::BitVec::unsigned_lt_bit")?,
            signed_less: abs("bitvec::BitVec::signed_lt_bit")?, equal: abs("bitvec::BitVec::eq_bit")?, word: word as usize })
    }
}

struct Program<'a> {
    elaborator: &'a Elaborator,
    globals: Globals,
    functions: Vec<ProgramFunction>,
    /// Each reflected function's index, by its global.
    index: BTreeMap<usize, usize>,
    /// The functions being reflected, to refuse recursion.
    stack: Vec<usize>,
}

impl Program<'_> {
    /// Whether `ty` is `BitVec(64)`.
    fn is_word(&self, at: usize, ty: &Type) -> bool {
        use crate::gendefs::GenDef;
        let Type::El { tm, .. } = ty else { return false; };
        let (head, args) = application_spine(tm);
        let code = absolute(head, at).and_then(|abs| self.elaborator.types.gdefs().key_for_abs(&(abs as u32)));
        matches!(code, Some(GenDef::TyCodeFn(tag)) if *tag as usize == self.globals.word) && args.len() == 1 && nat_literal(args[0]) == Some(64)
    }

    /// The global's parameter count, when it is a word function this
    /// fragment can call.
    fn word_signature(&self, at: usize) -> Option<usize> {
        let name = self.elaborator.global_qualified_name_at(at)?;
        let (ty, _) = self.elaborator.global_body(&name)?;
        let mut arity = 0;
        let mut current = &*ty;
        while let Type::Pi { dom, cod, .. } = current {
            if !self.is_word(at, dom) { return None; }
            arity += 1;
            current = cod;
        }
        (arity <= 6 && self.is_word(at, current)).then_some(arity)
    }

    /// The function at global `at`, reflected once.
    fn function(&mut self, at: usize) -> Result<usize, SourceError> {
        if let Some(index) = self.index.get(&at) { return Ok(*index); }
        if self.stack.contains(&at) { return unsupported("a recursive function is not compiled: a program's functions call only those below them"); }
        let name = self.elaborator.global_qualified_name_at(at).ok_or_else(|| SourceError::Unsupported("a function has no qualified name".into()))?;
        let arity = self.word_signature(at)
            .ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not a function of at most six BitVec(64) parameters returning BitVec(64)")))?;
        let (_, body) = self.elaborator.global_body(&name).ok_or_else(|| SourceError::Unsupported(format!("`{name}` must be transparent")))?;
        let mut term = &*body;
        for _ in 0..arity {
            let Term::Lam { body, .. } = term else { return unsupported("a function's parameters must be λs"); };
            term = body;
        }
        self.stack.push(at);
        let mut body = Body { at, arity, next_id: arity as u64 + 1, scope: Scope::default(), steps: Vec::new() };
        let result = arity as u64;
        let region = body.tail(self, term, 0, result);
        self.stack.pop();
        let region = region?;
        let index = self.functions.len();
        self.functions.push(ProgramFunction { source_name: name, arity, body: region, result });
        self.index.insert(at, index);
        Ok(index)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Constant(u64),
    Binary(SourceBinaryOperation, u64, u64),
    UnsignedLess(u64, u64),
    SignedLess(u64, u64),
    Equal(u64, u64),
    Call(usize, [u64; 6], usize),
}

/// The values computed on the path so far, and the ports in scope.
#[derive(Clone, Default)]
struct Scope { values: BTreeMap<Key, Port>, ports: Vec<Port> }

/// One function's body as it is reflected: finished regions, and the nodes
/// of the dataflow region being built.
struct Body {
    at: usize,
    arity: usize,
    next_id: u64,
    scope: Scope,
    steps: Vec<ProgramRegion>,
}

#[derive(Default)]
struct Pending { nodes: Vec<Node>, inputs: Vec<Port>, outputs: Vec<Port> }

impl Body {
    fn fresh(&mut self) -> Result<u64, SourceError> {
        if self.next_id >= 16384 { return unsupported("the function exceeds its value budget"); }
        let id = self.next_id;
        self.next_id += 1;
        Ok(id)
    }

    fn inputs(&self) -> Vec<Port> {
        let mut inputs: Vec<Port> = (0..self.arity as u64).map(|id| Port { id, width: 64 }).collect();
        inputs.extend(self.scope.ports.iter().copied());
        inputs
    }

    /// The nodes built since the last region, closed into one.
    fn flush(&mut self, pending: &mut Pending) {
        if pending.nodes.is_empty() { return; }
        let region = Region { inputs: std::mem::take(&mut pending.inputs), nodes: std::mem::take(&mut pending.nodes), outputs: std::mem::take(&mut pending.outputs) };
        self.steps.push(ProgramRegion::Dataflow(region));
    }

    fn node(&mut self, pending: &mut Pending, key: Option<Key>, width: u64, target: Option<u64>, make: impl FnOnce(u64) -> Node) -> Result<Port, SourceError> {
        if let (Some(key), None) = (key, target) { if let Some(port) = self.scope.values.get(&key) { return Ok(*port); } }
        if pending.nodes.is_empty() { pending.inputs = self.inputs(); }
        let port = Port { id: match target { Some(id) => id, None => self.fresh()? }, width };
        pending.nodes.push(make(port.id));
        pending.outputs.push(port);
        if let (Some(key), None) = (key, target) {
            self.scope.values.insert(key, port);
            self.scope.ports.push(port);
        }
        Ok(port)
    }

    fn parameter(&self, term: &Term, depth: u32) -> Option<Result<Port, SourceError>> {
        let Term::Var(LocalVar(index)) = term else { return None; };
        Some(index.checked_sub(depth).and_then(|index| self.arity.checked_sub(index as usize + 1))
            .map(|id| Port { id: id as u64, width: 64 })
            .ok_or_else(|| SourceError::Unsupported("a value reads a match payload or something outside the function".into())))
    }

    /// A word value.
    fn value(&mut self, program: &mut Program, pending: &mut Pending, term: &Term, depth: u32) -> Result<Port, SourceError> {
        if let Some(port) = self.parameter(term, depth) { return port; }
        if matches!(term, Term::Case { .. }) {
            return unsupported("a match is compiled only in tail position, as a function's result or a branch's");
        }
        let (head, args) = application_spine(term);
        let at = absolute(head, self.at).ok_or_else(|| SourceError::Unsupported("a value must apply a resolved function".into()))?;
        let globals = &program.globals;
        if at == globals.operations.of_nat && args.len() == 2 && nat_literal(args[0]) == Some(64) {
            if let Some(value) = nat_literal(args[1]) {
                return self.node(pending, Some(Key::Constant(value)), 64, None, |output| Node::Const { width: 64, output, value });
            }
        }
        if let Some(operation) = globals.operations.operations.get(&at).copied() {
            if args.len() != 3 || nat_literal(args[0]) != Some(64) { return unsupported("arithmetic is compiled at width 64"); }
            let left = self.value(program, pending, args[1], depth)?.id;
            let right = self.value(program, pending, args[2], depth)?.id;
            return self.node(pending, Some(Key::Binary(operation, left, right)), 64, None, |output| operation.node_at_width(64, output, left, right));
        }
        let Some(arity) = program.word_signature(at) else {
            let name = program.elaborator.global_qualified_name_at(at).unwrap_or_else(|| "a global".into());
            return unsupported(&format!("`{name}` is not an operation this compiler lowers, nor a function of BitVec(64) words it can call"));
        };
        if args.len() != arity { return unsupported("a call must apply every parameter"); }
        let callee = program.function(at)?;
        let mut arguments = [0u64; 6];
        for (slot, argument) in arguments.iter_mut().zip(&args) { *slot = self.value(program, pending, argument, depth)?.id; }
        let key = Key::Call(callee, arguments, arity);
        if let Some(port) = self.scope.values.get(&key) { return Ok(*port); }
        self.flush(pending);
        let result = self.fresh()?;
        self.steps.push(ProgramRegion::Call { callee, arguments: arguments[..arity].to_vec(), result });
        // The result arrives in RAX, which the next call takes: it moves to
        // a register of its own at once.
        self.scope.ports.push(Port { id: result, width: 64 });
        let kept = self.node(pending, None, 64, None, |output| Node::Move { width: 64, output, source: result })?;
        self.scope.values.insert(key, kept);
        self.scope.ports.push(kept);
        Ok(kept)
    }

    /// A one-bit test a match branches on.
    fn test(&mut self, program: &mut Program, pending: &mut Pending, term: &Term, depth: u32) -> Result<Port, SourceError> {
        let (head, args) = application_spine(term);
        let at = absolute(head, self.at);
        let globals = &program.globals;
        let comparison = match at {
            Some(at) if at == globals.unsigned_less => 0,
            Some(at) if at == globals.signed_less => 1,
            Some(at) if at == globals.equal => 2,
            _ => return unsupported("a match is compiled on a comparison: unsigned_lt_bit, signed_lt_bit or eq_bit of words"),
        };
        if args.len() != 3 || nat_literal(args[0]) != Some(64) { return unsupported("comparisons are compiled at width 64"); }
        let left = self.value(program, pending, args[1], depth)?.id;
        let right = self.value(program, pending, args[2], depth)?.id;
        match comparison {
            0 => self.node(pending, Some(Key::UnsignedLess(left, right)), 1, None, |output| Node::UnsignedLessThan { width: 64, output, left, right }),
            1 => self.node(pending, Some(Key::SignedLess(left, right)), 1, None, |output| Node::SignedLessThan { width: 64, output, left, right }),
            _ => self.node(pending, Some(Key::Equal(left, right)), 1, None, |output| Node::Equal { width: 64, output, left, right }),
        }
    }

    /// The region computing `term` into `target`, and everything before it.
    fn tail(&mut self, program: &mut Program, term: &Term, depth: u32, target: u64) -> Result<ProgramRegion, SourceError> {
        let mut pending = Pending::default();
        if let Term::Case { scrut, case_l, case_r, .. } = term {
            let condition = self.test(program, &mut pending, scrut, depth)?;
            self.flush(&mut pending);
            let inputs = self.inputs();
            let outputs = vec![Port { id: target, width: 64 }];
            let steps = std::mem::take(&mut self.steps);
            let scope = self.scope.clone();
            let when_true = self.tail(program, case_r, depth + 1, target);
            self.scope = scope.clone();
            let when_false = self.tail(program, case_l, depth + 1, target);
            self.scope = scope;
            self.steps = steps;
            let arguments = inputs.iter().copied().filter(|port| port.width == 64).collect();
            self.steps.push(ProgramRegion::Conditional { inputs, condition: condition.id, arguments, outputs,
                when_true: Box::new(when_true?), when_false: Box::new(when_false?) });
        } else {
            let value = self.value(program, &mut pending, term, depth)?;
            if value.id != target {
                self.node(&mut pending, None, 64, Some(target), |output| Node::Move { width: 64, output, source: value.id })?;
            }
            self.flush(&mut pending);
        }
        let mut steps = std::mem::take(&mut self.steps).into_iter().rev();
        let last = steps.next().ok_or_else(|| SourceError::Unsupported("an empty body".into()))?;
        Ok(steps.fold(last, |continuation, prefix| ProgramRegion::Compose(Box::new(prefix), Box::new(continuation))))
    }
}

fn absolute(term: &Term, caller: usize) -> Option<usize> {
    match term { Term::GlobalTm { var, .. } => caller.checked_sub(1 + var.0 as usize), _ => None }
}

/// A nullary global of type `List<Nat>`, evaluated and read back: how the
/// compiler learns the bytes and offsets `lower_program` computed, which
/// the certificate then states as literals and the kernel checks.
pub fn evaluate_numbers(elaborator: &Elaborator, name: &str) -> Result<Vec<u64>, SourceError> {
    let arena = ValueArena::new();
    let reader = Reader::new(elaborator, &arena);
    let mut cell = reader.global(elaborator, name)?;
    let mut numbers = Vec::new();
    loop {
        let (index, fields, children) = reader.ctor(cell)?;
        match (index, fields.first(), children.first()) {
            (0, _, _) => return Ok(numbers),
            (1, Some(head), Some(tail)) => {
                if numbers.len() >= 1 << 20 { return unsupported("an implausibly long list"); }
                numbers.push(reader.nat(head)?);
                cell = tail;
            }
            _ => return unsupported("not a list of numbers"),
        }
    }
}

/// A nullary global of type `Nat`, evaluated.
pub fn evaluate_number(elaborator: &Elaborator, name: &str) -> Result<u64, SourceError> {
    let arena = ValueArena::new();
    let reader = Reader::new(elaborator, &arena);
    let value = reader.global(elaborator, name)?;
    reader.nat(value)
}

use heather_kernel::value::{Env, TmClo, Val, ValueArena};

struct Reader<'a, 'v> {
    psi: &'a heather_kernel::term::GlobalCtx,
    arena: &'v ValueArena<'v>,
    cache: heather_kernel::reduce::GlobalCache,
}

impl<'a, 'v> Reader<'a, 'v> {
    fn new(elaborator: &'a Elaborator, arena: &'v ValueArena<'v>) -> Self {
        Reader { psi: elaborator.psi(), arena, cache: heather_kernel::reduce::GlobalCache::new() }
    }

    fn global(&self, elaborator: &Elaborator, name: &str) -> Result<&'v TmClo<'v>, SourceError> {
        let len = self.psi.bindings.len();
        let abs = elaborator.global_abs(name).ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not declared")))?;
        let head = Term::GlobalTm { var: heather_kernel::term::GlobalVar((len - 1 - abs) as u32),
            subst: heather_kernel::term::LocalSubst::id(&heather_kernel::term::LocalCtx::nil()) };
        Ok(self.arena.tm(TmClo::syn(Env::empty(), std::sync::Arc::new(head))))
    }

    fn force(&self, c: &'v TmClo<'v>) -> Result<std::sync::Arc<Val<'v>>, SourceError> {
        let mut eval = heather_kernel::eval::Eval::new(heather_kernel::typing::DEFAULT_FUEL,
            heather_kernel::reduce::Defs::transparent_cached(self.psi, &self.cache), heather_kernel::term::CtxBase::Nil, self.arena);
        eval.force(c).and_then(|v| eval.delta_whnf(v)).map_err(|_| SourceError::Unsupported("evaluation ran out of fuel".into()))
    }

    /// `(constructor index, fields, recursive children)` of a two-constructor
    /// inductive.
    fn ctor(&self, c: &'v TmClo<'v>) -> Result<(usize, Vec<&'v TmClo<'v>>, Vec<&'v TmClo<'v>>), SourceError> {
        let w = self.force(c)?;
        let (label, children) = match &*w {
            Val::Supf { label, children, .. } => (*label, self.spine(children)?),
            _ => (self.arena.tm(TmClo::val(std::sync::Arc::clone(&w))), vec![]),
        };
        let v = self.force(label)?;
        let (index, payload) = match &*v {
            Val::Inl { val, .. } => (0, *val),
            Val::Inr { val, .. } => (1, *val),
            _ => return unsupported("a value that is not a constructor"),
        };
        let Val::Pair { snd, .. } = &*self.force(payload)? else { return unsupported("a constructor payload that is not a pair"); };
        Ok((index, self.spine(snd)?, children))
    }

    fn spine(&self, c: &'v TmClo<'v>) -> Result<Vec<&'v TmClo<'v>>, SourceError> {
        let mut out = Vec::new();
        let mut v = self.force(c)?;
        loop {
            let next = match &*v {
                Val::Triv { .. } => return Ok(out),
                Val::Pair { fst, snd, .. } => { out.push(*fst); *snd }
                _ => return unsupported("a tuple that is not a pair chain"),
            };
            v = self.force(next)?;
        }
    }

    fn nat(&self, c: &'v TmClo<'v>) -> Result<u64, SourceError> {
        let mut v = self.force(c)?;
        let mut n = 0u64;
        loop {
            let next = match &*v {
                Val::Zero => return Ok(n),
                // A word's value is a numeral up to 2^64, an immediate's.
                Val::Succ(p) => { n = n.checked_add(1).ok_or_else(|| SourceError::Unsupported("a numeral past 64 bits".into()))?; *p }
                Val::NatRun { program, tail } => {
                    let count = heather_kernel::value::program::ContextProgram::repetition_count_up_to(program, u64::MAX - n)
                        .ok_or_else(|| SourceError::Unsupported("a numeral past 64 bits".into()))?;
                    n += count;
                    *tail
                }
                _ => return unsupported("a Nat that is not a numeral"),
            };
            v = self.force(next)?;
        }
    }
}
