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
//! program, called by a `Call` node), and `match` in tail position on a
//! test. A test is a comparison (`unsigned_lt_bit`, `signed_lt_bit`,
//! `eq_bit`), `&&`, `||`, `!`, a `Bool` literal, a match whose arms are
//! tests, or a call to a `Bool` helper of words, whose body is inlined as a
//! test: each compiles to conditionals on comparisons, an operand tested
//! only where the connective needs it.
//!
//! A loop, a recursion on a fuel or a `decreases` recursion on a word's
//! `toNat`, is a `runtime fn`'s (docs/native/runtime-fn-setups-design.md §16.11):
//! this reflector refuses one, naming the marker. It stays for tests through
//! `Bool` helpers, which the default setup does not compile yet, and for
//! `heather reflect`.
//!
//! Each function is proved on its own, its calls answered by its callees'
//! sources (`function_ir_compile::program_eval_sources`), so a proof never
//! unfolds a callee. A function evaluates, its calls answered by any
//! `call`, to its *expansion* by conversion: the decision tree it compiles,
//! spelled with the source's own operations and `call` (`expansion`). With
//! the callees' sources for `call`, a function whose matches are all on
//! comparisons is its expansion by conversion, and one that decides a
//! connective or a helper (`decided`) by case analysis on its comparisons
//! (`split_all`).
use super::*;
use heather_kernel::rc::Rc;
use crate::name_lookup::NameLookup;

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
    /// The body as the decision tree the program evaluates to, in the
    /// source's operations over parameters `a0, a1, …`, with function `k`'s
    /// calls answered by `call(k, [b0, …])`.
    pub expansion: String,
    /// A match decided a connective or a helper: the expansion is the
    /// source only by case analysis.
    pub decided: bool,
    /// A test calls a `Bool` helper, whose body is inlined: the default
    /// `runtime fn` setup does not compile that yet (`compile-x86` keeps
    /// such a program on this reflector, docs/native/runtime-fn-setups-design.md
    /// §16.9).
    pub helped: bool,
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
    /// What the function computes at `arguments`: its source applied.
    pub fn answer(&self, arguments: &[String]) -> String {
        format!("{}({})", self.source_name, arguments.join(", "))
    }

    pub fn render(&self) -> String {
        let parameters: Vec<String> = (0..self.arity).map(|id| id.to_string()).collect();
        format!("Function(parameters := [{}], body := {}, result := {})", parameters.join(", "), self.body.render(), self.result)
    }
}

pub fn ids(ids: &[u64]) -> String {
    ids.iter().map(u64::to_string).collect::<Vec<_>>().join(", ")
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
            Self::Call { callee, arguments, result } => format!("Call({callee}, [{}], {result})", ids(arguments)),
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
    /// Absent when the source does not import `bool`: then nothing tests one.
    boolean: Option<usize>,
    and: Option<usize>,
    or: Option<usize>,
    not: Option<usize>,
}

impl Globals {
    fn resolve(elaborator: &Elaborator) -> Result<Self, SourceError> {
        let abs = |name: &str| elaborator.global_abs(name).ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not loaded")));
        let word = elaborator.lookup_inductive("bitvec::BitVec").map(|ind| ind.tag)
            .ok_or_else(|| SourceError::Unsupported("`bitvec::BitVec` is not loaded".into()))?;
        let boolean = elaborator.lookup_inductive("bool::Bool").map(|ind| ind.tag as usize);
        Ok(Self { operations: OperationGlobals::resolve(elaborator)?, unsigned_less: abs("bitvec::BitVec::unsigned_lt_bit")?,
            signed_less: abs("bitvec::BitVec::signed_lt_bit")?, equal: abs("bitvec::BitVec::eq_bit")?, word: word as usize,
            boolean, and: elaborator.global_abs("bool::Bool::and"), or: elaborator.global_abs("bool::Bool::or"),
            not: elaborator.global_abs("bool::Bool::not") })
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

    /// Whether `ty` is `Bool`.
    fn is_bool(&self, at: usize, ty: &Type) -> bool {
        use crate::gendefs::GenDef;
        let Type::El { tm, .. } = ty else { return false; };
        let (head, args) = application_spine(tm);
        let code = absolute(head, at).and_then(|abs| self.elaborator.types.gdefs().key_for_abs(&(abs as u32)));
        matches!(code, Some(GenDef::TyCode(tag)) if Some(*tag as usize) == self.globals.boolean) && args.is_empty()
    }

    /// The global's word parameter count and its result type, when its
    /// parameters are words.
    fn signature(&self, at: usize) -> Option<(usize, Type)> {
        let name = NameLookup(self.elaborator).global_qualified_name_at(at)?;
        let (ty, _) = NameLookup(self.elaborator).global_body(&name)?;
        let mut arity = 0;
        let mut current = &*ty;
        while let Type::Pi { dom, cod, .. } = current {
            if !self.is_word(at, dom) { return None; }
            arity += 1;
            current = cod;
        }
        (arity <= 6).then(|| (arity, current.clone()))
    }

    /// The global's word parameter count, when it recurses on a fuel: a
    /// `Nat`, then words, returning a word. Such a loop is a `runtime fn`'s.
    fn loop_signature(&self, at: usize) -> Option<usize> {
        let name = NameLookup(self.elaborator).global_qualified_name_at(at)?;
        let (ty, _) = NameLookup(self.elaborator).global_body(&name)?;
        let Type::Pi { dom, cod, .. } = &*ty else { return None; };
        if !matches!(&**dom, Type::Nat) { return None; }
        let mut arity = 0;
        let mut current = &**cod;
        while let Type::Pi { dom, cod, .. } = current {
            if !self.is_word(at, dom) { return None; }
            arity += 1;
            current = cod;
        }
        (1..=4).contains(&arity).then_some(()).filter(|_| self.is_word(at, current)).map(|_| arity)
    }

    /// The global's parameter count, when it is a word function this
    /// fragment can call.
    fn word_signature(&self, at: usize) -> Option<usize> {
        self.signature(at).filter(|(_, result)| self.is_word(at, result)).map(|(arity, _)| arity)
    }

    /// The global's parameter count, when it is a `Bool` helper of words.
    fn test_signature(&self, at: usize) -> Option<usize> {
        self.signature(at).filter(|(_, result)| self.is_bool(at, result)).map(|(arity, _)| arity)
    }

    /// Whether a function's body, under its λs, is a `decreases`
    /// function's: a call of its generated recursor.
    fn measured(&self, at: usize, name: &str, body: &Term) -> bool {
        let (head, _) = application_spine(body);
        absolute(head, at).and_then(|g| NameLookup(self.elaborator).global_qualified_name_at(g)).is_some_and(|r| r == crate::measure::rec_name(name))
    }

    /// A transparent global's body under its `arity` parameters' λs.
    fn body_of(&self, at: usize, arity: usize) -> Result<(String, Rc<Term>), SourceError> {
        let name = NameLookup(self.elaborator).global_qualified_name_at(at).ok_or_else(|| SourceError::Unsupported("a function has no qualified name".into()))?;
        let (_, body) = NameLookup(self.elaborator).global_body(&name).ok_or_else(|| SourceError::Unsupported(format!("`{name}` must be transparent")))?;
        let mut term = body;
        for _ in 0..arity {
            let Term::Lam { body, .. } = &*term else { return unsupported("a function's parameters must be λs"); };
            term = Rc::clone(body);
        }
        Ok((name, term))
    }

    /// The function at global `at`, reflected once.
    fn function(&mut self, at: usize) -> Result<usize, SourceError> {
        if let Some(index) = self.index.get(&at) { return Ok(*index); }
        if self.stack.contains(&at) { return unsupported("a recursive function is not compiled: a program's functions call only those below them"); }
        let name = NameLookup(self.elaborator).global_qualified_name_at(at).ok_or_else(|| SourceError::Unsupported("a function has no qualified name".into()))?;
        let arity = self.word_signature(at)
            .ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not a function of at most six BitVec(64) parameters returning BitVec(64)")))?;
        let (_, term) = self.body_of(at, arity)?;
        if self.measured(at, &name, &term) {
            return unsupported(&format!("`{name}` is a loop: mark it `runtime fn {}` (docs/native/runtime-fn-setups-design.md §16.11)", name.rsplit("::").next().unwrap_or(&name)));
        }
        self.stack.push(at);
        let parameters: Vec<Port> = (0..arity as u64).map(|id| Port { id, width: 64 }).collect();
        let spell = (0..arity as u64).map(|id| (id, format!("a{id}"))).collect();
        let mut body = Body::new(parameters.clone(), arity as u64 + 1, spell);
        let result = arity as u64;
        let cx = Rc::new(Cx { at, parameters });
        let region = body.tail(self, &term, &cx, 0, &Target::Word(result));
        self.stack.pop();
        let (region, expansion) = region?;
        let index = self.functions.len();
        self.functions.push(ProgramFunction { source_name: name, arity, body: region, result, expansion, decided: body.decided, helped: body.helped });
        self.index.insert(at, index);
        Ok(index)
    }
}

/// Where a term's names resolve: the global it is the body of, and its
/// parameters' ports (a helper's are its call's arguments).
struct Cx {
    at: usize,
    parameters: Vec<Port>,
}

/// Where a test's outcome leads: a match's arm, or a further test.
#[derive(Clone)]
enum Arm {
    Tail(Rc<Term>, Rc<Cx>, u32),
    Decide(Rc<Term>, Rc<Cx>, u32, Box<Arm>, Box<Arm>),
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
    /// The words the body's names start from: a function's parameters, or a
    /// loop's state.
    parameters: Vec<Port>,
    next_id: u64,
    scope: Scope,
    steps: Vec<ProgramRegion>,
    /// Each port's value as the source spells it, operations inline.
    spell: BTreeMap<u64, String>,
    decided: bool,
    /// The helpers being inlined, to refuse recursion.
    helpers: Vec<usize>,
    /// A `Bool` helper was inlined somewhere in the body.
    helped: bool,
}

/// Where a tail's value goes: a word.
#[derive(Clone)]
enum Target {
    Word(u64),
}

impl Target {
    fn ids(&self) -> Vec<u64> {
        match self { Self::Word(id) => vec![*id] }
    }
}

#[derive(Default)]
struct Pending { nodes: Vec<Node>, inputs: Vec<Port>, outputs: Vec<Port> }

impl Body {
    fn new(parameters: Vec<Port>, next_id: u64, spell: BTreeMap<u64, String>) -> Self {
        Body { parameters, next_id, scope: Scope::default(), steps: Vec::new(), spell, decided: false, helpers: Vec::new(), helped: false }
    }

    fn fresh(&mut self) -> Result<u64, SourceError> {
        if self.next_id >= 16384 { return unsupported("the function exceeds its value budget"); }
        let id = self.next_id;
        self.next_id += 1;
        Ok(id)
    }

    fn inputs(&self) -> Vec<Port> {
        let mut inputs = self.parameters.clone();
        inputs.extend(self.scope.ports.iter().copied());
        inputs
    }

    /// The nodes built since the last region, closed into one.
    fn flush(&mut self, pending: &mut Pending) {
        if pending.nodes.is_empty() { return; }
        let region = Region { inputs: std::mem::take(&mut pending.inputs), nodes: std::mem::take(&mut pending.nodes), outputs: std::mem::take(&mut pending.outputs) };
        self.steps.push(ProgramRegion::Dataflow(region));
    }

    fn node(&mut self, pending: &mut Pending, key: Option<Key>, width: u64, target: Option<u64>, spelling: String, make: impl FnOnce(u64) -> Node) -> Result<Port, SourceError> {
        if let (Some(key), None) = (key, target) { if let Some(port) = self.scope.values.get(&key) { return Ok(*port); } }
        if pending.nodes.is_empty() { pending.inputs = self.inputs(); }
        let port = Port { id: match target { Some(id) => id, None => self.fresh()? }, width };
        pending.nodes.push(make(port.id));
        pending.outputs.push(port);
        self.spell.insert(port.id, spelling);
        if let (Some(key), None) = (key, target) {
            self.scope.values.insert(key, port);
            self.scope.ports.push(port);
        }
        Ok(port)
    }

    fn spelling(&self, port: Port) -> String {
        self.spell.get(&port.id).cloned().expect("every port is spelled where it is made")
    }

    fn parameter(&self, cx: &Cx, term: &Term, depth: u32) -> Option<Result<Port, SourceError>> {
        let Term::Var(LocalVar(index)) = term else { return None; };
        Some(index.checked_sub(depth).and_then(|index| cx.parameters.len().checked_sub(index as usize + 1))
            .map(|slot| cx.parameters[slot])
            .ok_or_else(|| SourceError::Unsupported("a value reads a match payload or something outside the function".into())))
    }

    /// A word value.
    fn value(&mut self, program: &mut Program, pending: &mut Pending, term: &Term, cx: &Cx, depth: u32) -> Result<Port, SourceError> {
        if let Some(port) = self.parameter(cx, term, depth) { return port; }
        if matches!(term, Term::Case { .. }) {
            return unsupported("a match is compiled only in tail position, as a function's result or a branch's");
        }
        let (head, args) = application_spine(term);
        if let Some(Err(error)) = self.parameter(cx, head, depth) { return Err(error); }
        let at = absolute(head, cx.at).ok_or_else(|| SourceError::Unsupported("a value must apply a resolved function".into()))?;
        let globals = &program.globals;
        if at == globals.operations.of_nat && args.len() == 2 && nat_literal(args[0]) == Some(64) {
            if let Some(value) = nat_literal(args[1]) {
                return self.node(pending, Some(Key::Constant(value)), 64, None, format!("@bitvec::BitVec::ofNat(64, {value})"),
                    |output| Node::Const { width: 64, output, value });
            }
        }
        if let Some(operation) = globals.operations.operations.get(&at).copied() {
            if args.len() != 3 || nat_literal(args[0]) != Some(64) { return unsupported("arithmetic is compiled at width 64"); }
            let left = self.value(program, pending, args[1], cx, depth)?;
            let right = self.value(program, pending, args[2], cx, depth)?;
            let spelling = format!("@{}(64, {}, {})", operation.semantic_name(), self.spelling(left), self.spelling(right));
            let (left, right) = (left.id, right.id);
            return self.node(pending, Some(Key::Binary(operation, left, right)), 64, None, spelling, |output| operation.node_at_width(64, output, left, right));
        }
        if program.loop_signature(at).is_some() {
            let name = NameLookup(program.elaborator).global_qualified_name_at(at).unwrap_or_else(|| "a global".into());
            return unsupported(&format!("`{name}` is a loop: mark it `runtime fn {}` (docs/native/runtime-fn-setups-design.md §16.11)", name.rsplit("::").next().unwrap_or(&name)));
        }
        let Some(arity) = program.word_signature(at) else {
            let name = NameLookup(program.elaborator).global_qualified_name_at(at).unwrap_or_else(|| "a global".into());
            return unsupported(&format!("`{name}` is not an operation this compiler lowers, nor a function of BitVec(64) words it can call"));
        };
        if args.len() != arity { return unsupported("a call must apply every parameter"); }
        let callee = program.function(at)?;
        self.call(program, pending, callee, &args, cx, depth)
    }

    /// A call of function `callee` of the program on `args`' values.
    fn call(&mut self, program: &mut Program, pending: &mut Pending, callee: usize, args: &[&Term], cx: &Cx, depth: u32) -> Result<Port, SourceError> {
        let mut arguments = [0u64; 6];
        let mut spelled = Vec::new();
        for (slot, argument) in arguments.iter_mut().zip(args) {
            let port = self.value(program, pending, argument, cx, depth)?;
            spelled.push(self.spelling(port));
            *slot = port.id;
        }
        let arity = args.len();
        let key = Key::Call(callee, arguments, arity);
        if let Some(port) = self.scope.values.get(&key) { return Ok(*port); }
        self.flush(pending);
        let result = self.fresh()?;
        let spelling = format!("call({callee}, [{}])", spelled.join(", "));
        self.steps.push(ProgramRegion::Call { callee, arguments: arguments[..arity].to_vec(), result });
        self.spell.insert(result, spelling.clone());
        // The result arrives in RAX, which the next call takes: it moves to
        // a register of its own at once.
        self.scope.ports.push(Port { id: result, width: 64 });
        let kept = self.node(pending, None, 64, None, spelling, |output| Node::Move { width: 64, output, source: result })?;
        self.scope.values.insert(key, kept);
        self.scope.ports.push(kept);
        Ok(kept)
    }

    /// A comparison's bit.
    fn comparison(&mut self, program: &mut Program, pending: &mut Pending, at: usize, args: &[&Term], cx: &Cx, depth: u32) -> Result<Option<Port>, SourceError> {
        let globals = &program.globals;
        let (comparison, name) = match at {
            at if at == globals.unsigned_less => (0, "unsigned_lt_bit"),
            at if at == globals.signed_less => (1, "signed_lt_bit"),
            at if at == globals.equal => (2, "eq_bit"),
            _ => return Ok(None),
        };
        if args.len() != 3 || nat_literal(args[0]) != Some(64) { return unsupported("comparisons are compiled at width 64"); }
        let left = self.value(program, pending, args[1], cx, depth)?;
        let right = self.value(program, pending, args[2], cx, depth)?;
        let spelling = format!("@bitvec::BitVec::{name}(64, {}, {})", self.spelling(left), self.spelling(right));
        let (left, right) = (left.id, right.id);
        let port = match comparison {
            0 => self.node(pending, Some(Key::UnsignedLess(left, right)), 1, None, spelling, |output| Node::UnsignedLessThan { width: 64, output, left, right })?,
            1 => self.node(pending, Some(Key::SignedLess(left, right)), 1, None, spelling, |output| Node::SignedLessThan { width: 64, output, left, right })?,
            _ => self.node(pending, Some(Key::Equal(left, right)), 1, None, spelling, |output| Node::Equal { width: 64, output, left, right })?,
        };
        Ok(Some(port))
    }

    /// The regions deciding `test` and then running `yes` where it holds and
    /// `no` where it does not, pushed onto the steps; and their expansion.
    fn branch(&mut self, program: &mut Program, test: &Term, cx: &Rc<Cx>, depth: u32, yes: &Arm, no: &Arm, target: &Target)
        -> Result<String, SourceError>
    {
        // A literal outcome takes its arm.
        match crate::spelling::inj_of(test) {
            Some((true, _)) => { self.decided = true; return self.arm(program, no, target); }
            Some((false, _)) => { self.decided = true; return self.arm(program, yes, target); }
            None => {}
        }
        // A match whose arms are tests: its scrutinee decides which.
        if let Term::Case { scrut, case_l, case_r, .. } = test {
            self.decided = true;
            let when_true = Arm::Decide(Rc::clone(case_r), Rc::clone(cx), depth + 1, Box::new(yes.clone()), Box::new(no.clone()));
            let when_false = Arm::Decide(Rc::clone(case_l), Rc::clone(cx), depth + 1, Box::new(yes.clone()), Box::new(no.clone()));
            return self.branch(program, scrut, cx, depth, &when_true, &when_false, target);
        }
        let (head, args) = application_spine(test);
        let at = absolute(head, cx.at).ok_or_else(|| SourceError::Unsupported("a match must test a comparison, a connective or a Bool helper".into()))?;
        let globals = &program.globals;
        if Some(at) == globals.not && args.len() == 1 {
            self.decided = true;
            return self.branch(program, args[0], cx, depth, no, yes, target);
        }
        if Some(at) == globals.and && args.len() == 2 {
            self.decided = true;
            let then = Arm::Decide(Rc::new(args[1].clone()), Rc::clone(cx), depth, Box::new(yes.clone()), Box::new(no.clone()));
            return self.branch(program, args[0], cx, depth, &then, no, target);
        }
        if Some(at) == globals.or && args.len() == 2 {
            self.decided = true;
            let otherwise = Arm::Decide(Rc::new(args[1].clone()), Rc::clone(cx), depth, Box::new(yes.clone()), Box::new(no.clone()));
            return self.branch(program, args[0], cx, depth, yes, &otherwise, target);
        }
        let mut pending = Pending::default();
        let condition = match self.comparison(program, &mut pending, at, &args, cx, depth)? {
            Some(condition) => condition,
            None => {
                // A Bool helper: its body is the test, its parameters the
                // arguments' ports.
                let Some(arity) = program.test_signature(at) else {
                    return unsupported("a match is compiled on a comparison (unsigned_lt_bit, signed_lt_bit or eq_bit of words), &&, ||, !, or a Bool helper of words");
                };
                if args.len() != arity { return unsupported("a Bool helper's call must apply every parameter"); }
                if self.helpers.contains(&at) || self.helpers.len() >= 32 { return unsupported("a recursive Bool helper is not compiled"); }
                let mut parameters = Vec::new();
                for argument in &args { parameters.push(self.value(program, &mut pending, argument, cx, depth)?); }
                self.flush(&mut pending);
                let (_, body) = program.body_of(at, arity)?;
                self.decided = true;
                self.helped = true;
                self.helpers.push(at);
                let inner = Rc::new(Cx { at, parameters });
                let expansion = self.branch(program, &body, &inner, 0, yes, no, target);
                self.helpers.pop();
                return expansion;
            }
        };
        self.flush(&mut pending);
        let inputs = self.inputs();
        let targets = target.ids();
        let outputs: Vec<Port> = targets.iter().map(|&id| Port { id, width: 64 }).collect();
        let steps = std::mem::take(&mut self.steps);
        let scope = self.scope.clone();
        let spelled = |body: &Self| -> Vec<String> { targets.iter().map(|id| body.spell.get(id).cloned().unwrap_or_default()).collect() };
        let when_true = self.arm(program, yes, target).map(|expansion| (self.close(), expansion));
        let yes_values = spelled(self);
        self.scope = scope.clone();
        let when_false = self.arm(program, no, target).map(|expansion| (self.close(), expansion));
        let no_values = spelled(self);
        self.scope = scope;
        self.steps = steps;
        let ((when_true, yes), (when_false, no)) = (when_true?, when_false?);
        // An output read after the conditional is a match on its condition
        // with each arm's value, as the evaluator branches at each read.
        for ((id, yes_value), no_value) in targets.iter().zip(yes_values).zip(no_values) {
            self.spell.insert(*id, format!("match {} {{ False => {no_value}, True => {yes_value} }}", self.spelling(condition)));
        }
        let arguments = inputs.iter().copied().filter(|port| port.width == 64).collect();
        self.steps.push(ProgramRegion::Conditional { inputs, condition: condition.id, arguments, outputs,
            when_true: Box::new(when_true?), when_false: Box::new(when_false?) });
        Ok(format!("match {} {{ False => {no}, True => {yes} }}", self.spelling(condition)))
    }

    /// An arm's regions, pushed onto the steps, and its expansion.
    fn arm(&mut self, program: &mut Program, arm: &Arm, target: &Target) -> Result<String, SourceError> {
        match arm {
            Arm::Tail(term, cx, depth) => self.compute(program, term, cx, *depth, target),
            Arm::Decide(test, cx, depth, yes, no) => self.branch(program, test, cx, *depth, yes, no, target),
        }
    }

    /// The steps so far as one region, the steps emptied.
    fn close(&mut self) -> Result<ProgramRegion, SourceError> {
        let mut steps = std::mem::take(&mut self.steps).into_iter().rev();
        let last = steps.next().ok_or_else(|| SourceError::Unsupported("an empty body".into()))?;
        Ok(steps.fold(last, |continuation, prefix| ProgramRegion::Compose(Box::new(prefix), Box::new(continuation))))
    }

    /// The steps computing `term` into `target`, pushed; and its expansion.
    fn compute(&mut self, program: &mut Program, term: &Term, cx: &Rc<Cx>, depth: u32, target: &Target) -> Result<String, SourceError> {
        // `match h: c { … }`: a match on `c` applied to `refl`, each arm
        // taking the case's equation, which no value reads.
        if let Term::AppAt { fun, arg } = term
            && let Term::Case { scrut, case_l, case_r, .. } = &**fun
            && matches!(&**arg, Term::Refl { tm, .. } if tm == scrut)
        {
            let under = |arm: &Rc<Term>| match &**arm {
                Term::Lam { body, .. } => Ok(Rc::clone(body)),
                _ => unsupported("a `match h:` arm must take its equation as a λ"),
            };
            let yes = Arm::Tail(under(case_r)?, Rc::clone(cx), depth + 2);
            let no = Arm::Tail(under(case_l)?, Rc::clone(cx), depth + 2);
            return self.branch(program, scrut, cx, depth, &yes, &no, target);
        }
        if let Term::Case { scrut, case_l, case_r, .. } = term {
            let yes = Arm::Tail(Rc::clone(case_r), Rc::clone(cx), depth + 1);
            let no = Arm::Tail(Rc::clone(case_l), Rc::clone(cx), depth + 1);
            return self.branch(program, scrut, cx, depth, &yes, &no, target);
        }
        let mut pending = Pending::default();
        let expansion = match target {
            Target::Word(target) => {
                let value = self.value(program, &mut pending, term, cx, depth)?;
                self.put(&mut pending, value, *target)?;
                self.spelling(value)
            }
        };
        self.flush(&mut pending);
        Ok(expansion)
    }

    /// `value` copied into `target`.
    fn put(&mut self, pending: &mut Pending, value: Port, target: u64) -> Result<(), SourceError> {
        if value.id != target {
            let spelling = self.spelling(value);
            self.node(pending, None, 64, Some(target), spelling, |output| Node::Move { width: 64, output, source: value.id })?;
        }
        Ok(())
    }

    /// The region computing `term` into `target`, and everything before it.
    fn tail(&mut self, program: &mut Program, term: &Term, cx: &Rc<Cx>, depth: u32, target: &Target) -> Result<(ProgramRegion, String), SourceError> {
        let expansion = self.compute(program, term, cx, depth, target)?;
        Ok((self.close()?, expansion))
    }
}

fn absolute(term: &Term, caller: usize) -> Option<usize> {
    match term { Term::GlobalTm { var, .. } => var.position(caller), _ => None }
}

/// A nullary global of type `List<Nat>`, evaluated and read back: how the
/// compiler learns the bytes and offsets `lower_program` computed, which
/// the certificate then states as literals and the kernel checks.
pub fn evaluate_numbers(elaborator: &Elaborator, name: &str) -> Result<Vec<u64>, SourceError> {
    with_reads(elaborator, |reads| reads.numbers(name))
}

/// Reads of one world that share what they force: `read` is given a
/// [`Reads`] over `elaborator`'s world, and every definition a read of it
/// evaluates is evaluated once for all of them (the evaluator keeps a
/// closed definition's value for as long as its arena lives, and here the
/// arena is the session's). So reads spelled from one another, as a part's
/// live-out set is from its parent's, each cost their own step and not the
/// chain from the root again. Everything the reads force is kept until
/// `read` returns, which is what [`Reads::full`] and [`read_sharing`] bound.
pub fn with_reads<R>(elaborator: &Elaborator, read: impl FnOnce(&Reads<'_, '_>) -> R) -> R {
    let arena = ValueArena::new();
    read(&Reads { elaborator, reader: Reader::new(elaborator, &arena), started: heather_kernel::stats::snapshot().eval_steps })
}

/// The evaluator steps a session takes before it is [`Reads::full`]. A step
/// keeps a few hundred bytes of values until its session ends, and a tool's
/// reads in one session ran past the suite's rail; counted in steps and not
/// in bytes because the kernel already counts them, so the bound asks
/// nothing new of it.
const SESSION_STEPS: u64 = 2_000_000;

/// `count` reads in order, `read(session, i)` the `i`th, in sessions each
/// ended once it is full: the reads after it start a new one, and pay again
/// for what they share with the ones before. So reads that share should be
/// neighbours, as a tree's parts are in preorder.
pub fn read_sharing<T, E>(elaborator: &Elaborator, count: usize, mut read: impl FnMut(&Reads<'_, '_>, usize) -> Result<T, E>) -> Result<Vec<T>, E> {
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        with_reads(elaborator, |reads| {
            while out.len() < count {
                out.push(read(reads, out.len())?);
                if reads.full() { break; }
            }
            Ok(())
        })?;
    }
    Ok(out)
}

/// A session of reads ([`with_reads`]): the world read, and the evaluator's
/// step count on this thread as the session started.
pub struct Reads<'a, 'v> { elaborator: &'a Elaborator, reader: Reader<'a, 'v>, started: u64 }

impl Reads<'_, '_> {
    /// Whether the session holds as much as one should ([`read_sharing`]).
    pub fn full(&self) -> bool { heather_kernel::stats::snapshot().eval_steps.saturating_sub(self.started) >= SESSION_STEPS }

    /// A nullary global of type `List<Nat>`, evaluated and read back.
    pub fn numbers(&self, name: &str) -> Result<Vec<u64>, SourceError> {
        match self.numbers_up_to(name, 1 << 20)? {
            (numbers, false) => Ok(numbers),
            (_, true) => unsupported("an implausibly long list"),
        }
    }

    /// [`Self::numbers`], stopping after the first `cap`: the numbers read,
    /// and whether the list went on past them. A cell is forced only when
    /// it is read, so nothing past the cap is evaluated (`heather eval`'s
    /// bound on what it prints).
    pub fn numbers_up_to(&self, name: &str, cap: usize) -> Result<(Vec<u64>, bool), SourceError> {
        let reader = &self.reader;
        let mut cell = reader.global(self.elaborator, name)?;
        let mut numbers = Vec::new();
        loop {
            let (index, fields, children) = reader.ctor(cell)?;
            match (index, fields.first(), children.first()) {
                (0, _, _) => return Ok((numbers, false)),
                (1, Some(head), Some(tail)) => {
                    if numbers.len() >= cap { return Ok((numbers, true)); }
                    numbers.push(reader.nat(head)?);
                    cell = tail;
                }
                _ => return unsupported("not a list of numbers"),
            }
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

/// What one read may spend: more than a declaration, since a read evaluates
/// a whole program's lowering, which the certificate states a function at a
/// time. A read is untrusted; this only bounds a runaway.
const READ_FUEL: u64 = heather_kernel::typing::DEFAULT_FUEL << 6;

struct Reader<'a, 'v> {
    psi: &'a heather_kernel::term::GlobalCtx,
    arena: &'v ValueArena<'v>,
    cache: heather_kernel::reduce::GlobalCache,
}

impl<'a, 'v> Reader<'a, 'v> {
    fn new(elaborator: &'a Elaborator, arena: &'v ValueArena<'v>) -> Self {
        Reader { psi: elaborator.psi(), arena, cache: heather_kernel::reduce::GlobalCache::for_psi(elaborator.psi()) }
    }

    fn global(&self, elaborator: &Elaborator, name: &str) -> Result<&'v TmClo<'v>, SourceError> {
        let abs = elaborator.global_abs(name).ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not declared")))?;
        let var = self.psi.reference(abs).ok_or_else(|| SourceError::Unsupported(format!("`{name}` is not in the world read")))?;
        let head = Term::GlobalTm { var,
            subst: heather_kernel::term::LocalSubst::id(&heather_kernel::term::LocalCtx::nil()) };
        Ok(self.arena.tm(TmClo::syn(Env::empty(), heather_kernel::rc::Rc::new(head))))
    }

    fn force(&self, c: &'v TmClo<'v>) -> Result<&'v Val<'v>, SourceError> {
        let mut eval = heather_kernel::eval::Eval::new(READ_FUEL,
            heather_kernel::reduce::Defs::transparent_cached(self.psi, &self.cache), heather_kernel::term::CtxBase::Nil, self.arena);
        eval.force(c).and_then(|v| eval.delta_whnf(v)).map_err(|_| SourceError::Unsupported("evaluation ran out of fuel".into()))
    }

    /// `(constructor index, fields, recursive children)` of a two-constructor
    /// inductive.
    fn ctor(&self, c: &'v TmClo<'v>) -> Result<(usize, Vec<&'v TmClo<'v>>, Vec<&'v TmClo<'v>>), SourceError> {
        let w = self.force(c)?;
        let (label, children) = match &*w {
            Val::Supf { label, children, .. } => (*label, self.spine(children)?),
            _ => (self.arena.tm(TmClo::val(w)), vec![]),
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
