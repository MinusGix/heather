//! The untrusted evaluator: closed core terms, run with their types erased.
//!
//! The kernel's evaluator is a conversion checker's: it keeps a neutral
//! spelling beside every unfolded call, evaluates the motives eliminators
//! carry, and holds every value it made until the query ends. A tool that
//! only wants a program's *answer* (the optimizer's walks, `heather eval`)
//! pays for all of that and reads none of it. This machine runs the same
//! terms as an interpreter would: types, levels and proofs erased
//! ([`Code`]), call by need as the kernel is, values freed when nothing
//! reads them.
//!
//! **Nothing here is trusted and nothing the kernel checks depends on it.**
//! A caller either has its answer checked afterwards (the optimizer's plans
//! are replayed by a checked function) or presents it as an evaluation. The
//! machine answers [`Stuck`] where it does not know a form, and a caller
//! falls back to the kernel's evaluator.
//!
//! Numbers are machine words here, where core `Nat` functions are recursors
//! the kernel runs by classifying their folds. The library's arithmetic is
//! named by the caller ([`Prim`], [`Prims`]) and run directly; each named
//! definition is first compared with its own body on small numbers, and one
//! that disagrees is run as written.

use heather_kernel::rc::Rc as Shared;
use heather_kernel::term::{self, GlobalBinding, GlobalCtx, GlobalRef, GlobalVar, Term};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

/// Why a run stopped without an answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stuck(pub String);

type Res<T> = Result<T, Stuck>;

fn stuck<T>(why: impl Into<String>) -> Res<T> {
    Err(Stuck(why.into()))
}

/// A value of the wrong form met where `wanted` was read.
fn met<T>(wanted: &str, found: &Val) -> Res<T> {
    let found = match found {
        Val::Nat(_) => "a number",
        Val::Clo(..) | Val::Ih(_) => "a function",
        Val::Pair(..) => "a pair",
        Val::Inl(_) | Val::Inr(_) => "a sum",
        Val::Sup(..) => "a tree",
        Val::Unit => "a unit or something erased",
    };
    stuck(format!("{wanted} was expected and {found} met"))
}

/// A tree former's eliminator: what its children are, and so what the
/// induction hypothesis reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tree {
    /// `W`: the children are a function of a position.
    Function,
    /// `Wf` and `IWf`: the children are a tuple, read at a `Fin`.
    Tuple,
}

/// A library definition over numbers the machine runs directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Prim {
    Add,
    /// Truncated at zero.
    Sub,
    Mul,
    Half,
    Twice,
    /// Zero where the divisor is.
    Div,
    /// The number itself where the divisor is zero.
    Mod,
    Min,
    Max,
    /// Two-valued: the answers are the definition's own at small numbers.
    Equal,
    LessOrEqual,
    Less,
    /// Two-valued, of one number: whether it is odd.
    Odd,
}

impl Prim {
    fn arity(self) -> usize {
        match self {
            Prim::Half | Prim::Twice | Prim::Odd => 1,
            _ => 2,
        }
    }

    fn two_valued(self) -> bool {
        matches!(self, Prim::Equal | Prim::LessOrEqual | Prim::Less | Prim::Odd)
    }

    fn number(self, a: u128, b: u128) -> Option<u128> {
        match self {
            Prim::Add => a.checked_add(b),
            Prim::Sub => Some(a.saturating_sub(b)),
            Prim::Mul => a.checked_mul(b),
            Prim::Half => Some(a / 2),
            Prim::Twice => a.checked_mul(2),
            Prim::Div => Some(a.checked_div(b).unwrap_or(0)),
            Prim::Mod => Some(a.checked_rem(b).unwrap_or(a)),
            Prim::Min => Some(a.min(b)),
            Prim::Max => Some(a.max(b)),
            Prim::Equal | Prim::LessOrEqual | Prim::Less | Prim::Odd => None,
        }
    }

    fn holds(self, a: u128, b: u128) -> bool {
        match self {
            Prim::Equal => a == b,
            Prim::LessOrEqual => a <= b,
            Prim::Less => a < b,
            Prim::Odd => a % 2 == 1,
            _ => false,
        }
    }
}

/// The definitions run directly, by position in Ψ.
pub type Prims = HashMap<usize, Prim>;

/// An erased term. Local variables are de Bruijn indices as in core; every
/// binder core has that a value is put for is kept, and nothing else.
pub enum Code {
    Var(u32),
    Lam(Rc<Code>),
    App(Rc<Code>, Rc<Code>),
    /// A definition at its arguments, outermost first.
    Global(usize, Box<[Rc<Code>]>, Linked),
    /// With whether it was found to be its definition: 0 not asked yet, 1
    /// yes, 2 no.
    Prim(Prim, usize, Box<[Rc<Code>]>, Cell<u8>),
    Nat(u128),
    Succ(Rc<Code>),
    /// `step` under the predecessor and the recursive answer.
    ElimNat { base: Rc<Code>, step: Rc<Code>, scrut: Rc<Code>, owner: usize },
    Pair(Rc<Code>, Rc<Code>),
    Fst(Rc<Code>),
    Snd(Rc<Code>),
    Inl(Rc<Code>),
    Inr(Rc<Code>),
    /// Each arm under the payload.
    Case { left: Rc<Code>, right: Rc<Code>, scrut: Rc<Code> },
    Sup(Rc<Code>, Rc<Code>),
    /// `step` under the label, the children and the induction hypothesis.
    Elim { tree: Tree, step: Rc<Code>, scrut: Rc<Code>, owner: usize },
    /// `body` under `bound`.
    Let { bound: Rc<Code>, body: Rc<Code> },
    /// `⟨⟩`, and every type, level and proof.
    Unit,
    Stuck(&'static str),
}

/// What a call found the first time it ran, kept at the call: the callee's
/// erased body, or for a definition of no arguments its one value.
#[derive(Default)]
pub struct Linked {
    body: std::cell::OnceCell<Rc<Code>>,
    value: std::cell::OnceCell<Thunk>,
}

type Env = Option<Rc<EnvNode>>;

pub struct EnvNode {
    value: Thunk,
    rest: Env,
}

fn push(env: &Env, value: Thunk) -> Env {
    Some(Rc::new(EnvNode { value, rest: env.clone() }))
}

/// A value to its head: components are read when asked for.
#[derive(Clone)]
pub enum Val {
    Nat(u128),
    Clo(Rc<Code>, Env),
    Pair(Thunk, Thunk),
    Inl(Thunk),
    Inr(Thunk),
    Sup(Thunk, Thunk),
    Unit,
    /// An induction hypothesis: the eliminator, waiting for which child.
    Ih(Rc<IhCell>),
}

pub struct IhCell {
    tree: Tree,
    step: Rc<Code>,
    env: Env,
    children: Thunk,
}

/// A value not yet asked for, computed once.
pub type Thunk = Rc<ThunkCell>;

pub struct ThunkCell(RefCell<State>);

enum State {
    Lazy(Rc<Code>, Env),
    /// An `elim_Nat` at a number: the recursive answer a step is handed.
    NatRec(Rc<Code>, Env, u128),
    Busy,
    Done(Val),
}

fn done(value: Val) -> Thunk {
    Rc::new(ThunkCell(RefCell::new(State::Done(value))))
}

/// The stack a run is first asked for, halved while the process cannot have
/// it (an address-space limit counts a stack whole) down to [`LEAST_STACK`].
const STACK: usize = 1 << 30;
const LEAST_STACK: usize = 32 << 20;

/// The stack one level of nesting is allowed for: several times the frames
/// a level takes, since a value dropped at the end unwinds through its
/// components the same way.
const LEVEL: usize = 2048;

/// A run over one Ψ: what it erased, and the closed definitions it has
/// evaluated, kept for the reads that follow.
pub struct Machine<'a> {
    psi: &'a GlobalCtx,
    prims: &'a Prims,
    codes: RefCell<HashMap<usize, Rc<Code>>>,
    closed: RefCell<HashMap<usize, Thunk>>,
    erased: RefCell<HashMap<(usize, usize), Rc<Code>>>,
    /// Terms built while erasing, kept so no address in `erased` is reused.
    kept: RefCell<Vec<Shared<Term>>>,
    /// A two-valued definition's answers, or `None` where it is run as
    /// written; a number-valued one's entry says only whether it is trusted.
    checked: RefCell<HashMap<usize, Option<(Val, Val)>>>,
    written: Cell<bool>,
    steps: Cell<u64>,
    fuel: u64,
    depth: Cell<u32>,
    /// The definition entered last, for a stuck run's report.
    last: Cell<usize>,
    /// Past half the nesting allowed: how often each definition was the
    /// last entered as the run nested further.
    deep: RefCell<HashMap<usize, u32>>,
    /// How deep a run nests before it answers [`Stuck`].
    deepest: u32,
}

/// `run` on a machine over `psi`, on a thread with the stack deep recursion
/// needs. Values do not leave: `run` reads what it wants out of them.
pub fn with_machine<R: Send>(psi: &GlobalCtx, prims: &Prims, fuel: u64, run: impl FnOnce(&Machine<'_>) -> R + Send) -> Result<R, Stuck> {
    let mut run = Some(run);
    let mut stack = STACK;
    loop {
        let spawned = std::thread::scope(|scope| {
            let run = &mut run;
            let handle = std::thread::Builder::new().stack_size(stack).spawn_scoped(scope, move || {
                let run = run.take().expect("a run is taken by the one thread that starts");
                let machine = Machine {
                    psi,
                    prims,
                    codes: RefCell::default(),
                    closed: RefCell::default(),
                    erased: RefCell::default(),
                    kept: RefCell::default(),
                    checked: RefCell::default(),
                    written: Cell::new(false),
                    steps: Cell::new(0),
                    fuel,
                    depth: Cell::new(0),
                    last: Cell::new(usize::MAX),
                    deep: RefCell::default(),
                    deepest: (stack / LEVEL) as u32,
                };
                run(&machine)
            });
            handle.ok().map(|handle| handle.join().unwrap_or_else(|panic| std::panic::resume_unwind(panic)))
        });
        match spawned {
            Some(out) => return Ok(out),
            None if stack > LEAST_STACK => stack /= 2,
            None => return stuck("no stack for the run"),
        }
    }
}

impl<'a> Machine<'a> {
    /// The position in Ψ of the definition the run entered last: where a
    /// stuck run was, near enough to name.
    pub fn last_entered(&self) -> Option<usize> {
        let deep = self.deep.borrow();
        match deep.iter().max_by_key(|(_, count)| **count) {
            Some((at, _)) => Some(*at),
            None => Some(self.last.get()).filter(|at| *at != usize::MAX),
        }
    }

    /// The steps taken so far.
    pub fn steps(&self) -> u64 {
        self.steps.get()
    }

    // ---- erasure ----------------------------------------------------------

    /// The position in Ψ a reference read under a prefix of `prefix`
    /// bindings names.
    fn position(&self, var: GlobalVar, prefix: usize) -> Option<usize> {
        match var.view() {
            GlobalRef::Const(p) => Some(p as usize),
            GlobalRef::Var(i) => prefix.checked_sub(1 + i as usize),
        }
    }

    fn body(&self, at: usize) -> Res<Rc<Code>> {
        if let Some(code) = self.codes.borrow().get(&at) {
            return Ok(code.clone());
        }
        let binding = self.psi.reference(at).and_then(|var| self.psi.lookup(var));
        let code = match binding {
            Some((_, GlobalBinding::Tm { body: Some(body), .. })) => self.erase(body, at),
            Some((_, GlobalBinding::Tm { body: None, .. })) => Rc::new(Code::Stuck("a declaration without a body")),
            _ => Rc::new(Code::Unit),
        };
        self.codes.borrow_mut().insert(at, code.clone());
        Ok(code)
    }

    fn erase(&self, t: &Shared<Term>, prefix: usize) -> Rc<Code> {
        let key = (Shared::as_ptr(t) as usize, prefix);
        if let Some(code) = self.erased.borrow().get(&key) {
            return code.clone();
        }
        let code = Rc::new(self.erase_new(t, prefix));
        self.erased.borrow_mut().insert(key, code.clone());
        code
    }

    fn erase_built(&self, t: Term, prefix: usize) -> Rc<Code> {
        let t = Shared::new(t);
        self.kept.borrow_mut().push(Shared::clone(&t));
        self.erase(&t, prefix)
    }

    fn erase_new(&self, t: &Shared<Term>, prefix: usize) -> Code {
        let e = |t: &Shared<Term>| self.erase(t, prefix);
        match &**t {
            Term::Var(v) => Code::Var(v.0),
            Term::Zero => Code::Nat(0),
            Term::NatLit(n) => match n.as_u128() {
                Some(n) => Code::Nat(n),
                None => Code::Stuck("a numeral past 128 bits"),
            },
            Term::Succ(p) => Code::Succ(e(p)),
            Term::ElimNat { base, step, scrut, .. } => Code::ElimNat { base: e(base), step: e(step), scrut: e(scrut), owner: prefix },
            Term::J { case, .. } => return self.erase_new(case, prefix),
            Term::Squash { tm, .. } => return self.erase_new(tm, prefix),
            Term::ElimSquash { case, scrut, .. } => Code::Let { bound: e(scrut), body: e(case) },
            Term::VecLit { level, elem, zero, one, width, bits } => {
                let chain = self.erase_built(term::vec_lit_chain(level, elem, zero, one, *width, *bits), prefix);
                Code::Let { bound: chain, body: Rc::new(Code::Var(0)) }
            }
            Term::VecItems { level, elem, items, from } => match term::vec_items_live(items, *from) {
                Some(live) => {
                    let chain = self.erase_built(term::vec_items_chain(level, elem, live), prefix);
                    Code::Let { bound: chain, body: Rc::new(Code::Var(0)) }
                }
                None => Code::Stuck("a vector literal read past its end"),
            },
            Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => Code::Pair(e(fst), e(snd)),
            Term::Fst { pair, .. } | Term::FstAt { pair } => Code::Fst(e(pair)),
            Term::Snd { pair, .. } | Term::SndAt { pair } => Code::Snd(e(pair)),
            Term::Inl { val, .. } | Term::InlAt { val, .. } => Code::Inl(e(val)),
            Term::Inr { val, .. } | Term::InrAt { val, .. } => Code::Inr(e(val)),
            Term::Case { case_l, case_r, scrut, .. } => Code::Case { left: e(case_l), right: e(case_r), scrut: e(scrut) },
            Term::Sup { label, children, .. } | Term::Supf { label, children, .. } | Term::Supi { label, children, .. } => {
                Code::Sup(e(label), e(children))
            }
            Term::ElimW { step, scrut, .. } => Code::Elim { tree: Tree::Function, step: e(step), scrut: e(scrut), owner: prefix },
            Term::ElimWf { step, scrut, .. } | Term::ElimIWf { step, scrut, .. } => {
                Code::Elim { tree: Tree::Tuple, step: e(step), scrut: e(scrut), owner: prefix }
            }
            Term::Lam { body, .. } => Code::Lam(e(body)),
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => Code::App(e(fun), e(arg)),
            Term::ULam { body, .. } | Term::CtxLam { body, .. } | Term::TyLam { body, .. } => return self.erase_new(body, prefix),
            Term::UApp { fun, .. } | Term::CtxApp { fun, .. } | Term::TyApp { fun, .. } => return self.erase_new(fun, prefix),
            Term::GlobalTm { var, subst } => {
                let Some(at) = self.position(*var, prefix) else { return Code::Stuck("a global out of scope") };
                let args: Box<[Rc<Code>]> = subst.terms.iter().map(e).collect();
                match self.prims.get(&at) {
                    Some(prim) if args.len() == prim.arity() => Code::Prim(*prim, at, args, Cell::new(0)),
                    // A definition that is a function of its numbers: the
                    // same, under as many binders.
                    Some(prim) if args.is_empty() => {
                        let arity = prim.arity() as u32;
                        let read = (0..arity).map(|i| Rc::new(Code::Var(arity - 1 - i))).collect();
                        let mut code = Code::Prim(*prim, at, read, Cell::new(0));
                        for _ in 0..arity {
                            code = Code::Lam(Rc::new(code));
                        }
                        code
                    }
                    _ => Code::Global(at, args, Linked::default()),
                }
            }
            Term::Triv { .. } | Term::Refl { .. } | Term::SRefl { .. } => Code::Unit,
            Term::TmNat
            | Term::TmPi { .. }
            | Term::TmTy(_)
            | Term::TmId { .. }
            | Term::TmSEq { .. }
            | Term::TmSEmpty { .. }
            | Term::TmSquash { .. }
            | Term::TmSigma { .. }
            | Term::TmUnit { .. }
            | Term::TmEmpty { .. }
            | Term::TmSum { .. }
            | Term::TmW { .. }
            | Term::TmVec { .. }
            | Term::TmFin { .. }
            | Term::TmWf { .. }
            | Term::TmDVec { .. }
            | Term::TmIWf { .. }
            | Term::TmM { .. } => Code::Unit,
            Term::ElimEmpty { .. } | Term::ElimSEmpty { .. } | Term::UnsquashEmpty { .. } => {
                Code::Stuck("a case that cannot happen was reached")
            }
            Term::Corec { .. } | Term::Out { .. } => Code::Stuck("codata"),
            Term::BoxTy(_)
            | Term::BoxTm(_)
            | Term::LetBoxTy { .. }
            | Term::LetBoxTm { .. }
            | Term::ElimCodeTy { .. }
            | Term::ElimCodeTm { .. } => Code::Stuck("quoted code"),
        }
    }

    // ---- the machine ------------------------------------------------------

    fn tick(&self) -> Res<()> {
        let steps = self.steps.get() + 1;
        self.steps.set(steps);
        if steps > self.fuel { stuck("the run passed its step bound") } else { Ok(()) }
    }

    fn lookup(&self, env: &Env, index: u32) -> Res<Thunk> {
        let mut at = env;
        let mut left = index;
        loop {
            let Some(node) = at else { return stuck("a variable outside its environment") };
            if left == 0 {
                return Ok(node.value.clone());
            }
            left -= 1;
            at = &node.rest;
        }
    }

    /// `code` in `env`, for when it is read.
    fn delay(&self, code: &Rc<Code>, env: &Env) -> Res<Thunk> {
        Ok(match &**code {
            Code::Var(i) => self.lookup(env, *i)?,
            Code::Nat(n) => done(Val::Nat(*n)),
            Code::Unit => done(Val::Unit),
            Code::Lam(body) => done(Val::Clo(body.clone(), env.clone())),
            Code::Global(at, args, linked) if args.is_empty() => linked.value.get_or_init(|| self.closed(*at)).clone(),
            _ => Rc::new(ThunkCell(RefCell::new(State::Lazy(code.clone(), env.clone())))),
        })
    }

    /// A definition of no arguments: one value for the whole run.
    fn closed(&self, at: usize) -> Thunk {
        if let Some(thunk) = self.closed.borrow().get(&at) {
            return thunk.clone();
        }
        let call = Rc::new(Code::Global(at, Box::new([]), Linked::default()));
        let thunk: Thunk = Rc::new(ThunkCell(RefCell::new(State::Lazy(call, None))));
        self.closed.borrow_mut().insert(at, thunk.clone());
        thunk
    }

    /// The value of a thunk, computed the first time.
    pub fn force(&self, thunk: &Thunk) -> Res<Val> {
        let state = {
            let mut cell = thunk.0.borrow_mut();
            if let State::Done(value) = &*cell {
                return Ok(value.clone());
            }
            std::mem::replace(&mut *cell, State::Busy)
        };
        let value = match state {
            State::Lazy(code, env) => match &*code {
                // A closed definition's thunk is the call itself: run its body.
                Code::Global(at, args, _) if args.is_empty() => self.eval(self.body(*at)?, None)?,
                _ => self.eval(code, env)?,
            },
            State::NatRec(node, env, n) => self.elim_nat(&node, env, n)?,
            State::Busy => return stuck("a value that reads itself"),
            State::Done(_) => unreachable!("returned above"),
        };
        *thunk.0.borrow_mut() = State::Done(value.clone());
        Ok(value)
    }

    fn elim_nat(&self, node: &Rc<Code>, env: Env, n: u128) -> Res<Val> {
        let Code::ElimNat { base, step, .. } = &**node else { return stuck("not an elim_Nat") };
        if n == 0 {
            return self.eval(base.clone(), env);
        }
        let rec = Rc::new(ThunkCell(RefCell::new(State::NatRec(node.clone(), env.clone(), n - 1))));
        self.eval(step.clone(), push(&push(&env, done(Val::Nat(n - 1))), rec))
    }

    fn nat_of(&self, code: &Rc<Code>, env: &Env) -> Res<u128> {
        match self.eval(code.clone(), env.clone())? {
            Val::Nat(n) => Ok(n),
            other => met("a number", &other),
        }
    }

    /// The step of a tree's eliminator at `scrut`, and the environment it
    /// runs in.
    fn elim_tree(&self, tree: Tree, step: &Rc<Code>, env: &Env, scrut: Val) -> Res<(Rc<Code>, Env)> {
        let Val::Sup(label, children) = scrut else { return met("a tree", &scrut) };
        let ih = done(Val::Ih(Rc::new(IhCell { tree, step: step.clone(), env: env.clone(), children: children.clone() })));
        Ok((step.clone(), push(&push(&push(env, label), children), ih)))
    }

    /// The child an induction hypothesis is asked about.
    fn child(&self, cell: &IhCell, which: Thunk) -> Res<Val> {
        match cell.tree {
            Tree::Function => match self.force(&cell.children)? {
                Val::Clo(body, env) => self.eval(body, push(&env, which)),
                _ => stuck("a tree's children were expected to be a function"),
            },
            Tree::Tuple => {
                let mut index = self.force(&which)?;
                let mut tuple = self.force(&cell.children)?;
                loop {
                    let Val::Pair(first, rest) = tuple else { return stuck("a tree's children were expected to be a tuple") };
                    match index {
                        Val::Inl(_) => return self.force(&first),
                        Val::Inr(next) => {
                            index = self.force(&next)?;
                            tuple = self.force(&rest)?;
                        }
                        _ => return stuck("a position among a tree's children was expected"),
                    }
                }
            }
        }
    }

    fn eval(&self, code: Rc<Code>, env: Env) -> Res<Val> {
        let depth = self.depth.get();
        if depth >= self.deepest {
            return stuck("the run nested too deeply");
        }
        self.depth.set(depth + 1);
        if depth >= self.deepest / 2 {
            *self.deep.borrow_mut().entry(self.last.get()).or_default() += 1;
        }
        let out = self.eval_loop(code, env);
        self.depth.set(depth);
        out
    }

    fn eval_loop(&self, mut code: Rc<Code>, mut env: Env) -> Res<Val> {
        loop {
            self.tick()?;
            let now = code.clone();
            match &*now {
                Code::Var(i) => return self.force(&self.lookup(&env, *i)?),
                Code::Lam(body) => return Ok(Val::Clo(body.clone(), env)),
                Code::App(fun, arg) => {
                    let fun = self.eval(fun.clone(), env.clone())?;
                    let arg = self.delay(arg, &env)?;
                    match fun {
                        Val::Clo(body, closed) => {
                            env = push(&closed, arg);
                            code = body;
                        }
                        Val::Ih(cell) => {
                            let child = self.child(&cell, arg)?;
                            (code, env) = self.elim_tree(cell.tree, &cell.step, &cell.env, child)?;
                        }
                        other => return met("a function", &other),
                    }
                }
                Code::Global(at, args, linked) => {
                    if args.is_empty() {
                        return self.force(linked.value.get_or_init(|| self.closed(*at)));
                    }
                    let mut callee = None;
                    for arg in args.iter() {
                        callee = push(&callee, self.delay(arg, &env)?);
                    }
                    env = callee;
                    code = match linked.body.get() {
                        Some(body) => body.clone(),
                        None => {
                            let body = self.body(*at)?;
                            let _ = linked.body.set(body.clone());
                            body
                        }
                    };
                    self.last.set(*at);
                }
                Code::Prim(prim, at, args, known) => {
                    if known.get() == 0 && !self.written.get() {
                        known.set(if self.trusted(*prim, *at)? { 1 } else { 2 });
                    }
                    if self.written.get() || known.get() != 1 {
                        let mut numbers = [0u128; 2];
                        for (number, arg) in numbers.iter_mut().zip(args.iter()) {
                            *number = self.nat_of(arg, &env)?;
                        }
                        return self.written_at(*at, &numbers[..args.len()]);
                    }
                    let a = self.nat_of(&args[0], &env)?;
                    let b = if args.len() > 1 { self.nat_of(&args[1], &env)? } else { 0 };
                    return self.prim(*prim, *at, a, b);
                }
                Code::Nat(n) => return Ok(Val::Nat(*n)),
                Code::Succ(pred) => {
                    return match self.nat_of(pred, &env)?.checked_add(1) {
                        Some(n) => Ok(Val::Nat(n)),
                        None => stuck("a number past 128 bits"),
                    };
                }
                Code::ElimNat { base, step, scrut, owner } => {
                    self.last.set(*owner);
                    let n = self.nat_of(scrut, &env)?;
                    if n == 0 {
                        code = base.clone();
                    } else {
                        let rec = Rc::new(ThunkCell(RefCell::new(State::NatRec(now.clone(), env.clone(), n - 1))));
                        env = push(&push(&env, done(Val::Nat(n - 1))), rec);
                        code = step.clone();
                    }
                }
                Code::Pair(first, second) => return Ok(Val::Pair(self.delay(first, &env)?, self.delay(second, &env)?)),
                Code::Fst(pair) => {
                    return match self.eval(pair.clone(), env)? {
                        Val::Pair(first, _) => self.force(&first),
                        other => met("a pair", &other),
                    };
                }
                Code::Snd(pair) => {
                    return match self.eval(pair.clone(), env)? {
                        Val::Pair(_, second) => self.force(&second),
                        other => met("a pair", &other),
                    };
                }
                Code::Inl(value) => return Ok(Val::Inl(self.delay(value, &env)?)),
                Code::Inr(value) => return Ok(Val::Inr(self.delay(value, &env)?)),
                Code::Case { left, right, scrut } => match self.eval(scrut.clone(), env.clone())? {
                    Val::Inl(value) => {
                        env = push(&env, value);
                        code = left.clone();
                    }
                    Val::Inr(value) => {
                        env = push(&env, value);
                        code = right.clone();
                    }
                    other => return met("a sum", &other),
                },
                Code::Sup(label, children) => return Ok(Val::Sup(self.delay(label, &env)?, self.delay(children, &env)?)),
                Code::Elim { tree, step, scrut, owner } => {
                    self.last.set(*owner);
                    let scrut = self.eval(scrut.clone(), env.clone())?;
                    (code, env) = self.elim_tree(*tree, step, &env, scrut)?;
                }
                Code::Let { bound, body } => {
                    env = push(&env, self.delay(bound, &env)?);
                    code = body.clone();
                }
                Code::Unit => return Ok(Val::Unit),
                Code::Stuck(why) => return stuck(*why),
            }
        }
    }

    // ---- named arithmetic -------------------------------------------------

    /// The definition at `at` as written, at two numbers.
    fn as_written(&self, at: usize, arity: usize, a: u128, b: u128) -> Res<Val> {
        let was = self.written.replace(true);
        let out = self.written_at(at, &[a, b][..arity]);
        self.written.set(was);
        out
    }

    /// A definition's body at numbers: as many as its context has are its
    /// environment, and it is applied to the rest.
    fn written_at(&self, at: usize, numbers: &[u128]) -> Res<Val> {
        self.last.set(at);
        let taken = match self.psi.reference(at).and_then(|var| self.psi.lookup(var)) {
            Some((_, GlobalBinding::Tm { ctx, .. })) => ctx.len().min(numbers.len()),
            _ => 0,
        };
        let mut env = None;
        for n in &numbers[..taken] {
            env = push(&env, done(Val::Nat(*n)));
        }
        let mut value = self.eval(self.body(at)?, env)?;
        for n in &numbers[taken..] {
            let Val::Clo(body, closed) = value else { return stuck("a function was expected") };
            value = self.eval(body, push(&closed, done(Val::Nat(*n))))?;
        }
        Ok(value)
    }

    /// Whether two values are the same data, read to the bottom: only for
    /// the small answers of a two-valued definition.
    fn alike(&self, a: &Val, b: &Val, budget: &mut u32) -> Res<bool> {
        if *budget == 0 {
            return Ok(false);
        }
        *budget -= 1;
        let both = |x: &Thunk, y: &Thunk, budget: &mut u32| -> Res<bool> { self.alike(&self.force(x)?, &self.force(y)?, budget) };
        Ok(match (a, b) {
            (Val::Nat(x), Val::Nat(y)) => x == y,
            (Val::Unit, Val::Unit) => true,
            (Val::Inl(x), Val::Inl(y)) | (Val::Inr(x), Val::Inr(y)) => both(x, y, budget)?,
            (Val::Pair(x, p), Val::Pair(y, q)) | (Val::Sup(x, p), Val::Sup(y, q)) => both(x, y, budget)? && both(p, q, budget)?,
            _ => false,
        })
    }

    /// Whether the definition at `at` does on small numbers what `prim`
    /// does, found once; with a two-valued one's two answers kept.
    fn trusted(&self, prim: Prim, at: usize) -> Res<bool> {
        if let Some(known) = self.checked.borrow().get(&at) {
            return Ok(known.is_some());
        }
        // While it is being compared, the definition runs as written.
        self.checked.borrow_mut().insert(at, None);
        const SAMPLES: [(u128, u128); 9] = [(0, 0), (0, 1), (1, 0), (1, 1), (3, 2), (2, 5), (7, 7), (12, 4), (9, 10)];
        let run = |a, b| self.as_written(at, prim.arity(), a, b);
        let verdict = if prim.two_valued() {
            let (yes, no) = match prim {
                Prim::Equal => (run(0, 0), run(0, 1)),
                Prim::LessOrEqual => (run(0, 0), run(1, 0)),
                Prim::Odd => (run(1, 0), run(0, 0)),
                _ => (run(0, 1), run(0, 0)),
            };
            match (yes, no) {
                (Ok(yes), Ok(no)) if !self.alike(&yes, &no, &mut 64)? => {
                    let mut agrees = true;
                    for (a, b) in SAMPLES {
                        let want = if prim.holds(a, b) { &yes } else { &no };
                        agrees &= matches!(run(a, b), Ok(got) if self.alike(&got, want, &mut 64)?);
                    }
                    agrees.then_some((yes, no))
                }
                _ => None,
            }
        } else {
            let agrees = SAMPLES.iter().all(|&(a, b)| matches!(run(a, b), Ok(Val::Nat(n)) if prim.number(a, b) == Some(n)));
            agrees.then_some((Val::Unit, Val::Unit))
        };
        let trusted = verdict.is_some();
        self.checked.borrow_mut().insert(at, verdict);
        Ok(trusted)
    }

    fn prim(&self, prim: Prim, at: usize, a: u128, b: u128) -> Res<Val> {
        if prim.two_valued() {
            let checked = self.checked.borrow();
            let Some(Some((yes, no))) = checked.get(&at) else { return stuck("a named definition that was not compared") };
            return Ok(if prim.holds(a, b) { yes.clone() } else { no.clone() });
        }
        match prim.number(a, b) {
            Some(n) => Ok(Val::Nat(n)),
            None => stuck("a number past 128 bits"),
        }
    }

    // ---- reading answers --------------------------------------------------

    /// The definition at position `at` of Ψ, taking no arguments.
    pub fn global(&self, at: usize) -> Thunk {
        self.closed(at)
    }

    /// A number, where it fits a word.
    pub fn nat(&self, thunk: &Thunk) -> Res<u64> {
        match self.force(thunk)? {
            Val::Nat(n) => u64::try_from(n).or_else(|_| stuck("a numeral past 64 bits")),
            _ => stuck("a Nat that is not a numeral"),
        }
    }

    /// A tuple's components: a chain of pairs ended by `⟨⟩`.
    pub fn spine(&self, thunk: &Thunk) -> Res<Vec<Thunk>> {
        let mut out = Vec::new();
        let mut value = self.force(thunk)?;
        loop {
            match value {
                Val::Unit => return Ok(out),
                Val::Pair(first, rest) => {
                    out.push(first);
                    value = self.force(&rest)?;
                }
                _ => return stuck("a tuple that is not a pair chain"),
            }
        }
    }

    /// `(constructor index, fields, recursive children)` of a value of a
    /// two-constructor inductive, as the elaborator lowers one.
    pub fn ctor(&self, thunk: &Thunk) -> Res<(usize, Vec<Thunk>, Vec<Thunk>)> {
        let (label, children) = match self.force(thunk)? {
            Val::Sup(label, children) => (self.force(&label)?, self.spine(&children)?),
            other => (other, vec![]),
        };
        let (index, payload) = match label {
            Val::Inl(payload) => (0, payload),
            Val::Inr(payload) => (1, payload),
            _ => return stuck("a value that is not a constructor"),
        };
        let Val::Pair(_, fields) = self.force(&payload)? else { return stuck("a constructor payload that is not a pair") };
        Ok((index, self.spine(&fields)?, children))
    }
}
