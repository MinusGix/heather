//! Proof-position relational congruence over resolved, non-dependent terms.
//! Reconstruction uses ordinary class projections and ordinary local goals.
use std::cell::RefCell;
use std::collections::HashMap;
use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_syntax::{parse_file, Expr, Item, Span};

use crate::oracle::Unfold;
use crate::{err, goals, Alias, Cx, ElabError, Elaborator, TyVar, R};
use crate::app_unify::AppUnify;

fn expression(text: &str, span: Span) -> R<Expr> {
    let source = format!("fn generated() -> Type {{ {text} }}");
    let mut file = parse_file(&source).map_err(|e| ElabError::Elab { msg: e.msg, span })?;
    let Some(Item::Decl(d)) = file.items.pop() else {
        unreachable!()
    };
    Ok(*d.body.result)
}

/// A homogeneous binary relation applied to two terms, `R(left, right)`:
/// the relation term, the two sides, and their common carrier.
pub(crate) struct Relation {
    pub(crate) head: Rc<Term>,
    pub(crate) left: Rc<Term>,
    pub(crate) right: Rc<Term>,
    pub(crate) carrier: Rc<Type>,
    pub(crate) level: Level,
}

impl Relation {
    /// `ty` read as written as `R(left, right)` with both domains of `R` the
    /// same carrier; `None` for anything else, an `=` among them.
    pub(crate) fn of_type(e: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> Option<Relation> {
        if let Some(mut rel) = Relation::of_family(ty) {
            // The code as emission spells it, `Eutt<R>(E, a, b)`, so an
            // obligation over the relation reads as the family.
            let Term::Lam { body: inner, .. } = &*rel.head else { unreachable!("built as a λ") };
            let Term::Lam { body: code, .. } = &**inner else { unreachable!("built as a λ") };
            let Type::M { sig, .. } = ty else { unreachable!("a family") };
            let mut here = cx.clone();
            here.push("__a".into(), (*rel.carrier).clone(), rel.level.clone());
            here.push("__b".into(), rel.carrier.shift_local(1), rel.level.clone());
            let decoded = Type::El { level: sig.family_level(), tm: Rc::clone(code) };
            let holds = sig.family_level();
            if let Ok(t) = crate::expr::ExprElab::quote_type_at(e, &here, &e.whnf(&here, &decoded, span).unwrap_or(decoded), &holds, &holds, span) {
                let Term::Lam { dom_level, cod_level, dom, .. } = &*rel.head else { unreachable!() };
                let Term::Lam { dom_level: il, cod_level: ic, dom: id, .. } = &**inner else { unreachable!() };
                let inner = Term::Lam { dom_level: il.clone(), cod_level: ic.clone(), dom: Rc::clone(id), body: Rc::new(t) };
                rel.head = Rc::new(Term::Lam { dom_level: dom_level.clone(), cod_level: cod_level.clone(), dom: Rc::clone(dom), body: Rc::new(inner) });
            }
            return Some(rel);
        }
        let Type::El { tm, .. } = ty else { return None };
        let (fun, right) = crate::spelling::app_of(tm)?;
        let (head, left) = crate::spelling::app_of(fun)?;
        // The two domains: stated by an `app` node, the head's for an
        // `app@` one (`docs/app-by-head-type-design.md` §6.2).
        let (first, dom) = match (fun.as_ref(), tm.as_ref()) {
            (
                Term::App { dom: first, dom_level: fl, .. },
                Term::App { dom, dom_level, .. },
            ) => ((first.clone(), fl.clone()), (dom.clone(), dom_level.clone())),
            _ => {
                let doms = AppUnify(e).app_domains(cx, tm, span).unwrap_or_default();
                let [.., first, dom] = doms.as_slice() else {
                    return None;
                };
                (first.clone(), dom.clone())
            }
        };
        (first.0 == dom.0).then(|| Relation {
            head: head.clone(),
            left: left.clone(),
            right: right.clone(),
            carrier: dom.0,
            level: dom.1,
        })
    }
}

impl Relation {
    /// A goal at an indexed codata family whose last two indices are the
    /// sides, `Eutt<R>(E, t, u)` (docs/equation-rewrite-design.md §11): the
    /// family lowers to `M(…)(⟨…, t, u⟩)`, not to an application, so its
    /// relation is the λ `λ a b. ⌜M(…)(⟨…, a, b⟩)⌝`, which converts with a
    /// library's name for it (`Eutt::Rel<R>(E)`).
    pub(crate) fn of_family(ty: &Type) -> Option<Relation> {
        let (sig, descents, pair) = family_sides(ty)?;
        let Term::Pair { fst_level, fst_ty, fst, snd, .. } = pair else { unreachable!("a pair") };
        let holds = sig.family_level();
        let Type::M { index, .. } = ty else { unreachable!("a family") };
        let body = Type::M {
            sig: sig.shift_local(2),
            index: Rc::new(with_last_pair(&index.shift_local(2), descents, Rc::new(Term::Var(LocalVar(1))), Rc::new(Term::Var(LocalVar(0))))),
        };
        let code = crate::code::code_of(&body)?;
        let inner = Term::Lam {
            dom_level: fst_level.clone(),
            cod_level: Level::succ(holds.clone()),
            dom: Rc::new(fst_ty.shift_local(1)),
            body: Rc::new(code),
        };
        let head = Term::Lam {
            dom_level: fst_level.clone(),
            cod_level: Level::join(fst_level.clone(), Level::succ(holds)),
            dom: Rc::clone(fst_ty),
            body: Rc::new(inner),
        };
        Some(Relation {
            head: Rc::new(head),
            left: Rc::clone(fst),
            right: Rc::clone(snd),
            carrier: Rc::clone(fst_ty),
            level: fst_level.clone(),
        })
    }

    /// `ty`, a relation application [`Relation::of_type`] read, with its two
    /// sides replaced: the application's last two arguments, or a family's
    /// last two indices.
    pub(crate) fn with_sides(ty: &Type, left: Rc<Term>, right: Rc<Term>) -> Option<Type> {
        match ty {
            Type::M { sig, index } => {
                let (_, descents, _) = family_sides(ty)?;
                Some(Type::M { sig: Rc::clone(sig), index: Rc::new(with_last_pair(index, descents, left, right)) })
            }
            Type::El { level, tm } => {
                let (fun, _) = crate::spelling::app_of(tm)?;
                let (head, _) = crate::spelling::app_of(fun)?;
                let fun = Rc::new(Term::AppAt { fun: Rc::clone(head), arg: left });
                Some(Type::El { level: level.clone(), tm: Rc::new(Term::AppAt { fun, arg: right }) })
            }
            _ => None,
        }
    }
}

/// The signature of an indexed codata family `ty`, how many pairs down its
/// index tuple the last two indices sit, and that pair, when the two have
/// one type, the later not depending on the earlier.
fn family_sides(ty: &Type) -> Option<(&Rc<heather_kernel::term::MSig>, usize, &Term)> {
    let Type::M { sig, index } = ty else { return None };
    // How many index binders: one per `Σ` down the telescope, plus the last.
    let mut n = 1;
    let mut idx = &*sig.idx;
    while let Type::Sigma { snd, .. } = idx {
        n += 1;
        idx = snd;
    }
    if n < 2 {
        return None;
    }
    let mut pair = &**index;
    for _ in 0..n - 2 {
        let Term::Pair { snd, .. } = pair else { return None };
        pair = snd;
    }
    let Term::Pair { fst_ty, snd_ty, .. } = pair else { return None };
    let lowered = snd_ty.inst_top(0, &Term::Zero);
    (lowered.shift_local(1) == **snd_ty && lowered == **fst_ty).then_some((sig, n - 2, pair))
}

/// `index` with the pair `descents` pairs down replaced by `⟨left, right⟩`.
fn with_last_pair(index: &Term, descents: usize, left: Rc<Term>, right: Rc<Term>) -> Term {
    let Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } = index else {
        unreachable!("family_sides found the pair")
    };
    let (fst, snd) = if descents == 0 {
        (left, right)
    } else {
        (Rc::clone(fst), Rc::new(with_last_pair(snd, descents - 1, left, right)))
    };
    Term::Pair {
        fst_level: fst_level.clone(),
        snd_level: snd_level.clone(),
        fst_ty: Rc::clone(fst_ty),
        snd_ty: Rc::clone(snd_ty),
        fst,
        snd,
    }
}

fn relation(e: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> R<Relation> {
    Relation::of_type(e, cx, ty, span).map_or_else(
        || err(
            "`rel_cong` needs a homogeneous binary relation application; native identity and dependent relations are outside this first fragment",
            span,
        ),
        Ok,
    )
}

/// One field of a local dictionary, already projected and already known to
/// take an argument: the projection term and the pieces of its `Π` type.
/// `None` where the field declined to project or is not a `Π`, which is still
/// a field the search *examines* (its budget counts declarations, not
/// candidates).
type Field = Option<(Rc<Term>, Level, Level, Rc<Type>, Rc<Type>)>;

struct Builder<'a> {
    e: &'a Elaborator,
    original: &'a Cx,
    cx: Cx,
    span: Span,
    relation: Relation,
    rel: String,
    carrier: String,
    witness: String,
    serial: usize,
    nodes: usize,
    goals: usize,
    derive: bool,
    /// The binders the walk is below, outermost first, each type scoped
    /// where its binder is: the λs of a consumer's argument, walked to a
    /// pointwise proof (`docs/equation-rewrite-design.md` §10.6).
    binders: Vec<(Rc<Type>, Level)>,
    /// The supplied proof's two sides at each depth below the binders,
    /// shifted once per depth.
    sides: Vec<(Rc<Term>, Rc<Term>)>,
    /// The projected fields of each dictionary reachable by name from
    /// `cx.dicts`, for this derivation's lifetime, per depth. Only the innermost binder
    /// of a name is ever searched (the `seen` set below), and the walk pushes
    /// nothing but freshly named aliases, so a name's projections are the
    /// same term at every search — while recomputing them is the `Σ`-spine
    /// walk of `project_field`, once per field per search
    /// (issues/relational-derivation-cost.md).
    fields: RefCell<HashMap<(String, usize), Rc<Vec<Field>>>>,
}

impl Builder<'_> {
    fn fresh(&mut self) -> String {
        loop {
            let name = format!("__rel_cong_{}", self.serial);
            self.serial += 1;
            if !self.cx.names.contains(&name)
                && !self.cx.aliases.iter_inner().any(|a| a.name == name)
                && !self.cx.tyvars.iter_inner().any(|a| a.name == name)
            {
                return name;
            }
        }
    }

    fn alias(&mut self, term: Rc<Term>, ty: Type, level: Level) -> String {
        let name = self.fresh();
        self.cx.aliases.push(Rc::new(Alias {
            name: name.clone(),
            depth: self.cx.names.len(),
            term,
            ty,
            level,
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));
        name
    }

    fn value(&mut self, value: Rc<Term>) -> String {
        let carrier = self.relation.carrier.shift_local(self.binders.len() as u32);
        self.alias(value, carrier, self.relation.level.clone())
    }

    /// A type variable for binder type `dom`, scoped where the walk is.
    fn domain(&mut self, dom: &Rc<Type>, level: &Level) -> String {
        let name = self.fresh();
        self.cx.tyvars.push(TyVar {
            name: name.clone(),
            ty: (**dom).clone(),
            level: level.clone(),
            depth: self.cx.names.len(),
        });
        name
    }

    /// The supplied proof's left and right sides at the walk's depth.
    fn sides(&mut self) -> (Rc<Term>, Rc<Term>) {
        let d = self.binders.len();
        while self.sides.len() <= d {
            let by = self.sides.len() as u32;
            let shifted = (
                Rc::new(self.relation.left.shift_local(by)),
                Rc::new(self.relation.right.shift_local(by)),
            );
            self.sides.push(shifted);
        }
        self.sides[d].clone()
    }

    fn core_checks(&self, term: &Term, ty: &Type, level: &Level) -> bool {
        // A synchronous kernel check, charged to the kernel-gate timer like
        // the deferred ones: the kernel's own counter column already says it
        // ran, and without the bracket this was half of a `rel_derive`
        // theorem's unattributed body time (issues/relational-derivation-cost.md).
        crate::stats::timed(crate::stats::Timer::KernelGate, || {
            self.e
                .kernel_check_term(
                    self.e.semantic_oracle().world(),
                    heather_kernel::layer::Layer::Prog,
                    &self.cx.gamma,
                    term,
                    ty,
                    level,
                )
                .is_ok()
        })
    }

    /// [`Builder::core_checks`]'s conversion half, in the same world and at
    /// the same fuel: a candidate whose own type does not convert to the goal
    /// cannot check at it.
    fn core_converts(&self, ty: &Type, goal: &Type, level: &Level) -> bool {
        crate::stats::timed(crate::stats::Timer::KernelGate, || {
            self.e
                .semantic_oracle()
                .convert_type(
                    &self.cx.gamma,
                    heather_kernel::layer::Layer::Prog,
                    ty,
                    goal,
                    level,
                )
                .is_ok()
        })
    }

    fn type_of(&self, text: &str) -> R<(Type, Level)> {
        let source = format!("fn generated(x: {text}) -> Type {{ Type }}");
        let mut file = parse_file(&source).map_err(|e| ElabError::Elab {
            msg: e.msg,
            span: self.span,
        })?;
        let Some(Item::Decl(d)) = file.items.pop() else {
            unreachable!()
        };
        self.e.elab_ty(&self.cx, &d.params[0].ty)
    }

    fn resolve(&self, ty: &Type, level: &Level) -> Option<Term> {
        self.e.resolve_goal(
            &self.cx,
            ty,
            level,
            &self.e.display_type(if self.binders.is_empty() { self.original } else { &self.cx }, ty),
            None,
            self.span,
            &mut Vec::new(),
        )
    }

    /// The argument-taking fields of the dictionary bound to `name`, computed
    /// once per derivation (see [`Builder::fields`]). An empty vector stands
    /// for "no dictionary here": a name that does not resolve, or resolves
    /// away from its recorded class, is a settled answer too.
    fn dictionary_fields(&self, name: &str, class: &str) -> Rc<Vec<Field>> {
        // Per depth: below a binder the dictionary is the same one, shifted.
        let key = (name.to_string(), self.cx.names.len());
        if let Some(cached) = self.fields.borrow().get(&key) {
            return cached.clone();
        }
        let built = Rc::new(self.project_fields(name, class));
        self.fields.borrow_mut().insert(key, built.clone());
        built
    }

    fn project_fields(&self, name: &str, class: &str) -> Vec<Field> {
        let Ok((dict, ty, _)) = self.e.resolve_reading(&self.cx, name, self.span) else {
            return Vec::new();
        };
        let Some(ind) = self.e.display_tag_of(&ty) else {
            return Vec::new();
        };
        if self.e.key_of(class) != self.e.key_of(&ind.name) {
            return Vec::new();
        }
        let Some(ctor) = ind.ctors.first() else {
            return Vec::new();
        };
        let dict = Rc::new(dict);
        (0..ctor.fields.len())
            .map(|index| {
                let (field, field_ty, _) = self
                    .e
                    .project_field(&self.cx, &ind, &ty, dict.clone(), index, self.span)
                    .ok()?;
                let Type::Pi {
                    dom_level,
                    cod_level,
                    dom,
                    cod,
                } = field_ty
                else {
                    return None;
                };
                Some((Rc::new(field), dom_level, cod_level, dom, cod))
            })
            .collect()
    }

    // A family operation such as image(f, xs) has a fixed first argument.
    // Search only complete local dictionaries, applying at most one argument
    // to a field. The kernel checks the resulting candidate at the exact
    // compatibility goal; no field names or operation bodies are interpreted.
    fn family_certificate(&self, fixed: &Rc<Term>, goal: &Type, level: &Level) -> Option<Term> {
        let mut seen = std::collections::HashSet::new();
        let mut examined = 0;
        let mut found: Option<Term> = None;
        for d in self.cx.dicts.iter_inner() {
            if !seen.insert(d.name.clone()) {
                continue;
            }
            for field in self.dictionary_fields(&d.name, &d.class).iter() {
                examined += 1;
                if examined > 64 {
                    return None;
                }
                let Some((field, dom_level, cod_level, dom, cod)) = field else {
                    continue;
                };
                if !self.core_checks(fixed, dom, dom_level) {
                    continue;
                }
                // The candidate's own type, which is what the check below
                // has to convert to the goal. Converting it *first* is the
                // same question asked without re-checking the projection
                // chain the candidate is applied to, and most fields of a
                // laws dictionary take an operation and say something else
                // entirely about it (`member_image`, `image_union`), so they
                // fail here for a fraction of the check's cost. Conversion
                // is a necessary condition of the check, in the check's own
                // world and at the check's fuel: what it refuses, the kernel
                // refuses.
                let at_fixed =
                    cod.apply_local(&LocalSubst::id(&self.cx.gamma).extended(fixed.clone()));
                if !self.core_converts(&at_fixed, goal, level) {
                    continue;
                }
                let candidate = crate::spelling::checked_app(
                    field.clone(),
                    dom_level.clone(),
                    cod_level.clone(),
                    dom.clone(),
                    cod.clone(),
                    fixed.clone(),
                );
                if self.core_checks(&candidate, goal, level) {
                    if found.as_ref().is_some_and(|prior| prior != &candidate) {
                        return None;
                    }
                    found = Some(candidate);
                }
            }
        }
        found
    }

    fn evidence(&mut self, ty: Type, level: Level, label: &str) -> R<String> {
        let term = if let Some(term) = self.resolve(&ty, &level) {
            term
        } else {
            let tactic = if self.derive {
                "rel_derive"
            } else {
                "rel_cong"
            };
            self.goals += 1;
            // Below binders the statement mentions them: the goal is closed
            // over them, at the tactic's own context, and applied back
            // (`docs/equation-rewrite-design.md` §10.4).
            let (closed, closed_level) = self.binders.iter().rev().fold((ty.clone(), level.clone()), |(cod, cod_level), (dom, dom_level)| {
                let pi = Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: dom.clone(),
                    cod: Rc::new(cod),
                };
                (pi, Level::join(dom_level.clone(), cod_level))
            });
            let goal = RelationalProof(self.e).relation_obligation(self.original, tactic, label, self.goals - 1, closed, closed_level, self.span)?;
            let k = self.binders.len() as u32;
            (0..k).rev().fold(goal.shift_local(k), |fun, i| Term::AppAt {
                fun: Rc::new(fun),
                arg: Rc::new(Term::Var(LocalVar(i))),
            })
        };
        Ok(self.alias(Rc::new(term), ty, level))
    }

    // One transparent head-reduction step at a time. Re-entering walk gives
    // registered/local certificates priority at every exposed application.
    fn expand(&mut self, left: &Rc<Term>, right: &Rc<Term>, depth: usize) -> Option<R<String>> {
        let oracle = self.e.semantic_oracle();
        let (l, r) = crate::stats::timed(crate::stats::Timer::ElabWhnf, || {
            (
                oracle.unfold(&self.cx.gamma, left, Unfold::OneStep).next(),
                oracle.unfold(&self.cx.gamma, right, Unfold::OneStep).next(),
            )
        });
        if l.is_none() && r.is_none() {
            return None;
        }
        let l = l.map(Rc::new).unwrap_or_else(|| left.clone());
        let r = r.map(Rc::new).unwrap_or_else(|| right.clone());
        if l == *left && r == *right {
            return None;
        }
        Some(self.walk(l, r, depth + 1))
    }

    // Recognize only the resolved library combinator, never a spelling alone.
    fn choice(&self, term: &Term) -> Option<Vec<Rc<Term>>> {
        let mut args = Vec::new();
        let mut head = term;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(arg.clone());
            head = fun;
        }
        let (definition, _, _) = self
            .e
            .resolve(&self.cx, "relation_function::choose", self.span)
            .ok()?;
        if head != &definition || args.len() != 4 {
            return None;
        }
        args.reverse();
        Some(args[1..].to_vec())
    }

    fn branch(&mut self, left: &Rc<Term>, right: &Rc<Term>, depth: usize) -> R<Option<String>> {
        let (Some(l), Some(r)) = (self.choice(left), self.choice(right)) else {
            return Ok(None);
        };
        let (bool_ty, bool_level) = self.type_of("bool::Bool")?;
        let first = self.alias(l[0].clone(), bool_ty.clone(), bool_level.clone());
        let second = self.alias(r[0].clone(), bool_ty, bool_level);
        let same = if l[0] == r[0] {
            "refl".to_string()
        } else if let (
            Some((lf, lx)),
            Some((rf, rx)),
        ) = (crate::spelling::app_of(l[0].as_ref()), crate::spelling::app_of(r[0].as_ref()))
        {
            let (op_ty, op_level) = self.type_of(&format!("{} → bool::Bool", self.carrier))?;
            if lf == rf && self.core_checks(lf, &op_ty, &op_level) {
                let test = self.alias(lf.clone(), op_ty, op_level);
                let (ty, level) = self.type_of(&format!(
                    "relation_props::PreservesRelation({}, relation::RelId<bool::Bool>, {test})",
                    self.rel
                ))?;
                let stable = self.evidence(ty, level, "branch_choice")?;
                let x = self.value(lx.clone());
                let y = self.value(rx.clone());
                let h = self.walk(lx.clone(), rx.clone(), depth + 1)?;
                format!("{stable}({x}, {y}, {h})")
            } else {
                let (ty, level) = self.type_of(&format!("{first} = {second}"))?;
                self.evidence(ty, level, "branch_choice")?
            }
        } else {
            let (ty, level) = self.type_of(&format!("{first} = {second}"))?;
            self.evidence(ty, level, "branch_choice")?
        };
        let yes = self.value(l[1].clone());
        let yes2 = self.value(r[1].clone());
        let no = self.value(l[2].clone());
        let no2 = self.value(r[2].clone());
        let hy = self.walk(l[1].clone(), r[1].clone(), depth + 1)?;
        let hn = self.walk(l[2].clone(), r[2].clone(), depth + 1)?;
        Ok(Some(format!("relation_function::choose_respects({}, {first}, {second}, {same}, {yes}, {yes2}, {hy}, {no}, {no2}, {hn})", self.rel)))
    }

    /// A consumer of a λ whose body changed: `f(…, λ z. a, …)` against
    /// `f(…, λ z. b, …)`, nothing else different. The two λs are related
    /// pointwise, `Pointwise(R)` (one per binder they share), and the
    /// consumer crosses that by the evidence `rewrite` asks for,
    /// `PreservesRelation(Pointwise(R), R, λ g. f(…, g, …))`
    /// (`MonoidRel::range_pointwise` for `∑`; `docs/equation-rewrite-design.md`
    /// §10.2, §10.6). `None` for any other pair, and for a consumer that does
    /// not map such functions into the carrier.
    fn across(&mut self, left: &Rc<Term>, right: &Rc<Term>, depth: usize) -> R<Option<String>> {
        let (head, largs) = crate::spelling::app_spine(left);
        let (rhead, rargs) = crate::spelling::app_spine(right);
        if head != rhead || largs.len() != rargs.len() {
            return Ok(None);
        }
        let changed: Vec<usize> = (0..largs.len()).filter(|&j| largs[j] != rargs[j]).collect();
        let [i] = changed[..] else { return Ok(None) };
        let Some(over) = self.shared_binders(largs[i], rargs[i]) else {
            return Ok(None);
        };
        let mut input = self.rel.clone();
        let mut fun = self.carrier.clone();
        for (dom, level) in over.iter().rev() {
            let d = self.domain(dom, level);
            input = format!("relation_props::Pointwise<{d}, {fun}>({input})");
            fun = format!("{d} → {fun}");
        }
        let (fun_ty, fun_level) = self.type_of(&fun)?;
        let (op_ty, op_level) = self.type_of(&format!("({fun}) → {}", self.carrier))?;
        // `λ g. f(…, g, …)`, written as a λ wherever `g` sits, as the
        // library's rules state it.
        let body = largs.iter().enumerate().fold(Rc::new(head.shift_local(1)), |fun, (j, a)| {
            let arg = if j == i { Rc::new(Term::Var(LocalVar(0))) } else { Rc::new(a.shift_local(1)) };
            Rc::new(Term::AppAt { fun, arg })
        });
        let context = Term::Lam {
            dom_level: fun_level.clone(),
            cod_level: self.relation.level.clone(),
            dom: Rc::new(fun_ty.clone()),
            body,
        };
        if !self.core_checks(&context, &op_ty, &op_level) {
            return Ok(None);
        }
        let op = self.alias(Rc::new(context), op_ty, op_level);
        let (ty, level) = self.type_of(&format!(
            "relation_props::PreservesRelation({input}, {}, {op})",
            self.rel
        ))?;
        if self.derive && self.resolve(&ty, &level).is_none() {
            if let Some(result) = self.expand(left, right, depth) {
                return result.map(Some);
            }
        }
        let certificate = self.evidence(ty, level, "compatibility")?;
        let x = self.alias(largs[i].clone(), fun_ty.clone(), fun_level.clone());
        let y = self.alias(rargs[i].clone(), fun_ty, fun_level);
        let (h_ty, h_level) = self.type_of(&format!("{input}({x}, {y})"))?;
        let (proof, _) = self.pointwise(largs[i], rargs[i], over.len(), depth)?;
        let h = self.alias(Rc::new(proof), h_ty, h_level);
        Ok(Some(format!("{certificate}({x}, {y}, {h})")))
    }

    /// The binder types two λs share, outermost first, each scoped where the
    /// λs are: as many as both have with the same type. `None` for no λ, or
    /// a binder whose type mentions an earlier one: the pointwise relation is
    /// not dependent.
    fn shared_binders(&self, left: &Term, right: &Term) -> Option<Vec<(Rc<Type>, Level)>> {
        let mut over = Vec::new();
        let (mut l, mut r) = (left, right);
        while let (
            Term::Lam { dom_level, dom, body: lb, .. },
            Term::Lam { dom: rdom, body: rb, .. },
        ) = (l, r)
        {
            if dom != rdom {
                break;
            }
            let lowered = crate::strengthen_ty(&self.cx.gamma, dom, over.len() as u32)?;
            over.push((Rc::new(lowered), dom_level.clone()));
            l = lb;
            r = rb;
        }
        (!over.is_empty()).then_some(over)
    }

    /// `λ z₁ … zₖ. p : Pointwise(…Pointwise(R))(left, right)` for two λs
    /// sharing `k` binders, and the level of that type: `p : R(a, b)` is
    /// their bodies walked below the binders and elaborated there. Nothing
    /// made below is kept, since it mentions the binders; the proof is a
    /// term, aliased where the λs are.
    fn pointwise(&mut self, left: &Rc<Term>, right: &Rc<Term>, k: usize, depth: usize) -> R<(Term, Level)> {
        let (
            Term::Lam { dom_level, dom, body: a, .. },
            Term::Lam { body: b, .. },
        ) = (&**left, &**right)
        else {
            unreachable!("shared binders are λs")
        };
        let saved = self.cx.clone();
        let z = self.fresh();
        self.cx.push(z, (**dom).clone(), dom_level.clone());
        self.binders.push((dom.clone(), dom_level.clone()));
        let inner = if k > 1 {
            self.pointwise(a, b, k - 1, depth)
        } else {
            self.body(a, b, depth)
        };
        self.binders.pop();
        self.cx = saved;
        let (body, holds) = inner?;
        let level = Level::join(dom_level.clone(), holds.clone());
        Ok((
            Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: holds,
                dom: dom.clone(),
                body: Rc::new(body),
            },
            level,
        ))
    }

    /// `p : R(a, b)` below the binders, elaborated there.
    fn body(&mut self, a: &Rc<Term>, b: &Rc<Term>, depth: usize) -> R<(Term, Level)> {
        let text = self.walk(a.clone(), b.clone(), depth + 1)?;
        let x = self.value(a.clone());
        let y = self.value(b.clone());
        let (ty, level) = self.type_of(&format!("{}({x}, {y})", self.rel))?;
        let expr = expression(&text, self.span)?;
        let term = self.e.generated_scope(|e| e.elab_check(&self.cx, &expr, &ty, &level))?;
        Ok((term, level))
    }

    /// Both sides as one constructor of an inductive type applied to one or
    /// two fields of the carrier: a context like a function's, whose
    /// compatibility evidence is registered at the constructor's name
    /// (`Respects2<…>(R, R, R, T::C)`, or `PreservesRelation(R, R, T::C)`
    /// for one field). A lowered constructor value is not an application,
    /// so the readers above never see it
    /// (issues/rel-cong-under-constructors.md).
    fn under_constructor(&mut self, left: &Rc<Term>, right: &Rc<Term>, depth: usize) -> R<Option<String>> {
        let Some((ind, i, lfields)) = self.e.view_ctor(&self.cx, left) else {
            return Ok(None);
        };
        let Some((rind, j, rfields)) = self.e.view_ctor(&self.cx, right) else {
            return Ok(None);
        };
        if ind.tag != rind.tag || i != j || lfields.len() != rfields.len() {
            return Ok(None);
        }
        let op = format!("{}::{}", ind.name, ind.ctors[i].name);
        let statement = match lfields.len() {
            1 => format!("relation_props::PreservesRelation({r}, {r}, {op})", r = self.rel),
            2 => format!(
                "algebra_rel::Respects2<{a}, {a}, {a}>({r}, {r}, {r}, {op})",
                a = self.carrier,
                r = self.rel
            ),
            _ => return Ok(None),
        };
        // A constructor whose fields are not the carrier's has no such
        // statement; it is not a context of this relation.
        let Ok((ty, level)) = self.type_of(&statement) else {
            return Ok(None);
        };
        let certificate = self.evidence(ty, level, "compatibility")?;
        let x = self.value(lfields[0].clone());
        let x2 = self.value(rfields[0].clone());
        let hx = self.field(&lfields[0], &rfields[0], depth)?;
        if lfields.len() == 1 {
            return Ok(Some(format!("{certificate}({x}, {x2}, {hx})")));
        }
        let y = self.value(lfields[1].clone());
        let y2 = self.value(rfields[1].clone());
        let hy = self.field(&lfields[1], &rfields[1], depth)?;
        Ok(Some(format!("{certificate}.respects2({x}, {x2}, {hx}, {y}, {y2}, {hy})")))
    }

    /// The proof for one field of a constructor context. A field of a
    /// lowered constructor value carries the annotations of where it sits,
    /// so the same expression inside a constructor and at the head of the
    /// supplied proof's statement can be two spellings: where the walk's
    /// syntactic tests do not place the pair, conversion decides whether it
    /// is the supplied change or no change at all.
    fn field(&mut self, left: &Rc<Term>, right: &Rc<Term>, depth: usize) -> R<String> {
        let (supplied_left, supplied_right) = self.sides();
        if left == right || (*left == supplied_left && *right == supplied_right) {
            return self.walk(left.clone(), right.clone(), depth + 1);
        }
        let l = self.value(left.clone());
        let r = self.value(right.clone());
        let (ty, level) = self.type_of(&format!("{}({l}, {r})", self.rel))?;
        let sl = self.value(supplied_left);
        let sr = self.value(supplied_right);
        let (supplied, _) = self.type_of(&format!("{}({sl}, {sr})", self.rel))?;
        if self.core_converts(&supplied, &ty, &level) {
            return Ok(self.witness.clone());
        }
        let (fixed, _) = self.type_of(&format!("{}({l}, {l})", self.rel))?;
        if self.core_converts(&fixed, &ty, &level) {
            return self.walk(left.clone(), left.clone(), depth + 1);
        }
        self.walk(left.clone(), right.clone(), depth + 1)
    }

    fn walk(&mut self, left: Rc<Term>, right: Rc<Term>, depth: usize) -> R<String> {
        self.nodes += 1;
        if self.nodes > (if self.derive { 512 } else { 256 })
            || depth > (if self.derive { 96 } else { 32 })
        {
            return err(
                if self.derive {
                    "`rel_derive` exceeds its 512-node / depth-96 bound"
                } else {
                    "`rel_cong` context exceeds its 256-node / depth-32 bound"
                },
                self.span,
            );
        }
        if self.derive {
            if let Some(proof) = self.branch(&left, &right, depth)? {
                return Ok(proof);
            }
        }
        // Identical occurrences stay fixed; equal endpoints never justify an
        // unrelated difference. Structural matching never unfolds operations.
        if left == right {
            let x = self.value(left);
            let (ty, level) = self.type_of(&format!(
                "relation_props::Reflexive<{}>({})",
                self.carrier, self.rel
            ))?;
            if let Some(dictionary) = self.resolve(&ty, &level) {
                let dictionary = self.alias(Rc::new(dictionary), ty, level);
                return Ok(format!("{dictionary}.rel_refl({x})"));
            }
            let (ty, level) = self.type_of(&format!("{}({x}, {x})", self.rel))?;
            return self.evidence(ty, level, "fixed");
        }
        let (supplied_left, supplied_right) = self.sides();
        if left == supplied_left && right == supplied_right {
            return Ok(self.witness.clone());
        }
        if let Some(proof) = self.across(&left, &right, depth)? {
            return Ok(proof);
        }
        if let (
            Some((lf, ly)),
            Some((rf, ry)),
        ) = (crate::spelling::app_of(left.as_ref()), crate::spelling::app_of(right.as_ref()))
        {
            if let (
                Some((lop, lx)),
                Some((rop, rx)),
            ) = (crate::spelling::app_of(lf.as_ref()), crate::spelling::app_of(rf.as_ref()))
            {
                let (op_ty, op_level) = self.type_of(&format!(
                    "{} → {} → {}",
                    self.carrier, self.carrier, self.carrier
                ))?;
                if lop == rop && self.core_checks(lop, &op_ty, &op_level) {
                    let x = self.value(lx.clone());
                    let x2 = self.value(rx.clone());
                    let y = self.value(ly.clone());
                    let y2 = self.value(ry.clone());
                    let op = self.alias(lop.clone(), op_ty, op_level);
                    let (ty, level) = self.type_of(&format!(
                        "algebra_rel::Respects2<{a}, {a}, {a}>({r}, {r}, {r}, {op})",
                        a = self.carrier,
                        r = self.rel
                    ))?;
                    if self.derive && self.resolve(&ty, &level).is_none() {
                        if let Some(result) = self.expand(&left, &right, depth) {
                            return result;
                        }
                    }
                    let dictionary = self.evidence(ty, level, "compatibility")?;
                    let hx = self.walk(lx.clone(), rx.clone(), depth + 1)?;
                    let hy = self.walk(ly.clone(), ry.clone(), depth + 1)?;
                    return Ok(format!(
                        "{dictionary}.respects2({x}, {x2}, {hx}, {y}, {y2}, {hy})"
                    ));
                }
            }
        }
        if let (
            Some((lf, lx)),
            Some((rf, rx)),
        ) = (crate::spelling::app_of(left.as_ref()), crate::spelling::app_of(right.as_ref()))
        {
            let (op_ty, op_level) =
                self.type_of(&format!("{} → {}", self.carrier, self.carrier))?;
            if lf == rf && self.core_checks(lf, &op_ty, &op_level) {
                let op = self.alias(lf.clone(), op_ty, op_level);
                let (ty, level) = self.type_of(&format!(
                    "relation_props::PreservesRelation({r}, {r}, {op})",
                    r = self.rel
                ))?;
                let family = if self.resolve(&ty, &level).is_none() {
                    if let Some((_, fixed)) = crate::spelling::app_of(lf) {
                        self.family_certificate(fixed, &ty, &level)
                    } else {
                        None
                    }
                } else {
                    None
                };
                if self.derive && family.is_none() && self.resolve(&ty, &level).is_none() {
                    if let Some(result) = self.expand(&left, &right, depth) {
                        return result;
                    }
                }
                let certificate = if let Some(proof) = family {
                    self.alias(Rc::new(proof), ty, level)
                } else {
                    self.evidence(ty, level, "compatibility")?
                };
                let x = self.value(lx.clone());
                let y = self.value(rx.clone());
                let h = self.walk(lx.clone(), rx.clone(), depth + 1)?;
                return Ok(format!("{certificate}({x}, {y}, {h})"));
            }
        }
        if let Some(proof) = self.under_constructor(&left, &right, depth)? {
            return Ok(proof);
        }
        if self.derive {
            if let Some(result) = self.expand(&left, &right, depth) {
                return result;
            }
            let l = self.value(left);
            let r = self.value(right);
            let (ty, level) = self.type_of(&format!("{}({l}, {r})", self.rel))?;
            return self.evidence(ty, level, "definition");
        }
        err(
            "`rel_cong` context mismatch: the supplied proof does not explain this change (only homogeneous unary/binary contexts are supported)",
            self.span,
        )
    }
}

/// Relational context proofs' part of the elaborator.
pub(crate) struct RelationalProof<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for RelationalProof<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl RelationalProof<'_> {
    /// A goal for evidence a relational tactic needs and resolution did not
    /// find: `ty` in `cx`, labelled for an `on ?label := …` in the block and
    /// reported with its statement when nothing discharges it. `serial`
    /// tells one tactic's goals at one site apart.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn relation_obligation(
        &self,
        cx: &Cx,
        tactic: &str,
        label: &str,
        serial: usize,
        ty: Type,
        level: Level,
        span: Span,
    ) -> R<Term> {
        match self.attempt.goal_arena.reserve_promoted(1) {
            goals::PromotionCapacity::Ready => {}
            goals::PromotionCapacity::Restart => {
                return err(
                    "internal: restarting declaration to reserve relational congruence goals",
                    span,
                );
            }
            goals::PromotionCapacity::Disabled => {
                return err(format!("`{tactic}` cannot create an obligation here"), span);
            }
        }
        let key = format!("{tactic}:{serial}");
        let spelling = self.spell_type_clean(cx, &ty);
        let term = self.new_goal_key(cx, None, Some((tactic, label)), ty, level, span, Some(&key), None)?;
        if let Some(spelling) = spelling {
            self.attempt.goal_arena.set_statement_spelling(span, &key, spelling);
        }
        Ok(term)
    }
}

pub(crate) fn check(
    e: &Elaborator,
    cx: &Cx,
    proof: &Expr,
    expected: &Type,
    level: &Level,
    span: Span,
    derive: bool,
) -> R<Term> {
    let (witness, proof_ty, proof_level) = e.elab_infer(cx, proof)?;
    let input = relation(e, cx, &proof_ty, span)?;
    let output = relation(e, cx, expected, span)?;
    if input.head != output.head || input.carrier != output.carrier || input.level != Level::Zero {
        return err(
            "`rel_cong` requires the same resolved relation and Type<0> carrier in its proof and goal",
            span,
        );
    }
    let mut b = Builder {
        e,
        original: cx,
        cx: cx.clone(),
        span,
        relation: input,
        rel: String::new(),
        carrier: String::new(),
        witness: String::new(),
        serial: 0,
        nodes: 0,
        goals: 0,
        derive,
        binders: Vec::new(),
        sides: Vec::new(),
        fields: RefCell::new(HashMap::new()),
    };
    b.carrier = b.fresh();
    b.cx.tyvars.push(TyVar {
        name: b.carrier.clone(),
        ty: (*b.relation.carrier).clone(),
        level: b.relation.level.clone(),
        depth: cx.names.len(),
    });
    let (rel_ty, rel_level) = b.type_of(&format!("{} → {} → Type", b.carrier, b.carrier))?;
    if !b.core_checks(&b.relation.head, &rel_ty, &rel_level) {
        return err(
            "`rel_cong` requires a non-dependent homogeneous relation",
            span,
        );
    }
    b.rel = b.alias(b.relation.head.clone(), rel_ty, rel_level);
    b.witness = b.alias(Rc::new(witness), proof_ty, proof_level);
    let generated = b.walk(output.left, output.right, 0)?;
    let expr = expression(&generated, span)?;
    e.generated_scope(|e| e.elab_check(&b.cx, &expr, expected, level))
}

/// The expected preservation telescope supplies the function and relation.
/// The generated lambda is checked normally; its pointwise request inspects
/// transparent definitions and returns ordinary proof terms or scoped goals.
pub(crate) fn derive(
    e: &Elaborator,
    cx: &Cx,
    expected: &Type,
    level: &Level,
    span: Span,
) -> R<Term> {
    let mut serial = 0;
    let mut fresh = || loop {
        let name = format!("__derive_arg_{serial}");
        serial += 1;
        if !cx.names.contains(&name) && !cx.aliases.iter_inner().any(|a| a.name == name) {
            break name;
        }
    };
    let x = fresh();
    let y = fresh();
    let h = fresh();
    let mut body = expression(&format!("λ {x} {y} {h} => rel_derive({h})"), span)?;
    // Goal identities belong to the user's request, not the synthetic lambda's
    // identical source offsets. Two requests must retain independent goals.
    body.span = span;
    if let heather_syntax::ExprKind::Lam {
        body: pointwise, ..
    } = &mut body.kind
    {
        pointwise.span = span;
    }
    e.generated_scope(|e| e.elab_check(cx, &body, expected, level))
}
