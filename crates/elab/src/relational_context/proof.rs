//! Proof-position relational congruence over resolved, non-dependent terms.
//! Reconstruction uses ordinary class projections and ordinary local goals.
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, Term, Type};
use heather_syntax::{parse_file, Expr, Item, Span};

use crate::{err, goals, Alias, Cx, ElabError, Elaborator, TyVar, R};

fn expression(text: &str, span: Span) -> R<Expr> {
    let source = format!("fn generated() -> Type {{ {text} }}");
    let mut file = parse_file(&source).map_err(|e| ElabError::Elab { msg: e.msg, span })?;
    let Some(Item::Decl(d)) = file.items.pop() else {
        unreachable!()
    };
    Ok(*d.body.result)
}

struct Relation {
    head: Rc<Term>,
    left: Rc<Term>,
    right: Rc<Term>,
    carrier: Rc<Type>,
    level: Level,
}

fn relation(e: &Elaborator, cx: &Cx, ty: &Type, span: Span) -> R<Relation> {
    if let Type::El { tm, .. } = ty
        && let Some((fun, right)) = crate::spelling::app_of(tm)
        && let Some((head, left)) = crate::spelling::app_of(fun)
    {
        // The two domains: stated by an `app` node, the head's for an
        // `app@` one (`docs/app-by-head-type-design.md` §6.2).
        let (first, dom) = match (fun.as_ref(), tm.as_ref()) {
            (
                Term::App { dom: first, dom_level: fl, .. },
                Term::App { dom, dom_level, .. },
            ) => ((first.clone(), fl.clone()), (dom.clone(), dom_level.clone())),
            _ => {
                let doms = e.app_domains(cx, tm, span).unwrap_or_default();
                let [.., first, dom] = doms.as_slice() else {
                    return relation_err(span);
                };
                (first.clone(), dom.clone())
            }
        };
        if first.0 == dom.0 {
            return Ok(Relation {
                head: head.clone(),
                left: left.clone(),
                right: right.clone(),
                carrier: dom.0,
                level: dom.1,
            });
        }
    }
    relation_err(span)
}

fn relation_err(span: Span) -> R<Relation> {
    err(
        "`rel_cong` needs a homogeneous binary relation application; native identity and dependent relations are outside this first fragment",
        span,
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
    /// The projected fields of each dictionary reachable by name from
    /// `cx.dicts`, for this derivation's lifetime. Only the innermost binder
    /// of a name is ever searched (the `seen` set below), and the walk pushes
    /// nothing but freshly named aliases, so a name's projections are the
    /// same term at every search — while recomputing them is the `Σ`-spine
    /// walk of `project_field`, once per field per search
    /// (issues/relational-derivation-cost.md).
    fields: RefCell<HashMap<String, Rc<Vec<Field>>>>,
}

impl Builder<'_> {
    fn fresh(&mut self) -> String {
        loop {
            let name = format!("__rel_cong_{}", self.serial);
            self.serial += 1;
            if !self.cx.names.contains(&name)
                && !self.cx.aliases.iter().any(|a| a.name == name)
                && !self.cx.tyvars.iter().any(|a| a.name == name)
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
        }));
        name
    }

    fn value(&mut self, value: Rc<Term>) -> String {
        self.alias(
            value,
            (*self.relation.carrier).clone(),
            self.relation.level.clone(),
        )
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
            &self.e.display_type(self.original, ty),
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
        if let Some(cached) = self.fields.borrow().get(name) {
            return cached.clone();
        }
        let built = Rc::new(self.project_fields(name, class));
        self.fields
            .borrow_mut()
            .insert(name.to_string(), built.clone());
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
        for d in self.cx.dicts.iter().rev() {
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
            match self.e.attempt.goal_arena.reserve_promoted(1) {
                goals::PromotionCapacity::Ready => {}
                goals::PromotionCapacity::Restart => {
                    return err(
                        "internal: restarting declaration to reserve relational congruence goals",
                        self.span,
                    );
                }
                goals::PromotionCapacity::Disabled => {
                    return err("`rel_cong` cannot create an obligation here", self.span);
                }
            }
            let tactic = if self.derive {
                "rel_derive"
            } else {
                "rel_cong"
            };
            let key = format!("{tactic}:{}", self.goals);
            self.goals += 1;
            let term = self.e.new_goal_key(
                self.original,
                None,
                Some((tactic, label)),
                ty.clone(),
                level.clone(),
                self.span,
                Some(&key),
                None,
            )?;
            if let Some(spelling) = self.e.spell_type_clean(self.original, &ty) {
                self.e
                    .attempt
                    .goal_arena
                    .set_statement_spelling(self.span, &key, spelling);
            }
            term
        };
        Ok(self.alias(Rc::new(term), ty, level))
    }

    // One transparent head-reduction step at a time. Re-entering walk gives
    // registered/local certificates priority at every exposed application.
    fn expand(&mut self, left: &Rc<Term>, right: &Rc<Term>, depth: usize) -> Option<R<String>> {
        let oracle = self.e.semantic_oracle();
        let (l, r) = crate::stats::timed(crate::stats::Timer::ElabWhnf, || {
            (
                oracle.term_reducts(&self.cx.gamma, left, 1).next(),
                oracle.term_reducts(&self.cx.gamma, right, 1).next(),
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
        if left == self.relation.left && right == self.relation.right {
            return Ok(self.witness.clone());
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
        if !cx.names.contains(&name) && !cx.aliases.iter().any(|a| a.name == name) {
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
