//! Proof-position relational congruence over resolved, non-dependent terms.
//! Reconstruction uses ordinary class projections and ordinary local goals.
use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, Item, Span, parse_file};

use crate::{Alias, Cx, ElabError, Elaborator, R, TyVar, err, goals};

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

fn relation(ty: &Type, span: Span) -> R<Relation> {
    if let Type::El { tm, .. } = ty {
        if let Term::App {
            fun,
            arg: right,
            dom,
            dom_level,
            ..
        } = tm.as_ref()
        {
            if let Term::App {
                fun: head,
                arg: left,
                dom: first,
                ..
            } = fun.as_ref()
            {
                if first == dom {
                    return Ok(Relation {
                        head: head.clone(),
                        left: left.clone(),
                        right: right.clone(),
                        carrier: dom.clone(),
                        level: dom_level.clone(),
                    });
                }
            }
        }
    }
    err(
        "`rel_cong` needs a homogeneous binary relation application; native identity and dependent relations are outside this first fragment",
        span,
    )
}

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
            self.span,
            &mut Vec::new(),
        )
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
            let Ok((dict, ty, _)) = self.e.resolve(&self.cx, &d.name, self.span) else {
                continue;
            };
            let Some(ind) = self.e.display_tag_of(&ty) else {
                continue;
            };
            if self.e.key_of(&d.class) != self.e.key_of(&ind.name) {
                continue;
            }
            let Some(ctor) = ind.ctors.first() else {
                continue;
            };
            for index in 0..ctor.fields.len() {
                examined += 1;
                if examined > 64 {
                    return None;
                }
                let Ok((field, field_ty, _)) = self.e.project_field(
                    &self.cx,
                    &ind,
                    &ty,
                    Rc::new(dict.clone()),
                    index,
                    self.span,
                ) else {
                    continue;
                };
                let Type::Pi {
                    dom_level,
                    cod_level,
                    dom,
                    cod,
                } = field_ty
                else {
                    continue;
                };
                if !self.core_checks(fixed, &dom, &dom_level) {
                    continue;
                }
                let candidate = Term::App {
                    fun: Rc::new(field),
                    arg: fixed.clone(),
                    dom_level,
                    cod_level,
                    dom,
                    cod,
                };
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
            let key = format!("rel_cong:{}", self.goals);
            self.goals += 1;
            let term = self.e.new_goal_key(
                self.original,
                None,
                Some(("rel_cong", label)),
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

    fn walk(&mut self, left: Rc<Term>, right: Rc<Term>, depth: usize) -> R<String> {
        self.nodes += 1;
        if self.nodes > 256 || depth > 32 {
            return err(
                "`rel_cong` context exceeds its 256-node / depth-32 bound",
                self.span,
            );
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
            Term::App {
                fun: lf, arg: ly, ..
            },
            Term::App {
                fun: rf, arg: ry, ..
            },
        ) = (left.as_ref(), right.as_ref())
        {
            if let (
                Term::App {
                    fun: lop, arg: lx, ..
                },
                Term::App {
                    fun: rop, arg: rx, ..
                },
            ) = (lf.as_ref(), rf.as_ref())
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
            Term::App {
                fun: lf, arg: lx, ..
            },
            Term::App {
                fun: rf, arg: rx, ..
            },
        ) = (left.as_ref(), right.as_ref())
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
                    if let Term::App { arg: fixed, .. } = lf.as_ref() {
                        self.family_certificate(fixed, &ty, &level)
                    } else {
                        None
                    }
                } else {
                    None
                };
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
) -> R<Term> {
    let (witness, proof_ty, proof_level) = e.elab_infer(cx, proof)?;
    let input = relation(&proof_ty, span)?;
    let output = relation(expected, span)?;
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
