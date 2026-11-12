//! A closed value spelled for a person to read (`heather eval`'s reader for
//! a type it has no encoder for): each layer is the term's weak head
//! (`Elaborator::whnf_tm`, decided in the value domain), read as a
//! constructor with the display's own decoder ([`Elaborator::view_ctor`],
//! which a diagnostic spells `C(…)` with), and its fields shown the same
//! way. So any first-order value reads by its declaration's constructor and
//! field names, the way the program writes it.
//!
//! A few declarations read as their literals: a `Nat` as its numeral, a
//! `List` as `[a, b]`, a `String` as a quoted string, a `Char` as a quoted
//! character. A head that is no constructor (a function, a type, a stuck
//! term) is the display's bounded spelling of it. The walk is bounded by a
//! count of nodes, and what is left past it is `…`; every layer is bounded
//! by the elaborator's fuel. An evaluation, untrusted: nothing here is
//! checked.
use std::cell::Cell;

use heather_kernel::rc::Rc;
use heather_kernel::term::Term;
use heather_syntax::ast::Span;

use crate::{Cx, Elaborator};

/// Evaluation steps one numeral may take to read.
const NUMERAL_STEPS: u64 = 1 << 24;
/// Characters of one string read before it is cut.
const STRING_CHARS: usize = 1 << 16;

/// `name`, a closed top-level term, evaluated and spelled, and whether it
/// was cut: at most `nodes` layers are read. `Err` for a name that is not a
/// plain top-level term, or a layer that runs out of fuel.
pub fn show_global(el: &Elaborator, name: &str, nodes: usize) -> Result<(String, bool), String> {
    let (head, _, _) = crate::host::Host(el).raw_global(name).ok_or_else(|| format!("`{name}` is not a closed top-level term"))?;
    let shown = Shown { el, cx: Cx::empty(), nodes: Cell::new(nodes), cut: Cell::new(false) };
    let mut out = String::new();
    shown.value(&Rc::new(head), &mut out)?;
    Ok((out, shown.cut.get()))
}

/// One spelling's walk: the world, the empty context every closed term is
/// read at, and the nodes left.
struct Shown<'e> {
    el: &'e Elaborator,
    cx: Cx,
    nodes: Cell<usize>,
    cut: Cell<bool>,
}

impl Shown<'_> {
    /// One more node, or `false` once the budget is spent.
    fn take(&self) -> bool {
        let left = self.nodes.get();
        if left == 0 {
            self.cut.set(true);
            return false;
        }
        self.nodes.set(left - 1);
        true
    }

    fn whnf(&self, t: &Term) -> Result<Rc<Term>, String> {
        self.el.whnf_tm(&self.cx, t, Span { start: 0, end: 0 })
            .map_err(|_| "evaluation ran out of fuel".to_string())
    }

    /// The constructor at `t`'s head: its declaration's module and name, the
    /// constructor's name, the fields' names, and the fields.
    fn ctor(&self, head: &Term) -> Option<Ctor> {
        let (ind, i, fields) = self.el.view_ctor(&self.cx, head)?;
        let ctor = ind.ctors.get(i)?;
        let names = ctor.fields.iter().map(|(name, _)| name.clone()).collect();
        Some(Ctor { module: ind.scope.module.clone(), decl: ind.name.clone(), name: ctor.name.clone(), names, fields, record: ind.is_record })
    }

    fn value(&self, t: &Rc<Term>, out: &mut String) -> Result<(), String> {
        if !self.take() {
            out.push('…');
            return Ok(());
        }
        let head = self.whnf(t)?;
        match &*head {
            Term::Zero | Term::Succ(_) | Term::NatLit(_) => {
                match self.el.semantic_oracle().nat_value(&self.cx.gamma, t, NUMERAL_STEPS) {
                    Some(n) => out.push_str(&n.to_string()),
                    None => out.push_str("<a numeral past 64 bits or its budget>"),
                }
                return Ok(());
            }
            Term::Lam { .. } => {
                out.push_str("<function>");
                return Ok(());
            }
            // A vector, `[T; n]`: a chain of pairs, or one of the kernel's
            // literal vectors.
            Term::Pair { .. } | Term::PairAt { .. } | Term::VecLit { .. } | Term::VecItems { .. } | Term::Triv { .. }
                if self.ctor(&head).is_none() => {
                let (items, rest) = self.vector(&head)?;
                out.push('[');
                for (k, item) in items.iter().enumerate() {
                    if k > 0 { out.push_str(", "); }
                    self.value(item, out)?;
                }
                if let Some(rest) = rest {
                    if !items.is_empty() { out.push_str(", "); }
                    out.push_str("…");
                    out.push_str(&self.el.display_rough_term(&self.cx, &rest, &[]));
                }
                out.push(']');
                return Ok(());
            }
            _ => {}
        }
        let Some(ctor) = self.ctor(&head) else {
            out.push_str(&self.el.display_rough_term(&self.cx, &head, &[]));
            return Ok(());
        };
        match (ctor.module.as_str(), ctor.decl.as_str()) {
            ("list", "List") => return self.list(ctor, out),
            ("string", "String") if ctor.fields.len() == 1 => {
                let mut text = String::new();
                let whole = self.chars(&ctor.fields[0], &mut text)?;
                out.push_str(&format!("{text:?}"));
                if !whole { out.push('…'); }
                return Ok(());
            }
            // A word as its numeral at its width, `104u8`.
            ("bitvec", "BitVec") if ctor.fields.len() == 1 => {
                if let Some((value, width)) = self.word(&ctor.fields[0])? {
                    out.push_str(&format!("{value}u{width}"));
                    return Ok(());
                }
            }
            ("char", "Char") if !ctor.fields.is_empty() => {
                return match self.number(&ctor.fields[0])? {
                    Some(code) => {
                        out.push_str(&format!("{:?}", char_of(code)));
                        Ok(())
                    }
                    None => self.fields(&ctor, out),
                };
            }
            _ => {}
        }
        self.fields(&ctor, out)
    }

    /// `C`, or `C(a, b)`, or a record's `R(f := a, g := b)`.
    fn fields(&self, ctor: &Ctor, out: &mut String) -> Result<(), String> {
        out.push_str(&ctor.name);
        if ctor.fields.is_empty() {
            return Ok(());
        }
        out.push('(');
        for (k, field) in ctor.fields.iter().enumerate() {
            if k > 0 { out.push_str(", "); }
            if let Some(Some(name)) = ctor.names.get(k).filter(|_| ctor.record) {
                out.push_str(name);
                out.push_str(" := ");
            }
            self.value(field, out)?;
        }
        out.push(')');
        Ok(())
    }

    /// A list from its first cell: `[a, b]`, cut with `…`.
    fn list(&self, mut cell: Ctor, out: &mut String) -> Result<(), String> {
        out.push('[');
        let mut first = true;
        loop {
            let [head, tail] = &cell.fields[..] else { break };
            if !first { out.push_str(", "); }
            first = false;
            self.value(head, out)?;
            if !self.take() {
                out.push_str(", …");
                break;
            }
            let next = self.whnf(tail)?;
            match self.ctor(&next) {
                Some(next) if next.decl == cell.decl && next.module == cell.module => cell = next,
                _ => {
                    out.push_str(" ++ ");
                    out.push_str(&self.el.display_rough_term(&self.cx, &next, &[]));
                    break;
                }
            }
        }
        out.push(']');
        Ok(())
    }

    /// A `List<Char>`'s characters appended to `text`; `false` when it was
    /// cut, or is not a list of characters all the way down.
    fn chars(&self, list: &Rc<Term>, text: &mut String) -> Result<bool, String> {
        let mut cell = self.whnf(list)?;
        for _ in 0..STRING_CHARS {
            let Some(ctor) = self.ctor(&cell) else { return Ok(false) };
            let [c, tail] = &ctor.fields[..] else { return Ok(true) };
            let code = match self.ctor(&*self.whnf(c)?) {
                Some(ch) if !ch.fields.is_empty() => self.number(&ch.fields[0])?,
                _ => None,
            };
            let Some(code) = code else { return Ok(false) };
            text.push(char_of(code));
            cell = self.whnf(tail)?;
        }
        Ok(false)
    }

    /// A vector's items from its weak head `head`, and what is left when
    /// the chain does not end in the empty vector.
    fn vector(&self, head: &Term) -> Result<(Vec<Rc<Term>>, Option<Rc<Term>>), String> {
        let mut items = Vec::new();
        let mut at = Rc::new(head.clone());
        loop {
            match &*at {
                Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
                    if items.len() >= STRING_CHARS { return Ok((items, Some(Rc::clone(snd)))); }
                    items.push(Rc::clone(fst));
                    let next = self.whnf(snd)?;
                    at = next;
                }
                // Packed bits, least significant first.
                Term::VecLit { zero, one, width, bits, .. } => {
                    items.extend((0..*width).map(|i| Rc::clone(if i < 64 && bits >> i & 1 == 1 { one } else { zero })));
                    return Ok((items, None));
                }
                Term::VecItems { items: listed, from, .. } => {
                    items.extend(listed.iter().skip(*from as usize).cloned());
                    return Ok((items, None));
                }
                Term::Triv { .. } => return Ok((items, None)),
                _ => return Ok((items, Some(at))),
            }
        }
    }

    /// A `BitVec`'s bits as a number and its width, when every bit reads as
    /// a `Bool` and the width is at most 128.
    fn word(&self, bits: &Rc<Term>) -> Result<Option<(u128, usize)>, String> {
        let (items, rest) = self.vector(&*self.whnf(bits)?)?;
        if rest.is_some() || items.len() > 128 {
            return Ok(None);
        }
        let mut value = 0u128;
        for (i, bit) in items.iter().enumerate() {
            match self.ctor(&*self.whnf(bit)?) {
                Some(b) if b.module == "bool" && b.name == "True" => value |= 1 << i,
                Some(b) if b.module == "bool" && b.name == "False" => {}
                _ => return Ok(None),
            }
        }
        Ok(Some((value, items.len())))
    }

    fn number(&self, t: &Rc<Term>) -> Result<Option<u64>, String> {
        Ok(self.el.semantic_oracle().nat_value(&self.cx.gamma, t, NUMERAL_STEPS))
    }
}

struct Ctor {
    module: String,
    decl: String,
    name: String,
    names: Vec<Option<String>>,
    fields: Vec<Rc<Term>>,
    /// A record's fields are shown by name, `R(f := a)`; a constructor's
    /// as its call writes them, `C(a)`.
    record: bool,
}

fn char_of(code: u64) -> char {
    u32::try_from(code).ok().and_then(char::from_u32).unwrap_or('\u{FFFD}')
}
