//! The certificate's declarations, input-independent ones first.
//!
//! A build over the semantic session replays the previous certificate image's
//! declarations only while every earlier declaration reproduced the previous
//! prefix exactly (`docs/declaration-slice-replay-design.md` §4). Generated in
//! execution order, the first declaration that mentions an `--arg` sits a few
//! percent into the module, so a build with other inputs re-elaborated nearly
//! all of it. Here the declarations whose text depends on the inputs, and every
//! declaration that refers to one, move to the end in their relative order, so
//! the rest is a prefix a build with other inputs can replay
//! (issues/check-module-delta-certificate-cost.md).
//!
//! Which declarations depend on the inputs is read off generations at other
//! inputs: a declaration whose text differs from a probe's, or that a probe
//! lacks, is a seed. Two probes at unrelated inputs, because one is fooled by
//! coincidence — a constant like `word_2` that the certificate and its one
//! probe both happen to need, but the previous build's did not, stays in the
//! prefix and breaks it there. The order is a replay heuristic and nothing else — every
//! replayed slice is still checked against the elaboration it stands for, so
//! a declaration misplaced here costs its replay, never a verdict. A
//! reference this module failed to see would put a use before its definition
//! and fail the build loudly, and a forward reference (a mutual group) moves
//! with its referrer, so a group is never split.

use std::collections::{BTreeMap, BTreeSet};

use heather_syntax::{Item, parse_file};

/// `certificate` with its input-dependent declarations last, judged against
/// `probes`, the same certificate generated at other inputs. Unchanged when
/// any does not parse: the elaborator reports the certificate's own error.
pub(super) fn inputs_last(certificate: &str, probes: &[String]) -> String {
    let Some(items) = segments(certificate) else { return certificate.to_string() };
    let Some(probes) = probes.iter().map(|p| segments(p)).collect::<Option<Vec<_>>>() else {
        return certificate.to_string();
    };
    let probes: Vec<BTreeMap<&str, &str>> = probes
        .iter()
        .map(|probe| probe.iter().filter_map(|s| Some((s.name.as_deref()?, s.text))).collect())
        .collect();
    let index: BTreeMap<&str, usize> =
        items.iter().enumerate().filter_map(|(i, s)| Some((s.name.as_deref()?, i))).collect();
    let references: Vec<BTreeSet<usize>> = items
        .iter()
        .enumerate()
        .map(|(i, s)| if s.import { BTreeSet::new() } else {
            identifiers(s.text).filter_map(|id| index.get(id).copied()).filter(|&j| j != i).collect()
        })
        .collect();
    let mut users = vec![Vec::new(); items.len()];
    for (i, refs) in references.iter().enumerate() {
        for &j in refs {
            users[j].push(i);
        }
    }
    let mut moved = vec![false; items.len()];
    let mut work: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, s)| s.name.as_deref().is_some_and(|name| probes.iter().any(|probe| probe.get(name) != Some(&s.text))))
        .map(|(i, _)| i)
        .collect();
    while let Some(i) = work.pop() {
        if std::mem::replace(&mut moved[i], true) {
            continue;
        }
        // A moved declaration drags its users after it, and anything it
        // refers to *later* in the module, which is a mutual group's shape.
        work.extend(users[i].iter().copied().filter(|&u| !moved[u]));
        work.extend(references[i].iter().copied().filter(|&j| j > i && !moved[j]));
    }
    let (stay, go): (Vec<_>, Vec<_>) = items.iter().zip(&moved).partition(|(_, m)| !**m);
    let mut out: String = stay.iter().chain(&go).map(|(s, _)| s.text).collect();
    out.push_str(&certificate[items.last().map_or(0, |s| s.end)..]);
    out
}

struct Segment<'a> {
    /// The declared name, if the item has one to be referred to by.
    name: Option<String>,
    /// An import stays where it is: it declares nothing, and everything after
    /// it may need it.
    import: bool,
    /// The item with everything between it and the previous one, so comments
    /// and attributes travel with the item they precede.
    text: &'a str,
    end: usize,
}

fn segments(src: &str) -> Option<Vec<Segment<'_>>> {
    let file = parse_file(src).ok()?;
    let mut start = 0;
    let mut out = Vec::with_capacity(file.items.len());
    for item in &file.items {
        let (name, span) = match item {
            Item::Decl(x) => (Some(x.name.clone()), x.span),
            Item::Inductive(x) => (Some(x.name.clone()), x.span),
            Item::Class(x) => (Some(x.name.clone()), x.span),
            // No declared name of its own: never a seed, but moved after a
            // declaration it refers to like any other item.
            Item::Instance(x) => (None, x.span),
            Item::Designation(x) => (None, x.span),
            Item::Datarepr(x) => (Some(x.name.clone()), x.span),
            Item::Impl(x) => (None, x.span),
            Item::Import(x) => (None, x.span),
        };
        out.push(Segment { name, import: matches!(item, Item::Import(_)), text: &src[start..span.end], end: span.end });
        start = span.end;
    }
    Some(out)
}

fn identifiers(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).filter(|t| !t.is_empty())
}

#[cfg(test)]
mod tests {
    use super::inputs_last;

    #[test]
    fn dependents_move_last_in_order_and_the_rest_keeps_its_order() {
        let at = |x: u64| format!(
            "import logic;\nfn a() -> Nat {{ 1 }}\nfn input() -> Nat {{ {x} }}\nfn b() -> Nat {{ a() }}\n\
             fn uses() -> Nat {{ input() }}\nfn c() -> Nat {{ b() }}\nfn uses_uses() -> Nat {{ uses() }}\n");
        let out = inputs_last(&at(20), &[at(21)]);
        let order: Vec<&str> = out.lines().filter_map(|l| l.strip_prefix("fn ")).map(|l| &l[..l.find('(').unwrap()]).collect();
        assert_eq!(order, ["a", "b", "c", "input", "uses", "uses_uses"]);
        assert!(out.starts_with("import logic;\n"));
        assert_eq!(out.len(), at(20).len());
    }

    #[test]
    fn identical_certificates_are_unchanged() {
        let src = "fn a() -> Nat { 1 }\nfn b() -> Nat { a() }\n";
        assert_eq!(inputs_last(src, &[src.to_string()]), src);
    }
}
