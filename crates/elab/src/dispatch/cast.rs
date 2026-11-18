//! `↑e` and `cast<B>(e)` (docs/language/casting-design.md §5.2, §14).
//!
//! A cast edge is an instance `Cast<A, B>(map)` of `morphism::Cast`, keyed at
//! its source `A` and indexed by its map, so the registry holds every edge in
//! scope with nothing new to persist. A cast is a *rewrite*, as an operator
//! symbol is: `↑e` at a position expecting `B` becomes the edges' maps
//! applied along the shortest path from `e`'s carrier to `B`, an ordinary
//! named application elaborated as written. The term is the one a writer
//! would have spelled (`Rat::ofInt(OfNat(n))`), so nothing downstream sees a
//! cast at all.

use std::collections::{BTreeMap, VecDeque};

use heather_kernel::term::Type;
use heather_syntax::{Expr, ExprKind, Span};

use crate::{Cx, Elaborator, R, err, names};
use crate::dispatch::Carriers;

/// One edge: the map's global, and the carrier it maps into.
struct Edge {
    map: String,
    target: String,
}

/// Casting's part of the elaborator.
pub(crate) struct Casts<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Casts<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Casts<'_> {
    fn cast_class_key() -> String {
        names::qkey("morphism", "Cast")
    }

    /// The edges in scope, by source carrier key.
    fn cast_edges(&self, cx: &Cx, span: Span) -> BTreeMap<String, Vec<Edge>> {
        let mut out: BTreeMap<String, Vec<Edge>> = BTreeMap::new();
        for (source, map) in self.traits.instances_of_class(&Self::cast_class_key()) {
            // A constructor edge (`OfNat`) maps into its own inductive; any
            // other map's codomain is read off its type.
            let target = match self.ctor_of(&map) {
                Some((ind, _)) => names::qkey(&ind.scope.module, &ind.name),
                None => {
                    let head = Expr { kind: ExprKind::Var(map.clone()), span };
                    let Ok((_, ty, _)) = self.elab_infer(cx, &head) else { continue };
                    let Ok(ty) = self.whnf(cx, &ty, span) else { continue };
                    let Type::Pi { cod, .. } = &ty else { continue };
                    let Some(target) = Carriers(self).carrier_of_ty(cx, cod, span) else { continue };
                    target.key
                }
            };
            out.entry(source).or_default().push(Edge { map, target });
        }
        out
    }

    /// The maps from `source` to `target` along the shortest path, first
    /// edge first; a refusal when there is none or two of the same length.
    fn cast_path(&self, cx: &Cx, source: &str, target: &str, shown: (&str, &str), span: Span) -> R<Vec<(String, String)>> {
        let edges = self.cast_edges(cx, span);
        // Breadth first, keeping every shortest way into each carrier.
        let mut ways: BTreeMap<String, Vec<Vec<(String, String)>>> = BTreeMap::new();
        ways.insert(source.to_string(), vec![Vec::new()]);
        let mut queue = VecDeque::from([source.to_string()]);
        while let Some(at) = queue.pop_front() {
            if at == target {
                break;
            }
            let here = ways[&at].clone();
            let depth = here[0].len();
            for edge in edges.get(&at).into_iter().flatten() {
                let extended: Vec<Vec<(String, String)>> = here
                    .iter()
                    .map(|way| way.iter().cloned().chain([(edge.map.clone(), edge.target.clone())]).collect())
                    .collect();
                match ways.get_mut(&edge.target) {
                    None => {
                        ways.insert(edge.target.clone(), extended);
                        queue.push_back(edge.target.clone());
                    }
                    Some(known) if known[0].len() == depth + 1 => known.extend(extended),
                    Some(_) => {}
                }
            }
        }
        let (from, to) = shown;
        match ways.get(target).map(Vec::as_slice) {
            Some([one]) => Ok(one.clone()),
            Some(several) => err(
                format!(
                    "`↑` from `{from}` to `{to}` has {} paths of the same length ({}): the \
                     shortest path decides a cast, and two of them leave it undecided; write the \
                     maps you mean",
                    several.len(),
                    several
                        .iter()
                        .map(|w| format!("`{}`", w.iter().map(|(m, _)| m.as_str()).collect::<Vec<_>>().join(" then ")))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                span,
            ),
            None => {
                let out: Vec<String> = edges.get(source).into_iter().flatten().map(|e| format!("`{}`", e.map)).collect();
                err(
                    format!(
                        "no cast from `{from}` to `{to}`: no path of cast edges joins them (the \
                         edges out of `{from}` here: {}); a lossy conversion is a named \
                         function, never `↑`",
                        if out.is_empty() { "none".to_string() } else { out.join(", ") }
                    ),
                    span,
                )
            }
        }
    }

    /// The edge whose map is `source → target` exactly, between two
    /// indices of one carrier (the widening of a word): edges between
    /// indexed carriers are declared for every pair, so there is no path to
    /// compose.
    fn indexed_edge(&self, cx: &Cx, source: &Type, target: &Type, level: &heather_kernel::level::Level, span: Span) -> Option<String> {
        for (_, map) in self.traits.instances_of_class(&Self::cast_class_key()) {
            let head = Expr { kind: ExprKind::Var(map.clone()), span };
            let Ok((_, ty, _)) = self.elab_infer(cx, &head) else { continue };
            let Ok(Type::Pi { dom, cod, cod_level, .. }) = self.whnf(cx, &ty, span) else { continue };
            let Some(cod) = crate::strengthen_ty(&cx.gamma, &cod, 1) else { continue };
            if self.conv_types(cx, &dom, source, level) && self.conv_types(cx, &cod, target, &cod_level) {
                return Some(map);
            }
        }
        None
    }

    /// `↑e` at `target`: the path's maps applied to `e`, or `e` itself when
    /// it is already at the target.
    fn cast_to_type(&self, cx: &Cx, operand: &Expr, target: &Type, span: Span) -> R<Expr> {
        if self.traits.class(&Self::cast_class_key()).is_none() {
            return err(
                "`↑` reads the cast edges, which `morphism` declares: `import morphism;` here \
                 (docs/language/casting-design.md §14)",
                span,
            );
        }
        // The identity cast first: an operand already of the target type
        // (an open carrier, `fn g<A>(x: A) → A { ↑x }`) needs no edge.
        let (_, source_ty, level) = self.elab_infer(cx, operand)?;
        if self.conv_types(cx, &source_ty, target, &level) {
            return Ok(operand.clone());
        }
        let Some(to) = Carriers(self).carrier_of_ty(cx, target, span) else {
            return err("`↑` needs a carrier to cast into, and this position expects no named type", span);
        };
        let Some(from) = Carriers(self).carrier_of_ty(cx, &source_ty, operand.span) else {
            return err("`↑`'s operand has no named carrier to cast from", operand.span);
        };
        if from.key == to.key {
            // One carrier at two indices (`BitVec(8)` and `BitVec(64)`): the
            // carrier graph cannot tell them apart, so the edge is the one
            // map between exactly these two types.
            return match self.indexed_edge(cx, &source_ty, target, &level, span) {
                Some(map) => Ok(Expr {
                    kind: ExprKind::App {
                        head: Box::new(Expr { kind: ExprKind::Var(map), span }),
                        args: vec![operand.clone()],
                        named: Vec::new(),
                        explicit: false,
                        goal_oriented: false,
                    },
                    span,
                }),
                None => err(
                    format!(
                        "no cast from `{}` to `{}`: they are one carrier at two indices, and no \
                         edge maps the one to the other; a lossy conversion is a named function, \
                         never `↑`",
                        self.display_type(cx, &source_ty),
                        self.display_type(cx, target)
                    ),
                    span,
                ),
            };
        }
        let path = self.cast_path(cx, &from.key, &to.key, (&from.written, &to.written), span)?;
        Ok(path.into_iter().fold(operand.clone(), |inner, (map, _)| Expr {
            kind: ExprKind::App {
                head: Box::new(Expr { kind: ExprKind::Var(map), span }),
                args: vec![inner],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        }))
    }

    /// The rewrite of a cast, if `e` is one: `↑e` (with the checking
    /// position's type) or `cast<B>(e)`.
    pub(crate) fn cast_rewrite(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<Option<Expr>> {
        let ExprKind::App { head, args, named, .. } = &e.kind else { return Ok(None) };
        if crate::surface::is_cast(e) {
            let Some(target) = expected else {
                return err(
                    "a cast needs a target here: write `cast<B>(e)`, or give the position a \
                     type (`let y: Rat = ↑n`)",
                    e.span,
                );
            };
            return self.cast_to_type(cx, &args[0], target, e.span).map(Some);
        }
        if let ExprKind::TyApp { head: name, args: tys } = &head.kind
            && matches!(&name.kind, ExprKind::Var(n) if n == "cast")
            && tys.len() == 1
            && args.len() == 1
            && named.is_empty()
            && !self.shadowed(cx, "cast")
            && self.key_of("cast").is_none()
        {
            let (target, _) = self.elab_ty(cx, &tys[0])?;
            return self.cast_to_type(cx, &args[0], &target, e.span).map(Some);
        }
        Ok(None)
    }

    /// The help a type mismatch carries when the found type embeds in the
    /// expected one (docs/language/casting-design.md §5.4): the path, and the fix.
    /// Empty where there is no path, or no edges in scope.
    pub(crate) fn cast_help(&self, cx: &Cx, got: &Type, expected: &Type, span: Span) -> String {
        if self.traits.class(&Self::cast_class_key()).is_none() {
            return String::new();
        }
        let (Some(from), Some(to)) = (Carriers(self).carrier_of_ty(cx, got, span), Carriers(self).carrier_of_ty(cx, expected, span)) else {
            return String::new();
        };
        if from.key == to.key {
            return String::new();
        }
        let Ok(path) = self.cast_path(cx, &from.key, &to.key, (&from.written, &to.written), span) else {
            return String::new();
        };
        let short = |key: &str| key.rsplit("::").next().unwrap_or(key).to_string();
        let chain: Vec<String> = std::iter::once(from.written.clone()).chain(path.iter().map(|(_, t)| short(t))).collect();
        format!("; `{}` embeds in `{}` ({}): write `↑` before it", from.written, to.written, chain.join(" → "))
    }
}
