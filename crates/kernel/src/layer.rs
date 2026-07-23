//! Layers of DeLaM (docs/delam/04, §Meta-programming Modalities, Table feat).

/// The four layers, `v < c < p < m`.
///
/// - `Var`: variables only; admits only the local/global variable rules and
///   conversion (ch. 04, "A Note on Layer v Rules").
/// - `Code`: MLTT syntax as static code; no computation.
/// - `Prog`: vanilla MLTT with computation; the layer of types of code, where
///   code promotion is absorbed by definitional equivalence.
/// - `Meta`: MLTT extended with universe polymorphism, contextual types, and
///   the recursive principles over code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Layer {
    Var,
    Code,
    Prog,
    Meta,
}

impl Layer {
    /// `typeof(i)`: the layer at which the *types* of layer-`i` terms live.
    pub fn type_layer(self) -> Layer {
        match self {
            Layer::Var | Layer::Code | Layer::Prog => Layer::Prog,
            Layer::Meta => Layer::Meta,
        }
    }

    /// The judgment `i comp`: layers whose terms compute (β rules apply).
    pub fn computes(self) -> bool {
        matches!(self, Layer::Prog | Layer::Meta)
    }
}
