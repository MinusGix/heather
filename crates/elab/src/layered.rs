//! The layered registries' shared shape: immutable sealed layers, one
//! mutable suffix layer, and a derived index that makes a lookup's cost
//! independent of how many layers a world has
//! (`issues/layered-registry-lookups.md`).
//!
//! `Names`, `Types`, `Provenance` and `GenDefs` each split their tables into
//! one layer per module (a semantic image seals the current layer), so a
//! world over the whole library holds hundreds of layers. Probing every
//! layer's map in turn made a miss (the usual answer of `has_record_field`,
//! `declares_any_as`, `constructor` asked about a non-constructor) cost one
//! hash of the key per layer.
//!
//! The index holds, per table, which sealed layers hold a key whose
//! [`index_hash`] is `h`. Sealed layers never change, so it is built from
//! them alone, in *runs*: each sealed layer starts a run of one, and two runs
//! covering equally many layers merge (a binary counter), so a world of `n`
//! sealed layers has at most `log₂ n + 1` runs. A run is immutable and
//! shared by every snapshot whose prefix holds it, exactly as the layers
//! are, so a snapshot copies pointers and never an index. A lookup hashes its
//! key once, asks each run which of its layers to probe (almost always none
//! or one), and probes only those, plus the current layer.
//!
//! The index is a superset: two keys with the same index hash share an
//! entry, and the probe of the layer itself decides. It changes no answer and
//! no order: [`Layered::find`] still visits layers newest first and
//! [`Layered::candidates`] oldest first, merely skipping layers that cannot
//! hold the key. It is derived, so nothing about an image's format changes.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use heather_kernel::rc::Rc;

/// The hash the index files a key under, computed once per lookup.
///
/// Any `Hash` key: the hash of a stored `String` and of the `&str` a lookup
/// passes agree because `String` hashes as `str`. A multiply-rotate word
/// hash with a final avalanche, not SipHash: an index collision costs one
/// extra probe, never a wrong answer.
pub(crate) fn index_hash<K: Hash + ?Sized>(key: &K) -> u64 {
    let mut h = WordHasher(0);
    key.hash(&mut h);
    // fmix64: the index maps use the hash as is.
    let mut x = h.0;
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    x ^ (x >> 33)
}

struct WordHasher(u64);

impl WordHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl Hasher for WordHasher {
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            self.add(u64::from_le_bytes(chunk.try_into().expect("eight bytes")));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0u8; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(word));
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }

    fn write_u32(&mut self, i: u32) {
        self.add(u64::from(i));
    }

    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }

    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

/// The index maps' hasher: their keys are already [`index_hash`]es.
#[derive(Default)]
struct PreHashed(u64);

impl Hasher for PreHashed {
    fn write(&mut self, _: &[u8]) {
        unreachable!("index maps are keyed by u64 only")
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

/// One table of one run: per key hash, the run's sealed layers holding a
/// key with that hash, as positions in [`Sealed::layers`], ascending. Almost
/// every hash names one layer, stored inline; [`MANY`] marks a position in
/// `many` instead, which keeps a map entry at twelve bytes.
#[derive(Default)]
struct Table {
    map: HashMap<u64, u32, BuildHasherDefault<PreHashed>>,
    many: Vec<Box<[u32]>>,
}

/// The tag of a [`Table::map`] value that indexes [`Table::many`].
const MANY: u32 = 1 << 31;

impl Table {
    fn hits(&self, h: u64) -> Option<&[u32]> {
        let v = self.map.get(&h)?;
        Some(if v & MANY == 0 { std::slice::from_ref(v) } else { &self.many[(v & !MANY) as usize] })
    }

    fn hit_lists(&self) -> impl Iterator<Item = (u64, &[u32])> {
        self.map.keys().map(|&h| (h, self.hits(h).expect("own key")))
    }

    fn insert(&mut self, h: u64, hits: &[u32]) {
        let v = if let [one] = hits {
            *one
        } else {
            let i = u32::try_from(self.many.len()).expect("fewer than 2³¹ shared hashes");
            self.many.push(hits.into());
            i | MANY
        };
        self.map.insert(h, v);
    }

    /// `self` followed by the newer table `newer`.
    fn then(&self, newer: &Table) -> Table {
        let mut out = Table {
            map: HashMap::with_capacity_and_hasher(self.map.len() + newer.map.len(), Default::default()),
            many: Vec::new(),
        };
        let mut both = Vec::new();
        for (h, old) in self.hit_lists() {
            match newer.hits(h) {
                Some(new) => {
                    both.clear();
                    both.extend_from_slice(old);
                    both.extend_from_slice(new);
                    out.insert(h, &both);
                }
                None => out.insert(h, old),
            }
        }
        for (h, new) in newer.hit_lists() {
            if !self.map.contains_key(&h) {
                out.insert(h, new);
            }
        }
        out
    }
}

/// One table set of a registry layer, as the index needs to see it.
pub(crate) trait Layer: Clone + Default {
    /// How many tables the registry indexes; `table` arguments are below it.
    const TABLES: usize;

    /// Report the [`index_hash`] of every key `table` holds.
    fn keys(&self, table: usize, out: &mut dyn FnMut(u64));
}

/// A run of consecutive sealed layers and, per table, which of them hold
/// which key hashes. Immutable once built.
struct Run {
    layers: u32,
    tables: Box<[Table]>,
}

impl Run {
    fn of<L: Layer>(position: u32, layer: &L) -> Run {
        let tables = (0..L::TABLES)
            .map(|table| {
                let mut out = Table::default();
                layer.keys(table, &mut |h| out.insert(h, &[position]));
                out
            })
            .collect();
        Run { layers: 1, tables }
    }

    /// `self` followed by the newer run `newer`.
    fn then(&self, newer: &Run) -> Run {
        let tables = self.tables.iter().zip(newer.tables.iter()).map(|(old, new)| old.then(new)).collect();
        Run { layers: self.layers + newer.layers, tables }
    }
}

/// The immutable prefix: the sealed layers, oldest first, and the runs that
/// index them, in the same order.
struct Sealed<L> {
    layers: Vec<Rc<L>>,
    runs: Vec<Rc<Run>>,
}

impl<L> Clone for Sealed<L> {
    fn clone(&self) -> Self {
        Sealed {
            layers: self.layers.clone(),
            runs: self.runs.clone(),
        }
    }
}

impl<L> Default for Sealed<L> {
    fn default() -> Self {
        Sealed { layers: Vec::new(), runs: Vec::new() }
    }
}

/// A registry's tables: immutable sealed layers shared between snapshots and
/// one suffix layer that only this value mutates.
pub(crate) struct Layered<L> {
    sealed: Rc<Sealed<L>>,
    current: Rc<L>,
}

impl<L: Layer> Default for Layered<L> {
    fn default() -> Self {
        Layered {
            sealed: Rc::new(Sealed::default()),
            current: Rc::new(L::default()),
        }
    }
}

impl<L> Clone for Layered<L> {
    fn clone(&self) -> Self {
        Layered {
            sealed: Rc::clone(&self.sealed),
            current: Rc::clone(&self.current),
        }
    }
}

impl<L: Layer> Layered<L> {
    pub(crate) fn current(&self) -> &L {
        &self.current
    }

    /// The suffix layer, detached from any snapshot sharing it.
    #[track_caller]
    pub(crate) fn current_mut(&mut self) -> &mut L {
        crate::stats::make_mut(&mut self.current)
    }

    /// Freeze the current layer, whatever it holds, and start an empty one.
    /// The caller decides whether the layer is worth sealing.
    pub(crate) fn seal_current(&mut self) {
        let layer = std::mem::replace(&mut self.current, Rc::new(L::default()));
        let sealed = crate::stats::make_mut(&mut self.sealed);
        let position = u32::try_from(sealed.layers.len()).expect("fewer than 2³² layers");
        let mut run = Run::of(position, layer.as_ref());
        sealed.layers.push(layer);
        while let Some(last) = sealed.runs.last()
            && last.layers == run.layers
        {
            run = last.then(&run);
            sealed.runs.pop();
        }
        sealed.runs.push(Rc::new(run));
    }

    /// How many layers are sealed.
    #[cfg(test)]
    pub(crate) fn sealed_len(&self) -> usize {
        self.sealed.layers.len()
    }

    /// How many runs index the sealed layers.
    #[cfg(test)]
    pub(crate) fn run_count(&self) -> usize {
        self.sealed.runs.len()
    }

    #[cfg(test)]
    pub(crate) fn shares_sealed_with(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.sealed, &other.sealed)
    }

    /// The first `Some` of `probe` over the layers that may hold `key` in
    /// `table`, newest first: the current layer, then the sealed layers the
    /// index names. The same answer as probing every layer newest first.
    #[inline]
    pub(crate) fn find<'a, K: Hash + ?Sized, T>(
        &'a self,
        table: usize,
        key: &K,
        mut probe: impl FnMut(&'a L) -> Option<T>,
    ) -> Option<T> {
        if let Some(found) = probe(&self.current) {
            return Some(found);
        }
        let h = index_hash(key);
        let sealed: &'a Sealed<L> = &self.sealed;
        for run in sealed.runs.iter().rev() {
            if let Some(hits) = run.tables[table].hits(h) {
                for &i in hits.iter().rev() {
                    if let Some(found) = probe(&sealed.layers[i as usize]) {
                        return Some(found);
                    }
                }
            }
        }
        None
    }

    /// Every layer that may hold `key` in `table`, oldest first: the sealed
    /// layers the index names, then the current layer. A superset (an index
    /// collision names a layer without the key), so the caller reads the
    /// layer's own table, which answers nothing for such a layer.
    pub(crate) fn candidates<'a, K: Hash + ?Sized>(
        &'a self,
        table: usize,
        key: &K,
    ) -> impl Iterator<Item = &'a L> + 'a {
        let h = index_hash(key);
        let sealed: &'a Sealed<L> = &self.sealed;
        sealed.runs.iter()
            .filter_map(move |run| run.tables[table].hits(h))
            .flat_map(move |hits| hits.iter().map(move |&i| sealed.layers[i as usize].as_ref()))
            .chain(std::iter::once(self.current.as_ref()))
    }

    /// Every layer, newest first: for the scans that read whole tables.
    pub(crate) fn layers(&self) -> impl Iterator<Item = &L> {
        std::iter::once(self.current.as_ref()).chain(self.sealed.layers.iter().rev().map(Rc::as_ref))
    }

    /// Every layer, oldest first.
    pub(crate) fn layers_oldest_first(&self) -> impl Iterator<Item = &L> {
        self.sealed.layers.iter().map(Rc::as_ref).chain(std::iter::once(self.current.as_ref()))
    }

    /// Does any sealed layer hold a key in `table`?
    pub(crate) fn sealed_holds_any(&self, table: usize) -> bool {
        self.sealed.runs.iter().any(|run| !run.tables[table].map.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[derive(Clone, Default)]
    struct Toy {
        a: HashMap<String, u32>,
        b: HashMap<u32, String>,
    }

    impl Layer for Toy {
        const TABLES: usize = 2;
        fn keys(&self, table: usize, out: &mut dyn FnMut(u64)) {
            match table {
                0 => self.a.keys().for_each(|k| out(index_hash(k.as_str()))),
                _ => self.b.keys().for_each(|k| out(index_hash(k))),
            }
        }
    }

    /// The index answers exactly as probing every layer would, for every
    /// layer count up to a few carries, for hits, shadowed keys and misses,
    /// in both orders, and the run count stays logarithmic.
    #[test]
    fn the_index_agrees_with_a_scan_of_every_layer() {
        let mut layered = Layered::<Toy>::default();
        for n in 0..70u32 {
            let layer = layered.current_mut();
            layer.a.insert(format!("only{n}"), n);
            layer.a.insert("shared".into(), n);
            if n % 3 == 0 {
                layer.a.insert("every_third".into(), n);
            }
            layer.b.insert(n, format!("b{n}"));
            layered.seal_current();
            assert!(layered.run_count() <= (n + 1).count_ones() as usize);

            for key in ["shared", "every_third", "only0", "only7", "missing"] {
                let scan = layered.layers().find_map(|l| l.a.get(key)).copied();
                assert_eq!(layered.find(0, key, |l| l.a.get(key)).copied(), scan, "{key} at {n}");
                let all: Vec<u32> = layered.layers_oldest_first().filter_map(|l| l.a.get(key)).copied().collect();
                let via: Vec<u32> = layered.candidates(0, key).filter_map(|l| l.a.get(key)).copied().collect();
                assert_eq!(via, all, "{key} at {n}");
            }
            for abs in [0, n, n + 1, 1000] {
                let scan = layered.layers().find_map(|l| l.b.get(&abs)).cloned();
                assert_eq!(layered.find(1, &abs, |l| l.b.get(&abs)).cloned(), scan);
            }
        }
        assert_eq!(layered.sealed_len(), 70);
        // A miss probes no sealed layer.
        let mut probed = 0;
        assert!(layered.find(0, "missing", |l| { probed += 1; l.a.get("missing") }).is_none());
        assert_eq!(probed, 1, "only the current layer");
    }

    /// A snapshot shares the runs it was taken with; extending one copy
    /// builds new runs without touching the other's.
    #[test]
    fn snapshots_share_runs_and_extend_apart() {
        let mut base = Layered::<Toy>::default();
        for n in 0..3u32 {
            base.current_mut().a.insert(format!("k{n}"), n);
            base.seal_current();
        }
        let mut left = base.clone();
        let right = base.clone();
        left.current_mut().a.insert("left".into(), 9);
        left.seal_current();
        assert!(right.shares_sealed_with(&base));
        assert_eq!(left.run_count(), 1);
        assert_eq!(right.run_count(), 2);
        assert!(right.find(0, "left", |l| l.a.get("left")).is_none());
        assert_eq!(left.find(0, "left", |l| l.a.get("left")), Some(&9));
        assert_eq!(left.find(0, "k0", |l| l.a.get("k0")), Some(&0));
    }
}
