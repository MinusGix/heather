//! `write-elf`'s layout and bytes by a label table (x86_64_asm_table).
//!
//! `Prog::laid_out` and `assemble` look a label up by walking the program,
//! so stating either a stretch at a time was still quadratic in the program
//! (issues/native-compile-linear-layout.md). Here the program's labels are
//! written down once, as a `LabelTable` whose functions are decision trees
//! over literals, and the kernel checks the table against the program in one
//! pass a stretch at a time (`LabelTable::checked`, from the end, each
//! item's index and offset carried). `LabelTable::laid_out_of` turns the
//! whole pass into the layout, and `LabelTable::piece_by` each piece of the
//! bytes into an evaluation by the table's offsets. The table is untrusted:
//! a wrong one is a pass the kernel refuses.

use std::collections::BTreeSet;

use super::verified::Piece;

/// A decision tree over `var`, the keys of `pairs` sorted: comparisons on
/// literals, so a lookup is logarithmic in the keys.
fn tree(var: &str, pairs: &[(u64, u64)]) -> String {
    match pairs {
        [] => "0".into(),
        [(_, value)] => value.to_string(),
        _ => {
            let mid = pairs.len() / 2;
            format!("match {var}.leb({}) {{ True => {}, False => {} }}", pairs[mid - 1].0, tree(var, &pairs[..mid]), tree(var, &pairs[mid..]))
        }
    }
}

/// Where each item starts, and where the last one ends.
pub(super) fn offsets(lens: &[u64]) -> Vec<u64> {
    let mut offsets = Vec::with_capacity(lens.len() + 1);
    offsets.push(0);
    for len in lens { offsets.push(offsets.last().unwrap() + len); }
    offsets
}

/// The table, `{p}_table()`: what the fork reads the bytes by, and what the
/// certificate checks.
pub(super) fn table(p: &str, items: &[(u64, String)], offsets: &[u64]) -> String {
    let mut named: Vec<(u64, usize)> = items.iter().enumerate().filter(|(_, (name, _))| *name != 0).map(|(i, (name, _))| (*name, i)).collect();
    named.sort_unstable();
    let index: Vec<(u64, u64)> = named.iter().map(|&(name, i)| (name, i as u64)).collect();
    let offset: Vec<(u64, u64)> = named.iter().map(|&(name, i)| (name, offsets[i])).collect();
    let names: Vec<(u64, u64)> = items.iter().enumerate().map(|(i, (name, _))| (i as u64, *name)).collect();
    format!("// Where each label is, and each item's name: the table the pass checks.
fn {p}_index_of(n: Nat) → Nat {{ {} }}
fn {p}_offset_of(n: Nat) → Nat {{ {} }}
fn {p}_name_at(i: Nat) → Nat {{ {} }}
fn {p}_table() → LabelTable {{ LabelTable(λ n => {p}_index_of(n), λ n => {p}_offset_of(n), λ i => {p}_name_at(i), {}) }}
", tree("n", &index), tree("n", &offset), tree("i", &names), items.len())
}

/// The pass at each cut of the literal, `{p}_checked_{c}`: the program's
/// first `c` items, `c` deep, ending where they end. `cuts` are the
/// literal's (`emission::code`).
pub(super) fn layout(p: &str, offsets: &[u64], cuts: &BTreeSet<usize>) -> String {
    let mut text = String::new();
    let mut earlier = 0;
    for &cut in cuts.iter().filter(|&&cut| cut > 0) {
        let rest = if earlier == 0 { "trivial".to_string() } else { format!("{p}_checked_{earlier}()") };
        let (k, end) = (cut - earlier, offsets[cut]);
        text.push_str(&format!("theorem {p}_checked_{cut}(): {p}_table().checked({p}_at_{cut}(), {cut}, {end}).IsTrue() {{
    {p}_table().checked_back({k}, {p}_at_{cut}(), {cut}, {end}, trivial, {rest})
}}
"));
        earlier = cut;
    }
    text
}

/// Where each piece's window ends, in items: the literal must be cut there.
pub(super) fn piece_cuts(pieces: &[Piece], items: usize) -> impl Iterator<Item = usize> + '_ {
    pieces.iter().map(move |piece| items - piece.back)
}

/// A piece's bytes read on the fork, by the table's offsets.
pub(super) fn piece_read(p: &str, piece: &Piece, items: usize, offsets: &[u64]) -> String {
    let top = items - piece.back;
    format!("asm_code_ending(no_fills(), {p}_table().labels(), {p}_at_{top}(), {}, {})", piece.count, offsets[top])
}

/// The bytes a piece at a time, as `verified::byte_pieces` states them, each
/// piece by the table (`LabelTable::piece_by`): the window's offsets carried
/// down from where the pass says it ends, its jumps' targets the table's.
pub(super) fn byte_pieces(p: &str, pieces: &[Piece], bytes: &[u8], items: usize, offsets: &[u64]) -> String {
    let mut text = String::new();
    let mut end = bytes.len();
    let length = offsets[items];
    for (c, piece) in pieces.iter().enumerate() {
        let (back, count, start) = (piece.back, piece.count, piece.start);
        let literal: Vec<String> = bytes[start..end].iter().map(|b| format!("@bitvec::BitVec::ofNat(8, {b})")).collect();
        end = start;
        let top = items - back;
        text.push_str(&format!("fn {p}_piece_{c}() → List<BitVec(8)> {{ [{}] }}
theorem {p}_piece_{c}_is(): asm_code_after(no_fills(), asm_labels({p}_code()), asm_back({p}_code(), {back}), {count}) = {p}_piece_{c}() {{
    trans({p}_table().piece_by({p}_code(), {length}, {p}_checked_{items}(), {p}_at_{top}(), {top}, {}, {count}, {p}_checked_{top}(), trivial), refl)
}}
", literal.join(", "), offsets[top]));
    }
    let m = pieces.len();
    let back: usize = pieces.iter().map(|piece| piece.count).sum();
    text.push_str(&format!("
// The code up to each piece's start, from the program's.
fn {p}_upto_{m}() → List<BitVec(8)> {{ [] }}
theorem {p}_upto_{m}_is(): asm_code(no_fills(), asm_labels({p}_code()), asm_back({p}_code(), {back})) = {p}_upto_{m}() {{ refl }}
"));
    for (c, Piece { back, count, .. }) in pieces.iter().enumerate().rev() {
        let next = c + 1;
        text.push_str(&format!("fn {p}_upto_{c}() → List<BitVec(8)> {{ {p}_upto_{next}() ++ {p}_piece_{c}() }}
theorem {p}_upto_{c}_is(): asm_code(no_fills(), asm_labels({p}_code()), asm_back({p}_code(), {back})) = {p}_upto_{c}() {{
    trans(asm_code_back(no_fills(), asm_labels({p}_code()), {count}, asm_back({p}_code(), {back})),
        trans(cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => x ++ asm_code_after(no_fills(), asm_labels({p}_code()), asm_back({p}_code(), {back}), {count}), {p}_upto_{next}_is()),
            cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => {p}_upto_{next}() ++ x, {p}_piece_{c}_is())))
}}
"));
    }
    text.push_str(&format!("
theorem {p}_bytes(): assemble(no_fills(), {p}_code(), []) = {p}_upto_0() {{
    trans(List::append_nil(asm_code(no_fills(), asm_labels({p}_code()), {p}_code())), {p}_upto_0_is())
}}
"));
    text
}
