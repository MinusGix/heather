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

/// The label a jump's item goes to, and whether the jump is conditional
/// (`verified::read_items_with` spells the items).
pub(super) fn jump(item: &str) -> Option<(u64, bool)> {
    let target = |prefix: &str| item.strip_prefix(prefix)
        .and_then(|rest| rest.trim_end_matches(')').rsplit(", ").next()?.parse::<u64>().ok());
    match (target("Jcc(").or_else(|| target("JccShort(")), target("Jmp(").or_else(|| target("JmpShort(")).or_else(|| target("CallTo("))) {
        (Some(to), _) => Some((to, true)),
        (_, Some(to)) => Some((to, false)),
        _ => None,
    }
}

/// Which labels' jumps can take the two-byte form, over one function's
/// items as emitted near (`JccShort`, `JmpShort`; issues/function-ir-verified-short-jumps.md):
/// every JCC and JMP to a label of these items starts short, and a label
/// any of whose jumps does not reach it within a signed byte goes back to
/// near, until nothing changes. Lengthening a jump only moves labels
/// further apart, so the set only shrinks and the loop ends. Untrusted: the
/// placement's `Short` heads say it, and the lowering's landing check is
/// what holds a short jump to its target.
pub(super) fn relax(items: &[(u64, String)], lens: &[u64]) -> BTreeSet<u64> {
    let named: BTreeSet<u64> = items.iter().filter(|(name, _)| *name != 0).map(|(name, _)| *name).collect();
    let jumps: Vec<(usize, u64, bool)> = items.iter().enumerate()
        .filter(|(_, (_, item))| item.starts_with("Jcc(") || item.starts_with("Jmp("))
        .filter_map(|(i, (_, item))| jump(item).map(|(to, conditional)| (i, to, conditional)))
        .filter(|(_, to, _)| named.contains(to)).collect();
    let mut short: BTreeSet<u64> = jumps.iter().map(|&(_, to, _)| to).collect();
    loop {
        let sized: Vec<u64> = items.iter().zip(lens).enumerate().map(|(i, (_, &len))| match jumps.iter().find(|&&(j, _, _)| j == i) {
            Some(&(_, to, _)) if short.contains(&to) => 2,
            _ => len,
        }).collect();
        let at = offsets(&sized);
        let offset: std::collections::BTreeMap<u64, u64> = items.iter().enumerate().filter(|(_, (name, _))| *name != 0).map(|(i, (name, _))| (*name, at[i])).collect();
        let far: Vec<u64> = jumps.iter().filter(|&&(_, to, _)| short.contains(&to)).filter(|&&(i, to, conditional)| {
            let distance = offset[&to] as i64 - at[i + 1] as i64;
            // A JCC lands ahead only (`ShortForward`), a JMP either way.
            !(if conditional { (0..=127).contains(&distance) } else { (-128..=127).contains(&distance) })
        }).map(|&(_, to, _)| to).collect();
        if far.is_empty() { return short; }
        for to in far { short.remove(&to); }
    }
}

/// An item with its jump in the two-byte form.
pub(super) fn shortened(item: &str) -> String {
    if let Some(rest) = item.strip_prefix("Jcc(") { format!("JccShort({rest}") }
    else if let Some(rest) = item.strip_prefix("Jmp(") { format!("JmpShort({rest}") }
    else { item.to_string() }
}

/// The bytes linked: each jump's displacement, its item's last four bytes,
/// written as `near_rel` has it (x86_64_layout), from the item's end to its
/// label's offset around 2^32. The reads give every item's bytes before the
/// labels are known (`Prog::unlinked`, native_compile), and a displacement
/// is all of an item's bytes that depends on them (`asm_bytes`). Untrusted,
/// as the reads are: bytes linked wrong are a piece the kernel refuses.
pub(super) fn link(items: &[(u64, String)], offsets: &[u64], bytes: &mut [u8]) -> Result<(), String> {
    let named: std::collections::BTreeMap<u64, u64> = items.iter().enumerate().filter(|(_, (name, _))| *name != 0).map(|(i, (name, _))| (*name, offsets[i])).collect();
    for (i, (_, item)) in items.iter().enumerate() {
        let Some((to, _)) = jump(item) else { continue };
        let (end, to) = (offsets[i + 1], *named.get(&to).ok_or_else(|| format!("a jump to label {to}, which no item names"))?);
        // A short jump's displacement is its last byte (`short_rel`), a
        // near one's its last four (`near_rel`).
        let short = item.starts_with("JccShort(") || item.starts_with("JmpShort(");
        let displacement = (to.wrapping_sub(end) as u32).to_le_bytes();
        let width = if short { 1 } else { 4 };
        let end = end as usize;
        if end < width || end > bytes.len() || offsets[i + 1] - offsets[i] < width as u64 + 1 { return Err("a jump's bytes did not read back".into()); }
        bytes[end - width..end].copy_from_slice(&displacement[..width]);
    }
    Ok(())
}

/// The table, `{p}_table()`: what the certificate checks the layout and the
/// bytes by.
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

/// The bytes a piece at a time (`verified::cut_pieces`), each
/// piece by the table (`LabelTable::piece_by`): the window's offsets carried
/// down from where the pass says it ends, its jumps' targets the table's.
/// Each window is the literal's definition where it ends, not
/// `asm_back(code, back)`: walking back from the whole program made every
/// piece's statement, and the `upto` chain's, convert past every later
/// piece, more than linear in the program (issues/write-elf-build-constants.md).
/// A piece's bytes are a list of numerals mapped to bytes: as a literal of
/// `word_literal`s each byte was eight constructors and a vector for the
/// elaborator, which made the pieces' definitions most of their cost, while
/// the kernel reads `ofNat` at a numeral as one word either way
/// (issues/native-certificate-literal-cost.md).
pub(super) fn byte_pieces(p: &str, pieces: &[Piece], bytes: &[u8], items: usize, offsets: &[u64]) -> String {
    let mut text = String::new();
    let mut end = bytes.len();
    let length = offsets[items];
    for (c, piece) in pieces.iter().enumerate() {
        let (count, start) = (piece.count, piece.start);
        let literal: Vec<String> = bytes[start..end].iter().map(u8::to_string).collect();
        end = start;
        let top = items - piece.back;
        text.push_str(&format!("fn {p}_piece_{c}() → List<BitVec(8)> {{ List::map<Nat, BitVec(8)>([{}], λ (b: Nat) => @bitvec::BitVec::ofNat(8, b)) }}
theorem {p}_piece_{c}_is(): asm_code_after(no_fills(), asm_labels({p}_code()), {p}_at_{top}(), {count}) = {p}_piece_{c}() {{
    trans({p}_table().piece_by({p}_code(), {length}, {p}_checked_{items}(), {p}_at_{top}(), {top}, {}, {count}, {p}_checked_{top}(), trivial), refl)
}}
", literal.join(", "), offsets[top]));
    }
    // Each piece's code up to its start, over the literal's definition there,
    // so a step walks back over its own piece only.
    let m = pieces.len();
    let at = |k: usize| if k == 0 { "Start".to_string() } else { format!("{p}_at_{k}()") };
    text.push_str(&format!("
// The code up to each piece's start, from the program's.
fn {p}_upto_{m}() → List<BitVec(8)> {{ [] }}
theorem {p}_upto_{m}_is(): asm_code(no_fills(), asm_labels({p}_code()), Start) = {p}_upto_{m}() {{ refl }}
"));
    for (c, Piece { back, count, .. }) in pieces.iter().enumerate().rev() {
        let (next, top) = (c + 1, at(items - back));
        text.push_str(&format!("fn {p}_upto_{c}() → List<BitVec(8)> {{ {p}_upto_{next}() ++ {p}_piece_{c}() }}
theorem {p}_upto_{c}_is(): asm_code(no_fills(), asm_labels({p}_code()), {top}) = {p}_upto_{c}() {{
    trans(asm_code_back(no_fills(), asm_labels({p}_code()), {count}, {top}),
        trans(cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ x => x ++ asm_code_after(no_fills(), asm_labels({p}_code()), {top}, {count}), {p}_upto_{next}_is()),
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
