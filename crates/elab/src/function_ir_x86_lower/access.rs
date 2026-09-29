//! Untrusted composition proposals over existing pure certificates and reads.
//! Publication checks literal bytes and branch targets in the kernel.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccessFragment {
    pub bytes: Vec<u8>,
    code: String,
    layout: String,
    imports: BTreeSet<String>,
    /// The bytes as the children's literals, appended in the code's shape,
    /// and a proof that `access_bytes(code)` is that: an encoding or a length
    /// stated through it walks literals, never every instruction's encoding.
    lit: String,
    lit_proof: String,
    /// The same shape over leaf markers (`§i§`), and each leaf's certified
    /// literal with its length: publication spells the published bytes as the
    /// shape over chunks of `bytes`, so each chunk is checked against its
    /// leaf's literal, and none is compared a thousand bytes deep.
    shape: String,
    leaves: Vec<(String, usize)>,
}
fn shifted(shape: &str, by: usize) -> String {
    let mut out = String::new();
    let mut rest = shape;
    while let Some(start) = rest.find('§') {
        out.push_str(&rest[..start]);
        let tail = &rest[start + '§'.len_utf8()..];
        let end = tail.find('§').expect("marker");
        let index: usize = tail[..end].parse().expect("marker index");
        out.push_str(&format!("§{}§", index + by));
        rest = &tail[end + '§'.len_utf8()..];
    }
    out.push_str(rest);
    out
}
fn filled(shape: &str, leaf: impl Fn(usize) -> String) -> String {
    let mut out = String::new();
    let mut rest = shape;
    while let Some(start) = rest.find('§') {
        out.push_str(&rest[..start]);
        let tail = &rest[start + '§'.len_utf8()..];
        let end = tail.find('§').expect("marker");
        out.push_str(&leaf(tail[..end].parse().expect("marker index")));
        rest = &tail[end + '§'.len_utf8()..];
    }
    out.push_str(rest);
    out
}
fn literal(bytes: &[u8]) -> String {
    bytes.iter().rev().fold("Nil<BitVec(8)>".to_string(), |rest, b| format!("Cons(@bitvec::BitVec::ofNat(8, {b}), {rest})"))
}
/// TEST r64, r64 on one register: the selector every access edge reads.
fn test_bytes(register: Gpr) -> [u8; 3] {
    let r = register_code(register);
    [0x48 | (r >> 3) | ((r >> 3) << 2), 0x85, 0xc0 | ((r & 7) << 3) | (r & 7)]
}

/// A loop's exit displacement (past the body, its TEST and the back edge),
/// the offset where the back edge starts, and the back displacement, which
/// with that offset and the edge's own six bytes completes a 2^32 orbit.
pub fn near_loop_edges(guard: usize, body: usize) -> Result<(usize, usize, u64), String> {
    let exit = body + 9;
    let back_from = guard + 9 + body + 3;
    let span = back_from + 6;
    if exit > i32::MAX as usize || span > i32::MAX as usize { return Err("loop exceeds the near-branch range".into()); }
    Ok((exit, back_from, (1u64 << 32) - span as u64))
}

impl AccessFragment {
    /// The `AccessCode` term this fragment publishes, for proofs that name
    /// its subtrees.
    pub fn code(&self) -> &str { &self.code }
    /// The named structured certificate declarations must be in scope when
    /// checking publication. A mismatched plan/name fails the encoding proof.
    pub fn structured(prefix: &str, plan: &LoweredStructured) -> Self {
        let bytes = encode_structured(plan);
        Self { imports: prefix.rsplit_once("::").map(|(module, _)| module.to_string()).into_iter().collect(), code: format!("AccessPure({prefix}_code())"), layout: format!("{prefix}_layout()"),
            lit: format!("{prefix}_lit()"), lit_proof: format!("{prefix}_bytes_are()"), shape: "§0§".into(), leaves: vec![(format!("{prefix}_lit()"), bytes.len())], bytes }
    }
    pub fn read(load: ByteLoad) -> Self {
        let bytes = load.bytes();
        Self { imports: BTreeSet::new(), lit: literal(&bytes), lit_proof: "refl".into(), shape: "§0§".into(), leaves: vec![(literal(&bytes), bytes.len())],
            bytes, code: format!("AccessRead({})", load.render()), layout: "trivial".into() }
    }
    pub fn sequence(self, tail: Self) -> Self {
        let mut bytes = self.bytes;
        bytes.extend(tail.bytes);
        let imports = self.imports.union(&tail.imports).cloned().collect();
        let lit = format!("({}) ++ ({})", self.lit, tail.lit);
        // A child whose literal is its bytes by conversion (`refl`) needs no
        // step, and a bare `refl` would leave `cong_fn` nothing to infer.
        let first = (self.lit_proof != "refl").then(|| format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ xs => xs ++ access_bytes({}), {})", tail.code, self.lit_proof));
        let second = (tail.lit_proof != "refl").then(|| format!("cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ ys => ({}) ++ ys, {})", self.lit, tail.lit_proof));
        let lit_proof = match (first, second) {
            (Some(a), Some(b)) => format!("trans({a}, {b})"),
            (Some(a), None) => a,
            (None, Some(b)) => b,
            (None, None) => "refl".into(),
        };
        let shape = format!("({}) ++ ({})", self.shape, shifted(&tail.shape, self.leaves.len()));
        let mut leaves = self.leaves;
        leaves.extend(tail.leaves);
        Self { imports, bytes, code: format!("AccessSequence({}, {})", self.code, tail.code),
            layout: format!("access_sequence_layout({}, {}, {}, {})", self.code, tail.code, self.layout, tail.layout), lit, lit_proof, shape, leaves }
    }
    /// Resolve both forward labels from child byte lengths. Larger spans
    /// decline explicitly until near-branch selection is available.
    pub fn branch(register: Gpr, yes: Self, no: Self) -> Result<Self, String> {
        let fd = yes.bytes.len().checked_add(2).filter(|n| *n <= 127).ok_or("access true arm exceeds short-branch range")?;
        let jd = no.bytes.len();
        if jd > 127 { return Err("access false arm exceeds short-branch range".into()); }
        let mut bytes = test_bytes(register).to_vec();
        bytes.extend([0x74, fd as u8]);
        bytes.extend(yes.bytes);
        bytes.extend([0xeb, jd as u8]);
        bytes.extend(no.bytes);
        let target = |d| format!("λ (start: BitVec(64)) => trans(sym(bitvec::BitVec::iter_add_eq_add(64, next_rip(start, 2), @bitvec::BitVec::sign_extend(7, 56, @bitvec::BitVec::ofNat(8, {d})))), bitvec::BitVec::iterate_increment_compose(64, start, 2, {d}))");
        let imports = yes.imports.union(&no.imports).cloned().collect();
        // Through the library lemmas, not a tuple against AccessLayout of the
        // literal tree: the tuple makes the elaborator spell the tree's reduct.
        let displacements = format!("@bitvec::BitVec::ofNat(8, {fd}), @bitvec::BitVec::ofNat(8, {jd})");
        // Its literal is the whole branch, checked by evaluation as before.
        let lit = literal(&bytes);
        let leaves = vec![(lit.clone(), bytes.len())];
        Ok(Self { imports, lit, lit_proof: "refl".into(), shape: "§0§".into(), leaves, bytes,
            code: format!("AccessBranch({}, {displacements}, {}, {})", register.heather_name(), yes.code, no.code),
            layout: format!("access_branch_layout({}, {displacements}, {}, {}, {}, {}, {}, {})",
                register.heather_name(), yes.code, no.code, target(fd), target(jd), yes.layout, no.layout),
        })
    }
    /// A bounded loop (docs/native-bounded-loops-design.md §3): the guard, a
    /// near exit edge over the body, the body, and a near back edge to the
    /// guard. Both displacements are resolved from child lengths here and
    /// checked in the kernel by the layout proof.
    pub fn looped(guard: Self, flag: Gpr, body: Self, step: Gpr) -> Result<Self, String> {
        let (exit, back_from, back) = near_loop_edges(guard.bytes.len(), body.bytes.len())?;
        let mut bytes = guard.bytes.clone();
        bytes.extend(test_bytes(flag));
        bytes.extend([0x0f, 0x84]);
        bytes.extend((exit as u32).to_le_bytes());
        bytes.extend(&body.bytes);
        bytes.extend(test_bytes(step));
        bytes.extend([0x0f, 0x84]);
        bytes.extend((back as u32).to_le_bytes());
        let imports = guard.imports.union(&body.imports).cloned().collect();
        let exit_d = format!("@bitvec::BitVec::ofNat(32, {exit})");
        let back_d = format!("@bitvec::BitVec::ofNat(32, {back})");
        let code = format!("AccessLoop({}, {}, {exit_d}, {}, {}, {back_d})", guard.code, flag.heather_name(), body.code, step.heather_name());
        // Both edges read the children's lengths through their literals.
        let exit_edge = format!("λ (start: BitVec(64)) => trans(near_branch_forward(start, 6, {exit}, {exit_d}, refl), \
            cong_fn<List<BitVec(8)>, BitVec(64)>(λ bs => next_rip(start, 6 + (bs.len() + 9)), sym({})))", body.lit_proof);
        let back_edge = format!("λ (start: BitVec(64)) => j(sym({}), λ g _ => near_branch_target(next_rip(start, g.len() + 9 + access_bytes({}).len() + 3), 6, {back_d}) = start, \
            j(sym({}), λ b _ => near_branch_target(next_rip(start, ({}).len() + 9 + b.len() + 3), 6, {back_d}) = start, \
                near_branch_returns(start, {back_from}, 6, {back_d}, refl)))", guard.lit_proof, body.code, body.lit_proof, guard.lit);
        let layout = format!("access_loop_layout({}, {}, {exit_d}, {}, {}, {back_d}, {exit_edge}, {back_edge}, {}, {})",
            guard.code, flag.heather_name(), body.code, step.heather_name(), guard.layout, body.layout);
        let (test_flag, test_step) = (literal(&test_bytes(flag)), literal(&test_bytes(step)));
        let mut exit_jump = vec![0x0f, 0x84]; exit_jump.extend((exit as u32).to_le_bytes());
        let mut back_jump = vec![0x0f, 0x84]; back_jump.extend((back as u32).to_le_bytes());
        let (exit_jump, back_jump) = (literal(&exit_jump), literal(&back_jump));
        let lit = format!("({}) ++ ({test_flag} ++ ({exit_jump} ++ (({}) ++ ({test_step} ++ {back_jump}))))", guard.lit, body.lit);
        let g = guard.leaves.len();
        let b = g + 2 + body.leaves.len();
        let shape = format!("({}) ++ (§{g}§ ++ (§{}§ ++ (({}) ++ (§{b}§ ++ §{}§))))", guard.shape, g + 1, shifted(&body.shape, g + 2), b + 1);
        let mut leaves = guard.leaves.clone();
        leaves.push((test_flag.clone(), 3));
        leaves.push((exit_jump.clone(), 6));
        leaves.extend(body.leaves.iter().cloned());
        leaves.push((test_step.clone(), 3));
        leaves.push((back_jump.clone(), 6));
        let lit_proof = format!("trans(cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ xs => xs ++ (canonical_bytes(TestRR({f}, {f})) ++ (near_control_bytes(JumpZeroNear({exit_d})) ++ \
            (access_bytes({}) ++ (canonical_bytes(TestRR({st}, {st})) ++ near_control_bytes(JumpZeroNear({back_d})))))), {}), \
            cong_fn<List<BitVec(8)>, List<BitVec(8)>>(λ ys => ({}) ++ (canonical_bytes(TestRR({f}, {f})) ++ (near_control_bytes(JumpZeroNear({exit_d})) ++ \
            (ys ++ (canonical_bytes(TestRR({st}, {st})) ++ near_control_bytes(JumpZeroNear({back_d})))))), {}))",
            body.code, guard.lit_proof, guard.lit, body.lit_proof, f = flag.heather_name(), st = step.heather_name());
        Ok(Self { imports, bytes, code, layout, lit, lit_proof, shape, leaves })
    }
    pub fn publish(&self, prefix: &str) -> String {
        let mut module = Module::default();
        module.raw("import x86_64_access_code; import x86_64; import x86_64_block; import bitvec; import list; import logic;");
        for name in &self.imports { module.raw(format!("import {name};")); }
        module.declaration(emitted_function(format!("{prefix}_code"), false, vec![], "AccessCode", &self.code));
        // The bytes spelled as the children's literals, appended in the code's
        // shape, so the encoding is the composed proof itself. A flat list
        // compared against that tree recurses once per byte, past the
        // kernel's depth budget for a loop of a thousand bytes or so.
        let mut offset = 0;
        let chunks: Vec<String> = self.leaves.iter().map(|(_, length)| {
            let chunk = literal(&self.bytes[offset.min(self.bytes.len())..(offset + length).min(self.bytes.len())]);
            offset += length;
            chunk
        }).collect();
        let published = filled(&self.shape, |i| chunks[i].clone());
        module.declaration(emitted_function(format!("{prefix}_bytes"), false, vec![], "List<BitVec(8)>", &published));
        module.declaration(emitted_theorem(format!("{prefix}_encoding"), false, vec![], format!("{prefix}_bytes() = access_bytes({prefix}_code())"), &format!("sym({})", self.lit_proof)));
        module.declaration(emitted_theorem(format!("{prefix}_layout"), false, vec![], format!("AccessLayout({prefix}_code())"), &self.layout));
        module.render()
    }
}
